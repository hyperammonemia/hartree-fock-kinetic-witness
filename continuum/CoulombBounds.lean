import CoulombCentering
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

open MeasureTheory
open CoulombCentering

namespace CoulombBounds

variable {X : Type*} [MeasurableSpace X]

/-- For the product probability of the reference orbital, the squared
    residual norm is at most 40; the energy proof only uses the weaker 64. -/
theorem centered_square (μ : Measure X) [IsProbabilityMeasure μ] (W : X → X → ℝ)
    (hp : ∀ x y, 0 ≤ W x y) (hJ : Integrable (hartree μ W) μ)
    (hJ₂ : ∀ x, hartree μ W x ≤ 2)
    (hwm : AEStronglyMeasurable (fun z : X × X => W z.1 z.2) (μ.prod μ))
    (hi : Integrable (fun z : X × X => (W z.1 z.2)^2) (μ.prod μ))
    (hbound : (∫ z : X × X, (W z.1 z.2)^2 ∂(μ.prod μ)) ≤ 4) :
    MemLp (fun z : X × X => centered μ W z.1 z.2) 2 (μ.prod μ) ∧
      (∫ z : X × X, (centered μ W z.1 z.2)^2 ∂(μ.prod μ)) ≤ 40 := by
  let m := ∫ x, hartree μ W x ∂μ
  have j0 (x : X) : 0 ≤ hartree μ W x := integral_nonneg (hp x)
  have m0 : 0 ≤ m := integral_nonneg j0
  have m2 : m ≤ 2 := by
    simpa [m] using integral_mono hJ (integrable_const (μ:=μ) (2:ℝ)) hJ₂
  have each (z : X × X) : (centered μ W z.1 z.2)^2 ≤ 2*(W z.1 z.2)^2+32 := by
    let t := -hartree μ W z.1-hartree μ W z.2+m
    have lo : -4 ≤ t := by dsimp [t]; linarith [hJ₂ z.1,hJ₂ z.2]
    have up : t ≤ 4 := by dsimp [t]; linarith [j0 z.1,j0 z.2]
    have ht : t^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr up) (sub_nonneg.mpr lo)]
    have heq : centered μ W z.1 z.2 = W z.1 z.2+t := by dsimp [centered,t,m]; ring
    rw [heq]
    nlinarith [sq_nonneg (W z.1 z.2-t)]
  have hm : AEStronglyMeasurable (fun z : X × X => centered μ W z.1 z.2) (μ.prod μ) :=
    ((hwm.sub hJ.aestronglyMeasurable.comp_fst).sub hJ.aestronglyMeasurable.comp_snd).add
      aestronglyMeasurable_const
  have hmajor : Integrable (fun z : X × X => 2*(W z.1 z.2)^2+32) (μ.prod μ) :=
    (hi.const_mul 2).add (integrable_const 32)
  have hs : Integrable (fun z : X × X => (centered μ W z.1 z.2)^2) (μ.prod μ) :=
    hmajor.mono' (hm.pow 2) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact each z)
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hs,?_⟩
  have hle := integral_mono hs hmajor each
  rw [integral_add (hi.const_mul 2) (integrable_const (μ:=μ.prod μ) (32:ℝ)),integral_const_mul] at hle
  simp at hle
  linarith

end CoulombBounds
