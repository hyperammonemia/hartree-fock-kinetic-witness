import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A weak exterior comparison principle for the three-dimensional radial measure. -/

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace HFExterior

def radialDensity (V u t : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * (deriv u r * deriv t r / 2 + V r * (u r * t r))

/-- Representatives on the half-line can be extended by their trace to the left of q. -/
structure ExteriorProfile (q : ℝ) (V u : ℝ → ℝ) : Prop where
  cont : Continuous u
  locallyAC : ∀ a b : ℝ, q ≤ a → q ≤ b → AbsolutelyContinuousOnInterval u a b
  finiteEnergy : Integrable (radialDensity V u u) (volume.restrict (Ioi q))

def weakExteriorSubsolution (q : ℝ) (V u : ℝ → ℝ) : Prop :=
  ∀ t : ℝ → ℝ, ExteriorProfile q V t → t q = 0 → (∀ r, 0 ≤ t r) →
    (∫ r in Ioi q, radialDensity V u t r) ≤ 0

def positivePart (u : ℝ → ℝ) (r : ℝ) : ℝ := max (u r) 0

private theorem positivePart_deriv {u : ℝ → ℝ} (hu : Continuous u) (r : ℝ) :
    deriv (positivePart u) r = if 0 < u r then deriv u r else 0 := by
  by_cases hr : 0 < u r
  · rw [if_pos hr]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hu.continuousAt (Ioi_mem_nhds hr)] with t ht
    exact max_eq_left (le_of_lt ht)
  · rw [if_neg hr]
    have hm : IsMinOn (positivePart u) univ r := by
      intro t _
      change max (u r) 0 ≤ max (u t) 0
      rw [max_eq_right (le_of_not_gt hr)]
      exact le_max_right _ _
    exact (hm.isLocalMin Filter.univ_mem).deriv_eq_zero

private theorem clipped_energy {u V : ℝ → ℝ} (hu : Continuous u) :
    radialDensity V (positivePart u) (positivePart u) =
      {r | 0 < u r}.indicator (radialDensity V u u) := by
  funext r
  by_cases hr : 0 < u r
  · simp [radialDensity, positivePart_deriv hu, positivePart, hr, hr.le]
  · simp [radialDensity, positivePart_deriv hu, positivePart, hr, le_of_not_gt hr]

private theorem pairing_positivePart {u V : ℝ → ℝ} (hu : Continuous u) (r : ℝ) :
    radialDensity V u (positivePart u) r =
      radialDensity V (positivePart u) (positivePart u) r := by
  by_cases hr : 0 < u r
  · simp [radialDensity, positivePart_deriv hu, positivePart, hr, hr.le]
  · simp [radialDensity, positivePart_deriv hu, positivePart, hr, le_of_not_gt hr]

theorem ExteriorProfile.positivePart {q : ℝ} {V u : ℝ → ℝ}
    (hu : ExteriorProfile q V u) : ExteriorProfile q V (positivePart u) where
  cont := hu.cont.max continuous_const
  locallyAC := fun a b ha hb =>
    (LipschitzWith.id.max_const 0).comp_absolutelyContinuousOnInterval (hu.locallyAC a b ha hb)
  finiteEnergy := by
    rw [clipped_energy hu.cont]
    exact hu.finiteEnergy.indicator (isOpen_lt continuous_const hu.cont).measurableSet

/-- Positivity of the potential turns the weak form inequality into pointwise exterior order.
No smoothness of the profile derivatives or condition at an artificial outer boundary is used. -/
theorem weak_radial_maximum {q : ℝ} {V u : ℝ → ℝ} (hq : 0 ≤ q)
    (hV : ∀ r, q < r → 0 < V r) (hu : ExteriorProfile q V u)
    (hb : u q ≤ 0) (hweak : weakExteriorSubsolution q V u) :
    ∀ r, q < r → u r ≤ 0 := by
  have hp := hu.positivePart
  have htest := hweak (positivePart u) hp (max_eq_right hb) (fun _ => le_max_right _ _)
  simp only [pairing_positivePart hu.cont] at htest
  have hm := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := q))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi q)]
      radialDensity V (positivePart u) (positivePart u) := by
    filter_upwards [hm] with r hr
    unfold radialDensity
    have hVr := hV r hr
    have hz : 0 ≤ deriv (positivePart u) r * deriv (positivePart u) r := mul_self_nonneg _
    have hy : 0 ≤ positivePart u r * positivePart u r := mul_self_nonneg _
    exact mul_nonneg (sq_nonneg _) (add_nonneg (by positivity) (mul_nonneg hVr.le hy))
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hp.finiteEnergy).mp
    (le_antisymm htest (integral_nonneg_of_ae hnonneg))
  have hzero : positivePart u =ᵐ[volume.restrict (Ioi q)] (fun _ => 0) := by
    filter_upwards [hm, heq] with r hr hz
    by_contra hn
    have hrpos : 0 < r := lt_of_le_of_lt hq hr
    have hVr := hV r hr
    have hpp : 0 < positivePart u r * positivePart u r := mul_self_pos.mpr hn
    have hgrad : 0 ≤ deriv (positivePart u) r * deriv (positivePart u) r := mul_self_nonneg _
    have hstrict : 0 < radialDensity V (positivePart u) (positivePart u) r :=
      mul_pos (sq_pos_of_pos hrpos) (add_pos_of_nonneg_of_pos (by positivity) (mul_pos hVr hpp))
    exact (ne_of_gt hstrict) hz
  have hpoint := MeasureTheory.Measure.eqOn_open_of_ae_eq hzero isOpen_Ioi hp.cont.continuousOn
    (continuous_const.continuousOn)
  intro r hr
  have h := hpoint (show r ∈ Ioi q from hr)
  exact (le_max_left (u r) 0).trans (le_of_eq h)

end HFExterior
