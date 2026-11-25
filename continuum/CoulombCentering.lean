import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace CoulombCentering

variable {X : Type*} [MeasurableSpace X]

/-- For the reference orbital the spatial probability measure is |u|² dx. -/
noncomputable def hartree (μ : Measure X) (W : X → X → ℝ) (x : X) : ℝ :=
  ∫ y, W x y ∂μ

noncomputable def centered (μ : Measure X) (W : X → X → ℝ) (x y : X) : ℝ :=
  W x y - hartree μ W x - hartree μ W y + ∫ z, hartree μ W z ∂μ

theorem row_zero (μ : Measure X) [IsProbabilityMeasure μ] (W : X → X → ℝ)
    (x : X) (hrow : Integrable (W x) μ) (hJ : Integrable (hartree μ W) μ) :
    ∫ y, centered μ W x y ∂μ = 0 := by
  have h1 : Integrable (fun y => W x y - hartree μ W x) μ :=
    hrow.sub (integrable_const (μ := μ) (hartree μ W x))
  have h2 : Integrable (fun y => W x y - hartree μ W x - hartree μ W y) μ := h1.sub hJ
  unfold centered
  rw [integral_add h2 (integrable_const (μ:=μ) (∫ z, hartree μ W z ∂μ)), integral_sub h1 hJ,
    integral_sub hrow (integrable_const (μ:=μ) (hartree μ W x))]
  simp [hartree]

theorem centered_symmetric (μ : Measure X) (W : X → X → ℝ)
    (symmW : ∀ x y, W x y = W y x) (x y : X) : centered μ W x y = centered μ W y x := by
  unfold centered
  rw [symmW x y]
  ring

/-- Positivity of the repulsive kernel and a Hartree bound give the
    pointwise floor on the centered interaction. -/
theorem pointwise_floor (μ : Measure X) (W : X → X → ℝ)
    (hw : ∀ x y, 0 ≤ W x y) (hj : ∀ x, hartree μ W x ≤ 2) (x y : X) :
    -(4:ℝ) ≤ centered μ W x y := by
  have hpos (t : X) : 0 ≤ hartree μ W t := integral_nonneg (hw t)
  have havg := integral_nonneg (μ:=μ) hpos
  unfold centered
  linarith [hw x y, hj x, hj y]

theorem multiplication_form_floor {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (L ρ : Z → ℝ) (hρ : ∀ z, 0 ≤ ρ z) (hL : ∀ z, -(4:ℝ) ≤ L z)
    (hi : Integrable ρ ν) (hform : Integrable (fun z => L z * ρ z) ν) :
    -(4:ℝ) * (∫ z, ρ z ∂ν) ≤ ∫ z, L z * ρ z ∂ν := by
  have h := integral_mono (hi.const_mul (-4)) hform (fun z => mul_le_mul_of_nonneg_right (hL z) (hρ z))
  simpa only [integral_const_mul] using h

/-- Orthogonality to arbitrary complex one-coordinate tests, including spin
    components. Joint integrability is the form-domain condition. -/
theorem single_test_first (μ : Measure X) [IsProbabilityMeasure μ] (W : X → X → ℝ)
    (hrow : ∀ x, Integrable (W x) μ) (hJ : Integrable (hartree μ W) μ) (f : X → ℂ)
    (htest : Integrable (fun z : X × X => f z.1 * (centered μ W z.1 z.2 : ℂ)) (μ.prod μ)) :
    ∫ z : X × X, f z.1 * (centered μ W z.1 z.2 : ℂ) ∂(μ.prod μ) = 0 := by
  rw [integral_prod _ htest]
  simp_rw [integral_const_mul, integral_complex_ofReal, row_zero μ W _ (hrow _) hJ]
  simp

theorem single_test_second (μ : Measure X) [IsProbabilityMeasure μ] (W : X → X → ℝ)
    (symmW : ∀ x y, W x y = W y x)
    (hrow : ∀ x, Integrable (W x) μ) (hJ : Integrable (hartree μ W) μ) (f : X → ℂ)
    (htest : Integrable (fun z : X × X => f z.2 * (centered μ W z.1 z.2 : ℂ)) (μ.prod μ)) :
    ∫ z : X × X, f z.2 * (centered μ W z.1 z.2 : ℂ) ∂(μ.prod μ) = 0 := by
  rw [integral_prod_symm _ htest]
  have each (y : X) : ∫ x, centered μ W x y ∂μ = 0 := by
    simpa only [centered_symmetric μ W symmW y] using row_zero μ W y (hrow y) hJ
  simp_rw [integral_const_mul, integral_complex_ofReal, each]
  simp

/-- Spin sum of the centered residual against the determinant of a constant
    occupied spinor and an arbitrary spinor. The orbitals here use the weighted
    representation relative to the positive reference spatial wavefunction. -/
theorem spin_singlet_single (μ : Measure X) [IsProbabilityMeasure μ] (W : X → X → ℝ)
    (symmW : ∀ x y, W x y = W y x) (hrow : ∀ x, Integrable (W x) μ)
    (hJ : Integrable (hartree μ W) μ) (a b : ℂ) (up down : X → ℂ)
    (hi₁ : Integrable (fun z : X × X => (a*down z.1-b*up z.1) *
      (centered μ W z.1 z.2 : ℂ)) (μ.prod μ))
    (hi₂ : Integrable (fun z : X × X => (a*down z.2-b*up z.2) *
      (centered μ W z.1 z.2 : ℂ)) (μ.prod μ)) :
    ∫ z : X × X, ((a*down z.2-up z.1*b)-(b*up z.2-down z.1*a)) *
      (centered μ W z.1 z.2 : ℂ) ∂(μ.prod μ) = 0 := by
  let f (x : X) := a*down x-b*up x
  calc
    _ = ∫ z : X × X, (f z.1*(centered μ W z.1 z.2 : ℂ) +
        f z.2*(centered μ W z.1 z.2 : ℂ)) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [f]
      ring
    _ = _ := by
      rw [integral_add hi₁ hi₂, single_test_first μ W hrow hJ f hi₁,
        single_test_second μ W symmW hrow hJ f hi₂, add_zero]

end CoulombCentering
