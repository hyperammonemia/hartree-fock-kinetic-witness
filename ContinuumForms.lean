import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual integral identities used in the radial witness. -/

namespace ContinuumForms
open MeasureTheory Measure

section Form
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def directional (v : E) (f : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ f x v

def fluxFactor (w u : E → ℝ) (x : E) : ℝ := w x * u x * u x

private theorem directional_mul (v : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    directional v (fun y => f y * g y) x =
      f x * directional v g x + g x * directional v f x := by
  simp [directional, fderiv_fun_mul hf hg]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One directional summand of the twice-kinetic ground-state transform on
the whole space. E can in particular be the one- or two-particle configuration
space in 3D. The ordinary regularity and integrability assumptions are explicit. -/
theorem ground_transform (μ : Measure E) [IsAddHaarMeasure μ]
    (v : E) (w u : E → ℝ)
    (hw : Differentiable ℝ w) (hu : Differentiable ℝ u)
    (hdw : Differentiable ℝ (directional v w))
    (hkin : Integrable (fun x => w x ^ 2 * directional v u x ^ 2) μ)
    (hfirst : Integrable (fun x => directional v (fluxFactor w u) x * directional v w x) μ)
    (hsecond : Integrable (fun x => fluxFactor w u x * directional v (directional v w) x) μ)
    (hflux : Integrable (fun x => fluxFactor w u x * directional v w x) μ) :
    (∫ x, directional v (fun y => w y * u y) x ^ 2 +
          (directional v (directional v w) x / w x) * (w x * u x)^2 ∂μ) =
        ∫ x, w x ^ 2 * directional v u x ^ 2 ∂μ := by
  have parts : (∫ x, fluxFactor w u x * directional v (directional v w) x ∂μ) =
      -(∫ x, directional v (fluxFactor w u) x * directional v w x ∂μ) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fluxFactor w u) (g := directional v w) (v := v)
      hfirst hsecond hflux (fun x _ => ((hw x).mul (hu x)).mul (hu x))
      (fun x _ => hdw x)
  have flux (x : E) : directional v (fluxFactor w u) x =
      2*w x*u x*directional v u x + u x^2*directional v w x := by
    change directional v (fun y => (fun z => w z*u z) y * u y) x = _
    rw [directional_mul v (f := fun z => w z*u z) (g := u) ((hw x).mul (hu x)) (hu x),
        directional_mul v (hw x) (hu x)]
    ring
  calc
    _ = ∫ x, (w x^2 * directional v u x^2 +
          directional v (fluxFactor w u) x * directional v w x) +
          fluxFactor w u x * directional v (directional v w) x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [directional_mul v (hw x) (hu x), flux]
      unfold fluxFactor
      field_simp
      ring
    _ = _ := by
      have split := integral_add (hkin.add hfirst) hsecond
      simp only [Pi.add_apply] at split
      rw [split, integral_add hkin hfirst, parts]
      ring
end Form

/-- The exact one-dimensional radial measure factor used after bounding the
Gaussian density and radial Jacobian on a unit annulus. -/
theorem sin_sq_unit_interval (a k : ℝ) (hk : 2 ≤ k) :
    1/4 ≤ ∫ r in a..a+1, Real.sin (k*r)^2 := by
  have hkpos : 0 < k := by linarith
  let P := fun r : ℝ => r/2 - Real.sin ((2*k)*r)/(4*k)
  have hd (r : ℝ) : HasDerivAt P (Real.sin (k*r)^2) r := by
    have h := ((hasDerivAt_id r).div_const 2).sub
      (((hasDerivAt_id r).const_mul (2*k)).sin.div_const (4*k))
    have slope : Real.sin (k*r)^2 =
        1/2 - Real.cos ((2*k)*r) * (2*k*1) / (4*k) := by
      rw [Real.sin_sq_eq_half_sub]
      simp only [mul_one, ← mul_assoc]
      field_simp [hkpos.ne']
      ring
    rw [slope]
    exact h
  have hc : Continuous (fun r : ℝ => Real.sin (k*r)^2) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := a+1) (fun r _ => hd r) (hc.intervalIntegrable a (a+1))
  have identity :
      4*k*(∫ r in a..a+1, Real.sin (k*r)^2) =
      2*k-Real.sin ((2*k)*(a+1))+Real.sin ((2*k)*a) := by
    rw [hftc]
    dsimp [P]
    field_simp [hkpos.ne']
    ring
  by_contra! bad
  have contra := mul_lt_mul_of_pos_left bad (show 0 < 4*k by linarith)
  nlinarith [Real.sin_le_one ((2*k)*(a+1)), Real.neg_one_le_sin ((2*k)*a)]

/-- Logarithm of the exterior comparison amplitude at the specified radius.
No evaluation of exp(10^18) is needed. -/
theorem exterior_margin (q : ℝ) (q0 : 100000 ≤ q) (q1 : q ≤ 100001) :
    3/4 * Real.log Real.pi + q^2/2 + Real.log q/10000000
       - (10:ℝ)^18/10000000 < -Real.log 2 := by
  have hpi := Real.log_le_sub_one_of_pos Real.pi_pos
  have hq := Real.log_le_sub_one_of_pos (show 0 < q by linarith)
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hs := mul_self_le_mul_self (show 0 ≤ q by linarith) q1
  nlinarith [Real.pi_lt_four]

/-- Numerical bounds on the two closed-form Gaussian moments in the
variational certificate, now evaluated with mathlib's real π and square root. -/
theorem gaussian_constants :
    32*(2/3-2/Real.pi) ≤ 1 ∧ (11:ℝ)/50 ≤ Real.sqrt ((2/Real.pi)/12) := by
  have lower : (7:ℝ)/11 ≤ 2/Real.pi := (le_div_iff₀ Real.pi_pos).2 (by
    linarith [Real.pi_lt_d4])
  constructor
  · linarith
  · have hs := Real.sq_sqrt (show 0 ≤ (2/Real.pi)/12 by positivity)
    have h0 := Real.sqrt_nonneg ((2/Real.pi)/12)
    by_contra! bad
    have prod := mul_pos (sub_pos.mpr bad)
      (show 0 < 11/50 + Real.sqrt ((2/Real.pi)/12) by linarith)
    nlinarith

#print axioms ground_transform
#print axioms sin_sq_unit_interval
#print axioms exterior_margin
#print axioms gaussian_constants
end ContinuumForms
