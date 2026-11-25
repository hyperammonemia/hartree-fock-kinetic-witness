import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! An explicit finite-frequency averaging estimate on the annulus of the radial witness. -/

open MeasureTheory Set
open scoped Interval

namespace KineticAmplification

noncomputable section

/-- The phase at the start of the interval is arbitrary. The lower bound is uniform in it. -/
theorem sin_sq_unit_window (s k : ℝ) (hk : 2 ≤ k) :
    (1 : ℝ) / 4 ≤ ∫ x in s..s+1, Real.sin (k * x) ^ 2 := by
  have hkpos : 0 < k := by linarith
  let F := fun x : ℝ => x / 2 - Real.sin (2 * k * x) / (4 * k)
  have hder (x : ℝ) : HasDerivAt F (Real.sin (k * x) ^ 2) x := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * k * t) (2 * k) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * k)
    have hsin := (Real.hasDerivAt_sin (2 * k * x)).comp x hlin
    have h := ((hasDerivAt_id x).div_const 2).sub (hsin.div_const (4 * k))
    have slope : Real.sin (k * x) ^ 2 =
        1 / 2 - (Real.cos (2 * k * x) * (2 * k)) / (4 * k) := by
      rw [Real.sin_sq_eq_half_sub]
      rw [show 2 * (k * x) = 2 * k * x by ring]
      field_simp [hkpos.ne']
      ring
    rw [slope]
    exact h
  have hcont : Continuous (fun x : ℝ => Real.sin (k * x) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable s (s + 1))]
  have hd : (Real.sin (2 * k * (s + 1)) - Real.sin (2 * k * s)) / (4 * k) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith [Real.sin_le_one (2 * k * (s + 1)), Real.neg_one_le_sin (2 * k * s)]
  calc
    (1 : ℝ) / 4 ≤ 1 / 2 -
        (Real.sin (2 * k * (s + 1)) - Real.sin (2 * k * s)) / (4 * k) := by linarith
    _ = F (s + 1) - F s := by dsimp [F]; ring

/-- A continuous density lower bound on the radial annulus transfers to its oscillatory mass. -/
theorem weighted_sin_sq_unit_window (s k m : ℝ) (g : ℝ → ℝ)
    (hk : 2 ≤ k) (hm : 0 ≤ m) (hg : Continuous g)
    (hlo : ∀ x ∈ Icc s (s + 1), m ≤ g x) :
    m / 4 ≤ ∫ x in s..s+1, g x * Real.sin (k * x) ^ 2 := by
  have hs : s ≤ s + 1 := by linarith
  have hc : Continuous (fun x : ℝ => Real.sin (k * x) ^ 2) := by fun_prop
  calc
    m / 4 = m * (1 / 4) := by ring
    _ ≤ m * (∫ x in s..s+1, Real.sin (k * x) ^ 2) :=
      mul_le_mul_of_nonneg_left (sin_sq_unit_window s k hk) hm
    _ = ∫ x in s..s+1, m * Real.sin (k * x) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := intervalIntegral.integral_mono_on hs
      ((continuous_const.mul hc).intervalIntegrable s (s+1))
      ((hg.mul hc).intervalIntegrable s (s+1))
      (fun x hx => mul_le_mul_of_nonneg_right (hlo x hx) (sq_nonneg _))

#print axioms KineticAmplification.weighted_sin_sq_unit_window

end

end KineticAmplification
