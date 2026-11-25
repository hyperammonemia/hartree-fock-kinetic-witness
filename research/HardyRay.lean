import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The one-dimensional radial identity behind the translated three-dimensional
Coulomb–Hardy form bound. It allows a nonzero trace at the Coulomb center. -/
open MeasureTheory
open scoped Interval
noncomputable section
namespace HFExterior

theorem radial_hardy_identity {b : ℝ} {f df : ℝ → ℝ}
    (hf : ∀ r, HasDerivAt f (df r) r) (hdf : Continuous df) (hb : f b = 0) :
    (∫ r in 0..b, (2 * r * df r + f r)^2) =
      4 * (∫ r in 0..b, r^2 * (df r)^2) - ∫ r in 0..b, (f r)^2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun r => (hf r).continuousAt
  let L := fun r => (2 * r * df r + f r)^2
  let R := fun r => 4 * (r^2 * (df r)^2) - (f r)^2
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hder (r : ℝ) : HasDerivAt (fun t => 2 * t * f t ^ 2) (L r - R r) r := by
    apply (((hasDerivAt_id r).const_mul 2).mul ((hf r).pow 2)).congr_deriv
    dsimp [L, R]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
    (fun r _ => hder r) ((hL.sub hR).intervalIntegrable 0 b)
  rw [intervalIntegral.integral_sub (hL.intervalIntegrable 0 b) (hR.intervalIntegrable 0 b)] at hFTC
  simp only [hb, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, sub_self] at hFTC
  have heq : (∫ r in 0..b, L r) = ∫ r in 0..b, R r := by linarith
  change (∫ r in 0..b, L r) = _
  rw [heq]
  dsimp only [R]
  have h4 : Continuous (fun r : ℝ => 4 * (r^2 * (df r)^2)) := by fun_prop
  rw [intervalIntegral.integral_sub (h4.intervalIntegrable _ _) ((hfc.pow 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

theorem radial_hardy {b : ℝ} {f df : ℝ → ℝ} (hb0 : 0 ≤ b)
    (hf : ∀ r, HasDerivAt f (df r) r) (hdf : Continuous df) (hb : f b = 0) :
    (∫ r in 0..b, (f r)^2) ≤ 4 * ∫ r in 0..b, r^2 * (df r)^2 := by
  have hpos := intervalIntegral.integral_nonneg hb0
    (f := fun r => (2 * r * df r + f r)^2) (fun _ _ => sq_nonneg _)
  rw [radial_hardy_identity hf hdf hb] at hpos
  linarith

end HFExterior
