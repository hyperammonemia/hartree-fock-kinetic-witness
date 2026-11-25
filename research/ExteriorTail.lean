import RadialBarrier
import WeakRadial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Application to the Gaussian and the fixed annulus of the radial witness. -/
open Set MeasureTheory
open scoped Interval
noncomputable section
namespace HFExterior

def gaussianRadial (r : ℝ) : ℝ := Real.exp (-r ^ 2 / 2 - 3 / 4 * Real.log Real.pi)

/-- A common continuous extension of a physical exterior difference to the left of its boundary. -/
def exteriorDifference (q : ℝ) (s w : ℝ → ℝ) (r : ℝ) : ℝ :=
  s (max q r) - w (max q r)

theorem exists_trace {a : ℝ} (ha : 1 ≤ a) {s : ℝ → ℝ}
    (hs : ContinuousOn s (Icc a (a+1)))
    (hm : (∫ r in a..a+1, 4 * Real.pi * r ^ 2 * s r ^ 2) ≤ 1) :
    ∃ q ∈ Icc a (a+1), s q ≤ 1 := by
  by_contra! bad
  have hab : a ≤ a+1 := by linarith
  have hi : IntervalIntegrable (fun r => 4 * Real.pi * r ^ 2 * s r ^ 2) volume a (a+1) :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (((continuousOn_const.mul (continuousOn_id.pow 2))).mul (hs.pow 2))
  have lower := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (b := a+1) (a := a) (c := (2 : ℝ))) hi
    (fun r hr => show (2 : ℝ) ≤ 4 * Real.pi * r ^ 2 * s r ^ 2 from by
      have hr1 : 1 ≤ r := ha.trans hr.1
      have hs1 : 1 < s r := bad r hr
      have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r-1)]
      have hs2 : 1 ≤ s r ^ 2 := by nlinarith [sq_nonneg (s r-1)]
      calc
        2 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
        _ ≤ 4 * Real.pi * r^2 := le_mul_of_one_le_right (by positivity) hr2
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hs2)
  simp at lower
  linarith

theorem explicit_barrier_tail {q r : ℝ} (hq0 : 100000 ≤ q) (hq1 : q ≤ 100001)
    (hr : Real.exp ((10 : ℝ)^18) ≤ r) :
    radialBarrier q (1/10000000) r < gaussianRadial r / 2 := by
  have hlog : (10:ℝ)^18 ≤ Real.log r := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos ((10:ℝ)^18)) hr
  have hp := Real.log_le_sub_one_of_pos Real.pi_pos
  have hq := Real.log_le_sub_one_of_pos (show 0 < q by linarith)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hsq := mul_self_le_mul_self (show 0 ≤ q by linarith) hq1
  unfold radialBarrier gaussianRadial
  calc
    _ < Real.exp (-r ^ 2 / 2 - 3 / 4 * Real.log Real.pi - Real.log 2) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_lt_four])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (show (0:ℝ) < 2 by norm_num)]

/-- The two function-space hypotheses are the finite exterior form energy and the weak
radial subsolution for the true marginal minus the explicit classical barrier. -/
theorem marginal_tail_of_weak_difference {q : ℝ} {V s : ℝ → ℝ}
    (hq0 : 100000 ≤ q) (hq1 : q ≤ 100001) (htrace : s q ≤ 1)
    (hV : ∀ r, q < r → 0 < V r)
    (hform : ExteriorProfile q V (exteriorDifference q s (radialBarrier q (1/10000000))))
    (hweak : weakExteriorSubsolution q V
      (exteriorDifference q s (radialBarrier q (1/10000000)))) {r : ℝ}
    (hqr : q < r) (hr : Real.exp ((10 : ℝ)^18) ≤ r) :
    s r < gaussianRadial r / 2 := by
  have hboundary : exteriorDifference q s (radialBarrier q (1/10000000)) q ≤ 0 := by
    simpa only [exteriorDifference, max_self, barrier_boundary] using sub_nonpos.mpr htrace
  have h := weak_radial_maximum (by linarith : 0 ≤ q) hV hform hboundary hweak r hqr
  simp only [exteriorDifference, max_eq_right hqr.le, sub_nonpos] at h
  exact h.trans_lt (explicit_barrier_tail hq0 hq1 hr)

end HFExterior
