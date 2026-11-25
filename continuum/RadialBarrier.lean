import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The exterior supersolution for the three-dimensional oscillator. -/

noncomputable section
open Set Filter
open scoped Topology

namespace HFExterior

def radialBarrier (q α r : ℝ) : ℝ :=
  Real.exp ((q ^ 2 - r ^ 2) / 2 + α * (Real.log q - Real.log r))

theorem barrier_boundary (q α : ℝ) : radialBarrier q α q = 1 := by
  simp [radialBarrier]

theorem barrier_pos (q α r : ℝ) : 0 < radialBarrier q α r :=
  Real.exp_pos _

private theorem barrier_log_deriv {q α r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (q ^ 2 - t ^ 2) / 2 + α * (Real.log q - Real.log t))
      (-r - α / r) r := by
  apply ((((hasDerivAt_const r (q ^ 2)).sub ((hasDerivAt_id r).pow 2)).div_const 2).add
    (((hasDerivAt_const r (Real.log q)).sub (Real.hasDerivAt_log hr.ne')).const_mul α)).congr_deriv
  simp [div_eq_mul_inv]
  ring

theorem barrier_hasDerivAt {q α r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialBarrier q α) ((-r - α / r) * radialBarrier q α r) r := by
  apply (barrier_log_deriv (q := q) (α := α) hr).exp.congr_deriv
  exact mul_comm _ _

private theorem logSlope_hasDerivAt {α r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => -t - α / t) (-1 + α / r ^ 2) r := by
  apply ((hasDerivAt_id r).neg.sub
    ((hasDerivAt_const r α).div (hasDerivAt_id r) hr.ne')).congr_deriv
  simp [div_eq_mul_inv]

theorem barrier_first_hasDerivAt {q α r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => (-t - α / t) * radialBarrier q α t)
      (((-r - α / r) ^ 2 - 1 + α / r ^ 2) * radialBarrier q α r) r := by
  apply ((logSlope_hasDerivAt (α := α) hr).mul
    (barrier_hasDerivAt (q := q) (α := α) hr)).congr_deriv
  ring

theorem barrier_second {q α r : ℝ} (hr : 0 < r) :
    deriv (deriv (radialBarrier q α)) r =
      ((-r - α / r) ^ 2 - 1 + α / r ^ 2) * radialBarrier q α r := by
  have hnear : deriv (radialBarrier q α) =ᶠ[nhds r]
      (fun t => (-t - α / t) * radialBarrier q α t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (barrier_hasDerivAt ht).deriv
  exact hnear.deriv_eq.trans (barrier_first_hasDerivAt hr).deriv

/-- The operator uses the radial three-dimensional Laplacian and the oscillator shift -3/2. -/
def oscillatorRadial (z : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(deriv (deriv z) r + 2 / r * deriv z r) / 2 + (r ^ 2 / 2 - 3 / 2) * z r

theorem oscillator_barrier {q α r : ℝ} (hr : 0 < r) :
    oscillatorRadial (radialBarrier q α) r =
      (-α + α * (1 - α) / (2 * r ^ 2)) * radialBarrier q α r := by
  rw [oscillatorRadial, barrier_second hr, (barrier_hasDerivAt hr).deriv]
  field_simp [hr.ne']
  ring

theorem exterior_supersolution {q α r d j : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hmargin : α + j ≤ d) :
    0 ≤ oscillatorRadial (radialBarrier q α) r + (d - j) * radialBarrier q α r := by
  rw [oscillator_barrier hr, ← add_mul]
  apply mul_nonneg _ (barrier_pos q α r).le
  have hterm : 0 ≤ α * (1 - α) / (2 * r ^ 2) := by positivity
  linarith

end HFExterior
