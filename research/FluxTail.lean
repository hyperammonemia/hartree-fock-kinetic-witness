import GaussianFlux
import FluxTests

/-! The signed squared-density difference and the final comparison with the fixed Gaussian. -/
noncomputable section
open MeasureTheory Set
namespace HFExterior

def clampedDensityExcess (q : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  let r := max q t
  a r / (gaussianRadial r)^2 - densityBarrier q (1/10000000) r

def densityFormPotential (q : ℝ) (a V : ℝ → ℝ) (r : ℝ) : ℝ :=
  4 * radialJacobian r * V r * clampedDensityExcess q a r

/-- Only fixed compact, nonnegative scalar multipliers enter the weak-form hypothesis.
The input a is the angularly averaged physical squared marginal. -/
theorem squared_marginal_shell {q : ℝ} (a V : ℝ → ℝ) (hq0 : 100000 ≤ q) (hq1 : q ≤ 100001)
    (htrace : a q ≤ 1) (hV : ∀ r, q < r → 0 ≤ V r)
    (hc : Continuous (clampedDensityExcess q a))
    (hac : ∀ l b : ℝ, q ≤ l → q ≤ b → AbsolutelyContinuousOnInterval (clampedDensityExcess q a) l b)
    (hf : IntegrableOn (FluxHats.flux (exteriorReciprocal q) (clampedDensityExcess q a)) (Ioi q))
    (htest : FluxHats.testsOnPieces q (FluxHats.flux (exteriorReciprocal q) (clampedDensityExcess q a))
      (densityFormPotential q a V)) {r : ℝ} (har : 0 ≤ a r) (hqr : q ≤ r)
    (hr : Real.exp ((10 : ℝ)^18) ≤ r) : Real.sqrt (a r) < gaussianRadial r/2 := by
  have hq : 0 < q := by linarith
  have hb : clampedDensityExcess q a q ≤ 0 := by
    simp only [clampedDensityExcess,max_self,sub_nonpos]
    apply (div_le_iff₀ (sq_pos_of_pos (show 0 < gaussianRadial q from Real.exp_pos _))).mpr
    rwa [mul_comm (densityBarrier q _ q),density_boundary]
  have hp : ∀ t, q < t → 0 ≤ clampedDensityExcess q a t → 0 ≤ densityFormPotential q a V t := by
    intro t ht hv
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (jacobian_pos (hq.trans ht)).le) (hV t ht)) hv
  have z := FluxHats.maximum_of_multipliers (exteriorReciprocal_continuous hq) (exteriorReciprocal_pos hq)
    hc hac hb hf hp htest r hqr
  simp only [clampedDensityExcess,max_eq_right hqr,sub_nonpos] at z
  exact density_tail_from_ratio hq0 hq1 hr har z

end HFExterior
