import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The Gaussian Hartree second moment in the reference oscillator. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaussianCoulomb

def gauss (r : ℝ) := Real.exp (-(r^2))
def erf (r : ℝ) := (2/Real.sqrt Real.pi)*(∫ x in (0:ℝ)..r, gauss x)

private theorem hcont : Continuous gauss := by unfold gauss; fun_prop

theorem erf_derivative (r : ℝ) :
    HasDerivAt erf ((2/Real.sqrt Real.pi)*gauss r) r :=
  (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 r)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).const_mul _

theorem erf_limit : Tendsto erf atTop (𝓝 1) := by
  have hi : Integrable gauss := by
    unfold gauss
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)
  have hg : (∫ x in Ioi (0:ℝ), gauss x) = Real.sqrt Real.pi/2 := by
    simpa [gauss] using integral_gaussian_Ioi (1:ℝ)
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hi.integrableOn
    (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop)
  change Tendsto (fun x => (2/Real.sqrt Real.pi) * (∫ z in (0:ℝ)..x, gauss z)) atTop (𝓝 1)
  have hc := ht.const_mul (2/Real.sqrt Real.pi)
  rw [hg, show (2/Real.sqrt Real.pi)*(Real.sqrt Real.pi/2)=1 by
    field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']] at hc
  exact hc

/-- After angular integration and insertion of the Newton potential erf(r)/r,
the r² Jacobian cancels the squared denominator. This evaluates the remaining
half-line integral, including its normalization, without a moment assumption. -/
theorem second_moment :
    (∫ r in Ioi (0:ℝ), (4/Real.sqrt Real.pi)*gauss r*(erf r)^2) = 2/3 := by
  let F := fun r => (2/3:ℝ) * erf r ^ 3
  have hd (r : ℝ) : HasDerivAt F ((4/Real.sqrt Real.pi)*gauss r*(erf r)^2) r := by
    convert ((erf_derivative r).pow 3).const_mul (2/3:ℝ) using 1; ring
  have endlim : Tendsto F atTop (𝓝 (2/3:ℝ)) := by
    simpa [F] using (erf_limit.pow 3).const_mul (2/3:ℝ)
  have pos (r : ℝ) (_ : r ∈ Ioi (0:ℝ)) : 0 ≤ (4/Real.sqrt Real.pi)*gauss r*(erf r)^2 := by
    unfold gauss; positivity
  have val := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hd r) pos endlim
  simpa [F, erf] using val

#print axioms second_moment
end GaussianCoulomb
