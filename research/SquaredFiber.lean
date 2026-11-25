import Mathlib.Analysis.InnerProductSpace.Calculus
import GaussianFlux
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The radial squared-density test identity and the flux integrability estimate.
The real Hilbert space can be the angular and residual-electron L² fiber. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace HFExterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem squared_fiber_pairing {U : ℝ → E} {h : ℝ → ℝ} {du : E} {dh r : ℝ}
    (hU : HasDerivAt U du r) (hh : HasDerivAt h dh r) :
    ⟪du, deriv (fun s => h s • U s) r⟫_ℝ/2 =
      h r*‖du‖^2/2 + deriv (fun s => ‖U s‖^2) r * dh/4 := by
  change ⟪du, deriv (h • U) r⟫_ℝ/2 = _
  rw [(hh.smul hU).deriv,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hU.norm_sq.deriv,real_inner_comm (U r) du]
  ring

theorem squared_fiber_drop_positive {U : ℝ → E} {h : ℝ → ℝ} {du : E} {dh r p : ℝ}
    (hU : HasDerivAt U du r) (hh : HasDerivAt h dh r) (hp : 0 ≤ p) (hh0 : 0 ≤ h r) :
    p*(deriv (fun s => ‖U s‖^2) r*dh/4) ≤ p*(⟪du, deriv (fun s => h s • U s) r⟫_ℝ/2) := by
  rw [squared_fiber_pairing hU hh]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (div_nonneg
    (mul_nonneg hh0 (sq_nonneg _)) (by norm_num))) hp

private theorem integrable_inner_of_memLp {μ : Measure ℝ} {f g : ℝ → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun r => ⟪f r,g r⟫_ℝ) μ := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with r hfr hgr
  rw [hfr,hgr]

/-- In physical variables, rU is square integrable by normalization, r U' by kinetic
energy, and r² U by the oscillator moment. These conditions control the transformed
flux in ordinary dr measure even though the transformed marginal may grow. -/
theorem squared_marginal_flux_integrable {q : ℝ} (U dU : ℝ → E)
    (hU : ∀ᵐ r ∂volume.restrict (Ioi q), HasDerivAt U (dU r) r)
    (mass : MemLp (fun r => r • U r) 2 (volume.restrict (Ioi q)))
    (gradient : MemLp (fun r => r • dU r) 2 (volume.restrict (Ioi q)))
    (moment : MemLp (fun r => r^2 • U r) 2 (volume.restrict (Ioi q))) :
    IntegrableOn (fun r => r^2*(deriv (fun s => ‖U s‖^2) r+2*r*‖U r‖^2)) (Ioi q) := by
  have h₁ := (integrable_inner_of_memLp mass gradient).const_mul 2
  have h₂ := (integrable_inner_of_memLp mass moment).const_mul 2
  apply (h₁.add h₂).congr
  filter_upwards [hU] with r hr
  simp only [Pi.add_apply, real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hr.norm_sq.deriv]
  ring

def densityScale : ℝ := Real.exp (3/2*Real.log Real.pi)
def squaredGaussianRatio (U : ℝ → E) (r : ℝ) : ℝ :=
  densityScale*Real.exp (r^2)*‖U r‖^2

omit [InnerProductSpace ℝ E] in
theorem squaredGaussianRatio_eq (U : ℝ → E) (r : ℝ) :
    squaredGaussianRatio U r = ‖U r‖^2 / gaussianRadial r ^ 2 := by
  apply (eq_div_iff (sq_pos_of_pos (show 0 < gaussianRadial r from Real.exp_pos _)).ne').mpr
  unfold squaredGaussianRatio densityScale gaussianRadial
  have ht : Real.exp (3/2*Real.log Real.pi)*Real.exp (r^2)*
      (Real.exp (-r^2/2-3/4*Real.log Real.pi))^2 = 1 := by
    rw [pow_two (Real.exp (-r^2/2-3/4*Real.log Real.pi))]
    simp only [← Real.exp_add]
    rw [show 3/2*Real.log Real.pi + r^2 +
      ((-r^2/2-3/4*Real.log Real.pi)+(-r^2/2-3/4*Real.log Real.pi)) = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (3/2*Real.log Real.pi)*Real.exp (r^2)*
        (Real.exp (-r^2/2-3/4*Real.log Real.pi))^2)*‖U r‖^2 := by ring
    _ = _ := by rw [ht,one_mul]

theorem transformed_squared_flux {U : ℝ → E} {du : E} {r : ℝ} (hU : HasDerivAt U du r) :
    radialJacobian r * deriv (squaredGaussianRatio U) r =
      densityScale * (r^2*(deriv (fun s => ‖U s‖^2) r+2*r*‖U r‖^2)) := by
  have hsq : HasDerivAt (fun t : ℝ => t^2) (2*r) r := by
    simpa using hasDerivAt_pow 2 r
  have he : HasDerivAt (fun t : ℝ => Real.exp (t^2)) (Real.exp (r^2)*(2*r)) r := hsq.exp
  have hd := (he.const_mul densityScale).mul hU.norm_sq
  simp only [Pi.mul_def] at hd
  change radialJacobian r * deriv (fun t => densityScale*Real.exp (t^2)*‖U t‖^2) r = _
  rw [hd.deriv,hU.norm_sq.deriv]
  simp only [radialJacobian,Real.exp_neg]
  field_simp [(Real.exp_pos (r^2)).ne']
  ring

theorem transformed_squared_flux_integrable {q : ℝ} (U dU : ℝ → E)
    (hU : ∀ᵐ r ∂volume.restrict (Ioi q), HasDerivAt U (dU r) r)
    (mass : MemLp (fun r => r • U r) 2 (volume.restrict (Ioi q)))
    (gradient : MemLp (fun r => r • dU r) 2 (volume.restrict (Ioi q)))
    (moment : MemLp (fun r => r^2 • U r) 2 (volume.restrict (Ioi q))) :
    IntegrableOn (fun r => radialJacobian r * deriv (squaredGaussianRatio U) r) (Ioi q) := by
  apply ((squared_marginal_flux_integrable U dU hU mass gradient moment).const_mul densityScale).congr
  filter_upwards [hU] with r hr
  exact (transformed_squared_flux hr).symm

end HFExterior
