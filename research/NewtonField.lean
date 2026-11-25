import NewtonGaussian
import CoulombSubstitution
import RadialConfiguration

/-! Evaluation of the normalized Newton potential of the fixed orbital's
Gaussian reference on the full three-dimensional configuration space. -/
noncomputable section
open MeasureTheory Set
namespace NewtonField
abbrev X := FinitePotential.Position
def density (y : X) := Real.exp (-(‖y‖^2))
def Z := Real.pi^((3:ℝ)/2)
def kernel (x : X) (t : ℝ) (y : X) := density y * Real.exp (-(t^2)*‖x-y‖^2)

theorem partition : (∫ y, density y) = Z := by
  simpa [density,Z,finrank_euclideanSpace_fin] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := X) (b := 1) (by norm_num)

private theorem inner_integral (x : X) (t : ℝ) :
    (∫ y, kernel x t y) = Z * CoulombSubstitution.profile ‖x‖ t := by
  have ht : 0 < 1+t^2 := by positivity
  have h := NewtonGaussian.gaussian_convolution x (t^2) (sq_nonneg t)
  change (∫ y : X, Real.exp (-(‖y‖^2))*Real.exp (-(t^2)*‖x-y‖^2)) = _
  rw [h,Real.div_rpow Real.pi_pos.le ht.le, Real.rpow_div_two_eq_sqrt 3 ht.le]
  have poweq : (Real.sqrt (1+t^2)) ^ (3:ℝ) = (Real.sqrt (1+t^2))^ (3:ℕ) := by norm_cast
  rw [poweq]
  unfold Z CoulombSubstitution.profile CoulombSubstitution.compress CoulombSubstitution.jac
  have hex : -(t^2/(1+t^2))*‖x‖^2 = -((‖x‖*(t/Real.sqrt (1+t^2)))^2) := by
    rw [mul_pow, div_pow,Real.sq_sqrt ht.le]; ring
  rw [hex]; ring

private theorem integrable_kernel (x : X) :
    Integrable (Function.uncurry (kernel x)) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hc : Continuous (Function.uncurry (kernel x)) := by
    unfold Function.uncurry kernel density; fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).2
  constructor
  · filter_upwards with t
    by_contra hn
    have hi := inner_integral x t
    rw [integral_undef hn] at hi
    have hp : 0 < Z*CoulombSubstitution.profile ‖x‖ t := by
      unfold Z CoulombSubstitution.profile CoulombSubstitution.jac
      positivity
    exact hp.ne' hi.symm
  · have hEq : (fun t => ∫ y, ‖Function.uncurry (kernel x) (t,y)‖) =
        (fun t => Z*CoulombSubstitution.profile ‖x‖ t) := by
      funext t
      convert inner_integral x t using 1
      apply integral_congr_ae
      filter_upwards with y
      exact Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    rw [hEq]
    exact (CoulombSubstitution.profile_integrable ‖x‖).const_mul Z

theorem field_integral (x : X) :
    RadialConfiguration.bareNewton x =
      (2/Real.sqrt Real.pi)*(∫ u in (0:ℝ)..1, Real.exp (-((‖x‖*u)^2))) := by
  have slice : ∀ᵐ y : X ∂volume, density y / ‖x-y‖ =
      (2/Real.sqrt Real.pi)*(∫ t in Ioi (0:ℝ), kernel x t y) := by
    filter_upwards [volume.ae_ne x] with y hy
    have h := NewtonGaussian.kernel_as_gaussians ‖x-y‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))
    have e (t : ℝ) : -(t^2)*‖x-y‖^2 = -((‖x-y‖*t)^2) := by ring
    simp only [kernel, e, integral_const_mul]
    rw [mul_left_comm, h, div_eq_mul_inv]
  have swap := integral_integral_swap (integrable_kernel x)
  have hZ : 0 < Z := Real.rpow_pos_of_pos Real.pi_pos _
  change (∫ y : X, density y / ‖x-y‖)/(∫ y, density y) = _
  rw [partition, integral_congr_ae slice,integral_const_mul,← swap]
  simp_rw [inner_integral]
  rw [integral_const_mul,CoulombSubstitution.profile_integral]
  field_simp [hZ.ne']

theorem uniform_bound (x : X) : RadialConfiguration.bareNewton x ≤ 2/Real.sqrt Real.pi := by
  rw [field_integral]
  simpa using mul_le_mul_of_nonneg_left (CoulombSubstitution.finite_profile_bound ‖x‖)
    (by positivity : 0 ≤ 2/Real.sqrt Real.pi)

theorem field_erf (x : X) (hx : x ≠ 0) :
    RadialConfiguration.bareNewton x = GaussianCoulomb.erf ‖x‖ / ‖x‖ := by
  rw [field_integral]
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    GaussianCoulomb.gauss (norm_ne_zero_iff.mpr hx)
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  change (2/Real.sqrt Real.pi)*(∫ u in (0:ℝ)..1, GaussianCoulomb.gauss (‖x‖*u)) = _
  rw [h]; unfold GaussianCoulomb.erf; ring

#print axioms field_integral
#print axioms uniform_bound
#print axioms field_erf
end NewtonField

