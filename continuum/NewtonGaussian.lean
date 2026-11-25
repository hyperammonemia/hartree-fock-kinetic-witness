import FinitePotential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Positive Gaussian-integral representation for the Coulomb kernel and
evaluation of its inner Gaussian convolution in three dimensions. -/
noncomputable section
open Set MeasureTheory
namespace NewtonGaussian
abbrev X := FinitePotential.Position

theorem kernel_as_gaussians (r : ℝ) (hr : 0 < r) :
    (2/Real.sqrt Real.pi) * (∫ t in Ioi (0:ℝ), Real.exp (-((r*t)^2))) = r⁻¹ := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-(t^2))) 0 hr
  have hg : (∫ t in Ioi (0:ℝ), Real.exp (-(t^2))) = Real.sqrt Real.pi/2 := by
    simpa using integral_gaussian_Ioi (1:ℝ)
  simp only [mul_zero, smul_eq_mul] at h
  rw [h,hg]
  field_simp [hr.ne', (Real.sqrt_pos.2 Real.pi_pos).ne']

private theorem completed (x y : X) (a : ℝ) (ha : 0 ≤ a) :
    -(‖y‖^2)-a*‖x-y‖^2 =
    -(a/(1+a))*‖x‖^2 -(1+a)*‖y-(a/(1+a)) • x‖^2 := by
  have hp : 0 < 1+a := by linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hp.le), real_inner_smul_right,
    real_inner_comm y x]
  field_simp [hp.ne']; ring

theorem gaussian_convolution (x : X) (a : ℝ) (ha : 0 ≤ a) :
    (∫ y : X, Real.exp (-(‖y‖^2)) * Real.exp (-a*‖x-y‖^2)) =
    Real.exp (-(a/(1+a))*‖x‖^2) * (Real.pi/(1+a))^((3:ℝ)/2) := by
  have pos : 0<1+a := by linarith
  let c := (a/(1+a)) • x
  let f := fun z : X => Real.exp (-(1+a)*‖z‖^2)
  calc
    _ = ∫ y, Real.exp (-(a/(1+a))*‖x‖^2)*f (y-c) := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [f,c]
      rw [← Real.exp_add, ← Real.exp_add]
      exact congrArg Real.exp (by simpa only [sub_eq_add_neg, neg_mul] using completed x y a ha)
    _ = _ := by
      rw [integral_const_mul, integral_sub_right_eq_self]
      have hv := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := X) pos
      have hval : (∫ z : X, f z) = (Real.pi/(1+a)) ^ ((3:ℝ)/2) := by
        simpa [f, finrank_euclideanSpace_fin] using hv
      rw [hval]

#print axioms kernel_as_gaussians
#print axioms gaussian_convolution
end NewtonGaussian
