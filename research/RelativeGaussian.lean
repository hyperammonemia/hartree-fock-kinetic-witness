import NewtonGaussian
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! The difference of the two three-dimensional Gaussian electron coordinates
has the standard three-dimensional Gaussian law. The statement is an
identity of Bochner integrals for nonnegative measurable observables. -/
noncomputable section
open MeasureTheory
namespace RelativeGaussian
abbrev X := FinitePotential.Position
def rho (x : X) := Real.exp (-(‖x‖^2))
def relative (z : X) := Real.exp (-(1/2:ℝ)*‖z‖^2)
def c := (Real.pi/2)^((3:ℝ)/2)

private theorem gaussian_slice (z : X) :
    (∫ y : X, rho y*rho (z+y)) = c*relative z := by
  have h := NewtonGaussian.gaussian_convolution (-z) 1 (by norm_num)
  calc
    _ = ∫ y : X, Real.exp (-‖y‖^2)*Real.exp (-1*‖-z-y‖^2) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show -z-y = -(z+y) by abel,norm_neg]
      simp [rho]
    _ = _ := by
      rw [h,norm_neg]
      unfold c relative
      norm_num only [one_add_one_eq_two]
      exact mul_comm _ _

theorem difference_integral (K : X → ℝ) (hm : Measurable K) (h0 : ∀ z, 0 ≤ K z)
    (hi : Integrable (fun z => K z*relative z)) :
    (∫ h : X × X, K (h.1-h.2)*rho h.1*rho h.2) =
      c*(∫ z : X, K z*relative z) := by
  let F := fun a : X × X => K a.1*(rho a.2*rho (a.1+a.2))
  have hr : Continuous rho := by unfold rho; fun_prop
  have hmF : Measurable F := (hm.comp measurable_fst).mul
    ((hr.measurable.comp measurable_snd).mul (hr.measurable.comp (measurable_fst.add measurable_snd)))
  have hpos (a : X × X) : 0 ≤ F a :=
    mul_nonneg (h0 _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have slice (z : X) : (∫ y, F (z,y)) = c*(K z*relative z) := by
    change (∫ y, K z*(rho y*rho (z+y))) = _
    rw [integral_const_mul,gaussian_slice]; ring
  have Fi : Integrable F (volume.prod volume) := by
    apply (integrable_prod_iff hmF.aestronglyMeasurable).2
    constructor
    · filter_upwards with z
      have hg : Integrable (fun y => rho y*rho (z+y)) := by
        by_contra hn
        have val := gaussian_slice z
        rw [integral_undef hn] at val
        exact (ne_of_gt (show 0<c*relative z by unfold c relative; positivity)) val.symm
      exact hg.const_mul (K z)
    · have e : (fun z : X => ∫ y : X, ‖F (z,y)‖) = fun z => c*(K z*relative z) := by
        funext z
        simp only [Real.norm_of_nonneg (hpos _),slice]
      rw [e]
      exact hi.const_mul c
  let S := fun a : X × X => (a.1-a.2,a.2)
  have mp : MeasurePreserving S (volume.prod volume) (volume.prod volume) :=
    measurePreserving_sub_prod volume volume
  have transfer := integral_map mp.measurable.aemeasurable
    (hmF.aestronglyMeasurable (μ := Measure.map S (volume.prod volume)))
  rw [mp.map_eq] at transfer
  calc
    _ = ∫ z : X × X, F (S z) ∂(volume.prod volume) := by
      apply integral_congr_ae; filter_upwards with z
      simp [F,S,mul_comm,mul_left_comm,mul_assoc]
    _ = ∫ z : X × X, F z ∂(volume.prod volume) := transfer.symm
    _ = _ := by rw [integral_prod _ Fi]; simp_rw [slice]; rw [integral_const_mul]

#print axioms difference_integral
end RelativeGaussian
