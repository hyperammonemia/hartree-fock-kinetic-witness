import GaussianCoulomb
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The scalar change of variables in the positive Gaussian representation
of the three-dimensional Newton potential. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CoulombSubstitution

def compress (t : ℝ) := t / Real.sqrt (1+t^2)
def jac (t : ℝ) := 1 / (Real.sqrt (1+t^2))^3
def profile (r t : ℝ) := Real.exp (-((r * compress t)^2)) * jac t

theorem derivative (t : ℝ) : HasDerivAt compress (jac t) t := by
  have hp : 0 < 1+t^2 := by positivity
  have hs := Real.sqrt_pos.2 hp
  let s := Real.sqrt (1+t^2)
  have hd : HasDerivAt (fun y : ℝ => Real.sqrt (1+y^2)) (t/s) t := by
    convert (((hasDerivAt_id t).pow 2).const_add 1).sqrt hp.ne' using 1
    · funext y; simp
    · change t/s = (2*t^(2-1:ℕ)*1)/(2*s)
      ring
  have eq : s*s-t^2=1 := by
    have h : s^2=1+t^2 := Real.sq_sqrt hp.le
    nlinarith
  convert (hasDerivAt_id t).div hd hs.ne' using 1
  · funext y; simp [compress]
  · change 1/s^3=(1*s-t*(t/s))/s^2
    calc
      _ = (s*s-t^2)/s^3 := by rw [eq]
      _ = _ := by field_simp [show s ≠ 0 from hs.ne']; ring

theorem limit : Tendsto compress atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h : Tendsto (fun t : ℝ => (Real.sqrt (1+t⁻¹^2))⁻¹) atTop (𝓝 1) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ((ht.pow 2).const_add 1)
    simpa using hs.inv₀ (by norm_num)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have hd : 0 < 1+t^2 := by positivity
  have he : 1+t⁻¹^2=(1+t^2)/t^2 := by field_simp; ring
  rw [he, Real.sqrt_div hd.le, Real.sqrt_sq ht.le]
  simp [compress, inv_div]

private def primitive (r x : ℝ) := ∫ u in (0:ℝ)..x, Real.exp (-((r*u)^2))

theorem primitive_deriv (r x : ℝ) :
    HasDerivAt (primitive r) (Real.exp (-((r*x)^2))) x := by
  have hc : Continuous (fun u : ℝ => Real.exp (-((r*u)^2))) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem profile_integrable (r : ℝ) : IntegrableOn (profile r) (Ioi (0:ℝ)) := by
  have hd (t : ℝ) : HasDerivAt (fun s => primitive r (compress s)) (profile r t) t :=
    (primitive_deriv r (compress t)).comp t (derivative t)
  apply integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hd t)
  · intro t _; unfold profile jac; positivity
  · exact (primitive_deriv r 1).continuousAt.tendsto.comp limit

theorem profile_integral (r : ℝ) :
    (∫ t in Ioi (0:ℝ), profile r t) = ∫ u in (0:ℝ)..1, Real.exp (-((r*u)^2)) := by
  have hd (t : ℝ) : HasDerivAt (fun s => primitive r (compress s)) (profile r t) t :=
    (primitive_deriv r (compress t)).comp t (derivative t)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (a:=0) (fun t _ => hd t)
    (profile_integrable r) ((primitive_deriv r 1).continuousAt.tendsto.comp limit)
  simpa [compress,primitive] using hi

theorem finite_profile_bound (r : ℝ) :
    (∫ u in (0:ℝ)..1, Real.exp (-((r*u)^2))) ≤ 1 := by
  calc
    _ ≤ ∫ _ : ℝ in (0:ℝ)..1, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-((r*u)^2)))).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro x _; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    _ = _ := by simp

#print axioms profile_integral
#print axioms finite_profile_bound
end CoulombSubstitution

