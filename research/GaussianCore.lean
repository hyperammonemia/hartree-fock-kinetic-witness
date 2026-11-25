import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

namespace GaussianCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem interval_schwarz (g : ℝ → ℝ) (hg : Continuous g) (r : ℝ) (hr : 0 ≤ r) :
    (∫ t in 0..r, g t)^2 ≤ r*∫ t in 0..r, (g t)^2 := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  let B := ∫ t in 0..r, g t
  have h0 : 0 ≤ ∫ t in 0..r, (r*g t-B)^2 :=
    intervalIntegral.integral_nonneg hr.le (fun _ _ => sq_nonneg _)
  have expand (t : ℝ) : (r*g t-B)^2 = (r^2)*(g t)^2+(-2*r*B)*g t+B^2 := by ring
  have c1 : Continuous (fun t => r^2*(g t)^2) := continuous_const.mul (hg.pow 2)
  have c2 : Continuous (fun t => (-2*r*B)*g t) := continuous_const.mul hg
  have ci12 : IntervalIntegrable (fun t => r^2*(g t)^2+(-2*r*B)*g t) volume 0 r :=
    (c1.add c2).intervalIntegrable _ _
  have cic : IntervalIntegrable (fun _ : ℝ => B^2) volume 0 r := continuous_const.intervalIntegrable _ _
  simp_rw [expand] at h0
  rw [intervalIntegral.integral_add ci12 cic,
    intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at h0
  simp only [sub_zero,smul_eq_mul] at h0
  change B^2 ≤ _
  by_contra! hh
  have hneg := mul_neg_of_pos_of_neg hr (sub_neg.mpr hh)
  dsimp [B] at h0 hh hneg
  nlinarith

theorem trace_bound (f d : ℝ → E) (hd : ∀ x, HasDerivAt f (d x) x) (hc : Continuous d)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖f r-f 0‖^2 ≤ r*∫ t in 0..r, ‖d t‖^2 := by
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=r) (fun x _ => hd x) (hc.intervalIntegrable _ _)
  have hn := intervalIntegral.norm_integral_le_integral_norm (f:=d) (μ:=volume) hr
  rw [heq] at hn
  have hpos := intervalIntegral.integral_nonneg (f:=fun t=>‖d t‖) (μ:=volume) hr
    (fun _ _ => norm_nonneg _)
  exact ((sq_le_sq₀ (norm_nonneg _) hpos).mpr hn).trans (interval_schwarz _ hc.norm r hr)

/-- Anchored Gaussian Poincaré inequality on every finite half-interval.
    The constant is uniform in its endpoint. -/
theorem gaussian_half_interval (f d : ℝ → E) (hd : ∀ x, HasDerivAt f (d x) x)
    (hc : Continuous d) (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in 0..R, Real.exp (-(x^2))*‖f x-f 0‖^2) ≤
      (∫ x in 0..R, Real.exp (-(x^2))*‖d x‖^2)/2 := by
  let w := fun x : ℝ => Real.exp (-(x^2))
  let g := fun x : ℝ => ‖d x‖^2
  let A := fun x : ℝ => ∫ t in 0..x, g t
  have hw : Continuous w := Real.continuous_exp.comp (continuous_id.pow 2).neg
  have hg : Continuous g := hc.norm.pow 2
  have hA (x : ℝ) : HasDerivAt A (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have ca : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have wp (x : ℝ) : HasDerivAt w ((-2)*x*w x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.exp) using 1 <;> simp [w] <;> ring
  have cf : Continuous (fun x => w x*‖f x-f 0‖^2) := hw.mul ((hf.sub continuous_const).norm.pow 2)
  have cx : Continuous (fun x : ℝ => w x*(x*A x)) := hw.mul (continuous_id.mul ca)
  have hcwp : Continuous (fun x : ℝ => (-2)*x*w x) := (continuous_const.mul continuous_id).mul hw
  have hle := intervalIntegral.integral_mono_on hR (cf.intervalIntegrable _ _) (cx.intervalIntegrable _ _)
    (fun x hx => mul_le_mul_of_nonneg_left (trace_bound f d hd hc x hx.1) (Real.exp_pos _).le)
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=0) (b:=R)
    (fun x _ => hA x) (fun x _ => wp x) (hg.intervalIntegrable _ _) (hcwp.intervalIntegrable _ _)
  have p (x : ℝ) : A x*((-2)*x*w x) = (-2)*(w x*(x*A x)) := by ring
  have rev (x : ℝ) : g x*w x=w x*g x := mul_comm _ _
  simp_rw [p,rev] at ibp
  rw [intervalIntegral.integral_const_mul,show A 0=0 by simp [A],zero_mul,sub_zero] at ibp
  have hA0 : 0 ≤ A R := intervalIntegral.integral_nonneg hR (fun _ _ => sq_nonneg _)
  have hboundary := mul_nonneg hA0 (Real.exp_pos (-(R^2))).le
  change 0 ≤ A R*w R at hboundary
  change (∫ x in 0..R, w x*‖f x-f 0‖^2) ≤ (∫ x in 0..R, w x*g x)/2
  linarith

/-- The full-line Gaussian gradient bound for Banach-valued C1 functions. The
    assumptions on the two displayed integrals are their form-domain bounds. -/
theorem gaussian_line (f d : ℝ → E) (hd : ∀ x, HasDerivAt f (d x) x)
    (hc : Continuous d)
    (hiF : Integrable (fun x => Real.exp (-(x^2))*‖f x-f 0‖^2))
    (hiG : Integrable (fun x => Real.exp (-(x^2))*‖d x‖^2)) :
    (∫ x, Real.exp (-(x^2))*‖f x-f 0‖^2) ≤ (∫ x, Real.exp (-(x^2))*‖d x‖^2)/2 := by
  let F := fun x : ℝ => Real.exp (-(x^2))*‖f x-f 0‖^2
  let G := fun x : ℝ => Real.exp (-(x^2))*‖d x‖^2
  have hrud (t : ℝ) : HasDerivAt (fun s => f (-s)) (-d (-t)) t := by
    simpa using (hd (-t)).comp t (hasDerivAt_neg t)
  have hruc : Continuous (fun t => -d (-t)) := (hc.comp continuous_neg).neg
  refine le_of_tendsto_of_tendsto
    (intervalIntegral_tendsto_integral hiF tendsto_neg_atTop_atBot tendsto_id)
    ((intervalIntegral_tendsto_integral hiG tendsto_neg_atTop_atBot tendsto_id).div_const 2) ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  change (∫ x in -R..R, F x) ≤ (∫ x in -R..R, G x)/2
  have hf := gaussian_half_interval f d hd hc R hR
  have hr := gaussian_half_interval _ _ hrud hruc R hR
  have negF : (∫ x in 0..R, Real.exp (-(x^2))*‖f (-x)-f 0‖^2) = ∫ x in -R..0, F x := by
    simpa [F] using (intervalIntegral.integral_comp_neg (a:=0) (b:=R) F)
  have negG : (∫ x in 0..R, Real.exp (-(x^2))*‖d (-x)‖^2) = ∫ x in -R..0, G x := by
    simpa [G] using (intervalIntegral.integral_comp_neg (a:=0) (b:=R) G)
  simp only [neg_zero,norm_neg] at hr
  rw [negF,negG] at hr
  change (∫ x in 0..R, F x) ≤ (∫ x in 0..R, G x)/2 at hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (f:=F) (hiF.intervalIntegrable (a:=-R) (b:=0))
    (hiF.intervalIntegrable (a:=0) (b:=R)),
    ← intervalIntegral.integral_add_adjacent_intervals (f:=G) (hiG.intervalIntegrable (a:=-R) (b:=0))
    (hiG.intervalIntegrable (a:=0) (b:=R))]
  linarith

end GaussianCore
