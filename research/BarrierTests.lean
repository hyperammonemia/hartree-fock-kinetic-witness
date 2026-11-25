import FluxTests
import GaussianFlux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integration by parts for the exterior Gaussian barrier in compact radial tests. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace HFExterior

/-- On one piece, the strong supersolution inequality pays the exact boundary
flux. The derivative and both integrals are for the same functions. -/
theorem barrier_piece_lower {a b : ℝ} {F dF P h dh : ℝ → ℝ} (hab : a ≤ b)
    (hF : ∀ r ∈ Icc a b, HasDerivAt F (dF r) r)
    (hdF : ContinuousOn dF (Icc a b)) (hP : ContinuousOn P (Icc a b))
    (hsign : ∀ r ∈ Icc a b, dF r ≤ P r) (hh : FluxHats.Piece a b h dh) :
    F b * h b - F a * h a ≤ (∫ r in a..b, F r*dh r) + ∫ r in a..b, P r*h r := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr fun r => (hh.deriv r).continuousAt
  have hA : IntervalIntegrable (fun r => dF r*h r) volume a b :=
    (hdF.mul hc.continuousOn).intervalIntegrable_of_Icc hab
  have hB : IntervalIntegrable (fun r => F r*dh r) volume a b :=
    ((HasDerivAt.continuousOn hF).mul hh.continuousDeriv.continuousOn).intervalIntegrable_of_Icc hab
  have hC : IntervalIntegrable (fun r => P r*h r) volume a b :=
    (hP.mul hc.continuousOn).intervalIntegrable_of_Icc hab
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun r => F r*h r) (f' := fun r => dF r*h r+F r*dh r)
    (fun r hr => (hF r (uIcc_of_le hab ▸ hr)).mul (hh.deriv r)) (hA.add hB)
  rw [intervalIntegral.integral_add hA hB] at ftc
  have hmono := intervalIntegral.integral_mono_on hab hA hC
    (fun r hr => mul_le_mul_of_nonneg_right (hsign r hr) (hh.nonneg r hr))
  linarith

/-- The compact three-piece test has zero exterior traces. Its internal flux
terms cancel at both joins. -/
theorem barrier_test_lower {q : ℝ} {F dF P : ℝ → ℝ}
    (hF : ∀ r, q < r → HasDerivAt F (dF r) r)
    (hdF : ContinuousOn dF (Ioi q)) (hP : ContinuousOn P (Ioi q))
    (hsign : ∀ r, q < r → dF r ≤ P r)
    (l c S t : ℝ) (L dL M dM R dR : ℝ → ℝ)
    (hql : q < l) (hlc : l < c) (hcS : c ≤ S) (hSt : S < t)
    (hpL : FluxHats.Piece l c L dL) (hpM : FluxHats.Piece c S M dM) (hpR : FluxHats.Piece S t R dR)
    (hL : L l = 0) (hLM : L c = M c) (hMR : M S = R S) (hR : R t = 0) :
    0 ≤ (∫ x in l..c, F x*dL x) + (∫ x in c..S, F x*dM x) + (∫ x in S..t, F x*dR x) +
      (∫ x in l..c, P x*L x) + (∫ x in c..S, P x*M x) + (∫ x in S..t, P x*R x) := by
  have one {a b : ℝ} {h dh : ℝ → ℝ} (hqa : q < a) (hab : a ≤ b) (hp : FluxHats.Piece a b h dh) :=
    barrier_piece_lower (F := F) (dF := dF) (P := P) hab
      (fun r hr => hF r (hqa.trans_le hr.1)) (hdF.mono fun _ hx => hqa.trans_le hx.1)
      (hP.mono fun _ hx => hqa.trans_le hx.1) (fun r hr => hsign r (hqa.trans_le hr.1)) hp
  have h1 := one hql hlc.le hpL
  have h2 := one (hql.trans hlc) hcS hpM
  have h3 := one ((hql.trans hlc).trans_le hcS) hSt.le hpR
  rw [hL,hLM,mul_zero,sub_zero] at h1
  rw [hMR] at h2
  rw [hR,mul_zero,zero_sub] at h3
  linarith

private theorem weighted_sub_integral {a b : ℝ} {f g h : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) (hh : Continuous h) :
    (∫ x in a..b, (f x-g x)*h x) = (∫ x in a..b, f x*h x) - ∫ x in a..b, g x*h x := by
  simp_rw [sub_mul]
  exact intervalIntegral.integral_sub (hf.mul_continuousOn hh.continuousOn)
    (hg.mul_continuousOn hh.continuousOn)

def locallyPairable (q : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ l t, q < l → l ≤ t → IntervalIntegrable F volume l t

/-- Subtracting a strong supersolution requires the weak inequality only for the
original subsolution. All outer traces and integration-by-parts terms are explicit. -/
theorem weak_difference_of_supersolution {q : ℝ} {A C F dF P : ℝ → ℝ}
    (hA : locallyPairable q A) (hC : locallyPairable q C)
    (hweak : FluxHats.testsOnPieces q A C)
    (hF : ∀ r, q < r → HasDerivAt F (dF r) r)
    (hdF : ContinuousOn dF (Ioi q)) (hP : ContinuousOn P (Ioi q))
    (hsign : ∀ r, q < r → dF r ≤ P r) :
    FluxHats.testsOnPieces q (fun r => A r-F r) (fun r => C r-P r) := by
  have hFc : ContinuousOn F (Ioi q) := HasDerivAt.continuousOn hF
  have hFi : locallyPairable q F := fun l t hql hlt =>
    (hFc.mono fun _ hx => hql.trans_le hx.1).intervalIntegrable_of_Icc hlt
  have hPi : locallyPairable q P := fun l t hql hlt =>
    (hP.mono fun _ hx => hql.trans_le hx.1).intervalIntegrable_of_Icc hlt
  intro l c S t L dL M dM R dR hql hlc hcS hSt hpL hpM hpR hL hLM hMR hR
  have weak := hweak l c S t L dL M dM R dR hql hlc hcS hSt hpL hpM hpR hL hLM hMR hR
  have barrier := barrier_test_lower hF hdF hP hsign l c S t L dL M dM R dR
    hql hlc hcS hSt hpL hpM hpR hL hLM hMR hR
  have hqC := hql.trans hlc
  have hqS := hqC.trans_le hcS
  have cL : Continuous L := continuous_iff_continuousAt.mpr fun r => (hpL.deriv r).continuousAt
  have cM : Continuous M := continuous_iff_continuousAt.mpr fun r => (hpM.deriv r).continuousAt
  have cR : Continuous R := continuous_iff_continuousAt.mpr fun r => (hpR.deriv r).continuousAt
  rw [weighted_sub_integral (hA l c hql hlc.le) (hFi l c hql hlc.le) hpL.continuousDeriv,
    weighted_sub_integral (hA c S hqC hcS) (hFi c S hqC hcS) hpM.continuousDeriv,
    weighted_sub_integral (hA S t hqS hSt.le) (hFi S t hqS hSt.le) hpR.continuousDeriv,
    weighted_sub_integral (hC l c hql hlc.le) (hPi l c hql hlc.le) cL,
    weighted_sub_integral (hC c S hqC hcS) (hPi c S hqC hcS) cM,
    weighted_sub_integral (hC S t hqS hSt.le) (hPi S t hqS hSt.le) cR]
  linarith

def barrierMomentum (q α r : ℝ) : ℝ := radialJacobian r * deriv (densityBarrier q α) r

def barrierMomentumSlope (q α r : ℝ) : ℝ :=
  4 * radialJacobian r * densityBarrier q α r * (α-α*(1-2*α)/(2*r^2))

theorem barrierMomentum_hasDerivAt {q α r : ℝ} (hr : 0 < r) :
    HasDerivAt (barrierMomentum q α) (barrierMomentumSlope q α r) r := by
  have hEq : (barrierMomentum q α) =ᶠ[nhds r]
      (fun t => (-(2*α))*t*Real.exp (-t^2)*densityBarrier q α t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    unfold barrierMomentum radialJacobian
    rw [(densityBarrier_hasDerivAt (show 0 < t from ht)).deriv]
    field_simp [(show 0 < t from ht).ne']
    ring
  have hgauss : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-t^2)) r := by fun_prop
  have hd : DifferentiableAt ℝ (fun t => (-(2*α))*t*Real.exp (-t^2)*densityBarrier q α t) r :=
    (((differentiableAt_const _).mul differentiableAt_id).mul hgauss).mul
      (densityBarrier_hasDerivAt hr).differentiableAt
  have hder : DifferentiableAt ℝ (barrierMomentum q α) r :=
    (hd.hasDerivAt.congr_of_eventuallyEq hEq).differentiableAt
  have h := hder.hasDerivAt
  change HasDerivAt _ (deriv (fun t => radialJacobian t*deriv (densityBarrier q α) t) r) _ at h
  rw [density_flux_deriv hr] at h
  exact h

/-- The concrete Gaussian barrier discharges the signs and smoothness needed by
the compact-test integration-by-parts inequality throughout the physical exterior. -/
theorem gaussian_barrier_test_lower {q α : ℝ} (hq : 0 < q) (ha0 : 0 ≤ α) (ha1 : 2*α ≤ 1)
    (V : ℝ → ℝ) (hVc : ContinuousOn V (Ioi q)) (hV : ∀ r, q < r → α ≤ V r)
    (l c S t : ℝ) (L dL M dM R dR : ℝ → ℝ)
    (hql : q < l) (hlc : l < c) (hcS : c ≤ S) (hSt : S < t)
    (hpL : FluxHats.Piece l c L dL) (hpM : FluxHats.Piece c S M dM) (hpR : FluxHats.Piece S t R dR)
    (hL : L l = 0) (hLM : L c = M c) (hMR : M S = R S) (hR : R t = 0) :
    let F := barrierMomentum q α
    let P := fun r => 4 * radialJacobian r * V r * densityBarrier q α r
    0 ≤ (∫ x in l..c, F x*dL x) + (∫ x in c..S, F x*dM x) + (∫ x in S..t, F x*dR x) +
      (∫ x in l..c, P x*L x) + (∫ x in c..S, P x*M x) + (∫ x in S..t, P x*R x) := by
  have hj : Continuous radialJacobian := by unfold radialJacobian; fun_prop
  have hB : ContinuousOn (densityBarrier q α) (Ioi q) := fun r hr =>
    (densityBarrier_hasDerivAt (hq.trans hr)).continuousAt.continuousWithinAt
  apply barrier_test_lower (dF := barrierMomentumSlope q α)
    (fun r hr => barrierMomentum_hasDerivAt (hq.trans hr)) _ _ _ l c S t L dL M dM R dR
    hql hlc hcS hSt hpL hpM hpR hL hLM hMR hR
  · intro r hr
    have hr0 : 0 < r := hq.trans hr
    have hBr := (densityBarrier_hasDerivAt (q := q) (α := α) hr0).continuousAt
    apply ContinuousAt.continuousWithinAt
    unfold barrierMomentumSlope
    fun_prop (disch := positivity)
  · exact (((continuousOn_const.mul hj.continuousOn).mul hVc).mul hB)
  · intro r hr
    have h := density_flux_supersolution (q := q) (hq.trans hr) ha0 ha1 (hV r hr)
    rw [density_flux_deriv (hq.trans hr)] at h
    unfold barrierMomentumSlope
    linarith

/-- On any exterior compact interval, the flux of the actual clamped
difference agrees almost everywhere with the difference of the two fluxes.
Only local absolute continuity of the marginal ratio is required. -/
theorem clamped_difference_flux_ae {q α l t : ℝ} (M : ℝ → ℝ)
    (hq : 0 < q) (hql : q < l) (hlt : l ≤ t) (hM : AbsolutelyContinuousOnInterval M l t) :
    ∀ᵐ r : ℝ, r ∈ Ι l t →
      FluxHats.flux (exteriorReciprocal q) (fun s => M (max q s)-densityBarrier q α (max q s)) r =
        radialJacobian r*deriv M r - barrierMomentum q α r := by
  filter_upwards [hM.ae_differentiableAt] with r hd hr
  have hmem := uIoc_subset_uIcc hr
  have hM' := hd hmem
  rw [uIcc_of_le hlt] at hmem
  have hqr : q < r := hql.trans_le hmem.1
  have hBr := densityBarrier_hasDerivAt (q := q) (α := α) (hq.trans hqr)
  have heq : (fun s => M (max q s)-densityBarrier q α (max q s)) =ᶠ[nhds r]
      (fun s => M s-densityBarrier q α s) := by
    filter_upwards [Ioi_mem_nhds hqr] with s hs
    rw [max_eq_right (show q ≤ s from le_of_lt hs)]
  unfold FluxHats.flux
  rw [physical_flux hqr.le,heq.deriv_eq,(hM'.hasDerivAt.sub hBr).deriv]
  unfold barrierMomentum
  rw [hBr.deriv]
  ring

end HFExterior
