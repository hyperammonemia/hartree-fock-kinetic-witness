import CutoffDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Filter Set MeasureTheory FinitePotential
open scoped Topology
namespace ReferenceOrbital
noncomputable section

private theorem glue (a : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a = g a) (hd : df a = dg a) (x : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t) (if x ≤ a then df x else dg x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with t ht
    simp [ht.le]
  · rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (df x) (Iic x) x := by
      apply (hf x).hasDerivWithinAt.congr <;> simp_all
    have hr : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (df x) (Ici x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr
      · intro t ht
        by_cases he : t = x
        · simp [he,hv]
        · simp [show ¬t ≤ x from fun h => he (le_antisymm h ht)]
      · simp [hv]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with t ht
    simp [not_le.mpr ht]

private def slope (t : ℝ) : ℝ := 30*t^2*(1-t)^2
private def slope' (t : ℝ) : ℝ := 60*t*(1-t)*(1-2*t)
private def curvature (t : ℝ) : ℝ := if t ≤ 0 then 0 else if t ≤ 1 then slope' t else 0

private theorem slope_deriv (t : ℝ) : HasDerivAt slope (slope' t) t := by
  have h := (((hasDerivAt_id t).pow 2).const_mul 30).mul (((hasDerivAt_id t).const_sub 1).pow 2)
  convert h using 1 <;> first | rfl | (dsimp [slope']; ring)

private theorem curvature_deriv (t : ℝ) : HasDerivAt HFKinetic.switchSlope (curvature t) t := by
  let cap := fun r : ℝ => if r ≤ 1 then slope r else 0
  let dc := fun r : ℝ => if r ≤ 1 then slope' r else 0
  have hcap : ∀ r, HasDerivAt cap (dc r) r :=
    glue 1 slope (fun _ => 0) slope' (fun _ => 0) slope_deriv (fun r => hasDerivAt_const r _)
      (by norm_num [slope]) (by norm_num [slope'])
  exact glue 0 (fun _ => 0) cap (fun _ => 0) dc (fun r => hasDerivAt_const r _) hcap
    (by norm_num [cap,slope]) (by norm_num [dc,slope']) t

private theorem curvature_cont : Continuous curvature := by
  have hp : Continuous slope' := by unfold slope'; fun_prop
  have hcap : Continuous (fun t : ℝ => if t ≤ 1 then slope' t else 0) := by
    apply Continuous.if_le hp continuous_const continuous_id continuous_const
    intro x hx
    change x=1 at hx
    subst x
    norm_num [slope']
  apply Continuous.if_le continuous_const hcap continuous_id continuous_const
  intro x hx
  change x=0 at hx
  subst x
  norm_num [slope']

theorem switch_c2 : ContDiff ℝ 2 FinitePotential.switch := by
  change ContDiff ℝ (1+1) FinitePotential.switch
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (HFKinetic.switch_derivative x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [show deriv FinitePotential.switch=HFKinetic.switchSlope from funext fun x => (HFKinetic.switch_derivative x).deriv]
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (curvature_deriv x).differentiableAt,?_⟩
    rw [show deriv HFKinetic.switchSlope=curvature from funext fun x => (curvature_deriv x).deriv]
    exact curvature_cont

theorem weight_c2 : ContDiff ℝ 2 weight := by
  let p (r : ℝ) := envelope r*Real.cos (frequency*r)
  have henv : ContDiff ℝ 2 envelope :=
    (switch_c2.comp (contDiff_id.sub contDiff_const)).mul (switch_c2.comp (contDiff_const.sub contDiff_id))
  have hp : ContDiff ℝ 2 p := henv.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  have hr : ContDiff ℝ 2 (fun x : Position => p ‖x‖) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x=0
    · subst x
      have hnear : ∀ᶠ x : Position in 𝓝 0, ‖x‖<radius :=
        continuous_norm.continuousAt.eventually_lt continuousAt_const (by simpa [radius] using Real.exp_pos (10^18:ℝ))
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hnear] with t ht
      have hout : ‖t‖-radius ≤ 0 := by linarith
      simp [p,envelope,FinitePotential.switch,hout]
    · exact hp.comp_contDiffAt x (contDiffAt_norm ℝ hx)
  change ContDiff ℝ 2 (fun x : Position => 1+amplitude*envelope ‖x‖*Real.cos (frequency*‖x‖))
  simp_rw [mul_assoc]
  exact contDiff_const.add (contDiff_const.mul hr)

theorem raw_c2 : ContDiff ℝ 2 rawOrbital :=
  (Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 2)).mul weight_c2

end
end ReferenceOrbital

