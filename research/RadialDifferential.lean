import CutoffDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

open Filter FinitePotential
open scoped Topology RealInnerProductSpace
namespace HFKinetic
noncomputable section

theorem switch_slope_continuous : Continuous switchSlope := by
  have hc : Continuous (fun t : ℝ => if t ≤ 1 then 30*t^2*(1-t)^2 else 0) := by
    apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    intro x hx
    change x = 1 at hx
    subst x
    norm_num
  change Continuous (fun t : ℝ => if t ≤ 0 then 0 else if t ≤ 1 then 30*t^2*(1-t)^2 else 0)
  apply Continuous.if_le continuous_const hc continuous_id continuous_const
  intro x hx
  change x = 0 at hx
  subst x
  norm_num

theorem switch_c1 : ContDiff ℝ 1 FinitePotential.switch := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (switch_derivative x).differentiableAt, ?_⟩
  have heq : deriv FinitePotential.switch = switchSlope := funext fun x => (switch_derivative x).deriv
  rw [heq]
  exact switch_slope_continuous

theorem envelope_c1 : ContDiff ℝ 1 envelope := by
  exact (switch_c1.comp (contDiff_id.sub contDiff_const)).mul
    (switch_c1.comp (contDiff_const.sub contDiff_id))

def radialProfile (r : ℝ) : ℝ := envelope r * Real.cos (frequency*r)
def radialModulation (x : Position) : ℝ := radialProfile ‖x‖
def radialCovector (x : Position) : Position →L[ℝ] ℝ := ‖x‖⁻¹ • innerSL ℝ x
def radialSlope (r : ℝ) : ℝ :=
  deriv envelope r * Real.cos (frequency*r) - frequency*envelope r*Real.sin (frequency*r)

theorem radialProfile_c1 : ContDiff ℝ 1 radialProfile :=
  envelope_c1.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

private theorem flat_at_origin : radialModulation =ᶠ[𝓝 (0:Position)] (fun _ => (0:ℝ)) := by
  have hR : (0:ℝ) < radius := Real.exp_pos _
  have hnear : ∀ᶠ x : Position in 𝓝 0, ‖x‖ < radius :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by simpa using hR)
  filter_upwards [hnear] with x hx
  have hout : ‖x‖-radius ≤ 0 := by linarith
  simp [radialModulation,radialProfile,envelope,FinitePotential.switch,hout]

theorem radialModulation_c1 : ContDiff ℝ 1 radialModulation := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq flat_at_origin
  · exact radialProfile_c1.comp_contDiffAt x (contDiffAt_norm ℝ hx)

theorem weight_c1 : ContDiff ℝ 1 weight := by
  change ContDiff ℝ 1 (fun x : Position => 1+amplitude*envelope ‖x‖*Real.cos (frequency*‖x‖))
  simp_rw [mul_assoc]
  exact contDiff_const.add (contDiff_const.mul radialModulation_c1)

theorem product_weight_c1 (Z : ℝ) :
    ContDiff ℝ 1 (fun x : Position × Position => weight x.1*weight x.2 / Z) := by
  simp only [div_eq_mul_inv]
  exact ((weight_c1.comp contDiff_fst).mul (weight_c1.comp contDiff_snd)).mul contDiff_const

theorem radialProfile_hasDerivAt (r : ℝ) : HasDerivAt radialProfile (radialSlope r) r := by
  have he := (envelope_derivative r).differentiableAt.hasDerivAt
  have hc := (Real.hasDerivAt_cos (frequency*r)).comp r ((hasDerivAt_id r).const_mul frequency)
  convert he.mul hc using 1 <;> first | rfl | (dsimp [radialSlope,Function.comp_def]; ring)

theorem norm_hasFDerivAt_radial {x : Position} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Position => ‖y‖) (radialCovector x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have he := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at he
  convert he using 1
  ext v
  simp [radialCovector, two_smul, smul_eq_mul]; field_simp [hn]; ring

theorem radialModulation_hasFDerivAt (x : Position) :
    HasFDerivAt radialModulation ((radialSlope ‖x‖) • radialCovector x) x := by
  by_cases hx : x = 0
  · subst x
    simp only [radialCovector, norm_zero,inv_zero,zero_smul,smul_zero]
    exact (hasFDerivAt_const (0:ℝ) (0:Position)).congr_of_eventuallyEq flat_at_origin
  · exact (radialProfile_hasDerivAt ‖x‖).comp_hasFDerivAt x (norm_hasFDerivAt_radial hx)

theorem radialModulation_direction (x v : Position) :
    fderiv ℝ radialModulation x v = radialSlope ‖x‖ * (inner ℝ x v / ‖x‖) := by
  rw [(radialModulation_hasFDerivAt x).fderiv]
  simp [radialCovector,innerSL_apply_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem weight_direction (x v : Position) :
    fderiv ℝ weight x v = amplitude*radialSlope ‖x‖ * (inner ℝ x v / ‖x‖) := by
  have hh := ((radialModulation_hasFDerivAt x).const_mul amplitude).const_add 1
  have hf : (fun y : Position => 1+amplitude*radialModulation y) = weight := by
    funext y; unfold radialModulation radialProfile weight; ring
  rw [hf] at hh
  rw [hh.fderiv]
  simp [radialCovector,innerSL_apply_apply,smul_eq_mul,div_eq_mul_inv] <;> ring

theorem weight_direction_origin (v : Position) : fderiv ℝ weight 0 v = 0 := by
  rw [weight_direction]
  simp

theorem weight_coordinate (x : Position) (j : Fin 3) :
    fderiv ℝ weight x (EuclideanSpace.single j 1) = amplitude*radialSlope ‖x‖ * (x j / ‖x‖) := by
  rw [weight_direction, EuclideanSpace.inner_single_right]
  simp

theorem product_weight_direction (z v : Position × Position) (Z : ℝ) :
    fderiv ℝ (fun q : Position × Position => weight q.1*weight q.2/Z) z v =
      (weight z.2 * fderiv ℝ weight z.1 v.1 + weight z.1 * fderiv ℝ weight z.2 v.2)/Z := by
  have ha := ((weight_c1.differentiable (by decide)) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (E := Position) (F := Position))
  have hb := ((weight_c1.differentiable (by decide)) z.2).hasFDerivAt.comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (E := Position) (F := Position))
  have hh := (ha.mul hb).const_mul Z⁻¹
  change HasFDerivAt (fun q : Position × Position => Z⁻¹*(weight q.1*weight q.2)) _ z at hh
  have heq : (fun q : Position × Position => Z⁻¹*(weight q.1*weight q.2)) =
      (fun q => weight q.1*weight q.2/Z) := by funext q; rw [div_eq_mul_inv,mul_comm]
  rw [heq] at hh
  rw [hh.fderiv]
  simp [ContinuousLinearMap.comp_apply,div_eq_mul_inv,smul_eq_mul,Function.comp_def] <;> ring

theorem product_weight_first (z : Position × Position) (j : Fin 3) (Z : ℝ) :
    fderiv ℝ (fun q : Position × Position => weight q.1*weight q.2/Z) z (EuclideanSpace.single j 1,0) =
      (weight z.2/Z)*(amplitude*radialSlope ‖z.1‖)*(z.1 j/‖z.1‖) := by
  rw [product_weight_direction]
  simp only [map_zero,mul_zero,add_zero,weight_coordinate]
  ring

theorem product_weight_second (z : Position × Position) (j : Fin 3) (Z : ℝ) :
    fderiv ℝ (fun q : Position × Position => weight q.1*weight q.2/Z) z (0,EuclideanSpace.single j 1) =
      (weight z.1/Z)*(amplitude*radialSlope ‖z.2‖)*(z.2 j/‖z.2‖) := by
  rw [product_weight_direction]
  simp only [map_zero,mul_zero,zero_add,weight_coordinate]
  ring

#print axioms radialModulation_c1
#print axioms product_weight_c1
#print axioms weight_direction
#print axioms weight_direction_origin
#print axioms product_weight_direction
end
end HFKinetic

