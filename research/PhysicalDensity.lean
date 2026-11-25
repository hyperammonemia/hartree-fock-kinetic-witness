import NewtonBounds
import CoulombCentering
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory FinitePotential
noncomputable section
namespace PhysicalDensity

abbrev X := Position
abbrev rho := NewtonPerturbation.ρ
def Z₀ : ℝ := ∫ x, rho x
def Z : ℝ := ∫ x, rawOrbital x^2
def baseline (x : X) : ℝ := rho x/Z₀
def source (x : X) : ℝ := rawOrbital x^2/Z
def μ : Measure X := volume.withDensity (fun x => ENNReal.ofReal (source x))
def W (x y : X) : ℝ := ‖x-y‖⁻¹

theorem raw_squared (x : X) : rawOrbital x^2=rho x*weight x^2 := by
  unfold FinitePotential.rawOrbital rho NewtonPerturbation.ρ
  rw [mul_pow,sq,← Real.exp_add]
  congr 2
  ring

theorem z₀_pos : 0<Z₀ := by
  change 0 < ∫ x, NewtonField.density x
  rw [NewtonField.partition]
  unfold NewtonField.Z
  positivity

theorem weight_window (x : X) : 49/64≤weight x^2 ∧ weight x^2≤81/64 := by
  have hb := RadialConfiguration.amplitude_small
  have h := NewtonPerturbation.squared_window x
  have a := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/8)
    (show (7/8:ℝ)≤1-amplitude by linarith) 2
  have b := pow_le_pow_left₀ (by linarith [amplitude_pos] : (0:ℝ)≤1+amplitude)
    (show 1+amplitude≤(9/8:ℝ) by linarith) 2
  constructor <;> nlinarith

theorem mass_window : (49/64)*Z₀≤Z ∧ Z≤(81/64)*Z₀ := by
  have hρ : Integrable rho := by
    by_contra h
    exact z₀_pos.ne' (integral_undef h)
  have hr := NewtonPerturbation.reweighted_window rho hρ (fun x => (Real.exp_pos _).le)
    HFKinetic.weight_c1.continuous.measurable
  have hz0 : (7/8:ℝ) ≤ 1-amplitude := by linarith [RadialConfiguration.amplitude_small]
  have hz1 : 1+amplitude ≤ (9/8:ℝ) := by linarith [RadialConfiguration.amplitude_small]
  have hlo := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/8) hz0 2) z₀_pos.le
  have hhi := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [amplitude_pos]) hz1 2) z₀_pos.le
  change (1-amplitude)^2*Z₀≤(∫ x, rho x*weight x^2) ∧
    (∫ x, rho x*weight x^2)≤(1+amplitude)^2*Z₀ at hr
  have he : Z = ∫ x, rho x*weight x^2 := integral_congr_ae (Filter.Eventually.of_forall raw_squared)
  rw [he]
  constructor <;> nlinarith [hr.1,hr.2]

theorem z_pos : 0<Z :=
  (mul_pos (by norm_num : (0:ℝ)<49/64) z₀_pos).trans_le mass_window.1

theorem source_pos (x : X) : 0<source x := div_pos (sq_pos_of_pos (rawOrbital_pos x)) z_pos
theorem baseline_pos (x : X) : 0<baseline x := div_pos (Real.exp_pos _) z₀_pos

theorem source_cont : Continuous source := by
  have h : Continuous rawOrbital := (by fun_prop : Continuous (fun x : X => Real.exp (-‖x‖^2/2))).mul
    HFKinetic.weight_c1.continuous
  exact (h.pow 2).div_const Z

theorem source_integrable : Integrable source := by
  have h : Integrable (fun x => rawOrbital x^2) := by
    by_contra hn
    exact z_pos.ne' (integral_undef hn)
  exact h.div_const Z

theorem source_mass : (∫ x, source x)=1 := by
  unfold source
  rw [integral_div]
  exact div_self z_pos.ne'

instance : IsProbabilityMeasure μ := by
  constructor
  rw [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal source_integrable (Filter.Eventually.of_forall fun x => (source_pos x).le),
    source_mass,ENNReal.ofReal_one]

/-- The reference density relative to the normalized undeformed Gaussian is
    between one half and two, pointwise even in the rapidly oscillating shell. -/
theorem density_window (x : X) : baseline x/2≤source x ∧ source x≤2*baseline x := by
  have D : 0<rho x := Real.exp_pos _
  have H0 : Z/2≤weight x^2*Z₀ := by
    have h := mul_le_mul_of_nonneg_right (weight_window x).1 z₀_pos.le
    linarith [mass_window.2]
  have H1 : weight x^2*Z₀≤2*Z := by
    have h := mul_le_mul_of_nonneg_right (weight_window x).2 z₀_pos.le
    linarith [mass_window.1]
  have low := mul_le_mul_of_nonneg_left H0 D.le
  have high := mul_le_mul_of_nonneg_left H1 D.le
  unfold baseline source
  rw [raw_squared]
  constructor
  · rw [div_div,div_le_div_iff₀ (mul_pos z₀_pos (by norm_num)) z_pos]
    nlinarith
  · rw [← mul_div_assoc,div_le_div_iff₀ z_pos z₀_pos]
    nlinarith

theorem integral_source (g : X → ℝ) : (∫ x, g x ∂μ)=∫ x, source x*g x := by
  unfold μ
  rw [integral_withDensity_eq_integral_toReal_smul source_cont.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (source_pos _).le,smul_eq_mul]

theorem hartree_eq (x : X) : CoulombCentering.hartree μ W x=coulombAverage x := by
  unfold CoulombCentering.hartree coulombAverage
  rw [integral_source,← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by unfold source W Z; ring

theorem hartree_range (x : X) : 0<CoulombCentering.hartree μ W x ∧ CoulombCentering.hartree μ W x≤2 := by
  rw [hartree_eq]
  have hJ0 := NewtonBounds.positive x
  have hb := RadialConfiguration.amplitude_small
  have hc := abs_le.mp (NewtonBounds.change x)
  have hs : (3/2:ℝ) ≤ Real.sqrt Real.pi := Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_three])
  have hJ : RadialConfiguration.bareNewton x≤4/3 :=
    (NewtonField.uniform_bound x).trans ((div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)).2 (by linarith))
  have hcsmall := mul_le_mul_of_nonneg_right hb hJ0.le
  constructor <;> linarith [hc.1,hc.2]

theorem row_integrable (x : X) : Integrable (W x) μ := by
  by_contra h
  exact (hartree_range x).1.ne' (integral_undef h)

theorem hartree_integrable : Integrable (CoulombCentering.hartree μ W) μ := by
  have hm : Measurable (fun z : X × X => W z.1 z.2) := by unfold W; fun_prop
  apply (integrable_const (μ:=μ) (2:ℝ)).mono' hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (hartree_range x).1.le]
  exact (hartree_range x).2

end PhysicalDensity
