import RadialConfiguration

/-! A pointwise comparison of normalized Newton potentials from the two
unnormalized Gaussian integrals in their definition. -/
noncomputable section
open MeasureTheory
namespace NewtonPerturbation
abbrev X := FinitePotential.Position
abbrev b := FinitePotential.amplitude
def ρ (x : X) := Real.exp (-(‖x‖^2))

theorem squared_window (x : X) :
    (1-b)^2 ≤ FinitePotential.weight x ^ 2 ∧
    FinitePotential.weight x ^ 2 ≤ (1+b)^2 := by
  have hb := FinitePotential.amplitude_pos.le
  have hs := RadialConfiguration.amplitude_small
  have h₁ := FinitePotential.switch_range (‖x‖-FinitePotential.radius)
  have h₂ := FinitePotential.switch_range (FinitePotential.radius+3-‖x‖)
  have hpos := mul_nonneg h₁.1 h₂.1
  have hh := mul_le_mul h₁.2 h₂.2 h₂.1 (by norm_num : (0:ℝ)≤1)
  change FinitePotential.envelope ‖x‖ ≤ 1*1 at hh
  change 0 ≤ FinitePotential.envelope ‖x‖ at hpos
  have hp := mul_nonneg hb hpos
  have hu := mul_le_mul_of_nonneg_left hh hb
  have low := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (FinitePotential.frequency*‖x‖)) hp
  have high := mul_le_mul_of_nonneg_left (Real.cos_le_one (FinitePotential.frequency*‖x‖)) hp
  have lb : 1-b ≤ FinitePotential.weight x := by unfold FinitePotential.weight; linarith
  have ub : FinitePotential.weight x ≤ 1+b := by unfold FinitePotential.weight; linarith
  exact ⟨pow_le_pow_left₀ (by linarith) lb 2,
    pow_le_pow_left₀ (FinitePotential.weight_pos x).le ub 2⟩

theorem reweighted_window (f : X → ℝ) (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hm : Measurable FinitePotential.weight) :
    (1-b)^2*(∫ y, f y) ≤ ∫ y, f y*(FinitePotential.weight y)^2 ∧
    (∫ y, f y*(FinitePotential.weight y)^2) ≤ (1+b)^2*(∫ y, f y) := by
  have hi : Integrable (fun y => f y * (FinitePotential.weight y)^2) := by
    apply (hf.const_mul ((1+b)^2)).mono' (hf.aestronglyMeasurable.mul (hm.pow_const 2).aestronglyMeasurable)
    filter_upwards with y
    change ‖f y * FinitePotential.weight y^2‖ ≤ (1+b)^2 * f y
    rw [Real.norm_of_nonneg (mul_nonneg (hf0 _) (sq_nonneg _)),mul_comm (f y)]
    exact mul_le_mul_of_nonneg_right (squared_window y).2 (hf0 _)
  constructor
  · rw [← integral_const_mul]
    apply integral_mono (hf.const_mul _) hi
    intro y
    simpa only [mul_comm (f y)] using mul_le_mul_of_nonneg_right (squared_window y).1 (hf0 y)
  · rw [← integral_const_mul]
    apply integral_mono hi (hf.const_mul _)
    intro y
    simpa only [mul_comm (f y)] using mul_le_mul_of_nonneg_right (squared_window y).2 (hf0 y)

private theorem ratios (A Af Z Zf : ℝ) (hA : 0 ≤ A) (hZ : 0 < Z)
    (aw : (1-b)^2*A ≤ Af ∧ Af ≤ (1+b)^2*A)
    (zw : (1-b)^2*Z ≤ Zf ∧ Zf ≤ (1+b)^2*Z) :
    |Af/Zf-A/Z| ≤ 5*b*(A/Z) := by
  have hb := FinitePotential.amplitude_pos.le
  have hs := RadialConfiguration.amplitude_small
  have lpos : 0 < 1-b := by linarith
  have zfp := lt_of_lt_of_le (mul_pos (sq_pos_of_pos lpos) hZ) zw.1
  have lo : (1-5*b)*(1+b)^2 ≤ (1-b)^2 := by nlinarith [sq_nonneg b, pow_nonneg hb 3]
  have hi : (1+b)^2 ≤ (1+5*b)*(1-b)^2 := by
    have hbb := mul_le_mul_of_nonneg_right hs hb
    nlinarith [pow_nonneg hb 3]
  have a0 := mul_nonneg (show 0≤1-5*b by linarith) hA
  have a1 := mul_nonneg (show 0≤1+5*b by linarith) hA
  rw [abs_le]
  constructor
  · have v1 := mul_le_mul_of_nonneg_right aw.1 hZ.le
    have v2 := mul_le_mul_of_nonneg_left zw.2 a0
    have v3 := mul_le_mul_of_nonneg_right lo (mul_nonneg hA hZ.le)
    field_simp [hZ.ne', zfp.ne']; nlinarith only [v1,v2,v3]
  · have v1 := mul_le_mul_of_nonneg_right aw.2 hZ.le
    have v2 := mul_le_mul_of_nonneg_left zw.1 a1
    have v3 := mul_le_mul_of_nonneg_right hi (mul_nonneg hA hZ.le)
    field_simp [hZ.ne', zfp.ne']; nlinarith only [v1,v2,v3]

theorem exact_field_change (x : X) (hm : Measurable FinitePotential.weight)
    (hρ : Integrable ρ) (hZ : 0 < ∫ y, ρ y)
    (hi : Integrable (fun y => ρ y / ‖x-y‖)) :
    |FinitePotential.coulombAverage x-RadialConfiguration.bareNewton x| ≤
      5*b*RadialConfiguration.bareNewton x := by
  have form (y : X) : (FinitePotential.rawOrbital y)^2 = ρ y * (FinitePotential.weight y)^2 := by
    unfold FinitePotential.rawOrbital ρ
    rw [mul_pow, sq, ← Real.exp_add]
    congr 2; ring
  have aw := reweighted_window (fun y => ρ y/‖x-y‖) hi
    (fun y => div_nonneg (Real.exp_pos _).le (norm_nonneg _)) hm
  have zw := reweighted_window ρ hρ (fun y => (Real.exp_pos _).le) hm
  unfold FinitePotential.coulombAverage RadialConfiguration.bareNewton
  simp_rw [form,show ∀ y : X, ρ y*FinitePotential.weight y^2/‖x-y‖ =
      (ρ y/‖x-y‖)*FinitePotential.weight y^2 by intro; ring]
  exact ratios _ _ _ _ (integral_nonneg (fun y => div_nonneg (Real.exp_pos _).le (norm_nonneg _)))
    hZ aw zw

#print axioms exact_field_change
end NewtonPerturbation

