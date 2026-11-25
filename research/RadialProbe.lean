import FinitePotential
import FiniteOscillatoryWindow
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The Gaussian shell and the exact marginal are in oscillator coordinates.
The Jacobian and the two-electron normalization are included in the integrand. -/
noncomputable section
open MeasureTheory Set FinitePotential
namespace RadialProbe

def gaussianSq (r : ℝ) : ℝ := Real.exp (-(r^2)) / (Real.pi * Real.sqrt Real.pi)

def coefficient (s : ℝ → ℝ) (r : ℝ) : ℝ :=
  8 * Real.pi * r^2 * (gaussianSq r - s r ^ 2)

def integrand (s : ℝ → ℝ) (r : ℝ) : ℝ :=
  coefficient s r * envelope r ^ 2 * Real.sin (frequency*r)^2

theorem frequency_large : 2 ≤ frequency := by
  have hm := margin_le_one
  have hm0 := margin_pos
  have hb : amplitude ≤ 1/2 := by
    unfold amplitude
    nlinarith [mul_self_le_mul_self hm0.le hm]
  have h := (le_inv_comm₀ (by norm_num : (0:ℝ)<2) amplitude_pos).2 (by norm_num; linarith)
  unfold frequency
  nlinarith [sq_nonneg ((amplitude : ℝ)⁻¹-2)]

theorem plateau {r : ℝ} (h : r ∈ Icc (radius+1) ((radius+1)+1)) : envelope r = 1 := by
  have h₁ : 1 ≤ r-radius := by linarith [h.1]
  have h₂ : 1 ≤ radius+3-r := by linarith [h.2]
  have f {x : ℝ} (hx : 1 ≤ x) : switch x = 1 := by
    simp [switch, show ¬ x ≤ 0 by linarith, hx]
  simp [envelope, f h₁, f h₂]

theorem coefficient_lower (s : ℝ → ℝ) (r : ℝ)
    (hr : r ∈ Icc (radius+1) ((radius+1)+1))
    (hs : s r ^ 2 ≤ gaussianSq r/4) : 4*margin ≤ coefficient s r := by
  have hR : 1 ≤ radius := Real.one_le_exp (by norm_num)
  have hr2 : 2 ≤ r := by linarith [hr.1]
  have hr' : r ≤ radius+3 := by linarith [hr.2]
  have he : margin ≤ Real.exp (-(r^2)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (by simpa only [sq] using mul_self_le_mul_self (by linarith : 0 ≤ r) hr')
  have hp := Real.pi_pos
  have hsqrt := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt Real.pi ≤ 2 := by
    nlinarith [Real.sq_sqrt hp.le, Real.pi_lt_four]
  have hex := Real.exp_pos (-(r^2))
  have hc : 4*margin ≤ (6*r^2 / Real.sqrt Real.pi) * Real.exp (-(r^2)) := by
    have hbase : 4 ≤ 6*r^2 / Real.sqrt Real.pi := by
      apply (le_div_iff₀ hsqrt).2
      nlinarith [sq_nonneg (r-2)]
    exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans
      (mul_le_mul_of_nonneg_right hbase hex.le)
  calc
    _ ≤ (6*r^2 / Real.sqrt Real.pi) * Real.exp (-(r^2)) := hc
    _ = (8*Real.pi*r^2) * (gaussianSq r * (3/4)) := by
      unfold gaussianSq
      field_simp [hp.ne', hsqrt.ne']; ring
    _ ≤ _ := by
      unfold coefficient
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

/-- A pointwise tail bound valid almost everywhere gives the actual oscillatory
excess, with the fixed margin and frequency in the proposed Hamiltonian. -/
theorem margin_of_marginal (s : ℝ → ℝ) (hi : Integrable (integrand s))
    (tail : ∀ᵐ r : ℝ, radius ≤ r → r ≤ radius+3 → s r ^ 2 ≤ gaussianSq r/4) :
    margin ≤ ∫ r, integrand s r := by
  let a := radius+1
  have ha : a ≤ a+1 := by linarith
  have hi' : IntervalIntegrable (integrand s) volume a (a+1) :=
    hi.intervalIntegrable
  have hglobal : 0 ≤ᵐ[volume] integrand s := by
    filter_upwards [tail] with r ht
    by_cases hl : radius ≤ r
    · by_cases hu : r ≤ radius+3
      · have hg : 0 ≤ gaussianSq r := by unfold gaussianSq; positivity
        have hd : 0 ≤ gaussianSq r - s r ^ 2 := by linarith [ht hl hu]
        unfold integrand coefficient
        positivity
      · simp [integrand, envelope, switch, show radius+3-r ≤ 0 by linarith]
    · simp [integrand, envelope, switch, show r-radius ≤ 0 by linarith]
  have hc : Continuous (fun r : ℝ => 4*margin * Real.sin (frequency*r)^2) := by fun_prop
  have window : (∫ r in a..a+1, 4*margin * Real.sin (frequency*r)^2) ≤
      ∫ r in a..a+1, integrand s r := by
    rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le ha]
    apply setIntegral_mono_ae_restrict (hc.intervalIntegrable a (a+1)).1 hi'.1
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae tail] with r hr ht
    have hm : r ∈ Icc (radius+1) ((radius+1)+1) := ⟨hr.1.le, hr.2⟩
    have hs := ht (by linarith [hm.1]) (by linarith [hm.2])
    simp only [integrand, plateau hm, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_right (coefficient_lower s r hm hs) (sq_nonneg _)
  have hk := ContinuumForms.sin_sq_unit_interval a frequency frequency_large
  have hpos := mul_le_mul_of_nonneg_left hk (show 0 ≤ 4*margin by positivity [margin_pos])
  rw [intervalIntegral.integral_const_mul] at window
  have hs : margin ≤ ∫ r in a..a+1, integrand s r := by linarith
  rw [intervalIntegral.integral_of_le ha] at hs
  exact hs.trans (setIntegral_le_integral hi hglobal)

def spatialIntegrand (s : ℝ → ℝ) (r : ℝ) : ℝ :=
  2*(gaussianSq r - s r^2) * envelope r^2 * Real.sin (frequency*r)^2

theorem spatial_margin (s : ℝ → ℝ) (hi : Integrable (integrand s))
    (tail : ∀ᵐ r : ℝ, radius ≤ r → r ≤ radius+3 → s r ^ 2 ≤ gaussianSq r/4) :
    margin ≤ ∫ x : Position, spatialIntegrand s ‖x‖ := by
  rw [integral_fun_norm_addHaar volume (spatialIntegrand s)]
  have hv : (volume : Measure Position).real (Metric.ball 0 1) = Real.pi*4/3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  rw [hv]
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat,
    smul_eq_mul]
  rw [← mul_assoc, ← integral_const_mul]
  have hR : 0 < radius := Real.exp_pos _
  have eq : (∫ r in Ioi (0:ℝ), 3*(Real.pi*4/3)*(r^2 * spatialIntegrand s r)) =
      ∫ r, integrand s r := by
    calc
      _ = ∫ r in Ioi (0:ℝ), integrand s r := by
        apply integral_congr_ae
        filter_upwards with r
        unfold integrand coefficient spatialIntegrand
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
        have ha : r-radius ≤ 0 := by simp only [mem_Ioi, not_lt] at hr; linarith
        simp [integrand, envelope, switch, ha])
  rw [eq]
  exact margin_of_marginal s hi tail

#print axioms spatial_margin
#print axioms margin_of_marginal
end RadialProbe
