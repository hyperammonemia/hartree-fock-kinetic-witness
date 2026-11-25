import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
High-frequency kinetic-energy amplification for integrable real-line profiles.
The profile can represent the axial or radial marginal of a particle density
multiplied by the square of the modulation envelope. The normed-space vectors
represent normalized leading gradients and derivative remainders. No
Hartree–Fock optimizer or Schrödinger operator is postulated in this module.
-/

open Filter MeasureTheory Set
open scoped Topology FourierTransform Real

namespace KineticAmplification

noncomputable section

/-- The frequency is πn so the doubled argument matches the usual Fourier convention. -/
def oscillation (n : ℕ) (x : ℝ) : ℝ := Real.sin (Real.pi * n * x) ^ 2

theorem oscillation_bounds (n : ℕ) (x : ℝ) :
    0 ≤ oscillation n x ∧ oscillation n x ≤ 1 :=
  ⟨sq_nonneg _, Real.sin_sq_le_one _⟩

theorem oscillation_integrable {q : ℝ → ℝ} (hq : Integrable q) (n : ℕ) :
    Integrable (fun x => q x * oscillation n x) := by
  apply hq.mul_bdd (c := 1)
  · exact (show Continuous (oscillation n) from by unfold oscillation; fun_prop).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (oscillation_bounds n x).1] using
        (oscillation_bounds n x).2

private def fourierIntegrand (q : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  𝐞 (-(x * (n : ℝ))) • (q x : ℂ)

private theorem fourierIntegrand_re (q : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (fourierIntegrand q n x).re = q x * Real.cos (2 * (Real.pi * n * x)) := by
  simp only [fourierIntegrand, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  rw [show 2 * Real.pi * -(x * (n : ℝ)) = -(2 * (Real.pi * n * x)) by ring,
    Real.cos_neg, mul_comm]

theorem integrable_cos_profile {q : ℝ → ℝ} (hq : Integrable q) (n : ℕ) :
    Integrable (fun x => q x * Real.cos (2 * (Real.pi * n * x))) := by
  apply hq.mul_bdd (c := 1)
  · exact (show Continuous (fun x : ℝ => Real.cos (2 * (Real.pi * (n : ℝ) * x))) by
      fun_prop).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    change ‖Real.cos (2 * (Real.pi * (n : ℝ) * x))‖ ≤ 1
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * (Real.pi * (n : ℝ) * x))

/-- The oscillatory cosine component of any integrable density has zero limit. -/
theorem cosine_profile_tendsto {q : ℝ → ℝ} (hq : Integrable q) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, q x * Real.cos (2 * (Real.pi * n * x)))
      atTop (𝓝 0) := by
  have hfreq : Tendsto (fun n : ℕ => (n : ℝ)) atTop (cocompact ℝ) :=
    tendsto_natCast_atTop_atTop.mono_right atTop_le_cocompact
  have hfourier : Tendsto (fun n : ℕ => ∫ x : ℝ, fourierIntegrand q n x) atTop (𝓝 0) :=
    (Real.tendsto_integral_exp_smul_cocompact (fun x : ℝ => (q x : ℂ))).comp hfreq
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hfourier
  change Tendsto (fun n : ℕ => (∫ x : ℝ, fourierIntegrand q n x).re) atTop (𝓝 0) at hreal
  have heq (n : ℕ) : (∫ x : ℝ, fourierIntegrand q n x).re =
      ∫ x : ℝ, q x * Real.cos (2 * (Real.pi * n * x)) := by
    have hi : Integrable (fourierIntegrand q n) := by
      have hq' : Integrable (fun x : ℝ => (q x : ℂ)) := hq.ofReal
      change Integrable (fun x : ℝ => 𝐞 (-(x * (n : ℝ))) • (q x : ℂ))
      simpa only [Real.inner_apply, mul_comm] using
        ((Real.fourierIntegral_convergent_iff (n : ℝ)).2 hq')
    calc
      _ = ∫ x : ℝ, (fourierIntegrand q n x).re := (integral_re hi).symm
      _ = _ := by simp only [fourierIntegrand_re]
  simpa only [heq] using hreal

/-- Squared sine weights converge against an integrable density to weight one half. -/
theorem sin_sq_profile_tendsto {q : ℝ → ℝ} (hq : Integrable q) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, q x * oscillation n x) atTop
      (𝓝 ((∫ x : ℝ, q x) / 2)) := by
  have heq (n : ℕ) : (∫ x : ℝ, q x * oscillation n x) =
      ((∫ x : ℝ, q x) - ∫ x : ℝ, q x * Real.cos (2 * (Real.pi * n * x))) / 2 := by
    calc
      _ = ∫ x : ℝ, (q x - q x * Real.cos (2 * (Real.pi * n * x))) / 2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change q x * Real.sin (Real.pi * n * x) ^ 2 =
            (q x - q x * Real.cos (2 * (Real.pi * n * x))) / 2
          rw [Real.sin_sq_eq_half_sub]
          ring
      _ = _ := by rw [integral_div, integral_sub hq (integrable_cos_profile hq n)]
  simpa only [heq, sub_zero] using
    ((tendsto_const_nhds (x := ∫ x : ℝ, q x)).sub (cosine_profile_tendsto hq)).div_const 2

/-- L¹-convergent moving densities have the same squared-sine limit. -/
theorem moving_profile_tendsto {q : ℝ → ℝ} {Q : ℕ → ℝ → ℝ}
    (hq : Integrable q) (hQ : ∀ n, Integrable (Q n))
    (hL : Tendsto (fun n : ℕ => ∫ x : ℝ, |Q n x - q x|) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, Q n x * oscillation n x) atTop
      (𝓝 ((∫ x : ℝ, q x) / 2)) := by
  have hbound (n : ℕ) :
      |(∫ x : ℝ, Q n x * oscillation n x) - ∫ x : ℝ, q x * oscillation n x|
        ≤ ∫ x : ℝ, |Q n x - q x| := by
    rw [← integral_sub (oscillation_integrable (hQ n) n) (oscillation_integrable hq n)]
    calc
      _ ≤ ∫ x : ℝ, |Q n x * oscillation n x - q x * oscillation n x| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x : ℝ => Q n x * oscillation n x - q x * oscillation n x)
      _ ≤ _ := by
        apply integral_mono ((oscillation_integrable (hQ n) n).sub (oscillation_integrable hq n)).abs
          ((hQ n).sub hq).abs
        intro x
        change |Q n x * oscillation n x - q x * oscillation n x| ≤ |Q n x - q x|
        rw [← sub_mul, abs_mul, abs_of_nonneg (oscillation_bounds n x).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (oscillation_bounds n x).2
  have hd : Tendsto (fun n : ℕ =>
      (∫ x : ℝ, Q n x * oscillation n x) - ∫ x : ℝ, q x * oscillation n x) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hL.neg) hL
      (fun n => (abs_le.mp (hbound n)).1) (fun n => (abs_le.mp (hbound n)).2)
  simpa only [sub_add_cancel, zero_add] using hd.add (sin_sq_profile_tendsto hq)

variable {E : Type*} [NormedAddCommGroup E]

/-- A vanishing derivative remainder preserves the limit of squared norms. -/
theorem sq_norm_add_tendsto {u r : ℕ → E} {L : ℝ}
    (hu : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 L))
    (hr : Tendsto (fun n => ‖r n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖u n + r n‖ ^ 2) atTop (𝓝 L) := by
  have hL : 0 ≤ L := ge_of_tendsto hu (Eventually.of_forall fun _ => sq_nonneg _)
  have hu' : Tendsto (fun n => ‖u n‖) atTop (𝓝 (Real.sqrt L)) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (‖u n‖ ^ 2)) atTop (𝓝 (Real.sqrt L)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hu
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hbound (n : ℕ) : |‖u n + r n‖ - ‖u n‖| ≤ ‖r n‖ := by
    simpa using abs_norm_sub_norm_le (u n + r n) (u n)
  have hd : Tendsto (fun n => ‖u n + r n‖ - ‖u n‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hr.neg) hr
      (fun n => (abs_le.mp (hbound n)).1) (fun n => (abs_le.mp (hbound n)).2)
  simpa only [sub_add_cancel, zero_add, Real.sq_sqrt hL] using (hd.add hu').pow 2

/-- One half the squared norm is the variational kinetic functional of a gradient vector. -/
def kinetic (v : E) : ℝ := ‖v‖ ^ 2 / 2

variable [NormedSpace ℝ E]

/-- A strict density contrast forces strict kinetic ordering after a common amplification. -/
theorem kinetic_order_of_profile_gap
    {p q : ℝ → ℝ} {P Q : ℕ → ℝ → ℝ} {u v r s : ℕ → E} {a : ℕ → ℝ}
    (hp : Integrable p) (hq : Integrable q)
    (hP : ∀ n, Integrable (P n)) (hQ : ∀ n, Integrable (Q n))
    (hLp : Tendsto (fun n : ℕ => ∫ x : ℝ, |P n x - p x|) atTop (𝓝 0))
    (hLq : Tendsto (fun n : ℕ => ∫ x : ℝ, |Q n x - q x|) atTop (𝓝 0))
    (hu : ∀ n, ‖u n‖ ^ 2 = ∫ x : ℝ, P n x * oscillation n x)
    (hv : ∀ n, ‖v n‖ ^ 2 = ∫ x : ℝ, Q n x * oscillation n x)
    (hr : Tendsto (fun n => ‖r n‖) atTop (𝓝 0))
    (hs : Tendsto (fun n => ‖s n‖) atTop (𝓝 0))
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hgap : (∫ x : ℝ, p x) < ∫ x : ℝ, q x) :
    ∀ᶠ n in atTop, kinetic (a n • (u n + r n)) < kinetic (a n • (v n + s n)) := by
  have he := sq_norm_add_tendsto (u := u) (by simpa only [hu] using moving_profile_tendsto hp hP hLp) hr
  have hh := sq_norm_add_tendsto (u := v) (by simpa only [hv] using moving_profile_tendsto hq hQ hLq) hs
  have hhalf : (∫ x : ℝ, p x) / 2 < (∫ x : ℝ, q x) / 2 := by linarith
  have positive := (hh.sub he).eventually (Ioi_mem_nhds (sub_pos.mpr hhalf))
  filter_upwards [positive, ha] with n hdiff hnpos
  have hn : ‖u n + r n‖ ^ 2 < ‖v n + s n‖ ^ 2 := sub_pos.mp hdiff
  simp only [kinetic, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos hnpos]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hn (sq_pos_of_pos hnpos)) (by norm_num)

#print axioms KineticAmplification.kinetic_order_of_profile_gap

end

end KineticAmplification
