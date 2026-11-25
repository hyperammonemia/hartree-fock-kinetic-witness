import FiniteKinetic
import WeightNormalization
import CutoffDerivative
import Mathlib.Tactic.FieldSimp

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

abbrev Configuration := Position × Position
def configMeasure : Measure Configuration := (volume : Measure Position).prod volume

def position (i : Fin 2) (x : Configuration) : Position := if i = 0 then x.1 else x.2
def remaining (i : Fin 2) (x : Configuration) : Position := if i = 0 then x.2 else x.1
def stepWeight (x : Configuration) : ℝ := weight x.1 * weight x.2
def stateNorm (Y : Configuration → ℝ) : ℝ :=
  normalization configMeasure (fun x => weight x.1) (fun x => weight x.2) Y
def sineProfile (i : Fin 2) (x : Configuration) : ℝ :=
  envelope ‖position i x‖ * Real.sin (frequency * ‖position i x‖)
def cutoffProfile (i : Fin 2) (x : Configuration) : ℝ :=
  deriv envelope ‖position i x‖ * Real.cos (frequency * ‖position i x‖)

theorem envelope_range (r : ℝ) : 0 ≤ envelope r ∧ envelope r ≤ 1 := by
  have h₀ := switch_range (r-radius)
  have h₁ := switch_range (radius+3-r)
  exact ⟨mul_nonneg h₀.1 h₁.1,(mul_le_mul h₀.2 h₁.2 h₁.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem amplitude_small : amplitude ≤ 1/100 := by
  have hw := mul_self_le_mul_self margin_pos.le margin_le_one
  unfold amplitude
  nlinarith

theorem weight_near_one (x : Position) : |weight x-1| ≤ amplitude := by
  have hg := envelope_range ‖x‖
  rw [weight, add_sub_cancel_left, abs_mul, abs_mul, abs_of_nonneg amplitude_pos.le,
    abs_of_nonneg hg.1]
  calc
    _ ≤ (amplitude*1)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg.2 amplitude_pos.le) (Real.abs_cos_le_one _)
        (abs_nonneg _) (mul_nonneg amplitude_pos.le zero_le_one)
    _ = _ := by ring

theorem sineProfile_abs (i : Fin 2) (x : Configuration) : |sineProfile i x| ≤ 1 := by
  have hg := envelope_range ‖position i x‖
  rw [sineProfile, abs_mul, abs_of_nonneg hg.1]
  exact (mul_le_mul hg.2 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem cutoffProfile_abs (i : Fin 2) (x : Configuration) : |cutoffProfile i x| ≤ 2 := by
  rw [cutoffProfile, abs_mul]
  exact (mul_le_mul (envelope_slope_abs _) (Real.abs_cos_le_one _) (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ 2)).trans_eq (mul_one 2)

theorem scalar_kinetic_scale : 2/(amplitude*frequency)^2 = 2*amplitude^2 := by
  rw [frequency]
  field_simp [amplitude_pos.ne']

/-- The ordinary product rule uses the physical cutoff derivative multiplied by b
and the sine derivative multiplied by b k. Scaling by (b k)⁻¹ = b produces scaled. -/
theorem physical_product_scaled {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (full other t h y : ℝ) (d e : G) :
    amplitude • (full • d + (other * (amplitude * (t-frequency*h)) * y) • e) =
      scaled amplitude full other h t y d e := by
  unfold scaled
  rw [smul_add,smul_smul,smul_smul]
  congr 2
  unfold frequency
  field_simp [amplitude_pos.ne']

private theorem cont_envelope : Continuous envelope := continuous_iff_continuousAt.mpr
  (fun r => (envelope_derivative r).continuousAt)
private theorem cont_weight : Continuous weight := by
  unfold weight
  exact continuous_const.add ((continuous_const.mul (cont_envelope.comp continuous_norm)).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_norm)))

private theorem integrable_mul_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A Y : Ω → ℝ} {C : ℝ} (hY : Integrable (fun x => Y x^2) μ)
    (ha : AEStronglyMeasurable A μ) (hb : ∀ x, |A x| ≤ C) :
    Integrable (fun x => A x^2 * Y x^2) μ := by
  have tmp := hY.mul_bdd (c := C^2) (ha.pow 2) (ae_of_all _ (fun x => by
    change ‖A x^2‖ ≤ C^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs (A x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2))
  simpa only [Pi.mul_apply,Pi.pow_apply,mul_comm] using tmp

private theorem step_cont : Continuous stepWeight :=
  (cont_weight.comp continuous_fst).mul (cont_weight.comp continuous_snd)

theorem stateNorm_bounds (Y : Configuration → ℝ) (hY : Integrable (fun x => Y x^2) configMeasure)
    (mass : (∫ x, Y x^2 ∂configMeasure) = 1) :
    1-2*amplitude ≤ stateNorm Y ∧ stateNorm Y ≤ 1+3*amplitude := by
  have hF : ∀ x, |stepWeight x| ≤ 2 := by
    intro x
    have h := weight_bounds amplitude_pos.le amplitude_small (weight_near_one x.1) (weight_near_one x.2)
    apply abs_le.mpr
    constructor <;> dsimp [stepWeight] <;> linarith [h.1,h.2, amplitude_pos,amplitude_small]
  have hw := integrable_mul_sq hY step_cont.aestronglyMeasurable hF
  refine normalization_bounds amplitude_pos.le amplitude_small _ _ _ hY mass ?_
     (ae_of_all _ fun x => ⟨weight_near_one x.1, weight_near_one x.2⟩)
  simpa only [stepWeight, mul_pow] using hw

def normalizedWave (Y : Configuration → ℝ) (x : Configuration) : ℝ :=
  stepWeight x / stateNorm Y * Y x

theorem normalizedWave_mass (Y : Configuration → ℝ) (hY : Integrable (fun x => Y x^2) configMeasure)
    (mass : (∫ x, Y x^2 ∂configMeasure) = 1) :
    (∫ x, normalizedWave Y x^2 ∂configMeasure) = 1 := by
  have hz : 0 < stateNorm Y := by linarith [(stateNorm_bounds Y hY mass).1,amplitude_small]
  have hsq : (stateNorm Y)^2 = ∫ x, (stepWeight x*Y x)^2 ∂configMeasure :=
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  calc
    _ = ∫ x, (stateNorm Y)⁻¹^2*(stepWeight x*Y x)^2 ∂configMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by unfold normalizedWave; ring
    _ = _ := by rw [integral_const_mul, ← hsq]; field_simp [hz.ne']

private theorem cont_sine (i : Fin 2) : Continuous (sineProfile i) := by
  have hp : Continuous (position i) := by
    by_cases hi : i = 0
    · have hp : position i = (Prod.fst : Configuration → Position) := funext fun _ => ite_eq_left hi
      rw [hp]
      exact continuous_fst
    · have hp : position i = (Prod.snd : Configuration → Position) := funext fun _ => ite_eq_right hi
      rw [hp]
      exact continuous_snd
  exact (cont_envelope.comp hp.norm).mul (Real.continuous_sin.comp (continuous_const.mul hp.norm))

/-- The nonnegative integrals are over the two physical three-dimensional coordinates.
P and d are the normalized modulated and unmodulated weak gradients. The displayed
product-rule hypothesis contains their full finite-frequency connection. -/
theorem fixed_kinetic_remainder {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Y : Configuration → ℝ) (d P e : Fin 2 → Configuration → G)
    (hY : Integrable (fun x => Y x^2) configMeasure) (mass : (∫ x, Y x^2 ∂configMeasure) = 1)
    (hd : ∀ i, Integrable (fun x => ‖d i x‖^2) configMeasure)
    (hP : ∀ i, Integrable (fun x => ‖P i x‖^2) configMeasure)
    (hgrad : (∑ i : Fin 2, ∫ x, ‖d i x‖^2 ∂configMeasure) ≤ 8)
    (hform : ∀ i, ∀ᵐ x ∂configMeasure, ‖e i x‖ = 1 ∧
       amplitude • P i x = scaled amplitude (stepWeight x/stateNorm Y)
         (weight (remaining i x)/stateNorm Y) (sineProfile i x) (cutoffProfile i x)
         (Y x) (d i x) (e i x)) :
    |(2/(amplitude*frequency)^2)*kinetic configMeasure P - probe configMeasure Y sineProfile| ≤
      54*amplitude := by
  have hz := stateNorm_bounds Y hY mass
  have hsup (i : Fin 2) (x : Configuration) :
      |stepWeight x/stateNorm Y| ≤ 2 ∧ |weight (remaining i x)/stateNorm Y| ≤ 2 ∧
        |weight (remaining i x)/stateNorm Y-1| ≤ 5*amplitude := by
    by_cases hi : i = 0
    · simpa [stepWeight,remaining,hi] using
        normalized_weights amplitude_pos.le amplitude_small hz (weight_near_one x.1) (weight_near_one x.2)
    · simpa [stepWeight,remaining,hi,mul_comm] using
        normalized_weights amplitude_pos.le amplitude_small hz (weight_near_one x.2) (weight_near_one x.1)
  have hmain := two_particle_remainder amplitude_pos amplitude_small Y d P e
    (fun x => stepWeight x/stateNorm Y) (fun i x => weight (remaining i x)/stateNorm Y)
    sineProfile cutoffProfile hY mass hd hP
    (fun i => integrable_mul_sq hY (cont_sine i).aestronglyMeasurable (sineProfile_abs i))
    hgrad (fun i => by
      filter_upwards [hform i] with x hx
      exact ⟨(hsup i x).1, (hsup i x).2.1, (hsup i x).2.2, sineProfile_abs i x,
        cutoffProfile_abs i x,hx.1,hx.2⟩)
  rw [scalar_kinetic_scale]
  convert hmain using 2; ring

/-- Product-rule formula for the normalized physical wave F Y / ‖F Y‖₂. -/
def modulatedGradient {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Y : Configuration → ℝ) (d e : Fin 2 → Configuration → G) (i : Fin 2) (x : Configuration) : G :=
  (stepWeight x/stateNorm Y) • d i x +
    ((weight (remaining i x)/stateNorm Y) * (amplitude*(cutoffProfile i x-frequency*sineProfile i x)) * Y x) • e i x

theorem constructed_kinetic_remainder {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Y : Configuration → ℝ) (d e : Fin 2 → Configuration → G)
    (hY : Integrable (fun x => Y x^2) configMeasure) (mass : (∫ x, Y x^2 ∂configMeasure) = 1)
    (hd : ∀ i, Integrable (fun x => ‖d i x‖^2) configMeasure)
    (hP : ∀ i, Integrable (fun x => ‖modulatedGradient Y d e i x‖^2) configMeasure)
    (hgrad : (∑ i : Fin 2, ∫ x, ‖d i x‖^2 ∂configMeasure) ≤ 8)
    (unit : ∀ i, ∀ᵐ x ∂configMeasure, ‖e i x‖ = 1) :
    |(2/(amplitude*frequency)^2)*kinetic configMeasure (modulatedGradient Y d e) -
         probe configMeasure Y sineProfile| ≤ 54*amplitude := by
  apply fixed_kinetic_remainder Y d _ e hY mass hd hP hgrad
  intro i
  filter_upwards [unit i] with x hx
  exact ⟨hx,physical_product_scaled _ _ _ _ _ _ _⟩

#print axioms fixed_kinetic_remainder
#print axioms constructed_kinetic_remainder
#print axioms normalizedWave_mass
end
end HFKinetic
