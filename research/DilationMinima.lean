import DilationEnergy
import DilationSlater

open MeasureTheory FinitePotential ContinuumHamiltonian
namespace HFKinetic
noncomputable section

def OscillatorExactMinimum (l : ℝ) (v : Position → ℝ) (s : State) : Prop :=
  Admissible v s ∧ ∀ w, Admissible v w → oscillatorEnergy l v s ≤ oscillatorEnergy l v w

def OscillatorHFMinimum (l : ℝ) (v : Position → ℝ) (s : State) : Prop :=
  (Admissible v s ∧ IsSlater s) ∧ ∀ w, Admissible v w → IsSlater w →
    oscillatorEnergy l v s ≤ oscillatorEnergy l v w

theorem energy_of_inverse (v : Position → ℝ) (w : State) {l : ℝ} (hl : 0<l) :
    formEnergy (scaledExternal l v) w = l⁻¹^2*oscillatorEnergy l v (scaledState l⁻¹ (inv_pos.mpr hl) w) := by
  simpa only [scaledState_inverse_other w hl] using scaledState_energy v (scaledState l⁻¹ (inv_pos.mpr hl) w) hl

theorem admissible_of_inverse (v : Position → ℝ) (w : State) {l : ℝ} (hl : 0<l)
    (h : Admissible (scaledExternal l v) w) : Admissible v (scaledState l⁻¹ (inv_pos.mpr hl) w) := by
  simpa only [scaledExternal_inverse v hl] using scaled_admissible (scaledExternal l v) w (inv_pos.mpr hl) h

theorem scaled_exactMinimum_iff (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    ExactMinimum (scaledExternal l v) (scaledState l hl s) ↔ OscillatorExactMinimum l v s := by
  constructor
  · rintro ⟨hs,he⟩
    refine ⟨(scaled_admissible_iff v s hl).mp hs,fun w hw => ?_⟩
    have h := he (scaledState l hl w) (scaled_admissible v w hl hw)
    rw [scaledState_energy v s hl,scaledState_energy v w hl] at h
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hl))).mp h
  · rintro ⟨hs,he⟩
    refine ⟨scaled_admissible v s hl hs,fun w hw => ?_⟩
    rw [scaledState_energy v s hl,energy_of_inverse v w hl]
    exact mul_le_mul_of_nonneg_left (he _ (admissible_of_inverse v w hl hw)) (sq_nonneg _)

theorem scaled_hfMinimum_iff (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    HFMinimum (scaledExternal l v) (scaledState l hl s) ↔ OscillatorHFMinimum l v s := by
  constructor
  · rintro ⟨⟨hs,hS⟩,he⟩
    refine ⟨⟨(scaled_admissible_iff v s hl).mp hs,(scaled_slater_iff s hl).mp hS⟩,fun w hw hW => ?_⟩
    have h := he (scaledState l hl w) (scaled_admissible v w hl hw) (scaled_slater w hl hW)
    rw [scaledState_energy v s hl,scaledState_energy v w hl] at h
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hl))).mp h
  · rintro ⟨⟨hs,hS⟩,he⟩
    refine ⟨⟨scaled_admissible v s hl hs,scaled_slater s hl hS⟩,fun w hw hW => ?_⟩
    rw [scaledState_energy v s hl,energy_of_inverse v w hl]
    exact mul_le_mul_of_nonneg_left
      (he _ (admissible_of_inverse v w hl hw) (scaled_slater w (inv_pos.mpr hl) hW)) (sq_nonneg _)

/-- Every minimization is taken over the full complex-spin form domain or over
all normalized complex Slater determinants. Dilation preserves the optimizer,
its uniqueness up to phase, the radial closed shell, and the kinetic ordering. -/
theorem oscillator_reversal_implies_fixed (e h : State)
    (he : OscillatorExactMinimum coupling externalOscillatorUnits e)
    (hh : OscillatorHFMinimum coupling externalOscillatorUnits h)
    (unique : ∀ w, OscillatorHFMinimum coupling externalOscillatorUnits w → SameRay w h)
    (closed : ∃ U : ℝ → ℝ, IsClosedShell h (fun x => (U ‖x‖:ℂ)))
    (reversal : ContinuumHamiltonian.kinetic e < ContinuumHamiltonian.kinetic h) :
    ContinuumHamiltonian.FixedRadialReversal := by
  have hl : 0 < coupling := by norm_num [coupling]
  refine ⟨scaledState coupling hl e,scaledState coupling hl h,
    (scaled_exactMinimum_iff externalOscillatorUnits e hl).mpr he,
    (scaled_hfMinimum_iff externalOscillatorUnits h hl).mpr hh,?_,
    scaled_closedShell_radial h hl closed,?_⟩
  · intro w hw
    let t := scaledState coupling⁻¹ (inv_pos.mpr hl) w
    have htw : scaledState coupling hl t = w := scaledState_inverse_other w hl
    have hmin : HFMinimum (scaledExternal coupling externalOscillatorUnits) (scaledState coupling hl t) := by
      rw [htw]
      exact hw
    have hray := scaled_sameRay hl (unique t ((scaled_hfMinimum_iff externalOscillatorUnits t hl).mp hmin))
    simpa only [htw] using hray
  · rw [scaledState_kinetic e hl,scaledState_kinetic h hl]
    exact mul_lt_mul_of_pos_left reversal (sq_pos_of_pos (inv_pos.mpr hl))

#print axioms scaled_exactMinimum_iff
#print axioms scaled_hfMinimum_iff
#print axioms oscillator_reversal_implies_fixed
end
end HFKinetic
