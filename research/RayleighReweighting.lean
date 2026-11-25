import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-! Normalization and nonnegative energy may be integrated against different
measures. In the radial witness they are the wavefunction mass and a positive
part of its ground-state energy form, respectively. -/

namespace RayleighReweighting
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

private theorem integral_window (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (b : ℝ) (hw : Integrable w μ)
    (window : ∀ x, |w x - 1| ≤ 5*b) :
    (1-5*b) * μ.real univ ≤ ∫ x, w x ∂μ ∧
      (∫ x, w x ∂μ) ≤ (1+5*b) * μ.real univ := by
  constructor
  · have h := integral_mono (integrable_const (1-5*b)) hw
      (fun x => by have := (abs_le.mp (window x)).1; linarith)
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  · have h := integral_mono hw (integrable_const (1+5*b))
      (fun x => by have := (abs_le.mp (window x)).2; linarith)
    simpa only [integral_const, smul_eq_mul, mul_comm] using h

/-- The probability measure μ normalizes the trial state. The finite positive
measure ν represents its unweighted energy density and may be singular with
respect to μ. A single pointwise weight window controls the Rayleigh quotient. -/
theorem normalized_energy (μ ν : Measure X) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (w : X → ℝ) (b : ℝ) (hb : 0 ≤ b) (hsmall : b ≤ 1/100)
    (hμ : Integrable w μ) (hν : Integrable w ν) (window : ∀ x, |w x - 1| ≤ 5*b) :
    1/2 ≤ (∫ x, w x ∂μ) ∧
      |(∫ x, w x ∂ν) / (∫ x, w x ∂μ) - ν.real univ| ≤ 20*b*ν.real univ := by
  let Z := ∫ x, w x ∂μ
  let N := ∫ x, w x ∂ν
  let M := ν.real univ
  have hz : 1-5*b ≤ Z ∧ Z ≤ 1+5*b := by
    simpa [Z, Measure.real] using integral_window μ w b hμ window
  have hn : (1-5*b)*M ≤ N ∧ N ≤ (1+5*b)*M := integral_window ν w b hν window
  have hm : 0 ≤ M := measureReal_nonneg
  have hzhalf : 1/2 ≤ Z := by linarith [hz.1]
  have hzpos : 0 < Z := by linarith
  have zmLo := mul_le_mul_of_nonneg_right hz.1 hm
  have zmHi := mul_le_mul_of_nonneg_right hz.2 hm
  have hmScale : 0 ≤ 20*b*M := mul_nonneg (by linarith) hm
  have zScale := mul_le_mul_of_nonneg_right hzhalf hmScale
  have lower : M-20*b*M ≤ N/Z :=
    (le_div_iff₀ hzpos).2 (by nlinarith only [hn.1, zmHi, zScale])
  have upper : N/Z ≤ M+20*b*M :=
    (div_le_iff₀ hzpos).2 (by nlinarith only [hn.2, zmLo, zScale])
  refine ⟨hzhalf, abs_le.mpr ⟨?_, ?_⟩⟩
  · change -(20*b*M) ≤ N/Z-M
    linarith
  · change N/Z-M ≤ 20*b*M
    linarith

#print axioms normalized_energy
end RayleighReweighting
