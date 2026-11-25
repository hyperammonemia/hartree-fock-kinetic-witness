import KineticDilation
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory MeasureTheory.Measure
namespace HFKinetic
noncomputable section

/-- The spatial singlet amplitude and its directional weak derivative use real tests. -/
def WeakAxis (μ : Measure DilationConfig) (Y dY : DilationConfig → ℝ) (v : DilationConfig) : Prop :=
  ∀ φ : DilationConfig → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ x, Y x * fderiv ℝ φ x v ∂μ) = -(∫ x, dY x * φ x ∂μ)

theorem dilated_pairing (μ : Measure DilationConfig) [IsAddHaarMeasure μ] {l : ℝ}
    (hl : 0 < l) (n : ℕ) (Y φ : DilationConfig → ℝ) :
    (∫ x, dilatedField l n Y x * φ x ∂μ) =
       (l⁻¹^n*l^6) * (∫ x, Y x*φ (l • x) ∂μ) := by
  let q := fun x => Y x*φ (l • x)
  have re : (fun x => dilatedField l n Y x*φ x) = fun x => l⁻¹^n*q (l⁻¹ • x) := by
    funext x
    simp [dilatedField,q,smul_eq_mul,smul_smul,hl.ne',mul_assoc]
  rw [re, integral_const_mul,physical_jacobian μ q hl]
  dsimp [q]
  ring

theorem dilated_derivative_test {l : ℝ} (φ : DilationConfig → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x v : DilationConfig) :
    fderiv ℝ (fun q => φ (l • q)) x v = l * fderiv ℝ φ (l • x) v := by
  let A : DilationConfig →L[ℝ] DilationConfig := l • ContinuousLinearMap.id ℝ DilationConfig
  have ha := ((hφ.differentiable (by decide)) (A x)).hasFDerivAt.comp x A.hasFDerivAt
  change fderiv ℝ (φ ∘ A) x v = _
  rw [ha.fderiv]
  simp [A,smul_eq_mul]

/-- If dY is the weak spatial derivative of the oscillator-scale singlet amplitude,
the λ⁻⁴ field is the weak derivative of the very same λ⁻³-dilated amplitude. -/
theorem physical_weak_derivative (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (Y dY : DilationConfig → ℝ) (v : DilationConfig) {l : ℝ} (hl : 0 < l)
    (hweak : WeakAxis μ Y dY v) :
    WeakAxis μ (dilatedField l 3 Y) (dilatedField l 4 dY) v := by
  intro φ hφ hcompact
  have hlin : ContDiff ℝ 1 (fun x : DilationConfig => l • x) :=
    (l • ContinuousLinearMap.id ℝ DilationConfig).contDiff
  have htest : ContDiff ℝ 1 (fun x : DilationConfig => φ (l • x)) := hφ.comp hlin
  have hw := hweak (fun x => φ (l • x)) htest (hcompact.comp_smul hl.ne')
  have test_pair : (∫ x, Y x*fderiv ℝ (fun q => φ (l • q)) x v ∂μ) =
        l*(∫ x, Y x*fderiv ℝ φ (l • x) v ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    change Y x * fderiv ℝ (fun q => φ (l • q)) x v = l * (Y x * fderiv ℝ φ (l • x) v)
    rw [dilated_derivative_test (l := l) φ hφ x v]
    ring
  rw [test_pair] at hw
  rw [dilated_pairing μ hl 3 Y (fun x => fderiv ℝ φ x v), dilated_pairing μ hl 4 dY φ]
  have c3 : l⁻¹^3*l^6 = l^3 := by field_simp [hl.ne']
  have c4 : l⁻¹^4*l^6 = l^2 := by field_simp [hl.ne']
  rw [c3,c4]
  linear_combination (l^2)*hw

#print axioms physical_weak_derivative
end
end HFKinetic

