import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
namespace HFKinetic
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- L² norm of the unnormalized product multiplier applied to the real amplitude. -/
def normalization (μ : Measure Ω) (f₀ f₁ Y : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f₀ x * f₁ x * Y x)^2 ∂μ)

theorem weight_bounds {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1/100) {v₀ v₁ : ℝ}
    (h₀ : |v₀-1| ≤ b) (h₁ : |v₁-1| ≤ b) :
    1-2*b ≤ v₀*v₁ ∧ v₀*v₁ ≤ 1+3*b := by
  obtain ⟨h₀l, h₀u⟩ := abs_le.mp h₀
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp h₁
  have hl : (1-b)*(1-b) ≤ v₀*v₁ := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hu : v₀*v₁ ≤ (1+b)*(1+b) := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  constructor <;> nlinarith [sq_nonneg b, mul_nonneg hb (sub_nonneg.mpr hb')]

theorem normalization_bounds {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1/100)
    (f₀ f₁ Y : Ω → ℝ) (hY : Integrable (fun x => Y x^2) μ)
    (hmass : (∫ x, Y x^2 ∂μ) = 1) (hw : Integrable (fun x => (f₀ x*f₁ x*Y x)^2) μ)
    (hf : ∀ᵐ x ∂μ, |f₀ x-1| ≤ b ∧ |f₁ x-1| ≤ b) :
    1-2*b ≤ normalization μ f₀ f₁ Y ∧ normalization μ f₀ f₁ Y ≤ 1+3*b := by
  have h0 : 0 ≤ 1-2*b := by linarith
  have h1 : 0 ≤ 1+3*b := by linarith
  have lw : (1-2*b)^2 ≤ ∫ x, (f₀ x*f₁ x*Y x)^2 ∂μ := by
    calc
      _ = ∫ x, (1-2*b)^2*Y x^2 ∂μ := by rw [integral_const_mul, hmass, mul_one]
      _ ≤ _ := by
        apply integral_mono_ae (hY.const_mul _) hw
        filter_upwards [hf] with x hx
        have h := (weight_bounds hb hb' hx.1 hx.2).1
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h 2) (sq_nonneg _)
  have up : (∫ x, (f₀ x*f₁ x*Y x)^2 ∂μ) ≤ (1+3*b)^2 := by
    calc
      _ ≤ ∫ x, (1+3*b)^2*Y x^2 ∂μ := by
        apply integral_mono_ae hw (hY.const_mul _)
        filter_upwards [hf] with x hx
        have h := weight_bounds hb hb' hx.1 hx.2
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h0.trans h.1) h.2 2) (sq_nonneg _)
      _ = _ := by rw [integral_const_mul, hmass, mul_one]
  unfold normalization
  have hnon := (sq_nonneg (1-2*b)).trans lw
  exact ⟨(Real.le_sqrt h0 hnon).mpr lw, (Real.sqrt_le_iff.mpr ⟨h1,up⟩)⟩

theorem normalized_weights {b z v₀ v₁ : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1/100)
    (hz : 1-2*b ≤ z ∧ z ≤ 1+3*b)
    (h₀ : |v₀-1| ≤ b) (h₁ : |v₁-1| ≤ b) :
    |v₀*v₁/z| ≤ 2 ∧ |v₁/z| ≤ 2 ∧ |v₁/z-1| ≤ 5*b := by
  have hzpos : 0 < z := by linarith [hz.1]
  have hw := weight_bounds hb hb' h₀ h₁
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp h₁
  have h₁pos : 0 ≤ v₁ := by linarith
  have hp : 0 ≤ v₀*v₁ := by linarith [hw.1]
  constructor
  · rw [abs_of_nonneg (div_nonneg hp hzpos.le), div_le_iff₀ hzpos]
    linarith [hw.2, hz.1]
  constructor
  · rw [abs_of_nonneg (div_nonneg h₁pos hzpos.le), div_le_iff₀ hzpos]
    linarith [hz.1]
  apply abs_le.mpr
  have hl : (1-5*b)*z ≤ v₁ := by
    have h := mul_le_mul_of_nonneg_left hz.2 (by linarith : 0 ≤ 1-5*b)
    nlinarith [sq_nonneg b]
  have hu : v₁ ≤ (1+5*b)*z := by
    have h := mul_le_mul_of_nonneg_left hz.1 (by linarith : 0 ≤ 1+5*b)
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb')]
  constructor
  · linarith [(le_div_iff₀ hzpos).mpr hl]
  · linarith [(div_le_iff₀ hzpos).mpr hu]

#print axioms normalization_bounds
#print axioms normalized_weights
end
end HFKinetic

