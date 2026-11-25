import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace WeightedGap

variable {X : Type*} [MeasurableSpace X]

/-- The unnormalized weighted variance. The normalization of the prescribed
    orbital cancels between the numerator and denominator of its gap. -/
noncomputable def variance (μ : Measure X) (w : X → ℝ) (z : X → ℂ) : ℝ :=
  sInf (Set.range fun c : ℂ => ∫ x, w x * ‖z x-c‖^2 ∂μ)

/-- Transfer the Gaussian Poincaré bound to every bounded orbital deformation
    in the specified interval. The gradient density may come from any complex
    form-domain vector. -/
theorem bounded_weight_transfer (μ : Measure X) (w g : X → ℝ) (z : X → ℂ)
    (wlo : ∀ x, 49/64 ≤ w x) (whi : ∀ x, w x ≤ 81/64) (g0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g μ) (hwg : Integrable (fun x => w x*g x) μ)
    (hd : ∀ c : ℂ, Integrable (fun x => ‖z x-c‖^2) μ)
    (hwd : ∀ c : ℂ, Integrable (fun x => w x*‖z x-c‖^2) μ)
    (hgauss : ∃ c : ℂ, (∫ x, ‖z x-c‖^2 ∂μ) ≤ (∫ x, g x ∂μ)/2) :
    49/81 * variance μ w z ≤ (∫ x, w x*g x ∂μ)/2 ∧
      variance μ w z / 2 ≤ (∫ x, w x*g x ∂μ)/2 := by
  have hw0 (x : X) : 0 ≤ w x := by linarith [wlo x]
  have hdev0 (c : ℂ) : 0 ≤ (∫ x, w x*‖z x-c‖^2 ∂μ) :=
    integral_nonneg (fun x => mul_nonneg (hw0 x) (sq_nonneg _))
  have hb : BddBelow (Set.range fun c : ℂ => ∫ x, w x * ‖z x-c‖^2 ∂μ) := by
    exact ⟨0, fun _ ⟨c,hc⟩ => hc ▸ hdev0 c⟩
  have hv0 : 0 ≤ variance μ w z := le_csInf (Set.range_nonempty _) (fun _ ⟨c,hc⟩ => hc ▸ hdev0 c)
  obtain ⟨c,hc⟩ := hgauss
  have hvc : variance μ w z ≤ (∫ x, w x*‖z x-c‖^2 ∂μ) :=
    csInf_le hb (Set.mem_range_self c)
  have hu := integral_mono (hwd c) ((hd c).const_mul (81/64:ℝ))
    (fun x => mul_le_mul_of_nonneg_right (whi x) (sq_nonneg _))
  have hl := integral_mono (hg.const_mul (49/64:ℝ)) hwg
    (fun x => mul_le_mul_of_nonneg_right (wlo x) (g0 x))
  rw [integral_const_mul] at hu hl
  constructor <;> linarith

end WeightedGap
