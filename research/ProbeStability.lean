import FiniteKinetic
import Mathlib.Tactic.FieldSimp

open MeasureTheory
open scoped BigOperators
namespace HFKinetic
noncomputable section

private theorem scalar_probe_difference {y z h δ : ℝ} (hd : 0 < δ) (hh : |h| ≤ 1) :
    |h^2*y^2-h^2*z^2| ≤ δ⁻¹*(y-z)^2+(δ/2)*(y^2+z^2) := by
  have hn : h^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg h) hh 2
  have twos : (y+z)^2 ≤ 2*(y^2+z^2) := by nlinarith [sq_nonneg (y-z)]
  have sq := sq_nonneg (2*|y-z| - δ*|y+z|)
  have id₁ := sq_abs (y-z)
  have id₂ := sq_abs (y+z)
  have young : δ*(|y-z| * |y+z|) ≤ (y-z)^2 + δ^2/4*(y+z)^2 := by
    nlinarith [sq, congrArg (fun a : ℝ => δ^2*a) id₂]
  have hs := mul_le_mul_of_nonneg_left twos (sq_nonneg δ)
  calc
    _ = h^2* (|y-z| * |y+z|) := by
      rw [← mul_sub, show y^2-z^2 = (y-z)*(y+z) by ring, abs_mul,abs_mul,
        abs_of_nonneg (sq_nonneg h)]
    _ ≤ |y-z| * |y+z| := mul_le_of_le_one_left (by positivity) hn
    _ ≤ ((y-z)^2+(δ^2/2)*(y^2+z^2))/δ := by
      apply (le_div_iff₀ hd).2
      nlinarith
    _ = _ := by field_simp [hd.ne']

theorem probe_stability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y Z : Ω → ℝ) (H : Fin 2 → Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hY : Integrable (fun x => Y x^2) μ) (hZ : Integrable (fun x => Z x^2) μ)
    (hD : Integrable (fun x => (Y x-Z x)^2) μ)
    (mY : (∫ x, Y x^2 ∂μ) = 1) (mZ : (∫ x, Z x^2 ∂μ) = 1)
    (distance : (∫ x, (Y x-Z x)^2 ∂μ) ≤ δ^2)
    (hyH : ∀ i, Integrable (fun x => H i x^2*Y x^2) μ)
    (hzH : ∀ i, Integrable (fun x => H i x^2*Z x^2) μ)
    (bounded : ∀ i, ∀ᵐ x ∂μ, |H i x| ≤ 1) :
    |probe μ Y H - probe μ Z H| ≤ 4*δ := by
  have one (i : Fin 2) :
      |(∫ x, H i x^2*Y x^2 ∂μ) - ∫ x, H i x^2*Z x^2 ∂μ| ≤ 2*δ := by
    rw [← integral_sub (hyH i) (hzH i)]
    calc
      _ ≤ ∫ x, |H i x^2*Y x^2-H i x^2*Z x^2| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, δ⁻¹*(Y x-Z x)^2+(δ/2)*(Y x^2+Z x^2) ∂μ := by
        apply integral_mono_ae ((hyH i).sub (hzH i)).abs
          ((hD.const_mul _).add ((hY.add hZ).const_mul _))
        filter_upwards [bounded i] with x hx using scalar_probe_difference hδ hx
      _ = δ⁻¹*(∫ x, (Y x-Z x)^2 ∂μ)+(δ/2)*(1+1) := by
        have hyz : Integrable (fun x => Y x^2+Z x^2) μ := hY.add hZ
        rw [integral_add (hD.const_mul (δ⁻¹)) (hyz.const_mul (δ/2)), integral_const_mul,
          integral_const_mul,integral_add hY hZ,mY,mZ]
      _ ≤ δ⁻¹*δ^2+(δ/2)*(1+1) := by gcongr
      _ = _ := by field_simp [hδ.ne']; ring
  unfold probe
  simp only [Fin.sum_univ_two]
  calc
    _ = |((∫ x, H 0 x^2*Y x^2 ∂μ) - ∫ x, H 0 x^2*Z x^2 ∂μ) +
         ((∫ x, H 1 x^2*Y x^2 ∂μ) - ∫ x, H 1 x^2*Z x^2 ∂μ)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := (add_le_add (one 0) (one 1)).trans_eq (by ring)

#print axioms probe_stability
end
end HFKinetic

