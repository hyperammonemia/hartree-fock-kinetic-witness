import FiniteKinetic
import FinitePotential
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp

open MeasureTheory MeasureTheory.Measure FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

abbrev DilationConfig := Position × Position

private theorem six_coordinates : Module.finrank ℝ DilationConfig = 6 := by
  rw [Module.finrank_prod,finrank_euclideanSpace_fin]

theorem physical_jacobian (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (f : DilationConfig → ℝ) {l : ℝ} (hl : 0 < l) :
    (∫ x, f (l⁻¹ • x) ∂μ) = l^6*(∫ x, f x ∂μ) := by
  simpa only [six_coordinates,smul_eq_mul] using μ.integral_comp_inv_smul_of_nonneg f hl.le

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

def dilatedField (l : ℝ) (n : ℕ) (f : DilationConfig → G) (x : DilationConfig) : G :=
  (l⁻¹^n) • f (l⁻¹ • x)

theorem dilated_square_integral (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (f : DilationConfig → G) (n : ℕ) {l : ℝ} (hl : 0 < l) :
    (∫ x, ‖dilatedField l n f x‖^2 ∂μ) = (l⁻¹^n)^2*l^6*(∫ x, ‖f x‖^2 ∂μ) := by
  simp only [dilatedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  rw [physical_jacobian μ (fun x => ‖f x‖^2) hl]
  ring

theorem physical_mass (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (Y : DilationConfig → G) {l : ℝ} (hl : 0 < l) :
    (∫ x, ‖dilatedField l 3 Y x‖^2 ∂μ) = ∫ x, ‖Y x‖^2 ∂μ := by
  rw [dilated_square_integral μ Y 3 hl]
  field_simp [hl.ne']

theorem physical_kinetic (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (P : Fin 2 → DilationConfig → G) {l : ℝ} (hl : 0 < l) :
    kinetic μ (fun i => dilatedField l 4 (P i)) = l⁻¹^2 * kinetic μ P := by
  unfold kinetic
  simp only [Fin.sum_univ_two,dilated_square_integral μ _ 4 hl]
  field_simp [hl.ne']

theorem physical_fixed_kinetic_order (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (P Q : Fin 2 → DilationConfig → G) (h : kinetic μ P < kinetic μ Q) :
    kinetic μ (fun i => dilatedField coupling 4 (P i)) <
    kinetic μ (fun i => dilatedField coupling 4 (Q i)) := by
  have hc : 0 < coupling := by norm_num [coupling]
  rw [physical_kinetic μ P hc,physical_kinetic μ Q hc]
  exact mul_lt_mul_of_pos_left h (sq_pos_of_pos (inv_pos.mpr hc))

#print axioms physical_jacobian
#print axioms physical_mass
#print axioms physical_kinetic
#print axioms physical_fixed_kinetic_order
end
end HFKinetic
