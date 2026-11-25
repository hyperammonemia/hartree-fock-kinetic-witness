import RelativeGaussian
import GaussianRadialMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Mean and second moment of physical Coulomb repulsion in the independent
two-electron Gaussian reference, integrated over the full pair space. -/
noncomputable section
open MeasureTheory Set GaussianRadialMoments RelativeGaussian
namespace PairGaussianMoments
abbrev Space := FinitePotential.Position

def mass := ∫ z : Space × Space, rho z.1 * rho z.2
def rep (n : ℕ) := ∫ z : Space × Space, (‖z.1-z.2‖^n)⁻¹ * rho z.1 * rho z.2

private theorem first_radial : I 1 = 1 := by
  rw [gamma_value]
  norm_num [Real.Gamma_one,Real.rpow_neg_one]

private theorem zeroth_radial : I 0 = Real.sqrt (2*Real.pi)/2 := by
  simpa [I,div_eq_mul_inv,mul_comm] using (integral_gaussian_Ioi (1/2))

private theorem second_radial : I 2 = I 0 := by simpa using recurrence 0

private def radialValue (n : ℕ) := ∫ z : Space, (‖z‖^n)⁻¹*relative z

private theorem radialValue_eq (n : ℕ) (hn : n ≤ 2) :
    radialValue n = 4*Real.pi*I (2-n) := by
  unfold radialValue relative
  rw [radial (fun r => (r^n)⁻¹ * Real.exp (-(1/2:ℝ)*r^2))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have h : r ≠ 0 := (mem_Ioi.mp hr).ne'
  interval_cases n <;> simp <;> field_simp

private theorem radial_pos (n : ℕ) (hn : n ≤ 2) : 0<radialValue n := by
  rw [radialValue_eq n hn]
  have hp : 0<Real.sqrt (2*Real.pi)/2 := by positivity
  interval_cases n <;> norm_num only [Nat.reduceSub] <;>
    simp only [second_radial,first_radial,zeroth_radial] <;> positivity

private theorem rep_eq (n : ℕ) (hn : n ≤ 2) : rep n = c*radialValue n := by
  apply difference_integral
  · fun_prop
  · intro z
    positivity
  · by_contra hi
    exact (radial_pos n hn).ne' (integral_undef hi)

private theorem mass_eq : mass = c*(4*Real.pi*I 2) := by
  have h := rep_eq 0 (by decide)
  rw [radialValue_eq 0 (by decide)] at h
  simpa [rep,mass] using h

theorem mass_pos : 0<mass := by
  rw [mass_eq,second_radial,zeroth_radial]
  unfold c
  positivity

theorem mean : rep 1/mass = Real.sqrt (2/Real.pi) := by
  rw [rep_eq 1 (by decide),radialValue_eq 1 (by decide),mass_eq]
  norm_num only [Nat.reduceSub]
  rw [first_radial,second_radial,zeroth_radial,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),
    Real.sqrt_div (by norm_num : (0:ℝ)≤2)]
  have hc : c ≠ 0 := by unfold c; positivity
  have hπ := Real.sqrt_pos.mpr Real.pi_pos
  have h₂ := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  field_simp [hc,hπ.ne',Real.pi_ne_zero]
  nlinarith

theorem second : rep 2/mass = 1 := by
  have he : rep 2 = mass := by
    rw [rep_eq 2 (by decide),radialValue_eq 2 (by decide),mass_eq,second_radial]
    rfl
  rw [he,div_self mass_pos.ne']

#print axioms mean
#print axioms second
end PairGaussianMoments
