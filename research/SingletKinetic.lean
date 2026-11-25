import FiniteKinetic
import ContinuumHamiltonian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.FieldSimp

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

abbrev SingletConfiguration := Position × Position

def singletSpin (a b : Fin 2) : ℝ :=
  if a = b then 0 else if a = 0 then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹

theorem spin_mass : (∑ a : Fin 2, ∑ b : Fin 2, singletSpin a b^2) = 1 := by
  simp only [Fin.sum_univ_two,singletSpin]
  norm_num [inv_pow,Real.sq_sqrt]

theorem weak_const (u v : SingletConfiguration → ℂ) (e : SingletConfiguration) (c : ℂ)
    (w : ContinuumHamiltonian.IsWeakPartial u v e) :
    ContinuumHamiltonian.IsWeakPartial (fun q => c*u q) (fun q => c*v q) e := by
  intro φ hφ hS
  simp only [mul_assoc, integral_const_mul]
  rw [w φ hφ hS, mul_neg]

theorem component_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G : Ω → Position} (hG : MemLp G 2 μ) (j : Fin 3) :
    MemLp (fun x => G x j) 2 μ := by
  exact hG.of_le ((PiLp.continuous_apply _ _ j).comp_aestronglyMeasurable hG.1)
    (ae_of_all _ fun x => PiLp.norm_apply_le (G x) j)

/-- Tensor a spatial wave with the normalized two-spin singlet. -/
def singletState (Y : SingletConfiguration → ℝ)
    (G : Fin 2 → SingletConfiguration → Position) (hY : MemLp Y 2 volume)
    (hG : ∀ i, MemLp (G i) 2 volume) (hw : ∀ i j,
      ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) : ContinuumHamiltonian.State where
  wave := fun a b x => (singletSpin a b : ℂ)*(Y x : ℂ)
  grad := fun a b i j x => (singletSpin a b : ℂ)*(G i x j : ℂ)
  squareIntegrable := fun a b => hY.ofReal.const_mul (singletSpin a b : ℂ)
  gradSquareIntegrable := fun a b i j =>
    (component_memLp (hG i) j).ofReal.const_mul (singletSpin a b : ℂ)
  weakGradient := fun a b i j => weak_const _ _ _ _ (hw i j)

private theorem singlet_factor (f : SingletConfiguration → ℝ) (c : ℝ) :
    (∫ x, ‖(c:ℂ)*(f x:ℂ)‖^2) = c^2*(∫ x, f x^2) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]

private theorem sum_spin (a : ℝ) : (∑ p : Fin 2, ∑ q : Fin 2, singletSpin p q^2*a) = a := by
  simp_rw [← Finset.sum_mul]
  rw [spin_mass,one_mul]

variable (Y : SingletConfiguration → ℝ) (G : Fin 2 → SingletConfiguration → Position)
    (hY : MemLp Y 2 volume) (hG : ∀ i, MemLp (G i) 2 volume)
    (hw : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ))
      (fun x => (G i x j : ℂ)) (ContinuumHamiltonian.axis i j))

theorem singletState_mass : ContinuumHamiltonian.mass (singletState Y G hY hG hw) = ∫ x, Y x^2 := by
  unfold ContinuumHamiltonian.mass singletState
  simp_rw [singlet_factor]
  exact sum_spin _

theorem singletState_kinetic :
    ContinuumHamiltonian.kinetic (singletState Y G hY hG hw) = kinetic volume G := by
  have compSum (i : Fin 2) : ∑ j : Fin 3, ∫ x, (G i x j)^2 = ∫ x, ‖G i x‖^2 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => (component_memLp (hG i) j).integrable_sq)]
    exact integral_congr_ae (ae_of_all _ fun x => (EuclideanSpace.real_norm_sq_eq (G i x)).symm)
  unfold ContinuumHamiltonian.kinetic singletState kinetic
  simp_rw [singlet_factor,← Finset.mul_sum,compSum]
  rw [sum_spin]

#print axioms spin_mass
#print axioms singletState_mass
#print axioms singletState_kinetic
end
end HFKinetic
