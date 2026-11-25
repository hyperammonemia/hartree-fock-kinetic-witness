import FixedKinetic
import SingletKinetic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases

open MeasureTheory FinitePotential
namespace HFKinetic
noncomputable section

def tensorSquare (u : Position → ℝ) (z : Configuration) := u z.1*u z.2
def orbitalNorm (u : Position → ℝ) : ℝ := Real.sqrt (∫ x, (weight x*u x)^2)
def normalizedOrbital (u : Position → ℝ) (x : Position) : ℝ := weight x*u x/orbitalNorm u

theorem stateNorm_tensor (u : Position → ℝ) : stateNorm (tensorSquare u) = orbitalNorm u ^ 2 := by
  let I := ∫ x, (weight x*u x)^2
  have hn : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hprod : (∫ z : Configuration, (weight z.1*weight z.2*tensorSquare u z)^2 ∂configMeasure) = I^2 := by
    calc
      _ = ∫ z : Configuration, (weight z.1*u z.1)^2*(weight z.2*u z.2)^2
              ∂(volume : Measure Position).prod volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by unfold tensorSquare; ring
      _ = I*I := integral_prod_mul (fun x => (weight x*u x)^2) (fun x => (weight x*u x)^2)
      _ = _ := (pow_two I).symm
  change Real.sqrt (∫ z : Configuration, (weight z.1*weight z.2*tensorSquare u z)^2 ∂configMeasure) =
    (Real.sqrt I)^2
  rw [hprod,Real.sqrt_sq hn,Real.sq_sqrt hn]

theorem normalizedWave_tensor (u : Position → ℝ) :
    normalizedWave (tensorSquare u) = tensorSquare (normalizedOrbital u) := by
  funext z
  unfold normalizedWave
  rw [stateNorm_tensor]
  unfold tensorSquare normalizedOrbital stepWeight
  simp only [div_eq_mul_inv]
  ring

/-- The exact spin factors in the continuum determinant agree with the two-component singlet. -/
theorem singlet_of_tensor_closedShell (u : Position → ℝ)
    (G : Fin 2 → Configuration → Position) (hy : MemLp (tensorSquare u) 2 volume)
    (hg : ∀ i, MemLp (G i) 2 volume) (weak : ∀ i j, ContinuumHamiltonian.IsWeakPartial
      (fun x => (tensorSquare u x : ℂ)) (fun x => (G i x j : ℂ)) (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.IsClosedShell (singletState (tensorSquare u) G hy hg weak) (fun x => (u x : ℂ)) := by
  intro a b
  refine ae_of_all _ fun z => ?_
  fin_cases a <;> fin_cases b <;>
    norm_num [singletState,singletSpin,tensorSquare,ContinuumHamiltonian.determinant,
      div_eq_mul_inv,mul_comm,mul_left_comm]

#print axioms stateNorm_tensor
#print axioms normalizedWave_tensor
#print axioms singlet_of_tensor_closedShell
end
end HFKinetic
