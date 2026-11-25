import ModulatedWeak
import StateKineticOrder
import SingletKinetic

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

/-- The field belongs to the domain of the physical spin Hamiltonian before
multiplication by the fixed radial weight. -/
def SpatialWeak (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position) : Prop :=
  ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun q => (Y q : ℂ)) (fun q => (d i q j : ℂ))
    (ContinuumHamiltonian.axis i j)

def normalizedPhysicalSinglet (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (hy : MemLp Y 2 configMeasure) (hd : ∀ i, MemLp (d i) 2 configMeasure)
    (hw : SpatialWeak Y d) : ContinuumHamiltonian.State :=
  singletState (normalizedWave Y) (physicalGradient Y d) (normalizedWave_memLp Y hy)
    (physicalGradient_memLp Y d hy hd) (fun i j => physicalGradient_isWeakPartial Y d i j
      hy.ofReal (component_memLp (hd i) j).ofReal (hw i j))

theorem normalizedPhysicalSinglet_mass (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (hy : MemLp Y 2 configMeasure) (hd : ∀ i, MemLp (d i) 2 configMeasure)
    (hw : SpatialWeak Y d) (mass : (∫ x, Y x^2 ∂configMeasure) = 1) :
    ContinuumHamiltonian.mass (normalizedPhysicalSinglet Y d hy hd hw) = 1 :=
  (singletState_mass ..).trans (normalizedWave_mass Y hy.integrable_sq mass)

theorem normalizedPhysicalSinglet_kinetic (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (hy : MemLp Y 2 configMeasure) (hd : ∀ i, MemLp (d i) 2 configMeasure)
    (hw : SpatialWeak Y d) :
    ContinuumHamiltonian.kinetic (normalizedPhysicalSinglet Y d hy hd hw) =
      kinetic configMeasure (physicalGradient Y d) := singletState_kinetic ..

/-- The actual complex-spin continuum kinetic observables of these states
are ordered under the finite marginal contrast and the reference-state distance. -/
theorem physicalSinglet_kinetic_order
    (U R P : Configuration → ℝ) (dU dP : Fin 2 → Configuration → Position)
    (hU : MemLp U 2 configMeasure) (hR : MemLp R 2 configMeasure) (hP : MemLp P 2 configMeasure)
    (mU : (∫ x, U x^2 ∂configMeasure) = 1)
    (mR : (∫ x, R x^2 ∂configMeasure) = 1)
    (mP : (∫ x, P x^2 ∂configMeasure) = 1)
    (hdu : ∀ i, MemLp (dU i) 2 configMeasure) (hdp : ∀ i, MemLp (dP i) 2 configMeasure)
    (wU : SpatialWeak U dU) (wP : SpatialWeak P dP)
    (gU : (∑ i : Fin 2, ∫ x, ‖dU i x‖^2 ∂configMeasure) ≤ 8)
    (gP : (∑ i : Fin 2, ∫ x, ‖dP i x‖^2 ∂configMeasure) ≤ 8)
    (distance : (∫ x, (P x-R x)^2 ∂configMeasure) ≤ (5*(margin/1000))^2)
    (density : margin ≤ probe configMeasure U sineProfile - probe configMeasure R sineProfile) :
    ContinuumHamiltonian.kinetic (normalizedPhysicalSinglet P dP hP hdp wP) <
    ContinuumHamiltonian.kinetic (normalizedPhysicalSinglet U dU hU hdu wU) := by
  rw [normalizedPhysicalSinglet_kinetic,normalizedPhysicalSinglet_kinetic]
  exact kinetic_order_of_density_distance U R P dU dP hU hR hP mU mR mP hdu hdp gU gP distance density

#print axioms normalizedPhysicalSinglet_mass
#print axioms physicalSinglet_kinetic_order
end
end HFKinetic
