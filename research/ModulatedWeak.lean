import PhysicalGradient
import WeakProduct

open MeasureTheory FinitePotential
namespace HFKinetic
noncomputable section

theorem normalizedWeight_axis (Y : Configuration → ℝ) (i : Fin 2) (j : Fin 3) (x : Configuration) :
    fderiv ℝ (fun q => stepWeight q / stateNorm Y) x (ContinuumHamiltonian.axis i j) =
      (weight (remaining i x)/stateNorm Y) *
         (amplitude * (cutoffProfile i x - frequency*sineProfile i x)) *
         (position i x j / ‖position i x‖) := by
  by_cases hi : i = 0
  · simpa [ContinuumHamiltonian.axis,stepWeight,position,remaining,cutoffProfile,sineProfile,radialSlope,hi,mul_assoc]
      using product_weight_first x j (stateNorm Y)
  · simpa [ContinuumHamiltonian.axis,stepWeight,position,remaining,cutoffProfile,sineProfile,radialSlope,hi,mul_assoc]
      using product_weight_second x j (stateNorm Y)

/-- For a real spatial singlet amplitude regarded as a complex wavefunction, each
displayed component is genuinely the weak derivative of its normalized modulation. -/
theorem normalizedWave_weak_partial (Y dY : Configuration → ℝ) (i : Fin 2) (j : Fin 3)
    (hu : MemLp (fun x => (Y x : ℂ)) 2 volume)
    (hd : MemLp (fun x => (dY x : ℂ)) 2 volume)
    (weak : ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (dY x : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.IsWeakPartial (fun x => (normalizedWave Y x : ℂ))
      (fun x => (((stepWeight x/stateNorm Y)*dY x +
        (weight (remaining i x)/stateNorm Y) *
           (amplitude * (cutoffProfile i x - frequency*sineProfile i x)) *
           (position i x j / ‖position i x‖)*Y x : ℝ) : ℂ))
      (ContinuumHamiltonian.axis i j) := by
  let w := fun x : Configuration => stepWeight x/stateNorm Y
  have hprod := ContinuumHamiltonian.weakPartial_mul hu hd weak w (product_weight_c1 (stateNorm Y))
  have waveEq : (fun x => (Y x : ℂ)*(w x : ℂ)) = (fun x => (normalizedWave Y x : ℂ)) := by
    funext x
    simp [w,normalizedWave,mul_comm]
  rw [waveEq] at hprod
  convert hprod using 1
  funext x
  dsimp only [w]
  rw [normalizedWeight_axis]
  push_cast
  ring

theorem physicalGradient_component (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (i : Fin 2) (j : Fin 3) (x : Configuration) :
    physicalGradient Y d i x j = (stepWeight x/stateNorm Y)*d i x j +
      (weight (remaining i x)/stateNorm Y) * (amplitude*(cutoffProfile i x-frequency*sineProfile i x)) *
          (position i x j / ‖position i x‖)*Y x := by
  have hs : cutoffProfile i x-frequency*sineProfile i x = radialSlope ‖position i x‖ := by
    unfold cutoffProfile sineProfile radialSlope
    ring
  change (stepWeight x/stateNorm Y)*d i x j +
    ((weight (remaining i x)/stateNorm Y) * (amplitude*(cutoffProfile i x-frequency*sineProfile i x))*Y x) *
      radialUnit (position i x) j = _
  rw [hs]
  linear_combination (weight (remaining i x)/stateNorm Y*amplitude*Y x) *
    radialSlope_unit_component (position i x) j

/-- Every component of the very vector field in the finite kinetic comparison
is the weak partial of its normalized wave in the six-dimensional Hamiltonian. -/
theorem physicalGradient_isWeakPartial (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (i : Fin 2) (j : Fin 3) (hu : MemLp (fun x => (Y x : ℂ)) 2 volume)
    (hd : MemLp (fun x => (d i x j : ℂ)) 2 volume)
    (hw : ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (d i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.IsWeakPartial (fun x => (normalizedWave Y x : ℂ))
      (fun x => (physicalGradient Y d i x j : ℂ)) (ContinuumHamiltonian.axis i j) := by
  simpa only [physicalGradient_component] using normalizedWave_weak_partial Y (fun x => d i x j) i j hu hd hw

#print axioms normalizedWave_weak_partial
#print axioms physicalGradient_isWeakPartial
end
end HFKinetic

