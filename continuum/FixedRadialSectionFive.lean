import SectionFive
import FixedRadialDomain

noncomputable section
namespace FixedRadialSectionFive
open SectionFive RadialConfiguration MeasureTheory Set
open scoped InnerProductSpace

def measures {dom : Submodule ℝ Wave} (G : DomainData dom) : Measures dom Config where
  mass s := mass s.val.val
  positiveEnergy s := densityMeasure (positiveDensity G.toWeakGradient s.val)
  probability s := mass_probability s.val.val s.property
  finiteEnergy s := positiveMeasure_finite G.toWeakGradient s.val (G.positiveIntegrable s.val)

theorem positive_mass_eq {dom : Submodule ℝ Wave} (G : DomainData dom) (u : UnitState dom) :
    ((measures G).positiveEnergy u).real univ = ∫ z, positiveDensity G.toWeakGradient u.val z := by
  change ENNReal.toReal ((densityMeasure (positiveDensity G.toWeakGradient u.val)) univ) = _
  rw [density_univ (G.positiveIntegrable u.val) (positiveDensity_nonneg _ _),
    ENNReal.toReal_ofReal (integral_nonneg (positiveDensity_nonneg _ _))]

def shiftedDensity {dom : Submodule ℝ Wave} (G : WeakGradient dom) (u : dom) (z : Config) : ℝ :=
  (∑ p : Fin 2, ∑ i : Fin 3, (G.component u p i z+coord z p i*u.val z)^2)/2

/-- The repulsive term permits the explicit shifted oscillator as a lower
comparison. No unknown interacting spectral data enter this estimate. -/
theorem shiftedPart_le_positive {dom : Submodule ℝ Wave} (G : DomainData dom) (u : UnitState dom) :
    (∫ z, shiftedDensity G.toWeakGradient u.val z) ≤ ((measures G).positiveEnergy u).real univ := by
  rw [positive_mass_eq]
  have nonneg (z : Config) : 0 ≤ shiftedDensity G.toWeakGradient u.val z := by
    unfold shiftedDensity
    positivity
  have lower (z : Config) : shiftedDensity G.toWeakGradient u.val z ≤
      positiveDensity G.toWeakGradient u.val z := by
    change shiftedDensity G.toWeakGradient u.val z ≤
      shiftedDensity G.toWeakGradient u.val z+(u.val.val z)^2/(100*‖z.1-z.2‖)
    exact le_add_of_nonneg_right (by positivity)
  exact integral_mono_of_nonneg (ae_of_all _ nonneg) (G.positiveIntegrable u.val) (ae_of_all _ lower)

def fields (wM : Measurable weight) (jM : Measurable j) (jfM : Measurable jf) : Fields Config :=
  ⟨weight,j,jf,wM,jM,jfM⟩

/-- Bounds in oscillator units for the actual fixed local fields, the
six-coordinate weak kinetic energy and the product-volume L² distance.
The sign convention is recovered from the nonnegative representatives. -/
structure Conclusion {dom : Submodule ℝ Wave} (G : DomainData dom)
    (T : dom ≃ₗ[ℝ] dom) (ψ Φ : UnitState dom) : Prop where
  baselinePositive : (∫ z, positiveDensity G.toWeakGradient ψ.val z) ≤ 1/25
  pulledPositive : (∫ z, positiveDensity G.toWeakGradient (pulled T Φ).val z) ≤ 11/100
  newEnergyLower : physicalEnergy G.toWeakGradient vOld ψ-21/5*b ≤
    physicalEnergy G.toWeakGradient vNew Φ
  newEnergyUpper : physicalEnergy G.toWeakGradient vNew Φ ≤
    physicalEnergy G.toWeakGradient vOld ψ+14/5*b
  excessNonneg : 0 ≤ physicalEnergy G.toWeakGradient vOld (pulled T Φ)-
    physicalEnergy G.toWeakGradient vOld ψ
  excessUpper : physicalEnergy G.toWeakGradient vOld (pulled T Φ)-
    physicalEnergy G.toWeakGradient vOld ψ ≤ 7*b
  commonSignDistance :
    (‖(pulled T Φ).val.val-ψ.val.val‖ ≤ 4*Real.sqrt b ∧
      ‖Φ.val.val-ψ.val.val‖ ≤ 4*Real.sqrt b+6*b) ∨
    (‖(pulled T Φ).val.val+ψ.val.val‖ ≤ 4*Real.sqrt b ∧
      ‖Φ.val.val+ψ.val.val‖ ≤ 4*Real.sqrt b+6*b)
  pulledDistance : (∀ᵐ z : Config ∂volume, 0 ≤ ψ.val.val z) →
    (∀ᵐ z : Config ∂volume, 0 ≤ Φ.val.val z) →
    ‖(pulled T Φ).val.val-ψ.val.val‖ ≤ 4*Real.sqrt b
  physicalDistance : (∀ᵐ z : Config ∂volume, 0 ≤ ψ.val.val z) →
    (∀ᵐ z : Config ∂volume, 0 ≤ Φ.val.val z) →
    ‖Φ.val.val-ψ.val.val‖ ≤ 4*Real.sqrt b+6*b
  pulledKinetic : kinetic G.toWeakGradient (pulled T Φ).val ≤ 311/100

set_option maxHeartbeats 1000000 in
/-- Physical hypotheses are stated on all trials, or as Gaussian identities.
No small energy error, interacting spectral-gap estimate, or overlap bound
for the selected pair is an input. All estimates hold up to sign for every
minimizing pair. Nonnegative representatives also give an oriented distance. -/
theorem fixed_radial_stability (dom : Submodule ℝ Wave) (G : DomainData dom)
    (T : dom ≃ₗ[ℝ] dom) (q osc : Form dom) (g : GaussianState dom) (ψ Φ : UnitState dom)
    (wM : Measurable weight) (jM : Measurable j) (jfM : Measurable jf)
    (mulRule : ∀ u : dom, ∀ᵐ z : Config ∂volume, (T u).val z=multiplier z*u.val z)
    (newtonBound : ∀ z, |j z| ≤ 4) (newtonChange : ∀ z, |jf z-j z| ≤ 24*b)
    (oldBilinear : ∀ u, energy q u=physicalEnergy G.toWeakGradient vOld u)
    (bareTransform : ∀ u, physicalEnergy G.toWeakGradient vOld u =
      baseRayleigh (fields wM jM jfM) ((measures G).mass u) ((measures G).positiveEnergy u))
    (dressedTransform : ∀ u, physicalEnergy G.toWeakGradient vNew ((normalizedEquiv T) u) =
      newRayleigh (fields wM jM jfM) ((measures G).mass u) ((measures G).positiveEnergy u))
    (oscillatorValue : ∀ u, energy osc u = ∫ z, shiftedDensity G.toWeakGradient u.val z)
    (oscillatorGap : ∀ z : dom, ⟪g.state.val,z⟫_ℝ=0 → ‖z‖^2 ≤ osc z z)
    (direct : ℝ) (gaussianPositive : 100*((measures G).positiveEnergy g.state).real univ=direct)
    (gaussianHartree : (∫ z, j z ∂((measures G).mass g.state))=2*direct)
    (oldMin : Minimizes (physicalEnergy G.toWeakGradient vOld) ψ)
    (newMin : Minimizes (physicalEnergy G.toWeakGradient vNew) Φ) :
    Conclusion G T ψ Φ := by
  have old : Minimizes (energy q) ψ := fun u => by simpa only [oldBilinear] using oldMin u
  have h := variational_stability_on_domain dom q osc (physicalEnergy G.toWeakGradient vNew)
    T (fields wM jM jfM) (measures G) g.state ψ Φ b direct FinitePotential.amplitude_pos.le
    amplitude_small weight_window newtonBound newtonChange
    (fun u => (oldBilinear u).trans (bareTransform u)) dressedTransform
    (fun u => (oscillatorValue u).le.trans (shiftedPart_le_positive G u))
    oscillatorGap gaussianPositive gaussianHartree old newMin
  have movement := normalized_multiplier_displacement T mulRule (pulled T Φ)
  change ‖((normalizedEquiv T) ((normalizedEquiv T).symm Φ)).val-(pulled T Φ).val‖ ≤ _ at movement
  rw [Equiv.apply_symm_apply] at movement
  have triangle : ‖Φ.val-ψ.val‖ ≤ ‖Φ.val-(pulled T Φ).val‖+‖(pulled T Φ).val-ψ.val‖ := by
    simpa only [dist_eq_norm] using dist_triangle Φ.val (pulled T Φ).val ψ.val
  have plusTriangle : ‖Φ.val+ψ.val‖ ≤ ‖Φ.val-(pulled T Φ).val‖+‖(pulled T Φ).val+ψ.val‖ := by
    simpa only [dist_eq_norm, sub_neg_eq_add] using dist_triangle Φ.val (pulled T Φ).val (-ψ.val)
  have directMinus (d : ‖(pulled T Φ).val-ψ.val‖ ≤ 4*Real.sqrt b) :
      ‖Φ.val-ψ.val‖ ≤ 4*Real.sqrt b+6*b := by linarith only [triangle, movement, d]
  have directPlus (d : ‖(pulled T Φ).val+ψ.val‖ ≤ 4*Real.sqrt b) :
      ‖Φ.val+ψ.val‖ ≤ 4*Real.sqrt b+6*b := by linarith only [plusTriangle, movement, d]
  have oldNonpos := h.oldMinimumNonpos
  have cost := h.pulledExcess.2
  simp only [oldBilinear] at oldNonpos cost
  have tBound := kinetic_le_old G (pulled T Φ) newtonBound
  exact ⟨by simpa only [positive_mass_eq] using h.oldPositiveBound,
    by simpa only [positive_mass_eq] using h.pulledPositiveBound, by simpa only [oldBilinear] using h.newEnergyLower,
    by simpa only [oldBilinear] using h.newEnergyUpper,
    by simpa only [oldBilinear] using h.pulledExcess.1,
    by simpa only [oldBilinear] using h.pulledExcess.2,
    h.distanceUpToSign.imp (fun d => ⟨d, directMinus d⟩) (fun d => ⟨d, directPlus d⟩),
    fun ψpos Φpos => h.orientedDistance (overlap_nonneg T ψ Φ mulRule ψpos Φpos),
    fun ψpos Φpos => directMinus (h.orientedDistance (overlap_nonneg T ψ Φ mulRule ψpos Φpos)),
    by linarith only [oldNonpos, cost, tBound, amplitude_small]⟩

#check fixed_radial_stability
#check Conclusion.commonSignDistance
#check Conclusion.pulledKinetic
#print axioms fixed_radial_stability
end FixedRadialSectionFive
