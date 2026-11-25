import PhysicalGradient
import ProbeStability
import KineticDilation

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

private theorem weighted_probe_integrable (Y : Configuration → ℝ)
    (hY : MemLp Y 2 configMeasure) (i : Fin 2) :
    Integrable (fun x => sineProfile i x^2*Y x^2) configMeasure := by
  have hp := (position_continuous i).norm
  have hs : MemLp (sineProfile i) ⊤ configMeasure :=
    memLp_top_of_bound ((envelope_c1.continuous.comp hp).mul
      (Real.continuous_sin.comp (continuous_const.mul hp))).aestronglyMeasurable 1
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using sineProfile_abs i x)
  have h : MemLp (fun x => sineProfile i x*Y x) 2 configMeasure := hs.fun_mul hY
  simpa only [mul_pow] using h.integrable_sq

/-- The radial density contrast and the distance of the pulled-back state
suffice for the kinetic ordering of the two explicitly normalized waves.
All quantities being compared are finite integrals of their displayed gradients. -/
theorem kinetic_order_of_density_distance
    (U R P : Configuration → ℝ) (dU dP : Fin 2 → Configuration → Position)
    (hU : MemLp U 2 configMeasure) (hR : MemLp R 2 configMeasure) (hP : MemLp P 2 configMeasure)
    (mU : (∫ x, U x^2 ∂configMeasure) = 1)
    (mR : (∫ x, R x^2 ∂configMeasure) = 1)
    (mP : (∫ x, P x^2 ∂configMeasure) = 1)
    (hdu : ∀ i, MemLp (dU i) 2 configMeasure) (hdp : ∀ i, MemLp (dP i) 2 configMeasure)
    (gU : (∑ i : Fin 2, ∫ x, ‖dU i x‖^2 ∂configMeasure) ≤ 8)
    (gP : (∑ i : Fin 2, ∫ x, ‖dP i x‖^2 ∂configMeasure) ≤ 8)
    (distance : (∫ x, (P x-R x)^2 ∂configMeasure) ≤ (5*(margin/1000))^2)
    (density : margin ≤ probe configMeasure U sineProfile - probe configMeasure R sineProfile) :
    kinetic configMeasure (physicalGradient P dP) < kinetic configMeasure (physicalGradient U dU) := by
  have hδ : 0 < 5*(margin/1000) := by positivity [margin_pos]
  have dist := probe_stability configMeasure P R sineProfile hδ hP.integrable_sq hR.integrable_sq
    (hP.sub hR).integrable_sq mP mR distance (weighted_probe_integrable P hP)
    (weighted_probe_integrable R hR) (fun i => ae_of_all _ (sineProfile_abs i))
  have hu := abs_le.mp (physical_kinetic_remainder U dU hU mU hdu gU)
  have hv := abs_le.mp (physical_kinetic_remainder P dP hP mP hdp gP)
  apply sign_at_fixed_parameters _ _ _ _ _ density
  · linarith [(abs_le.mp dist).2]
  · linarith [hu.1, amplitude_pos]
  · linarith [hv.2, amplitude_pos]

#print axioms kinetic_order_of_density_distance
end
end HFKinetic
