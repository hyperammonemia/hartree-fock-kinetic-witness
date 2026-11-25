import ContinuumHamiltonian
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Uniqueness of the recorded weak gradients, including under a change of
representative of the spin wavefunction. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumHamiltonian

theorem weakPartial_congr {u w du dw : Config → ℂ} {v : Config}
    (huw : u =ᵐ[volume] w) (hu : IsWeakPartial u du v) (hw : IsWeakPartial w dw v)
    (idu : MemLp du 2 volume) (idw : MemLp dw 2 volume) : du =ᵐ[volume] dw := by
  apply ae_eq_of_integral_contDiff_smul_eq (idu.locallyIntegrable (by norm_num))
    (idw.locallyIntegrable (by norm_num))
  intro φ hφ hc
  have h₁ := hu φ (hφ.of_le (by decide)) hc
  have h₂ := hw φ (hφ.of_le (by decide)) hc
  have eq : (∫ z, u z * ((fderiv ℝ φ z v : ℝ) : ℂ)) =
      ∫ z, w z * ((fderiv ℝ φ z v : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [huw] with z hz
    rw [hz]
  rw [h₁,h₂] at eq
  simpa only [Complex.real_smul, mul_comm] using neg_injective eq

theorem kinetic_congr {u w : State} (h : ∀ a b, u.wave a b =ᵐ[volume] w.wave a b) :
    kinetic u = kinetic w := by
  unfold kinetic
  apply congrArg (fun x : ℝ => x / 2)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  apply integral_congr_ae
  filter_upwards [weakPartial_congr (h a b) (u.weakGradient a b p j)
    (w.weakGradient a b p j) (u.gradSquareIntegrable a b p j) (w.gradSquareIntegrable a b p j)]
    with z hz
  rw [hz]

#print axioms weakPartial_congr
#print axioms kinetic_congr
end ContinuumHamiltonian
