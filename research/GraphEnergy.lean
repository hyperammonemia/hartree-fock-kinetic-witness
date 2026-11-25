import GraphSpace
import Mathlib.MeasureTheory.Function.Holder

/-! The oscillator, pair interaction and bounded multiplicative field on the
actual two-electron graph domain. The norm is the ambient product maximum. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace GraphEnergy
open RadialConfiguration ClosedGraphDomain
abbrev D := graphSpace

def totalGradient (a : D) := ∑ p : Fin 2, ∑ i : Fin 3, ‖a.val.2.1 p i‖^2
def shiftEnergy (V : Config → ℝ) (a : D) :=
  (totalGradient a+‖a.val.2.2.1‖^2)/2 + ‖a.val.2.2.2‖^2/100 +
  ∫ x, V x*(a.val.1 x)^2

theorem mass_identity (u : Wave) : (∫ x, (u x)^2) = ‖u‖^2 := by
  have h := L2.inner_def (𝕜:=ℝ) u u
  simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using h.symm

private theorem integrable_sq (u : Wave) : Integrable (fun x => (u x)^2) := by
  simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using
    L2.integrable_inner (𝕜:=ℝ) u u

theorem trap_identity (a : D) : (∫ x : Config, (‖x.1‖^2+‖x.2‖^2)*(a.val.1 x)^2) =
    ‖a.val.2.2.1‖^2 := by
  rw [← mass_identity]
  apply integral_congr_ae
  filter_upwards [a.property.2.1] with x hx
  simp only [hx,mul_pow,trapWeight,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]

theorem pair_identity (a : D) : (∫ x : Config, (a.val.1 x)^2/‖x.1-x.2‖) =
    ‖a.val.2.2.2‖^2 := by
  rw [← mass_identity]
  apply integral_congr_ae
  filter_upwards [a.property.2.2] with x hx
  rw [hx,mul_pow,pairWeight,Real.sq_sqrt (inv_nonneg.mpr (norm_nonneg _))]
  ring

theorem bounded_term_integrable (V : Config → ℝ) (hm : Measurable V) {K : ℝ}
    (bound : ∀ x, |V x|≤K) (u : Wave) : Integrable (fun x => V x*(u x)^2) := by
  apply ((integrable_sq u).const_mul K).mono' (hm.aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable u).pow 2))
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_right (bound _) (sq_nonneg _)

private theorem grad_bound (a : D) (p : Fin 2) (i : Fin 3) : ‖a.val.2.1 p i‖^2 ≤ totalGradient a := by
  have h := Finset.single_le_sum (f:=fun j : Fin 3 => ‖a.val.2.1 p j‖^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact h.trans (Finset.single_le_sum (f:=fun q : Fin 2 => ∑ j : Fin 3, ‖a.val.2.1 q j‖^2)
    (fun q _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ p))

theorem graph_estimate (V : Config → ℝ) (hm : Measurable V) {K : ℝ}
    (bound : ∀ x, |V x|≤K) (a : D) :
    (1/100:ℝ)*‖a‖^2 ≤ shiftEnergy V a + (K+1)*‖waveMap a‖^2 := by
  let u := a.val.1
  have potential := integral_mono ((integrable_sq u).const_mul (-K))
    (bounded_term_integrable V hm bound u) (fun x => mul_le_mul_of_nonneg_right
      (abs_le.mp (bound x)).1 (sq_nonneg (u x)))
  rw [integral_const_mul,mass_identity] at potential
  let H := 100*(shiftEnergy V a+(K+1)*‖u‖^2)
  have grad0 : 0 ≤ totalGradient a := Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hg : totalGradient a ≤ H := by
    dsimp [H,shiftEnergy]; linarith [sq_nonneg ‖a.val.2.2.1‖,sq_nonneg ‖a.val.2.2.2‖,sq_nonneg ‖u‖]
  have ht : ‖a.val.2.2.1‖^2 ≤ H := by
    dsimp [H,shiftEnergy]; linarith [sq_nonneg ‖a.val.2.2.1‖,sq_nonneg ‖a.val.2.2.2‖,sq_nonneg ‖u‖]
  have hw : ‖a.val.2.2.2‖^2 ≤ H := by
    dsimp [H,shiftEnergy]; linarith [sq_nonneg ‖a.val.2.2.1‖,sq_nonneg ‖u‖]
  have hu : ‖u‖^2 ≤ H := by
    dsimp [H,shiftEnergy]; linarith [sq_nonneg ‖a.val.2.2.1‖,sq_nonneg ‖a.val.2.2.2‖,sq_nonneg ‖u‖]
  have sqH := Real.sq_sqrt (grad0.trans hg)
  have norm_le {v : Wave} (hv : ‖v‖^2≤H) : ‖v‖≤Real.sqrt H :=
    le_of_sq_le_sq (sqH.symm ▸ hv) (Real.sqrt_nonneg H)
  have big : ‖a‖≤Real.sqrt H := by
    change max ‖u‖ (max ‖a.val.2.1‖ (max ‖a.val.2.2.1‖ ‖a.val.2.2.2‖)) ≤ _
    refine max_le (norm_le hu) (max_le ?_ (max_le (norm_le ht) (norm_le hw)))
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg H)).2 (fun p =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg H)).2 (fun i => norm_le ((grad_bound a p i).trans hg)))
  have fin := pow_le_pow_left₀ (norm_nonneg a) big 2
  rw [sqH] at fin
  change (1/100:ℝ)*‖a‖^2 ≤ shiftEnergy V a + (K+1)*‖u‖^2
  linarith only [fin]

#print axioms trap_identity
#print axioms pair_identity
#print axioms graph_estimate
end GraphEnergy
