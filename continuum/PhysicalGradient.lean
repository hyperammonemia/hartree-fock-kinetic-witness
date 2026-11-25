import FixedKinetic
import RadialDifferential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

/-- The arbitrary unit vector at the origin disappears from the gradient because
the radial cutoff and its derivative vanish there. -/
def radialUnit (x : Position) : Position :=
  if x = 0 then EuclideanSpace.single 0 1 else ‖x‖⁻¹ • x

theorem radialUnit_norm (x : Position) : ‖radialUnit x‖ = 1 := by
  by_cases h : x = 0
  · subst x
    simp [radialUnit,EuclideanSpace.single]
  · rw [radialUnit,ite_eq_right h,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

theorem radialUnit_measurable : Measurable radialUnit := by
  exact Measurable.ite (measurableSet_singleton (0:Position)) measurable_const
    (continuous_norm.measurable.inv.smul measurable_id)

theorem position_continuous (i : Fin 2) : Continuous (position i) := by
  by_cases h : i = 0
  · have eq : position i = (Prod.fst : Configuration → Position) := funext fun _ => ite_eq_left h
    rw [eq]; exact continuous_fst
  · have eq : position i = (Prod.snd : Configuration → Position) := funext fun _ => ite_eq_right h
    rw [eq]; exact continuous_snd

theorem remaining_continuous (i : Fin 2) : Continuous (remaining i) := by
  by_cases h : i = 0
  · have eq : remaining i = (Prod.snd : Configuration → Position) := funext fun _ => ite_eq_left h
    rw [eq]; exact continuous_snd
  · have eq : remaining i = (Prod.fst : Configuration → Position) := funext fun _ => ite_eq_right h
    rw [eq]; exact continuous_fst

theorem radialSlope_zero : radialSlope 0 = 0 := by
  have h : (0:ℝ)-radius ≤ 0 := by linarith [show 0 < radius from Real.exp_pos _]
  have hs : switchSlope (0-radius) = 0 := ite_eq_left h
  have hv : FinitePotential.switch (0-radius) = 0 := ite_eq_left h
  unfold radialSlope
  rw [(envelope_derivative 0).deriv,hs,hv]
  simp

theorem radialSlope_unit_component (x : Position) (j : Fin 3) :
    radialSlope ‖x‖ * radialUnit x j = radialSlope ‖x‖ * (x j/‖x‖) := by
  by_cases h : x = 0
  · subst x; simp [radialSlope_zero]
  · simp [radialUnit,h,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

private theorem weight_abs (x : Position) : |weight x| ≤ 1+amplitude := by
  have h := abs_le.mp (weight_near_one x)
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

private theorem weight_top {p : Configuration → Position} (hp : Continuous p) :
    MemLp (fun x => weight (p x)) ⊤ configMeasure :=
  memLp_top_of_bound (weight_c1.continuous.comp hp).aestronglyMeasurable (1+amplitude)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using weight_abs (p x))

def physicalGradient (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (i : Fin 2) (x : Configuration) : Position :=
  modulatedGradient Y d (fun k q => radialUnit (position k q)) i x

/-- Dividing by the actual state norm preserves square integrability. -/
theorem normalizedWave_memLp (Y : Configuration → ℝ) (hY : MemLp Y 2 configMeasure) :
    MemLp (normalizedWave Y) 2 configMeasure := by
  have h : MemLp (fun x : Configuration => weight x.1*weight x.2) ⊤ configMeasure :=
    (weight_top continuous_fst).fun_mul (weight_top continuous_snd)
  have h' := h.mul_const (stateNorm Y)⁻¹
  change MemLp (fun x : Configuration => ((weight x.1*weight x.2)/stateNorm Y)*Y x) 2 configMeasure
  simpa only [div_eq_mul_inv] using
    (h'.fun_mul hY : MemLp (fun x => ((weight x.1*weight x.2)*(stateNorm Y)⁻¹)*Y x) 2 configMeasure)

/-- The gradient displayed by the product rule lies in L² for every H¹ input. -/
theorem physicalGradient_memLp (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (hY : MemLp Y 2 configMeasure) (hd : ∀ i, MemLp (d i) 2 configMeasure) (i : Fin 2) :
    MemLp (physicalGradient Y d i) 2 configMeasure := by
  let a : Configuration → ℝ := fun x => stepWeight x / stateNorm Y
  let o : Configuration → ℝ := fun x => weight (remaining i x)/stateNorm Y
  let e : Configuration → Position := fun x => radialUnit (position i x)
  have ha : MemLp a ⊤ configMeasure := by
    simpa only [a,stepWeight,div_eq_mul_inv] using
      ((weight_top continuous_fst).fun_mul (weight_top continuous_snd) :
        MemLp (fun x => weight x.1*weight x.2) ⊤ configMeasure).mul_const (stateNorm Y)⁻¹
  have ho : MemLp o ⊤ configMeasure := by
    simpa only [o,div_eq_mul_inv] using (weight_top (remaining_continuous i)).mul_const (stateNorm Y)⁻¹
  have hp := (position_continuous i).norm
  have ht : MemLp (cutoffProfile i) ⊤ configMeasure :=
    memLp_top_of_bound ((envelope_c1.continuous_deriv_one.comp hp).mul
      (Real.continuous_cos.comp (continuous_const.mul hp))).aestronglyMeasurable 2
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using cutoffProfile_abs i x)
  have hs : MemLp (sineProfile i) ⊤ configMeasure :=
    memLp_top_of_bound ((envelope_c1.continuous.comp hp).mul
      (Real.continuous_sin.comp (continuous_const.mul hp))).aestronglyMeasurable 1
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using sineProfile_abs i x)
  have he : MemLp e ⊤ configMeasure := memLp_top_of_bound
    (radialUnit_measurable.comp (position_continuous i).measurable).aestronglyMeasurable 1
    (ae_of_all _ fun x => (radialUnit_norm (position i x)).le)
  have hc : MemLp (fun x => o x*(amplitude*(cutoffProfile i x-frequency*sineProfile i x))) ⊤ configMeasure :=
    ho.fun_mul ((ht.sub (hs.const_mul frequency)).const_mul amplitude)
  have hcy : MemLp (fun x => o x*(amplitude*(cutoffProfile i x-frequency*sineProfile i x))*Y x)
      2 configMeasure := hc.fun_mul hY
  exact (ha.smul (hd i) : MemLp (a • d i) 2 configMeasure).add
    (hcy.smul he : MemLp _ 2 configMeasure)

/-- With the actual unit radial field, all integrability assumptions for the
normalized physical gradient follow from those of the unmodulated state. -/
theorem physical_kinetic_remainder (Y : Configuration → ℝ) (d : Fin 2 → Configuration → Position)
    (hY : MemLp Y 2 configMeasure) (mass : (∫ x, Y x^2 ∂configMeasure) = 1)
    (hd : ∀ i, MemLp (d i) 2 configMeasure)
    (hgrad : (∑ i : Fin 2, ∫ x, ‖d i x‖^2 ∂configMeasure) ≤ 8) :
    |(2/(amplitude*frequency)^2)*kinetic configMeasure (physicalGradient Y d) -
         probe configMeasure Y sineProfile| ≤ 54*amplitude := by
  apply constructed_kinetic_remainder Y d (fun i x => radialUnit (position i x))
    hY.integrable_sq mass
  · exact fun i => (memLp_two_iff_integrable_sq_norm (hd i).aestronglyMeasurable).1 (hd i)
  · intro i
    have h := physicalGradient_memLp Y d hY hd i
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  · exact hgrad
  · exact fun i => ae_of_all _ fun x => radialUnit_norm (position i x)

#print axioms radialSlope_unit_component
#print axioms physicalGradient_memLp
#print axioms physical_kinetic_remainder
end
end HFKinetic
