import ProductGaussian
import GaussianCore
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
noncomputable section
namespace OscillatorGaussian

/-- Oscillator probability measure with Lebesgue density exp(-x²)/sqrt π. -/
abbrev γ : Measure ℝ := gaussianReal 0 (1/2)

private theorem density (x : ℝ) : gaussianPDFReal 0 (1/2) x =
    (Real.sqrt Real.pi)⁻¹ * Real.exp (-(x^2)) := by
  norm_num [gaussianPDFReal]
  <;> ring_nf

theorem gaussian_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂γ) = (Real.sqrt Real.pi)⁻¹ * ∫ x, Real.exp (-(x^2))*f x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1/2 : ℝ≥0)≠0)]
  simp only [density,smul_eq_mul,mul_assoc,integral_const_mul]

private theorem weighted_integrable {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) {C : ℝ} (hb : ∀ x, ‖f x‖≤C) :
    Integrable (fun x => Real.exp (-(x^2))*‖f x‖^2) := by
  have hw : Integrable (fun x : ℝ => Real.exp (-(x^2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)
  apply hw.mul_bdd (c := C^2) (hf.norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hb x))).mpr (hb x)

/-- An anchored Gaussian Poincaré bound for every bounded C¹ trajectory with
    bounded derivative. Both integrability assumptions are discharged. -/
theorem line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f d : ℝ → E) (hd : ∀ t, HasDerivAt f (d t) t) (hc : Continuous d)
    {C D : ℝ} (hfB : ∀ t, ‖f t‖≤C) (hdB : ∀ t, ‖d t‖≤D) :
    (∫ t, ‖f t-f 0‖^2 ∂γ) ≤ (∫ t, ‖d t‖^2 ∂γ)/2 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hdev (t : ℝ) : ‖f t-f 0‖≤C+C := (norm_sub_le _ _).trans (add_le_add (hfB t) (hfB 0))
  have h := GaussianCore.gaussian_line f d hd hc
    (weighted_integrable _ (hf.sub continuous_const) hdev) (weighted_integrable d hc hdB)
  rw [gaussian_integral,gaussian_integral]
  have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg Real.pi))
  linarith

section Products
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Integrate the two slice inequalities without differentiating through a
    conditional expectation. The centers on the two fibers are independent. -/
theorem product_from_slices (f : X × Y → ℂ) (u : X → ℂ) (v : Y → ℂ)
    (A B : X × Y → ℝ) (hf : MemLp f 2 (μ.prod ν)) (hu : MemLp u 2 μ)
    (hv : MemLp v 2 ν) (hA : Integrable A (μ.prod ν)) (hB : Integrable B (μ.prod ν))
    (hx : ∀ y, (∫ x, ‖f (x,y)-v y‖^2 ∂μ) ≤ (∫ x, A (x,y) ∂μ)/2)
    (hy : ∀ x, (∫ y, ‖f (x,y)-u x‖^2 ∂ν) ≤ (∫ y, B (x,y) ∂ν)/2) :
    (∫ z, ‖f z-(∫ t, f t ∂(μ.prod ν))‖^2 ∂(μ.prod ν)) ≤
      ((∫ z, A z ∂(μ.prod ν))+(∫ z, B z ∂(μ.prod ν)))/2 := by
  let D (z : X × Y) := ‖f z-u z.1‖^2
  let E (z : X × Y) := ‖f z-v z.2‖^2
  have hu' := hf.sub (hu.comp_measurePreserving (measurePreserving_fst (μ:=μ) (ν:=ν)))
  have hv' := hf.sub (hv.comp_measurePreserving (measurePreserving_snd (μ:=μ) (ν:=ν)))
  have hD : Integrable D (μ.prod ν) := (memLp_two_iff_integrable_sq_norm hu'.aestronglyMeasurable).mp hu'
  have hE : Integrable E (μ.prod ν) := (memLp_two_iff_integrable_sq_norm hv'.aestronglyMeasurable).mp hv'
  have h1 : (∫ z, E z ∂(μ.prod ν)) ≤ (∫ z, A z ∂(μ.prod ν))/2 := by
    rw [integral_prod_symm E hE,integral_prod_symm A hA,← integral_div]
    exact integral_mono hE.integral_prod_right (hA.integral_prod_right.div_const 2) hx
  have h2 : (∫ z, D z ∂(μ.prod ν)) ≤ (∫ z, B z ∂(μ.prod ν))/2 := by
    rw [integral_prod D hD,integral_prod B hB,← integral_div]
    exact integral_mono hD.integral_prod_left (hB.integral_prod_left.div_const 2) hy
  have h3 := ProductGaussian.product_variance_integral μ ν f u v hf hu hv
  change _ ≤ (∫ z, D z ∂(μ.prod ν))+(∫ z, E z ∂(μ.prod ν)) at h3
  linarith
end Products

private theorem mem_bounded {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℂ} (hm : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hm C (Filter.Eventually.of_forall hC)

private theorem square_mem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (h : MemLp f 2 μ) : Integrable (fun x => ‖f x‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- Cartesian two-dimensional oscillator with a uniform bound on the function
    and its two partial derivatives, in particular every C¹ compact test. -/
theorem plane (f dx dy : ℝ × ℝ → ℂ) (hf : Continuous f)
    (hdx : Continuous dx) (hdy : Continuous dy) {C : ℝ}
    (hb : ∀ z, ‖f z‖≤C ∧ ‖dx z‖≤C ∧ ‖dy z‖≤C)
    (hx : ∀ x y, HasDerivAt (fun t => f (t,y)) (dx (x,y)) x)
    (hy : ∀ x y, HasDerivAt (fun t => f (x,t)) (dy (x,y)) y) :
    (∫ z, ‖f z-(∫ t, f t ∂(γ.prod γ))‖^2 ∂(γ.prod γ)) ≤
      ((∫ z, ‖dx z‖^2 ∂(γ.prod γ))+(∫ z, ‖dy z‖^2 ∂(γ.prod γ)))/2 := by
  have cx (y : ℝ) : Continuous (fun t : ℝ => (t,y)) := continuous_id.prodMk continuous_const
  have cy (x : ℝ) : Continuous (fun t : ℝ => (x,t)) := continuous_const.prodMk continuous_id
  apply product_from_slices γ γ f (fun x => f (x,0)) (fun y => f (0,y))
    (fun z => ‖dx z‖^2) (fun z => ‖dy z‖^2)
    (mem_bounded _ hf.aestronglyMeasurable (fun z => (hb z).1))
    (mem_bounded _ (hf.comp (cx 0)).aestronglyMeasurable (fun x => (hb (x,0)).1))
    (mem_bounded _ (hf.comp (cy 0)).aestronglyMeasurable (fun y => (hb (0,y)).1))
    (square_mem _ (mem_bounded _ hdx.aestronglyMeasurable (fun z => (hb z).2.1)))
    (square_mem _ (mem_bounded _ hdy.aestronglyMeasurable (fun z => (hb z).2.2)))
  · intro y
    exact line _ _ (fun t => hx t y) (hdx.comp (cx y)) (fun t => (hb (t,y)).1) (fun t => (hb (t,y)).2.1)
  · intro x
    exact line _ _ (fun t => hy x t) (hdy.comp (cy x)) (fun t => (hb (x,t)).1) (fun t => (hb (x,t)).2.2)

abbrev Cube := (ℝ × ℝ) × ℝ
abbrev gaussianCube : Measure Cube := (γ.prod γ).prod γ

/-- The full three-dimensional oscillator gap on complex test functions and
    their three actual partial derivatives. Conditional means appear only on
    the two-dimensional slices. -/
theorem cube (f dx dy dz : Cube → ℂ) (hf : Continuous f)
    (hdx : Continuous dx) (hdy : Continuous dy) (hdz : Continuous dz) {C : ℝ}
    (hb : ∀ z, ‖f z‖≤C ∧ ‖dx z‖≤C ∧ ‖dy z‖≤C ∧ ‖dz z‖≤C)
    (hx : ∀ x y z, HasDerivAt (fun t => f ((t,y),z)) (dx ((x,y),z)) x)
    (hy : ∀ x y z, HasDerivAt (fun t => f ((x,t),z)) (dy ((x,y),z)) y)
    (hz : ∀ x y z, HasDerivAt (fun t => f ((x,y),t)) (dz ((x,y),z)) z) :
    (∫ z, ‖f z-(∫ t, f t ∂gaussianCube)‖^2 ∂gaussianCube) ≤
      (∫ z, ‖dx z‖^2+‖dy z‖^2+‖dz z‖^2 ∂gaussianCube)/2 := by
  have cp (z : ℝ) : Continuous (fun p : ℝ × ℝ => (p,z)) := continuous_id.prodMk continuous_const
  have ct (p : ℝ × ℝ) : Continuous (fun z : ℝ => (p,z)) := continuous_const.prodMk continuous_id
  let u := fun p : ℝ × ℝ => f (p,0)
  let v := fun t : ℝ => ∫ p, f (p,t) ∂(γ.prod γ)
  have hF (z : ℝ) : MemLp (fun p => f (p,z)) 2 (γ.prod γ) :=
    mem_bounded _ (hf.comp (cp z)).aestronglyMeasurable (fun p => (hb (p,z)).1)
  have hdxF (z : ℝ) : Integrable (fun p => ‖dx (p,z)‖^2) (γ.prod γ) :=
    square_mem _ (mem_bounded _ (hdx.comp (cp z)).aestronglyMeasurable (fun p => (hb (p,z)).2.1))
  have hdyF (z : ℝ) : Integrable (fun p => ‖dy (p,z)‖^2) (γ.prod γ) :=
    square_mem _ (mem_bounded _ (hdy.comp (cp z)).aestronglyMeasurable (fun p => (hb (p,z)).2.2.1))
  have hv : MemLp v 2 γ := by
    have hm : AEStronglyMeasurable (fun z : ℝ × (ℝ × ℝ) => f (z.2,z.1)) (γ.prod (γ.prod γ)) :=
      (hf.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
    apply mem_bounded γ hm.integral_prod_right'
    intro z
    calc
      ‖v z‖ ≤ ∫ p, ‖f (p,z)‖ ∂(γ.prod γ) := norm_integral_le_integral_norm _
      _ ≤ ∫ _p : ℝ × ℝ, C ∂(γ.prod γ) :=
        integral_mono ((hF z).integrable (by norm_num)).norm (integrable_const _) (fun p => (hb (p,z)).1)
      _ = C := by simp
  have hX := square_mem gaussianCube (mem_bounded _ hdx.aestronglyMeasurable (fun z => (hb z).2.1))
  have hY := square_mem gaussianCube (mem_bounded _ hdy.aestronglyMeasurable (fun z => (hb z).2.2.1))
  have hZ := square_mem gaussianCube (mem_bounded _ hdz.aestronglyMeasurable (fun z => (hb z).2.2.2))
  rw [integral_add (hX.add hY) hZ]
  apply product_from_slices (γ.prod γ) γ f u v
    (fun z => ‖dx z‖^2+‖dy z‖^2) (fun z => ‖dz z‖^2)
    (mem_bounded _ hf.aestronglyMeasurable (fun z => (hb z).1)) (hF 0) hv (hX.add hY) hZ
  · intro z
    rw [integral_add (hdxF z) (hdyF z)]
    exact plane (fun p => f (p,z)) (fun p => dx (p,z)) (fun p => dy (p,z))
      (hf.comp (cp z)) (hdx.comp (cp z)) (hdy.comp (cp z))
      (fun p => ⟨(hb (p,z)).1,(hb (p,z)).2.1,(hb (p,z)).2.2.1⟩)
      (fun x y => hx x y z) (fun x y => hy x y z)
  · rintro ⟨x,y⟩
    exact line _ _ (fun z => hz x y z) (hdz.comp (ct (x,y)))
      (fun z => (hb ((x,y),z)).1) (fun z => (hb ((x,y),z)).2.2.2)


end OscillatorGaussian
