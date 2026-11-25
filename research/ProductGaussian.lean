import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ComplexConjugate

namespace ProductGaussian

private theorem pyth {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (J : H →ₗᵢ[ℂ] V) (s : V) (t : H) :
    ‖s-J t‖^2=‖s-J (J.toContinuousLinearMap.adjoint s)‖^2+‖J.toContinuousLinearMap.adjoint s-t‖^2 := by
  let a := J.toContinuousLinearMap.adjoint s
  have horth : inner ℂ (s-J a) (J (a-t))=0 := by
    rw [inner_sub_left,J.inner_map_map]
    exact sub_eq_zero.mpr (J.toContinuousLinearMap.adjoint_inner_left (a-t) s).symm
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have decomp : s-J a+J (a-t)=s-J t := by rw [map_sub]; abel
  rw [decomp,J.norm_map] at hs
  simpa only [sq] using hs

private theorem adj_contract {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (J : H →ₗᵢ[ℂ] V) (s : V) :
    ‖J.toContinuousLinearMap.adjoint s‖ ≤ ‖s‖ := by
  calc
    _ ≤ ‖J.toContinuousLinearMap.adjoint‖*‖s‖ := J.toContinuousLinearMap.adjoint.le_opNorm s
    _ ≤ 1*‖s‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; exact mul_le_mul_of_nonneg_right J.norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = _ := one_mul _

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

noncomputable def fstIso : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

noncomputable def sndIso : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.snd measurePreserving_snd

private theorem first_rep (f : Lp ℂ 2 μ) :
    (fstIso μ ν f : X × Y → ℂ) =ᵐ[μ.prod ν] (fun p => f p.1) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_fst

private theorem second_rep (g : Lp ℂ 2 ν) :
    (sndIso μ ν g : X × Y → ℂ) =ᵐ[μ.prod ν] (fun p => g p.2) :=
  Lp.coeFn_compMeasurePreserving g measurePreserving_snd

noncomputable def one (μ : Measure X) [IsProbabilityMeasure μ] : Lp ℂ 2 μ := Lp.const 2 μ 1

private theorem one_rep (μ : Measure X) [IsProbabilityMeasure μ] :
    (one μ : X → ℂ) =ᵐ[μ] (fun _ => (1:ℂ)) := Lp.coeFn_const 2 μ (1:ℂ)

private theorem first_one : fstIso μ ν (one μ)=one (μ.prod ν) := by
  apply Lp.ext
  filter_upwards [first_rep μ ν (one μ), (one_rep μ).comp_tendsto
    (Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=ν)).tendsto_ae,one_rep (μ.prod ν)] with p h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

private theorem second_one : sndIso μ ν (one ν)=one (μ.prod ν) := by
  apply Lp.ext
  filter_upwards [second_rep μ ν (one ν), (one_rep ν).comp_tendsto
    (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=ν)).tendsto_ae,one_rep (μ.prod ν)] with p h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

private theorem mean_pair (μ : Measure X) [IsProbabilityMeasure μ] (s : Lp ℂ 2 μ) :
    inner ℂ (one μ) s=∫ z, s z ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [one_rep μ] with x hx
  simp only [RCLike.inner_apply',hx,map_one,one_mul]

private theorem pair_mean (μ : Measure X) [IsProbabilityMeasure μ] (s : Lp ℂ 2 μ) :
    inner ℂ s (one μ)=∫ z, conj (s z) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [one_rep μ] with x hx
  simp only [RCLike.inner_apply',hx,mul_one]

private theorem cross_inner (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    inner ℂ (fstIso μ ν f) (sndIso μ ν g) =
      (∫ x, conj (f x) ∂μ)*(∫ y, g y ∂ν) := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : X × Y, conj (f z.1)*g z.2 ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards [first_rep μ ν f,second_rep μ ν g] with z h1 h2
      rw [RCLike.inner_apply',h1,h2]
    _ = _ := integral_prod_mul (fun x => conj (f x)) g

private theorem cross_projection (g : Lp ℂ 2 ν) :
    (fstIso μ ν).toContinuousLinearMap.adjoint (sndIso μ ν g)=(∫ y, g y ∂ν) • one μ := by
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right,inner_smul_right,pair_mean]
  exact (cross_inner μ ν f g).trans (mul_comm _ _)

/-- Efron--Stein's two-coordinate bound in the actual L2 of a product
    probability measure. Each one-coordinate approximant can be chosen
    independently, including the explicit anchors in the Gaussian trace bound. -/
theorem product_variance (s : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖s-(∫ z, s z ∂(μ.prod ν)) • one (μ.prod ν)‖^2 ≤
      ‖s-fstIso μ ν u‖^2 + ‖s-sndIso μ ν v‖^2 := by
  let J := fstIso μ ν; let K := sndIso μ ν
  let JA := J.toContinuousLinearMap.adjoint; let KA := K.toContinuousLinearMap.adjoint
  have hm : (∫ y, (KA s) y ∂ν) = ∫ z, s z ∂(μ.prod ν) := by
    rw [← mean_pair ν,← mean_pair (μ.prod ν)]
    change inner ℂ _ (K.toContinuousLinearMap.adjoint s)=_
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (sndIso μ ν (one ν)) s=_
    rw [second_one]
  have hp : J (JA (K (KA s))) = (∫ z, s z ∂(μ.prod ν)) • one (μ.prod ν) := by
    change fstIso μ ν ((fstIso μ ν).toContinuousLinearMap.adjoint (sndIso μ ν (KA s)))=_
    rw [cross_projection,map_smul,hm,first_one]
  have h1 := pyth J s u
  have h2 := pyth K s v
  have h3 := pyth J s (JA (K (KA s)))
  change ‖s-J (JA (K (KA s)))‖^2 = ‖s-J (JA s)‖^2+‖JA s-JA (K (KA s))‖^2 at h3
  rw [hp] at h3
  have hd : ‖JA s-JA (K (KA s))‖ ≤ ‖s-K (KA s)‖ := by
    rw [←map_sub]
    exact adj_contract J _
  have hds := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hd
  change ‖s-J u‖^2 = ‖s-J (JA s)‖^2 + ‖JA s-u‖^2 at h1
  change ‖s-K v‖^2 = ‖s-K (KA s)‖^2 + ‖KA s-v‖^2 at h2
  change _ ≤ ‖s-J u‖^2+‖s-K v‖^2
  linarith [sq_nonneg ‖JA s-u‖,sq_nonneg ‖KA s-v‖]

private theorem norm_sq_integral (τ : Measure X) (f : Lp ℂ 2 τ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂τ := by
  calc
    _ = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner f
    _ = ∫ x, RCLike.re (inner ℂ (f x) (f x)) ∂τ := by
      rw [L2.inner_def,integral_re (L2.integrable_inner (𝕜:=ℂ) f f)]
    _ = _ := by simp only [inner_self_eq_norm_sq]

private theorem norm_sub_rep (τ : Measure X) (F G : Lp ℂ 2 τ) (f g : X → ℂ)
    (hf : (F : X → ℂ) =ᵐ[τ] f) (hg : (G : X → ℂ) =ᵐ[τ] g) :
    ‖F-G‖^2 = ∫ x, ‖f x-g x‖^2 ∂τ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub F G,hf,hg] with t h1 h2 h3
  simp only [h1,Pi.sub_apply,h2,h3]

/-- Direct scalar-coordinate statement for subsequent Fubini iteration. -/
theorem product_variance_integral (f : X × Y → ℂ) (u : X → ℂ) (v : Y → ℂ)
    (hf : MemLp f 2 (μ.prod ν)) (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    (∫ z, ‖f z-(∫ t, f t ∂(μ.prod ν))‖^2 ∂(μ.prod ν)) ≤
      (∫ z, ‖f z-u z.1‖^2 ∂(μ.prod ν))+(∫ z, ‖f z-v z.2‖^2 ∂(μ.prod ν)) := by
  let F := hf.toLp f; let U := hu.toLp u; let V := hv.toLp v
  let c := ∫ z, f z ∂(μ.prod ν)
  have hF : (F : X × Y → ℂ) =ᵐ[μ.prod ν] f := hf.coeFn_toLp
  have hmean : (∫ z, F z ∂(μ.prod ν))=c := integral_congr_ae hF
  have hconst : (c • one (μ.prod ν) : Lp ℂ 2 (μ.prod ν)) =ᵐ[μ.prod ν] fun _ => c := by
    filter_upwards [Lp.coeFn_smul c (one (μ.prod ν)),one_rep (μ.prod ν)] with p h1 h2
    simp only [h1,Pi.smul_apply,h2,smul_eq_mul,mul_one]
  have hU : (fstIso μ ν U : X × Y → ℂ) =ᵐ[μ.prod ν] fun p => u p.1 :=
    (first_rep μ ν U).trans (hu.coeFn_toLp.comp_tendsto
      (Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=ν)).tendsto_ae)
  have hV : (sndIso μ ν V : X × Y → ℂ) =ᵐ[μ.prod ν] fun p => v p.2 :=
    (second_rep μ ν V).trans (hv.coeFn_toLp.comp_tendsto
      (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=ν)).tendsto_ae)
  have h := product_variance μ ν F U V
  rw [hmean,norm_sub_rep _ _ _ _ _ hF hconst,norm_sub_rep _ _ _ _ _ hF hU,
    norm_sub_rep _ _ _ _ _ hF hV] at h
  exact h

end ProductGaussian
