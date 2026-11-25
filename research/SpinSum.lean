import CoordinateTensor

open MeasureTheory
open scoped ComplexConjugate TensorProduct

namespace SpinSum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

noncomputable def component (c : ℂ) (a b : Fin 2 → Lp ℂ 2 μ) (s t : Fin 2) :
    Lp ℂ 2 (μ.prod μ) :=
  c • (CoordinateTensor.pure μ (a s) (b t) - CoordinateTensor.pure μ (b s) (a t))

noncomputable def coordinate (c : ℂ) (a b : Fin 2 → Lp ℂ 2 μ) (s t : Fin 2) (z : X × X) : ℂ :=
  c*((a s) z.1*(b t) z.2-(b s) z.1*(a t) z.2)

private theorem component_rep (c : ℂ) (a b : Fin 2 → Lp ℂ 2 μ) (s t : Fin 2) :
    (component μ c a b s t : X × X → ℂ) =ᵐ[μ.prod μ] coordinate μ c a b s t := by
  unfold component coordinate
  filter_upwards [Lp.coeFn_smul c (CoordinateTensor.pure μ (a s) (b t)-CoordinateTensor.pure μ (b s) (a t)),
    Lp.coeFn_sub (CoordinateTensor.pure μ (a s) (b t)) (CoordinateTensor.pure μ (b s) (a t)),
    CoordinateTensor.pure_rep μ (a s) (b t),CoordinateTensor.pure_rep μ (b s) (a t)] with z h1 h2 h3 h4
  simp only [h1,Pi.smul_apply,h2,Pi.sub_apply,h3,h4,smul_eq_mul]

private theorem expand_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (c : ℂ) (a b x y : V) : inner ℂ (c • (a-b)) (c • (x-y)) =
      conj c*c*(inner ℂ a x-inner ℂ a y-inner ℂ b x+inner ℂ b y) := by
  simp only [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]
  ring

variable [SFinite μ]

private theorem pairing (u v p q : Lp ℂ 2 μ) :
    inner ℂ (CoordinateTensor.pure μ u v) (CoordinateTensor.pure μ p q) =
      inner ℂ u p * inner ℂ v q := by
  change inner ℂ (CoordinateTensor.embedding μ (u ⊗ₜ[ℂ] v))
    (CoordinateTensor.embedding μ (p ⊗ₜ[ℂ] q)) = _
  rw [(CoordinateTensor.embedding μ).inner_map_map,TensorProduct.inner_tmul]

private theorem block_inner (c : ℂ) (u v p q : Fin 2 → Lp ℂ 2 μ) (s t : Fin 2) :
    inner ℂ (component μ c u v s t) (component μ c p q s t) =
      (conj c*c)*(inner ℂ (u s) (p s)*inner ℂ (v t) (q t) -
        inner ℂ (u s) (q s)*inner ℂ (v t) (p t) - inner ℂ (v s) (p s)*inner ℂ (u t) (q t) +
        inner ℂ (v s) (q s)*inner ℂ (u t) (p t)) := by
  rw [component,component,expand_inner]
  simp only [pairing]

omit [SFinite μ] in
private theorem coordinate_pair (c : ℂ) (u v p q : Fin 2 → Lp ℂ 2 μ) (s t : Fin 2) :
    (∫ z, conj (coordinate μ c u v s t z)*coordinate μ c p q s t z ∂(μ.prod μ)) =
      inner ℂ (component μ c u v s t) (component μ c p q s t) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [component_rep μ c u v s t,component_rep μ c p q s t] with z h1 h2
  rw [RCLike.inner_apply',h1,h2]

/-- The explicit sum over the two binary spin labels uses exactly the common
    physical convention for the six-dimensional coordinate integral. -/
theorem two_spin_gram (c : ℂ) (hc : conj c*c=1/2) (u v p q : Fin 2 → Lp ℂ 2 μ) :
    (∑ s : Fin 2, ∑ t : Fin 2, ∫ z, conj (coordinate μ c u v s t z)*
        coordinate μ c p q s t z ∂(μ.prod μ)) =
      (∑ s : Fin 2, inner ℂ (u s) (p s))*(∑ t : Fin 2, inner ℂ (v t) (q t)) -
      (∑ s : Fin 2, inner ℂ (u s) (q s))*(∑ t : Fin 2, inner ℂ (v t) (p t)) := by
  simp only [Fin.sum_univ_two,coordinate_pair,block_inner,hc]
  ring

end SpinSum
