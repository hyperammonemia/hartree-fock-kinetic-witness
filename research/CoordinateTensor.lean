import CoordinateSlater

open MeasureTheory
open scoped TensorProduct ComplexConjugate

namespace CoordinateTensor

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]

private theorem product_mem (f g : Lp ℂ 2 μ) :
    MemLp (fun z : X × X => f z.1*g z.2) 2 (μ.prod μ) := by
  have mf := (Lp.memLp f).aestronglyMeasurable
  have mg := (Lp.memLp g).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm (mf.comp_fst.mul mg.comp_snd)).mpr ?_
  have hf := (memLp_two_iff_integrable_sq_norm mf).mp (Lp.memLp f)
  have hg := (memLp_two_iff_integrable_sq_norm mg).mp (Lp.memLp g)
  change Integrable (fun z : X × X => ‖f z.1*g z.2‖^2) (μ.prod μ)
  simpa only [norm_mul,mul_pow] using hf.mul_prod hg

noncomputable def pure (f g : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod μ) :=
  (product_mem μ f g).toLp _

theorem pure_rep (f g : Lp ℂ 2 μ) :
    (pure μ f g : X × X → ℂ) =ᵐ[μ.prod μ] (fun z => f z.1*g z.2) :=
  (product_mem μ f g).coeFn_toLp

omit [SFinite μ] in
private theorem at_fst {f g : X → ℂ} (h : f =ᵐ[μ] g) :
    (fun z : X × X => f z.1) =ᵐ[μ.prod μ] (fun z => g z.1) :=
  h.comp_tendsto (Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=μ)).tendsto_ae

omit [SFinite μ] in
private theorem at_snd {f g : X → ℂ} (h : f =ᵐ[μ] g) :
    (fun z : X × X => f z.2) =ᵐ[μ.prod μ] (fun z => g z.2) :=
  h.comp_tendsto (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=μ)).tendsto_ae

noncomputable def productBilinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 (μ.prod μ) :=
  LinearMap.mk₂ ℂ (pure μ)
    (fun f f' g => by
      apply Lp.ext
      filter_upwards [pure_rep μ (f+f') g, at_fst μ (Lp.coeFn_add f f'),
        Lp.coeFn_add (pure μ f g) (pure μ f' g), pure_rep μ f g, pure_rep μ f' g]
        with z h0 h1 h2 h3 h4
      simp only [Pi.add_apply,h0,h1,h2,h3,h4,add_mul])
    (fun c f g => by
      apply Lp.ext
      filter_upwards [pure_rep μ (c • f) g, at_fst μ (Lp.coeFn_smul c f),
        Lp.coeFn_smul c (pure μ f g),pure_rep μ f g] with z h0 h1 h2 h3
      simp only [Pi.smul_apply,smul_eq_mul,h0,h1,h2,h3,mul_assoc])
    (fun f g g' => by
      apply Lp.ext
      filter_upwards [pure_rep μ f (g+g'), at_snd μ (Lp.coeFn_add g g'),
        Lp.coeFn_add (pure μ f g) (pure μ f g'), pure_rep μ f g, pure_rep μ f g']
        with z h0 h1 h2 h3 h4
      simp only [Pi.add_apply,h0,h1,h2,h3,h4,mul_add])
    (fun c f g => by
      apply Lp.ext
      filter_upwards [pure_rep μ f (c • g), at_snd μ (Lp.coeFn_smul c g),
        Lp.coeFn_smul c (pure μ f g),pure_rep μ f g] with z h0 h1 h2 h3
      simp only [Pi.smul_apply,smul_eq_mul,h0,h1,h2,h3]
      ring)

noncomputable def productLinear : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 μ) →ₗ[ℂ] Lp ℂ 2 (μ.prod μ) :=
  TensorProduct.lift (productBilinear μ)

theorem productLinear_pure (f g : Lp ℂ 2 μ) :
    productLinear μ (f ⊗ₜ[ℂ] g) = pure μ f g := rfl

private theorem inner_pure (a b x y : Lp ℂ 2 μ) :
    inner ℂ (pure μ a b) (pure μ x y) = inner ℂ a x * inner ℂ b y := by
  simp only [L2.inner_def,RCLike.inner_apply']
  calc
    _ = ∫ z : X × X, (conj (a z.1)*x z.1)*(conj (b z.2)*y z.2) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [pure_rep μ a b,pure_rep μ x y] with z h1 h2
      simp only [h1,h2,map_mul]
      ring
    _ = _ := integral_prod_mul (fun t => conj (a t)*x t) (fun t => conj (b t)*y t)

theorem product_inner (s t : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 μ) :
    inner ℂ (productLinear μ s) (productLinear μ t) = inner ℂ s t := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | tmul x y => rw [productLinear_pure,productLinear_pure,TensorProduct.inner_tmul,inner_pure]
    | add u v hu hv =>
      rw [map_add,inner_add_right,hu,hv]
      exact (inner_add_right (𝕜:=ℂ) (a ⊗ₜ b) u v).symm
  | add u v hu hv =>
    rw [map_add,inner_add_left,hu,hv]
    exact (inner_add_left (𝕜:=ℂ) u v t).symm

/-- Canonical isometry from algebraic Hilbert tensors into the full physical
    product L2 space. Its range need not contain the interacting residual. -/
noncomputable def embedding : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 μ) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod μ) :=
  (productLinear μ).isometryOfInner (product_inner μ)

/-- Taking the inherited L2 norm on a one-body energy domain permits Coulomb
    multiplication to remain an unbounded map on its algebraic tensor domain. -/
noncomputable def formEmbedding {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (J : F →ₗᵢ[ℂ] Lp ℂ 2 μ) :
    (F ⊗[ℂ] F) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod μ) :=
  (embedding μ).comp (TensorProduct.mapIsometry J J)

theorem slater_rep (f g : Lp ℂ 2 μ) :
    (embedding μ (SlaterGeometry.slater f g) : X × X → ℂ) =ᵐ[μ.prod μ]
      CoordinateSlater.wave (SlaterGeometry.normalizer : ℂ) f g := by
  change (productLinear μ _ : X × X → ℂ) =ᵐ[μ.prod μ] _
  rw [SlaterGeometry.slater,map_smul,map_sub,productLinear_pure,productLinear_pure]
  filter_upwards [Lp.coeFn_smul (SlaterGeometry.normalizer : ℂ) (pure μ f g - pure μ g f),
    Lp.coeFn_sub (pure μ f g) (pure μ g f),pure_rep μ f g,pure_rep μ g f] with z h1 h2 h3 h4
  simp only [h1,Pi.smul_apply,h2,Pi.sub_apply,h3,h4,smul_eq_mul,CoordinateSlater.wave]

private theorem pure_norm_bound (w f : Lp ℂ 2 μ) :
    ‖(productBilinear μ).flip w f‖ ≤ ‖w‖*‖f‖ := by
  change ‖embedding μ (f ⊗ₜ[ℂ] w)‖ ≤ _
  rw [(embedding μ).norm_map,TensorProduct.norm_tmul,mul_comm]

noncomputable def insertRight (w : Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod μ) :=
  ((productBilinear μ).flip w).mkContinuous ‖w‖ (pure_norm_bound μ w)

/-- Partial contraction on the whole two-particle coordinate Hilbert space,
    including the weak derivative of a finite-energy determinant. -/
noncomputable def contractRight (w : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod μ) →L[ℂ] Lp ℂ 2 μ :=
  (insertRight μ w).adjoint

theorem contract_pairing (w φ : Lp ℂ 2 μ) (s : Lp ℂ 2 (μ.prod μ)) :
    inner ℂ φ (contractRight μ w s)=inner ℂ (pure μ φ w) s :=
  (insertRight μ w).adjoint_inner_right φ s

theorem contract_bound (w : Lp ℂ 2 μ) (s : Lp ℂ 2 (μ.prod μ)) :
    ‖contractRight μ w s‖ ≤ ‖w‖*‖s‖ := by
  refine ((contractRight μ w).le_opNorm s).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg s))
  change ‖(insertRight μ w).adjoint‖ ≤ ‖w‖
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (pure_norm_bound μ w)

theorem contract_pure (w f g : Lp ℂ 2 μ) :
    contractRight μ w (pure μ f g) = inner ℂ w g • f := by
  apply ext_inner_left ℂ
  intro test
  rw [contract_pairing,inner_pure,inner_smul_right,mul_comm]

theorem contract_slater (w f g : Lp ℂ 2 μ) :
    contractRight μ w (embedding μ (SlaterGeometry.slater f g)) =
      (SlaterGeometry.normalizer:ℂ) • (inner ℂ w g • f - inner ℂ w f • g) := by
  change contractRight μ w (productLinear μ _) = _
  rw [SlaterGeometry.slater,map_smul,map_sub,productLinear_pure,productLinear_pure,
    map_smul,map_sub,contract_pure,contract_pure]

/-- A six-dimensional weak-derivative identity on a product test descends
    to the one-dimensional orbital-testing identity after contraction. -/
theorem contract_weak_test (w φ dφ : Lp ℂ 2 μ) (s ds : Lp ℂ 2 (μ.prod μ))
    (h : inner ℂ (pure μ dφ w) s = -inner ℂ (pure μ φ w) ds) :
    inner ℂ dφ (contractRight μ w s) = -inner ℂ φ (contractRight μ w ds) := by
  rwa [contract_pairing,contract_pairing]

end CoordinateTensor
