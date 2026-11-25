import SlaterGeometry

open scoped TensorProduct ComplexConjugate
open SlaterGeometry

namespace SlaterEnergy

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The residual lives in a full two-particle space, where it can have
    infinite Schmidt rank. The occupied determinants live in the Hilbertian
    algebraic tensor product and are embedded isometrically. -/
theorem overlap_is_double (I : (H ⊗[ℂ] H) →ₗᵢ[ℂ] G) (r : G)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (h : ∀ z ∈ P, ∀ w : H, inner ℂ r (I (slater z w)) = 0) (x y : H) :
    inner ℂ r (I (slater x y)) = inner ℂ r (I (slater (Pᗮ.starProjection x) (Pᗮ.starProjection y))) := by
  have hp (v : H) : P.starProjection v ∈ P := (P.orthogonalProjectionOnto v).property
  have hrow (z : H) (v : H) : inner ℂ r (I (slater z (P.starProjection v))) = 0 := by
    rw [slater_flip (P.starProjection v) z, map_neg, inner_neg_right, h _ (hp v) _, neg_zero]
  calc
    _ = inner ℂ r (I (slater (P.starProjection x + Pᗮ.starProjection x)
        (P.starProjection y + Pᗮ.starProjection y))) :=
      congrArg₂ (fun s t => inner ℂ r (I (slater s t)))
        (P.starProjection_add_starProjection_orthogonal x).symm
        (P.starProjection_add_starProjection_orthogonal y).symm
    _ = _ := by
      simp only [slater_add_left, slater_add_right, map_add, inner_add_right,
        h _ (hp x) _, hrow, zero_add]

theorem residual_overlap_bound (I : (H ⊗[ℂ] H) →ₗᵢ[ℂ] G) (r : G)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (h : ∀ z ∈ P, ∀ w : H, inner ℂ r (I (slater z w))=0)
    (a b x y : H) (ha : a∈P) (hb : b∈P) (hd : ‖slater a b‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖inner ℂ r (I (slater x y))‖ ≤ ‖r‖ * (1 - ‖inner ℂ (slater a b) (slater x y)‖^2) := by
  rw [overlap_is_double I r P h x y]
  exact (norm_inner_le_norm (𝕜:=ℂ) r (I (slater (Pᗮ.starProjection x) (Pᗮ.starProjection y)))).trans <| by
    rw [I.norm_map]
    exact mul_le_mul_of_nonneg_left (double_excitation_bound P a b x y ha hb hd hx hy) (norm_nonneg r)

private theorem residual_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (d s : V) (hd : ‖d‖=1) (hs : ‖s‖=1) :
    ‖s - inner ℂ d s • d‖^2 = 1 - ‖inner ℂ d s‖^2 := by
  let c := inner ℂ d s
  have horth : inner ℂ d (s-c • d)=0 := by
    rw [inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K (𝕜:=ℂ) d,hd]
    simp [c]
  have orth : inner ℂ (c • d) (s - c • d)=0 := by
    rw [inner_smul_left,horth,mul_zero]
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • d) (s-c • d) orth
  have hadd : c • d+(s-c • d)=s := by abel
  rw [hadd, hs, norm_smul, hd, mul_one] at hsum
  dsimp [c] at hsum
  linarith

noncomputable def interaction {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (I : V →ₗᵢ[ℂ] G) (L : V →ₗ[ℂ] G) (z : V) : ℝ := (inner ℂ (I z) (L z)).re

/-- Decomposition of a symmetric form into reference, residual and orthogonal
    diagonal pieces. `L` can be unbounded in the Hilbert norm on the domain. -/
theorem form_expansion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (I : V →ₗᵢ[ℂ] G) (L : V →ₗ[ℂ] G)
    (symm : ∀ u v : V, inner ℂ (I u) (L v) = inner ℂ (L u) (I v))
    (d s : V) (c : ℂ) (hd : inner ℂ (L d) (I d) = 0) :
    interaction I L s = interaction I L (s-c • d) + 2*(conj c * inner ℂ (L d) (I s)).re := by
  let η := s-c • d
  have z : inner ℂ (L d) (I η) = inner ℂ (L d) (I s) := by
    simp [η, map_sub, map_smul, inner_sub_right,inner_smul_right,hd]
  have zz : inner ℂ (I η) (L d) = conj (inner ℂ (L d) (I s)) := by
    rw [← z]; exact (inner_conj_symm (I η) (L d)).symm
  have decomp : s = η + c • d := (sub_add_cancel s (c • d)).symm
  have hc : inner ℂ (I s) (L s) = inner ℂ (I η) (L η) +
      (conj c * inner ℂ (L d) (I s)) + conj (conj c * inner ℂ (L d) (I s)) := by
    conv_lhs => rw [decomp]
    simp only [map_add, map_smul, inner_add_left,inner_add_right,inner_smul_left,inner_smul_right]
    rw [symm d η,z,zz,symm d d,hd]
    simp
  have he := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.conj_re] at he
  unfold interaction
  change _ = (inner ℂ (I η) (L η)).re + _
  linarith

/-- A strict global energy margin over every normalized Slater determinant.
    The assumptions on the one-body gap, the multiplication form and its
    occupied residual are the continuum operator estimates. -/
theorem global_hf_margin (I : (H ⊗[ℂ] H) →ₗᵢ[ℂ] G) (L : (H ⊗[ℂ] H) →ₗ[ℂ] G)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection] (a b x y : H)
    (ha : a∈P) (hb : b∈P) (hd : ‖slater a b‖=1)
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hxy : inner ℂ x y=0)
    (symm : ∀ u v, inner ℂ (I u) (L v) = inner ℂ (L u) (I v))
    (hcenter : ∀ z ∈ P, ∀ w : H, inner ℂ (L (slater a b)) (I (slater z w))=0)
    (hn : ‖L (slater a b)‖ ≤ 8) (floor : ∀ z, -(4:ℝ)*‖z‖^2 ≤ interaction I L z)
    (oneBody : ℝ) (gap : (1-‖inner ℂ (slater a b) (slater x y)‖^2)/2 ≤ oneBody) :
    3/10*(1-‖inner ℂ (slater a b) (slater x y)‖^2) ≤
      oneBody + (1/100)*interaction I L (slater x y) := by
  let d := slater a b; let s := slater x y; let c := inner ℂ d s
  let loss := 1-‖c‖^2
  have hd' : ‖d‖=1 := hd
  have hs : ‖s‖=1 := slater_unit x y hx hy hxy
  have hc1 : ‖c‖≤1 := by simpa [c,hd',hs] using norm_inner_le_norm (𝕜:=ℂ) d s
  have hl : 0 ≤ loss := by dsimp [loss]; nlinarith [norm_nonneg c]
  have hmat : ‖inner ℂ (L d) (I s)‖ ≤ 8*loss :=
    (residual_overlap_bound I (L d) P hcenter a b x y ha hb hd hx hy).trans
      (mul_le_mul_of_nonneg_right hn hl)
  have hmod : ‖conj c * inner ℂ (L d) (I s)‖ ≤ 8*loss := by
    rw [norm_mul, RCLike.norm_conj]
    exact (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans (by simpa using hmat)
  have hre : -(8*loss) ≤ (conj c * inner ℂ (L d) (I s)).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (conj c * inner ℂ (L d) (I s)))).1
    linarith
  have hd0 : inner ℂ (L d) (I d)=0 := hcenter a ha b
  have form := form_expansion I L symm d s c hd0
  have hdiag := floor (s-c • d)
  rw [show ‖s-c • d‖^2=loss from residual_sq d s hd hs] at hdiag
  change 3/10*loss ≤ oneBody + (1/100)*interaction I L s
  change loss/2 ≤ oneBody at gap
  linarith

/-- A competing normalized state at or below the reference energy must be
    that reference up to a single unit-modulus complex phase. -/
theorem equality_is_phase {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (d s : V) (E : ℝ) (hd : ‖d‖=1) (hs : ‖s‖=1)
    (hmargin : 3/10*(1-‖inner ℂ d s‖^2) ≤ E) (hle : E ≤ 0) :
    ∃ c : ℂ, ‖c‖=1 ∧ s=c • d := by
  let c := inner ℂ d s
  have hr := residual_sq d s hd hs
  have h0 : ‖s-c • d‖=0 := by
    change ‖s-c • d‖^2=1-‖c‖^2 at hr
    change 3/10*(1-‖c‖^2) ≤ E at hmargin
    nlinarith [norm_nonneg (s-c • d)]
  have hc : ‖c‖=1 := by
    change ‖s-c • d‖^2=1-‖c‖^2 at hr
    rw [h0] at hr
    nlinarith [norm_nonneg c]
  exact ⟨c,hc,sub_eq_zero.mp (norm_eq_zero.mp h0)⟩

end SlaterEnergy
