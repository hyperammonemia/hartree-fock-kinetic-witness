import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped TensorProduct ComplexConjugate

namespace SlaterGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def normalizer : ℝ := 1 / Real.sqrt 2

private theorem normalizer_squared : (normalizer : ℂ)^2 = (1/2 : ℂ) := by
  have h : normalizer^2 = (1/2 : ℝ) := by
    rw [normalizer, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  calc
    _ = ((normalizer^2 : ℝ) : ℂ) := by push_cast; rfl
    _ = (1/2 : ℝ) := congrArg ((↑) : ℝ → ℂ) h
    _ = _ := by norm_num

/-- Normalized antisymmetrized product of two orthonormal complex spin orbitals. -/
noncomputable def slater (x y : H) : H ⊗[ℂ] H :=
  (normalizer : ℂ) • (x ⊗ₜ[ℂ] y - y ⊗ₜ[ℂ] x)

private theorem expand_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a b c d : V) :
    inner ℂ ((normalizer:ℂ) • (a-b)) ((normalizer:ℂ) • (c-d)) =
      (normalizer:ℂ)^2 * (inner ℂ a c - inner ℂ a d - inner ℂ b c + inner ℂ b d) := by
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, Complex.conj_ofReal]
  ring

theorem inner_slater (a b x y : H) :
    inner ℂ (slater a b) (slater x y) =
      inner ℂ a x * inner ℂ b y - inner ℂ a y * inner ℂ b x := by
  calc
    _ = (normalizer:ℂ)^2 * (2 * (inner ℂ a x * inner ℂ b y - inner ℂ a y * inner ℂ b x)) := by
      rw [slater, slater, expand_inner]
      simp only [TensorProduct.inner_tmul]
      ring
    _ = _ := by rw [normalizer_squared]; ring

theorem slater_norm_sq (x y : H) :
    ‖slater x y‖^2 = ‖x‖^2 * ‖y‖^2 - ‖inner ℂ x y‖^2 := by
  have h := inner_slater x y x y
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (slater x y),
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) x, inner_self_eq_norm_sq_to_K (𝕜:=ℂ) y,
    ← inner_conj_symm y x, Complex.mul_conj'] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h

theorem slater_norm_le (x y : H) : ‖slater x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [slater_norm_sq, mul_pow]
  linarith [sq_nonneg ‖inner ℂ x y‖]

theorem slater_unit (x y : H) (hx : ‖x‖=1) (hy : ‖y‖=1) (hxy : inner ℂ x y=0) :
    ‖slater x y‖=1 := by
  have h := slater_norm_sq x y
  rw [hx,hy,hxy,norm_zero] at h
  nlinarith [norm_nonneg (slater x y)]

theorem slater_add_left (x y z : H) : slater (x+y) z = slater x z + slater y z := by
  simp only [slater, TensorProduct.add_tmul, TensorProduct.tmul_add, smul_sub, smul_add]
  abel

theorem slater_add_right (x y z : H) : slater x (y+z) = slater x y + slater x z := by
  simp only [slater, TensorProduct.add_tmul, TensorProduct.tmul_add, smul_sub, smul_add]
  abel

theorem slater_flip (x y : H) : slater y x = -slater x y := by
  simp only [slater, smul_sub]; abel

theorem inner_projected (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (a b x y : H) (ha : a∈P) (hb : b∈P) :
    inner ℂ (slater a b) (slater x y) =
      inner ℂ (slater a b) (slater (P.starProjection x) (P.starProjection y)) := by
  simp only [inner_slater, ← P.inner_starProjection_left_eq_right,
    P.starProjection_eq_self_iff.mpr ha, P.starProjection_eq_self_iff.mpr hb]

/-- The complement may be infinite-dimensional. The reference plane is allowed
    to be any closed subspace containing the two reference orbitals. -/
theorem double_excitation_bound (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (a b x y : H) (ha : a∈P) (hb : b∈P) (hd : ‖slater a b‖=1)
    (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖slater (Pᗮ.starProjection x) (Pᗮ.starProjection y)‖ ≤
      1 - ‖inner ℂ (slater a b) (slater x y)‖^2 := by
  let o := ‖inner ℂ (slater a b) (slater x y)‖
  have ho0 : 0 ≤ o := norm_nonneg _
  have ho : o ≤ ‖P.starProjection x‖*‖P.starProjection y‖ := by
    dsimp [o]
    rw [inner_projected P a b x y ha hb]
    exact (norm_inner_le_norm (𝕜:=ℂ) (slater a b) (slater (P.starProjection x) (P.starProjection y))).trans
      (by rw [hd,one_mul]; exact slater_norm_le _ _)
  have hpx := P.norm_sq_eq_add_norm_sq_starProjection x
  have hpy := P.norm_sq_eq_add_norm_sq_starProjection y
  rw [hx] at hpx
  rw [hy] at hpy
  have px : ‖P.starProjection x‖ ≤ 1 := by nlinarith [sq_nonneg ‖Pᗮ.starProjection x‖]
  have py : ‖P.starProjection y‖ ≤ 1 := by nlinarith [sq_nonneg ‖Pᗮ.starProjection y‖]
  have ox : o ≤ ‖P.starProjection x‖ := ho.trans <| by simpa using mul_le_mul_of_nonneg_left py (norm_nonneg (P.starProjection x))
  have oy : o ≤ ‖P.starProjection y‖ := ho.trans <| by simpa using mul_le_mul_of_nonneg_right px (norm_nonneg (P.starProjection y))
  have ox2 := (sq_le_sq₀ ho0 (norm_nonneg _)).mpr ox
  have oy2 := (sq_le_sq₀ ho0 (norm_nonneg _)).mpr oy
  change _ ≤ 1 - o^2
  refine (slater_norm_le _ _).trans ?_
  nlinarith [sq_nonneg (‖Pᗮ.starProjection x‖ - ‖Pᗮ.starProjection y‖)]

end SlaterGeometry
