import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A rank-one comparison for a negative weak eigenspace on a complex form
domain. Rotation and exchange that fix the reference mode act trivially. -/
noncomputable section
namespace GroundSymmetry
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

def weakEigenspace (q : D → (D →ₗ[ℂ] ℂ)) (E : ℝ) : Submodule ℂ D where
  carrier := {u | ∀ z, q z u = (E:ℂ) * inner ℂ z u}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv z
    rw [map_add, inner_add_right, hu z, hv z, mul_add]
  smul_mem' := by
    intro c u hu z
    rw [map_smul, inner_smul_right, hu z]
    simp only [smul_eq_mul]; ring

/-- If the form is nonnegative on the reference orthogonal complement, a
negative-energy eigenvector in that complement is zero. -/
theorem overlap_injective (q : D → (D →ₗ[ℂ] ℂ)) (g : D) (E : ℝ) (hE : E < 0)
    (nonneg : ∀ w, inner ℂ g w = 0 → 0 ≤ (q w w).re) {u v : D}
    (hu : u ∈ weakEigenspace q E) (hv : v ∈ weakEigenspace q E)
    (huv : inner ℂ g u = inner ℂ g v) : u = v := by
  have h := (weakEigenspace q E).sub_mem hu hv
  change ∀ z, q z (u-v) = (E:ℂ) * inner ℂ z (u-v) at h
  have hz := nonneg (u-v) (by rw [inner_sub_right, huv, sub_self])
  rw [h] at hz
  have hreal : (inner ℂ (u-v) (u-v)).re = ‖u-v‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜 := ℂ) (u-v)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hreal] at hz
  by_contra hn
  have normpos := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  exact (not_lt_of_ge hz) (mul_neg_of_neg_of_pos hE (sq_pos_of_pos normpos))

theorem negative_mode_unique (q : D → (D →ₗ[ℂ] ℂ)) (g : D) (E : ℝ) (hE : E < 0)
    (nonneg : ∀ w, inner ℂ g w = 0 → 0 ≤ (q w w).re) {u v : D}
    (hu : u ∈ weakEigenspace q E) (hv : v ∈ weakEigenspace q E) (huz : u ≠ 0) :
    ∃ c : ℂ, v = c • u := by
  have hg : inner ℂ g u ≠ 0 := fun hz => huz (overlap_injective q g E hE nonneg hu
    (weakEigenspace q E).zero_mem (by simpa using hz))
  let c := inner ℂ g v / inner ℂ g u
  refine ⟨c, overlap_injective q g E hE nonneg hv ((weakEigenspace q E).smul_mem c hu) ?_⟩
  rw [inner_smul_right]
  exact (div_mul_cancel₀ _ hg).symm

/-- Every symmetry that preserves the eigenspace and preserves the reference
coefficient fixes the eigenvector, including its phase. -/
theorem invariant_mode (q : D → (D →ₗ[ℂ] ℂ)) (g : D) (E : ℝ) (hE : E < 0)
    (nonneg : ∀ w, inner ℂ g w = 0 → 0 ≤ (q w w).re) (U : D → D)
    (maps : ∀ u ∈ weakEigenspace q E, U u ∈ weakEigenspace q E)
    (reference : ∀ u, inner ℂ g (U u) = inner ℂ g u)
    {u : D} (hu : u ∈ weakEigenspace q E) : U u = u :=
  overlap_injective q g E hE nonneg (maps u hu) hu (reference u)

#print axioms negative_mode_unique
#print axioms invariant_mode
end GroundSymmetry
