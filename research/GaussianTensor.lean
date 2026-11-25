import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith

namespace GaussianTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Orthogonality gives an additive error bound under successive coordinate
    averages. A product of averages computes the product-space mean. -/
theorem average_step (P : Submodule ℂ H) [P.HasOrthogonalProjection] (x y : H) :
    ‖x-P.starProjection y‖^2 ≤ ‖x-P.starProjection x‖^2+‖x-y‖^2 := by
  have member : P.starProjection (x-y) ∈ P := (P.orthogonalProjectionOnto (x-y)).property
  have orth := P.starProjection_inner_eq_zero x (P.starProjection (x-y)) member
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orth
  have add : (x-P.starProjection x)+P.starProjection (x-y)=x-P.starProjection y := by
    rw [map_sub]
    abel
  rw [add] at hs
  have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (P.norm_starProjection_apply_le (x-y))
  nlinarith

theorem three_coordinate_variance (P Q R : Submodule ℂ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] [R.HasOrthogonalProjection] (x : H) :
    ‖x-P.starProjection (Q.starProjection (R.starProjection x))‖^2 ≤
      ‖x-P.starProjection x‖^2 + ‖x-Q.starProjection x‖^2 + ‖x-R.starProjection x‖^2 := by
  linarith [average_step P x (Q.starProjection (R.starProjection x)),
    average_step Q x (R.starProjection x)]

end GaussianTensor
