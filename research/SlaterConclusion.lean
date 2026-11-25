import SlaterEnergy
import SlaterOccupation

open scoped TensorProduct
open SlaterGeometry SlaterOccupation SlaterEnergy

namespace SlaterConclusion

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

noncomputable def energy (I : (H ⊗[ℂ] H) →ₗᵢ[ℂ] G) (L : (H ⊗[ℂ] H) →ₗ[ℂ] G)
    (q : H → ℝ) (x y : H) : ℝ := q x + q y + (1/100)*interaction I L (slater x y)

/-- Uniqueness and the global gap over orthonormal complex spinors, using a
    one-particle gap, Coulomb centering, a norm bound, and the lower form bound. -/
theorem reference_uniquely_minimizes (I : (H ⊗[ℂ] H) →ₗᵢ[ℂ] G) (L : (H ⊗[ℂ] H) →ₗ[ℂ] G)
    (q : H → ℝ) (P : Submodule ℂ H) [P.HasOrthogonalProjection] (a b : H)
    (hPa : a∈P) (hPb : b∈P) (ha : ‖a‖=1) (hb : ‖b‖=1) (hab : inner ℂ a b=0)
    (hq0a : q a=0) (hq0b : q b=0) (hgap : ∀ z, ‖unoccupied a b z‖^2/2 ≤ q z)
    (symm : ∀ u v, inner ℂ (I u) (L v) = inner ℂ (L u) (I v))
    (hcenter : ∀ z ∈ P, ∀ w : H, inner ℂ (L (slater a b)) (I (slater z w))=0)
    (hn : ‖L (slater a b)‖ ≤ 8) (hfloor : ∀ z, -(4:ℝ)*‖z‖^2 ≤ interaction I L z) :
    ∀ x y : H, ‖x‖=1 → ‖y‖=1 → inner ℂ x y=0 →
      energy I L q a b + 3/10*(1-‖inner ℂ (slater a b) (slater x y)‖^2) ≤ energy I L q x y ∧
      (energy I L q x y ≤ energy I L q a b →
        ∃ c : ℂ, ‖c‖=1 ∧ slater x y = c • slater a b) := by
  have hD := slater_unit a b ha hb hab
  have href : energy I L q a b=0 := by
    simp only [energy,interaction,hq0a,hq0b,symm (slater a b) (slater a b),hcenter a hPa b]
    norm_num
  intro x y hx hy hxy
  have hgap' := one_body_gap q a b x y ha hb hab hx hy hxy hgap
  have h := global_hf_margin I L P a b x y hPa hPb hD hx hy hxy symm hcenter hn hfloor
    (q x+q y) hgap'
  change 3/10*(1-‖inner ℂ (slater a b) (slater x y)‖^2) ≤ energy I L q x y at h
  rw [href,zero_add]
  exact ⟨h, fun hle => equality_is_phase (slater a b) (slater x y) _ hD (slater_unit x y hx hy hxy) h hle⟩

end SlaterConclusion
