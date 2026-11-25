import SlaterGeometry

open scoped TensorProduct ComplexConjugate
open SlaterGeometry

namespace SlaterOccupation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Excited part of a spin orbital relative to two occupied orthonormal vectors. -/
noncomputable def unoccupied (a b x : H) : H :=
  x - inner ℂ a x • a - inner ℂ b x • b

private theorem unoccupied_gram (a b x y : H) (ha : ‖a‖=1) (hb : ‖b‖=1)
    (hab : inner ℂ a b=0) :
    inner ℂ (unoccupied a b x) (unoccupied a b y) = inner ℂ x y -
      conj (inner ℂ a x) * inner ℂ a y - conj (inner ℂ b x) * inner ℂ b y := by
  have hba : inner ℂ b a=0 := by rw [← inner_conj_symm b a,hab]; simp
  have hxa : inner ℂ x a = conj (inner ℂ a x) := (inner_conj_symm x a).symm
  have hxb : inner ℂ x b = conj (inner ℂ b x) := (inner_conj_symm x b).symm
  have haa : inner ℂ a a=1 := by simp [inner_self_eq_norm_sq_to_K,ha]
  have hbb : inner ℂ b b=1 := by simp [inner_self_eq_norm_sq_to_K,hb]
  simp only [unoccupied,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    hxa,hxb,haa,hbb,hab,hba]
  ring

theorem unoccupied_norm_sq (a b x : H) (ha : ‖a‖=1) (hb : ‖b‖=1) (hab : inner ℂ a b=0) :
    ‖unoccupied a b x‖^2 = ‖x‖^2 - ‖inner ℂ a x‖^2 - ‖inner ℂ b x‖^2 := by
  have h := unoccupied_gram a b x x ha hb hab
  rw [Complex.conj_mul',Complex.conj_mul',inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h

private theorem complex_lagrange (a b c d : ℂ) :
    ‖a*d-c*b‖^2 + ‖conj a*c+conj b*d‖^2 =
      (‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

/-- The expected number of unoccupied electrons equals the probability of at
    least one excitation plus the probability of a double excitation. -/
theorem occupation_identity (a b x y : H) (ha : ‖a‖=1) (hb : ‖b‖=1) (hab : inner ℂ a b=0)
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hxy : inner ℂ x y=0) :
    1 - ‖inner ℂ (slater a b) (slater x y)‖^2 =
      ‖unoccupied a b x‖^2 + ‖unoccupied a b y‖^2 -
        ‖slater (unoccupied a b x) (unoccupied a b y)‖^2 := by
  have hgram : inner ℂ (unoccupied a b x) (unoccupied a b y) =
      -(conj (inner ℂ a x) * inner ℂ a y + conj (inner ℂ b x) * inner ℂ b y) := by
    rw [unoccupied_gram a b x y ha hb hab,hxy]
    ring
  rw [inner_slater,slater_norm_sq,hgram,norm_neg,unoccupied_norm_sq a b x ha hb hab,
    unoccupied_norm_sq a b y ha hb hab,hx,hy]
  linarith only [complex_lagrange (inner ℂ a x) (inner ℂ b x) (inner ℂ a y) (inner ℂ b y)]

/-- A one-particle form gap implies the two-electron determinant gap uniformly
    over unrestricted complex spin orbitals, with the same constant. -/
theorem one_body_gap (q : H → ℝ) (a b x y : H) (ha : ‖a‖=1) (hb : ‖b‖=1)
    (hab : inner ℂ a b=0) (hx : ‖x‖=1) (hy : ‖y‖=1) (hxy : inner ℂ x y=0)
    (hgap : ∀ z, ‖unoccupied a b z‖^2/2 ≤ q z) :
    (1-‖inner ℂ (slater a b) (slater x y)‖^2)/2 ≤ q x + q y := by
  rw [occupation_identity a b x y ha hb hab hx hy hxy]
  linarith [sq_nonneg ‖slater (unoccupied a b x) (unoccupied a b y)‖, hgap x, hgap y]

end SlaterOccupation
