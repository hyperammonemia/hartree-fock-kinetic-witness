import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Unit vectors in a real form domain with the ambient Hilbert norm. No
completeness of the domain and no boundedness of the form are required. -/
noncomputable section
namespace SectionFive
open scoped InnerProductSpace

abbrev UnitState (D : Type*) [Norm D] := {x : D // ‖x‖ = 1}
abbrev Form (D : Type*) [AddCommGroup D] [Module ℝ D] := D →ₗ[ℝ] D →ₗ[ℝ] ℝ

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]

def energy (q : Form D) (s : UnitState D) : ℝ := q s.val s.val

/-- Variational minimality against every normalized vector in the same domain. -/
def Minimizes (q : UnitState D → ℝ) (s : UnitState D) : Prop := ∀ v, q s ≤ q v

omit [InnerProductSpace ℝ D] in
private theorem unit_ne (u : UnitState D) : u.val ≠ 0 := by
  intro h
  have hn := u.property
  rw [h, norm_zero] at hn
  norm_num at hn

private theorem mapped_pos (T : D ≃ₗ[ℝ] D) (s : UnitState D) : 0 < ‖T s.val‖ :=
  norm_pos_iff.mpr (fun h => unit_ne s (T.injective (h.trans T.map_zero.symm)))

def unitAction (T : D ≃ₗ[ℝ] D) (s : UnitState D) : UnitState D :=
  ⟨‖T s.val‖⁻¹ • T s.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mapped_pos T s)),
      inv_mul_cancel₀ (mapped_pos T s).ne']⟩

private theorem undo_unitAction (T : D ≃ₗ[ℝ] D) (s : UnitState D) :
    unitAction T.symm (unitAction T s) = s := by
  apply Subtype.ext
  change ‖T.symm (‖T s.val‖⁻¹ • T s.val)‖⁻¹ • T.symm (‖T s.val‖⁻¹ • T s.val) = s.val
  simp only [map_smul, LinearEquiv.symm_apply_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (mapped_pos T s)), s.property, mul_one, inv_inv,
    smul_smul, mul_inv_cancel₀ (mapped_pos T s).ne', one_smul]

/-- The normalized multiplier of a domain-preserving invertible linear map is
a bijection of the unit form domain. Its inverse is the normalized inverse map. -/
def normalizedEquiv (T : D ≃ₗ[ℝ] D) : UnitState D ≃ UnitState D where
  toFun := unitAction T
  invFun := unitAction T.symm
  left_inv := undo_unitAction T
  right_inv := undo_unitAction T.symm

theorem form_nonneg_of_unit (p : Form D)
    (posUnit : ∀ s : UnitState D, 0 ≤ p s.val s.val) (x : D) : 0 ≤ p x x := by
  by_cases h : x = 0
  · simp [h]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr h
  let u : UnitState D := ⟨‖x‖⁻¹ • x, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
  have hu : ‖x‖ • u.val = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hpos := mul_nonneg (sq_nonneg ‖x‖) (posUnit u)
  have hx : p (‖x‖ • u.val) (‖x‖ • u.val) = ‖x‖^2*p u.val u.val := by
    simp [map_smul, smul_eq_mul, pow_two, mul_assoc]
  rwa [← hx, hu] at hpos

private theorem null_shift (p : Form D) (pos : ∀ x, 0 ≤ p x x)
    (u v : D) (hv : p v v = 0) (t : ℝ) :
    p (u+t • v) (u+t • v) = p u u := by
  have line (s : ℝ) : p (u+s • v) (u+s • v) = p u u+s*(p u v+p v u) := by
    simp [map_add, map_smul, smul_eq_mul, hv]
    ring
  have hc : p u v+p v u = 0 := by
    by_contra bad
    have h := pos (u+(-(p u u+1)/(p u v+p v u)) • v)
    rw [line, div_mul_cancel₀ _ bad] at h
    linarith
  rw [line, hc, mul_zero, add_zero]

/-- An oscillator comparison on a known codimension-one space suffices. The
interacting ground state is obtained by minimization. Stationarity and its
relative gap estimate are proved here rather than assumed. -/
theorem gap_from_comparison (q : Form D) (ψ : UnitState D) (ref : D) (κ : ℝ)
    (hκ : 0 < κ) (hmin : Minimizes (energy q) ψ) (he : energy q ψ ≤ 0)
    (hcomp : ∀ z : D, ⟪ref,z⟫_ℝ = 0 → κ*‖z‖^2 ≤ q z z)
    (y : UnitState D) :
    κ*(1-⟪ψ.val,y.val⟫_ℝ^2) ≤ energy q y-energy q ψ := by
  let E := energy q ψ
  let p : Form D := q-E • innerₗ D
  have diag (x : D) : p x x = q x x-E*‖x‖^2 := by
    simp [p, smul_eq_mul]
  have pos (x : D) : 0 ≤ p x x := by
    apply form_nonneg_of_unit p _ x
    intro s
    rw [diag, s.property]
    have hs := hmin s
    change q ψ.val ψ.val ≤ q s.val s.val at hs
    dsimp [E, energy]
    linarith
  have zero : p ψ.val ψ.val = 0 := by simp [diag, ψ.property, E, energy]
  have overlap : ⟪ref,ψ.val⟫_ℝ ≠ 0 := by
    intro hz
    have b := hcomp ψ.val hz
    rw [ψ.property] at b
    change q ψ.val ψ.val ≤ 0 at he
    linarith
  let t := -⟪ref,y.val⟫_ℝ / ⟪ref,ψ.val⟫_ℝ
  let z := y.val+t • ψ.val
  have orth : ⟪ref,z⟫_ℝ = 0 := by
    simp only [z, inner_add_right, real_inner_smul_right, t, div_mul_cancel₀ _ overlap]
    ring
  have swap : ⟪y.val,ψ.val⟫_ℝ = ⟪ψ.val,y.val⟫_ℝ := real_inner_comm _ _
  have normz : 1-⟪ψ.val,y.val⟫_ℝ^2 ≤ ‖z‖^2 := by
    rw [show z = y.val+t • ψ.val from rfl, norm_add_sq_real, real_inner_smul_right,
      swap, norm_smul, Real.norm_eq_abs, ψ.property, y.property, mul_one,
      sq_abs]
    nlinarith only [sq_nonneg (t+⟪ψ.val,y.val⟫_ℝ)]
  have gap := hcomp z orth
  have ev : E*‖z‖^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he (sq_nonneg _)
  have same := null_shift p pos y.val ψ.val zero t
  change p z z = p y.val y.val at same
  rw [diag, diag, y.property] at same
  have lower := mul_le_mul_of_nonneg_left normz hκ.le
  change κ*(1-⟪ψ.val,y.val⟫_ℝ^2) ≤ q y.val y.val-E
  linarith

#print axioms normalizedEquiv
#print axioms gap_from_comparison
end SectionFive
