import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Real.Sqrt

/-! The continuous square-root seminorm of a positive semidefinite real
symmetric energy form on an already normed graph domain. -/
noncomputable section
namespace FormSeminorm
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

def squareRoot (b : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (symm : ∀ x y, b x y=b y x)
    (pos : ∀ x, 0≤b x x) : Seminorm ℝ D := by
  let core : PreInnerProductSpace.Core ℝ D := {
    inner := fun x y => b x y
    conj_inner_symm := fun x y => symm y x
    re_inner_nonneg := pos
    add_left := fun x y z => by simp
    smul_left := fun x y t => by simp }
  letI : PreInnerProductSpace.Core ℝ D := core
  exact @normSeminorm ℝ D _ (InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜:=ℝ))
    InnerProductSpace.Core.toNormedSpace

theorem sqrt_apply (b : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (symm : ∀ x y, b x y=b y x)
    (pos : ∀ x, 0≤b x x) (u : D) :
    squareRoot b symm pos u = Real.sqrt (b u u) := rfl

theorem sq_eq (b : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (symm : ∀ x y, b x y=b y x)
    (pos : ∀ x, 0≤b x x) (u : D) : (squareRoot b symm pos u)^2 = b u u := by
  rw [sqrt_apply,Real.sq_sqrt (pos u)]

theorem continuous_root (b : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (symm : ∀ x y, b x y=b y x)
    (pos : ∀ x, 0≤b x x) (hc : Continuous (fun x => b x x)) :
    Continuous (squareRoot b symm pos) := Real.continuous_sqrt.comp hc

#print axioms sq_eq
#print axioms continuous_root
end FormSeminorm
