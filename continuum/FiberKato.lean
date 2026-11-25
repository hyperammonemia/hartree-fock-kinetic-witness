import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The regularized Hilbert-valued fiber norm in the weak marginal test. -/

noncomputable section
open scoped InnerProductSpace

namespace HFExterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fiberLength (ε : ℝ) (u : E) : ℝ := Real.sqrt (‖u‖ ^ 2 + ε ^ 2)

def fiberSpeed (ε : ℝ) (u v : E) : ℝ := ⟪u, v⟫_ℝ / fiberLength ε u

omit [InnerProductSpace ℝ E] in
theorem fiberLength_pos {ε : ℝ} (he : 0 < ε) (u : E) : 0 < fiberLength ε u := by
  unfold fiberLength
  positivity

theorem fiberLength_hasDerivAt {U : ℝ → E} {v : E} {x ε : ℝ}
    (he : 0 < ε) (hU : HasDerivAt U v x) :
    HasDerivAt (fun t => fiberLength ε (U t)) (fiberSpeed ε (U x) v) x := by
  have ha : 0 < ‖U x‖ ^ 2 + ε ^ 2 := by positivity
  have hsum : HasDerivAt (fun t => ‖U t‖^2 + ε^2) (2 * ⟪U x, v⟫_ℝ) x :=
    hU.norm_sq.add_const _
  apply (HasDerivAt.sqrt hsum ha.ne').congr_deriv
  unfold fiberSpeed fiberLength
  field_simp [(Real.sqrt_pos.mpr ha).ne']

theorem fiberSpeed_sq_le {ε : ℝ} (he : 0 < ε) (u v : E) :
    fiberSpeed ε u v ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [fiberSpeed, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (fiberLength_pos he u))).mpr
  unfold fiberLength
  rw [Real.sq_sqrt (by positivity)]
  have hc := real_inner_mul_inner_self_le u v
  simp only [real_inner_self_eq_norm_sq] at hc
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖v‖)]

/-- One Cartesian kinetic pairing against the actual regularized vector test η U / sε. -/
theorem fiber_test_pairing {U : ℝ → E} {v : E} {η : ℝ → ℝ} {η' x ε : ℝ}
    (he : 0 < ε) (hU : HasDerivAt U v x) (hη : HasDerivAt η η' x) :
    ⟪v, deriv (fun t => (η t / fiberLength ε (U t)) • U t) x⟫_ℝ =
      fiberSpeed ε (U x) v * η' +
      η x / fiberLength ε (U x) * (‖v‖ ^ 2 - fiberSpeed ε (U x) v ^ 2) := by
  have hs := fiberLength_hasDerivAt he hU
  have hn := (fiberLength_pos he (U x)).ne'
  have hd := (hη.div hs hn).smul hU
  change ⟪v, deriv ((η / fun t => fiberLength ε (U t)) • U) x⟫_ℝ = _
  rw [hd.deriv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (U x) v]
  simp only [Pi.div_apply]
  unfold fiberSpeed
  field_simp [hn]
  ring

theorem fiber_test_kinetic_lower {U : ℝ → E} {v : E} {η : ℝ → ℝ} {η' x ε : ℝ}
    (he : 0 < ε) (hU : HasDerivAt U v x) (hη : HasDerivAt η η' x) (hη0 : 0 ≤ η x) :
    fiberSpeed ε (U x) v * η' ≤
      ⟪v, deriv (fun t => (η t / fiberLength ε (U t)) • U t) x⟫_ℝ := by
  rw [fiber_test_pairing he hU hη]
  exact le_add_of_nonneg_right
    (mul_nonneg (div_nonneg hη0 (fiberLength_pos he (U x)).le)
      (sub_nonneg.mpr (fiberSpeed_sq_le he (U x) v)))

end HFExterior
