import FinitePotential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
namespace HFKinetic
noncomputable section

private theorem glue (a : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a = g a) (hd : df a = dg a) (x : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t) (if x ≤ a then df x else dg x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with t ht
    simp [ht.le]
  · rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (df x) (Iic x) x := by
      apply (hf x).hasDerivWithinAt.congr <;> simp_all
    have hr : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (df x) (Ici x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr
      · intro t ht
        by_cases he : t = x
        · simp [he,hv]
        · simp [show ¬t ≤ x from fun h => he (le_antisymm h ht)]
      · simp [hv]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with t ht
    simp [not_le.mpr ht]

private def poly (t : ℝ) := 6*t^5 - 15*t^4 + 10*t^3
private def slope (t : ℝ) := 30*t^2*(1-t)^2

private theorem poly_derivative (t : ℝ) : HasDerivAt poly (slope t) t := by
  have H := ((((hasDerivAt_id t).pow 5).const_mul 6).sub
    (((hasDerivAt_id t).pow 4).const_mul 15)).add (((hasDerivAt_id t).pow 3).const_mul 10)
  convert H using 1 <;> first | rfl | (dsimp [slope]; ring)

def switchSlope (t : ℝ) : ℝ := if t ≤ 0 then 0 else if t ≤ 1 then slope t else 0

theorem switch_derivative (t : ℝ) : HasDerivAt FinitePotential.switch (switchSlope t) t := by
  let cap := fun t : ℝ => if t ≤ 1 then poly t else 1
  let dc := fun t : ℝ => if t ≤ 1 then slope t else 0
  have hc : ∀ x, HasDerivAt cap (dc x) x :=
    glue 1 poly (fun _ => 1) slope (fun _ => 0) poly_derivative
      (fun x => hasDerivAt_const x _) (by norm_num [poly]) (by norm_num [slope])
  have hd := glue 0 (fun _ => 0) cap (fun _ => 0) dc (fun x => hasDerivAt_const x _) hc
    (by norm_num [cap,poly]) (by norm_num [dc,slope]) t
  have heq : FinitePotential.switch = (fun t : ℝ => if t ≤ 0 then 0 else cap t) := by
    funext r
    rcases lt_trichotomy r 1 with hr | rfl | hr
    · simp [FinitePotential.switch,cap,poly,hr.le,not_le.mpr hr]
    · norm_num [FinitePotential.switch,cap,poly]
    · simp [FinitePotential.switch,cap,not_le.mpr hr,hr.le]
  rw [heq]
  exact hd

theorem switch_slope_range (r : ℝ) : 0 ≤ switchSlope r ∧ switchSlope r ≤ 2 := by
  unfold switchSlope
  split_ifs with h0 h1
  · norm_num
  · have hr : 0 ≤ r := by linarith
    have hs : 0 ≤ r*(1-r) := mul_nonneg hr (by linarith)
    have hx : r*(1-r) ≤ 1/4 := by nlinarith [sq_nonneg (r-1/2)]
    have hp := pow_le_pow_left₀ hs hx 2
    unfold slope
    constructor
    · positivity
    · nlinarith
  · norm_num

theorem envelope_derivative (r : ℝ) :
    HasDerivAt FinitePotential.envelope
      (switchSlope (r-FinitePotential.radius)*FinitePotential.switch (FinitePotential.radius+3-r) -
       FinitePotential.switch (r-FinitePotential.radius)*switchSlope (FinitePotential.radius+3-r)) r := by
  have ha := (switch_derivative (r-FinitePotential.radius)).comp r
    ((hasDerivAt_id r).sub_const FinitePotential.radius)
  have hc := (switch_derivative (FinitePotential.radius+3-r)).comp r
    ((hasDerivAt_id r).const_sub (FinitePotential.radius+3))
  convert ha.mul hc using 1 <;> first | rfl |
    (dsimp [Function.comp_def]; ring)

theorem envelope_slope_abs (r : ℝ) : |deriv FinitePotential.envelope r| ≤ 2 := by
  rw [(envelope_derivative r).deriv]
  have h1 := switch_slope_range (r-FinitePotential.radius)
  have h2 := switch_slope_range (FinitePotential.radius+3-r)
  have f1 := FinitePotential.switch_range (r-FinitePotential.radius)
  have f2 := FinitePotential.switch_range (FinitePotential.radius+3-r)
  have a := mul_le_mul h1.2 f2.2 f2.1 (by norm_num : (0:ℝ) ≤ 2)
  have c := mul_le_mul f1.2 h2.2 h2.1 (by norm_num : (0:ℝ) ≤ 1)
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg h1.1 f2.1],by nlinarith [mul_nonneg f1.1 h2.1]⟩

#print axioms switch_derivative
#print axioms envelope_slope_abs
end
end HFKinetic

