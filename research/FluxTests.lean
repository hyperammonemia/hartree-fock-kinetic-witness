import FluxHats
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Obtain both compact hats from a single variational test class of continuous,
piecewise C¹ multipliers. The outer trace values are zero. -/

noncomputable section
open Set MeasureTheory
open scoped Interval
namespace HFExterior.FluxHats

structure Piece (a b : ℝ) (h dh : ℝ → ℝ) : Prop where
  deriv : ∀ r, HasDerivAt h (dh r) r
  continuousDeriv : Continuous dh
  nonneg : ∀ r ∈ Icc a b, 0 ≤ h r

/-- Three smooth pieces with matching traces form a compact Lipschitz radial test upon
extension by zero. A zero-length middle piece permits a hat with only two pieces. -/
def testsOnPieces (q : ℝ) (F P : ℝ → ℝ) : Prop :=
  ∀ (l c S t : ℝ) (L dL M dM R dR : ℝ → ℝ),
    q < l → l < c → c ≤ S → S < t →
    Piece l c L dL → Piece c S M dM → Piece S t R dR →
    L l = 0 → L c = M c → M S = R S → R t = 0 →
    (∫ x in l..c, F x*dL x) + (∫ x in c..S, F x*dM x) + (∫ x in S..t, F x*dR x) +
    (∫ x in l..c, P x*L x) + (∫ x in c..S, P x*M x) + (∫ x in S..t, P x*R x) ≤ 0

theorem rise_piece {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) {a b : ℝ}
    (hab : a < b) : Piece a b (rise w a b) (fun r => w r/length w a b) where
  deriv r := (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable a r)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).div_const _
  continuousDeriv := hw.div_const _
  nonneg := fun _ hr => rise_nonneg hw hp hab hr

theorem fall_piece {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) {a b : ℝ}
    (hab : a < b) : Piece a b (fall w a b) (fun r => -w r/length w a b) where
  deriv r := (intervalIntegral.integral_hasDerivAt_left (hw.intervalIntegrable r b)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).div_const _
  continuousDeriv := hw.neg.div_const _
  nonneg := fun _ hr => fall_nonneg hw hp hab hr

private theorem const_piece (a b : ℝ) : Piece a b (fun _ => 1) (fun _ => 0) where
  deriv r := hasDerivAt_const r 1
  continuousDeriv := continuous_const
  nonneg := fun _ _ => zero_le_one

private theorem unit_fall (S : ℝ) : Piece S (S+1) (fun r => S+1-r) (fun _ => -1) where
  deriv r := by simpa using (hasDerivAt_const r (S+1)).sub (hasDerivAt_id r)
  continuousDeriv := continuous_const
  nonneg := fun _ hr => sub_nonneg.mpr hr.2

theorem compactTests_of_pieces {q : ℝ} {w v P : ℝ → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (h : testsOnPieces q (flux w v) P) : CompactTests q w v P := by
  have hfirst (a b : ℝ) : rise w a b a = 0 := by simp [rise,length]
  have hlast (a b : ℝ) : fall w a b b = 0 := by simp [fall,length]
  have hpeak (a b : ℝ) (hab : a < b) : rise w a b b = 1 := div_self (length_pos hw hp hab).ne'
  have hpeak' (a b : ℝ) (hab : a < b) : fall w a b a = 1 := div_self (length_pos hw hp hab).ne'
  constructor
  · intro l c t hql hlc hct
    have hh := h l c c t _ _ _ _ _ _ hql hlc le_rfl hct (rise_piece hw hp hlc) (const_piece c c)
      (fall_piece hw hp hct) (hfirst l c) (hpeak l c hlc) (hpeak' c t hct).symm (hlast c t)
    simpa only [intervalIntegral.integral_same,add_zero,neg_div,mul_neg,intervalIntegral.integral_neg,
      sub_eq_add_neg] using hh
  · intro l c S hql hlc hcS
    have hh := h l c S (S+1) _ _ _ _ _ _ hql hlc hcS.le (by linarith)
      (rise_piece hw hp hlc) (const_piece c S) (unit_fall S) (hfirst l c) (hpeak l c hlc)
      (by ring) (by ring)
    simpa only [mul_zero,intervalIntegral.integral_zero,add_zero,mul_neg,mul_one,
      intervalIntegral.integral_neg,sub_eq_add_neg] using hh

/-- Maximum principle from the actual three-piece Euler tests and finite flux. -/
theorem maximum_of_multipliers {q : ℝ} {w v P : ℝ → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (hv : Continuous v)
    (hac : ∀ a b : ℝ, q ≤ a → q ≤ b → AbsolutelyContinuousOnInterval v a b)
    (hb : v q ≤ 0) (hF : IntegrableOn (flux w v) (Ioi q))
    (hP : ∀ r, q < r → 0 ≤ v r → 0 ≤ P r)
    (htests : testsOnPieces q (flux w v) P) : ∀ c, q ≤ c → v c ≤ 0 :=
  maximum hw hp hv hac hb hF hP (compactTests_of_pieces hw hp htests)

end HFExterior.FluxHats
