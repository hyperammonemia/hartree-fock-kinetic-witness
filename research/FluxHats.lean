import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Compact radial flux tests. Here w is the reciprocal of the positive radial Jacobian p. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Interval Topology
namespace HFExterior.FluxHats

def length (w : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ r in a..b, w r
def rise (w : ℝ → ℝ) (a b r : ℝ) : ℝ := length w a r / length w a b
def fall (w : ℝ → ℝ) (a b r : ℝ) : ℝ := length w r b / length w a b
def flux (w v : ℝ → ℝ) (r : ℝ) : ℝ := deriv v r / w r

theorem length_pos {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ r, 0 < w r)
    {a b : ℝ} (hab : a < b) : 0 < length w a b :=
  intervalIntegral.integral_pos hab hw.continuousOn (fun x _ => (hpos x).le)
    ⟨a, ⟨le_rfl, hab.le⟩, hpos a⟩

theorem rise_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ r, 0 < w r)
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) : 0 ≤ rise w a b x :=
  div_nonneg (intervalIntegral.integral_nonneg hx.1 (fun z _ => (hpos z).le))
    (length_pos hw hpos hab).le

theorem fall_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ r, 0 < w r)
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) : 0 ≤ fall w a b x :=
  div_nonneg (intervalIntegral.integral_nonneg hx.2 (fun z _ => (hpos z).le))
    (length_pos hw hpos hab).le

theorem flux_rise_value {w v : ℝ → ℝ} (hpos : ∀ r, 0 < w r) {a b : ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) :
    (∫ r in a..b, flux w v r * (w r / length w a b)) =
      (v b - v a) / length w a b := by
  have h (r : ℝ) : flux w v r * (w r/length w a b) = deriv v r/length w a b := by
    simp only [flux,div_eq_mul_inv]
    calc
      _ = deriv v r * ((w r)⁻¹*w r) * (length w a b)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ (hpos r).ne',mul_one]
  simp only [h, intervalIntegral.integral_div, hv.integral_deriv_eq_sub]

/-- This predicate is the weak Euler inequality evaluated on the two compact
piecewise-C¹ nonnegative tests. The first has two reciprocal-Jacobian ramps.
The second falls linearly on a unit interval. The integrands retain the
actual flux term and the actual potential term on each piece. -/
structure CompactTests (q : ℝ) (w v P : ℝ → ℝ) : Prop where
  cap : ∀ l c t : ℝ, q < l → l < c → c < t →
    (∫ r in l..c, flux w v r * (w r/length w l c)) -
      (∫ r in c..t, flux w v r * (w r/length w c t)) +
      (∫ r in l..c, P r * rise w l c r) + (∫ r in c..t, P r*fall w c t r) ≤ 0
  cutoff : ∀ l c S : ℝ, q < l → l < c → c < S →
    (∫ r in l..c, flux w v r * (w r/length w l c)) - (∫ r in S..S+1, flux w v r) +
      (∫ r in l..c, P r*rise w l c r) + (∫ r in c..S, P r) +
      (∫ r in S..S+1, P r * (S+1-r)) ≤ 0

/-- A last crossing of the positive half-level gives a compact rising interval. -/
private theorem select_rise {v : ℝ → ℝ} (hv : Continuous v) {q c : ℝ} (hqc : q < c)
    (hq : v q ≤ 0) (hc : 0 < v c) :
    ∃ l, q < l ∧ l < c ∧ v l < v c ∧ ∀ x ∈ Icc l c, 0 ≤ v x := by
  let K := Icc q c ∩ {x | v x = v c/2}
  have hcomp : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hv continuous_const)
  obtain ⟨d,hd,hvd⟩ := intermediate_value_Icc hqc.le hv.continuousOn
    (show v c/2 ∈ Icc (v q) (v c) from ⟨by linarith,by linarith⟩)
  obtain ⟨l,hl,hmax⟩ := hcomp.exists_isMaxOn (show K.Nonempty from ⟨d,hd,hvd⟩)
    continuous_id.continuousOn
  have hlv : v l = v c/2 := hl.2
  have hlq : q < l := lt_of_le_of_ne hl.1.1 (by intro h; rw [← h] at hlv; linarith)
  have hlc : l < c := lt_of_le_of_ne hl.1.2 (by intro h; rw [h] at hlv; linarith)
  refine ⟨l,hlq,hlc,by linarith,?_⟩
  intro x hx
  by_contra! hneg
  obtain ⟨y,hxy,hyv⟩ := intermediate_value_Icc hx.2 hv.continuousOn
    (show v c/2 ∈ Icc (v x) (v c) from ⟨by linarith, by linarith⟩)
  have hxy' : x < y := lt_of_le_of_ne hxy.1 (by intro h; rw [← h] at hyv; linarith)
  have hyK : y ∈ K := ⟨⟨hlq.le.trans (hx.1.trans hxy.1),hxy.2⟩,hyv⟩
  have hyl : y ≤ l := hmax y hyK
  linarith [hx.1]

private theorem small_tail {F : ℝ → ℝ} {q c A : ℝ} (hf : IntegrableOn F (Ioi q))
    (hqc : q ≤ c) (hA : 0 < A) :
    ∃ S : ℝ, c < S ∧ |∫ r in S..S+1, F r| < A := by
  have hl : Tendsto (fun S : ℝ => ∫ x in Ioi S, |F x|) atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨S,hS,hsmall⟩ := ((eventually_gt_atTop c).and (hl.eventually (gt_mem_nhds hA))).exists
  refine ⟨S,hS,lt_of_le_of_lt ?_ hsmall⟩
  have hb : S ≤ S+1 := by linarith
  have hfS : IntegrableOn (fun x => |F x|) (Ioi S) := by
    simpa only [Real.norm_eq_abs] using hf.norm.mono_set (Ioi_subset_Ioi (hqc.trans hS.le))
  calc
    _ ≤ ∫ x in S..S+1, |F x| := intervalIntegral.abs_integral_le_integral_abs hb
    _ = ∫ x in Ioc S (S+1), |F x| := intervalIntegral.integral_of_le hb
    _ ≤ _ := setIntegral_mono_set hfS (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall fun _ hx => hx.1)

/-- Compact hats and an integrable flux preclude a positive excursion on the entire half-line. -/
theorem maximum {q : ℝ} {w v P : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ r, 0 < w r)
    (hv : Continuous v) (hAC : ∀ a b : ℝ, q ≤ a → q ≤ b → AbsolutelyContinuousOnInterval v a b)
    (hboundary : v q ≤ 0) (hF : IntegrableOn (flux w v) (Ioi q))
    (hP : ∀ r, q < r → 0 ≤ v r → 0 ≤ P r) (htest : CompactTests q w v P) :
    ∀ c, q ≤ c → v c ≤ 0 := by
  intro c hqc
  rcases hqc.eq_or_lt with heq | hqc'
  · simpa only [← heq] using hboundary
  by_contra! hc
  obtain ⟨l,hlq,hlc,hvl,hlpos⟩ := select_rise hv hqc' hboundary hc
  have left := flux_rise_value hpos (hAC l c hlq.le hqc)
  have A : 0 < (v c-v l)/length w l c :=
    div_pos (sub_pos.mpr hvl) (length_pos hw hpos hlc)
  have Pl : 0 ≤ ∫ r in l..c, P r*rise w l c r := intervalIntegral.integral_nonneg hlc.le
    (fun r hr => mul_nonneg (hP r (hlq.trans_le hr.1) (hlpos r hr))
      (rise_nonneg hw hpos hlc hr))
  by_cases hright : ∀ r, c ≤ r → 0 ≤ v r
  · obtain ⟨S,hS,hsmall⟩ := small_tail hF hqc A
    have hwk := htest.cutoff l c S hlq hlc hS
    rw [left] at hwk
    have Pc : 0 ≤ ∫ r in c..S, P r := intervalIntegral.integral_nonneg hS.le
      (fun r hr => hP r (hqc'.trans_le hr.1) (hright r hr.1))
    have rem : 0 ≤ ∫ r in S..S+1, P r*(S+1-r) := intervalIntegral.integral_nonneg (by linarith)
      (fun r hr => mul_nonneg (hP r ((hqc'.trans hS).trans_le hr.1)
        (hright r (hS.le.trans hr.1))) (sub_nonneg.mpr hr.2))
    linarith [le_abs_self (∫ r in S..S+1, flux w v r)]
  · push_neg at hright
    obtain ⟨d,hcd,hd⟩ := hright
    have hcd' : c < d := lt_of_le_of_ne hcd (by intro h; rw [← h] at hd; linarith)
    obtain ⟨l',hl'd,hl'c,hl'v,hl'p⟩ := select_rise
      (v := fun x => v (-x)) (hv.comp continuous_neg)
      (q := -d) (c := -c) (by linarith) (by simpa using hd.le) (by simpa using hc)
    let t := -l'
    have hct : c < t := by dsimp [t]; linarith
    have htv : v t < v c := by simpa only [t,neg_neg] using hl'v
    have htpos (r : ℝ) (hr : r ∈ Icc c t) : 0 ≤ v r := by
      have h : -r ∈ Icc l' (-c) := ⟨by dsimp [t] at hr; linarith [hr.2],by linarith [hr.1]⟩
      simpa only [neg_neg] using hl'p (-r) h
    have Pr : 0 ≤ ∫ r in c..t, P r*fall w c t r := intervalIntegral.integral_nonneg hct.le
      (fun r hr => mul_nonneg (hP r (hqc'.trans_le hr.1) (htpos r hr))
        (fall_nonneg hw hpos hct hr))
    have right := flux_rise_value hpos (hAC c t hqc (hqc.trans hct.le))
    have hwk := htest.cap l c t hlq hlc hct
    rw [left,right] at hwk
    have hnegative : (v t-v c)/length w c t < 0 :=
      div_neg_of_neg_of_pos (sub_neg.mpr htv) (length_pos hw hpos hct)
    linarith

end HFExterior.FluxHats
