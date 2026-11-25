import ClosedGraphDomain
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! A complete normed linear form domain embedded faithfully into the
two-electron real L² space by its wave component. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClosedGraphDomain
open RadialConfiguration

private def IsWeighted (a b : Wave) (k : Config → ℝ) := ∀ᵐ x ∂volume, b x = k x*a x

private theorem weight_zero (k : Config → ℝ) : IsWeighted 0 0 k := by
  filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=(volume:Measure Config))] with x hx
  simp [hx]

private theorem weight_add {a b d e : Wave} {k : Config → ℝ}
    (h : IsWeighted a b k) (j : IsWeighted d e k) : IsWeighted (a+d) (b+e) k := by
  filter_upwards [Lp.coeFn_add a d, Lp.coeFn_add b e,h,j] with x ha hb h0 h1
  simp only [ha,hb,Pi.add_apply,h0,h1,mul_add]

private theorem weight_smul (c : ℝ) {a b : Wave} {k : Config → ℝ}
    (h : IsWeighted a b k) : IsWeighted (c • a) (c • b) k := by
  filter_upwards [Lp.coeFn_smul c a,Lp.coeFn_smul c b,h] with x ha hb h0
  simp only [ha,hb,Pi.smul_apply,smul_eq_mul,h0]
  ring

def graphSpace : Submodule ℝ Carrier where
  carrier := domain
  zero_mem' := by
    refine ⟨fun p i φ hφ hk => ?_,weight_zero _,weight_zero _⟩
    change ⟪(0:Wave),_⟫_ℝ = -⟪(0:Wave),_⟫_ℝ
    simp
  add_mem' := by
    intro a b ha hb
    refine ⟨fun p i φ hφ hk => ?_,weight_add ha.2.1 hb.2.1,weight_add ha.2.2 hb.2.2⟩
    change ⟪a.1+b.1,_⟫_ℝ = -⟪a.2.1 p i+b.2.1 p i,_⟫_ℝ
    rw [inner_add_left,inner_add_left,ha.1 p i φ hφ hk,hb.1 p i φ hφ hk,neg_add]
  smul_mem' := by
    intro c a ha
    refine ⟨fun p i φ hφ hk => ?_,weight_smul c ha.2.1,weight_smul c ha.2.2⟩
    change ⟪c • a.1,_⟫_ℝ = -⟪c • a.2.1 p i,_⟫_ℝ
    rw [real_inner_smul_left,real_inner_smul_left,ha.1 p i φ hφ hk,mul_neg]

instance : CompleteSpace graphSpace := domain_complete

def waveMap : graphSpace →L[ℝ] Wave :=
  (ContinuousLinearMap.fst ℝ Wave _).comp graphSpace.subtypeL

theorem wave_norm_le (a : graphSpace) : ‖waveMap a‖ ≤ ‖a‖ := le_max_left _ _

private theorem gradient_identified (a b c : Wave) (v : Config)
    (h : (a,b) ∈ weakGraph v) (j : (a,c) ∈ weakGraph v) : b = c := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp b).locallyIntegrable (by norm_num))
    ((Lp.memLp c).locallyIntegrable (by norm_num))
  intro φ hφ hk
  have h0 := (weak_iff a b v).mp h φ (hφ.of_le (by decide)) hk
  have h1 := (weak_iff a c v).mp j φ (hφ.of_le (by decide)) hk
  rw [h0] at h1
  simpa only [smul_eq_mul,mul_comm] using neg_injective h1

private theorem weight_identified {a b c : Wave} {k : Config → ℝ}
    (h : IsWeighted a b k) (j : IsWeighted a c k) : b=c := by
  apply Lp.ext
  filter_upwards [h,j] with x h0 h1
  exact h0.trans h1.symm

theorem wave_injective : Function.Injective waveMap := by
  intro a b hab
  have hw : a.val.1=b.val.1 := hab
  apply Subtype.ext
  apply Prod.ext hw
  apply Prod.ext
  · funext p i
    have h := a.property.1 p i
    rw [hw] at h
    exact gradient_identified _ _ _ _ h (b.property.1 p i)
  · apply Prod.ext
    · have h : IsWeighted a.val.1 a.val.2.2.1 trapWeight := a.property.2.1
      rw [hw] at h
      exact weight_identified h b.property.2.1
    · have h : IsWeighted a.val.1 a.val.2.2.2 pairWeight := a.property.2.2
      rw [hw] at h
      exact weight_identified h b.property.2.2

#print axioms wave_injective
#print axioms wave_norm_le
end ClosedGraphDomain
