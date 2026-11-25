import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Attainment at the bottom of a closed quadratic form by control on one
codimension-one subspace. The norm on D is its complete form norm. -/
noncomputable section
open Filter
open scoped Topology
namespace FormAttainment
variable {𝕜 D : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]

private theorem tri (p : Seminorm 𝕜 D) (u v : D) : p (u-v) ≤ p u+p v := by
  simpa only [sub_eq_add_neg, map_neg_eq_map] using map_add_le_add p u (-v)

private theorem approximate_affine (p : Seminorm 𝕜 D) (L : D →L[𝕜] 𝕜)
    (g : D) (hg : L g = 1) (C : ℝ) (hC : 0 < C)
    (coerc : ∀ w, L w = 0 → ‖w‖ ≤ C*p w)
    (near : ∀ t : ℝ, 0<t → ∃ u : D, ‖u‖=1 ∧ p u<t)
    (ε : ℝ) (hε : 0<ε) : ∃ y, L y=1 ∧ p y<ε := by
  by_contra! fail
  have lc (u : D) : ‖L u‖ ≤ p u/ε := by
    by_cases hz : L u=0
    · simp [hz, div_nonneg (apply_nonneg p u) hε.le]
    have hu := fail ((L u)⁻¹ • u) (by simp [hz])
    rw [map_smul_eq_mul, norm_inv, ← div_eq_inv_mul] at hu
    exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using (le_div_iff₀ (norm_pos_iff.mpr hz)).1 hu)
  let K := C + (C*p g+‖g‖)/ε
  have cg : 0 ≤ C*p g+‖g‖ := by positivity [apply_nonneg p g]
  have hK : 0<K := add_pos_of_pos_of_nonneg hC (div_nonneg cg hε.le)
  obtain ⟨u,hu,hp⟩ := near (1/K) (by positivity)
  let z := u - L u • g
  have hz : L z=0 := by simp [z,hg]
  have ht := tri p u (L u • g)
  rw [map_smul_eq_mul] at ht
  have hn : ‖u‖ ≤ ‖z‖+‖L u‖*‖g‖ := by
    simpa only [z, sub_add_cancel, norm_smul] using norm_add_le z (L u • g)
  have h1 : ‖u‖ ≤ C*p u + (C*p g+‖g‖)*‖L u‖ := by
    nlinarith only [hn, coerc z hz, mul_le_mul_of_nonneg_left ht hC.le]
  have h2 := mul_le_mul_of_nonneg_left (lc u) cg
  have h3 : ‖u‖ ≤ K*p u := by
    calc
      _ ≤ C*p u + (C*p g+‖g‖)*‖L u‖ := h1
      _ ≤ C*p u + (C*p g+‖g‖)*(p u/ε) := add_le_add (le_refl _) h2
      _ = _ := by unfold K; ring
  rw [hu] at h3
  exact (not_lt_of_ge h3) (by simpa [mul_comm] using (lt_div_iff₀ hK).1 hp)

/-- A continuous form seminorm that can be arbitrarily small on unit vectors
vanishes on an actual nonzero vector when it controls the form norm on ker L.
The proof uses completeness and a single reference mode. -/
theorem attained_zero [CompleteSpace D] (p : Seminorm 𝕜 D) (hp : Continuous p)
    (L : D →L[𝕜] 𝕜) (g : D) (hg : L g = 1) (C : ℝ) (hC : 0 < C)
    (coerc : ∀ w, L w=0 → ‖w‖ ≤ C*p w)
    (near : ∀ t : ℝ, 0<t → ∃ u : D, ‖u‖=1 ∧ p u<t) :
    ∃ w : D, L w=1 ∧ p w=0 := by
  choose v hv hsmall using fun n : ℕ => approximate_affine p L g hg C hC coerc near
    (1/((n:ℝ)+1)) (by positivity)
  have lim : Tendsto (fun n => p (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => apply_nonneg p (v n)) (fun n => (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : CauchySeq v := by
    apply Metric.cauchySeq_iff.mpr
    intro ε he
    have delta : 0 < ε/(2*C) := by positivity
    obtain ⟨N,hN⟩ := eventually_atTop.1 (lim.eventually (gt_mem_nhds delta))
    refine ⟨N,fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hz : L (v m-v n)=0 := by simp [hv]
    have h := mul_le_mul_of_nonneg_left (tri p (v m) (v n)) hC.le
    have hden : 0 < 2*C := by positivity
    nlinarith only [coerc _ hz, h, (lt_div_iff₀ hden).1 (hN m hm),
      (lt_div_iff₀ hden).1 (hN n hn)]
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, ?_, tendsto_nhds_unique (hp.continuousAt.tendsto.comp hw) lim⟩
  have hL : Tendsto (fun n => L (v n)) atTop (𝓝 (1:𝕜)) := by simp [hv]
  exact tendsto_nhds_unique (L.continuous.continuousAt.tendsto.comp hw) hL

#print axioms attained_zero
end FormAttainment
