import RadialConfiguration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! Closedness and completeness of the concrete two-electron graph domain.
The graph records weak derivatives, oscillator moment and Coulomb form
weight. Its topology is the graph topology, while mass is the L² norm
of the first component. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace ClosedGraphDomain
open RadialConfiguration

/-- The multiplication operator is closed for every finite field, including
the singular Coulomb weight with a chosen value on the null collision set. -/
theorem multiplication_closed (w : Config → ℝ) :
    IsClosed {z : Wave × Wave | ∀ᵐ x ∂volume, z.2 x = w x*z.1 x} := by
  apply IsSeqClosed.isClosed
  intro f v hf hv
  obtain ⟨k,hk,h₁⟩ := (tendstoInMeasure_of_tendsto_Lp hv.fst).exists_seq_tendsto_ae
  obtain ⟨m,hm,h₂⟩ := (tendstoInMeasure_of_tendsto_Lp (hv.snd.comp hk.tendsto_atTop)).exists_seq_tendsto_ae
  have he : ∀ᵐ x : Config ∂volume, ∀ n : ℕ, (f n).2 x = w x*(f n).1 x :=
    ae_all_iff.mpr hf
  filter_upwards [h₁,h₂,he] with x hx hy heq
  apply tendsto_nhds_unique hy
  have lim := (hx.comp hm.tendsto_atTop).const_mul (w x)
  exact lim.congr (fun n => (heq (k (m n))).symm)

def testWave (φ : Config → ℝ) (hc : Continuous φ) (hk : HasCompactSupport φ) : Wave :=
  (hc.memLp_of_hasCompactSupport hk).toLp φ

def testSlope (φ : Config → ℝ) (v : Config) := fun x => fderiv ℝ φ x v

def testDerivative (φ : Config → ℝ) (v : Config) (hφ : ContDiff ℝ 1 φ)
    (hk : HasCompactSupport φ) : Wave :=
  testWave (testSlope φ v) ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (HasCompactSupport.fderiv_apply ℝ hk v)

def weakGraph (v : Config) : Set (Wave × Wave) := {z |
  ∀ (φ : Config → ℝ) (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ),
    ⟪z.1,testDerivative φ v hφ hk⟫_ℝ = -⟪z.2,testWave φ hφ.continuous hk⟫_ℝ}

theorem inner_test (a : Wave) (φ : Config → ℝ) (hc : Continuous φ) (hk : HasCompactSupport φ) :
    ⟪a,testWave φ hc hk⟫_ℝ = ∫ x, a x*φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hc.memLp_of_hasCompactSupport hk : MemLp φ 2 volume).coeFn_toLp] with x hx
  change inner ℝ (a x) ((hc.memLp_of_hasCompactSupport hk : MemLp φ 2 volume).toLp φ x) = _
  rw [hx,RCLike.inner_apply']
  rfl

theorem weak_iff (a b : Wave) (v : Config) :
    (a,b) ∈ weakGraph v ↔ ∀ (φ : Config → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, a x * fderiv ℝ φ x v) = -(∫ x, b x*φ x) := by
  change (∀ (φ : Config → ℝ) (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ),
    ⟪a,testDerivative φ v hφ hk⟫_ℝ = -⟪b,testWave φ hφ.continuous hk⟫_ℝ) ↔ _
  simp only [testDerivative,inner_test,testSlope]

theorem weak_closed (v : Config) : IsClosed (weakGraph v) := by
  apply IsSeqClosed.isClosed
  intro f a hf ha φ hφ hk
  have h₁ : Tendsto (fun n => ⟪(f n).1,testDerivative φ v hφ hk⟫_ℝ) atTop
      (𝓝 ⟪a.1,testDerivative φ v hφ hk⟫_ℝ) := ha.fst.inner tendsto_const_nhds
  have h₂ : Tendsto (fun n => -⟪(f n).2,testWave φ hφ.continuous hk⟫_ℝ) atTop
      (𝓝 (-⟪a.2,testWave φ hφ.continuous hk⟫_ℝ)) := (ha.snd.inner tendsto_const_nhds).neg
  exact tendsto_nhds_unique h₁ (h₂.congr (fun n => (hf n φ hφ hk).symm))

abbrev Carrier := Wave × (Fin 2 → Fin 3 → Wave) × Wave × Wave
def trapWeight (z : Config) := Real.sqrt (‖z.1‖^2+‖z.2‖^2)
def pairWeight (z : Config) := Real.sqrt (‖z.1-z.2‖⁻¹)

def domain : Set Carrier := {a |
  (∀ p i, (a.1,a.2.1 p i) ∈ weakGraph (axis p i)) ∧
  (∀ᵐ x ∂volume, a.2.2.1 x = trapWeight x*a.1 x) ∧
  (∀ᵐ x ∂volume, a.2.2.2 x = pairWeight x*a.1 x)}

theorem domain_closed : IsClosed domain := by
  apply IsSeqClosed.isClosed
  intro f a hf ha
  refine ⟨fun p i => ?_, ?_, ?_⟩
  · apply (weak_closed (axis p i)).isSeqClosed (fun n => (hf n).1 p i)
    have hc : Continuous (fun a : Carrier => (a.1,a.2.1 p i)) := by fun_prop
    exact hc.continuousAt.tendsto.comp ha
  · apply (multiplication_closed trapWeight).isSeqClosed (fun n => (hf n).2.1)
    have hc : Continuous (fun a : Carrier => (a.1,a.2.2.1)) := by fun_prop
    exact hc.continuousAt.tendsto.comp ha
  · apply (multiplication_closed pairWeight).isSeqClosed (fun n => (hf n).2.2)
    have hc : Continuous (fun a : Carrier => (a.1,a.2.2.2)) := by fun_prop
    exact hc.continuousAt.tendsto.comp ha

theorem domain_complete : CompleteSpace domain := domain_closed.completeSpace_coe

#print axioms multiplication_closed
#print axioms weak_iff
#print axioms domain_complete
end ClosedGraphDomain
