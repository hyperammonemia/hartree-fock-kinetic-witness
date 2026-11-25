import UnitVariational
import RadialConfiguration
import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section
namespace FixedRadialSectionFive
open SectionFive RadialConfiguration MeasureTheory Set
open scoped InnerProductSpace

abbrev b := FinitePotential.amplitude

def vOld (x : Point) : ℝ := (‖x‖^2-3)/2 - bareNewton x/100
abbrev vNew := FinitePotential.externalOscillatorUnits

def externalDensity (v : Point → ℝ) (u : Wave) (z : Config) : ℝ :=
  (v z.1+v z.2)*(u z)^2

def interactionDensity (u : Wave) (z : Config) : ℝ := (u z)^2/‖z.1-z.2‖

def kinetic {dom : Submodule ℝ Wave} (G : WeakGradient dom) (u : dom) : ℝ :=
  (∑ p : Fin 2, ∑ i : Fin 3, ∫ z, (G.component u p i z)^2)/2

def physicalEnergy {dom : Submodule ℝ Wave} (G : WeakGradient dom)
    (v : Point → ℝ) (s : UnitState dom) : ℝ :=
  kinetic G s.val + (∫ z, externalDensity v s.val.val z) +
    (∫ z, interactionDensity s.val.val z)/100

/-- The common oscillator form domain as a predicate on actual L² classes. -/
def inOscillatorDomain (u : Wave) : Prop :=
  Integrable (fun z : Config => (‖z.1‖^2+‖z.2‖^2)*(u z)^2) ∧
  ∃ derivative : Fin 2 → Fin 3 → Wave,
    ∀ (p : Fin 2) (i : Fin 3) (φ : Config → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, u z * fderiv ℝ φ z (axis p i)) = -(∫ z, derivative p i z * φ z)

/-- Both potentials and the repulsion are form-integrable on this same
linear subspace. The weak derivative data also enter the physical energies. -/
structure DomainData (dom : Submodule ℝ Wave) extends WeakGradient dom where
  fullDomain : ∀ u : Wave, u ∈ dom ↔ inOscillatorDomain u
  oldExternal : ∀ u : dom, Integrable (externalDensity vOld u.val)
  newExternal : ∀ u : dom, Integrable (externalDensity vNew u.val)
  pairIntegrable : ∀ u : dom, Integrable (interactionDensity u.val)
  positiveIntegrable : ∀ u : dom, Integrable (positiveDensity toWeakGradient u)

/-- A concrete kinetic bound using the attractive Hartree depth and the two
oscillator shifts. The Coulomb interaction contributes with positive sign. -/
theorem kinetic_le_old {dom : Submodule ℝ Wave} (G : DomainData dom) (u : UnitState dom)
    (newtonBound : ∀ z, |j z| ≤ 4) :
    kinetic G.toWeakGradient u.val ≤ physicalEnergy G.toWeakGradient vOld u+76/25 := by
  let Y := u.val.val
  have hi : Integrable (fun z => (Y z)^2) := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      using L2.integrable_inner (𝕜 := ℝ) Y Y
  have one : (∫ z, (Y z)^2) = 1 := by
    have h := L2.inner_def (𝕜 := ℝ) Y Y
    have hn : ‖Y‖=1 := u.property
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hn, one_pow] at h
    exact h.symm
  have point (z : Config) : (-76/25)*(Y z)^2 ≤ externalDensity vOld Y z := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have jmax := (abs_le.mp (newtonBound z)).2
    unfold j at jmax
    unfold vOld
    nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  have ext := integral_mono (hi.const_mul (-76/25)) (G.oldExternal u.val) point
  rw [integral_const_mul, one, mul_one] at ext
  have rep : 0 ≤ ∫ z, interactionDensity Y z := integral_nonneg (fun z => by
    unfold interactionDensity; positivity)
  change kinetic G.toWeakGradient u.val ≤ kinetic G.toWeakGradient u.val +
    (∫ z, externalDensity vOld Y z) + (∫ z, interactionDensity Y z)/100 + 76/25
  linarith

structure GaussianState (dom : Submodule ℝ Wave) where
  state : UnitState dom
  representative : ∀ᵐ z : Config ∂volume, state.val.val z =
    (Real.pi^(-(3:ℝ)/2))*Real.exp (-((‖z.1‖^2+‖z.2‖^2)/2))

private theorem multiplier_close (z : Config) : |multiplier z-1| ≤ 3*b := by
  obtain ⟨lo,hi⟩ := abs_le.mp (weight_window z)
  change -(5*b) ≤ multiplier z^2-1 at lo
  change multiplier z^2-1 ≤ 5*b at hi
  have b0 : 0 ≤ b := FinitePotential.amplitude_pos.le
  have bs : b ≤ 1/100 := amplitude_small
  have bm := mul_le_mul_of_nonneg_left bs b0
  have l : 1-3*b ≤ multiplier z := le_of_sq_le_sq (by nlinarith only [lo,bm,b0]) (multiplier_pos _).le
  have u : multiplier z ≤ 1+3*b := le_of_sq_le_sq (by nlinarith [sq_nonneg b]) (by linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem normalization_cost {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗ[ℝ] V) (u : UnitState V) (ε : ℝ) (raw : ‖T u.val-u.val‖ ≤ ε) :
    ‖((normalizedEquiv T) u).val-u.val‖ ≤ 2*ε := by
  let v := (normalizedEquiv T) u
  have npos : 0 < ‖T u.val‖ := by
    apply norm_pos_iff.mpr
    intro zero
    have uz := T.injective (zero.trans T.map_zero.symm)
    have un := u.property
    rw [uz,norm_zero] at un
    norm_num at un
  have reconstruct : ‖T u.val‖ • v.val = T u.val := by
    change ‖T u.val‖ • (‖T u.val‖⁻¹ • T u.val) = T u.val
    rw [smul_smul,mul_inv_cancel₀ npos.ne',one_smul]
  have dnorm : ‖v.val-T u.val‖ = |1-‖T u.val‖| := by
    rw [show v.val-T u.val=(1-‖T u.val‖) • v.val by rw [sub_smul,one_smul,reconstruct]]
    rw [norm_smul, v.property, mul_one, Real.norm_eq_abs]
  have bound := abs_norm_sub_norm_le (T u.val) u.val
  rw [u.property, abs_sub_comm] at bound
  have triangle : ‖v.val-u.val‖ ≤ ‖v.val-T u.val‖+‖T u.val-u.val‖ := by
    simpa only [dist_eq_norm] using dist_triangle v.val (T u.val) u.val
  change ‖v.val-u.val‖ ≤ 2*ε
  linarith only [triangle, dnorm, bound, raw]

/-- Multiplying by the concrete F and normalizing displaces any unit L²
state by at most 6b. This controls the physical new state as well as its pullback. -/
theorem normalized_multiplier_displacement {dom : Submodule ℝ Wave} (T : dom ≃ₗ[ℝ] dom)
    (mulRule : ∀ u : dom, ∀ᵐ z : Config ∂volume, (T u).val z=multiplier z*u.val z)
    (u : UnitState dom) : ‖((normalizedEquiv T) u).val-u.val‖ ≤ 6*b := by
  have hu : ‖u.val.val‖=1 := u.property
  have raw : ‖(T u.val).val-u.val.val‖ ≤ 3*b*‖u.val.val‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (T u.val).val u.val.val, mulRule u.val] with z hz ht
    change |((T u.val).val-u.val.val : Wave) z| ≤ 3*b*|u.val.val z|
    rw [hz]
    change |(T u.val).val z-u.val.val z| ≤ _
    rw [ht, ← sub_one_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (multiplier_close _) (abs_nonneg _)
  rw [hu,mul_one] at raw
  exact (normalization_cost T u (3*b) raw).trans_eq (by ring)

theorem overlap_nonneg {dom : Submodule ℝ Wave} (T : dom ≃ₗ[ℝ] dom)
    (ψ Φ : UnitState dom)
    (mulRule : ∀ u : dom, ∀ᵐ z : Config ∂volume, (T u).val z=multiplier z*u.val z)
    (ψpos : ∀ᵐ z : Config ∂volume, 0 ≤ ψ.val.val z)
    (Φpos : ∀ᵐ z : Config ∂volume, 0 ≤ Φ.val.val z) :
    0 ≤ ⟪ψ.val,((normalizedEquiv T).symm Φ).val⟫_ℝ := by
  let raw := T.symm Φ.val
  have physical : T raw = Φ.val := T.apply_symm_apply Φ.val
  have mapped := mulRule raw
  rw [physical] at mapped
  have rawpos : ∀ᵐ z : Config ∂volume, 0 ≤ raw.val z := by
    filter_upwards [mapped, Φpos] with z hz hz0
    rw [hz] at hz0
    exact nonneg_of_mul_nonneg_right hz0 (multiplier_pos z)
  have yp : ∀ᵐ z : Config ∂volume, 0 ≤ ((normalizedEquiv T).symm Φ).val.val z := by
    change ∀ᵐ z : Config ∂volume, 0 ≤ (‖raw‖⁻¹ • raw.val : Wave) z
    filter_upwards [Lp.coeFn_smul (‖raw‖⁻¹ : ℝ) raw.val, rawpos] with z hz hpos
    rw [hz]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hpos
  change 0 ≤ ⟪ψ.val.val,((normalizedEquiv T).symm Φ).val.val⟫_ℝ
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [ψpos, yp] with z h0 h1
  rw [Real.inner_apply]
  exact mul_nonneg h0 h1

#print axioms kinetic_le_old
#print axioms normalized_multiplier_displacement
#print axioms overlap_nonneg
end FixedRadialSectionFive
