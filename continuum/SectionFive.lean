import UnitVariational
import PullbackIntegrals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Section 5 estimates on the unit sphere of a single linear form domain.
The oscillator comparison is assumed only on its own Gaussian complement.
Inputs concerning the physical measures and differential operators are explicit. -/
noncomputable section
namespace SectionFive
open MeasureTheory Set
open scoped InnerProductSpace

structure Measures (D X : Type*) [Norm D] [MeasurableSpace X] where
  mass : UnitState D → Measure X
  positiveEnergy : UnitState D → Measure X
  probability : ∀ u, IsProbabilityMeasure (mass u)
  finiteEnergy : ∀ u, IsFiniteMeasure (positiveEnergy u)

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]

def pulled (T : D ≃ₗ[ℝ] D) (u : UnitState D) : UnitState D := (normalizedEquiv T).symm u

structure Stability (q : Form D) (qf : UnitState D → ℝ) (T : D ≃ₗ[ℝ] D) (ψ Φ : UnitState D)
    (A : UnitState D → ℝ) (b : ℝ) : Prop where
  oldMinimumNonpos : energy q ψ ≤ 0
  oldPositiveBound : A ψ ≤ 1/25
  pulledPositiveBound : A (pulled T Φ) ≤ 11/100
  newEnergyLower : energy q ψ-21/5*b ≤ qf Φ
  newEnergyUpper : qf Φ ≤ energy q ψ+14/5*b
  pulledExcess : 0 ≤ energy q (pulled T Φ)-energy q ψ ∧
    energy q (pulled T Φ)-energy q ψ ≤ 7*b
  distanceUpToSign : ‖(pulled T Φ).val-ψ.val‖ ≤ 4*Real.sqrt b ∨
    ‖(pulled T Φ).val+ψ.val‖ ≤ 4*Real.sqrt b
  orientedDistance : 0 ≤ ⟪ψ.val,(pulled T Φ).val⟫_ℝ →
    ‖(pulled T Φ).val-ψ.val‖ ≤ 4*Real.sqrt b

private theorem distance_of_overlap (ψ y : UnitState D) (b : ℝ) (hb : 0 ≤ b)
    (bound : 24/25*(1-⟪ψ.val,y.val⟫_ℝ^2) ≤ 7*b) :
    (0 ≤ ⟪ψ.val,y.val⟫_ℝ → ‖y.val-ψ.val‖ ≤ 4*Real.sqrt b) ∧
    (⟪ψ.val,y.val⟫_ℝ ≤ 0 → ‖y.val+ψ.val‖ ≤ 4*Real.sqrt b) := by
  have absolute := abs_real_inner_le_norm ψ.val y.val
  rw [ψ.property, y.property, mul_one] at absolute
  obtain ⟨lo, hi⟩ := abs_le.mp absolute
  have sq := Real.sq_sqrt hb
  have swap : ⟪y.val,ψ.val⟫_ℝ = ⟪ψ.val,y.val⟫_ℝ := real_inner_comm _ _
  constructor
  · intro pos
    have hprod := mul_nonneg pos (sub_nonneg.mpr hi)
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    rw [norm_sub_sq_real, swap, ψ.property, y.property]
    nlinarith
  · intro neg
    have hprod := mul_nonpos_of_nonpos_of_nonneg neg
      (show 0 ≤ ⟪ψ.val,y.val⟫_ℝ+1 by linarith)
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    rw [norm_add_sq_real, swap, ψ.property, y.property]
    nlinarith

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace X]

/-- The two minimizers are tested against every unit vector of dom. The new
energy is evaluated at the *physical* trial T u /
‖T u‖. No energy-error, state-distance, interacting gap, or minimizer
stationarity assumption occurs. The final overlap implication chooses a sign. -/
theorem variational_stability_on_domain (dom : Submodule ℝ H)
    (q osc : Form dom) (qf : UnitState dom → ℝ) (T : dom ≃ₗ[ℝ] dom) (f : Fields X) (M : Measures dom X)
    (gaussian ψ Φ : UnitState dom) (b direct : ℝ) (hb : 0 ≤ b) (hs : b ≤ 1/100)
    (hw : ∀ x, |f.weight x-1| ≤ 5*b) (hj : ∀ x, |f.hartree x| ≤ 4)
    (hchange : ∀ x, |f.dressedHartree x-f.hartree x| ≤ 24*b)
    (baseRepresentation : ∀ u, energy q u=baseRayleigh f (M.mass u) (M.positiveEnergy u))
    (newRepresentation : ∀ u, qf ((normalizedEquiv T) u)=
      newRayleigh f (M.mass u) (M.positiveEnergy u))
    (oscillatorPart : ∀ u, energy osc u ≤ (M.positiveEnergy u).real univ)
    (oscillatorGap : ∀ z : dom, ⟪gaussian.val,z⟫_ℝ = 0 → ‖z‖^2 ≤ osc z z)
    (gaussianPositive : 100*(M.positiveEnergy gaussian).real univ=direct)
    (gaussianHartree : (∫ x, f.hartree x ∂(M.mass gaussian))=2*direct)
    (oldMin : Minimizes (energy q) ψ) (newMin : Minimizes qf Φ) :
    Stability q qf T ψ Φ (fun u => (M.positiveEnergy u).real univ) b := by
  let A := fun u : UnitState dom => (M.positiveEnergy u).real univ
  let y := pulled T Φ
  have unpull : (normalizedEquiv T) y = Φ := (normalizedEquiv T).apply_symm_apply Φ
  have floor (u : UnitState dom) : A u-1/25 ≤ energy q u := by
    let := M.probability u
    rw [baseRepresentation]
    exact baseline_floor f _ _ hj
  have perturb (u : UnitState dom) :
      |qf ((normalizedEquiv T) u)-energy q u| ≤ 20*b*A u+2*b := by
    let := M.probability u
    let := M.finiteEnergy u
    rw [newRepresentation, baseRepresentation]
    exact rayleigh_difference f _ _ b hb hs hw hj hchange
  have gaussNonpos : energy q gaussian ≤ 0 := by
    rw [baseRepresentation]
    unfold baseRayleigh
    rw [gaussianHartree]
    have hn : 0 ≤ (M.positiveEnergy gaussian).real univ := measureReal_nonneg
    linarith
  have enon : energy q ψ ≤ 0 := (oldMin gaussian).trans gaussNonpos
  have aψ : A ψ ≤ 1/25 := by linarith [floor ψ]
  have varψ := (abs_le.mp (perturb ψ)).2
  have trial := newMin ((normalizedEquiv T) ψ)
  have upper : qf Φ ≤ energy q ψ+14/5*b := by
    nlinarith only [varψ, trial, mul_le_mul_of_nonneg_left aψ hb]
  have vary := abs_le.mp (perturb y)
  rw [unpull] at vary
  have ya : 0 ≤ A y := measureReal_nonneg
  have ay : A y ≤ 11/100 := by
    nlinarith only [vary.1, floor y, upper, enon, hs,
      mul_le_mul_of_nonneg_right hs ya]
  have prod := mul_le_mul_of_nonneg_left ay hb
  have ecost : energy q y-energy q ψ ≤ 7*b := by
    nlinarith only [vary.1, upper, prod]
  have elower : energy q ψ-21/5*b ≤ qf Φ := by
    nlinarith only [oldMin y, vary.1, prod]
  let p : Form dom := q-osc+(1/25:ℝ) • innerₗ dom
  have diag (x : dom) : p x x=q x x-osc x x+1/25*‖x‖^2 := by
    simp [p, smul_eq_mul]
  have comp (z : dom) (orth : ⟪gaussian.val,z⟫_ℝ=0) : 24/25*‖z‖^2 ≤ q z z := by
    have hp := form_nonneg_of_unit p (fun s => by
      rw [diag, s.property]
      have h0 := oscillatorPart s
      change osc s.val s.val ≤ A s at h0
      have h1 := floor s
      change A s-1/25 ≤ q s.val s.val at h1
      linarith) z
    rw [diag] at hp
    linarith [oscillatorGap z orth]
  have gap := gap_from_comparison q ψ gaussian.val (24/25) (by norm_num) oldMin enon comp y
  obtain ⟨hplus,hminus⟩ := distance_of_overlap ψ y b hb (gap.trans ecost)
  exact ⟨enon, aψ, ay, elower, upper, ⟨sub_nonneg.mpr (oldMin y), ecost⟩,
    (le_total 0 ⟪ψ.val,y.val⟫_ℝ).imp hplus hminus, hplus⟩

#check variational_stability_on_domain
#print axioms variational_stability_on_domain
end SectionFive
