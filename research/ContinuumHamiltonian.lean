import FinitePotential
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-! The two-electron variational problem with all complex spin orbitals on
Euclidean three-space. Gradients are specified in the distributional sense.
Counting measure over spin indices is implemented by finite sums. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumHamiltonian

abbrev X := FinitePotential.Position
abbrev Config := X × X
abbrev Spin := Fin 2
abbrev Spinor := Spin → X → ℂ
abbrev Wave := Spin → Spin → Config → ℂ

def axis (p : Fin 2) (j : Fin 3) : Config :=
  if p = 0 then (EuclideanSpace.single j 1, 0) else (0, EuclideanSpace.single j 1)

def IsWeakPartial (ψ dψ : Config → ℂ) (v : Config) : Prop :=
  ∀ φ : Config → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ z, ψ z * ((fderiv ℝ φ z v : ℝ) : ℂ)) = -(∫ z, dψ z * (φ z : ℂ))

structure State where
  wave : Wave
  grad : Spin → Spin → Fin 2 → Fin 3 → Config → ℂ
  squareIntegrable : ∀ a b, MemLp (wave a b) 2 volume
  gradSquareIntegrable : ∀ a b p j, MemLp (grad a b p j) 2 volume
  weakGradient : ∀ a b p j, IsWeakPartial (wave a b) (grad a b p j) (axis p j)

def kinetic (s : State) : ℝ :=
  (∑ a : Spin, ∑ b : Spin, ∑ p : Fin 2, ∑ j : Fin 3, ∫ z, ‖s.grad a b p j z‖^2)/2

def mass (s : State) : ℝ := ∑ a : Spin, ∑ b : Spin, ∫ z, ‖s.wave a b z‖^2

def coulomb (z : Config) : ℝ := ‖z.1-z.2‖⁻¹

def external (v : X → ℝ) (z : Config) : ℝ := v z.1 + v z.2

def formEnergy (v : X → ℝ) (s : State) : ℝ :=
  kinetic s + ∑ a : Spin, ∑ b : Spin,
    ∫ z, (external v z + coulomb z) * ‖s.wave a b z‖^2

def Admissible (v : X → ℝ) (s : State) : Prop :=
  mass s = 1 ∧
  (∀ a b, ∀ᵐ z ∂volume, s.wave a b z = -s.wave b a (z.2,z.1)) ∧
  (∀ a b, Integrable (fun z => external v z * ‖s.wave a b z‖^2)) ∧
  (∀ a b, Integrable (fun z => coulomb z * ‖s.wave a b z‖^2))

def determinant (u v : Spinor) (a b : Spin) (z : Config) : ℂ :=
  (u a z.1 * v b z.2 - v a z.1 * u b z.2) / (Real.sqrt 2 : ℂ)

def orbitalInner (u v : Spinor) : ℂ :=
  ∑ a : Spin, ∫ x, star (u a x) * v a x

def IsSlater (s : State) : Prop :=
  ∃ u v : Spinor, (∀ a, MemLp (u a) 2 volume ∧ MemLp (v a) 2 volume) ∧
    orbitalInner u u = 1 ∧ orbitalInner v v = 1 ∧ orbitalInner u v = 0 ∧
    ∀ a b, s.wave a b =ᵐ[volume] determinant u v a b

def ExactMinimum (v : X → ℝ) (s : State) : Prop :=
  Admissible v s ∧ ∀ w, Admissible v w → formEnergy v s ≤ formEnergy v w

def HFMinimum (v : X → ℝ) (s : State) : Prop :=
  (Admissible v s ∧ IsSlater s) ∧
    ∀ w, Admissible v w → IsSlater w → formEnergy v s ≤ formEnergy v w

/-- Same spatial orbital for both spins, one spin up and one down. -/
def IsClosedShell (s : State) (u : X → ℂ) : Prop :=
  ∀ a b, s.wave a b =ᵐ[volume] determinant
    (fun t x => if t = 0 then u x else 0)
    (fun t x => if t = 1 then u x else 0) a b

def SameRay (u v : State) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ a b, u.wave a b =ᵐ[volume] fun x => c * v.wave a b x

/-- Target proposition for the fixed field and the kinetic integrals of both
optimizers. Each globally minimizing determinant lies on the same ray. -/
def FixedRadialReversal : Prop :=
  ∃ e h : State, ExactMinimum FinitePotential.physicalExternal e ∧
    HFMinimum FinitePotential.physicalExternal h ∧
    (∀ w, HFMinimum FinitePotential.physicalExternal w → SameRay w h) ∧
    (∃ U : ℝ → ℝ, IsClosedShell h (fun x => (U ‖x‖ : ℂ))) ∧ kinetic e < kinetic h

theorem determinant_exchange (u v : Spinor) (a b : Spin) (x y : X) :
    determinant u v a b (x,y) = -determinant u v b a (y,x) := by
  unfold determinant
  simp only
  ring

theorem kinetic_nonneg (s : State) : 0 ≤ kinetic s := by
  unfold kinetic
  apply div_nonneg _ (by norm_num)
  repeat' apply Finset.sum_nonneg; intro _ _
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem total_energy_order {v : X → ℝ} {e h : State}
    (he : ExactMinimum v e) (hh : HFMinimum v h) : formEnergy v e ≤ formEnergy v h :=
  he.2 h hh.1.1
#print axioms determinant_exchange
#print axioms kinetic_nonneg
#print axioms total_energy_order
end ContinuumHamiltonian
