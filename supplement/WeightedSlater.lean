import Std

namespace WeightedSlater
open Lean.Grind

/-- The unnormalized two-spinor Slater determinant at two configurations. A
configuration may include both position and a spin index. -/
def wedgePair {X R : Type} [CommRing R] (u v : X → R) (x y : X) : R :=
  u x * v y - v x * u y

/-- A common one-body multiplier acts on the determinant by its product at
the two particle coordinates. Normalizing both sides preserves this identity. -/
theorem multiply_pair {X R : Type} [CommRing R] (w u v : X → R) (x y : X) :
    wedgePair (fun z => w z * u z) (fun z => w z * v z) x y =
      (w x * w y) * wedgePair u v x y := by
  unfold wedgePair
  grind

section Stability
variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

/-- In the weighted projector estimate, q is the squared upper/lower weight
ratio. Hardy plus Young yield the input exchange bound. The remaining inputs
are the Fock spectral-gap and kinetic-form bounds. -/
theorem exchange_bound (d q e A B K X : R)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (he : 0 ≤ e)
    (gap : d*B ≤ 2*A) (gradient : K ≤ 2*A+2*e*B)
    (hardyYoung : X ≤ q*(B+K)) :
    d*X ≤ 2*q*(d+1+2*e)*A := by
  have h1 := OrderedRing.mul_nonneg hd (show 0 ≤ q*(B+K)-X by grind)
  have h2 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hd hq)
    (show 0 ≤ 2*A+2*e*B-K by grind)
  have h3 := OrderedRing.mul_nonneg
    (OrderedRing.mul_nonneg hq (show 0 ≤ 1+2*e by grind))
    (show 0 ≤ 2*A-d*B by grind)
  grind

/-- A single coupling threshold gives a strict energy penalty proportional
to squared Hilbert-Schmidt distance, for every admissible trial projector.
The continuum trace identities and Hardy inequality are analytic inputs. -/
theorem energy_margin (g d q e A B K X energyDiff : R)
    (hd : 0 < d) (hq : 0 ≤ q) (he : 0 ≤ e) (hg : 0 ≤ g) (hA : 0 ≤ A)
    (gap : d*B ≤ 2*A) (gradient : K ≤ 2*A+2*e*B)
    (hardyYoung : X ≤ q*(B+K))
    (expansion : 2*A-g*X ≤ 2*energyDiff)
    (weakCoupling : 2*g*q*(d+1+2*e) ≤ d) :
    A ≤ 2*energyDiff ∧ d*B ≤ 4*energyDiff := by
  have hd0 : 0 ≤ d := by grind
  have hx := exchange_bound d q e A B K X hd0 hq he gap gradient hardyYoung
  have h1 := OrderedRing.mul_nonneg hg (show 0 ≤ 2*q*(d+1+2*e)*A-d*X by grind)
  have h2 := OrderedRing.mul_nonneg hA (show 0 ≤ d-2*g*q*(d+1+2*e) by grind)
  have h3 := OrderedRing.mul_nonneg hd0 (show 0 ≤ 2*energyDiff-(2*A-g*X) by grind)
  have margin : A ≤ 2*energyDiff := by
    by_cases ok : A ≤ 2*energyDiff
    · exact ok
    · have bad := OrderedRing.mul_pos hd (show 0 < A-2*energyDiff by grind)
      grind
  exact ⟨margin, by grind⟩
end Stability

#print axioms multiply_pair
#print axioms exchange_bound
#print axioms energy_margin
end WeightedSlater
