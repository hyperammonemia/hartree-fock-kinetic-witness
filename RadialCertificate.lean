import Std

/-!
Scalar part of a continuum kinetic-energy certificate. This file quantifies
over ordered fields. The hypotheses on energies, angle coordinates and
operator estimates have their analytic derivations in continuum-witness.md.
-/
namespace RadialCertificate

open Lean.Grind
variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K]
  [Std.LawfulOrderLT K] [OrderedRing K]

/-- The Gaussian integrals give D²π=2, Var(J)=2/3−D², and
a²=D²/12, where a is the transition matrix element to the three p pairs. -/
theorem gaussian_moment_bounds (piVal d variance a : K)
    (archimedes : 7*piVal ≤ 22) (momentD : d*d*piVal=2)
    (momentVar : 3*variance=2-3*d*d) (a0 : 0 ≤ a)
    (momentA : 12*a*a=d*d) : 32*variance ≤ 1 ∧ 11 ≤ 50*a := by
  have hs := OrderedRing.mul_nonneg
    (show 0 ≤ d*d by have := OrderedRing.sq_nonneg (a := d); grind)
    (show 0 ≤ 22-7*piVal by grind)
  constructor
  · grind
  · by_cases h : 11 ≤ 50*a
    · exact h
    · have bad := OrderedRing.mul_pos (show 0 < 11-50*a by grind)
          (show 0 < 11+50*a by grind)
      grind

/-- Completing the square in the complement of the radial oscillator
ground state. Here z is the complementary norm divided by λ. -/
theorem one_electron_floor (x z sigma e : K) (normalized : x*x ≤ 1)
    (rayleigh : 99*z*z-100*sigma*x*z ≤ 50*e) :
    -(50*(sigma*sigma)) ≤ 99*e := by
  have s := OrderedRing.sq_nonneg (a := 99*z-50*sigma*x)
  have rem := OrderedRing.mul_nonneg
    (show 0 ≤ sigma*sigma by have := OrderedRing.sq_nonneg (a := sigma); grind)
    (show 0 ≤ 1-x*x by grind)
  grind

/-- A variance bound and a two-dimensional Rayleigh quotient. The energies
e and t have first been shifted by λD and divided by λ², with λ = 1/100.
The conclusion gives E₁ − E₂ > 1/2,000,000 in the oscillator units. -/
theorem ion_gap (e t variance coupling : K)
    (moment : 32*variance ≤ 1)
    (transition : 11 ≤ 50*coupling)
    (oneElectron : -(50*variance) ≤ 99*e)
    (twoElectron : 1000001*t ≤ 20500-200000*coupling) :
    1 < 200*(e-t) := by
  grind

theorem ion_gap_from_trial_states (piVal d sigma a x z diag e t : K)
    (archimedes : 7*piVal ≤ 22) (momentD : d*d*piVal=2)
    (momentVar : 3*(sigma*sigma)=2-3*d*d) (a0 : 0 ≤ a)
    (momentA : 12*a*a=d*d) (normalized : x*x ≤ 1)
    (radial : 99*z*z-100*sigma*x*z ≤ 50*e)
    (hardy : diag ≤ 5)
    (pairTrial : 1000001*t ≤ 20000+100*diag-200000*a) :
    1 < 200*(e-t) := by
  obtain ⟨v, u⟩ := gaussian_moment_bounds piVal d (sigma*sigma) a
    archimedes momentD momentVar a0 momentA
  apply ion_gap e t (sigma*sigma) a v u (one_electron_floor x z sigma e normalized radial)
  grind

/-- a and b are the squared sines of the two principal angles between
the occupied planes. d is the norm of the two-particle excitation. -/
theorem double_excitation (a b d : K)
    (a0 : 0 ≤ a) (a1 : a ≤ 1) (b0 : 0 ≤ b) (b1 : b ≤ 1)
    (angles : d*d=a*b) :
    d ≤ 1-(1-a)*(1-b) := by
  have hA := OrderedRing.mul_nonneg a0 (show 0 ≤ 1-b by grind)
  have hB := OrderedRing.mul_nonneg b0 (show 0 ≤ 1-a by grind)
  let loss := 1-(1-a)*(1-b)
  have ad : a ≤ loss := by dsimp [loss]; grind
  have bd : b ≤ loss := by dsimp [loss]; grind
  have ld : 0 ≤ loss := by grind
  have x := OrderedRing.mul_nonneg b0 (show 0 ≤ loss-a by grind)
  have y := OrderedRing.mul_nonneg ld (show 0 ≤ loss-b by grind)
  have sq : d*d ≤ loss*loss := by grind
  change d ≤ loss
  by_cases h : d ≤ loss
  · exact h
  · have pos := OrderedRing.mul_pos (show 0 < d-loss by grind)
        (show 0 < d+loss by grind)
    grind

/-- With λ=1/100 the excitation gap ≥1/2, the diagonal remainder ≥−4,
and the norm of the reference residual ≤8 give a strict global HF bound. -/
theorem global_hf_margin (loss doubleAmp energyDifference : K)
    (amp : doubleAmp ≤ loss)
    (formBound : 50*loss-4*loss-16*doubleAmp ≤ 100*energyDifference) :
    3*loss ≤ 10*energyDifference := by
  grind

/-- The pullback of the exact minimizer lies close to the original ground
state. Both have norm one and positive overlap. -/
theorem ground_state_distance (b dist overlap energyError : K)
    (b0 : 0 ≤ b) (o0 : 0 ≤ overlap) (o1 : overlap ≤ 1)
    (distance : dist*dist=2*(1-overlap))
    (spectralGap : 96*(1-overlap*overlap) ≤ 100*energyError)
    (variation : energyError ≤ 8*b) : dist*dist ≤ 25*b := by
  have h := OrderedRing.mul_nonneg o0 (show 0 ≤ 1-overlap by grind)
  grind

/-- Compare the two scaled kinetic energies at the specified finite
amplitude b=(m/1000)². rootB is its positive square root. -/
theorem finite_reversal (m rootB b scale hfT exactT hfProbe trueProbe pulledProbe : K)
    (m0 : 0 < m) (m1 : m ≤ 1)
    (amplitude : 1000*rootB=m) (square : b=rootB*rootB)
    (positiveScale : 0 < scale)
    (tail : m ≤ hfProbe-trueProbe)
    (stateError : pulledProbe-trueProbe ≤ 20*rootB)
    (hfRemainder : hfProbe-scale*hfT ≤ 100*b)
    (exactRemainder : scale*exactT-pulledProbe ≤ 100*b) : exactT < hfT := by
  have r0 : 0 ≤ rootB := by grind
  have r1 : rootB ≤ 1 := by grind
  have bound := OrderedRing.mul_nonneg r0 (show 0 ≤ 1-rootB by grind)
  by_cases h : exactT < hfT
  · exact h
  · have bad := OrderedRing.mul_nonneg (show 0 ≤ scale by grind)
        (show 0 ≤ exactT-hfT by grind)
    grind

#print axioms gaussian_moment_bounds
#print axioms one_electron_floor
#print axioms ion_gap
#print axioms ion_gap_from_trial_states
#print axioms double_excitation
#print axioms global_hf_margin
#print axioms ground_state_distance
#print axioms finite_reversal
end RadialCertificate
