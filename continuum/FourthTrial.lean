import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact arithmetic for two Gaussian double excitations in the unmodified
two-electron trap, using only the ordinary one-electron oscillator gap. -/
namespace FourthTrial

/-- A coefficient and the powers of t (longitudinal), v (transverse) and
q (relative radius squared) in the radial-coordinate polynomial. -/
abbrev Term := ℤ × ℕ × ℕ × ℕ
abbrev Poly := List Term
def ground : Poly := [(1,0,0,0)]
def quadratic : Poly := [(1,1,0,0),(1,0,1,0),(-1,0,0,1)]
def quartic : Poly := [(7,0,0,2),(-1,2,0,0),(-2,1,1,0),(-1,0,2,0),
  (-6,1,0,1),(-2,0,1,1),(20,1,0,0),(20,0,1,0),(-60,0,0,1),(60,0,0,0)]

def oddMoment : ℕ → ℕ
  | 0 => 1
  | n+1 => (2*n+1)*oddMoment n

def ev (coulomb : Bool) (i j k : ℕ) : ℕ :=
  oddMoment i * 2^j * j.factorial * (if coulomb then 2^k*k.factorial else oddMoment (k+1))

def moment (coulomb : Bool) (p q : Poly) : ℤ :=
  (p.map (fun (a,i,j,k) => (q.map (fun (b,l,m,n) =>
    a*b*(ev coulomb (i+l) (j+m) (k+n) : ℤ))).sum)).sum

def matrix (c : Bool) := [ground,quadratic,quartic].map
  (fun a => [ground,quadratic,quartic].map (moment c a))

theorem gram_matrix : matrix false = [[1,0,0],[0,12,0],[0,0,6720]] := by decide
theorem coulomb_matrix : matrix true = [[1,1,21],[1,11,97],[21,97,4985]] := by decide

/-- e and s are the shifted one- and two-electron energies divided by λ².
The trial is the Gaussian times 1 − λ(P₂/30 + P₄/1600). -/
theorem removal_from_ordinary_gap (D σ x z e s : ℝ)
    (mass : x^2 ≤ 1) (variance : σ^2 ≤ 1/33) (Dlo : 159/200 ≤ D)
    (one : 49/50*z^2-2*σ*x*z ≤ e)
    (trial : (1+(383/24000)/10000)*s ≤
        223/6000-2*(223/4800)*D + D*((83917/4608000)+(383/24000))/100) :
    1/200 < e-s := by
  have h := sq_nonneg ((49/50:ℝ)*z-σ*x)
  have hx := mul_nonneg (sq_nonneg σ) (sub_nonneg.mpr mass)
  have low : -(50/(49*33):ℝ) ≤ e := by nlinarith only [one,h,hx,variance]
  have hi : s ≤ -(9/250:ℝ) := by linarith only [trial,Dlo]
  linarith only [low,hi]

#print axioms gram_matrix
#print axioms coulomb_matrix
#print axioms removal_from_ordinary_gap
end FourthTrial
