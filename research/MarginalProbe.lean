import FiniteKinetic
import RadialProbe
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

def densitySine (x : Position) : ℝ := envelope ‖x‖ * Real.sin (frequency*‖x‖)
def pairProbe (h : Position → ℝ) (Y : Position × Position → ℝ) : ℝ :=
  (∫ z, h z.1^2*Y z^2) + ∫ z, h z.2^2*Y z^2

def firstMarginal (Y : Position × Position → ℝ) (x : Position) := ∫ y, Y (x,y)^2

theorem fubini_weighted_marginal (h : Position → ℝ) (Y : Position × Position → ℝ)
    (hi : Integrable (fun z : Position × Position => h z.1^2*Y z^2)) :
    (∫ z : Position × Position, h z.1^2*Y z^2) = ∫ x, h x^2*firstMarginal Y x := by
  rw [integral_prod (fun z : Position × Position => h z.1^2*Y z^2) hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => integral_const_mul _ _

theorem pairProbe_marginal (h : Position → ℝ) (Y : Position × Position → ℝ)
    (hi : Integrable (fun z : Position × Position => h z.1^2*Y z^2))
    (symmetry : ∀ᵐ z : Position × Position, Y z.swap^2 = Y z^2) :
    pairProbe h Y = 2 * ∫ x, h x^2*firstMarginal Y x := by
  have hswap : (∫ z : Position × Position, h z.2^2*Y z^2) =
      ∫ z : Position × Position, h z.1^2*Y z^2 := by
    calc
      _ = ∫ z : Position × Position, h z.2^2*Y z.swap^2 := by
        apply integral_congr_ae
        filter_upwards [symmetry] with z hz using congrArg (fun a => h z.2^2*a) hz.symm
      _ = _ := integral_prod_swap (fun z : Position × Position => h z.1^2*Y z^2)
  unfold pairProbe
  rw [hswap,fubini_weighted_marginal h Y hi]
  ring

theorem marginal_integrable (h : Position → ℝ) (Y : Position × Position → ℝ)
    (hi : Integrable (fun z : Position × Position => h z.1^2*Y z^2)) :
    Integrable (fun x => h x^2*firstMarginal Y x) := by
  have hy := hi.integral_prod_left
  apply hy.congr
  exact ae_of_all _ fun x => integral_const_mul _ _

/-- Evaluate both two-particle probe integrals through the first marginal.
The Gaussian-shell theorem gives their strict positive finite margin. -/
theorem actual_pair_probe_margin (U R : Position × Position → ℝ) (s : ℝ → ℝ)
    (uI : Integrable (fun z : Position × Position => densitySine z.1^2*U z^2))
    (rI : Integrable (fun z : Position × Position => densitySine z.1^2*R z^2))
    (uSym : ∀ᵐ z : Position × Position, U z.swap^2 = U z^2)
    (rSym : ∀ᵐ z : Position × Position, R z.swap^2 = R z^2)
    (uMarg : ∀ᵐ x : Position, firstMarginal U x = RadialProbe.gaussianSq ‖x‖)
    (rMarg : ∀ᵐ x : Position, firstMarginal R x = s ‖x‖^2)
    (rInt : Integrable (RadialProbe.integrand s))
    (tail : ∀ᵐ r : ℝ, radius ≤ r → r ≤ radius+3 → s r^2 ≤ RadialProbe.gaussianSq r/4) :
    margin ≤ pairProbe densitySine U-pairProbe densitySine R := by
  rw [pairProbe_marginal _ _ uI uSym,pairProbe_marginal _ _ rI rSym,← mul_sub,
      ← integral_sub (marginal_integrable _ _ uI) (marginal_integrable _ _ rI), ← integral_const_mul]
  apply (RadialProbe.spatial_margin s rInt tail).trans_eq
  apply integral_congr_ae
  filter_upwards [uMarg,rMarg] with x hu hr
  rw [hu,hr]
  unfold RadialProbe.spatialIntegrand densitySine
  ring

#print axioms pairProbe_marginal
#print axioms actual_pair_probe_margin
end
end HFKinetic
