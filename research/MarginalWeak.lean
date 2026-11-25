import FiberKato
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Regularized marginal comparison as integrals on Euclidean three-space. -/
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace HFExterior

abbrev MarginalPosition := EuclideanSpace ℝ (Fin 3)
abbrev PhysicalFiber := Lp ℝ 2 (volume : Measure MarginalPosition)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem physical_fiber_mass (u : PhysicalFiber) : ‖u‖^2 = ∫ y, (u y)^2 := by
  rw [← real_inner_self_eq_norm_sq u, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

def waveFiber (ψ : MarginalPosition × MarginalPosition → ℝ) (x : MarginalPosition) :
    PhysicalFiber := by
  classical
  exact if h : MemLp (fun y => ψ (x,y)) 2 volume then h.toLp _ else 0

theorem waveFiber_rep {ψ : MarginalPosition × MarginalPosition → ℝ}
    (hψ : MemLp ψ 2 (volume.prod volume)) :
    ∀ᵐ x, (waveFiber ψ x : MarginalPosition → ℝ) =ᵐ[volume] fun y => ψ (x,y) := by
  classical
  filter_upwards [hψ.aestronglyMeasurable.prodMk_left, hψ.integrable_sq.prod_right_ae] with x hm hi
  have hx := (memLp_two_iff_integrable_sq hm).mpr hi
  simp only [waveFiber, dif_pos hx]
  exact hx.coeFn_toLp

theorem waveFiber_marginal {ψ : MarginalPosition × MarginalPosition → ℝ}
    (hψ : MemLp ψ 2 (volume.prod volume)) :
    ∀ᵐ x, ‖waveFiber ψ x‖^2 = ∫ y, ψ (x,y)^2 := by
  filter_upwards [waveFiber_rep hψ] with x hx
  rw [physical_fiber_mass]
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]

theorem waveFiber_total_mass {ψ : MarginalPosition × MarginalPosition → ℝ}
    (hψ : MemLp ψ 2 (volume.prod volume)) :
    (∫ x, ‖waveFiber ψ x‖^2) = ∫ z, ψ z^2 ∂volume.prod volume :=
  (integral_congr_ae (waveFiber_marginal hψ)).trans (integral_prod _ hψ.integrable_sq).symm

theorem marginal_integral_of_representative {ψ : MarginalPosition × MarginalPosition → ℝ}
    (hψ : MemLp ψ 2 (volume.prod volume)) {U : MarginalPosition → PhysicalFiber}
    (hU : U =ᵐ[volume] waveFiber ψ) (M : MarginalPosition → ℝ) :
    (∫ x, M x*‖U x‖) = ∫ x, M x*Real.sqrt (∫ y, ψ (x,y)^2) := by
  apply integral_congr_ae
  filter_upwards [hU, waveFiber_marginal hψ] with x hx hm
  rw [hx, ← hm, Real.sqrt_sq (norm_nonneg _)]

def coulombFiber (x : MarginalPosition) (u : PhysicalFiber) : ℝ :=
  ∫ y, (u y)^2 / ‖x-y‖

theorem coulombFiber_nonneg (x : MarginalPosition) (u : PhysicalFiber) : 0 ≤ coulombFiber x u :=
  integral_nonneg (fun y => div_nonneg (sq_nonneg _) (norm_nonneg _))

theorem coulombFiber_congr_off_diagonal (x : MarginalPosition) (u : PhysicalFiber)
    (w : MarginalPosition → ℝ) (hw : ∀ y, y ≠ x → w y = ‖x-y‖⁻¹) :
    (∫ y, w y*(u y)^2) = coulombFiber x u := by
  apply integral_congr_ae
  filter_upwards [(volume : Measure MarginalPosition).ae_ne x] with y hy
  rw [hw y hy, div_eq_mul_inv, mul_comm]

def oneBodyFiber (V : MarginalPosition → ℝ) (u : PhysicalFiber)
    (du : Fin 3 → MarginalPosition → ℝ) : ℝ :=
  ∫ y, (∑ j : Fin 3, (du j y)^2)/2 + V y * (u y)^2

theorem residual_fiber_lower (V : MarginalPosition → ℝ) (e₁ : ℝ)
    (domain : PhysicalFiber → (Fin 3 → MarginalPosition → ℝ) → Prop)
    (hbound : ∀ u du, domain u du → e₁ * (∫ y, (u y)^2) ≤ oneBodyFiber V u du)
    (U : MarginalPosition → PhysicalFiber) (du : MarginalPosition → Fin 3 → MarginalPosition → ℝ)
    (hd : ∀ᵐ x, domain (U x) (du x)) :
    ∀ᵐ x, e₁ * ‖U x‖^2 ≤ oneBodyFiber V (U x) (du x) := by
  filter_upwards [hd] with x hx
  rw [physical_fiber_mass]
  exact hbound (U x) (du x) hx

def coordLine {F : Type*} (U : MarginalPosition → F) (j : Fin 3) (x : MarginalPosition)
    (t : ℝ) : F := U (x + t • EuclideanSpace.single j 1)

def testSlope (η : MarginalPosition → ℝ) (j : Fin 3) (x : MarginalPosition) : ℝ :=
  deriv (coordLine η j x) 0

def testLaplacian (η : MarginalPosition → ℝ) (x : MarginalPosition) : ℝ :=
  ∑ j : Fin 3, testSlope (testSlope η j) j x

/-- The scalar distributional derivative identity, expressed with true coordinate slopes
of smooth tests. The function itself need only be locally integrable. -/
def coordinateWeakDerivative (f df : MarginalPosition → ℝ) (j : Fin 3) : Prop :=
  ∀ φ : MarginalPosition → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ x, f x * testSlope φ j x) = -(∫ x, df x * φ x)

theorem weak_laplacian_identity (f η : MarginalPosition → ℝ)
    (hweak : ∀ j, coordinateWeakDerivative f (testSlope f j) j)
    (hφ : ∀ j, ContDiff ℝ 1 (testSlope η j) ∧ HasCompactSupport (testSlope η j))
    (h₁ : ∀ j, Integrable (fun x => testSlope f j x * testSlope η j x))
    (h₂ : ∀ j, Integrable (fun x => f x * testSlope (testSlope η j) j x)) :
    (∫ x, ∑ j : Fin 3, testSlope f j x * testSlope η j x) =
      -(∫ x, f x * testLaplacian η x) := by
  simp only [testLaplacian, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => h₁ j), integral_finsetSum _ (fun j _ => h₂ j),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hz := hweak j (testSlope η j) (hφ j).1 (hφ j).2
  linarith

def normalizedTest (ε : ℝ) (U : MarginalPosition → E) (η : MarginalPosition → ℝ)
    (x : MarginalPosition) : E := (η x / fiberLength ε (U x)) • U x

def vectorPair (ε : ℝ) (U : MarginalPosition → E) (η : MarginalPosition → ℝ)
    (x : MarginalPosition) : ℝ :=
  (∑ j : Fin 3, ⟪deriv (coordLine U j x) 0, deriv (coordLine (normalizedTest ε U η) j x) 0⟫_ℝ) / 2

def scalarPair (ε : ℝ) (U : MarginalPosition → E) (η : MarginalPosition → ℝ)
    (x : MarginalPosition) : ℝ :=
  (∑ j : Fin 3, deriv (coordLine (fun y => fiberLength ε (U y)) j x) 0 *
    deriv (coordLine η j x) 0) / 2

theorem regularized_pairing_by_parts (ε : ℝ) (U : MarginalPosition → E) (η : MarginalPosition → ℝ)
    (hweak : ∀ j, coordinateWeakDerivative (fun x => fiberLength ε (U x))
      (testSlope (fun x => fiberLength ε (U x)) j) j)
    (hφ : ∀ j, ContDiff ℝ 1 (testSlope η j) ∧ HasCompactSupport (testSlope η j))
    (h₁ : ∀ j, Integrable (fun x => testSlope (fun y => fiberLength ε (U y)) j x * testSlope η j x))
    (h₂ : ∀ j, Integrable (fun x => fiberLength ε (U x) * testSlope (testSlope η j) j x)) :
    (∫ x, scalarPair ε U η x) = ∫ x, (-testLaplacian η x/2) * fiberLength ε (U x) := by
  have hh := weak_laplacian_identity (fun x => fiberLength ε (U x)) η hweak hφ h₁ h₂
  calc
    _ = (∫ x, ∑ j : Fin 3, testSlope (fun y => fiberLength ε (U y)) j x * testSlope η j x)/2 :=
      integral_div _ _
    _ = -(∫ x, fiberLength ε (U x) * testLaplacian η x)/2 := by rw [hh]
    _ = (-1/2 : ℝ)*(∫ x, fiberLength ε (U x) * testLaplacian η x) := by ring
    _ = ∫ x, (-1/2 : ℝ)*(fiberLength ε (U x)*testLaplacian η x) := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      ring

private theorem pairing_le {ε : ℝ} (he : 0 < ε) {U : MarginalPosition → E}
    {η : MarginalPosition → ℝ} {x : MarginalPosition}
    (hU : ∀ j, DifferentiableAt ℝ (coordLine U j x) 0)
    (hη : ∀ j, DifferentiableAt ℝ (coordLine η j x) 0) (hη0 : 0 ≤ η x) :
    scalarPair ε U η x ≤ vectorPair ε U η x := by
  unfold scalarPair vectorPair
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  have hk := fiber_test_kinetic_lower he (hU j).hasDerivAt (hη j).hasDerivAt
    (show 0 ≤ coordLine η j x 0 by simpa [coordLine] using hη0)
  have hd := (fiberLength_hasDerivAt he (hU j).hasDerivAt).deriv
  change deriv (fun t => fiberLength ε (coordLine U j x t)) 0 * _ ≤ _
  rw [hd]
  exact hk

/-- Integrating the actual derivative pairing at the normalized vector test gives the
regularized scalar form inequality. The input equality is the vector Euler equality at
that test. The two fiber inputs are the residual-particle form bound and the repulsive sign. -/
theorem integrated_fiber_comparison {ε e₁ e₂ : ℝ} (he : 0 < ε)
    (U : MarginalPosition → E) (η V residual interaction : MarginalPosition → ℝ)
    (hU : ∀ᵐ x, ∀ j, DifferentiableAt ℝ (coordLine U j x) 0)
    (hη : ∀ᵐ x, ∀ j, DifferentiableAt ℝ (coordLine η j x) 0)
    (hn : ∀ᵐ x, 0 ≤ η x)
    (hy : ∀ᵐ x, e₁ * ‖U x‖^2 ≤ residual x)
    (hw : ∀ᵐ x, 0 ≤ interaction x)
    (hi₁ : Integrable (fun x => scalarPair ε U η x +
      (V x + (e₁-e₂)) * η x * (‖U x‖^2 / fiberLength ε (U x))))
    (hi₂ : Integrable (fun x => vectorPair ε U η x + (η x / fiberLength ε (U x)) *
      ((V x - e₂)*‖U x‖^2 + residual x + interaction x)))
    (hEq : (∫ x, vectorPair ε U η x + (η x / fiberLength ε (U x)) *
      ((V x - e₂)*‖U x‖^2 + residual x + interaction x)) = 0) :
    (∫ x, scalarPair ε U η x + (V x + (e₁-e₂)) * η x *
      (‖U x‖^2 / fiberLength ε (U x))) ≤ 0 := by
  apply le_trans (integral_mono_ae hi₁ hi₂ _) hEq.le
  filter_upwards [hU, hη, hn, hy, hw] with x hux hηx hpos hres hinter
  have hp := pairing_le he hux hηx hpos
  have hc : 0 ≤ η x / fiberLength ε (U x) := div_nonneg hpos (fiberLength_pos he _).le
  have hE : (V x + (e₁-e₂))*‖U x‖^2 ≤ (V x-e₂)*‖U x‖^2+residual x+interaction x := by
    nlinarith
  calc
    _ = scalarPair ε U η x + (η x / fiberLength ε (U x)) *
        ((V x+(e₁-e₂))*‖U x‖^2) := by ring
    _ ≤ _ := add_le_add hp (mul_le_mul_of_nonneg_left hE hc)

private theorem regularization_errors {ε : ℝ} (he : 0 < ε) (u : E) :
    |‖u‖ - fiberLength ε u| ≤ ε ∧
    |‖u‖ - ‖u‖^2 / fiberLength ε u| ≤ ε := by
  have hn := norm_nonneg u
  have hp := fiberLength_pos he u
  have hs : fiberLength ε u ^ 2 = ‖u‖^2 + ε^2 :=
    Real.sq_sqrt (by positivity)
  have ha : ‖u‖ ≤ fiberLength ε u := (sq_le_sq₀ hn hp.le).mp (by linarith [sq_nonneg ε])
  have hb : fiberLength ε u ≤ ‖u‖+ε :=
    (sq_le_sq₀ hp.le (add_nonneg hn he.le)).mp (by nlinarith [mul_nonneg hn he.le])
  have ht : 0 ≤ ‖u‖/fiberLength ε u := div_nonneg hn hp.le
  have ht1 : ‖u‖/fiberLength ε u ≤ 1 := (div_le_one hp).mpr ha
  have hident : ‖u‖-‖u‖^2/fiberLength ε u =
      (‖u‖/fiberLength ε u)*(fiberLength ε u-‖u‖) := by field_simp [hp.ne']; ring
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr ha)]
    linarith
  · rw [hident, abs_of_nonneg (mul_nonneg ht (sub_nonneg.mpr ha))]
    calc
      _ ≤ 1 * (fiberLength ε u-‖u‖) := mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr ha)
      _ ≤ ε := by linarith

/-- After applying the weak derivative identity to the compact smooth scalar test,
take ε to zero. For that application A is minus half the Laplacian of the test and
B is the test times the exterior potential. Both error terms are bounded by ε. -/
theorem remove_fiber_regularization (U : MarginalPosition → E) (A B : MarginalPosition → ℝ)
    (hc : Integrable (fun x => |A x|+|B x|))
    (hi : Integrable (fun x => (A x+B x)*‖U x‖))
    (hreg : ∀ ε : ℝ, 0 < ε → Integrable (fun x =>
      A x * fiberLength ε (U x) + B x * (‖U x‖^2 / fiberLength ε (U x))))
    (hweak : ∀ ε : ℝ, 0 < ε → (∫ x,
      A x * fiberLength ε (U x) + B x * (‖U x‖^2 / fiberLength ε (U x))) ≤ 0) :
    (∫ x, (A x+B x)*‖U x‖) ≤ 0 := by
  let K : ℝ := ∫ x, |A x|+|B x|
  let L : ℝ := ∫ x, (A x+B x)*‖U x‖
  have hK : 0 ≤ K := integral_nonneg (fun x => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hbound (ε : ℝ) (he : 0 < ε) : L ≤ ε*K := by
    let S := fun x => A x * fiberLength ε (U x) + B x * (‖U x‖^2 / fiberLength ε (U x))
    let C := fun x => ε*(|A x|+|B x|)
    have hm (x : MarginalPosition) : (A x+B x)*‖U x‖ ≤ S x+C x := by
      obtain ⟨h₁,h₂⟩ := regularization_errors he (U x)
      have hA := calc
        A x*(‖U x‖-fiberLength ε (U x)) ≤ |A x*(‖U x‖-fiberLength ε (U x))| := le_abs_self _
        _ ≤ |A x|*ε := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)
      have hB := calc
        B x*(‖U x‖-‖U x‖^2/fiberLength ε (U x)) ≤ |B x*(‖U x‖-‖U x‖^2/fiberLength ε (U x))| :=
          le_abs_self _
        _ ≤ |B x|*ε := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
      dsimp only [S,C]
      linarith
    have hiS : Integrable S := hreg ε he
    have hiC : Integrable C := hc.const_mul ε
    have hb := integral_mono hi (hiS.add hiC) hm
    rw [integral_add hiS hiC] at hb
    have hC : (∫ x, C x) = ε*K := integral_const_mul _ _
    rw [hC] at hb
    exact hb.trans (add_le_of_nonpos_left (hweak ε he))
  change L ≤ 0
  by_contra! hL
  let ε := L/(K+1)
  have hd : 0 < K+1 := by linarith
  have he : 0 < ε := div_pos hL hd
  have hx : ε*(K+1)=L := by dsimp [ε]; field_simp [hd.ne']
  have := hbound ε he
  nlinarith

/-- Slicing, form integrability, and the vector-valued eigenvalue equation for the
specific admissible test η Ψ / sqrt(s²+ε²). Each entry has a mathematical meaning
before deriving the scalar distributional inequality. -/
structure AdmissibleMarginalTest (ε e₁ e₂ λ : ℝ) (U : MarginalPosition → PhysicalFiber)
    (dy : MarginalPosition → Fin 3 → MarginalPosition → ℝ) (V η : MarginalPosition → ℝ) : Prop where
  weakSlope : ∀ j, coordinateWeakDerivative (fun x => fiberLength ε (U x))
    (testSlope (fun x => fiberLength ε (U x)) j) j
  slopeInt : ∀ j, Integrable (fun x => testSlope (fun y => fiberLength ε (U y)) j x * testSlope η j x)
  hessianInt : ∀ j, Integrable (fun x => fiberLength ε (U x) * testSlope (testSlope η j) j x)
  scalarInt : Integrable (scalarPair ε U η)
  laplaceInt : Integrable (fun x => (-testLaplacian η x/2)*fiberLength ε (U x))
  sourceInt : Integrable (fun x => (V x+(e₁-e₂))*η x*(‖U x‖^2/fiberLength ε (U x)))
  vectorInt : Integrable (fun x => vectorPair ε U η x + (η x/fiberLength ε (U x))*
    ((V x-e₂)*‖U x‖^2 + oneBodyFiber V (U x) (dy x) + λ*coulombFiber x (U x)))
  vectorEuler : (∫ x, vectorPair ε U η x + (η x/fiberLength ε (U x))*
    ((V x-e₂)*‖U x‖^2 + oneBodyFiber V (U x) (dy x) + λ*coulombFiber x (U x))) = 0

/-- The scalar distributional inequality for the physical L²(R³) marginal, with the
actual Coulomb kernel. The surviving PDE assumptions explicitly identify the variational
domain on y-fibers and the admissibility of the normalized vector tests. -/
theorem physical_marginal_distribution (e₁ e₂ λ : ℝ) (hλ : 0 ≤ λ)
    (U : MarginalPosition → PhysicalFiber) (dy : MarginalPosition → Fin 3 → MarginalPosition → ℝ)
    (V η : MarginalPosition → ℝ) (dom : PhysicalFiber → (Fin 3 → MarginalPosition → ℝ) → Prop)
    (hRayleigh : ∀ u v, dom u v → e₁*(∫ y, (u y)^2) ≤ oneBodyFiber V u v)
    (hdom : ∀ᵐ x, dom (U x) (dy x))
    (hU : ∀ᵐ x, ∀ j, DifferentiableAt ℝ (coordLine U j x) 0)
    (hη : ∀ᵐ x, ∀ j, DifferentiableAt ℝ (coordLine η j x) 0)
    (hφ : ∀ j, ContDiff ℝ 1 (testSlope η j) ∧ HasCompactSupport (testSlope η j))
    (hn : ∀ᵐ x, 0 ≤ η x)
    (hc : Integrable (fun x => |(-testLaplacian η x/2)|+|(V x+(e₁-e₂))*η x|))
    (hi : Integrable (fun x => (-testLaplacian η x/2+(V x+(e₁-e₂))*η x)*‖U x‖))
    (h : ∀ ε : ℝ, 0 < ε → AdmissibleMarginalTest ε e₁ e₂ λ U dy V η) :
    (∫ x, (-testLaplacian η x/2 + (V x+(e₁-e₂))*η x)*‖U x‖) ≤ 0 := by
  apply remove_fiber_regularization U (fun x => -testLaplacian η x/2)
    (fun x => (V x+(e₁-e₂))*η x) hc hi
  · intro ε he
    exact (h ε he).laplaceInt.add (h ε he).sourceInt
  intro ε he
  have hd := h ε he
  have hy := residual_fiber_lower V e₁ dom hRayleigh U dy hdom
  have hW : ∀ᵐ x, 0 ≤ λ*coulombFiber x (U x) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg hλ (coulombFiber_nonneg x _))
  have hb := integrated_fiber_comparison he U η V (fun x => oneBodyFiber V (U x) (dy x))
    (fun x => λ*coulombFiber x (U x)) hU hη hn hy hW (hd.scalarInt.add hd.sourceInt)
    hd.vectorInt hd.vectorEuler
  rw [integral_add hd.scalarInt hd.sourceInt,
    regularized_pairing_by_parts ε U η hd.weakSlope hφ hd.slopeInt hd.hessianInt] at hb
  rw [integral_add hd.laplaceInt hd.sourceInt]
  exact hb

end HFExterior
