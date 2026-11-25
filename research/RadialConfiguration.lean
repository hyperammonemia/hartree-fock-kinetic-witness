import FinitePotential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Concrete configuration space, signed Newton fields, two measures and the
distributional gradient used in the scalar spatial branch of Section 5. -/
noncomputable section
namespace RadialConfiguration
open MeasureTheory Set
open scoped InnerProductSpace

abbrev Point := FinitePotential.Position
abbrev Config := Point × Point
abbrev Wave := Lp ℝ 2 (volume : Measure Config)

def multiplier (z : Config) := FinitePotential.weight z.1 * FinitePotential.weight z.2
def weight (z : Config) := multiplier z ^ 2
def bareNewton (x : Point) : ℝ :=
  (∫ y : Point, Real.exp (-(‖y‖^2)) / ‖x-y‖) / (∫ y : Point, Real.exp (-(‖y‖^2)))
def j (z : Config) := bareNewton z.1 + bareNewton z.2
def jf (z : Config) := FinitePotential.coulombAverage z.1 + FinitePotential.coulombAverage z.2

theorem multiplier_pos (z : Config) : 0 < multiplier z :=
  mul_pos (FinitePotential.weight_pos _) (FinitePotential.weight_pos _)

theorem amplitude_small : FinitePotential.amplitude ≤ 1/100 := by
  have h := mul_self_le_mul_self FinitePotential.margin_pos.le FinitePotential.margin_le_one
  unfold FinitePotential.amplitude
  nlinarith

private theorem single_drift (x : Point) :
    |FinitePotential.weight x-1| ≤ FinitePotential.amplitude := by
  have s := FinitePotential.switch_range (‖x‖-FinitePotential.radius)
  have t := FinitePotential.switch_range (FinitePotential.radius+3-‖x‖)
  have env0 : 0 ≤ FinitePotential.envelope ‖x‖ := mul_nonneg s.1 t.1
  have env1 : FinitePotential.envelope ‖x‖ ≤ 1 := by
    simpa [FinitePotential.envelope] using mul_le_mul s.2 t.2 t.1 (by norm_num : (0:ℝ) ≤ 1)
  have p0 := mul_nonneg FinitePotential.amplitude_pos.le env0
  have p1 := mul_le_mul_of_nonneg_left env1 FinitePotential.amplitude_pos.le
  have low := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (FinitePotential.frequency*‖x‖)) p0
  have high := mul_le_mul_of_nonneg_left (Real.cos_le_one (FinitePotential.frequency*‖x‖)) p0
  unfold FinitePotential.weight
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Derives the configuration weight assumption for the fixed potential. -/
theorem weight_window (z : Config) : |weight z-1| ≤ 5*FinitePotential.amplitude := by
  let b := FinitePotential.amplitude
  have b0 : 0 ≤ b := FinitePotential.amplitude_pos.le
  have bs : b ≤ 1/100 := amplitude_small
  obtain ⟨p0,p1⟩ := abs_le.mp (single_drift z.1)
  obtain ⟨q0,q1⟩ := abs_le.mp (single_drift z.2)
  change -b ≤ _ at p0 q0
  change _ ≤ b at p1 q1
  have lo : (1-b)*(1-b) ≤ multiplier z :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (FinitePotential.weight_pos _).le
  have hi : multiplier z ≤ (1+b)*(1+b) :=
    mul_le_mul (by linarith) (by linarith) (FinitePotential.weight_pos _).le (by linarith)
  have lower := mul_self_le_mul_self (mul_self_nonneg (1-b)) lo
  have upper := mul_self_le_mul_self (multiplier_pos z).le hi
  have b2 := mul_le_mul_of_nonneg_left bs b0
  have b3 := mul_le_mul_of_nonneg_left bs (sq_nonneg b)
  have b4 := mul_le_mul_of_nonneg_left bs (pow_nonneg b0 3)
  change |multiplier z ^ 2-1| ≤ 5*b
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg b, pow_nonneg b0 4],
    by nlinarith⟩

def densityMeasure (a : Config → ℝ) : Measure Config :=
  volume.withDensity (fun z => ENNReal.ofReal (a z))

theorem density_univ {a : Config → ℝ} (ha : Integrable a)
    (h0 : ∀ z, 0 ≤ a z) :
    densityMeasure a univ = ENNReal.ofReal (∫ z, a z) := by
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ha (ae_of_all _ h0)).symm

def mass (u : Wave) := densityMeasure (fun z => (u z)^2)

/-- Unit norm in the actual real L² space supplies the probability measure. -/
theorem mass_probability (u : Wave) (hu : ‖u‖=1) : IsProbabilityMeasure (mass u) := by
  have i := L2.integrable_inner (𝕜 := ℝ) u u
  have hi : Integrable (fun z => (u z)^2) := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using i
  have one : (∫ z, (u z)^2) = 1 := by
    have h := L2.inner_def (𝕜 := ℝ) u u
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hu, one_pow] at h
    exact h.symm
  constructor
  rw [mass, density_univ hi (fun z => sq_nonneg _), one, ENNReal.ofReal_one]

def axis (p : Fin 2) (i : Fin 3) : Config :=
  if p=0 then (EuclideanSpace.single i 1,0) else (0,EuclideanSpace.single i 1)

/-- Weak derivatives of L² representatives in each of the six directions. -/
structure WeakGradient (dom : Submodule ℝ Wave) where
  component : dom → Fin 2 → Fin 3 → Wave
  byParts : ∀ (u : dom) (p : Fin 2) (i : Fin 3) (φ : Config → ℝ),
    ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ z, u.val z * fderiv ℝ φ z (axis p i)) = -(∫ z, component u p i z * φ z)

def coord (z : Config) (p : Fin 2) (i : Fin 3) : ℝ :=
  if p=0 then z.1 i else z.2 i

/-- The positive baseline density equals the sum of the Gaussian-shifted
gradient squares and λ times the Coulomb density. -/
def positiveDensity {dom : Submodule ℝ Wave} (G : WeakGradient dom) (u : dom) (z : Config) : ℝ :=
  (∑ p : Fin 2, ∑ i : Fin 3, (G.component u p i z + coord z p i * u.val z)^2)/2 +
    (u.val z)^2/(100*‖z.1-z.2‖)

theorem positiveDensity_nonneg {dom : Submodule ℝ Wave} (G : WeakGradient dom) (u : dom)
    (z : Config) : 0 ≤ positiveDensity G u z := by
  unfold positiveDensity
  positivity

theorem positiveMeasure_finite {dom : Submodule ℝ Wave} (G : WeakGradient dom) (u : dom)
    (h : Integrable (positiveDensity G u)) :
    IsFiniteMeasure (densityMeasure (positiveDensity G u)) := by
  constructor
  rw [density_univ h (positiveDensity_nonneg G u)]
  exact ENNReal.ofReal_lt_top

#print axioms mass_probability
#print axioms weight_window
end RadialConfiguration
