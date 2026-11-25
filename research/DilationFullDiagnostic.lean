import FiniteKinetic
import FinitePotential
import ContinuumHamiltonian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
/- Source section SingletKinetic.lean -/

open MeasureTheory FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

abbrev SingletConfiguration := Position × Position

def singletSpin (a b : Fin 2) : ℝ :=
  if a = b then 0 else if a = 0 then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹

theorem spin_mass : (∑ a : Fin 2, ∑ b : Fin 2, singletSpin a b^2) = 1 := by
  simp only [Fin.sum_univ_two,singletSpin]
  norm_num [inv_pow,Real.sq_sqrt]

theorem weak_const (u v : SingletConfiguration → ℂ) (e : SingletConfiguration) (c : ℂ)
    (w : ContinuumHamiltonian.IsWeakPartial u v e) :
    ContinuumHamiltonian.IsWeakPartial (fun q => c*u q) (fun q => c*v q) e := by
  intro φ hφ hS
  simp only [mul_assoc, integral_const_mul]
  rw [w φ hφ hS, mul_neg]

theorem component_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G : Ω → Position} (hG : MemLp G 2 μ) (j : Fin 3) :
    MemLp (fun x => G x j) 2 μ := by
  exact hG.of_le ((PiLp.continuous_apply _ _ j).comp_aestronglyMeasurable hG.aestronglyMeasurable)
    (ae_of_all _ fun x => PiLp.norm_apply_le (G x) j)

/-- Tensor a spatial wave with the normalized two-spin singlet. -/
def singletState (Y : SingletConfiguration → ℝ)
    (G : Fin 2 → SingletConfiguration → Position) (hY : MemLp Y 2 volume)
    (hG : ∀ i, MemLp (G i) 2 volume) (hw : ∀ i j,
      ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) : ContinuumHamiltonian.State where
  wave := fun a b x => (singletSpin a b : ℂ)*(Y x : ℂ)
  grad := fun a b i j x => (singletSpin a b : ℂ)*(G i x j : ℂ)
  squareIntegrable := fun a b => hY.ofReal.const_mul (singletSpin a b : ℂ)
  gradSquareIntegrable := fun a b i j =>
    (component_memLp (hG i) j).ofReal.const_mul (singletSpin a b : ℂ)
  weakGradient := fun a b i j => weak_const _ _ _ (singletSpin a b : ℂ) (hw i j)

private theorem singlet_factor (f : SingletConfiguration → ℝ) (c : ℝ) :
    (∫ x, ‖(c:ℂ)*(f x:ℂ)‖^2) = c^2*(∫ x, f x^2) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]

private theorem sum_spin (a : ℝ) : (∑ p : Fin 2, ∑ q : Fin 2, singletSpin p q^2*a) = a := by
  simp_rw [← Finset.sum_mul]
  rw [spin_mass,one_mul]

variable (Y : SingletConfiguration → ℝ) (G : Fin 2 → SingletConfiguration → Position)
    (hY : MemLp Y 2 volume) (hG : ∀ i, MemLp (G i) 2 volume)
    (hw : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ))
      (fun x => (G i x j : ℂ)) (ContinuumHamiltonian.axis i j))

theorem singletState_mass : ContinuumHamiltonian.mass (singletState Y G hY hG hw) = ∫ x, Y x^2 := by
  unfold ContinuumHamiltonian.mass singletState
  simp_rw [singlet_factor]
  exact sum_spin _

theorem singletState_kinetic :
    ContinuumHamiltonian.kinetic (singletState Y G hY hG hw) = kinetic volume G := by
  have compSum (i : Fin 2) : ∑ j : Fin 3, ∫ x, (G i x j)^2 = ∫ x, ‖G i x‖^2 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => (component_memLp (hG i) j).integrable_sq)]
    exact integral_congr_ae (ae_of_all _ fun x => (EuclideanSpace.real_norm_sq_eq (G i x)).symm)
  unfold ContinuumHamiltonian.kinetic singletState kinetic
  simp_rw [singlet_factor,← Finset.mul_sum,compSum]
  rw [sum_spin]

#print axioms spin_mass
#print axioms singletState_mass
#print axioms singletState_kinetic
end
end HFKinetic
/- Source section KineticDilation.lean -/

open MeasureTheory MeasureTheory.Measure FinitePotential
open scoped BigOperators
namespace HFKinetic
noncomputable section

abbrev DilationConfig := Position × Position

private theorem six_coordinates : Module.finrank ℝ DilationConfig = 6 := by
  rw [Module.finrank_prod,finrank_euclideanSpace_fin]

theorem physical_jacobian (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (f : DilationConfig → ℝ) {l : ℝ} (hl : 0 < l) :
    (∫ x, f (l⁻¹ • x) ∂μ) = l^6*(∫ x, f x ∂μ) := by
  simpa only [six_coordinates,smul_eq_mul] using μ.integral_comp_inv_smul_of_nonneg f hl.le

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

def dilatedField (l : ℝ) (n : ℕ) (f : DilationConfig → G) (x : DilationConfig) : G :=
  (l⁻¹^n) • f (l⁻¹ • x)

theorem dilated_square_integral (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (f : DilationConfig → G) (n : ℕ) {l : ℝ} (hl : 0 < l) :
    (∫ x, ‖dilatedField l n f x‖^2 ∂μ) = (l⁻¹^n)^2*l^6*(∫ x, ‖f x‖^2 ∂μ) := by
  simp only [dilatedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  rw [physical_jacobian μ (fun x => ‖f x‖^2) hl]
  ring

theorem physical_mass (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (Y : DilationConfig → G) {l : ℝ} (hl : 0 < l) :
    (∫ x, ‖dilatedField l 3 Y x‖^2 ∂μ) = ∫ x, ‖Y x‖^2 ∂μ := by
  rw [dilated_square_integral μ Y 3 hl]
  field_simp [hl.ne']

theorem physical_kinetic (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (P : Fin 2 → DilationConfig → G) {l : ℝ} (hl : 0 < l) :
    kinetic μ (fun i => dilatedField l 4 (P i)) = l⁻¹^2 * kinetic μ P := by
  unfold kinetic
  simp only [Fin.sum_univ_two,dilated_square_integral μ _ 4 hl]
  field_simp [hl.ne']

theorem physical_fixed_kinetic_order (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (P Q : Fin 2 → DilationConfig → G) (h : kinetic μ P < kinetic μ Q) :
    kinetic μ (fun i => dilatedField coupling 4 (P i)) <
    kinetic μ (fun i => dilatedField coupling 4 (Q i)) := by
  have hc : 0 < coupling := by norm_num [coupling]
  rw [physical_kinetic μ P hc,physical_kinetic μ Q hc]
  exact mul_lt_mul_of_pos_left h (sq_pos_of_pos (inv_pos.mpr hc))

#print axioms physical_jacobian
#print axioms physical_mass
#print axioms physical_kinetic
#print axioms physical_fixed_kinetic_order
end
end HFKinetic

/- Source section DilationWeak.lean -/

open MeasureTheory MeasureTheory.Measure
namespace HFKinetic
noncomputable section

/-- The spatial singlet amplitude and its directional weak derivative use real tests. -/
def WeakAxis (μ : Measure DilationConfig) (Y dY : DilationConfig → ℝ) (v : DilationConfig) : Prop :=
  ∀ φ : DilationConfig → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ x, Y x * fderiv ℝ φ x v ∂μ) = -(∫ x, dY x * φ x ∂μ)

theorem dilated_pairing (μ : Measure DilationConfig) [IsAddHaarMeasure μ] {l : ℝ}
    (hl : 0 < l) (n : ℕ) (Y φ : DilationConfig → ℝ) :
    (∫ x, dilatedField l n Y x * φ x ∂μ) =
       (l⁻¹^n*l^6) * (∫ x, Y x*φ (l • x) ∂μ) := by
  let q := fun x => Y x*φ (l • x)
  have re : (fun x => dilatedField l n Y x*φ x) = fun x => l⁻¹^n*q (l⁻¹ • x) := by
    funext x
    simp [dilatedField,q,smul_eq_mul,smul_smul,hl.ne',mul_assoc]
  rw [re, integral_const_mul,physical_jacobian μ q hl]
  dsimp [q]
  ring

theorem dilated_derivative_test {l : ℝ} (φ : DilationConfig → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x v : DilationConfig) :
    fderiv ℝ (fun q => φ (l • q)) x v = l * fderiv ℝ φ (l • x) v := by
  let A : DilationConfig →L[ℝ] DilationConfig := l • ContinuousLinearMap.id ℝ DilationConfig
  have ha := ((hφ.differentiable (by decide)) (A x)).hasFDerivAt.comp x A.hasFDerivAt
  change fderiv ℝ (φ ∘ A) x v = _
  rw [ha.fderiv]
  simp [A,smul_eq_mul]

/-- If dY is the weak spatial derivative of the oscillator-scale singlet amplitude,
the λ⁻⁴ field is the weak derivative of the very same λ⁻³-dilated amplitude. -/
theorem physical_weak_derivative (μ : Measure DilationConfig) [IsAddHaarMeasure μ]
    (Y dY : DilationConfig → ℝ) (v : DilationConfig) {l : ℝ} (hl : 0 < l)
    (hweak : WeakAxis μ Y dY v) :
    WeakAxis μ (dilatedField l 3 Y) (dilatedField l 4 dY) v := by
  intro φ hφ hcompact
  have hlin : ContDiff ℝ 1 (fun x : DilationConfig => l • x) :=
    (l • ContinuousLinearMap.id ℝ DilationConfig).contDiff
  have htest : ContDiff ℝ 1 (fun x : DilationConfig => φ (l • x)) := hφ.comp hlin
  have hw := hweak (fun x => φ (l • x)) htest (hcompact.comp_smul hl.ne')
  have test_pair : (∫ x, Y x*fderiv ℝ (fun q => φ (l • q)) x v ∂μ) =
        l*(∫ x, Y x*fderiv ℝ φ (l • x) v ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    change Y x * fderiv ℝ (fun q => φ (l • q)) x v = l * (Y x * fderiv ℝ φ (l • x) v)
    rw [dilated_derivative_test (l := l) φ hφ x v]
    ring
  rw [test_pair] at hw
  rw [dilated_pairing μ hl 3 Y (fun x => fderiv ℝ φ x v), dilated_pairing μ hl 4 dY φ]
  have c3 : l⁻¹^3*l^6 = l^3 := by field_simp [hl.ne']
  have c4 : l⁻¹^4*l^6 = l^2 := by field_simp [hl.ne']
  rw [c3,c4]
  linear_combination (l^2)*hw

#print axioms physical_weak_derivative
end
end HFKinetic

/- Source section DilationState.lean -/

open MeasureTheory MeasureTheory.Measure FinitePotential
namespace HFKinetic
noncomputable section

instance configurationVolumeHaar : IsAddHaarMeasure (volume : Measure DilationConfig) := by
  change IsAddHaarMeasure ((volume : Measure Position).prod volume)
  infer_instance

theorem dilated_memLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure DilationConfig} [IsAddHaarMeasure μ] (n : ℕ) {l : ℝ} (hl : 0 < l)
    {Y : DilationConfig → G} (hY : MemLp Y 2 μ) : MemLp (dilatedField l n Y) 2 μ := by
  have hs : l⁻¹ ≠ 0 := inv_ne_zero hl.ne'
  let t : DilationConfig ≃ᵐ DilationConfig :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 hs).unit).toMeasurableEquiv
  have hm : MemLp Y 2 (Measure.map (fun x : DilationConfig => l⁻¹ • x) μ) := by
    rw [map_addHaar_smul μ hs]
    exact hY.smul_measure ENNReal.ofReal_ne_top
  have hi : MemLp (Y ∘ t) 2 μ := t.memLp_map_measure_iff.mp hm
  exact hi.const_smul (l⁻¹^n)

theorem weakAxis_iff_complex (Y d : DilationConfig → ℝ) (v : DilationConfig) :
    WeakAxis volume Y d v ↔ ContinuumHamiltonian.IsWeakPartial
      (fun x => (Y x : ℂ)) (fun x => (d x : ℂ)) v := by
  constructor
  · intro h φ hφ hs
    simpa only [← Complex.ofReal_mul,integral_complex_ofReal,← Complex.ofReal_neg] using
      congrArg (fun a : ℝ => (a:ℂ)) (h φ hφ hs)
  · intro h φ hφ hs
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_mul,integral_complex_ofReal,← Complex.ofReal_neg] using h φ hφ hs

theorem weak_dilated_spin_axis (Y : DilationConfig → ℝ) (G : Fin 2 → DilationConfig → Position)
    (i : Fin 2) (j : Fin 3) {l : ℝ} (hl : 0 < l)
    (weak : ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.IsWeakPartial (fun x => ((dilatedField l 3 Y x : ℝ) : ℂ))
      (fun x => (dilatedField l 4 (G i) x j : ℂ)) (ContinuumHamiltonian.axis i j) := by
  apply (weakAxis_iff_complex (dilatedField l 3 Y)
    (dilatedField l 4 (fun x => G i x j)) (ContinuumHamiltonian.axis i j)).mp
  exact physical_weak_derivative volume Y (fun x => G i x j) _ hl
    ((weakAxis_iff_complex Y _ _).mpr weak)

def dilatedSinglet (l : ℝ) (hl : 0 < l) (Y : DilationConfig → ℝ)
    (G : Fin 2 → DilationConfig → Position) (hy : MemLp Y 2 volume) (hg : ∀ i, MemLp (G i) 2 volume)
    (weak : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) : ContinuumHamiltonian.State :=
  singletState (dilatedField l 3 Y) (fun i => dilatedField l 4 (G i)) (dilated_memLp 3 hl hy)
    (fun i => dilated_memLp 4 hl (hg i)) (fun i j => weak_dilated_spin_axis Y G i j hl (weak i j))

theorem dilatedSinglet_kinetic (l : ℝ) (hl : 0 < l) (Y : DilationConfig → ℝ)
    (G : Fin 2 → DilationConfig → Position) (hy : MemLp Y 2 volume) (hg : ∀ i, MemLp (G i) 2 volume)
    (weak : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.kinetic (dilatedSinglet l hl Y G hy hg weak) =
      l⁻¹^2 * ContinuumHamiltonian.kinetic (singletState Y G hy hg weak) := by
  unfold dilatedSinglet
  rw [singletState_kinetic,singletState_kinetic]
  exact physical_kinetic volume G hl

#print axioms dilated_memLp
#print axioms weak_dilated_spin_axis
#print axioms dilatedSinglet_kinetic
end
end HFKinetic
/- Source section ManyBodyDilation.lean -/

open MeasureTheory MeasureTheory.Measure FinitePotential ContinuumHamiltonian
open scoped BigOperators
namespace HFKinetic
noncomputable section

theorem ae_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    {c : ℝ} (hc : c ≠ 0) {P : E → Prop} (h : ∀ᵐ x ∂μ, P x) : ∀ᵐ x ∂μ, P (c • x) := by
  let t : E ≃ᵐ E := (Homeomorph.smul (isUnit_iff_ne_zero.2 hc).unit).toMeasurableEquiv
  have hmap : ∀ᵐ y ∂Measure.map (fun x : E => c • x) μ, P y := by
    rw [map_addHaar_smul μ hc]
    exact ae_smul_measure h _
  exact t.measurableEmbedding.ae_map_iff.mp hmap

theorem complex_spatial_jacobian (f : Config → ℂ) {l : ℝ} (hl : 0 < l) :
    (∫ x, f (l⁻¹ • x)) = (l^6:ℝ) • (∫ x, f x) := by
  have hd : Module.finrank ℝ Config = 6 := by rw [Module.finrank_prod,finrank_euclideanSpace_fin]
  simpa only [hd] using (volume : Measure Config).integral_comp_inv_smul_of_nonneg f hl.le

private theorem complex_pair (n : ℕ) {l : ℝ} (hl : 0 < l) (Y : Config → ℂ) (φ : Config → ℝ) :
    (∫ x, dilatedField l n Y x * (φ x:ℂ)) =
      ((l⁻¹^n*l^6:ℝ):ℂ) * ∫ x, Y x * (φ (l • x):ℂ) := by
  let q : Config → ℂ := fun x => Y x*(φ (l • x):ℂ)
  have eq : (fun x => dilatedField l n Y x*(φ x:ℂ)) =
      (fun x => ((l⁻¹^n:ℝ):ℂ)*q (l⁻¹ • x)) := by
    funext x
    simp [dilatedField,q,Complex.real_smul,smul_smul,hl.ne',mul_assoc]
  rw [eq, integral_const_mul,complex_spatial_jacobian q hl]
  simp [q,Complex.real_smul,mul_assoc]

theorem complex_weak_dilation (u du : Config → ℂ) (v : Config) {l : ℝ} (hl : 0 < l)
    (w : IsWeakPartial u du v) :
    IsWeakPartial (dilatedField l 3 u) (dilatedField l 4 du) v := by
  intro φ hφ hs
  have hlin : ContDiff ℝ 1 (fun x : Config => l • x) :=
    (l • ContinuousLinearMap.id ℝ Config).contDiff
  have hw := w (fun q => φ (l • q)) (hφ.comp hlin) (hs.comp_smul hl.ne')
  have key : (∫ x, u x * ((fderiv ℝ (fun q => φ (l • q)) x v : ℝ):ℂ)) =
      (l:ℂ)*(∫ x, u x*((fderiv ℝ φ (l • x) v : ℝ):ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    change u x * ((fderiv ℝ (fun q => φ (l • q)) x v : ℝ):ℂ) =
      (l:ℂ)*(u x*((fderiv ℝ φ (l • x) v : ℝ):ℂ))
    rw [dilated_derivative_test (l := l) φ hφ x v,Complex.ofReal_mul]
    ring
  rw [key] at hw
  rw [complex_pair 3 hl u (fun x => fderiv ℝ φ x v),complex_pair 4 hl du φ]
  have c3 : l⁻¹^3*l^6 = l^3 := by field_simp [hl.ne']
  have c4 : l⁻¹^4*l^6 = l^2 := by field_simp [hl.ne']
  rw [c3,c4]
  push_cast
  linear_combination (l:ℂ)^2*hw

def scaledState (l : ℝ) (hl : 0<l) (s : State) : State where
  wave := fun a b => dilatedField l 3 (s.wave a b)
  grad := fun a b i j => dilatedField l 4 (s.grad a b i j)
  squareIntegrable := fun a b => dilated_memLp 3 hl (s.squareIntegrable a b)
  gradSquareIntegrable := fun a b i j => dilated_memLp 4 hl (s.gradSquareIntegrable a b i j)
  weakGradient := fun a b i j => complex_weak_dilation _ _ _ hl (s.weakGradient a b i j)

theorem dilated_inverse {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (f : Config → G) {l : ℝ} (hl : 0 < l) :
    dilatedField l⁻¹ n (dilatedField l n f) = f := by
  funext x
  simp [dilatedField,smul_smul,inv_pow,hl.ne']

private theorem state_extensional {s t : State} (w : s.wave = t.wave) (g : s.grad = t.grad) : s = t := by
  cases s
  cases t
  cases w
  cases g
  rfl

theorem scaledState_inverse (s : State) {l : ℝ} (hl : 0<l) :
    scaledState l⁻¹ (inv_pos.mpr hl) (scaledState l hl s) = s := by
  apply state_extensional
  · exact funext fun a => funext fun b => dilated_inverse 3 (s.wave a b) hl
  · exact funext fun a => funext fun b => funext fun i => funext fun j =>
      dilated_inverse 4 (s.grad a b i j) hl

theorem scaledState_inverse_other (s : State) {l : ℝ} (hl : 0<l) :
    scaledState l hl (scaledState l⁻¹ (inv_pos.mpr hl) s) = s := by
  simpa only [inv_inv] using scaledState_inverse s (inv_pos.mpr hl)

theorem scaledState_mass (s : State) {l : ℝ} (hl : 0<l) :
    ContinuumHamiltonian.mass (scaledState l hl s) = ContinuumHamiltonian.mass s := by
  unfold ContinuumHamiltonian.mass
  simp only [scaledState,physical_mass volume _ hl]

theorem scaledState_kinetic (s : State) {l : ℝ} (hl : 0<l) :
    ContinuumHamiltonian.kinetic (scaledState l hl s) = l⁻¹^2 * ContinuumHamiltonian.kinetic s := by
  have eql (f : Config → ℂ) : (∫ x, ‖dilatedField l 4 f x‖^2) = l⁻¹^2 * ∫ x, ‖f x‖^2 := by
    rw [dilated_square_integral volume f 4 hl]
    field_simp [hl.ne']
  unfold ContinuumHamiltonian.kinetic
  simp only [scaledState,eql,← Finset.mul_sum]
  ring

theorem scaled_sameRay {s t : State} {l : ℝ} (hl : 0<l) (h : SameRay s t) :
    SameRay (scaledState l hl s) (scaledState l hl t) := by
  obtain ⟨c,hc,ht⟩ := h
  refine ⟨c,hc,fun a b => ?_⟩
  filter_upwards [ae_scaled (volume : Measure Config) (inv_ne_zero hl.ne') (ht a b)] with x hx
  change l⁻¹^3 • s.wave a b (l⁻¹ • x) = c*(l⁻¹^3 • t.wave a b (l⁻¹ • x))
  rw [hx]
  simp [Complex.real_smul,mul_left_comm]

#print axioms complex_weak_dilation
#print axioms scaledState_inverse
#print axioms scaledState_kinetic
end
end HFKinetic
/- Source section DilationEnergy.lean -/

open MeasureTheory FinitePotential ContinuumHamiltonian
open scoped BigOperators
namespace HFKinetic
noncomputable section

def scaledExternal (l : ℝ) (v : Position → ℝ) (x : Position) := l⁻¹^2*v (l⁻¹ • x)

/-- Oscillator coordinates have Coulomb coefficient l. -/
def oscillatorEnergy (l : ℝ) (v : Position → ℝ) (s : State) : ℝ :=
  ContinuumHamiltonian.kinetic s + ∑ a : Spin, ∑ b : Spin,
    ∫ z, (external v z + l*coulomb z)*‖s.wave a b z‖^2

theorem scaledExternal_inverse (v : Position → ℝ) {l : ℝ} (hl : 0<l) :
    scaledExternal l⁻¹ (scaledExternal l v) = v := by
  funext x
  simp [scaledExternal,smul_smul,inv_pow,hl.ne',mul_assoc]

theorem coulomb_pullback {l : ℝ} (hl : 0<l) (z : Config) : coulomb (l⁻¹ • z) = l*coulomb z := by
  change ‖l⁻¹ • z.1-l⁻¹ • z.2‖⁻¹ = l*‖z.1-z.2‖⁻¹
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hl.le),mul_inv_rev,inv_inv,mul_comm]

private theorem density_pull (B : Config → ℝ) (u : Config → ℂ) {l : ℝ} (z : Config) :
    B (l⁻¹ • z)*‖dilatedField l 3 u z‖^2 =
        (l⁻¹^3)^2 * (B (l⁻¹ • z)*‖u (l⁻¹ • z)‖^2) := by
  simp only [dilatedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem potential_pullback (B : Config → ℝ) (u : Config → ℂ) {l : ℝ} (hl : 0<l) :
    (∫ z, B (l⁻¹ • z)*‖dilatedField l 3 u z‖^2) = ∫ z, B z*‖u z‖^2 := by
  simp_rw [density_pull B u]
  rw [integral_const_mul,physical_jacobian volume (fun z => B z*‖u z‖^2) hl]
  field_simp [hl.ne']

theorem integrable_potential_pullback (B : Config → ℝ) (u : Config → ℂ) {l : ℝ} (hl : 0<l)
    (h : Integrable (fun z => B z*‖u z‖^2)) :
    Integrable (fun z => B (l⁻¹ • z)*‖dilatedField l 3 u z‖^2) := by
  have hab := (h.comp_smul (inv_ne_zero hl.ne')).const_mul ((l⁻¹^3)^2)
  apply hab.congr
  exact ae_of_all _ fun z => (density_pull B u z).symm

theorem external_pullback (v : Position → ℝ) (l : ℝ) (z : Config) :
    external (scaledExternal l v) z = l⁻¹^2*external v (l⁻¹ • z) := by
  change l⁻¹^2*v (l⁻¹ • z.1)+l⁻¹^2*v (l⁻¹ • z.2) = l⁻¹^2*(v (l⁻¹ • z.1)+v (l⁻¹ • z.2))
  ring

private theorem potential_coeff (v : Position → ℝ) {l : ℝ} (hl : 0<l) (z : Config) :
    external (scaledExternal l v) z+coulomb z =
       l⁻¹^2*(external v (l⁻¹ • z)+l*coulomb (l⁻¹ • z)) := by
  rw [external_pullback,coulomb_pullback hl]
  field_simp [hl.ne']

theorem scaledState_energy (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    formEnergy (scaledExternal l v) (scaledState l hl s) = l⁻¹^2*oscillatorEnergy l v s := by
  let B := fun z : Config => external v z+l*coulomb z
  have eq (a b : Spin) : (∫ z, (external (scaledExternal l v) z+coulomb z)*
      ‖(scaledState l hl s).wave a b z‖^2) = l⁻¹^2 * ∫ z, B z*‖s.wave a b z‖^2 := by
    calc
      _ = ∫ z, l⁻¹^2*(B (l⁻¹ • z)*‖dilatedField l 3 (s.wave a b) z‖^2) := by
        apply integral_congr_ae
        refine ae_of_all _ fun z => ?_
        change (external (scaledExternal l v) z+coulomb z)*‖dilatedField l 3 (s.wave a b) z‖^2 = _
        rw [potential_coeff v hl z]
        exact mul_assoc _ _ _
      _ = _ := by rw [integral_const_mul,potential_pullback B _ hl]
  unfold formEnergy oscillatorEnergy
  rw [scaledState_kinetic s hl]
  simp_rw [eq,← Finset.mul_sum]
  exact (mul_add _ _ _).symm

theorem scaled_admissible (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) (h : Admissible v s) :
    Admissible (scaledExternal l v) (scaledState l hl s) := by
  obtain ⟨hm,hs,hv,hc⟩ := h
  refine ⟨(scaledState_mass s hl).trans hm,?_,?_,?_⟩
  · intro a b
    filter_upwards [ae_scaled (volume : Measure Config) (inv_ne_zero hl.ne') (hs a b)] with z hz
    change (l⁻¹^3) • s.wave a b (l⁻¹ • z) = -((l⁻¹^3) • s.wave b a (l⁻¹ • (z.2,z.1)))
    simpa only [smul_neg] using congrArg (fun a : ℂ => (l⁻¹^3) • a) hz
  · intro a b
    have hE := (integrable_potential_pullback (external v) (s.wave a b) hl (hv a b)).const_mul (l⁻¹^2)
    apply hE.congr
    refine ae_of_all _ fun z => ?_
    change l⁻¹^2*(external v (l⁻¹ • z)*‖dilatedField l 3 (s.wave a b) z‖^2) =
      external (scaledExternal l v) z*‖dilatedField l 3 (s.wave a b) z‖^2
    rw [external_pullback]
    ring
  · intro a b
    have hW := (integrable_potential_pullback coulomb (s.wave a b) hl (hc a b)).const_mul l⁻¹
    apply hW.congr
    refine ae_of_all _ fun z => ?_
    change l⁻¹*(coulomb (l⁻¹ • z)*‖dilatedField l 3 (s.wave a b) z‖^2) =
      coulomb z*‖dilatedField l 3 (s.wave a b) z‖^2
    rw [coulomb_pullback hl]
    field_simp [hl.ne']

theorem scaled_admissible_iff (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    Admissible (scaledExternal l v) (scaledState l hl s) ↔ Admissible v s := by
  refine ⟨fun h => ?_, scaled_admissible v s hl⟩
  have hi := scaled_admissible _ _ (inv_pos.mpr hl) h
  simpa only [scaledExternal_inverse v hl,scaledState_inverse s hl] using hi

#print axioms scaledState_energy
#print axioms scaled_admissible_iff
end
end HFKinetic
/- Source section DilationSlater.lean -/

open MeasureTheory MeasureTheory.Measure FinitePotential ContinuumHamiltonian
open scoped BigOperators
namespace HFKinetic
noncomputable section

def orbitalScale (l : ℝ) : ℝ := Real.sqrt (l⁻¹^3)
def scaledOrbital (l : ℝ) (u : Spinor) : Spinor :=
  fun a x => (orbitalScale l:ℂ)*u a (l⁻¹ • x)

theorem orbitalScale_squared {l : ℝ} (hl : 0<l) : orbitalScale l^2=l⁻¹^3 :=
  Real.sq_sqrt (pow_nonneg (inv_nonneg.mpr hl.le) _)

private theorem orbitalScale_squared_cast {l : ℝ} (hl : 0<l) :
    (orbitalScale l:ℂ)^2 = ((l⁻¹^3:ℝ):ℂ) := by
  exact_mod_cast orbitalScale_squared hl

theorem scaledOrbital_memLp {l : ℝ} (hl : 0<l) (u : Spinor) (a : Spin)
    (h : MemLp (u a) 2 volume) : MemLp (scaledOrbital l u a) 2 volume := by
  have hs : l⁻¹≠0 := inv_ne_zero hl.ne'
  let t : Position ≃ᵐ Position := (Homeomorph.smul (isUnit_iff_ne_zero.2 hs).unit).toMeasurableEquiv
  have hm : MemLp (u a) 2 (Measure.map (fun x : Position => l⁻¹ • x) volume) := by
    rw [map_addHaar_smul volume hs]
    exact h.smul_measure ENNReal.ofReal_ne_top
  have hc : MemLp (u a ∘ t) 2 volume := t.memLp_map_measure_iff.mp hm
  exact hc.const_mul (orbitalScale l:ℂ)

theorem single_particle_jacobian (f : Position → ℂ) {l : ℝ} (hl : 0<l) :
    (∫ x, f (l⁻¹ • x)) = (l^3:ℝ) • (∫ x, f x) := by
  simpa only [finrank_euclideanSpace_fin] using
    (volume : Measure Position).integral_comp_inv_smul_of_nonneg f hl.le

theorem scaledOrbital_inner (u v : Spinor) {l : ℝ} (hl : 0<l) :
    orbitalInner (scaledOrbital l u) (scaledOrbital l v) = orbitalInner u v := by
  unfold orbitalInner
  apply Finset.sum_congr rfl
  intro a ha
  let q : Position → ℂ := fun x => star (u a x)*v a x
  have eq : (fun x => star (scaledOrbital l u a x)*scaledOrbital l v a x) =
      (fun x => (orbitalScale l:ℂ)^2 * q (l⁻¹ • x)) := by
    funext x
    simp [scaledOrbital,q]
    ring
  rw [eq,integral_const_mul,single_particle_jacobian q hl,Complex.real_smul,orbitalScale_squared_cast hl]
  have e : ((l⁻¹^3:ℝ):ℂ)*((l^3:ℝ):ℂ)=1 := by
    exact_mod_cast (show l⁻¹^3*l^3=1 by field_simp [hl.ne'])
  rw [← mul_assoc,e,one_mul]

theorem scaled_determinant (u v : Spinor) (a b : Spin) (z : Config) {l : ℝ} (hl : 0<l) :
    dilatedField l 3 (determinant u v a b) z = determinant (scaledOrbital l u) (scaledOrbital l v) a b z := by
  simp only [dilatedField,Complex.real_smul,← orbitalScale_squared_cast hl]
  unfold determinant scaledOrbital
  change (orbitalScale l:ℂ)^2 *
      ((u a (l⁻¹ • z.1)*v b (l⁻¹ • z.2)-v a (l⁻¹ • z.1)*u b (l⁻¹ • z.2))/(Real.sqrt 2:ℂ)) = _
  ring

theorem scaled_slater (s : State) {l : ℝ} (hl : 0<l) (h : IsSlater s) :
    IsSlater (scaledState l hl s) := by
  obtain ⟨u,v,hm,hu,hv,huv,hd⟩ := h
  refine ⟨scaledOrbital l u,scaledOrbital l v,
    fun a => ⟨scaledOrbital_memLp hl u a (hm a).1,scaledOrbital_memLp hl v a (hm a).2⟩,
    (scaledOrbital_inner u u hl).trans hu,(scaledOrbital_inner v v hl).trans hv,
    (scaledOrbital_inner u v hl).trans huv,?_⟩
  intro a b
  filter_upwards [ae_scaled (volume : Measure Config) (inv_ne_zero hl.ne') (hd a b)] with z hz
  change l⁻¹^3 • s.wave a b (l⁻¹ • z) = _
  rw [hz]
  exact scaled_determinant u v a b z hl

theorem scaled_slater_iff (s : State) {l : ℝ} (hl : 0<l) :
    IsSlater (scaledState l hl s) ↔ IsSlater s := by
  refine ⟨fun h => ?_,scaled_slater s hl⟩
  simpa only [scaledState_inverse s hl] using scaled_slater _ (inv_pos.mpr hl) h

theorem scaled_closedShell (s : State) (u : Position → ℂ) {l : ℝ} (hl : 0<l)
    (h : IsClosedShell s u) : IsClosedShell (scaledState l hl s)
        (fun x => (orbitalScale l:ℂ)*u (l⁻¹ • x)) := by
  let spinOrb (i : Spin) : Spinor := fun t x => if t=i then u x else 0
  have eq (i : Spin) : scaledOrbital l (spinOrb i) = fun t x =>
      if t=i then (orbitalScale l:ℂ)*u (l⁻¹ • x) else 0 := by
    funext t x
    by_cases ht : t=i <;> simp [scaledOrbital,spinOrb,ht]
  intro a b
  filter_upwards [ae_scaled (volume : Measure Config) (inv_ne_zero hl.ne') (h a b)] with z hz
  change l⁻¹^3 • s.wave a b (l⁻¹ • z) = _
  rw [hz]
  calc
    _ = determinant (scaledOrbital l (spinOrb 0)) (scaledOrbital l (spinOrb 1)) a b z :=
      scaled_determinant _ _ _ _ _ hl
    _ = _ := by rw [eq 0,eq 1]

theorem scaled_closedShell_radial (s : State) {l : ℝ} (hl : 0<l)
    (h : ∃ U : ℝ → ℝ, IsClosedShell s (fun x => (U ‖x‖:ℂ))) :
    ∃ V : ℝ → ℝ, IsClosedShell (scaledState l hl s) (fun x => (V ‖x‖:ℂ)) := by
  obtain ⟨U,hU⟩ := h
  refine ⟨fun r => orbitalScale l*U (l⁻¹*r),?_⟩
  have hh := scaled_closedShell s (fun x => (U ‖x‖:ℂ)) hl hU
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hl.le),Complex.ofReal_mul] using hh

#print axioms scaledOrbital_inner
#print axioms scaled_slater_iff
#print axioms scaled_closedShell_radial
end
end HFKinetic
/- Source section DilationMinima.lean -/

open MeasureTheory FinitePotential ContinuumHamiltonian
namespace HFKinetic
noncomputable section

def OscillatorExactMinimum (l : ℝ) (v : Position → ℝ) (s : State) : Prop :=
  Admissible v s ∧ ∀ w, Admissible v w → oscillatorEnergy l v s ≤ oscillatorEnergy l v w

def OscillatorHFMinimum (l : ℝ) (v : Position → ℝ) (s : State) : Prop :=
  (Admissible v s ∧ IsSlater s) ∧ ∀ w, Admissible v w → IsSlater w →
    oscillatorEnergy l v s ≤ oscillatorEnergy l v w

theorem energy_of_inverse (v : Position → ℝ) (w : State) {l : ℝ} (hl : 0<l) :
    formEnergy (scaledExternal l v) w = l⁻¹^2*oscillatorEnergy l v (scaledState l⁻¹ (inv_pos.mpr hl) w) := by
  simpa only [scaledState_inverse_other w hl] using scaledState_energy v (scaledState l⁻¹ (inv_pos.mpr hl) w) hl

theorem admissible_of_inverse (v : Position → ℝ) (w : State) {l : ℝ} (hl : 0<l)
    (h : Admissible (scaledExternal l v) w) : Admissible v (scaledState l⁻¹ (inv_pos.mpr hl) w) := by
  simpa only [scaledExternal_inverse v hl] using scaled_admissible (scaledExternal l v) w (inv_pos.mpr hl) h

theorem scaled_exactMinimum_iff (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    ExactMinimum (scaledExternal l v) (scaledState l hl s) ↔ OscillatorExactMinimum l v s := by
  constructor
  · rintro ⟨hs,he⟩
    refine ⟨(scaled_admissible_iff v s hl).mp hs,fun w hw => ?_⟩
    have h := he (scaledState l hl w) (scaled_admissible v w hl hw)
    rw [scaledState_energy v s hl,scaledState_energy v w hl] at h
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hl))).mp h
  · rintro ⟨hs,he⟩
    refine ⟨scaled_admissible v s hl hs,fun w hw => ?_⟩
    rw [scaledState_energy v s hl,energy_of_inverse v w hl]
    exact mul_le_mul_of_nonneg_left (he _ (admissible_of_inverse v w hl hw)) (sq_nonneg _)

theorem scaled_hfMinimum_iff (v : Position → ℝ) (s : State) {l : ℝ} (hl : 0<l) :
    HFMinimum (scaledExternal l v) (scaledState l hl s) ↔ OscillatorHFMinimum l v s := by
  constructor
  · rintro ⟨⟨hs,hS⟩,he⟩
    refine ⟨⟨(scaled_admissible_iff v s hl).mp hs,(scaled_slater_iff s hl).mp hS⟩,fun w hw hW => ?_⟩
    have h := he (scaledState l hl w) (scaled_admissible v w hl hw) (scaled_slater w hl hW)
    rw [scaledState_energy v s hl,scaledState_energy v w hl] at h
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hl))).mp h
  · rintro ⟨⟨hs,hS⟩,he⟩
    refine ⟨⟨scaled_admissible v s hl hs,scaled_slater s hl hS⟩,fun w hw hW => ?_⟩
    rw [scaledState_energy v s hl,energy_of_inverse v w hl]
    exact mul_le_mul_of_nonneg_left
      (he _ (admissible_of_inverse v w hl hw) (scaled_slater w (inv_pos.mpr hl) hW)) (sq_nonneg _)

/-- Every minimization is taken over the full complex-spin form domain or over
all normalized complex Slater determinants. Dilation preserves the optimizer,
its uniqueness up to phase, the radial closed shell, and the kinetic ordering. -/
theorem oscillator_reversal_implies_fixed (e h : State)
    (he : OscillatorExactMinimum coupling externalOscillatorUnits e)
    (hh : OscillatorHFMinimum coupling externalOscillatorUnits h)
    (unique : ∀ w, OscillatorHFMinimum coupling externalOscillatorUnits w → SameRay w h)
    (closed : ∃ U : ℝ → ℝ, IsClosedShell h (fun x => (U ‖x‖:ℂ)))
    (reversal : ContinuumHamiltonian.kinetic e < ContinuumHamiltonian.kinetic h) :
    ContinuumHamiltonian.FixedRadialReversal := by
  have hl : 0 < coupling := by norm_num [coupling]
  refine ⟨scaledState coupling hl e,scaledState coupling hl h,
    (scaled_exactMinimum_iff externalOscillatorUnits e hl).mpr he,
    (scaled_hfMinimum_iff externalOscillatorUnits h hl).mpr hh,?_,
    scaled_closedShell_radial h hl closed,?_⟩
  · intro w hw
    let t := scaledState coupling⁻¹ (inv_pos.mpr hl) w
    have htw : scaledState coupling hl t = w := scaledState_inverse_other w hl
    have hmin : HFMinimum (scaledExternal coupling externalOscillatorUnits) (scaledState coupling hl t) := by
      rw [htw]
      exact hw
    have hray := scaled_sameRay hl (unique t ((scaled_hfMinimum_iff externalOscillatorUnits t hl).mp hmin))
    simpa only [htw] using hray
  · rw [scaledState_kinetic e hl,scaledState_kinetic h hl]
    exact mul_lt_mul_of_pos_left reversal (sq_pos_of_pos (inv_pos.mpr hl))

#print axioms scaled_exactMinimum_iff
#print axioms scaled_hfMinimum_iff
#print axioms oscillator_reversal_implies_fixed
end
end HFKinetic
