import DilationState

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
