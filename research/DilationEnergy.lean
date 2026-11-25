import ManyBodyDilation

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
