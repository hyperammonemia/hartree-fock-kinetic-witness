import ManyBodyDilation

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
