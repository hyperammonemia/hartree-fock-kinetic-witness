import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The angular squared marginal of an actual wavefunction on Euclidean three-space squared. -/

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace HFExterior.Polar

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Direction := sphere (0 : Position) 1
abbrev Radius := Ioi (0 : ℝ)

def surface : Measure Direction := (volume : Measure Position).toSphere
def radial : Measure Radius := Measure.volumeIoiPow 2

/-- The unnormalized spherical surface measure has mass 4π. -/
theorem surface_area : surface.real univ = 4*Real.pi := by
  unfold surface
  rw [Measure.toSphere_real_apply_univ]
  have hvol : (volume : Measure Position).real (ball 0 1) = Real.pi * 4 / 3 := by
    unfold Measure.real
    rw [EuclideanSpace.volume_ball_fin_three]
    simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  rw [hvol]
  simp only [Position,finrank_euclideanSpace_fin,Nat.cast_ofNat]
  ring

/-- General polar change of variables for a nonradial integrand. -/
theorem spatial_integral (H : Position → ℝ) :
    (∫ x, H x) = ∫ z : Direction × Radius, H ((z.2 : ℝ) • (z.1 : Position)) ∂surface.prod radial := by
  let e := homeomorphUnitSphereProd Position
  calc
    (∫ x, H x) = ∫ x : ({(0 : Position)}ᶜ : Set Position), H x.1 ∂volume.comap (↑) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl H,restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure Position).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (fun z => H ((e.symm z).1))
      change (∫ x, H ((e.symm (e x)).1) ∂volume.comap (↑)) = _ at h
      simp only [Homeomorph.symm_apply_apply] at h
      have hd : Module.finrank ℝ Position - 1 = 2 := by simp [Position]
      simpa only [e,homeomorphUnitSphereProd_symm_apply_coe,hd,surface,radial] using h

/-- Fubini in the two-electron wavefunction followed by the exact angular
coordinate change. The density has its physical square and normalization. -/
theorem pair_polar_mass (ψ : Position × Position → ℝ)
    (hψ : MemLp ψ 2 ((volume : Measure Position).prod volume)) :
    (∫ z, ψ z^2 ∂(volume : Measure Position).prod volume) =
      ∫ z : Direction × Radius, (∫ y, ψ ((z.2 : ℝ) • (z.1 : Position),y)^2)
        ∂surface.prod radial := by
  exact (integral_prod _ hψ.integrable_sq).trans (spatial_integral (fun x => ∫ y, ψ (x,y)^2))

/-- Every bounded radial probe is handled by its actual multiplication
integrand whenever the wavefunction times the probe is integrable. -/
theorem pair_polar_probe (ψ : Position × Position → ℝ) (g : ℝ → ℝ)
    (hi : Integrable (fun z : Position × Position => g ‖z.1‖ * ψ z^2)
      ((volume : Measure Position).prod volume)) :
    (∫ z : Position × Position, g ‖z.1‖*ψ z^2 ∂(volume : Measure Position).prod volume) =
      ∫ z : Direction × Radius, g (z.2 : ℝ) * (∫ y, ψ ((z.2 : ℝ) • (z.1 : Position),y)^2)
        ∂surface.prod radial := by
  rw [integral_prod _ hi,spatial_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    have hnorm : ‖(z.1 : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp z.1.property
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.property, hnorm, mul_one,integral_const_mul]

theorem spatial_integrable {H : Position → ℝ} (hf : Integrable H) :
    Integrable (fun z : Direction × Radius => H ((z.2 : ℝ) • (z.1 : Position))) (surface.prod radial) := by
  let e := homeomorphUnitSphereProd Position
  have hi : Integrable (fun x : ({(0 : Position)}ᶜ : Set Position) => H x.1) (volume.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have h := (volume : Measure Position).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (g := fun z => H ((e.symm z).1)) (Homeomorph.measurableEmbedding _)
  have hp := h.mp (by simpa only [Function.comp_apply, e, Homeomorph.symm_apply_apply] using hi)
  have hd : Module.finrank ℝ Position - 1 = 2 := by simp [Position]
  simpa only [e,homeomorphUnitSphereProd_symm_apply_coe,hd,surface,radial] using hp

theorem ordinary_radius (f : ℝ → ℝ) :
    (∫ r : Radius, f r.1 ∂radial) = ∫ r in Ioi (0 : ℝ), r^2*f r := by
  simp only [radial,Measure.volumeIoiPow,ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r^2) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg _),smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem angular_integral (H : Position → ℝ) (hf : Integrable H) :
    (∫ x, H x) = ∫ r in Ioi (0 : ℝ), r^2*(∫ w : Direction, H (r • (w : Position)) ∂surface) :=
  (spatial_integral H).trans ((integral_prod_symm _ (spatial_integrable hf)).trans
    (ordinary_radius (fun r => ∫ w : Direction, H (r • (w : Position)) ∂surface)))

def angularDensity (ψ : Position × Position → ℝ) (r : ℝ) : ℝ :=
  (∫ w : Direction, (∫ y, ψ (r • (w : Position),y)^2) ∂surface)/(4*Real.pi)

/-- The normalized squared angular marginal, integrated in ordinary radius,
recovers the physical six-dimensional mass with exactly 4πr². -/
theorem pair_radial_mass (ψ : Position × Position → ℝ)
    (hψ : MemLp ψ 2 ((volume : Measure Position).prod volume)) :
    (∫ z, ψ z^2 ∂(volume : Measure Position).prod volume) =
      ∫ r in Ioi (0 : ℝ), (4*Real.pi)*r^2*angularDensity ψ r := by
  rw [integral_prod _ hψ.integrable_sq,angular_integral _ hψ.integrable_sq.integral_prod_left]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  unfold angularDensity
  field_simp [Real.pi_ne_zero]
  ring

end HFExterior.Polar
