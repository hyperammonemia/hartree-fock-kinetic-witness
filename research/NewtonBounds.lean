import NewtonField
import NewtonPerturbation
import RadialDifferential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fixed Hartree-field bounds for the physical potential and its two-electron
reference. All expressions are the actual normalized Newton integrals. -/
noncomputable section
open MeasureTheory RadialConfiguration
namespace NewtonBounds
abbrev X := FinitePotential.Position
abbrev b := FinitePotential.amplitude

theorem positive (x : X) : 0<bareNewton x := by
  rw [NewtonField.field_integral]
  apply mul_pos (by positivity)
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-((‖x‖*u)^2)))).intervalIntegrable _ _)
    (fun _ => Real.exp_pos _) (by norm_num)

theorem spatial_decay {x : X} (hx : x≠0) : bareNewton x ≤ ‖x‖⁻¹ := by
  have mono : Monotone GaussianCoulomb.erf := monotone_of_deriv_nonneg
    (fun r => (GaussianCoulomb.erf_derivative r).differentiableAt)
    (fun r => by rw [(GaussianCoulomb.erf_derivative r).deriv]; unfold GaussianCoulomb.gauss; positivity)
  have he := mono.ge_of_tendsto GaussianCoulomb.erf_limit ‖x‖
  rw [NewtonField.field_erf x hx,← one_div]
  exact div_le_div_of_nonneg_right he (norm_nonneg _)

theorem bounded (x : X) : bareNewton x ≤ 2 := by
  have hs : 1≤Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  exact (NewtonField.uniform_bound x).trans ((div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)).2 (by linarith))

theorem change (x : X) : |FinitePotential.coulombAverage x-bareNewton x| ≤ 5*b*bareNewton x := by
  have part : 0 < ∫ y, NewtonPerturbation.ρ y := by
    change 0 < ∫ y, NewtonField.density y
    rw [NewtonField.partition]
    unfold NewtonField.Z
    positivity
  apply NewtonPerturbation.exact_field_change x HFKinetic.weight_c1.continuous.measurable _ part
  · by_contra hi
    exact part.ne' (integral_undef hi)
  · by_contra hi
    have hp := positive x
    change 0 < (∫ y, NewtonPerturbation.ρ y / ‖x-y‖)/(∫ y, NewtonPerturbation.ρ y) at hp
    rw [integral_undef hi,zero_div] at hp
    exact hp.false

theorem pair_bound (z : Config) : |j z| ≤ 4 := by
  rw [abs_of_nonneg (add_nonneg (positive z.1).le (positive z.2).le : 0≤j z)]
  exact add_le_add (bounded _) (bounded _) |>.trans (by norm_num)

theorem pair_change (z : Config) : |jf z-j z| ≤ 24*b := by
  have he : jf z-j z = (FinitePotential.coulombAverage z.1-bareNewton z.1)+
      (FinitePotential.coulombAverage z.2-bareNewton z.2) := by unfold jf j; ring
  rw [he]
  have h0 : 0≤5*b := by positivity [FinitePotential.amplitude_pos]
  have ht := (abs_add_le _ _).trans (add_le_add (change z.1) (change z.2))
  have hj := mul_le_mul_of_nonneg_left (bounded z.1) h0
  have hk := mul_le_mul_of_nonneg_left (bounded z.2) h0
  linarith [FinitePotential.amplitude_pos]

private theorem average_measurable (d : X → ℝ) (hd : Measurable d) :
    Measurable (fun x : X => (∫ y, d y / ‖x-y‖)/(∫ y, d y)) := by
  have hm : Measurable (fun z : X × X => d z.2 / ‖z.1-z.2‖) :=
    (hd.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.div_const _

theorem fields_measurable : Measurable j ∧ Measurable jf := by
  have h : Measurable bareNewton := average_measurable _ (by fun_prop)
  have ho : Continuous FinitePotential.rawOrbital := by
    unfold FinitePotential.rawOrbital
    exact (by fun_prop : Continuous (fun x : X => Real.exp (-‖x‖^2/2))).mul HFKinetic.weight_c1.continuous
  have k : Measurable FinitePotential.coulombAverage := average_measurable _ (ho.pow 2).measurable
  exact ⟨(h.comp measurable_fst).add (h.comp measurable_snd),
    (k.comp measurable_fst).add (k.comp measurable_snd)⟩

#print axioms spatial_decay
#print axioms pair_bound
#print axioms pair_change
#print axioms fields_measurable
end NewtonBounds
