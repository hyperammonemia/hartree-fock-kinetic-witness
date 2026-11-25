import ReferenceOrbital
import ContinuumForms
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory FinitePotential ContinuumForms
noncomputable section
namespace ReferenceTransform

abbrev axis (i : Fin 3) : Position := EuclideanSpace.single i 1

def gradSq (f : Position → ℝ) (x : Position) : ℝ :=
  ∑ i : Fin 3, directional (axis i) f x ^ 2

private theorem raw_c1 : ContDiff ℝ 1 rawOrbital := ReferenceOrbital.raw_c2.of_le (by norm_num)

private theorem slope_c1 (v : Position) : ContDiff ℝ 1 (directional v rawOrbital) :=
  (ReferenceOrbital.raw_c2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem dir_cont (v : Position) {z : Position → ℝ} (h : ContDiff ℝ 1 z) :
    Continuous (directional v z) :=
  (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem square_compact {f : Position → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => f x^2) := by
  simp only [sq]
  exact HasCompactSupport.mul_right hf

private theorem rhs_integrable (v : Position) {z : Position → ℝ}
    (hz : ContDiff ℝ 1 z) (hk : HasCompactSupport z) :
    Integrable (fun x => rawOrbital x^2*directional v z x^2) := by
  exact ((raw_c1.continuous.pow 2).mul ((dir_cont v hz).pow 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_left (square_compact (HasCompactSupport.fderiv_apply ℝ hk v)))

/-- The unnormalized fixed Gaussian-cutoff orbital has an exact directional
    ground-state transformation for every compact C¹ test, with its four
    integration-by-parts conditions proved on three-dimensional space. -/
theorem directional_transform (v : Position) {z : Position → ℝ}
    (hz : ContDiff ℝ 1 z) (hk : HasCompactSupport z) :
    (∫ x, directional v (fun y => rawOrbital y*z y) x^2+
      (directional v (directional v rawOrbital) x/rawOrbital x)*(rawOrbital x*z x)^2) =
      ∫ x, rawOrbital x^2 * directional v z x^2 := by
  have hf : ContDiff ℝ 1 (fluxFactor rawOrbital z) := (raw_c1.mul hz).mul hz
  have hfc : HasCompactSupport (fluxFactor rawOrbital z) := HasCompactSupport.mul_left hk
  apply ground_transform volume v rawOrbital z (raw_c1.differentiable one_ne_zero)
    (hz.differentiable one_ne_zero) ((slope_c1 v).differentiable one_ne_zero)
    (rhs_integrable v hz hk)
  · exact ((dir_cont v hf).mul (slope_c1 v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (HasCompactSupport.fderiv_apply ℝ hfc v))
  · exact (hf.continuous.mul (dir_cont v (slope_c1 v))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right hfc)
  · exact (hf.continuous.mul (slope_c1 v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right hfc)

private theorem lhs_integrable (v : Position) {φ : Position → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hk : HasCompactSupport φ) : Integrable (fun x => directional v φ x^2+
      (directional v (directional v rawOrbital) x/rawOrbital x)*φ x^2) := by
  apply Integrable.add
  · exact ((dir_cont v hφ).pow 2).integrable_of_hasCompactSupport
      (square_compact (HasCompactSupport.fderiv_apply ℝ hk v))
  · exact (((dir_cont v (slope_c1 v)).div raw_c1.continuous (fun x => (rawOrbital_pos x).ne')).mul
      (hφ.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.mul_left (square_compact hk))

/-- Compact physical orbitals are arbitrary here. The on-site field is exactly
    FinitePotential.externalOscillatorUnits and its Hartree term cancels
    against the displayed Coulomb average. -/
theorem external_transform {φ : Position → ℝ} (hφ : ContDiff ℝ 1 φ) (hk : HasCompactSupport φ) :
    (∫ x, gradSq φ x + 2*(externalOscillatorUnits x+coupling*coulombAverage x)*φ x^2) =
      ∫ x, rawOrbital x^2 * gradSq (φ/rawOrbital) x := by
  let z := φ/rawOrbital
  have hz : ContDiff ℝ 1 z := hφ.div raw_c1 (fun x => (rawOrbital_pos x).ne')
  have hzk : HasCompactSupport z := by
    change HasCompactSupport (φ/rawOrbital)
    rw [div_eq_mul_inv]
    exact HasCompactSupport.mul_right hk
  have hφz : (fun x => rawOrbital x*z x)=φ := by
    funext x
    change rawOrbital x*(φ x/rawOrbital x)=φ x
    field_simp [(rawOrbital_pos x).ne']
  let L (i : Fin 3) (x : Position) := directional (axis i) φ x^2+
    (directional (axis i) (directional (axis i) rawOrbital) x/rawOrbital x)*φ x^2
  let R (i : Fin 3) (x : Position) := rawOrbital x^2*directional (axis i) z x^2
  have hL (x : Position) : gradSq φ x+2*(externalOscillatorUnits x+coupling*coulombAverage x)*φ x^2 =
      ∑ i, L i x := by
    simp only [L,gradSq,externalOscillatorUnits,sub_add_cancel,laplacian,axis,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
    field_simp [(rawOrbital_pos x).ne']
    <;> ring
  have hR (x : Position) : rawOrbital x^2*gradSq (φ/rawOrbital) x = ∑ i, R i x := by
    simp only [gradSq,Finset.mul_sum,R,z]
  have hi (i : Fin 3) : (∫ x, L i x)=∫ x, R i x := by
    have h := directional_transform (axis i) hz hzk
    rw [hφz] at h
    have hpt (x : Position) : rawOrbital x*z x=φ x := congrFun hφz x
    simpa only [hpt,L,R] using h
  calc
    _ = ∫ x, ∑ i, L i x := integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = ∑ i, ∫ x, L i x := integral_finsetSum _ (fun i _ => lhs_integrable (axis i) hφ hk)
    _ = ∑ i, ∫ x, R i x := Finset.sum_congr rfl (fun i _ => hi i)
    _ = ∫ x, ∑ i, R i x := (integral_finsetSum _ (fun i _ => rhs_integrable (axis i) hz hzk)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => (hR x).symm)

end ReferenceTransform
