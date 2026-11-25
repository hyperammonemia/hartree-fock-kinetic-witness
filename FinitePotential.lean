import ContinuumForms
import RadialCertificate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
The fixed local external potential of Section 1 of continuum-witness.md.
The final conditional theorem instantiates the scalar kinetic certificate
at the actual parameters, with their signs and normalization verified in ℝ.
-/
noncomputable section
namespace FinitePotential

abbrev Position := EuclideanSpace ℝ (Fin 3)

def radius : ℝ := Real.exp (10^18)
def margin : ℝ := Real.exp (-((radius+3)^2))
def amplitude : ℝ := (margin/1000)^2
def frequency : ℝ := amplitude⁻¹ ^ 2
def coupling : ℝ := 1/100

def switch (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else 6*t^5-15*t^4+10*t^3

private theorem smoothstep_nonneg (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    0 ≤ 6*t^5-15*t^4+10*t^3 := by
  have ht1 : 0 ≤ 1-t := by linarith
  calc
    0 ≤ t^3 * (10*(1-t)^2+5*t*(1-t)+t^2) := by positivity
    _ = _ := by ring

theorem switch_range (t : ℝ) : 0 ≤ switch t ∧ switch t ≤ 1 := by
  unfold switch
  split_ifs with low high
  · norm_num
  · norm_num
  · have ht : 0 ≤ t := by linarith
    have ht' : t ≤ 1 := by linarith
    have a := smoothstep_nonneg t ht ht'
    have b := smoothstep_nonneg (1-t) (by linarith) (by linarith)
    constructor <;> nlinarith

def envelope (r : ℝ) : ℝ := switch (r-radius) * switch (radius+3-r)
def weight (x : Position) : ℝ :=
  1 + amplitude * envelope ‖x‖ * Real.cos (frequency * ‖x‖)

theorem margin_pos : 0 < margin := Real.exp_pos _
theorem margin_le_one : margin ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
theorem amplitude_pos : 0 < amplitude := by
  unfold amplitude
  exact sq_pos_of_pos (div_pos margin_pos (by norm_num))

theorem weight_pos (x : Position) : 0 < weight x := by
  have h1 := switch_range (‖x‖-radius)
  have h2 := switch_range (radius+3-‖x‖)
  have hg0 : 0 ≤ envelope ‖x‖ := mul_nonneg h1.1 h2.1
  have hg1 : envelope ‖x‖ ≤ 1 := by
    unfold envelope
    simpa using mul_le_mul h1.2 h2.2 h2.1 (by norm_num : (0:ℝ) ≤ 1)
  have ha1 : amplitude ≤ 1/1000000 := by
    have hb := mul_self_le_mul_self margin_pos.le margin_le_one
    unfold amplitude
    nlinarith
  have hag0 := mul_nonneg amplitude_pos.le hg0
  have hag1 := mul_le_mul_of_nonneg_left hg1 amplitude_pos.le
  have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (frequency*‖x‖)) hag0
  unfold weight
  nlinarith

-- A common normalization of this prescribed orbital cancels from the
-- Laplacian ratio and from the normalized Coulomb average below.
def rawOrbital (x : Position) : ℝ := Real.exp (-(‖x‖^2)/2) * weight x

theorem rawOrbital_pos (x : Position) : 0 < rawOrbital x :=
  mul_pos (Real.exp_pos _) (weight_pos x)

def coulombAverage (x : Position) : ℝ :=
  (∫ y : Position, rawOrbital y^2 / ‖x-y‖) / (∫ y : Position, rawOrbital y^2)

def laplacian (u : Position → ℝ) (x : Position) : ℝ :=
  ∑ i : Fin 3, ContinuumForms.directional (EuclideanSpace.single i 1)
    (ContinuumForms.directional (EuclideanSpace.single i 1) u) x

def externalOscillatorUnits (x : Position) : ℝ :=
  laplacian rawOrbital x / (2 * rawOrbital x) - coupling * coulombAverage x

def physicalExternal (y : Position) : ℝ :=
  coupling⁻¹^2 * externalOscillatorUnits (coupling⁻¹ • y)

/-- T values here are in oscillator units. The tail and the two genuine
kinetic remainder bounds are the continuum estimates in Sections 4–6. -/
theorem sign_at_fixed_parameters (hfT exactT hfProbe trueProbe pulledProbe : ℝ)
    (tail : margin ≤ hfProbe-trueProbe)
    (stateError : pulledProbe-trueProbe ≤ 20*(margin/1000))
    (hfRemainder : hfProbe-(2/(amplitude*frequency)^2)*hfT ≤ 100*amplitude)
    (exactRemainder : (2/(amplitude*frequency)^2)*exactT-pulledProbe ≤ 100*amplitude) :
    exactT < hfT := by
  have scalePositive : 0 < 2/(amplitude*frequency)^2 := by
    have hk : 0 < frequency := sq_pos_of_pos (inv_pos.mpr amplitude_pos)
    exact div_pos (by norm_num) (sq_pos_of_pos (mul_pos amplitude_pos hk))
  exact RadialCertificate.finite_reversal margin (margin/1000) amplitude
    (2/(amplitude*frequency)^2) hfT exactT hfProbe trueProbe pulledProbe
    margin_pos margin_le_one (by ring) (by simp only [amplitude, pow_two])
    scalePositive tail stateError hfRemainder exactRemainder

#print axioms weight_pos
#print axioms physicalExternal
#print axioms sign_at_fixed_parameters
end FinitePotential
