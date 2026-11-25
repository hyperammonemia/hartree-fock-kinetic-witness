import RayleighReweighting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace SectionFive
open MeasureTheory Set

/-- w is the product weight F² and j, jf are the sums of the two
unscaled one-body Newton fields on configuration space. -/
structure Fields (X : Type*) [MeasurableSpace X] where
  weight : X → ℝ
  hartree : X → ℝ
  dressedHartree : X → ℝ
  weightMeas : Measurable weight
  hartreeMeas : Measurable hartree
  dressedMeas : Measurable dressedHartree

variable {X : Type*} [MeasurableSpace X]

def baseRayleigh (f : Fields X) (μ ν : Measure X) : ℝ :=
  ν.real univ - (∫ x, f.hartree x ∂μ)/100

def newRayleigh (f : Fields X) (μ ν : Measure X) : ℝ :=
  (∫ x, f.weight x ∂ν) / (∫ x, f.weight x ∂μ) -
    (∫ x, (f.weight x / (∫ y, f.weight y ∂μ)) * f.dressedHartree x ∂μ)/100

private theorem boundedIntegrable (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ} {C : ℝ}
    (hmeas : Measurable h) (bound : ∀ x, |h x| ≤ C) : Integrable h μ :=
  (integrable_const C).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using bound x))

private theorem abs_mean_le (μ : Measure X) [IsProbabilityMeasure μ] {h : X → ℝ} {C : ℝ}
    (hi : Integrable h μ) (bound : ∀ x, |h x| ≤ C) : |∫ x, h x ∂μ| ≤ C := by
  have lo := integral_mono (integrable_const (-C)) hi (fun x => (abs_le.mp (bound x)).1)
  have hi' := integral_mono hi (integrable_const C) (fun x => (abs_le.mp (bound x)).2)
  exact abs_le.mpr ⟨by simpa using lo, by simpa using hi'⟩

/-- A pointwise oscillator field bound controls the entire signed baseline
Hartree correction for every probability density. -/
theorem baseline_floor (f : Fields X) (μ ν : Measure X) [IsProbabilityMeasure μ]
    (hj : ∀ x, |f.hartree x| ≤ 4) : ν.real univ - 1/25 ≤ baseRayleigh f μ ν := by
  have mean := abs_mean_le μ (boundedIntegrable μ f.hartreeMeas hj) hj
  unfold baseRayleigh
  linarith [(abs_le.mp mean).2]

/-- The probability measure and positive energy measure may be singular to one
another. Both Hartree terms and their normalizations are actual integrals. -/
theorem rayleigh_difference (f : Fields X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] (b : ℝ) (hb : 0 ≤ b) (hs : b ≤ 1/100)
    (hw : ∀ x, |f.weight x - 1| ≤ 5*b)
    (hj : ∀ x, |f.hartree x| ≤ 4) (hchange : ∀ x, |f.dressedHartree x-f.hartree x| ≤ 24*b) :
    |newRayleigh f μ ν-baseRayleigh f μ ν| ≤ 20*b*ν.real univ+2*b := by
  let Z := ∫ x, f.weight x ∂μ
  have wb (x : X) : |f.weight x| ≤ 2 := by
    obtain ⟨l,u⟩ := abs_le.mp (hw x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have wi (m : Measure X) [IsFiniteMeasure m] : Integrable f.weight m :=
    boundedIntegrable m f.weightMeas wb
  obtain ⟨half, ep⟩ := RayleighReweighting.normalized_energy μ ν f.weight b hb hs
    (wi μ) (wi ν) hw
  change 1/2 ≤ Z at half
  have zpos : 0 < Z := by linarith
  have closeZ : |Z-1| ≤ 5*b := by
    have h := abs_mean_le μ ((wi μ).sub (integrable_const (1:ℝ))) hw
    simpa [Z, integral_sub (wi μ) (integrable_const (1:ℝ))] using h
  have ratio (x : X) : |f.weight x/Z-1| ≤ 20*b := by
    obtain ⟨zl,zu⟩ := abs_le.mp closeZ
    obtain ⟨wl,wu⟩ := abs_le.mp (hw x)
    have numerator : |f.weight x-Z| ≤ 10*b := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [show f.weight x/Z-1=(f.weight x-Z)/Z by field_simp [zpos.ne'], abs_div, abs_of_pos zpos]
    apply (div_le_iff₀ zpos).2
    nlinarith only [numerator, mul_le_mul_of_nonneg_right half hb]
  let h := fun x => (f.weight x/Z)*f.dressedHartree x
  have point (x : X) : |h x-f.hartree x| ≤ 124*b := by
    have jfb : |f.dressedHartree x| ≤ 5 := by
      have h1 := abs_le.mp (hj x)
      have h2 := abs_le.mp (hchange x)
      exact abs_le.mpr ⟨by linarith [h1.1,h2.1], by linarith [h1.2,h2.2]⟩
    have mult := mul_le_mul (ratio x) jfb (abs_nonneg _) (by linarith : 0 ≤ 20*b)
    calc
      _ = |(f.weight x/Z-1)*f.dressedHartree x+(f.dressedHartree x-f.hartree x)| := by
        congr 1
        dsimp [h]
        ring
      _ ≤ |(f.weight x/Z-1)*f.dressedHartree x|+|f.dressedHartree x-f.hartree x| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; linarith [hchange x]
  have hmeas : Measurable h := (f.weightMeas.div_const Z).mul f.dressedMeas
  have diffi := boundedIntegrable μ (hmeas.sub f.hartreeMeas) point
  have ji := boundedIntegrable μ f.hartreeMeas hj
  have hI : Integrable h μ := by
    apply boundedIntegrable μ hmeas (C := 6)
    intro x
    obtain ⟨dl,du⟩ := abs_le.mp (point x)
    obtain ⟨jl,ju⟩ := abs_le.mp (hj x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have mean := abs_mean_le μ diffi point
  change |∫ x, h x-f.hartree x ∂μ| ≤ 124*b at mean
  rw [integral_sub hI ji] at mean
  change |(∫ x, f.weight x ∂ν)/Z-ν.real univ| ≤ 20*b*ν.real univ at ep
  change |((∫ x, f.weight x ∂ν)/Z-(∫ x, h x ∂μ)/100) -
    (ν.real univ-(∫ x, f.hartree x ∂μ)/100)| ≤ _
  obtain ⟨e1,e2⟩ := abs_le.mp ep
  obtain ⟨m1,m2⟩ := abs_le.mp mean
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms rayleigh_difference
end SectionFive
