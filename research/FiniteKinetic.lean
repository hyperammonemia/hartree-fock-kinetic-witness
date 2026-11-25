import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-! A finite-frequency estimate for two normalized-particle gradient fields. -/

open MeasureTheory
open scoped BigOperators

namespace HFKinetic
noncomputable section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Here h is the envelope times sine and t is its derivative times cosine.
The first multiplier is the full product weight divided by the state norm.
The second multiplier omits the differentiated particle. -/
def scaled (b full other h t y : ℝ) (d e : G) : G :=
  (b * full) • d + (other * (b^2 * t - h) * y) • e

def leading (h y : ℝ) (e : G) : G := (-(h * y)) • e

theorem local_difference {b full other h t y : ℝ} (d e : G)
    (hb : 0 ≤ b) (hb' : b ≤ 1 / 100)
    (hf : |full| ≤ 2) (ho : |other| ≤ 2) (hw : |other - 1| ≤ 5*b)
    (hh : |h| ≤ 1) (ht : |t| ≤ 2) (he : ‖e‖ ≤ 1) :
    ‖scaled b full other h t y d e - leading h y e‖ ≤ b*(2*‖d‖ + 6*|y|) := by
  have eqv : scaled b full other h t y d e - leading h y e =
      (b*full) • d + ((other*b^2*t - (other-1)*h)*y) • e := by
    unfold scaled leading
    rw [add_sub_assoc, ← sub_smul]
    congr 2
    ring
  have hosc : |(other-1)*h| ≤ 5*b := by
    rw [abs_mul]
    calc
      _ ≤ (5*b) * 1 := mul_le_mul hw hh (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hder : |other*b^2*t| ≤ 4*b^2 := by
    simp only [abs_mul, abs_of_nonneg (sq_nonneg b)]
    calc
      _ ≤ (2*b^2)*2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right ho (sq_nonneg b)) ht (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hcoeff : |other*b^2*t - (other-1)*h| ≤ 6*b := by
    have hh' := abs_sub (other*b^2*t) ((other-1)*h)
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb')]
  have hfull : |b*full| ≤ 2*b := by
    rw [abs_mul, abs_of_nonneg hb, mul_comm (2:ℝ)]
    exact mul_le_mul_of_nonneg_left hf hb
  rw [eqv]
  calc
    _ ≤ ‖(b*full) • d‖ + ‖((other*b^2*t - (other-1)*h)*y) • e‖ := norm_add_le _ _
    _ = |b*full| * ‖d‖ + (|other*b^2*t - (other-1)*h| * |y|)*‖e‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul]
    _ ≤ (2*b)*‖d‖ + ((6*b)*|y|)*1 := by
      exact add_le_add (mul_le_mul_of_nonneg_right hfull (norm_nonneg _))
        (mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)) he (norm_nonneg _)
          (by positivity))
    _ = _ := by ring

omit [NormedSpace ℝ G] in
theorem sq_norm_error {p l : G} {b a s : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1/100)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hl : ‖l‖ ≤ s) (hd : ‖p-l‖ ≤ b*(2*a+6*s)) :
    |‖p‖^2-‖l‖^2| ≤ b*(3*a^2+15*s^2) := by
  have hu : |‖p‖ - ‖l‖| ≤ b*(2*a+6*s) := (abs_norm_sub_norm_le p l).trans hd
  have hp : ‖p‖ ≤ s + b*(2*a+6*s) := by
    have := (abs_le.mp hu).2
    linarith
  have hmain : (2*a+6*s)*(2*s) ≤ 2*a^2+14*s^2 := by nlinarith [sq_nonneg (a-s)]
  have hquad : (2*a+6*s)^2 ≤ 8*a^2+72*s^2 := by nlinarith [sq_nonneg (2*a-6*s)]
  have hweak : b*(2*a+6*s)^2 ≤ (1/100)*(8*a^2+72*s^2) :=
    mul_le_mul hb' hquad (sq_nonneg _) (by norm_num)
  calc
    _ = |‖p‖-‖l‖| * (‖p‖+‖l‖) := by
      rw [show ‖p‖^2-‖l‖^2 = (‖p‖-‖l‖)*(‖p‖+‖l‖) by ring, abs_mul,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (b*(2*a+6*s))*(2*s+b*(2*a+6*s)) := by
      apply mul_le_mul hu (by linarith) (by positivity) (by positivity)
    _ = b*((2*a+6*s)*(2*s)+b*(2*a+6*s)^2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hb
      nlinarith [sq_nonneg a, sq_nonneg s]

theorem leading_sq {h y : ℝ} {e : G} (he : ‖e‖ = 1) :
    ‖leading h y e‖^2 = h^2 * y^2 := by
  rw [leading, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The two terms are the two particles, each with its ordinary Euclidean gradient. -/
def kinetic (μ : Measure Ω) (P : Fin 2 → Ω → G) : ℝ :=
  (∑ i : Fin 2, ∫ x, ‖P i x‖^2 ∂μ) / 2

def probe (μ : Measure Ω) (Y : Ω → ℝ) (h : Fin 2 → Ω → ℝ) : ℝ :=
  ∑ i : Fin 2, ∫ x, (h i x)^2*(Y x)^2 ∂μ

theorem two_particle_remainder {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1/100)
    (Y : Ω → ℝ) (d P e : Fin 2 → Ω → G)
    (full : Ω → ℝ) (other h t : Fin 2 → Ω → ℝ)
    (hY : Integrable (fun x => Y x ^ 2) μ) (mass : (∫ x, Y x ^ 2 ∂μ) = 1)
    (hd : ∀ i, Integrable (fun x => ‖d i x‖^2) μ)
    (hP : ∀ i, Integrable (fun x => ‖P i x‖^2) μ)
    (hhY : ∀ i, Integrable (fun x => (h i x)^2*(Y x)^2) μ)
    (hgrad : (∑ i : Fin 2, ∫ x, ‖d i x‖^2 ∂μ) ≤ 8)
    (data : ∀ i, ∀ᵐ x ∂μ,
      |full x| ≤ 2 ∧ |other i x| ≤ 2 ∧ |other i x-1| ≤ 5*b ∧
      |h i x| ≤ 1 ∧ |t i x| ≤ 2 ∧ ‖e i x‖ = 1 ∧
      b • P i x = scaled b (full x) (other i x) (h i x) (t i x) (Y x) (d i x) (e i x)) :
    |b^2*(2*kinetic μ P) - probe μ Y h| ≤ 54*b := by
  have one (i : Fin 2) :
      |b^2*(∫ x, ‖P i x‖^2 ∂μ) - ∫ x, (h i x)^2*(Y x)^2 ∂μ| ≤
          b*(3*(∫ x, ‖d i x‖^2 ∂μ)+15) := by
    have him : Integrable (fun x => b^2 * ‖P i x‖^2 - (h i x)^2*(Y x)^2) μ :=
      ((hP i).const_mul (b^2)).sub (hhY i)
    have habs : |b^2*(∫ x, ‖P i x‖^2 ∂μ) - ∫ x, (h i x)^2*(Y x)^2 ∂μ| ≤
        ∫ x, |b^2 * ‖P i x‖^2 - (h i x)^2*(Y x)^2| ∂μ := by
      rw [← integral_const_mul, ← integral_sub ((hP i).const_mul (b^2)) (hhY i)]
      exact abs_integral_le_integral_abs
    have hma : Integrable (fun x => b*(3*‖d i x‖^2+15*(Y x)^2)) μ :=
      (((hd i).const_mul 3).add (hY.const_mul 15)).const_mul b
    have hle : (∫ x, |b^2 * ‖P i x‖^2 - (h i x)^2*(Y x)^2| ∂μ) ≤
        ∫ x, b*(3*‖d i x‖^2+15*(Y x)^2) ∂μ := by
      apply integral_mono_ae him.abs hma
      filter_upwards [data i] with x hx
      rcases hx with ⟨hf, ho, hw, hh, ht, he, hform⟩
      have hlead : ‖leading (h i x) (Y x) (e i x)‖ ≤ |Y x| := by
        rw [leading, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, he, mul_one]
        exact mul_le_of_le_one_left (abs_nonneg _) hh
      have er := sq_norm_error (p := b • P i x) (l := leading (h i x) (Y x) (e i x))
        hb.le hb' (norm_nonneg (d i x)) (abs_nonneg (Y x)) hlead
        (by rw [hform]; exact local_difference _ _ hb.le hb' hf ho hw hh ht he.le)
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, leading_sq he, sq_abs] at er
      exact er
    calc
      _ ≤ _ := habs.trans hle
      _ = _ := by
        rw [integral_const_mul, integral_add ((hd i).const_mul 3) (hY.const_mul 15),
          integral_const_mul, integral_const_mul, mass]
        ring
  have hfinish := abs_add_le
    (b^2*(∫ x, ‖P 0 x‖^2 ∂μ)-∫ x, (h 0 x)^2*(Y x)^2 ∂μ)
    (b^2*(∫ x, ‖P 1 x‖^2 ∂μ)-∫ x, (h 1 x)^2*(Y x)^2 ∂μ)
  rw [Fin.sum_univ_two] at hgrad
  unfold kinetic probe
  simp only [Fin.sum_univ_two]
  calc
    _ = |(b^2*(∫ x, ‖P 0 x‖^2 ∂μ)-∫ x, (h 0 x)^2*(Y x)^2 ∂μ) +
          (b^2*(∫ x, ‖P 1 x‖^2 ∂μ)-∫ x, (h 1 x)^2*(Y x)^2 ∂μ)| := by congr 1; ring
    _ ≤ _ := hfinish
    _ ≤ _ := (add_le_add (one 0) (one 1)).trans (by nlinarith [mul_le_mul_of_nonneg_left hgrad hb.le])

#print axioms two_particle_remainder
end
end HFKinetic

