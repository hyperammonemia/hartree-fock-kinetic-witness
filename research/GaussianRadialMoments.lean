import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Gaussian radial moments used by the quadratic and quartic double excitations. -/
noncomputable section
open Set MeasureTheory
namespace GaussianRadialMoments
abbrev X := EuclideanSpace ℝ (Fin 3)

def I (n : ℕ) := ∫ r in Ioi (0:ℝ), r^n * Real.exp (-(1/2:ℝ)*r^2)

theorem gamma_value (n : ℕ) :
    I n = (1/2:ℝ)^(-((n:ℝ)+1)/2)*(1/2)*Real.Gamma (((n:ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=(n:ℝ)) (b:=1/2)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (by norm_num)
  simpa [I, Real.rpow_natCast] using h

theorem recurrence (n : ℕ) : I (n+2) = ((n:ℝ)+1)*I n := by
  rw [gamma_value,gamma_value]
  push_cast
  have hp : 0 < ((n:ℝ)+1)/2 := by positivity
  have ea : ((n:ℝ)+2+1)/2=((n:ℝ)+1)/2+1 := by ring
  have eb : -((n:ℝ)+2+1)/2= -((n:ℝ)+1)/2+(-1) := by ring
  rw [ea,eb, Real.Gamma_add_one hp.ne', Real.rpow_add (by norm_num : (0:ℝ)<1/2)]
  norm_num only [Real.rpow_neg_one, inv_div, div_one]
  ring

theorem radial (f : ℝ → ℝ) :
    (∫ x : X, f ‖x‖) = 4*Real.pi*(∫ r in Ioi (0:ℝ), r^2*f r) := by
  rw [integral_fun_norm_addHaar volume f]
  have hvol : (volume : Measure X).real (Metric.ball 0 1)=Real.pi*4/3 := by
    simp [Measure.real,EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  rw [hvol]
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
  ring

def ordinary (k : ℕ) := ∫ z : X, ‖z‖^(2*k)*Real.exp (-(1/2:ℝ)*‖z‖^2)
def weighted (k : ℕ) := ∫ z : X, (‖z‖^(2*k)*Real.exp (-(1/2:ℝ)*‖z‖^2))/‖z‖

theorem ordinary_value (k : ℕ) : ordinary k = 4*Real.pi*I (2*k+2) := by
  unfold ordinary
  rw [radial (fun r => r^(2*k)*Real.exp (-(1/2:ℝ)*r^2))]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  simp [pow_add, mul_comm, mul_assoc]

theorem weighted_value (k : ℕ) : weighted k = 4*Real.pi*I (2*k+1) := by
  unfold weighted
  rw [radial (fun r => r^(2*k)*Real.exp (-(1/2:ℝ)*r^2)/r)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hp : r ≠ 0 := (mem_Ioi.mp hr).ne'
  simp [pow_add]
  field_simp

theorem ordinary_step (k : ℕ) : ordinary (k+1) = (2*k+3:ℝ)*ordinary k := by
  rw [ordinary_value,ordinary_value]
  have he : 2*(k+1)+2 = (2*k+2)+2 := by omega
  rw [he,recurrence]
  push_cast; ring

theorem weighted_step (k : ℕ) : weighted (k+1) = (2*k+2:ℝ)*weighted k := by
  rw [weighted_value,weighted_value]
  have he : 2*(k+1)+1 = (2*k+1)+2 := by omega
  rw [he,recurrence]
  push_cast; ring

#print axioms ordinary_step
#print axioms weighted_step
end GaussianRadialMoments

