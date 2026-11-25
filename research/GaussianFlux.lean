import ExteriorTail
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The squared-marginal barrier and its Gaussian radial flux. -/
open Set Filter
open scoped Topology
noncomputable section
namespace HFExterior

def radialJacobian (r : ℝ) : ℝ := r^2 * Real.exp (-r^2)
def densityBarrier (q α r : ℝ) : ℝ :=
  Real.exp (q^2 + 3/2 * Real.log Real.pi + 2*α*(Real.log q-Real.log r))

theorem jacobian_pos {r : ℝ} (hr : 0 < r) : 0 < radialJacobian r :=
  mul_pos (sq_pos_of_pos hr) (Real.exp_pos _)

theorem densityBarrier_pos (q α r : ℝ) : 0 < densityBarrier q α r := Real.exp_pos _

theorem gaussian_square_barrier (q α r : ℝ) :
    gaussianRadial r^2 * densityBarrier q α r = radialBarrier q α r ^ 2 := by
  simp only [gaussianRadial,radialBarrier,densityBarrier,pow_two,← Real.exp_add]
  congr 1
  ring

theorem density_boundary (q α : ℝ) : gaussianRadial q ^ 2 * densityBarrier q α q = 1 := by
  rw [gaussian_square_barrier,barrier_boundary]
  norm_num

theorem densityBarrier_hasDerivAt {q α r : ℝ} (hr : 0 < r) :
    HasDerivAt (densityBarrier q α) ((-(2*α)/r)*densityBarrier q α r) r := by
  have hl : HasDerivAt (fun t : ℝ => q^2+3/2*Real.log Real.pi+2*α*(Real.log q-Real.log t))
      (-(2*α)/r) r := by
    apply ((hasDerivAt_const r (q^2+3/2*Real.log Real.pi)).add
      (((hasDerivAt_const r (Real.log q)).sub (Real.hasDerivAt_log hr.ne')).const_mul (2*α))).congr_deriv
    simp [div_eq_mul_inv]
    <;> ring
  apply hl.exp.congr_deriv
  exact mul_comm _ _

private theorem gaussianExp_deriv (r : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t^2)) ((-2*r)*Real.exp (-r^2)) r := by
  have hd : HasDerivAt (fun t : ℝ => -t^2) (-2*r) r := by
    apply (((hasDerivAt_id r).pow 2).neg).congr_deriv
    simp
    <;> ring
  exact hd.exp.congr_deriv (mul_comm _ _)

theorem density_flux_deriv {q α r : ℝ} (hr : 0 < r) :
    deriv (fun t => radialJacobian t * deriv (densityBarrier q α) t) r =
      4 * radialJacobian r * densityBarrier q α r *
        (α-α*(1-2*α)/(2*r^2)) := by
  let flux := fun t => (-(2*α))*t*Real.exp (-t^2)*densityBarrier q α t
  have hnear : (fun t => radialJacobian t * deriv (densityBarrier q α) t) =ᶠ[𝓝 r] flux := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    rw [(densityBarrier_hasDerivAt ht).deriv]
    dsimp [flux,radialJacobian]
    field_simp [(show 0 < t from ht).ne']
    <;> ring
  rw [hnear.deriv_eq]
  have h := ((((hasDerivAt_id r).const_mul (-(2*α))).mul (gaussianExp_deriv r)).mul
    (densityBarrier_hasDerivAt (q := q) (α := α) hr))
  change deriv (fun t => (-(2*α))*t*Real.exp (-t^2)*densityBarrier q α t) r = _
  rw [h.deriv]
  dsimp [radialJacobian]
  field_simp [hr.ne']
  <;> ring

theorem density_flux_supersolution {q α r V : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hα1 : 2*α ≤ 1) (hV : α ≤ V) :
    0 ≤ -deriv (fun t => radialJacobian t * deriv (densityBarrier q α) t) r/4 +
      radialJacobian r * V * densityBarrier q α r := by
  rw [density_flux_deriv hr]
  have hc : 0 ≤ α*(1-2*α)/(2*r^2) := by positivity
  have hp := (jacobian_pos hr).le
  have hB := (densityBarrier_pos q α r).le
  have hm := mul_nonneg (mul_nonneg hp hB) (show 0 ≤ V-α+α*(1-2*α)/(2*r^2) by linarith)
  linarith

theorem density_tail_from_ratio {q r a : ℝ} (hq0 : 100000 ≤ q) (hq1 : q ≤ 100001)
    (hr : Real.exp ((10 : ℝ)^18) ≤ r) (ha : 0 ≤ a)
    (hM : a/(gaussianRadial r)^2 ≤ densityBarrier q (1/10000000) r) :
    Real.sqrt a < gaussianRadial r/2 := by
  have hg : 0 < gaussianRadial r := Real.exp_pos _
  have hd := (div_le_iff₀ (sq_pos_of_pos hg)).mp hM
  rw [mul_comm (densityBarrier q _ r),gaussian_square_barrier] at hd
  have h := explicit_barrier_tail hq0 hq1 hr
  have hb := barrier_pos q (1/10000000) r
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ gaussianRadial r/2)).mp
  rw [Real.sq_sqrt ha]
  exact hd.trans_lt ((sq_lt_sq₀ hb.le (by positivity)).mpr h)

end HFExterior
