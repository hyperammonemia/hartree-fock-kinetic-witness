import ContinuumHamiltonian
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
noncomputable section
open MeasureTheory
namespace ContinuumHamiltonian

set_option maxHeartbeats 1400000

private theorem test_integrable {u : Config → ℂ} (hu : MemLp u 2 volume)
    {f : Config → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => u x * (f x : ℂ)) := by
  have hm : MemLp (fun x => (f x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hf).memLp_of_hasCompactSupport
      (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
  exact hu.integrable_mul hm

private def d (f : Config → ℝ) (v : Config) := fun x => (fderiv ℝ f x) v

private theorem d_cont {f : Config → ℝ} (hf : ContDiff ℝ 1 f) (v : Config) :
    Continuous (d f v) :=
  (hf.continuous_fderiv_apply one_ne_zero).comp
    (continuous_id.prodMk (continuous_const (y := v)))

private theorem d_mul {w φ : Config → ℝ} (hw : ContDiff ℝ 1 w) (hp : ContDiff ℝ 1 φ)
    (v x : Config) : d (w*φ) v x = w x * d φ v x + d w v x * φ x := by
  unfold d
  have h1 := (hw.differentiable one_ne_zero).differentiableAt (x := x)
  have h2 := (hp.differentiable one_ne_zero).differentiableAt (x := x)
  rw [fderiv_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [mul_comm (φ x)]

private def prodTest (u : Config → ℂ) (w : Config → ℝ) : Config → ℂ := fun x => u x * (w x : ℂ)

private theorem prod_assoc (a : Config → ℂ) (b c : Config → ℝ) :
    prodTest (prodTest a b) c = prodTest a (b*c) := by
  funext x
  simp [prodTest, mul_assoc]

private theorem prod_add (u v : Config → ℂ) (a : Config → ℝ) :
    prodTest (u+v) a = prodTest u a + prodTest v a := by
  funext x
  simp [prodTest, add_mul]

private theorem prod_dmul (u : Config → ℂ) (w φ : Config → ℝ)
    (hw : ContDiff ℝ 1 w) (hp : ContDiff ℝ 1 φ) (v : Config) :
    prodTest u (d (w*φ) v) = prodTest u (w*d φ v) + prodTest u (d w v*φ) := by
  funext x
  simp only [prodTest, d_mul hw hp, Complex.ofReal_add, mul_add, Pi.mul_apply, Pi.add_apply]

private theorem rearrange (a b c : ℂ) (h : a+b = -c) : a = -(c+b) := by
  linear_combination h

/-- The weak derivative of a wave component multiplied by a C¹ real weight. -/
theorem weakPartial_mul {u du : Config → ℂ} {v : Config}
    (hu : MemLp u 2 volume) (hdu : MemLp du 2 volume) (hd : IsWeakPartial u du v)
    (w : Config → ℝ) (hw : ContDiff ℝ 1 w) :
    IsWeakPartial (fun x => u x * (w x : ℂ))
      (fun x => du x * (w x : ℂ) + u x * ((fderiv ℝ w x v : ℝ) : ℂ)) v := by
  intro φ hp hc
  have A : Integrable (prodTest u (w*d φ v)) :=
    test_integrable hu (hw.continuous.mul (d_cont hp v))
      (HasCompactSupport.mul_left (HasCompactSupport.fderiv_apply ℝ hc v))
  have B : Integrable (prodTest u (d w v*φ)) :=
    test_integrable hu ((d_cont hw v).mul hp.continuous) (HasCompactSupport.mul_left hc)
  have C : Integrable (prodTest du (w*φ)) :=
    test_integrable hdu (hw.continuous.mul hp.continuous) (HasCompactSupport.mul_left hc)
  have h := hd (w*φ) (hw.mul hp) (HasCompactSupport.mul_left hc)
  change (∫ x, prodTest u (d (w*φ) v) x) = -(∫ x, prodTest du (w*φ) x) at h
  change (∫ x, prodTest (prodTest u w) (d φ v) x) =
    -(∫ x, prodTest (prodTest du w + prodTest u (d w v)) φ x)
  rw [prod_dmul u w φ hw hp v] at h
  simp only [Pi.add_apply] at h
  rw [integral_add A B] at h
  rw [prod_assoc, prod_add, prod_assoc, prod_assoc]
  simp only [Pi.add_apply]
  rw [integral_add C B]
  exact rearrange _ _ _ h

#print axioms weakPartial_mul
end ContinuumHamiltonian
