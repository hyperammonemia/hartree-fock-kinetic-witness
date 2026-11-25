import SlaterGeometry
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped ComplexConjugate

namespace CoordinateSlater

variable {X : Type*} [MeasurableSpace X]

noncomputable def wave (c : ℂ) (a b : X → ℂ) (z : X × X) : ℂ :=
  c*(a z.1*b z.2-b z.1*a z.2)

private noncomputable def pair (f g : X → ℂ) (x : X) := conj (f x)*g x

private theorem pair_int (μ : Measure X) (a b : Lp ℂ 2 μ) : Integrable (pair a b) μ := by
  simpa only [pair,← RCLike.inner_apply'] using L2.integrable_inner (𝕜:=ℂ) a b

/-- Configuration space may contain both position and a discrete spin label.
    All four orbitals are genuine, arbitrary complex L2 vectors. -/
theorem integral_gram (μ : Measure X) [SFinite μ] (c : ℂ) (hc : conj c*c=1/2)
    (a b x y : Lp ℂ 2 μ) :
    ∫ z : X × X, conj (wave c a b z)*wave c x y z ∂(μ.prod μ) =
      inner ℂ a x*inner ℂ b y-inner ℂ a y*inner ℂ b x := by
  let ax := pair a x; let ay := pair a y; let bx := pair b x; let by' := pair b y
  have h1 : Integrable (fun z : X × X => ax z.1*by' z.2) (μ.prod μ) :=
    (pair_int μ a x).mul_prod (pair_int μ b y)
  have h2 : Integrable (fun z : X × X => ay z.1*bx z.2) (μ.prod μ) :=
    (pair_int μ a y).mul_prod (pair_int μ b x)
  have h3 : Integrable (fun z : X × X => bx z.1*ay z.2) (μ.prod μ) :=
    (pair_int μ b x).mul_prod (pair_int μ a y)
  have h4 : Integrable (fun z : X × X => by' z.1*ax z.2) (μ.prod μ) :=
    (pair_int μ b y).mul_prod (pair_int μ a x)
  have h12 : Integrable (fun z : X × X => ax z.1*by' z.2-ay z.1*bx z.2) (μ.prod μ) := h1.sub h2
  have h123 : Integrable (fun z : X × X => ax z.1*by' z.2-ay z.1*bx z.2-bx z.1*ay z.2) (μ.prod μ) :=
    h12.sub h3
  have point (z : X × X) :
      conj (wave c a b z)*wave c x y z = (conj c*c)*
        (ax z.1*by' z.2-ay z.1*bx z.2-bx z.1*ay z.2+by' z.1*ax z.2) := by
    simp only [wave,ax,ay,bx,by',pair,map_mul,map_sub]
    ring
  simp_rw [point]
  rw [integral_const_mul,integral_add h123 h4,integral_sub h12 h3,integral_sub h1 h2,
    integral_prod_mul,integral_prod_mul,integral_prod_mul,integral_prod_mul,hc]
  simp only [L2.inner_def,RCLike.inner_apply',ax,ay,bx,by',pair]
  ring

/-- The abstract antisymmetric tensor and its coordinate determinant have
    exactly the same transition amplitude. -/
theorem integral_eq_tensor_inner (μ : Measure X) [SFinite μ] (c : ℂ) (hc : conj c*c=1/2)
    (a b x y : Lp ℂ 2 μ) :
    ∫ z : X × X, conj (wave c a b z)*wave c x y z ∂(μ.prod μ) =
      inner ℂ (SlaterGeometry.slater a b) (SlaterGeometry.slater x y) :=
  (integral_gram μ c hc a b x y).trans (SlaterGeometry.inner_slater a b x y).symm

/-- Contracting a physical determinant against an occupied spin orbital
    recovers its companion. This is a component of the form-domain argument. -/
theorem partial_contraction (μ : Measure X) (c : ℂ) (u v w : Lp ℂ 2 μ) (x : X) :
    (∫ y, conj (w y) * wave c u v (x,y) ∂μ) =
      c*(u x * inner ℂ w v - v x * inner ℂ w u) := by
  have p (y : X) : conj (w y) * wave c u v (x,y) =
      (c*u x)*pair w v y - (c*v x)*pair w u y := by
    simp only [wave,pair]
    ring
  have ha : Integrable (fun y => (c*u x)*pair w v y) μ := (pair_int μ w v).const_mul _
  have hb : Integrable (fun y => (c*v x)*pair w u y) μ := (pair_int μ w u).const_mul _
  simp_rw [p]
  rw [integral_sub ha hb,integral_const_mul,integral_const_mul]
  simp only [L2.inner_def,RCLike.inner_apply',pair]
  ring

theorem recover_first (μ : Measure X) (c : ℂ) (u v : Lp ℂ 2 μ)
    (hvv : inner ℂ v v=1) (hvu : inner ℂ v u=0) (x : X) :
    (∫ y, conj (v y) * wave c u v (x,y) ∂μ) = c*u x := by
  rw [partial_contraction,hvv,hvu]
  ring

end CoordinateSlater
