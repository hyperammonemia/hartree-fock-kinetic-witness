import RadialConfiguration
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Spatial convolution on the two-electron configuration space seen as an
integral of L² translations. This gives norm convergence of the wave and
each of its six weak derivatives under the same smoothing procedure. -/
noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace MollifyGraph
open RadialConfiguration

def shifts : C(Config,C(Config,Config)) :=
  (⟨fun z : Config × Config => z.1+z.2, continuous_fst.add continuous_snd⟩ :
    C(Config × Config,Config)).curry

theorem shift_preserving (t : Config) : MeasurePreserving (shifts t) volume volume :=
  measurePreserving_add_left volume t

def translation (u : Wave) (t : Config) : Wave :=
  Lp.compMeasurePreserving (shifts t) (shift_preserving t) u

theorem translation_continuous (u : Wave) : Continuous (translation u) :=
  continuous_const.compMeasurePreservingLp shifts.continuous shift_preserving (by norm_num)

theorem translation_zero (u : Wave) : translation u 0 = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving u (shift_preserving 0)] with x hx
  simpa [translation,shifts] using hx

def mollify (φ : ContDiffBump (0 : Config)) (u : Wave) : Wave :=
  ((φ.normed volume) ⋆[lsmul ℝ ℝ, volume] translation u) 0

theorem norm_convergence (φ : ℕ → ContDiffBump (0 : Config))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (u : Wave) :
    Tendsto (fun n => mollify (φ n) u) atTop (𝓝 u) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ:=volume)
    hφ (translation_continuous u) 0
  rw [translation_zero] at h
  exact h

theorem weak_components_converge (φ : ℕ → ContDiffBump (0 : Config))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (u : Wave) (d : Fin 2 → Fin 3 → Wave) :
    Tendsto (fun n => (mollify (φ n) u,fun p i => mollify (φ n) (d p i))) atTop
      (𝓝 (u,d)) := by
  apply (norm_convergence φ hφ u).prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro p
  exact tendsto_pi_nhds.mpr (fun i => norm_convergence φ hφ (d p i))

#print axioms norm_convergence
#print axioms weak_components_converge
end MollifyGraph
