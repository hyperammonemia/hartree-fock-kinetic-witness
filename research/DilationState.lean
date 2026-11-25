import DilationWeak
import SingletKinetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory MeasureTheory.Measure FinitePotential
namespace HFKinetic
noncomputable section

instance configurationVolumeHaar : IsAddHaarMeasure (volume : Measure DilationConfig) := by
  change IsAddHaarMeasure ((volume : Measure Position).prod volume)
  infer_instance

theorem dilated_memLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure DilationConfig} [IsAddHaarMeasure μ] (n : ℕ) {l : ℝ} (hl : 0 < l)
    {Y : DilationConfig → G} (hY : MemLp Y 2 μ) : MemLp (dilatedField l n Y) 2 μ := by
  have hs : l⁻¹ ≠ 0 := inv_ne_zero hl.ne'
  let t : DilationConfig ≃ᵐ DilationConfig :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 hs).unit).toMeasurableEquiv
  have hm : MemLp Y 2 (Measure.map (fun x : DilationConfig => l⁻¹ • x) μ) := by
    rw [map_addHaar_smul μ hs]
    exact hY.smul_measure ENNReal.ofReal_ne_top
  have hi : MemLp (Y ∘ t) 2 μ := t.memLp_map_measure_iff.mp hm
  exact hi.const_smul (l⁻¹^n)

theorem weakAxis_iff_complex (Y d : DilationConfig → ℝ) (v : DilationConfig) :
    WeakAxis volume Y d v ↔ ContinuumHamiltonian.IsWeakPartial
      (fun x => (Y x : ℂ)) (fun x => (d x : ℂ)) v := by
  constructor
  · intro h φ hφ hs
    simpa only [← Complex.ofReal_mul,integral_complex_ofReal,← Complex.ofReal_neg] using
      congrArg (fun a : ℝ => (a:ℂ)) (h φ hφ hs)
  · intro h φ hφ hs
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_mul,integral_complex_ofReal,← Complex.ofReal_neg] using h φ hφ hs

theorem weak_dilated_spin_axis (Y : DilationConfig → ℝ) (G : Fin 2 → DilationConfig → Position)
    (i : Fin 2) (j : Fin 3) {l : ℝ} (hl : 0 < l)
    (weak : ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.IsWeakPartial (fun x => ((dilatedField l 3 Y x : ℝ) : ℂ))
      (fun x => (dilatedField l 4 (G i) x j : ℂ)) (ContinuumHamiltonian.axis i j) := by
  apply (weakAxis_iff_complex (dilatedField l 3 Y)
    (dilatedField l 4 (fun x => G i x j)) (ContinuumHamiltonian.axis i j)).mp
  exact physical_weak_derivative volume Y (fun x => G i x j) _ hl
    ((weakAxis_iff_complex Y _ _).mpr weak)

def dilatedSinglet (l : ℝ) (hl : 0 < l) (Y : DilationConfig → ℝ)
    (G : Fin 2 → DilationConfig → Position) (hy : MemLp Y 2 volume) (hg : ∀ i, MemLp (G i) 2 volume)
    (weak : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) : ContinuumHamiltonian.State :=
  singletState (dilatedField l 3 Y) (fun i => dilatedField l 4 (G i)) (dilated_memLp 3 hl hy)
    (fun i => dilated_memLp 4 hl (hg i)) (fun i j => weak_dilated_spin_axis Y G i j hl (weak i j))

theorem dilatedSinglet_kinetic (l : ℝ) (hl : 0 < l) (Y : DilationConfig → ℝ)
    (G : Fin 2 → DilationConfig → Position) (hy : MemLp Y 2 volume) (hg : ∀ i, MemLp (G i) 2 volume)
    (weak : ∀ i j, ContinuumHamiltonian.IsWeakPartial (fun x => (Y x : ℂ)) (fun x => (G i x j : ℂ))
      (ContinuumHamiltonian.axis i j)) :
    ContinuumHamiltonian.kinetic (dilatedSinglet l hl Y G hy hg weak) =
      l⁻¹^2 * ContinuumHamiltonian.kinetic (singletState Y G hy hg weak) := by
  unfold dilatedSinglet
  rw [singletState_kinetic,singletState_kinetic]
  exact physical_kinetic volume G hl

#print axioms dilated_memLp
#print axioms weak_dilated_spin_axis
#print axioms dilatedSinglet_kinetic
end
end HFKinetic
