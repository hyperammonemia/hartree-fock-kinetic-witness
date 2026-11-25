import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace SlaterFormDomain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem invert_rows (F : Submodule ℂ H) (u v : H) (a b c d : ℂ)
    (hdet : a*d-b*c ≠ 0) (h1 : a • u+b • v ∈ F) (h2 : c • u+d • v ∈ F) : u ∈ F ∧ v ∈ F := by
  have rowU : d • (a • u+b • v)-b • (c • u+d • v) = (a*d-b*c) • u := by
    simp only [smul_add,smul_smul,sub_smul]
    rw [mul_comm d a,mul_comm d b]
    abel
  have rowV : a • (c • u+d • v)-c • (a • u+b • v) = (a*d-b*c) • v := by
    simp only [smul_add,smul_smul,sub_smul]
    rw [mul_comm c a,mul_comm c b]
    abel
  constructor
  · apply (F.smul_mem_iff hdet).mp
    rw [← rowU]
    exact F.sub_mem (F.smul_mem _ h1) (F.smul_mem _ h2)
  · apply (F.smul_mem_iff hdet).mp
    rw [← rowV]
    exact F.sub_mem (F.smul_mem _ h2) (F.smul_mem _ h1)

/-- The finite-energy space may fail to be closed in the L2 norm.
    Weak tests from any dense set suffice to recover both generating orbitals. -/
theorem orbitals_in_form_domain (F : Submodule ℂ H) (T : Set H) (ht : Dense T) (u v : H)
    (hu : inner ℂ u u=1) (hv : inner ℂ v v=1) (huv : inner ℂ u v=0)
    (hcontract : ∀ w ∈ T, inner ℂ w v • u - inner ℂ w u • v ∈ F) :
    u ∈ F ∧ v ∈ F := by
  have hvu : inner ℂ v u=0 := by rw [← inner_conj_symm v u,huv]; simp
  let D (w : H × H) := inner ℂ w.1 v * (-inner ℂ w.2 u) - (-inner ℂ w.1 u)*inner ℂ w.2 v
  have hcont : Continuous D := by dsimp [D]; fun_prop
  have hopen : IsOpen {w : H × H | D w ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hne : ({w : H × H | D w ≠ 0} : Set (H × H)).Nonempty := by
    refine ⟨(v,u),?_⟩
    change inner ℂ v v * (-inner ℂ u u) - (-inner ℂ v u)*inner ℂ u v ≠ 0
    rw [hv,hu,hvu,huv]
    norm_num
  obtain ⟨⟨w,t⟩,hT,hD⟩ := (ht.prod ht).exists_mem_open hopen hne
  apply invert_rows F u v (inner ℂ w v) (-inner ℂ w u) (inner ℂ t v) (-inner ℂ t u) hD
  · simpa only [neg_smul,sub_eq_add_neg] using hcontract w hT.1
  · simpa only [neg_smul,sub_eq_add_neg] using hcontract t hT.2

end SlaterFormDomain
