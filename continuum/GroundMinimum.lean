import FormAttainment
import Mathlib.Analysis.Real.Sqrt

/-! Attainment of a physical Rayleigh infimum on a graph domain. The injection
J measures physical mass. The complete norm on D controls all form components. -/
noncomputable section
namespace GroundMinimum
variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem ground_state (J : D →L[ℝ] H) (inj : Function.Injective J) (mass : ∀ u, ‖J u‖ ≤ ‖u‖)
    (q : D → ℝ) (E : ℝ) (hE : E ≤ 0) (p : Seminorm ℝ D) (cont : Continuous p)
    (form : ∀ u, (p u)^2 = q u-E*‖J u‖^2)
    (L : D →L[ℝ] ℝ) (g : D) (hg : L g=1) (c K γ : ℝ)
    (hc : 0<c) (hK : 0≤K) (hγ : 0<γ)
    (closedBound : ∀ u, c*‖u‖^2 ≤ q u+K*‖J u‖^2)
    (gap : ∀ u, L u=0 → γ*‖J u‖^2 ≤ q u)
    (near : ∀ ε : ℝ, 0<ε → ∃ u, ‖J u‖=1 ∧ q u<E+ε) :
    ∃ w : D, ‖J w‖=1 ∧ q w=E ∧ ∀ u, ‖J u‖=1 → q w≤q u := by
  let C := Real.sqrt ((1+K/γ)/c)
  have Cpos : 0<C := Real.sqrt_pos.2 (div_pos (add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg hK hγ.le)) hc)
  have Csq : C^2=(1+K/γ)/c := Real.sq_sqrt (by positivity)
  have coerc (u : D) (hu : L u=0) : ‖u‖ ≤ C*p u := by
    have qe : q u ≤ (p u)^2 := by nlinarith only [form u,mul_nonpos_of_nonpos_of_nonneg hE (sq_nonneg ‖J u‖)]
    have gm : ‖J u‖^2 ≤ (p u)^2/γ :=
      (le_div_iff₀ hγ).2 (by simpa only [mul_comm] using (gap u hu).trans qe)
    have sq : ‖u‖^2 ≤ (C*p u)^2 := by
      rw [mul_pow,Csq]
      have bound := (closedBound u).trans (add_le_add qe (mul_le_mul_of_nonneg_left gm hK))
      calc
        _ ≤ ((p u)^2+K*((p u)^2/γ))/c := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using bound)
        _ = _ := by ring
    exact le_of_sq_le_sq sq (mul_nonneg Cpos.le (apply_nonneg p u))
  have pn (t : ℝ) (ht : 0<t) : ∃ u : D, ‖u‖=1 ∧ p u<t := by
    obtain ⟨u,hu,he⟩ := near (t^2) (sq_pos_of_pos ht)
    have hn : 1 ≤ ‖u‖ := hu ▸ mass u
    have hp0 := apply_nonneg p u
    have hpu : p u<t := by have h := form u; rw [hu] at h; nlinarith
    have hnorm : 0<‖u‖ := lt_of_lt_of_le zero_lt_one hn
    refine ⟨‖u‖⁻¹ • u,?_,?_⟩
    · simp [norm_smul,hnorm.ne']
    · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm, ← div_eq_inv_mul]
      apply (div_lt_iff₀ hnorm).2
      exact hpu.trans_le (by simpa using mul_le_mul_of_nonneg_left hn ht.le)
  obtain ⟨u,hu,hzero⟩ := FormAttainment.attained_zero p cont L g hg C Cpos coerc pn
  have hju : J u ≠ 0 := by
    intro h
    have hu0 := inj (h.trans J.map_zero.symm)
    simp [hu0] at hu
  have hpos : 0<‖J u‖ := norm_pos_iff.mpr hju
  let w : D := ‖J u‖⁻¹ • u
  have hw : ‖J w‖=1 := by simp [w,norm_smul,hpos.ne']
  have hp : p w=0 := by simp [w,map_smul_eq_mul,hzero]
  have e : q w=E := by have h := form w; rw [hp,hw] at h; linarith
  refine ⟨w,hw,e,?_⟩
  intro v hv
  have h := form v
  rw [hv] at h
  nlinarith only [h,sq_nonneg (p v),e]

#print axioms ground_state
end GroundMinimum
