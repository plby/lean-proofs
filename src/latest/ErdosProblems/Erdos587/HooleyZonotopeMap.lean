import ErdosProblems.Erdos587.HooleyZonotope

/-! # Linear images and reindexing of centered zonotopes -/

open scoped BigOperators

namespace Erdos587.CFP

lemma deltaZonotope_linear_image {ι : Type*} [Fintype ι] {d n : ℕ}
    (v : ι → Fin d → ℝ) (q : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    deltaZonotope (q ∘ v) = q '' deltaZonotope v := by
  have hsum (θ : ι → ℝ) :
      Fintype.linearCombination ℝ (q ∘ v) θ = q (Fintype.linearCombination ℝ v θ) := by
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, Function.comp_apply]
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨Fintype.linearCombination ℝ v θ, ⟨θ, hθ, rfl⟩, (hsum θ).symm⟩
  · rintro ⟨y, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨θ, hθ, hsum θ⟩

lemma deltaZonotope_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (v : κ → Fin d → ℝ) (e : ι ≃ κ) : deltaZonotope (v ∘ e) = deltaZonotope v := by
  have hsum (θ : ι → ℝ) :
      Fintype.linearCombination ℝ v (θ ∘ e.symm) =
        Fintype.linearCombination ℝ (v ∘ e) θ := by
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    simpa only [Function.comp_apply, e.symm_apply_apply] using
      (Equiv.sum_comp e (fun j => θ (e.symm j) • v j)).symm
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ ∘ e.symm, ⟨fun j => hθ.1 _, fun j => hθ.2 _⟩, hsum θ⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨θ ∘ e, ⟨fun i => hθ.1 _, fun i => hθ.2 _⟩, ?_⟩
    rw [← hsum]
    congr 1
    funext j
    simp only [Function.comp_apply, e.apply_symm_apply]

end Erdos587.CFP

namespace Erdos587.GeneralizedAP

lemma delta_intLinearMapRealExtension_comp {d n k : ℕ}
    (q : (Fin d → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (p : (Fin n → ℤ) →ₗ[ℤ] (Fin k → ℤ)) :
    intLinearMapRealExtension (p.comp q) =
      (intLinearMapRealExtension p).comp (intLinearMapRealExtension q) := by
  apply LinearMap.ext
  intro x
  rw [show x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) from pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [show Pi.single i (1 : ℝ) = intCastVec (Pi.single i (1 : ℤ)) by
    ext j
    simp [intCastVec, Pi.single_apply]]
  simp only [intLinearMapRealExtension_intCastVec, LinearMap.comp_apply]

lemma delta_intLinearMapRealExtension_id {d : ℕ} :
    intLinearMapRealExtension (LinearMap.id : (Fin d → ℤ) →ₗ[ℤ] _) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [show x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) from pi_eq_sum_univ' x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [show Pi.single i (1 : ℝ) = intCastVec (Pi.single i (1 : ℤ)) by
    ext j
    simp [intCastVec, Pi.single_apply]]
  simp only [intLinearMapRealExtension_intCastVec, LinearMap.id_apply]

end Erdos587.GeneralizedAP
