import Wikipedia.HopfProblem.DegreeCollapseNewAttachingCirclePlacement

/-!
# A single circle crossing gives the exact whole-level basin intersection count

The entire backward basin, not only the parametrized attaching image, is
carried onto the target circle. A unique target parameter in the forward
basin therefore makes the actual level intersection a singleton.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem unit_level_count_of_circle_placement {M X : Type*} [TopologicalSpace M]
    (F : Flow ℝ M) {f : M → ℝ} {a : ℝ} {p q : M}
    (P : {y : M // f y = a} ≃ {y : M // f y = a})
    (δ : X → {y : M // f y = a}) (z₀ : X)
    (hplacement : ∀ x, Tendsto (fun t => F t x.val) atBot (𝓝 p) ↔ P x ∈ range δ)
    (hsingle : ∀ z, Tendsto (fun t => F t (δ z).val) atTop (𝓝 q) ↔ z = z₀) :
    {x : {y : M // f y = a} | Tendsto (fun t => F t x.val) atBot (𝓝 p) ∧
      Tendsto (fun t => F t (P x).val) atTop (𝓝 q)}.ncard = 1 := by
  have heq : {x : {y : M // f y = a} | Tendsto (fun t => F t x.val) atBot (𝓝 p) ∧
      Tendsto (fun t => F t (P x).val) atTop (𝓝 q)} = {P.symm (δ z₀)} := by
    ext x
    constructor
    · rintro ⟨hx, hforward⟩
      obtain ⟨z, hz⟩ := (hplacement x).mp hx
      have hz0 : z = z₀ := (hsingle z).mp (hz.symm ▸ hforward)
      apply mem_singleton_iff.mpr
      apply P.injective
      rw [P.apply_symm_apply, ← hz, hz0]
    · intro hx
      rcases mem_singleton_iff.mp hx with rfl
      refine ⟨(hplacement _).mpr ⟨z₀, (P.apply_symm_apply _).symm⟩, ?_⟩
      rw [P.apply_symm_apply]
      exact (hsingle z₀).mpr rfl
  rw [heq]
  exact ncard_singleton _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
