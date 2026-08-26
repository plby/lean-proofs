import ErdosProblems.Erdos1148.ModularOpenThickening

/-! # Uniform right-neighborhoods for compact subsets of open modular sets -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups Topology

theorem exists_compact_modular_right_thickening {K U : Set ModularOrbitSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ u : SL(2, ℝ), EntryCloseOne η u → modularRightTranslate u x ∈ U := by
  let A := (fun p : SL(2, ℝ) × ModularOrbitSpace => modularRightTranslate p.1 p.2) ⁻¹' U
  have hpre : A ∈ 𝓝 (1 : SL(2, ℝ)) ×ˢ 𝓝ˢ K := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    rw [← nhds_prod_eq]
    apply continuous_modularRightTranslate_joint.continuousAt.preimage_mem_nhds
    simpa only [modularRightTranslate_one, id_eq] using hU.mem_nhds (hKU hx)
  obtain ⟨W, hW, V, hV, hWV⟩ := Filter.mem_prod_iff.mp hpre
  obtain ⟨η, hη, hηW⟩ := exists_entryCloseOne_subset_nhds_one hW
  refine ⟨η, hη, ?_⟩
  intro x hx u hu
  exact hWV (show (u, x) ∈ W ×ˢ V from ⟨hηW hu, subset_of_mem_nhdsSet hV hx⟩)

end Erdos1148.DukeArithmetic
