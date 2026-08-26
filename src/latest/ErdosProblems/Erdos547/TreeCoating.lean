import ErdosProblems.Erdos547.CoatingPartition
import ErdosProblems.Erdos547.CoatingNumbers

/-!
# Uniform tree coating with all four shrub parts large

The padding parameter is integral.  The size bound is `(1+10*η)*n`;
no assertion of the sharper constant from the published coating lemma is used.
-/

namespace Erdos547

open SimpleGraph
open scoped SimpleGraph

universe u

open scoped Classical in
theorem eventually_tree_coating (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η) (hη : η ≤ 1 / 10) :
    ∃ K n₀ : ℕ, ∀ (U : Type u) [Fintype U] [DecidableEq U]
      (T : SimpleGraph U) [DecidableRel T.Adj] (hT : T.IsTree) (r : U),
      n₀ ≤ Fintype.card U →
      ∃ m ℓ : ℕ, ∃ P : FineTreePartition (coatedTree T r m) (coatingSeed r m 0) ℓ
          (coatedTreeColour (hT.coloringTwoOfVert r) r m),
        (coatedTree T r m).IsTree ∧ T ⊑ coatedTree T r m ∧ P.seeds.card ≤ K ∧
        (Fintype.card (CoatedVertex U m) : ℝ) ≤ (1 + 10 * η) * Fintype.card U ∧
        (ℓ : ℝ) ≤ ρ * Fintype.card (CoatedVertex U m) ∧
        ∀ i : Fin 2, η * Fintype.card U ≤ (P.nearVertices i).card ∧
          η * Fintype.card U ≤ (P.farVertices i).card := by
  classical
  obtain ⟨K, n₀, hnumbers⟩ := eventually_coating_numbers η ρ hρ hρη hη
  refine ⟨K, n₀, ?_⟩
  intro U instU instEq T instAdj hT r hn
  obtain ⟨m, ℓ, a, hℓ, hℓn, hK, hroom, hparts, ha, hsize, hsmall⟩ :=
    hnumbers (Fintype.card U) hn
  let col := hT.coloringTwoOfVert r
  have hr : col r = 0 := by
    apply Fin.ext
    change T.dist r r % 2 = 0
    simp
  obtain ⟨P, hseeds, hfour⟩ := exists_coating_partition_at_scale T hT col r hr m ℓ K a hℓ
    (by rw [card_coatedVertex]; exact hℓn) (by rw [card_coatedVertex]; exact hK) hroom hparts
  refine ⟨m, ℓ, P, coatedTree_isTree T hT r m, ⟨coatedTreeOldCopy T r m⟩, hseeds, ?_, ?_, ?_⟩
  · rw [card_coatedVertex]
    exact hsize
  · rw [card_coatedVertex]
    exact hsmall
  · intro i
    have hnear : (a : ℝ) ≤ (P.nearVertices i).card := by exact_mod_cast (hfour i).1
    have hfar : (a : ℝ) ≤ (P.farVertices i).card := by exact_mod_cast (hfour i).2
    exact ⟨ha.trans hnear, ha.trans hfar⟩

end Erdos547

#print axioms Erdos547.eventually_tree_coating
