import ErdosProblems.Erdos547.ForestSeparator
import ErdosProblems.Erdos547.HullSeeds
import ErdosProblems.Erdos547.TreeAttachments

/-!
# A small rooted separator with at most two attachments per component
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_two_attachment_separator {U : Type*} [Fintype U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : U) (q : ℕ) (hq : 1 ≤ q) :
    ∃ S H : Finset U, r ∈ S ∧ S ⊆ H ∧ (T.induce (H : Set U)).Connected ∧
      q * S.card ≤ 2 * (Fintype.card U + q) ∧
      (∀ u ∈ H, u ∉ S → degreeIn T H u = 2) ∧
      ∀ C : Finset U, Disjoint C S → (T.induce (C : Set U)).Connected →
        C.card ≤ 2 * q - 1 ∧ (S.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 2 := by
  classical
  obtain ⟨W, hr, hcount, hsmall⟩ := exists_rooted_tree_separator T hT r q hq
  obtain ⟨S, H, hWS, hSH, hScard, hH, hdeg⟩ :=
    exists_hull_seed_extension T hT W ⟨r, hr⟩
  refine ⟨S, H, hWS hr, hSH, hH, ?_, hdeg, ?_⟩
  · have hh := Nat.mul_le_mul_left q hScard
    nlinarith only [hh, hcount]
  · intro C hCS hC
    exact ⟨hsmall C (hCS.mono_right hWS) hC,
      card_cut_neighbours_le_two T hT.isAcyclic C H S hC hH hSH hCS
        (fun u hu hn ↦ (hdeg u hu hn).le)⟩

end Erdos547

#print axioms Erdos547.exists_two_attachment_separator
