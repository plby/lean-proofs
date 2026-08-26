import ErdosProblems.Erdos73.OddPathProjection
import ErdosProblems.Erdos73.MatchingComparison
import ErdosProblems.Erdos556.TutteBerge

/-! The odd-path packing hypothesis gives the doubled-graph matching barrier. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}

theorem oddTerminalPacking_of_large_auxMatching {N : Finset (Sym2 (OddPathVertex A))}
    (hN : EdgeMatching (oddPathAuxiliary G A) N) {k : ℕ}
    (hk : (oddPathBaseMatching A).card + k ≤ N.card) : HasOddTerminalPathPacking G A k := by
  obtain ⟨P, hP, hdis⟩ := exists_disjoint_augmentingPaths (oddPathBaseMatching_isMatching G A) hN hk
  choose Q hQ hsrc htgt hsub using fun i => exists_oddTerminalPath_of_augmenting (hP i)
  refine ⟨Q, hQ, ?_⟩
  intro i j hij
  exact (oddPathAugmenting_projection_disjoint (hP j) (hdis hij)).mono (hsub i) (hsub j)

open scoped Classical in
theorem exists_oddPathMatchingBarrier {k : ℕ}
    (hno : ¬ HasOddTerminalPathPacking G A k) :
    ∃ W : Finset (OddPathVertex A),
      W.card + A.card + 2 ≤
        (((⊤ : (oddPathAuxiliary G A).Subgraph).deleteVerts
          (W : Set (OddPathVertex A))).coe).oddComponents.ncard + 2 * k := by
  obtain ⟨N, hN, _, W, hW⟩ := tutte_berge_certificate (oddPathAuxiliary G A)
  have hbound : N.card < (oddPathBaseMatching A).card + k := by
    by_contra hbad
    apply hno
    apply oddTerminalPacking_of_large_auxMatching (N := N)
    · convert hN using 1
    · omega
  have hbase := oddPathBaseMatching_card_add A
  have hverts := oddPathAuxiliary_card A
  rw [← Fintype.card_eq_nat_card] at hW
  have hWcoe : (W.toFinset : Set (OddPathVertex A)) = W := by
    ext x
    exact Set.mem_toFinset
  have hcount := congrArg (fun S : Set (OddPathVertex A) =>
    (((⊤ : (oddPathAuxiliary G A).Subgraph).deleteVerts S).coe).oddComponents.ncard) hWcoe
  refine ⟨W.toFinset, ?_⟩
  simp only [Set.toFinset_card, Fintype.card_eq_nat_card,
    Nat.card_coe_set_eq]
  omega

end Erdos73
