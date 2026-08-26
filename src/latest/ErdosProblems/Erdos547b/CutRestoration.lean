/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6Dichotomy

/-! # Restore deleted graph edges and exceptional vertices in a disjoint cut -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoCutRestoration

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

theorem crossing_le_add_deleted (X Y : Finset V) (hXY : Disjoint X Y) :
    (G.interedges X Y).card ≤ (H.interedges X Y).card + (G.edgeFinset \ H.edgeFinset).card := by
  have hdiff : (G.interedges X Y \ H.interedges X Y).card ≤ (G.edgeFinset \ H.edgeFinset).card := by
    apply Finset.card_le_card_of_injOn (fun p : V × V => s(p.1, p.2))
    · intro p hp
      have hg := (SimpleGraph.mem_interedges_iff G).mp (Finset.mem_sdiff.mp hp).1
      apply Finset.mem_sdiff.mpr
      refine ⟨by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hg.2.2, ?_⟩
      intro he
      have hh : H.Adj p.1 p.2 := by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      exact (Finset.mem_sdiff.mp hp).2 ((SimpleGraph.mem_interedges_iff H).mpr ⟨hg.1, hg.2.1, hh⟩)
    · intro p hp r hr hpr
      have hp' := (SimpleGraph.mem_interedges_iff G).mp (Finset.mem_sdiff.mp hp).1
      have hr' := (SimpleGraph.mem_interedges_iff G).mp (Finset.mem_sdiff.mp hr).1
      rcases Sym2.eq_iff.mp hpr with he | he
      · exact Prod.ext he.1 he.2
      · exact (Finset.disjoint_left.mp hXY hp'.1 (he.1 ▸ hr'.2.1)).elim
  have hsplit := Finset.card_sdiff_add_card_inter (G.interedges X Y) (H.interedges X Y)
  have hi := Finset.card_le_card (Finset.inter_subset_right :
    G.interedges X Y ∩ H.interedges X Y ⊆ H.interedges X Y)
  omega

theorem cluster_cut_restoration_le
    {I : Type*} [DecidableEq I] (P : ClusterAssignment V I)
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (A B : Finset I) (hAB : Disjoint A B) :
    (G.interedges (clusterUnion P A) (exceptionalVertices P ∪ clusterUnion P B)).card ≤
      (J.interedges (clusterUnion P A) (clusterUnion P B)).card +
        (clusterUnion P A).card * ((exceptionalVertices P).card + loss) +
        (H.edgeFinset \ J.edgeFinset).card := by
  let X := clusterUnion P A
  let Y := clusterUnion P B
  let E := exceptionalVertices P
  have hclean := original_interedges_le_cleaned_add_loss G H hHG loss hloss X (E ∪ Y)
  have hsplit : H.interedges X (E ∪ Y) = H.interedges X E ∪ H.interedges X Y := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    tauto
  have hcount := (Finset.card_union_le (H.interedges X E) (H.interedges X Y))
  rw [← hsplit] at hcount
  have hE := H.card_interedges_le_mul X E
  have hdeleted := crossing_le_add_deleted H J X Y (clusterUnion_disjoint P hAB)
  change (G.interedges X (E ∪ Y)).card ≤
    (J.interedges X Y).card + X.card * (E.card + loss) + (H.edgeFinset \ J.edgeFinset).card
  rw [Nat.mul_add]
  omega

end Erdos547b.ZhaoCutRestoration

#print axioms Erdos547b.ZhaoCutRestoration.crossing_le_add_deleted
#print axioms Erdos547b.ZhaoCutRestoration.cluster_cut_restoration_le
