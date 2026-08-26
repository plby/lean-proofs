/- The edge-minimal graph used in linkage deletion/contraction normalization. -/
import ErdosProblems.Erdos73.UniqueLinkageDefs
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos73Infrastructure.SimpleGraph.LinkageNormalization
variable {V I : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B : Finset V} (Q : I → Finset V)

/-- Edges whose two ends lie in one of the connected columns. -/
def columnGraph (G : _root_.SimpleGraph V) : _root_.SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ i, x ∈ Q i ∧ y ∈ Q i
  symm := ⟨by rintro x y ⟨hxy, i, hx, hy⟩; exact ⟨hxy.symm, i, hy, hx⟩⟩
  loopless := ⟨by rintro x ⟨hxx, _⟩; exact hxx.ne rfl⟩

theorem columnGraph_le : columnGraph Q G ≤ G := fun _ _ h => h.1

theorem columnGraph_induce (i : I) :
    (columnGraph Q G).induce {x | x ∈ Q i} = G.induce {x | x ∈ Q i} := by
  ext x y
  exact ⟨fun h => h.1, fun h => ⟨h, i, x.property, y.property⟩⟩

/-- The graph has no proper spanning subgraph retaining a perfect linkage
and connectedness of every column. -/
def EdgeMinimal (G : _root_.SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ H : _root_.SimpleGraph V, H ≤ G → Nonempty (PerfectPathPacking H A B) →
    (∀ i, (H.induce {x | x ∈ Q i}).Connected) → G ≤ H

theorem exists_edgeMinimal [Fintype V]
    (R : PerfectPathPacking G A B)
    (hQ : ∀ i, (G.induce {x | x ∈ Q i}).Connected) :
    ∃ H : _root_.SimpleGraph V, H ≤ G ∧
      Nonempty (PerfectPathPacking H A B) ∧
      (∀ i, (H.induce {x | x ∈ Q i}).Connected) ∧ EdgeMinimal Q H A B := by
  classical
  let eligible (H : _root_.SimpleGraph V) := H ≤ G ∧
    Nonempty (PerfectPathPacking H A B) ∧ ∀ i, (H.induce {x | x ∈ Q i}).Connected
  have hex : ∃ n, ∃ H, eligible H ∧ H.edgeFinset.card = n :=
    ⟨G.edgeFinset.card, G, ⟨le_rfl, ⟨R⟩, hQ⟩, rfl⟩
  obtain ⟨H, hH, hcard⟩ := Nat.find_spec hex
  refine ⟨H, hH.1, hH.2.1, hH.2.2, ?_⟩
  intro J hJ hR hJQ
  have hmin : H.edgeFinset.card ≤ J.edgeFinset.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨J, ⟨hJ.trans hH.1, hR, hJQ⟩, rfl⟩
  have heq : J.edgeFinset = H.edgeFinset :=
    Finset.eq_of_subset_of_card_le (_root_.SimpleGraph.edgeFinset_mono hJ) hmin
  exact (_root_.SimpleGraph.edgeFinset_inj.mp heq).symm.le

/-- In an edge-minimal graph every edge is a linkage edge or a column edge. -/
theorem EdgeMinimal.eq_row_sup_column (hmin : EdgeMinimal Q G A B)
    (hQ : ∀ i, (G.induce {x | x ∈ Q i}).Connected)
    (R : PerfectPathPacking G A B) :
    G = R.toPathPacking.spanningGraph ⊔ columnGraph Q G := by
  apply le_antisymm
  · apply hmin _ (sup_le R.toPathPacking.spanningGraph_le (columnGraph_le Q))
    · exact ⟨R.inSpanningGraph.mapLe le_sup_left⟩
    · intro i
      have hc : ((columnGraph Q G).induce {x | x ∈ Q i}).Connected := by
        rw [columnGraph_induce]
        exact hQ i
      exact hc.mono (fun _ _ h => Or.inr h)
  · exact sup_le R.toPathPacking.spanningGraph_le (columnGraph_le Q)

/-- Once no row edge lies in any column, minimality determines the complete
linkage edge set, independent of the chosen perfect linkage. -/
theorem EdgeMinimal.linkage_edgeSet_eq (hmin : EdgeMinimal Q G A B)
    (hQ : ∀ i, (G.induce {x | x ∈ Q i}).Connected)
    (hdis : ∀ R : PerfectPathPacking G A B,
      Disjoint R.toPathPacking.spanningGraph (columnGraph Q G))
    (R S : PerfectPathPacking G A B) :
    R.toPathPacking.edgeSet = S.toPathPacking.edgeSet := by
  have hR := hmin.eq_row_sup_column Q hQ R
  have hS := hmin.eq_row_sup_column Q hQ S
  have heq : R.toPathPacking.spanningGraph = S.toPathPacking.spanningGraph := by
    calc
      R.toPathPacking.spanningGraph = G \ columnGraph Q G := by
        have he := congrArg (fun J => J \ columnGraph Q G) hR
        simpa only [sup_sdiff_right_self, (hdis R).sdiff_eq_left] using he.symm
      _ = S.toPathPacking.spanningGraph := by
        have he := congrArg (fun J => J \ columnGraph Q G) hS
        simpa only [sup_sdiff_right_self, (hdis S).sdiff_eq_left] using he
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    by_cases hxy : x = y
    · subst y
      have hnot (P : PerfectPathPacking G A B) : s(x, x) ∉ P.toPathPacking.edgeSet := by
        intro h
        exact (P.toPathPacking.edgeSet_subset_edgeSet h).ne rfl
      simp only [hnot R, hnot S]
    · have hadj := congrArg (fun H : _root_.SimpleGraph V => H.Adj x y) heq
      have hiff := hadj.to_iff
      change (s(x, y) ∈ R.toPathPacking.edgeSet ∧ x ≠ y) ↔
        (s(x, y) ∈ S.toPathPacking.edgeSet ∧ x ≠ y) at hiff
      exact ⟨fun h => (hiff.mp ⟨h, hxy⟩).1, fun h => (hiff.mpr ⟨h, hxy⟩).1⟩

end Erdos73Infrastructure.SimpleGraph.LinkageNormalization
