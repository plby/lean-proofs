import ErdosProblems.Erdos19.DistinguishedPalette
import ErdosProblems.Erdos19.ExceptionalColorMatching
import ErdosProblems.Erdos19.BufferedMatchingFamily
import ErdosProblems.Erdos19.MatchingColorExtension

/-! # Initializing the special palette without consuming the block reservoir

The exceptional color is extended first in the entire pair graph, leaving an
independent uncovered set. Every other special color is extended outside the
reservoir. Thus the initial extensions use at most one reservoir edge at each vertex.
-/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_special_palette_initialization (H J : SetHypergraph V) (hJH : J ⊆ H)
    (hlarge : ∀ e : J, 3 ≤ e.1.ncard) (m : ℕ) (color : J.EdgeColoring (Fin m))
    (S : Finset (Fin m)) (bad : Fin m) (hbad : bad ∈ S)
    (R : _root_.SimpleGraph V) (U Y : Set V) (hUY : Disjoint U Y) (d : ℕ)
    (hmissing : ∀ u ∈ U, ((H.twoGraph \ R).neighborSet u)ᶜ.ncard ≤ d)
    (hbuffer : ∀ a ∈ S, a ≠ bad →
      d + S.card ≤ (Y \ J.coveredVertices {e | color e = a}).ncard) :
    ∃ J₀ : SetHypergraph V, ∃ c₀ : J₀.EdgeColoring (Fin m),
      J ⊆ J₀ ∧ J₀ ⊆ H ∧
      (∀ e : J, ∀ he : e.1 ∈ J₀, c₀ ⟨e.1, he⟩ = color e) ∧
      (∀ e : J₀, c₀ e ∉ S → e.1 ∈ J) ∧
      (∀ a, a ∉ S → J₀.coveredVertices {e | c₀ e = a} =
        J.coveredVertices {e | color e = a}) ∧
      (∀ a ∈ S, a ≠ bad → U ⊆ J₀.coveredVertices {e | c₀ e = a}) ∧
      (∀ v, ((J₀.twoGraph ⊓ R).neighborSet v).ncard ≤ 1) ∧
      ∃ Z : Set V, (∀ x ∈ Z, ∀ y ∈ Z, ¬H.twoGraph.Adj x y) ∧
        ∀ v, v ∉ Z → v ∈ J₀.coveredVertices {e | c₀ e = bad} := by
  classical
  obtain ⟨p, index, hp, hindexBad, hindexMem, hindexNe, hindexSurj⟩ :=
    exists_distinguished_palette_index S bad hbad
  let Cbad := J.coveredVertices {e | color e = bad}
  obtain ⟨Mbad, hMbad, hbadAvoid, hbadIndependent⟩ :=
    exists_matching_avoiding_with_independent_remainder H.twoGraph Cbad
  let G := H.twoGraph \ R
  let C : Fin p → Set V := fun i ↦ J.coveredVertices {e | color e = index (Sum.inr i)}
  have hbadLoad : ∀ u ∈ U, (Mbad.spanningCoe.neighborSet u).ncard ≤ 1 := by
    intro u _
    rw [matching_neighbor_ncard H.twoGraph Mbad hMbad]
    split_ifs <;> omega
  have hbuffer' : ∀ i, d + 1 + p ≤ (Y \ C i).ncard := by
    intro i
    have h := hbuffer (index (Sum.inr i)) (hindexMem _) (hindexNe i)
    change d + S.card ≤ (Y \ C i).ncard at h
    omega
  obtain ⟨M, hM, hdis⟩ := exists_buffered_matching_family G Mbad.spanningCoe U Y hUY
    d 1 hmissing hbadLoad p C hbuffer'
  have hGQ : G ≤ H.twoGraph := sdiff_le
  let family : Unit ⊕ Fin p → H.twoGraph.Subgraph :=
    Sum.elim (fun _ ↦ Mbad) (fun i ↦ liftSubgraph hGQ (M i))
  have hfamily : ∀ i, (family i).IsMatching := by
    intro i
    rcases i with i | i
    · exact hMbad
    · exact (hM i).1
  have hfamilyDis : Pairwise fun i j ↦ Disjoint (family i).spanningCoe (family j).spanningCoe := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact (hij (congrArg Sum.inl (Subsingleton.elim _ _))).elim
    · exact (hM j).2.2.2.2
    · exact (hM i).2.2.2.2.symm
    · exact hdis (fun h ↦ hij (congrArg Sum.inr h))
  have hnew : Disjoint J (matchingFamilyHypergraph family) := by
    apply Set.disjoint_left.mpr
    intro e heJ heM
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp heM
    have hsize := matchingEdges_size (family i) hi
    have hlargeE := hlarge ⟨e, heJ⟩
    change 3 ≤ e.ncard at hlargeE
    omega
  have havoid : ∀ i, Disjoint (J.coveredVertices {e | color e = index i}) (family i).verts := by
    intro i
    rcases i with i | i
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      rw [hindexBad]
      exact hbadAvoid.symm
    · apply Set.disjoint_left.mpr
      intro v hvC hvM
      exact ((hM i).2.2.1 hvM).2 hvC
  obtain ⟨c₀, hagree, hcoverage, hold, hnewColors⟩ :=
    J.extend_coloring_by_indexed_matching_family family hfamily hfamilyDis hnew color index havoid
  let J₀ := J ∪ matchingFamilyHypergraph family
  have hJ₀H : J₀ ⊆ H := Set.union_subset hJH (matchingFamily_subset H family)
  have hnonSpecial : ∀ e : J₀, c₀ e ∉ S → e.1 ∈ J := by
    intro e he
    by_contra heJ
    have hmem := hnewColors ⟨e.1, e.2.resolve_left heJ⟩
    obtain ⟨i, hi⟩ := hmem
    exact he (hi ▸ hindexMem i)
  have hRgraph : J₀.twoGraph ⊓ R ≤ Mbad.spanningCoe := by
    intro x y hxy
    rcases hxy.1.2 with heJ | heM
    · have hsize := hlarge ⟨{x, y}, heJ⟩
      change 3 ≤ ({x, y} : Set V).ncard at hsize
      rw [Set.ncard_pair hxy.1.1] at hsize
      omega
    · obtain ⟨i, hi⟩ := (matchingFamily_pair_iff family x y).mp heM
      rcases i with i | i
      · exact hi
      · have hG : G.Adj x y := (M i).adj_sub hi
        exact (hG.2 hxy.2).elim
  refine ⟨J₀, c₀, Set.subset_union_left, hJ₀H, ?_, hnonSpecial, ?_, ?_, ?_, ?_⟩
  · intro e _
    exact hagree e
  · intro a ha
    apply Set.Subset.antisymm _ (hold a)
    intro v hv
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hea, hve⟩ := Set.mem_iUnion.mp he
    have heJ : e.1 ∈ J := hnonSpecial e
      (fun h ↦ ha ((show c₀ e = a from hea) ▸ h))
    exact Set.mem_iUnion.mpr ⟨⟨e.1, heJ⟩, Set.mem_iUnion.mpr
      ⟨(hagree ⟨e.1, heJ⟩).symm.trans hea, hve⟩⟩
  · intro a ha hne
    obtain ⟨i, hi⟩ := hindexSurj a ha
    rcases i with i | i
    · have hiUnit : i = () := Subsingleton.elim _ _
      subst i
      exact (hne (hi.symm.trans hindexBad)).elim
    · intro v hv
      rw [← hi, hcoverage (Sum.inr i)]
      by_cases hvC : v ∈ C i
      · exact Or.inl hvC
      · exact Or.inr ((hM i).2.1 ⟨hv, hvC⟩)
  · intro v
    have hcard := Set.ncard_le_ncard (show (J₀.twoGraph ⊓ R).neighborSet v ⊆
      Mbad.spanningCoe.neighborSet v from fun _ h ↦ hRgraph h)
    have hone : (Mbad.spanningCoe.neighborSet v).ncard ≤ 1 := by
      rw [matching_neighbor_ncard H.twoGraph Mbad hMbad]
      split_ifs <;> omega
    exact hcard.trans hone
  · let Z := (Cbad ∪ Mbad.verts)ᶜ
    refine ⟨Z, ?_, ?_⟩
    · intro x hx y hy
      exact hbadIndependent x y (fun h ↦ hx (Or.inl h)) (fun h ↦ hy (Or.inl h))
        (fun h ↦ hx (Or.inr h)) (fun h ↦ hy (Or.inr h))
    · intro v hv
      have hmem : v ∈ Cbad ∪ Mbad.verts := by
        by_contra h
        exact hv h
      have h := hcoverage (Sum.inl ())
      rw [hindexBad] at h
      rw [h]
      exact hmem

#print axioms exists_special_palette_initialization

end Erdos19.SetHypergraph
