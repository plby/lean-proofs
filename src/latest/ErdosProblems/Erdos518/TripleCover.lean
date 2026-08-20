/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.BlueTriple
import ErdosProblems.Erdos518.OneLongPath
import ErdosProblems.Erdos518.Cover
import ErdosProblems.Erdos518.TripleFree

/-!
# Covers obtained from ordered blue triples

This file carries out the path-counting step at the start of the high-degree branch of the
Chen--Chen proof.  The hyperedges are the three-element subsets of `Configuration.Y1` which
possess an ordering satisfying `Configuration.OrderedBlueTriple`.

The distinguished path `Q` is retained as one member of the cover.  A hyperedge is covered by
the spliced complement-colour path from `BlueTriple`; the remaining vertices of `Y1` are paired
and routed through `Q`; and the vertices of `Y0` are singleton paths.  Thus one hyperedge saves
one path when `a1` is odd, while two disjoint hyperedges save one path when `a1` is even.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance tripleCoverDecidableEq : DecidableEq V := Classical.decEq V

/-- The three-uniform hypergraph of ordered complement-colour triples on `Y1`. -/
noncomputable def blueTripleHypergraph : Finset (Finset V) := by
  classical
  exact C.Y1.powerset.filter fun T ↦
    T.card = 3 ∧ ∃ u ∈ T, ∃ m ∈ T, ∃ v ∈ T,
      u ≠ m ∧ u ≠ v ∧ m ≠ v ∧ C.OrderedBlueTriple u m v

@[simp] lemma mem_blueTripleHypergraph {T : Finset V} :
    T ∈ C.blueTripleHypergraph ↔
      T ⊆ C.Y1 ∧ T.card = 3 ∧ ∃ u ∈ T, ∃ m ∈ T, ∃ v ∈ T,
        u ≠ m ∧ u ≠ v ∧ m ≠ v ∧ C.OrderedBlueTriple u m v := by
  classical
  simp [blueTripleHypergraph]

/-- Every edge of `blueTripleHypergraph` is a three-element subset of `Y1`. -/
lemma blueTripleHypergraph_threeUniform {T : Finset V}
    (hT : T ∈ C.blueTripleHypergraph) : T ⊆ C.Y1 ∧ T.card = 3 := by
  exact ⟨(C.mem_blueTripleHypergraph.mp hT).1,
    (C.mem_blueTripleHypergraph.mp hT).2.1⟩

/-- On a subset of `Y1`, the ordered predicate from `TripleFree` is equivalent to saying that
the induced blue-triple hypergraph has no edge. -/
lemma tripleFreeOn_iff_no_blueTriple_edge {Y' : Finset V} (hY' : Y' ⊆ C.Y1) :
    C.TripleFreeOn Y' ↔
      ∀ T ∈ C.blueTripleHypergraph, ¬ T ⊆ Y' := by
  classical
  constructor
  · intro hfree T hT hTY'
    obtain ⟨-, -, u, huT, m, hmT, v, hvT, hum, huv, hmv, htriple⟩ :=
      C.mem_blueTripleHypergraph.mp hT
    exact hfree u (hTY' huT) m (hTY' hmT) v (hTY' hvT)
      hum huv hmv htriple
  · intro hno u hu m hm v hv hum huv hmv htriple
    let T : Finset V := {u, m, v}
    have hTsub : T ⊆ C.Y1 := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hY' hu
      · exact hY' hm
      · exact hY' hv
    have hTcard : T.card = 3 := by
      simp [T, hum, huv, hmv]
    have hTmem : T ∈ C.blueTripleHypergraph := by
      apply C.mem_blueTripleHypergraph.mpr
      refine ⟨hTsub, hTcard, u, ?_, m, ?_, v, ?_, hum, huv, hmv, htriple⟩
      all_goals simp [T]
    exact hno T hTmem (by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hu
      · exact hm
      · exact hv)

/-- Every member of `Y1` has a complement-colour neighbour on `Q`. -/
lemma exists_blueNeighbor_mem_Q_of_mem_Y1 {y : V} (hy : y ∈ C.Y1) :
    ∃ x ∈ C.Q, C.Gᶜ.Adj y x := by
  classical
  have hpos : 0 < C.blueDegreeToX y := C.blueDegreeToX_pos_of_mem_Y1 hy
  have hne : (C.X.filter fun x ↦ C.Gᶜ.Adj y x).Nonempty := by
    rw [← Finset.card_pos]
    simpa [blueDegreeToX] using hpos
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxX, hxy⟩ := Finset.mem_filter.mp hx
  exact ⟨x, C.mem_X.mp hxX, hxy⟩

/-- Pair any prescribed subset of `Y1`, routing every pair through `Q`. -/
lemma exists_pairPathFamily_of_subset_Y1 {R : Finset V} (hR : R ⊆ C.Y1) :
    ∃ qs : List (List V),
      qs.length = ceilHalf R.card ∧
      (∀ q ∈ qs, IsPath C.Gᶜ q) ∧
      ∀ y ∈ R, ∃ q ∈ qs, y ∈ q := by
  classical
  have hpair : ∀ a ∈ R.toList, ∀ b ∈ R.toList,
      ∃ q : List V, IsPath C.Gᶜ q ∧ a ∈ q ∧ b ∈ q := by
    intro a ha b hb
    have haR : a ∈ R := by simpa using ha
    have hbR : b ∈ R := by simpa using hb
    obtain ⟨x, hxQ, hax⟩ := C.exists_blueNeighbor_mem_Q_of_mem_Y1 (hR haR)
    obtain ⟨y, hyQ, hby⟩ := C.exists_blueNeighbor_mem_Q_of_mem_Y1 (hR hbR)
    exact exists_path_covering_pair_of_adj_mem_path C.q_isPath hax hxQ hyQ hby.symm
  obtain ⟨qs, hlen, hpaths, hcover⟩ :=
    exists_pairing_path_cover C.Gᶜ R.toList hpair
  refine ⟨qs, ?_, hpaths, ?_⟩
  · simpa [ceilHalf] using hlen
  · intro y hy
    exact hcover y (by simpa using hy)

/-- An edge of the blue-triple hypergraph has a complement-colour path containing every one
of its three vertices. -/
lemma exists_path_covering_blueTriple_edge {T : Finset V}
    (hT : T ∈ C.blueTripleHypergraph) :
    ∃ p : List V, IsPath C.Gᶜ p ∧ ∀ y ∈ T, y ∈ p := by
  classical
  obtain ⟨hTY1, hTcard, u, huT, m, hmT, v, hvT, hum, huv, hmv, htriple⟩ :=
    C.mem_blueTripleHypergraph.mp hT
  obtain ⟨p, hp, hup, hmp, hvp⟩ :=
    C.exists_path_of_orderedBlueTriple htriple
      (hTY1 huT) (hTY1 hmT) (hTY1 hvT) hum huv hmv
  have hsub : ({u, m, v} : Finset V) ⊆ T := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huT, hmT, hvT⟩
  have heq : ({u, m, v} : Finset V) = T := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hTcard, hum, huv, hmv]
  refine ⟨p, hp, ?_⟩
  intro y hyT
  rw [← heq] at hyT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
  rcases hyT with rfl | rfl | rfl
  · exact hup
  · exact hmp
  · exact hvp

/-- The concrete cover obtained from one ordered blue triple.  `Q` is kept as a separate path;
the triple, the remaining paired vertices of `Y1`, and the singleton vertices of `Y0` supply
the other paths. -/
lemma hasPathCoverAtMost_of_one_blueTriple {T : Finset V}
    (hT : T ∈ C.blueTripleHypergraph) :
    HasPathCoverAtMost C.Gᶜ (2 + ceilHalf (C.a1 - 3) + C.a0) := by
  classical
  obtain ⟨p, hp, hpT⟩ := C.exists_path_covering_blueTriple_edge hT
  let R : Finset V := C.Y1 \ T
  have hRsub : R ⊆ C.Y1 := Finset.sdiff_subset
  obtain ⟨qs, hqslen, hqspaths, hqscover⟩ :=
    C.exists_pairPathFamily_of_subset_Y1 hRsub
  let singles : List (List V) := singletonPathFamilyFinset C.Y0
  let ps : List (List V) := C.Q :: p :: (qs ++ singles)
  have hRcard : R.card = C.a1 - 3 := by
    have hTsub := (C.blueTripleHypergraph_threeUniform hT).1
    have hTcard := (C.blueTripleHypergraph_threeUniform hT).2
    rw [Finset.card_sdiff_of_subset hTsub, C.a1_eq_card_Y1, hTcard]
  refine ⟨ps, ?_, ?_, ?_⟩
  · simp only [ps, singles, List.length_cons, List.length_append,
      singletonPathFamilyFinset_length, hqslen]
    rw [hRcard, ← C.a0_eq_card_Y0]
    omega
  · intro q hq
    simp only [ps, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | rfl | hq | hq
    · exact C.q_isPath
    · exact hp
    · exact hqspaths q hq
    · exact (isPathCoverOn_singletonPathFamilyFinset C.Gᶜ C.Y0).1 q (by
        simpa only [singles] using hq)
  · intro y
    by_cases hyX : y ∈ C.X
    · exact ⟨C.Q, by simp [ps], C.mem_X.mp hyX⟩
    have hyY : y ∈ C.Y := C.mem_Y.mpr hyX
    have hy01 : y ∈ C.Y0 ∪ C.Y1 := by simpa [C.Y0_union_Y1] using hyY
    rcases Finset.mem_union.mp hy01 with hy0 | hy1
    · refine ⟨[y], ?_, by simp⟩
      simp [ps, singles, singletonPathFamilyFinset, hy0]
    · by_cases hyT : y ∈ T
      · exact ⟨p, by simp [ps], hpT y hyT⟩
      · have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨hy1, hyT⟩
        obtain ⟨q, hq, hyq⟩ := hqscover y hyR
        exact ⟨q, by simp [ps, hq], hyq⟩

/-- The concrete cover obtained from two disjoint ordered blue triples. -/
lemma hasPathCoverAtMost_of_two_disjoint_blueTriples {T U : Finset V}
    (hT : T ∈ C.blueTripleHypergraph) (hU : U ∈ C.blueTripleHypergraph)
    (hdisj : Disjoint T U) :
    HasPathCoverAtMost C.Gᶜ (3 + ceilHalf (C.a1 - 6) + C.a0) := by
  classical
  obtain ⟨p, hp, hpT⟩ := C.exists_path_covering_blueTriple_edge hT
  obtain ⟨q, hq, hqU⟩ := C.exists_path_covering_blueTriple_edge hU
  let R : Finset V := C.Y1 \ (T ∪ U)
  have hRsub : R ⊆ C.Y1 := Finset.sdiff_subset
  obtain ⟨rs, hrslen, hrspaths, hrscover⟩ :=
    C.exists_pairPathFamily_of_subset_Y1 hRsub
  let singles : List (List V) := singletonPathFamilyFinset C.Y0
  let ps : List (List V) := C.Q :: p :: q :: (rs ++ singles)
  have hTUsub : T ∪ U ⊆ C.Y1 := Finset.union_subset
    (C.blueTripleHypergraph_threeUniform hT).1
    (C.blueTripleHypergraph_threeUniform hU).1
  have hTUcard : (T ∪ U).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj,
      (C.blueTripleHypergraph_threeUniform hT).2,
      (C.blueTripleHypergraph_threeUniform hU).2]
  have hRcard : R.card = C.a1 - 6 := by
    rw [Finset.card_sdiff_of_subset hTUsub, C.a1_eq_card_Y1, hTUcard]
  refine ⟨ps, ?_, ?_, ?_⟩
  · simp only [ps, singles, List.length_cons, List.length_append,
      singletonPathFamilyFinset_length, hrslen]
    rw [hRcard, ← C.a0_eq_card_Y0]
    omega
  · intro s hs
    simp only [ps, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | rfl | rfl | hs | hs
    · exact C.q_isPath
    · exact hp
    · exact hq
    · exact hrspaths s hs
    · exact (isPathCoverOn_singletonPathFamilyFinset C.Gᶜ C.Y0).1 s (by
        simpa only [singles] using hs)
  · intro y
    by_cases hyX : y ∈ C.X
    · exact ⟨C.Q, by simp [ps], C.mem_X.mp hyX⟩
    have hyY : y ∈ C.Y := C.mem_Y.mpr hyX
    have hy01 : y ∈ C.Y0 ∪ C.Y1 := by simpa [C.Y0_union_Y1] using hyY
    rcases Finset.mem_union.mp hy01 with hy0 | hy1
    · refine ⟨[y], ?_, by simp⟩
      simp [ps, singles, singletonPathFamilyFinset, hy0]
    · by_cases hyT : y ∈ T
      · exact ⟨p, by simp [ps], hpT y hyT⟩
      · by_cases hyU : y ∈ U
        · exact ⟨q, by simp [ps], hqU y hyU⟩
        · have hyR : y ∈ R := by
            exact Finset.mem_sdiff.mpr ⟨hy1, by simp [hyT, hyU]⟩
          obtain ⟨s, hs, hys⟩ := hrscover y hyR
          exact ⟨s, by simp [ps, hs], hys⟩

/-- If `a1` is odd, the key equality and failure of a `c`-path complement-colour cover force
the blue-triple hypergraph to be empty. -/
theorem blueTripleHypergraph_eq_empty_of_odd
    (hkey : C.a0 + ceilHalf C.a1 = C.c) (hodd : Odd C.a1) :
    C.blueTripleHypergraph = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  have hcover := C.hasPathCoverAtMost_of_one_blueTriple hT
  have ha1 : 3 ≤ C.a1 := by
    rw [C.a1_eq_card_Y1]
    exact (C.blueTripleHypergraph_threeUniform hT).2 ▸
      Finset.card_le_card (C.blueTripleHypergraph_threeUniform hT).1
  apply C.cover_failures.2
  apply hcover.mono
  obtain ⟨m, hm⟩ := hodd
  simp only [hm, ceilHalf] at hkey ⊢
  omega

/-- If `a1` is even, the key equality and failure of a `c`-path complement-colour cover imply
that every two edges of the blue-triple hypergraph meet. -/
theorem blueTripleHypergraph_matching_of_even
    (hkey : C.a0 + ceilHalf C.a1 = C.c) (heven : Even C.a1) :
    ∀ T ∈ C.blueTripleHypergraph, ∀ U ∈ C.blueTripleHypergraph,
      ¬ Disjoint T U := by
  classical
  intro T hT U hU hdisj
  have hcover := C.hasPathCoverAtMost_of_two_disjoint_blueTriples hT hU hdisj
  have hTUsub : T ∪ U ⊆ C.Y1 := Finset.union_subset
    (C.blueTripleHypergraph_threeUniform hT).1
    (C.blueTripleHypergraph_threeUniform hU).1
  have ha1 : 6 ≤ C.a1 := by
    rw [C.a1_eq_card_Y1]
    have hcard : (T ∪ U).card = 6 := by
      rw [Finset.card_union_of_disjoint hdisj,
        (C.blueTripleHypergraph_threeUniform hT).2,
        (C.blueTripleHypergraph_threeUniform hU).2]
    exact hcard ▸ Finset.card_le_card hTUsub
  apply C.cover_failures.2
  apply hcover.mono
  obtain ⟨m, hm⟩ := heven
  simp only [hm, ceilHalf] at hkey ⊢
  omega

end Configuration
end Erdos518
