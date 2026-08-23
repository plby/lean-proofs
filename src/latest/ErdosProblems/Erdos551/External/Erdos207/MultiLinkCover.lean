/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.RandomLinkMatchingCover

/-!
# Composing the crossing-link covers

The robust matching argument is applied once for every outer vertex.  This
file performs that finite iteration.  Its extension hypothesis is deliberately
state-dependent: pair-conflict and forbidden-participation deletions for the
next link are computed after all earlier links have been matched.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A bipartite partition of the inner link at one center vertex. -/
structure BipartiteLink (V : Type*) [DecidableEq V] where
  center : V
  left : Finset V
  right : Finset V
  center_not_left : center ∉ left
  center_not_right : center ∉ right
  disjoint_sides : Disjoint left right

namespace BipartiteLink

def leftEmbedding
    {V : Type*} [DecidableEq V] (K : BipartiteLink V) : ↥K.left ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def rightEmbedding
    {V : Type*} [DecidableEq V] (K : BipartiteLink V) : ↥K.right ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

lemma center_ne_left
    {V : Type*} [DecidableEq V] (K : BipartiteLink V) (a : ↥K.left) :
    K.center ≠ K.leftEmbedding a := by
  intro h
  exact K.center_not_left (h ▸ a.2)

lemma center_ne_right
    {V : Type*} [DecidableEq V] (K : BipartiteLink V) (b : ↥K.right) :
    K.center ≠ K.rightEmbedding b := by
  intro h
  exact K.center_not_right (h ▸ b.2)

lemma left_ne_right
    {V : Type*} [DecidableEq V] (K : BipartiteLink V)
    (a : ↥K.left) (b : ↥K.right) :
    K.leftEmbedding a ≠ K.rightEmbedding b := by
  intro h
  apply Finset.disjoint_left.mp K.disjoint_sides a.2
  change a.1 = b.1 at h
  simpa only [h] using b.2

/-- Every even set of non-center vertices admits the balanced bipartition
used to turn a perfect link matching into a triangle cover. -/
theorem exists_balanced_of_even
    {V : Type*} [DecidableEq V] (center : V) (W : Finset V)
    (hcenter : center ∉ W) (heven : Even W.card) :
    ∃ K : BipartiteLink V,
      K.center = center ∧ K.left ∪ K.right = W ∧
      K.left.card = K.right.card := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp heven
  have hmle : m ≤ W.card := by omega
  obtain ⟨L, hLW, hLcard⟩ := Finset.exists_subset_card_eq hmle
  let R := W \ L
  have hRcard : R.card = m := by
    change (W \ L).card = m
    rw [Finset.card_sdiff_of_subset hLW, hm, hLcard]
    omega
  have hcenterL : center ∉ L := fun h ↦ hcenter (hLW h)
  have hcenterR : center ∉ R := by
    intro h
    exact hcenter (Finset.sdiff_subset h)
  have hdisjoint : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    exact (Finset.mem_sdiff.mp hxR).2 hxL
  let K : BipartiteLink V :=
    ⟨center, L, R, hcenterL, hcenterR, hdisjoint⟩
  refine ⟨K, rfl, ?_, ?_⟩
  · dsimp only [K]
    change L ∪ (W \ L) = W
    rw [union_comm, Finset.sdiff_union_of_subset hLW]
  · dsimp only [K]
    rw [hLcard, hRcard]

end BipartiteLink

/-- A triple system covers every spoke from the center to either side of a
bipartite link. -/
def CoversBipartiteLink
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (M : TripleSystemOn V) : Prop :=
  (∀ x ∈ K.left, (coveredGraph M).Adj K.center x) ∧
  (∀ x ∈ K.right, (coveredGraph M).Adj K.center x)

/-- Exact structural output required from one state-dependent link step. -/
def HasLinkCoverExtension
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V) : Prop :=
  ∃ M : TripleSystemOn V,
    M ⊆ available ∧ Disjoint P M ∧
    IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F ∧
    CoversBipartiteLink K M

private lemma coveredGraph_mono_link
    {V : Type*} [DecidableEq V]
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    coveredGraph P ≤ coveredGraph Q := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
  exact coveredGraph_adj.mpr ⟨T, hPQ hTP, huT, hvT, huv⟩

lemma CoversBipartiteLink.mono
    {V : Type*} [DecidableEq V]
    {K : BipartiteLink V} {P Q : TripleSystemOn V}
    (h : CoversBipartiteLink K P) (hPQ : P ⊆ Q) :
    CoversBipartiteLink K Q := by
  constructor
  · intro x hx
    exact coveredGraph_mono_link hPQ (h.1 x hx)
  · intro x hx
    exact coveredGraph_mono_link hPQ (h.2 x hx)

/-- Finite composition of all state-dependent link extensions.  The output
is the genuinely new family `P \ P0`, not the enlarged total family; every
link spoke is covered by this new family itself. -/
theorem exists_simultaneous_bipartiteLink_cover
    {O V : Type*} [Fintype O] [DecidableEq O] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P0 : TripleSystemOn V)
    (K : O → BipartiteLink V)
    (hP0packing : IsPackingOn P0) (hP0avoid : AvoidsForbidden P0 F)
    (hstep : ∀ (P : TripleSystemOn V),
      P0 ⊆ P → P ⊆ P0 ∪ available →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : O, HasLinkCoverExtension F available P (K o)) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P0 M ∧
      IsPackingOn (P0 ∪ M) ∧ AvoidsForbidden (P0 ∪ M) F ∧
      ∀ o : O, CoversBipartiteLink (K o) M := by
  classical
  have hind : ∀ S : Finset O, ∃ P : TripleSystemOn V,
      P0 ⊆ P ∧ P ⊆ P0 ∪ available ∧
      IsPackingOn P ∧ AvoidsForbidden P F ∧
      ∀ o ∈ S, CoversBipartiteLink (K o) (P \ P0) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨P0, Subset.rfl, ?_, hP0packing, hP0avoid, ?_⟩
        · exact subset_union_left
        · simp
    | @insert o S ho ih =>
        obtain ⟨P, hP0P, hPsub, hPpacking, hPavoid, hPcover⟩ := ih
        obtain ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
          hMcover⟩ := hstep P hP0P hPsub hPpacking hPavoid o
        let P' := P ∪ M
        have hP0P' : P0 ⊆ P' :=
          hP0P.trans subset_union_left
        have hP'sub : P' ⊆ P0 ∪ available := by
          intro T hT
          rcases mem_union.mp hT with hTP | hTM
          · exact hPsub hTP
          · exact mem_union_right P0 (hMavailable hTM)
        have holdDiff : P \ P0 ⊆ P' \ P0 := by
          intro T hT
          exact mem_sdiff.mpr
            ⟨mem_union_left M (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩
        have hnewDiff : M ⊆ P' \ P0 := by
          intro T hTM
          apply mem_sdiff.mpr
          refine ⟨mem_union_right P hTM, ?_⟩
          intro hTP0
          exact Finset.disjoint_left.mp hPMdisjoint (hP0P hTP0) hTM
        refine ⟨P', hP0P', hP'sub, hPMpacking, hPMavoid, ?_⟩
        intro j hj
        rw [mem_insert] at hj
        rcases hj with rfl | hjS
        · exact hMcover.mono hnewDiff
        · exact (hPcover j hjS).mono holdDiff
  obtain ⟨P, hP0P, hPsub, hPpacking, hPavoid, hcover⟩ :=
    hind (Finset.univ : Finset O)
  let M := P \ P0
  have hMavailable : M ⊆ available := by
    intro T hTM
    have hT := hPsub (mem_sdiff.mp hTM).1
    rcases mem_union.mp hT with hTP0 | hTA
    · exact ((mem_sdiff.mp hTM).2 hTP0).elim
    · exact hTA
  have hP0M : P0 ∪ M = P := by
    ext T
    constructor
    · intro hT
      rcases mem_union.mp hT with hTP0 | hTM
      · exact hP0P hTP0
      · exact (mem_sdiff.mp hTM).1
    · intro hTP
      by_cases hTP0 : T ∈ P0
      · exact mem_union_left M hTP0
      · exact mem_union_right P0 (mem_sdiff.mpr ⟨hTP, hTP0⟩)
  have hdisjoint : Disjoint P0 M := by
    rw [Finset.disjoint_left]
    intro T hTP0 hTM
    exact (mem_sdiff.mp hTM).2 hTP0
  refine ⟨M, hMavailable, hdisjoint, ?_, ?_, ?_⟩
  · simpa only [hP0M] using hPpacking
  · simpa only [hP0M] using hPavoid
  · intro o
    exact hcover o (mem_univ o)

end

end Erdos207
