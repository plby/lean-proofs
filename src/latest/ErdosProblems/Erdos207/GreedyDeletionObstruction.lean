/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionStatistics
import ErdosProblems.Erdos207.PairSharingCount
import ErdosProblems.Erdos207.GreedyLegality

/-!
# The two causes of a greedy deletion

A currently legal triangle can disappear after selecting `U` for only two
reasons.  It either shares a graph edge with `U`, or `U` and that triangle
are the last two missing members of a forbidden configuration.  The latter
family is exposed explicitly below; later trajectory estimates count it by
the same extension-weight mechanism used for rooted threats.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Triangles which, together with `U`, complete a forbidden configuration
over the current chosen family `P`. -/
def twoAwayForbiddenTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (U : TripleOn V) :
    TripleSystemOn V := by
  classical
  exact (univ : Finset (TripleOn V)).filter fun T ↦
    T ≠ U ∧ ∃ C ∈ F, T ∈ C ∧ U ∈ C ∧ (C.erase T).erase U ⊆ P

@[simp]
lemma mem_twoAwayForbiddenTriangles_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {T U : TripleOn V} :
    T ∈ twoAwayForbiddenTriangles F P U ↔
      T ≠ U ∧ ∃ C ∈ F, T ∈ C ∧ U ∈ C ∧
        (C.erase T).erase U ⊆ P := by
  classical
  simp [twoAwayForbiddenTriangles]

/-- The two-away relation is symmetric in its two unselected triangles. -/
lemma mem_twoAwayForbiddenTriangles_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {T U : TripleOn V} :
    T ∈ twoAwayForbiddenTriangles F P U ↔
      U ∈ twoAwayForbiddenTriangles F P T := by
  rw [mem_twoAwayForbiddenTriangles_iff,
    mem_twoAwayForbiddenTriangles_iff]
  constructor
  · rintro ⟨hTU, C, hCF, hTC, hUC, hsub⟩
    refine ⟨hTU.symm, C, hCF, hUC, hTC, ?_⟩
    have herase : (C.erase T).erase U = (C.erase U).erase T := by
      ext W
      simp only [mem_erase]
      tauto
    rw [← herase]
    exact hsub
  · rintro ⟨hUT, C, hCF, hUC, hTC, hsub⟩
    refine ⟨hUT.symm, C, hCF, hTC, hUC, ?_⟩
    have herase : (C.erase U).erase T = (C.erase T).erase U := by
      ext W
      simp only [mem_erase]
      tauto
    rw [← herase]
    exact hsub

/-- If two distinct triangles meet in an edge witnessed by the covered
graph, then the second belongs to the first triangle's pair-sharing family. -/
lemma mem_triplesSharingPair_of_covered_by_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    {T U : TripleOn V}
    (hcovered : ¬ TriangleAvoidsGraph (coveredGraph ({U} : TripleSystemOn V)) T) :
    T ∈ triplesSharingPair U := by
  simp only [TriangleAvoidsGraph] at hcovered
  push Not at hcovered
  obtain ⟨x, hxT, y, hyT, hxy, hxyCovered⟩ := hcovered
  obtain ⟨W, hW, hxW, hyW, _⟩ := coveredGraph_adj.mp hxyCovered
  have hWU : W = U := by simpa using hW
  subst W
  rw [mem_triplesSharingPair_iff]
  have hpair : ({x, y} : Finset V) ⊆ U.1 ∩ T.1 := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_inter.mpr ⟨hxW, hxT⟩
    · exact mem_inter.mpr ⟨hyW, hyT⟩
  have hcard : ({x, y} : Finset V).card = 2 := by simp [hxy]
  rw [← hcard]
  exact card_le_card hpair

/-- Exact structural obstruction behind every triangle deleted by a legal
greedy step. -/
theorem greedyDeletedIn_subset_pairSharing_union_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} {U : TripleOn V}
    (hS : GreedyInvariant F S) (hU : U ∈ S.available) :
    greedyDeletedIn F Q S U ⊆
      triplesSharingPair U ∪ twoAwayForbiddenTriangles F S.chosen U := by
  intro T hTdeleted
  have hTold : T ∈ S.available := by
    exact (mem_sdiff.mp hTdeleted).1 |> (mem_inter.mp ·) |>.1
  have hTlegal : IsLegalExtension F S.chosen T := hS.2.2 T hTold
  have hUlegal : IsLegalExtension F S.chosen U := hS.2.2 U hU
  have hlocalT := (isLegalExtension_iff hS.1 hS.2.1 T).mp hTlegal
  by_cases hTU : T = U
  · subst T
    apply mem_union.mpr
    left
    rw [mem_triplesSharingPair_iff, inter_self, U.2]
    norm_num
  have hTnotNext : T ∉ (greedyStep F S U).available := by
    intro hTnext
    exact (mem_sdiff.mp hTdeleted).2
      (mem_inter.mpr ⟨hTnext, (mem_inter.mp (mem_sdiff.mp hTdeleted).1).2⟩)
  have hnotLegalNext : ¬ IsLegalExtension F (insert U S.chosen) T := by
    intro hlegal
    apply hTnotNext
    change T ∈ legalAvailable F (insert U S.chosen) (S.available.erase U)
    exact mem_legalAvailable_iff.mpr
      ⟨mem_erase.mpr ⟨hTU, hTold⟩, hlegal⟩
  have hstepInv := hS.step hU
  have hlocalNext :=
    (isLegalExtension_iff hstepInv.1 hstepInv.2.1 T).not.mp hnotLegalNext
  have hTnotInsert : T ∉ insert U S.chosen := by
    simp [hTU, hlocalT.1]
  have hbad :
      ¬ TriangleAvoidsGraph (coveredGraph (insert U S.chosen)) T ∨
        CompletesForbidden F (insert U S.chosen) T := by
    tauto
  rcases hbad with hpair | hforbidden
  · apply mem_union.mpr
    left
    apply mem_triplesSharingPair_of_covered_by_singleton
    intro havoidsU
    apply hpair
    intro x hxT y hyT hxy hcovered
    obtain ⟨W, hW, hxW, hyW, hxyW⟩ := coveredGraph_adj.mp hcovered
    rw [mem_insert] at hW
    rcases hW with hWU | hWP
    · have hWU' : W = U := by simpa using hWU
      subst W
      exact havoidsU x hxT y hyT hxy
        (coveredGraph_adj.mpr ⟨U, mem_singleton_self U, hxW, hyW, hxyW⟩)
    · exact hlocalT.2.1 x hxT y hyT hxy
        (coveredGraph_adj.mpr ⟨W, hWP, hxW, hyW, hxyW⟩)
  · apply mem_union.mpr
    right
    obtain ⟨C, hCF, hTC, hCerase⟩ := hforbidden
    have hUC : U ∈ C := by
      by_contra hUnotC
      apply hlocalT.2.2
      refine ⟨C, hCF, hTC, ?_⟩
      intro W hW
      have hWins : W ∈ insert U S.chosen := hCerase hW
      rcases mem_insert.mp hWins with hWU | hWP
      · subst W
        exact (hUnotC (mem_of_mem_erase hW)).elim
      · exact hWP
    refine mem_twoAwayForbiddenTriangles_iff.mpr
      ⟨hTU, C, hCF, hTC, hUC, ?_⟩
    intro W hW
    have hWeraseT : W ∈ C.erase T := (mem_erase.mp hW).2
    have hWins : W ∈ insert U S.chosen := hCerase hWeraseT
    rcases mem_insert.mp hWins with hWU | hWP
    · exact ((mem_erase.mp hW).1 hWU).elim
    · exact hWP

/-- Pair-sharing is not only a necessary deletion obstruction: every
currently available triangle sharing a pair with the selected triangle is
indeed deleted by the step. -/
theorem mem_greedyDeletedIn_univ_of_pairSharing
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T U : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hU : U ∈ S.available) (hshare : U ∈ triplesSharingPair T) :
    U ∈ greedyDeletedIn F (univ : TripleSystemOn V) S T := by
  apply mem_sdiff.mpr
  constructor
  · simp [greedyAvailableIn, hU]
  · intro hUnextRestricted
    have hUnext : U ∈ (greedyStep F S T).available := by
      exact (mem_inter.mp hUnextRestricted).1
    have hlegalNext := (hS.step hT).2.2 U hUnext
    have havoids :=
      ((isLegalExtension_iff (hS.step hT).1 (hS.step hT).2.1 U).mp
        hlegalNext).2.1
    have hinter : 2 ≤ (T.1 ∩ U.1).card :=
      mem_triplesSharingPair_iff.mp hshare
    obtain ⟨P, hP⟩ := powersetCard_nonempty.mpr hinter
    have hPcard : P.card = 2 := (mem_powersetCard.mp hP).2
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hPcard
    have hsub := (mem_powersetCard.mp hP).1
    have hx : x ∈ T.1 ∩ U.1 := hsub (by simp)
    have hy : y ∈ T.1 ∩ U.1 := hsub (by simp)
    have hcovered : (coveredGraph (insert T S.chosen)).Adj x y :=
      coveredGraph_adj.mpr
        ⟨T, mem_insert_self T S.chosen, (mem_inter.mp hx).1,
          (mem_inter.mp hy).1, hxy⟩
    exact havoids x (mem_inter.mp hx).2 y (mem_inter.mp hy).2 hxy
      hcovered

/-- Consequently, deletions from any test family are bounded by the two
ambient obstruction families. -/
theorem card_greedyDeletedIn_le_pairSharing_add_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} {U : TripleOn V}
    (hS : GreedyInvariant F S) (hU : U ∈ S.available) :
    (greedyDeletedIn F Q S U).card ≤
      (triplesSharingPair U).card +
        (twoAwayForbiddenTriangles F S.chosen U).card := by
  exact (card_le_card
    (greedyDeletedIn_subset_pairSharing_union_twoAway hS hU)).trans
      (card_union_le _ _)

end

end Erdos207
