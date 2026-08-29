/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CoherentNondegenerateHammockLimit
import ErdosProblems.Erdos599.CoherentNondegenerateHammockLargeDiagnostic

/-!
# A contained large roof-filtered hammock at the limiting reference

The capped coherent tracker handles the branch in which its sufficiently
late rows are genuinely maximal.  If a row instead takes the large branch
of `MaximalUpTo`, the separate successor-sized diagnostic choice supplies
the contained family.  Both the hypothesis and conclusion retain the
`CapturedByStageRoof` filter.  No implication from a bare strong edge is
asserted.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentNondegenerateHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}

private theorem mk_sdiff_eq_succ_of_card_le
    {X : Type u} {H M : Set X}
    (hkappa : aleph0 ≤ kappa) (hHcard : #H = succ kappa)
    (hMcard : #M ≤ kappa) : #(H \ M : Set X) = succ kappa := by
  apply le_antisymm
  · rw [← hHcard]
    exact Cardinal.mk_subtype_mono Set.sdiff_subset
  · by_contra hnot
    have hdiffLt : #(H \ M : Set X) < succ kappa := lt_of_not_ge hnot
    have hdiffLe : #(H \ M : Set X) ≤ kappa := lt_succ_iff.mp hdiffLt
    have hsuccLe : succ kappa ≤ kappa := by
      calc
        succ kappa = #H := hHcard.symm
        _ ≤ #(H \ M : Set X) + #M := Cardinal.le_mk_sdiff_add_mk H M
        _ ≤ kappa := Cardinal.add_le_of_le hkappa hdiffLe hMcard
    exact (not_le_of_gt (lt_succ kappa)) hsuccLe

/-- A filtered inclusion-maximal family of size at most `kappa` excludes a
filtered successor-sized family.  This is the filtered cardinal analogue
of `not_hasHammockCard_succ_of_maximal_of_card_le`. -/
theorem not_hasFilteredNondegenerateHammockCard_succ_of_maximal_of_card_le
    {Y : Set Gamma.DPath} {x v : V}
    {P : AltPath Gamma.graph → Prop} {M : Set (AltPath Gamma.graph)}
    (hkappa : aleph0 ≤ kappa)
    (hMmax : Maximal (fun K ↦ FilteredNondegenerateHammock
      Gamma Y x (.vertex v) P K) M)
    (hMcard : #M ≤ kappa) :
    ¬HasFilteredNondegenerateHammockCard
      Gamma Y x (.vertex v) P (succ kappa) := by
  rintro ⟨H, hH, hHcard⟩
  let R : Set (AltPath Gamma.graph) := H \ M
  have hR : FilteredNondegenerateHammock Gamma Y x (.vertex v) P R :=
    hH.subset Set.sdiff_subset
  have hRcard : #R = succ kappa :=
    mk_sdiff_eq_succ_of_card_le hkappa hHcard hMcard
  have hVertices : #(hammockVertexSet M) ≤ kappa :=
    mk_hammockVertexSet_le hkappa hMcard
  obtain ⟨Q, hQR, hsafe, hinitial, hend, hnondeg, hdisjoint⟩ :=
    exists_mem_nondegenerateHammock_disjoint_of_mk_eq
      hR.1 hRcard hVertices
  have hMcontained : HammockContained M (hammockVertexSet M) :=
    Set.Subset.rfl
  have hInsert : FilteredNondegenerateHammock Gamma Y x (.vertex v) P
      (insert Q M) :=
    hMmax.1.insert hsafe hinitial hend hnondeg (hR.2 Q hQR)
      (disjoint_hammockInterior_of_contained hMcontained hdisjoint)
  have hEq : M = insert Q M :=
    hMmax.eq_of_subset hInsert (Set.subset_insert Q M)
  have hQM : Q ∈ M := hEq.symm.subset (Set.mem_insert Q M)
  exact hQR.2 hQM

private theorem stageFamily_global
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} {a : Ladder.Stage (succ kappa)}
    {H : Set (AltPath Gamma.graph)}
    (hLocal : FilteredNondegenerateHammock Gamma (L.warpAt a)
      x (.vertex v) (Roofed Gamma kappa
        (fun c ↦ Gamma.roof (L.frontier c)) a) H)
    (hGlobalHammock : Hammock Gamma L.limitWarp x (.vertex v) H) :
    FilteredNondegenerateHammock Gamma L.limitWarp x (.vertex v)
      (CapturedByStageRoof L) H := by
  refine ⟨⟨hGlobalHammock, ?_⟩, ?_⟩
  · intro Q hQ
    have hQdata := hLocal.1.1.1 Q hQ
    exact DWeb.KappaLadder.Deferred.not_isDegenerate_limitWarp_of_warpAt_of_subset_roof
      hL (hLocal.2 Q hQ)
        ((hLocal.2 Q hQ) (Q.mem_vertexSet_of_terminal_eq hQdata.2.2))
        (hLocal.1.2 Q hQ)
  · intro Q hQ
    exact ⟨a, hLocal.2 Q hQ⟩

/-- A filtered successor-sized limiting hammock has a successor-sized
filtered replacement inside `Z`.  The capped rows and large diagnostic rows
must both already have been inserted into `Z`. -/
theorem exists_contained_limit_largeFilteredHammock
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) (a₀ : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcapped : ∀ a, a₀ ≤ a → HammockContained
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a) Z)
    (hlarge : ∀ a, a₀ ≤ a → HammockContained
      (CoherentNondegenerateHammockLargeDiagnostic.chosenAt
        Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a) Z)
    (hGlobalLarge : HasFilteredNondegenerateHammockCard Gamma L.limitWarp
      x (.vertex v) (CapturedByStageRoof L) (succ kappa)) :
    ∃ K : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammock Gamma L.limitWarp x (.vertex v)
        (CapturedByStageRoof L) K ∧
      #K = succ kappa ∧ HammockContained K Z := by
  obtain ⟨d₀, hglobal₀, hmono₀⟩ := exists_stable_tail hkappa hL hne
  obtain ⟨d₁, htransport⟩ :=
    hL.exists_eventually_hammock_limitWarp x (.vertex v)
  let d := max (max a₀ d₀) d₁
  have ha₀ : a₀ ≤ d := (le_max_left a₀ d₀).trans (le_max_left _ _)
  have hd₀ : d₀ ≤ d := (le_max_right a₀ d₀).trans (le_max_left _ _)
  have hd₁ : d₁ ≤ d := le_max_right _ _
  have hglobal : ∀ a, d ≤ a → FilteredNondegenerateHammock
      Gamma L.limitWarp x (.vertex v) (CapturedByStageRoof L)
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a) :=
    fun a hda ↦ hglobal₀ a (hd₀.trans hda)
  have hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a ⊆
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v b :=
    fun a hda b hab ↦ hmono₀ a (hd₀.trans hda) b hab
  by_cases hmax : ∀ a, d ≤ a → Maximal
      (fun H ↦ FilteredNondegenerateHammock Gamma (L.warpAt a)
        x (.vertex v) (Roofed Gamma kappa
          (fun c ↦ Gamma.roof (L.frontier c)) a) H)
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a)
  · let T := tailFamily L x v d
    have hTmax : Maximal (fun H ↦ FilteredNondegenerateHammock
        Gamma L.limitWarp x (.vertex v) (CapturedByStageRoof L) H) T :=
      tailFamily_maximal hL hne d hglobal hmono hmax
    have hTcontained : HammockContained T Z :=
      tailFamily_contained x v d
        (fun a hda ↦ hcapped a (ha₀.trans hda))
    have hTlarge : succ kappa ≤ #T := by
      apply succ_le_of_lt
      by_contra hsmall
      exact (not_hasFilteredNondegenerateHammockCard_succ_of_maximal_of_card_le
        hkappa hTmax (not_lt.mp hsmall)) hGlobalLarge
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp hTlarge
    let K : Set (AltPath Gamma.graph) := Subtype.val '' s
    have hKT : K ⊆ T := by
      rintro Q ⟨q, _hq, rfl⟩
      exact q.2
    have hKcard : #K = succ kappa :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val s
        Set.injOn_subtype_val).trans hs
    have hKcontained : HammockContained K Z := by
      intro z hz
      simp only [hammockVertexSet, Set.mem_iUnion] at hz ⊢
      obtain ⟨Q, hQK, hzQ⟩ := hz
      exact hTcontained (Set.mem_iUnion.2 ⟨Q,
        Set.mem_iUnion.2 ⟨hKT hQK, hzQ⟩⟩)
    exact ⟨K, hTmax.1.subset hKT, hKcard, hKcontained⟩
  · push Not at hmax
    obtain ⟨a, hda, hnotmax⟩ := hmax
    have hspec := (at_spec Gamma kappa hkappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c))
      (CoherentHammockTracker.safeConvex_of_deferred Gamma kappa hL)
      x v (filteredPersistent_of_deferred Gamma kappa hL hne) a).1
    rcases hspec with hsmall | hlargeStage
    · exact (hnotmax hsmall.2.1).elim
    · obtain ⟨K₀, hK₀, hK₀card⟩ := hlargeStage.2.2
      have hExists : HasFilteredNondegenerateHammockCard Gamma (L.warpAt a)
          x (.vertex v) (Roofed Gamma kappa
            (fun c ↦ Gamma.roof (L.frontier c)) a) (succ kappa) :=
        ⟨K₀, hK₀, hK₀card⟩
      let K := CoherentNondegenerateHammockLargeDiagnostic.chosenAt
        Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a
      have hKspec :=
        CoherentNondegenerateHammockLargeDiagnostic.chosenAt_spec_of_exists
          Gamma kappa L.warpAt
            (fun c ↦ Gamma.roof (L.frontier c)) x v a hExists
      have hKglobal : FilteredNondegenerateHammock Gamma L.limitWarp
          x (.vertex v) (CapturedByStageRoof L) K :=
        stageFamily_global hL hKspec.1
          (htransport a (hd₁.trans hda) K hKspec.1.1.1)
      exact ⟨K, hKglobal, hKspec.2, hlarge a (ha₀.trans hda)⟩

#print axioms
  not_hasFilteredNondegenerateHammockCard_succ_of_maximal_of_card_le
#print axioms exists_contained_limit_largeFilteredHammock

end Erdos599.Blueprint.CoherentNondegenerateHammockTracker
