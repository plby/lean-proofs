/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CoherentNondegenerateHammockTracker

/-!
# The roof-filtered coherent tracker at the limiting reference

Global maximality is asserted only among paths captured by an ordinary
stage roof.  This is exactly the class for which local/global
nondegeneracy is invariant, and exactly the class used by the final
finite shortcut argument.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentNondegenerateHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}

def CapturedByStageRoof (L : Gamma.KappaLadder (succ kappa))
    (Q : AltPath Gamma.graph) : Prop :=
  ∃ a : Ladder.Stage (succ kappa),
    Q.vertexSet ⊆ Gamma.roof (L.frontier a)

private theorem stageRoof_mono
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b) :
    Gamma.roof (L.frontier a) ⊆ Gamma.roof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact Gamma.roof_cut (hL.frontierChronology hab)
  · exact Set.Subset.rfl

/-- Finite pointwise stage capture can be synchronized at one stage.  This
is the adapter from a preferred-marker scheduler to `CapturedByStageRoof`. -/
theorem exists_stageRoof_of_finite_of_pointwise
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a0 : Ladder.Stage (succ kappa)) {S : Set V} (hS : S.Finite)
    (hpoint : ∀ x ∈ S, ∃ a : Ladder.Stage (succ kappa),
      x ∈ Gamma.roof (L.frontier a)) :
    ∃ a : Ladder.Stage (succ kappa), S ⊆ Gamma.roof (L.frontier a) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨a0, by simp⟩
  | @insert x S hx hS ih =>
      obtain ⟨a, hxa⟩ := hpoint x (Set.mem_insert x S)
      obtain ⟨b, hSb⟩ := ih (fun y hy ↦ hpoint y (Set.mem_insert_of_mem x hy))
      refine ⟨max a b, ?_⟩
      rintro y (rfl | hy)
      · exact stageRoof_mono hL (le_max_left a b) hxa
      · exact stageRoof_mono hL (le_max_right a b) (hSb hy)

theorem capturedByStageRoof_of_finite_of_pointwise
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a0 : Ladder.Stage (succ kappa)) {Q : AltPath Gamma.graph}
    (hfinite : Q.vertexSet.Finite)
    (hpoint : ∀ x ∈ Q.vertexSet, ∃ a : Ladder.Stage (succ kappa),
      x ∈ Gamma.roof (L.frontier a)) :
    CapturedByStageRoof L Q :=
  exists_stageRoof_of_finite_of_pointwise hL a0 hfinite hpoint

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

/-- Sufficiently late tracker rows are global filtered nondegenerate
hammocks and increase without further filtering. -/
theorem exists_stable_tail
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) :
    ∃ d : Ladder.Stage (succ kappa),
      (∀ a, d ≤ a → FilteredNondegenerateHammock Gamma L.limitWarp
        x (.vertex v) (CapturedByStageRoof L)
        (chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a)) ∧
      (∀ a, d ≤ a → ∀ b, a ≤ b →
        chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a ⊆
        chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v b) := by
  obtain ⟨d, hd⟩ := hL.exists_eventually_hammock_limitWarp x (.vertex v)
  have hspec := at_spec Gamma kappa hkappa L.warpAt
    (fun c ↦ Gamma.roof (L.frontier c))
    (CoherentHammockTracker.safeConvex_of_deferred Gamma kappa hL)
    x v (filteredPersistent_of_deferred Gamma kappa hL hne)
  refine ⟨d, ?_, ?_⟩
  · intro a hda
    have hLocal := (hspec a).1.isFilteredNondegenerateHammock
    exact stageFamily_global hL hLocal (hd a hda _ hLocal.1.1)
  · intro a hda b hab Q hQa
    rcases hab.eq_or_lt with rfl | hab
    · exact hQa
    · have hLocalA := (hspec a).1.isFilteredNondegenerateHammock
      have hGlobalA := stageFamily_global hL hLocalA
        (hd a hda _ hLocalA.1.1)
      have hsafeB := hL.isSafe_warpAt_of_le_of_limitWarp hab.le
        (hLocalA.1.1.1 Q hQa).1 (hGlobalA.1.1.1 Q hQa).1
      exact retained_of_deferred Gamma kappa hkappa hL hne hab hQa hsafeB

def tailFamily (L : Gamma.KappaLadder (succ kappa)) (x v : V)
    (d : Ladder.Stage (succ kappa)) : Set (AltPath Gamma.graph) :=
  {Q | ∃ a, d ≤ a ∧ Q ∈ chosenAt Gamma kappa L.warpAt
    (fun c ↦ Gamma.roof (L.frontier c)) x v a}

theorem chosenAt_subset_tailFamily (x v : V)
    {d a : Ladder.Stage (succ kappa)} (hda : d ≤ a) :
    chosenAt Gamma kappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c)) x v a ⊆
      tailFamily L x v d :=
  fun _ hQ ↦ ⟨a, hda, hQ⟩

theorem tailFamily_filteredHammock (x v : V)
    (d : Ladder.Stage (succ kappa))
    (hglobal : ∀ a, d ≤ a →
      FilteredNondegenerateHammock Gamma L.limitWarp x (.vertex v)
        (CapturedByStageRoof L)
        (chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a))
    (hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a ⊆
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v b) :
    FilteredNondegenerateHammock Gamma L.limitWarp x (.vertex v)
      (CapturedByStageRoof L) (tailFamily L x v d) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro Q ⟨a, hda, hQa⟩
    exact (hglobal a hda).1.1.1 Q hQa
  · rintro Q ⟨a, hda, hQa⟩ R ⟨b, hdb, hRb⟩ hQR
    rcases le_total a b with hab | hba
    · exact (hglobal b hdb).1.1.2 (hmono a hda b hab hQa) hRb hQR
    · exact (hglobal a hda).1.1.2 hQa (hmono b hdb a hba hRb) hQR
  · rintro Q ⟨a, hda, hQa⟩
    exact (hglobal a hda).1.2 Q hQa
  · rintro Q ⟨a, hda, hQa⟩
    exact (hglobal a hda).2 Q hQa

theorem tailFamily_contained (x v : V)
    (d : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcontained : ∀ a, d ≤ a → HammockContained
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a) Z) :
    HammockContained (tailFamily L x v d) Z := by
  intro z hz
  simp only [hammockVertexSet, Set.mem_iUnion] at hz
  obtain ⟨Q, ⟨a, hda, hQa⟩, hzQ⟩ := hz
  exact hcontained a hda (Set.mem_iUnion.2 ⟨Q,
    Set.mem_iUnion.2 ⟨hQa, hzQ⟩⟩)

/-- The increasing tail is maximal among globally nondegenerate paths which
are captured by an ordinary stage roof. -/
theorem tailFamily_maximal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) (d : Ladder.Stage (succ kappa))
    (hglobal : ∀ a, d ≤ a →
      FilteredNondegenerateHammock Gamma L.limitWarp x (.vertex v)
        (CapturedByStageRoof L)
        (chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a))
    (hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a ⊆
      chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v b)
    (hmax : ∀ a, d ≤ a → Maximal
      (fun H ↦ FilteredNondegenerateHammock Gamma (L.warpAt a)
        x (.vertex v) (Roofed Gamma kappa
          (fun c ↦ Gamma.roof (L.frontier c)) a) H)
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a)) :
    Maximal (fun H ↦ FilteredNondegenerateHammock Gamma L.limitWarp
      x (.vertex v) (CapturedByStageRoof L) H) (tailFamily L x v d) := by
  refine ⟨tailFamily_filteredHammock x v d hglobal hmono, ?_⟩
  intro K hK htailK Q hQK
  by_cases hQtail : Q ∈ tailFamily L x v d
  · exact hQtail
  obtain ⟨aRoof, hQRoof⟩ := hK.2 Q hQK
  obtain ⟨aSafe, hQSafe⟩ :=
    hL.exists_eventually_isSafe_warpAt Q (hK.1.1.1 Q hQK).1
  let b := max d (max aRoof aSafe)
  have hdb : d ≤ b := le_max_left _ _
  have hroofb : aRoof ≤ b := (le_max_left aRoof aSafe).trans (le_max_right d _)
  have hsafeb : aSafe ≤ b := (le_max_right aRoof aSafe).trans (le_max_right d _)
  have hroofMono : Gamma.roof (L.frontier aRoof) ⊆
      Gamma.roof (L.frontier b) := by
    rcases hroofb.lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (hL.frontierChronology hlt)
    · rw [heq]
  have hQRoofB : Roofed Gamma kappa
      (fun c ↦ Gamma.roof (L.frontier c)) b Q := by
    exact hQRoof.trans hroofMono
  have hQend := (hK.1.1.1 Q hQK).2.2
  have hQstart := (hK.1.1.1 Q hQK).2.1
  have hQnondegB :=
    DWeb.KappaLadder.Deferred.not_isDegenerate_warpAt_of_limitWarp_of_subset_roof
      hL hQend (hQstart.trans_ne hne) hQRoofB (hK.1.2 Q hQK)
  let H := chosenAt Gamma kappa L.warpAt
    (fun c ↦ Gamma.roof (L.frontier c)) x v b
  have hHsub : H ⊆ K :=
    (chosenAt_subset_tailFamily x v hdb).trans htailK
  have hQnotH : Q ∉ H := fun hQH ↦
    hQtail (chosenAt_subset_tailFamily x v hdb hQH)
  have hdisj : ∀ R ∈ H,
      Disjoint (hammockInterior x (.vertex v) Q)
        (hammockInterior x (.vertex v) R) := by
    intro R hRH
    exact hK.1.1.2 hQK (hHsub hRH) (fun hQR ↦ hQnotH (hQR ▸ hRH))
  have hinsert : FilteredNondegenerateHammock Gamma (L.warpAt b)
      x (.vertex v) (Roofed Gamma kappa
        (fun c ↦ Gamma.roof (L.frontier c)) b) (insert Q H) :=
    (hmax b hdb).1.insert (hQSafe b hsafeb) hQstart hQend
      hQnondegB hQRoofB hdisj
  exact chosenAt_subset_tailFamily x v hdb
    ((hmax b hdb).2 hinsert (Set.subset_insert Q H)
      (Set.mem_insert Q H))

theorem exists_contained_filteredMaximalUpTo_of_maximal
    (Y : Set Gamma.DPath) (x v : V)
    (P : AltPath Gamma.graph → Prop) {Z : Set V}
    {M : Set (AltPath Gamma.graph)}
    (hM : Maximal (fun H ↦ FilteredNondegenerateHammock
      Gamma Y x (.vertex v) P H) M)
    (hcontained : HammockContained M Z) :
    ∃ H : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammockMaximalUpTo Gamma Y x (.vertex v)
        P kappa H ∧ HammockContained H Z := by
  by_cases hsmall : #M ≤ kappa
  · exact ⟨M, maximalUpTo_of_maximal hM.1 hM hsmall, hcontained⟩
  · have hlarge : succ kappa ≤ #M := succ_le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ kappa).trans hlarge)
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hlarge
    let H : Set (AltPath Gamma.graph) := Subtype.val '' s
    let K : Set (AltPath Gamma.graph) := Subtype.val '' t
    have hHM : H ⊆ M := by rintro Q ⟨q, _hq, rfl⟩; exact q.2
    have hKM : K ⊆ M := by rintro Q ⟨q, _hq, rfl⟩; exact q.2
    have hHcard : #H = kappa :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val s Set.injOn_subtype_val).trans hs
    have hKcard : #K = succ kappa :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val t Set.injOn_subtype_val).trans ht
    refine ⟨H, maximalUpTo_of_large (hM.1.subset hHM) hHcard
      (hM.1.subset hKM) hKcard, ?_⟩
    intro z hz
    simp only [hammockVertexSet, Set.mem_iUnion] at hz ⊢
    obtain ⟨Q, hQH, hzQ⟩ := hz
    exact hcontained (Set.mem_iUnion.2 ⟨Q,
      Set.mem_iUnion.2 ⟨hHM hQH, hzQ⟩⟩)

/-- The limiting restricted maximal-up-to family is drawn entirely from the
actual causal tracker rows. -/
theorem exists_contained_limit_filteredMaximalUpTo
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) (a0 : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcontained : ∀ a, a0 ≤ a → HammockContained
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a) Z) :
    ∃ H : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammockMaximalUpTo Gamma L.limitWarp
        x (.vertex v) (CapturedByStageRoof L) kappa H ∧
      HammockContained H Z := by
  obtain ⟨d0, hglobal0, hmono0⟩ := exists_stable_tail hkappa hL hne
  obtain ⟨d1, htransport⟩ :=
    hL.exists_eventually_hammock_limitWarp x (.vertex v)
  let d := max (max a0 d0) d1
  have ha0 : a0 ≤ d := (le_max_left a0 d0).trans (le_max_left _ _)
  have hd0 : d0 ≤ d := (le_max_right a0 d0).trans (le_max_left _ _)
  have hd1 : d1 ≤ d := le_max_right _ _
  have hglobal := fun a hda ↦ hglobal0 a (hd0.trans hda)
  have hmono := fun a hda b hab ↦ hmono0 a (hd0.trans hda) b hab
  by_cases hmax : ∀ a, d ≤ a → Maximal
      (fun H ↦ FilteredNondegenerateHammock Gamma (L.warpAt a)
        x (.vertex v) (Roofed Gamma kappa
          (fun c ↦ Gamma.roof (L.frontier c)) a) H)
      (chosenAt Gamma kappa L.warpAt
        (fun c ↦ Gamma.roof (L.frontier c)) x v a)
  · exact exists_contained_filteredMaximalUpTo_of_maximal
      L.limitWarp x v (CapturedByStageRoof L)
      (tailFamily_maximal hL hne d hglobal hmono hmax)
      (tailFamily_contained x v d
        (fun a hda ↦ hcontained a (ha0.trans hda)))
  · push Not at hmax
    obtain ⟨a, hda, hnotmax⟩ := hmax
    have hspec := (at_spec Gamma kappa hkappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c))
      (CoherentHammockTracker.safeConvex_of_deferred Gamma kappa hL)
      x v (filteredPersistent_of_deferred Gamma kappa hL hne) a).1
    rcases hspec with hsmall | hlarge
    · exact (hnotmax hsmall.2.1).elim
    · obtain ⟨K, hK, hKcard⟩ := hlarge.2.2
      have hGlobalChosen := stageFamily_global hL hlarge.1
        (htransport a (hd1.trans hda) _ hlarge.1.1.1)
      have hGlobalK := stageFamily_global hL hK
        (htransport a (hd1.trans hda) K hK.1.1)
      exact ⟨chosenAt Gamma kappa L.warpAt
          (fun c ↦ Gamma.roof (L.frontier c)) x v a,
        maximalUpTo_of_large hGlobalChosen hlarge.2.1 hGlobalK hKcard,
        hcontained a (ha0.trans hda)⟩

#print axioms exists_stable_tail
#print axioms capturedByStageRoof_of_finite_of_pointwise
#print axioms tailFamily_maximal
#print axioms exists_contained_limit_filteredMaximalUpTo

end Erdos599.Blueprint.CoherentNondegenerateHammockTracker
