/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CoherentHammockTracker

/-!
# Global maximality from coherent stage hammocks

After the endpoint incidences stabilize, the actual coherent tracker is an
increasing family of globally safe hammocks.  If every late stage choice is
inclusion-maximal, the tail union is globally inclusion-maximal: a proposed
additional global path is safe at a sufficiently late stage and contradicts
that stage's maximality.  Otherwise one late large branch directly supplies
a global maximal-up-to hammock.  All selected output paths come from the
tracked stage choices.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}

/-- The actual selected families eventually are global hammocks and are
increasing without any further filtering. -/
theorem exists_stable_tail
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (x : V) (e : AltEnd V) :
    ∃ d : Ladder.Stage (succ kappa),
      (∀ a, d ≤ a → Hammock Gamma L.limitWarp x e
        (chosenAt Gamma kappa L.warpAt x e a)) ∧
      (∀ a, d ≤ a → ∀ b, a ≤ b →
        chosenAt Gamma kappa L.warpAt x e a ⊆
          chosenAt Gamma kappa L.warpAt x e b) := by
  obtain ⟨d, hd⟩ := hL.exists_eventually_hammock_limitWarp x e
  have hspec := at_spec Gamma kappa hkappa L.warpAt
    (safeConvex_of_deferred Gamma kappa hL) x e
  refine ⟨d, ?_, ?_⟩
  · intro a hda
    exact hd a hda _ (hspec a).1.isHammock
  · intro a hda b hab Q hQa
    rcases hab.eq_or_lt with rfl | hab
    · exact hQa
    · have hQglobal := (hd a hda _ (hspec a).1.isHammock).1 Q hQa
      exact (hspec b).2 a hab Q hQa
        (hL.isSafe_warpAt_of_le_of_limitWarp hab.le
          ((hspec a).1.isHammock.1 Q hQa).1 hQglobal.1)

/-- The actual tail union of the tracker, not an independently chosen
global hammock. -/
def tailFamily (L : Gamma.KappaLadder (succ kappa)) (x : V) (e : AltEnd V)
    (d : Ladder.Stage (succ kappa)) : Set (AltPath Gamma.graph) :=
  {Q | ∃ a, d ≤ a ∧ Q ∈ chosenAt Gamma kappa L.warpAt x e a}

theorem chosenAt_subset_tailFamily (x : V) (e : AltEnd V)
    {d a : Ladder.Stage (succ kappa)} (hda : d ≤ a) :
    chosenAt Gamma kappa L.warpAt x e a ⊆ tailFamily L x e d :=
  fun _ hQ ↦ ⟨a, hda, hQ⟩

theorem tailFamily_hammock (x : V) (e : AltEnd V)
    (d : Ladder.Stage (succ kappa))
    (hglobal : ∀ a, d ≤ a → Hammock Gamma L.limitWarp x e
      (chosenAt Gamma kappa L.warpAt x e a))
    (hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt x e a ⊆
        chosenAt Gamma kappa L.warpAt x e b) :
    Hammock Gamma L.limitWarp x e (tailFamily L x e d) := by
  constructor
  · rintro Q ⟨a, hda, hQa⟩
    exact (hglobal a hda).1 Q hQa
  · rintro Q ⟨a, hda, hQa⟩ R ⟨b, hdb, hRb⟩ hQR
    rcases le_total a b with hab | hba
    · exact (hglobal b hdb).2 (hmono a hda b hab hQa) hRb hQR
    · exact (hglobal a hda).2 hQa (hmono b hdb a hba hRb) hQR

theorem tailFamily_contained (x : V) (e : AltEnd V)
    (d : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcontained : ∀ a, d ≤ a →
      HammockContained (chosenAt Gamma kappa L.warpAt x e a) Z) :
    HammockContained (tailFamily L x e d) Z := by
  intro v hv
  simp only [hammockVertexSet, Set.mem_iUnion] at hv
  obtain ⟨Q, ⟨a, hda, hQa⟩, hvQ⟩ := hv
  exact hcontained a hda (Set.mem_iUnion.2 ⟨Q,
    Set.mem_iUnion.2 ⟨hQa, hvQ⟩⟩)

/-- Eventual local safeness of each candidate path is sufficient for
maximality of an increasing tail of genuinely maximal stage hammocks. -/
theorem tailFamily_maximal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (x : V) (e : AltEnd V) (d : Ladder.Stage (succ kappa))
    (hglobal : ∀ a, d ≤ a → Hammock Gamma L.limitWarp x e
      (chosenAt Gamma kappa L.warpAt x e a))
    (hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt x e a ⊆
        chosenAt Gamma kappa L.warpAt x e b)
    (hmax : ∀ a, d ≤ a →
      Maximal (fun H ↦ Hammock Gamma (L.warpAt a) x e H)
        (chosenAt Gamma kappa L.warpAt x e a)) :
    Maximal (fun H ↦ Hammock Gamma L.limitWarp x e H)
      (tailFamily L x e d) := by
  refine ⟨tailFamily_hammock x e d hglobal hmono, ?_⟩
  intro K hK htailK Q hQK
  obtain ⟨a, ha⟩ := hL.exists_eventually_isSafe_warpAt Q (hK.1 Q hQK).1
  let b := max d a
  have hdb : d ≤ b := le_max_left d a
  have hab : a ≤ b := le_max_right d a
  let H := chosenAt Gamma kappa L.warpAt x e b
  have hHsub : H ⊆ K := (chosenAt_subset_tailFamily x e hdb).trans htailK
  have hinsert : Hammock Gamma (L.warpAt b) x e (insert Q H) := by
    refine ⟨?_, hK.2.subset (Set.insert_subset hQK hHsub)⟩
    intro R hR
    rcases hR with rfl | hR
    · exact ⟨ha b hab, (hK.1 R hQK).2⟩
    · exact (hmax b hdb).1.1 R hR
  have hQH : Q ∈ H := (hmax b hdb).2 hinsert (Set.subset_insert Q H)
    (Set.mem_insert Q H)
  exact chosenAt_subset_tailFamily x e hdb hQH

/-- An already maximal contained hammock can be thinned to the required
maximal-up-to form without introducing any path outside its carrier. -/
theorem exists_contained_maximalUpTo_of_maximal
    (Y : Set Gamma.DPath) (x : V) (e : AltEnd V) {Z : Set V}
    {M : Set (AltPath Gamma.graph)}
    (hM : Maximal (fun H ↦ Hammock Gamma Y x e H) M)
    (hcontained : HammockContained M Z) :
    ∃ H : Set (AltPath Gamma.graph),
      HammockMaximalUpTo Gamma Y x e kappa H ∧ HammockContained H Z := by
  by_cases hsmall : #M ≤ kappa
  · exact ⟨M, maximalUpTo_of_maximal hM.1 hM hsmall, hcontained⟩
  · have hlarge : succ kappa ≤ #M := succ_le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp ((le_succ kappa).trans hlarge)
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
    intro v hv
    simp only [hammockVertexSet, Set.mem_iUnion] at hv ⊢
    obtain ⟨Q, hQH, hvQ⟩ := hv
    exact hcontained (Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨hHM hQH, hvQ⟩⟩)

/-- The coherent tracker supplies a genuine globally maximal-up-to-`kappa`
hammock inside any set containing all sufficiently late tracker rows.
This uses neither a global confinement hypothesis nor unproved transfer of
stage maximality. -/
theorem exists_contained_limit_maximalUpTo
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (x : V) (e : AltEnd V) (a0 : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcontained : ∀ a, a0 ≤ a →
      HammockContained (chosenAt Gamma kappa L.warpAt x e a) Z) :
    ∃ H : Set (AltPath Gamma.graph),
      HammockMaximalUpTo Gamma L.limitWarp x e kappa H ∧ HammockContained H Z := by
  obtain ⟨d0, hglobal0, hmono0⟩ := exists_stable_tail hkappa hL x e
  obtain ⟨d1, htransport⟩ := hL.exists_eventually_hammock_limitWarp x e
  let d := max (max a0 d0) d1
  have ha0 : a0 ≤ d := (le_max_left a0 d0).trans (le_max_left _ _)
  have hd0 : d0 ≤ d := (le_max_right a0 d0).trans (le_max_left _ _)
  have hd1 : d1 ≤ d := le_max_right _ _
  have hglobal : ∀ a, d ≤ a → Hammock Gamma L.limitWarp x e
      (chosenAt Gamma kappa L.warpAt x e a) :=
    fun a hda ↦ hglobal0 a (hd0.trans hda)
  have hmono : ∀ a, d ≤ a → ∀ b, a ≤ b →
      chosenAt Gamma kappa L.warpAt x e a ⊆
        chosenAt Gamma kappa L.warpAt x e b :=
    fun a hda b hab ↦ hmono0 a (hd0.trans hda) b hab
  by_cases hmax : ∀ a, d ≤ a →
      Maximal (fun H ↦ Hammock Gamma (L.warpAt a) x e H)
        (chosenAt Gamma kappa L.warpAt x e a)
  · exact exists_contained_maximalUpTo_of_maximal L.limitWarp x e
      (tailFamily_maximal hL x e d hglobal hmono hmax)
      (tailFamily_contained x e d (fun a hda ↦ hcontained a (ha0.trans hda)))
  · push Not at hmax
    obtain ⟨a, hda, hnotmax⟩ := hmax
    have hspec := (at_spec Gamma kappa hkappa L.warpAt
      (safeConvex_of_deferred Gamma kappa hL) x e a).1
    rcases hspec with hsmall | hlarge
    · exact (hnotmax hsmall.2.1).elim
    · obtain ⟨K, hK, hKcard⟩ := hlarge.2.2
      exact ⟨chosenAt Gamma kappa L.warpAt x e a,
        maximalUpTo_of_large (hglobal a hda) hlarge.2.1
          (htransport a (hd1.trans hda) K hK) hKcard,
        hcontained a (ha0.trans hda)⟩

#print axioms exists_stable_tail
#print axioms tailFamily_maximal
#print axioms exists_contained_limit_maximalUpTo

end Erdos599.Blueprint.CoherentHammockTracker
