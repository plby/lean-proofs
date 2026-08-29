/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CoherentHammockLimit
import ErdosProblems.Erdos599.LargeHammockMaximalCardinality

/-!
# Transporting contained large hammocks through a coherent stage tracker

Assume every sufficiently late stage can replace a local successor-sized
hammock by one contained in a fixed set `Z`.  Then any successor-sized
hammock for the limiting reference has such a contained replacement.

If some late tracker row uses the large branch of `MaximalUpTo`, the local
replacement hypothesis and uniform hammock transport give the answer
directly.  Otherwise every late row is inclusion-maximal.  The coherent tail
is then globally inclusion-maximal; a global successor-sized hammock forces
that tail to have cardinality greater than `kappa`, and a successor-sized
subfamily of the contained tail is the required witness.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}

/-- A coherent tracker transfers the existence of a successor-sized
limiting hammock to a successor-sized hammock contained in `Z`, provided
each sufficiently late stage has the corresponding contained local
replacement property. -/
theorem exists_contained_limit_largeHammock
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (x : V) (e : AltEnd V) (a0 : Ladder.Stage (succ kappa)) {Z : Set V}
    (hcontained : ∀ a, a0 ≤ a →
      HammockContained (chosenAt Gamma kappa L.warpAt x e a) Z)
    (hLocalLarge : ∀ a, a0 ≤ a →
      HasHammockCard Gamma (L.warpAt a) x e (succ kappa) →
        ∃ K : Set (AltPath Gamma.graph),
          Hammock Gamma (L.warpAt a) x e K ∧
          #K = succ kappa ∧ HammockContained K Z)
    (hGlobalLarge : HasHammockCard Gamma L.limitWarp x e (succ kappa)) :
    ∃ K : Set (AltPath Gamma.graph),
      Hammock Gamma L.limitWarp x e K ∧
      #K = succ kappa ∧ HammockContained K Z := by
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
  · let T := tailFamily L x e d
    have hTmax : Maximal (fun H ↦ Hammock Gamma L.limitWarp x e H) T :=
      tailFamily_maximal hL x e d hglobal hmono hmax
    have hTcontained : HammockContained T Z :=
      tailFamily_contained x e d
        (fun a hda ↦ hcontained a (ha0.trans hda))
    have hTlarge : succ kappa ≤ #T := by
      apply succ_le_of_lt
      by_contra hsmall
      exact (not_hasHammockCard_succ_of_maximal_of_card_le
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
      intro v hv
      simp only [hammockVertexSet, Set.mem_iUnion] at hv ⊢
      obtain ⟨Q, hQK, hvQ⟩ := hv
      exact hTcontained (Set.mem_iUnion.2 ⟨Q,
        Set.mem_iUnion.2 ⟨hKT hQK, hvQ⟩⟩)
    exact ⟨K, hTmax.1.subset hKT, hKcard, hKcontained⟩
  · push Not at hmax
    obtain ⟨a, hda, hnotmax⟩ := hmax
    have hspec := (at_spec Gamma kappa hkappa L.warpAt
      (safeConvex_of_deferred Gamma kappa hL) x e a).1
    rcases hspec with hsmall | hlarge
    · exact (hnotmax hsmall.2.1).elim
    · have hLocalWitness :
          HasHammockCard Gamma (L.warpAt a) x e (succ kappa) :=
        ⟨hlarge.2.2.choose, hlarge.2.2.choose_spec.1,
          hlarge.2.2.choose_spec.2⟩
      obtain ⟨K, hK, hKcard, hKcontained⟩ :=
        hLocalLarge a (ha0.trans hda) hLocalWitness
      exact ⟨K, htransport a (hd1.trans hda) K hK,
        hKcard, hKcontained⟩

#print axioms exists_contained_limit_largeHammock

end Erdos599.Blueprint.CoherentHammockTracker
