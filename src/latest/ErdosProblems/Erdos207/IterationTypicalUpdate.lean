/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTypical

/-!
# Deterministic stability of iteration typicality

The probabilistic part of the master update only needs to bound what is lost
from old degree and extension sets.  This file isolates that deterministic
argument: subset monotonicity gives every upper bound, and a loss of at most
`(xi' - xi)` times the target preserves the lower multiplicative window.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A subset of an old finite set remains in a wider multiplicative window
provided the deleted part is bounded by the increase in relative error. -/
lemma WithinMultiplicativeError.card_subset_of_loss
    {X : Type*} [DecidableEq X]
    {old new : Finset X} {xi xi' target : ℝ≥0}
    (hwindow : WithinMultiplicativeError xi (old.card : ℝ≥0) target)
    (hsub : new ⊆ old) (hxi : xi ≤ xi')
    (hloss : ((old \ new).card : ℝ≥0) ≤ (xi' - xi) * target) :
    WithinMultiplicativeError xi' (new.card : ℝ≥0) target := by
  constructor
  · by_cases hlarge : 1 ≤ xi'
    · simp only [tsub_eq_zero_of_le hlarge, zero_mul, zero_le]
    · have hxi'one : xi' ≤ 1 := le_of_not_ge hlarge
      have hxione : xi ≤ 1 := hxi.trans hxi'one
      have hsplit :
          (1 - xi') * target + (xi' - xi) * target =
            (1 - xi) * target := by
        apply NNReal.eq
        push_cast
        rw [NNReal.coe_sub hxi'one, NNReal.coe_sub hxi,
          NNReal.coe_sub hxione]
        ring
      have hcard : old.card = (old \ new).card + new.card := by
        rw [card_sdiff_add_card_eq_card hsub]
      have hsum :
          (1 - xi') * target + ((old \ new).card : ℝ≥0) ≤
            (new.card : ℝ≥0) + ((old \ new).card : ℝ≥0) := by
        calc
          (1 - xi') * target + ((old \ new).card : ℝ≥0) ≤
              (1 - xi') * target + (xi' - xi) * target := by gcongr
          _ = (1 - xi) * target := hsplit
          _ ≤ (old.card : ℝ≥0) := hwindow.1
          _ = (new.card : ℝ≥0) + ((old \ new).card : ℝ≥0) := by
            exact_mod_cast (by omega : old.card = new.card + (old \ new).card)
      exact (add_le_add_iff_right
        ((old \ new).card : ℝ≥0)).mp (by
          simpa only [add_comm] using hsum)
  · calc
      (new.card : ℝ≥0) ≤ (old.card : ℝ≥0) := by
        exact_mod_cast card_le_card hsub
      _ ≤ (1 + xi) * target := hwindow.2
      _ ≤ (1 + xi') * target := by gcongr

lemma neighborsIn_mono_graph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G' G : SimpleGraph V} (hGG : G' ≤ G) (U : Finset V) (v : V) :
    neighborsIn G' U v ⊆ neighborsIn G U v := by
  intro w hw
  rw [mem_neighborsIn_iff] at hw ⊢
  exact ⟨hw.1, hGG hw.2⟩

/-- Typicality passes to graph/availability subsets when every tested degree
and extension set loses at most the extra relative error budget. -/
theorem IsIterationTypical.of_subset_loss
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {G G' : SimpleGraph V} {A A' : TripleSystemOn V}
    {p eta xi xi' : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta xi h)
    (hkn : k ≤ next) (hGG : G' ≤ G) (hAA : A' ⊆ A)
    (hxi : xi ≤ xi')
    (hdegreeSame : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn G (W.U i.castSucc) v) \
          neighborsIn G' (W.U i.castSucc) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeNext : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn G (W.U i.succ) v) \
          neighborsIn G' (W.U i.succ) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.succ).card))
    (hextension : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V, Q ≤ G' →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      (((iterationExtensionVertices A Q (W.U iStar)) \
          iterationExtensionVertices A' Q (W.U iStar)).card : ℝ≥0) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    IsIterationTypical W next G' A' p eta xi' h := by
  refine ⟨?_, ?_⟩
  · intro i hnexti
    have hki : k.val ≤ i.val :=
      (show k.val ≤ next.val from hkn).trans hnexti
    refine ⟨?_, ?_⟩
    · intro v hv
      apply (htyp.1 i hki).1 v hv |>.card_subset_of_loss
      · exact neighborsIn_mono_graph hGG _ _
      · exact hxi
      · exact hdegreeSame i hnexti v hv
    · intro v hv
      apply (htyp.1 i hki).2 v hv |>.card_subset_of_loss
      · exact neighborsIn_mono_graph hGG _ _
      · exact hxi
      · exact hdegreeNext i hnexti v hv
  · intro i hnexti iStar hiStar Q hQG' hQU hQcard
    have hki : k.val ≤ i.val :=
      (show k.val ≤ next.val from hkn).trans hnexti
    apply (htyp.2 i hki iStar hiStar Q (hQG'.trans hGG) hQU hQcard)
      |>.card_subset_of_loss
    · exact iterationExtensionVertices_mono_available hAA Q (W.U iStar)
    · exact hxi
    · exact hextension i hnexti iStar hiStar Q hQG' hQU hQcard

end

end Erdos207
