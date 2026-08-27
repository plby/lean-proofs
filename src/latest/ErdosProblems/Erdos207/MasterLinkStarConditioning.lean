/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointInclusionCardTail
import ErdosProblems.Erdos207.MasterLinkDegreeLoss

/-!
# Conditioning a link kernel on all vertex-star caps

The simultaneous link law is conditioned, separately in every old-state
fiber, on the event that no vertex lies in too many selected link triangles.
The binomial C4 tail proves positivity uniformly.  The resulting kernel is
supported both on its old structural property and all star caps, and retains
an exponential C4 estimate with the reciprocal conditioning loss absorbed
into the base.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- All selected triangle stars obey their prescribed strict caps. -/
def LinkStarCapsGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (caps : V -> Nat) (M : TripleSystemOn V) : Prop :=
  ∀ v : V, (ambientTriplesThrough v ∩ M).card < caps v

/-- A link law conditioned on all vertex-star caps. -/
def starCappedLinkLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : FiniteLaw (TripleSystemOn V)) (caps : V -> Nat)
    (hGood : 0 < L.probability (LinkStarCapsGood caps)) :
    FiniteLaw (TripleSystemOn V) :=
  L.conditionOn (LinkStarCapsGood caps) hGood

/-- A C4 estimate for an arbitrary selected-family map gives the same
simultaneous vertex-star tail bound. -/
theorem probability_not_linkStarCapsGood_selected_le
    {Omega V : Type*} [Fintype Omega]
    [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (caps : V → Nat) (alpha epsilon : NNReal)
    (hC4 : ∀ Q : TripleSystemOn V,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ alpha ^ Q.card)
    (htail : ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps v)).card *
        alpha ^ caps v ≤ epsilon) :
    L.probability (fun omega ↦
      ¬ LinkStarCapsGood caps (selected omega)) ≤ epsilon := by
  calc
    L.probability (fun omega ↦
        ¬ LinkStarCapsGood caps (selected omega)) ≤
        L.probability (fun omega ↦ Exists fun v : V ↦
          caps v ≤ (ambientTriplesThrough v ∩ selected omega).card) := by
      apply L.probability_mono
      intro omega hbad
      unfold LinkStarCapsGood at hbad
      push Not at hbad
      exact hbad
    _ ≤ ∑ v : V, L.probability (fun omega ↦
        caps v ≤ (ambientTriplesThrough v ∩ selected omega).card) := by
      simpa using L.probability_exists_le (univ : Finset V)
        (fun v omega ↦
          caps v ≤ (ambientTriplesThrough v ∩ selected omega).card)
    _ ≤ ∑ v : V,
        ((ambientTriplesThrough v).powersetCard (caps v)).card *
          alpha ^ caps v := by
      apply sum_le_sum
      intro v _hv
      exact L.probability_card_inter_selected_ge_le_of_card_jointInclusion
        selected (ambientTriplesThrough v) alpha (caps v) hC4
    _ ≤ epsilon := htail

/-- The same binomial union bound, before conditioning: failure of any
vertex-star cap has probability at most the displayed tail sum. -/
theorem probability_not_linkStarCapsGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : FiniteLaw (TripleSystemOn V)) (caps : V -> Nat)
    (alpha epsilon : NNReal)
    (hC4 : ∀ Q : TripleSystemOn V,
      L.probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
    (htail : ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps v)).card *
        alpha ^ caps v <= epsilon) :
    L.probability (fun M => ¬ LinkStarCapsGood caps M) <= epsilon :=
  probability_not_linkStarCapsGood_selected_le L
    (fun M : TripleSystemOn V ↦ M) caps alpha epsilon hC4 htail

/-- Pointwise construction of a star-capped link law. -/
theorem exists_starCappedLinkLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : FiniteLaw (TripleSystemOn V)) (caps : V -> Nat)
    (alpha epsilon : NNReal)
    (hC4 : ∀ Q : TripleSystemOn V,
      L.probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
    (htail : ∑ v : V,
        ((ambientTriplesThrough v).powersetCard (caps v)).card *
          alpha ^ caps v <= epsilon)
    (hepsilon : epsilon < 1) :
    Exists fun hGood : 0 < L.probability (LinkStarCapsGood caps) =>
      (starCappedLinkLaw L caps hGood).SupportedOn
          (LinkStarCapsGood caps) ∧
      (∀ Q : TripleSystemOn V,
        (starCappedLinkLaw L caps hGood).probability
            (fun M => Q ⊆ M) <=
          (alpha / (1 - epsilon)) ^ Q.card) ∧
      1 - epsilon <= L.probability (LinkStarCapsGood caps) := by
  have h := L.exists_conditionOn_cardCaps_of_jointInclusion_of_sum_le
    (fun M : TripleSystemOn V => M)
    ambientTriplesThrough caps (univ : Finset V) alpha epsilon hC4
    (by simpa using htail) hepsilon
  unfold starCappedLinkLaw LinkStarCapsGood
  simpa only [mem_univ, forall_const] using h

/-- Simultaneously star-condition every fiber of a state-dependent link
kernel, preserving any property that already held throughout its support. -/
theorem exists_starCappedLinkKernel
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    (K : Omega -> FiniteLaw (TripleSystemOn V))
    (caps : Omega -> V -> Nat) (P : Omega -> TripleSystemOn V -> Prop)
    (alpha epsilon : NNReal)
    (hP : ∀ omega, (K omega).SupportedOn (P omega))
    (hC4 : ∀ omega Q,
      (K omega).probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
    (htail : ∀ omega, ∑ v : V,
        ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
          alpha ^ caps omega v <= epsilon)
    (hepsilon : epsilon < 1) :
    ∃ hGood : ∀ omega,
        0 < (K omega).probability (LinkStarCapsGood (caps omega)),
      let Kc : Omega -> FiniteLaw (TripleSystemOn V) := fun omega =>
        starCappedLinkLaw (K omega) (caps omega) (hGood omega)
      (∀ omega, (Kc omega).SupportedOn fun M =>
        P omega M ∧ LinkStarCapsGood (caps omega) M) ∧
      (∀ omega Q,
        (Kc omega).probability (fun M => Q ⊆ M) <=
          (alpha / (1 - epsilon)) ^ Q.card) ∧
      (∀ omega, 1 - epsilon <=
        (K omega).probability (LinkStarCapsGood (caps omega))) := by
  have hex : ∀ omega, Exists fun hGood :
      0 < (K omega).probability (LinkStarCapsGood (caps omega)) =>
      (starCappedLinkLaw (K omega) (caps omega) hGood).SupportedOn
          (LinkStarCapsGood (caps omega)) ∧
      (∀ Q : TripleSystemOn V,
        (starCappedLinkLaw (K omega) (caps omega) hGood).probability
            (fun M => Q ⊆ M) <=
          (alpha / (1 - epsilon)) ^ Q.card) ∧
      1 - epsilon <=
        (K omega).probability (LinkStarCapsGood (caps omega)) := by
    intro omega
    exact exists_starCappedLinkLaw (K omega) (caps omega) alpha epsilon
      (hC4 omega) (htail omega) hepsilon
  choose hGood hsupp hC4c hlower using hex
  refine ⟨hGood, ?_, hC4c, hlower⟩
  intro omega M hmass
  exact ⟨(hP omega).conditionOn (hGood omega) M hmass,
    hsupp omega M hmass⟩

end

end Erdos207
