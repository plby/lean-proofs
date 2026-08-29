/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SeededHammockExtension
import ErdosProblems.Erdos599.HalfwayClubGeometry
import ErdosProblems.Erdos599.DeferredStageSafeConvexity

/-!
# A prefix-causal coherent tracker for stage hammocks

At a stage below `kappa⁺`, retain every earlier selected path which is still
safe for the current reference, and extend that seed to a hammock maximal
up to `kappa`.  There are at most `kappa` earlier stages, so the seed stays
small.  Order-convexity of safeness guarantees its pairwise compatibility.
The defining recursion is total and uses only reference stages through the
current stage; this causality is needed by the simultaneous ladder/row rule.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} (Gamma : DWeb V) (kappa : Cardinal.{u})

/-- Earlier selected paths which remain safe at the current stage. -/
def survivorSeed (Y : Set Gamma.DPath) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa), b < a → Set (AltPath Gamma.graph)) :
    Set (AltPath Gamma.graph) :=
  {Q | (∃ b, ∃ hba : b < a, Q ∈ prior b hba) ∧ IsSafe Y Q}

/-- The coherent choices depend on no future reference stage. -/
def chosenAt (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (x : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  WellFounded.fix wellFounded_lt
    (fun b prior ↦ seededHammockExtension Gamma (reference b) kappa x e
      (survivorSeed Gamma kappa (reference b) b prior)) a

theorem at_eq (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (x : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    chosenAt Gamma kappa reference x e a =
      seededHammockExtension Gamma (reference a) kappa x e
        (survivorSeed Gamma kappa (reference a) a
          (fun b _hba ↦ chosenAt Gamma kappa reference x e b)) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun b prior ↦ seededHammockExtension Gamma (reference b) kappa x e
      (survivorSeed Gamma kappa (reference b) b prior)) a

/-- The total selector always has the advertised cardinal bound, whether
or not a supplied arbitrary reference process satisfies the validity laws. -/
theorem card_at_le (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (x : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    #(chosenAt Gamma kappa reference x e a) ≤ kappa := by
  rw [at_eq]
  exact seededHammockExtension_card_le Gamma (reference a) kappa x e _ hkappa

theorem survivorSeed_card_le (hkappa : aleph0 ≤ kappa)
    (Y : Set Gamma.DPath) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa), b < a → Set (AltPath Gamma.graph))
    (hprior : ∀ b hba, #(prior b hba) ≤ kappa) :
    #(survivorSeed Gamma kappa Y a prior) ≤ kappa := by
  have hsub : survivorSeed Gamma kappa Y a prior ⊆
      LinkageBlueprint.ClubStageGeometry.CausalClosureSystem.priorUnion a prior := by
    rintro Q ⟨⟨b, hba, hQ⟩, _hsafe⟩
    exact Set.mem_iUnion.2 ⟨⟨b, hba⟩, hQ⟩
  exact (Cardinal.mk_subtype_mono hsub).trans
    (LinkageBlueprint.ClubStageGeometry.CausalClosureSystem.mk_priorUnion_le
      hkappa a prior hprior)

/-- Agreement through one stage gives exactly the same coherent choice at
that stage.  Thus a truncated prior ladder can compute the next row. -/
theorem at_congr_le
    (reference reference' : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (x : V) (e : AltEnd V) :
    ∀ a : Ladder.Stage (succ kappa),
      (∀ b, b ≤ a → reference b = reference' b) →
      chosenAt Gamma kappa reference x e a = chosenAt Gamma kappa reference' x e a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih hprefix
  rw [at_eq, at_eq, hprefix a le_rfl]
  apply congrArg (seededHammockExtension Gamma (reference' a) kappa x e)
  ext Q
  simp only [survivorSeed, Set.mem_ofPred_eq]
  have hprevious :
      (∃ b, ∃ hba : b < a, Q ∈ chosenAt Gamma kappa reference x e b) ↔
        ∃ b, ∃ hba : b < a, Q ∈ chosenAt Gamma kappa reference' x e b := by
    constructor
    · rintro ⟨b, hba, hQ⟩
      refine ⟨b, hba, ?_⟩
      rw [← ih b hba (fun c hcb ↦ hprefix c (hcb.trans hba.le))]
      exact hQ
    · rintro ⟨b, hba, hQ⟩
      refine ⟨b, hba, ?_⟩
      rw [ih b hba (fun c hcb ↦ hprefix c (hcb.trans hba.le))]
      exact hQ
  exact and_congr_left (fun _ ↦ hprevious)

/-- No-loss-and-recovery is the exact stagewise law required to retain
all surviving older paths simultaneously. -/
def SafeConvex (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath) : Prop :=
  ∀ a b c, a ≤ b → b ≤ c → ∀ Q : AltPath Gamma.graph,
    IsSafe (reference a) Q → IsSafe (reference c) Q → IsSafe (reference b) Q

/-- Actual validity and coherence of the prefix-causal tracker. -/
theorem at_spec (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (hconvex : SafeConvex Gamma kappa reference) (x : V) (e : AltEnd V) :
    ∀ a : Ladder.Stage (succ kappa),
      HammockMaximalUpTo Gamma (reference a) x e kappa
        (chosenAt Gamma kappa reference x e a) ∧
      ∀ b, b < a → ∀ Q ∈ chosenAt Gamma kappa reference x e b,
        IsSafe (reference a) Q → Q ∈ chosenAt Gamma kappa reference x e a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih
  let seed := survivorSeed Gamma kappa (reference a) a
    (fun b _hba ↦ chosenAt Gamma kappa reference x e b)
  have hseed : Hammock Gamma (reference a) x e seed := by
    constructor
    · rintro Q ⟨⟨b, hba, hQb⟩, hsafe⟩
      exact ⟨hsafe, ((ih b hba).1.isHammock.1 Q hQb).2⟩
    · rintro Q ⟨⟨b, hba, hQb⟩, hQsafe⟩
        R ⟨⟨c, hca, hRc⟩, hRsafe⟩ hQR
      rcases lt_trichotomy b c with hbc | rfl | hcb
      · have hQsafeC := hconvex b c a hbc.le hca.le Q
          ((ih b hba).1.isHammock.1 Q hQb).1 hQsafe
        have hQc := (ih c hca).2 b hbc Q hQb hQsafeC
        exact (ih c hca).1.isHammock.2 hQc hRc hQR
      · exact (ih b hba).1.isHammock.2 hQb hRc hQR
      · have hRsafeB := hconvex c b a hcb.le hba.le R
          ((ih c hca).1.isHammock.1 R hRc).1 hRsafe
        have hRb := (ih b hba).2 c hcb R hRc hRsafeB
        exact (ih b hba).1.isHammock.2 hQb hRb hQR
  have hsmall : #seed ≤ kappa :=
    survivorSeed_card_le Gamma kappa hkappa (reference a) a _
      (fun b _hba ↦ card_at_le Gamma kappa hkappa reference x e b)
  have hchosen := seededHammockExtension_spec Gamma (reference a) kappa x e
    seed hkappa hseed hsmall
  rw [at_eq]
  refine ⟨hchosen.2, ?_⟩
  intro b hba Q hQ hsafe
  exact hchosen.1 ⟨⟨b, hba, hQ⟩, hsafe⟩

/-- The safeness-convexity premise is proved for a genuine deferred ladder. -/
theorem safeConvex_of_deferred
    {L : Gamma.KappaLadder (succ kappa)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    SafeConvex Gamma kappa L.warpAt := by
  intro a b c hab hbc Q hQa hQc
  exact hL.isSafe_warpAt_of_le_of_le hab hbc hQa hQc

#print axioms at_congr_le
#print axioms at_spec

end Erdos599.Blueprint.CoherentHammockTracker
