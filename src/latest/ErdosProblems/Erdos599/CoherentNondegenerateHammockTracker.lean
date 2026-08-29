/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CoherentHammockTracker
import ErdosProblems.Erdos599.FilteredNondegenerateHammockExtension
import ErdosProblems.Erdos599.DeferredNondegenerateHammockTransport

/-!
# A roof-filtered coherent nondegenerate-hammock tracker

The filter is part of the selected family, not a conclusion inferred from
safeness.  This is the precise extra invariant needed to preserve
nondegeneracy while the ladder reference grows.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.CoherentNondegenerateHammockTracker

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} (Gamma : DWeb V) (kappa : Cardinal.{u})

def Roofed (roofAt : Ladder.Stage (succ kappa) → Set V)
    (a : Ladder.Stage (succ kappa)) (Q : AltPath Gamma.graph) : Prop :=
  Q.vertexSet ⊆ roofAt a

/-- Earlier choices which still satisfy all three current-stage
requirements: safety, nondegeneracy, and roof containment. -/
def survivorSeed
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V) (v : V)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa), b < a →
      Set (AltPath Gamma.graph)) : Set (AltPath Gamma.graph) :=
  {Q | (∃ b, ∃ hba : b < a, Q ∈ prior b hba) ∧
    IsSafe (reference a) Q ∧
    ¬IsDegenerate (reference a) Q (.vertex v) ∧ Roofed Gamma kappa roofAt a Q}

/-- The choice reads only the reference and roof rows through its current
stage, so it can be inserted into a causal row construction. -/
def chosenAt
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  WellFounded.fix wellFounded_lt
    (fun b prior ↦ seededFilteredNondegenerateHammockExtension
      Gamma (reference b) kappa x (.vertex v)
      (Roofed Gamma kappa roofAt b)
      (survivorSeed Gamma kappa reference roofAt v b prior)) a

theorem at_eq
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    chosenAt Gamma kappa reference roofAt x v a =
      seededFilteredNondegenerateHammockExtension
        Gamma (reference a) kappa x (.vertex v)
        (Roofed Gamma kappa roofAt a)
        (survivorSeed Gamma kappa reference roofAt v a
          (fun b _hba ↦ chosenAt Gamma kappa reference roofAt x v b)) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun b prior ↦ seededFilteredNondegenerateHammockExtension
      Gamma (reference b) kappa x (.vertex v)
      (Roofed Gamma kappa roofAt b)
      (survivorSeed Gamma kappa reference roofAt v b prior)) a

theorem card_at_le (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    #(chosenAt Gamma kappa reference roofAt x v a) ≤ kappa := by
  rw [at_eq]
  exact seededFilteredNondegenerateHammockExtension_card_le
    Gamma (reference a) kappa x (.vertex v) _ _ hkappa

theorem survivorSeed_card_le (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V) (v : V)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa), b < a →
      Set (AltPath Gamma.graph))
    (hprior : ∀ b hba, #(prior b hba) ≤ kappa) :
    #(survivorSeed Gamma kappa reference roofAt v a prior) ≤ kappa := by
  have hsub : survivorSeed Gamma kappa reference roofAt v a prior ⊆
      LinkageBlueprint.ClubStageGeometry.CausalClosureSystem.priorUnion a prior := by
    rintro Q ⟨⟨b, hba, hQ⟩, _⟩
    exact Set.mem_iUnion.2 ⟨⟨b, hba⟩, hQ⟩
  exact (Cardinal.mk_subtype_mono hsub).trans
    (LinkageBlueprint.ClubStageGeometry.CausalClosureSystem.mk_priorUnion_le
      hkappa a prior hprior)

/-- Prefix agreement for both inputs gives the identical current choice. -/
theorem at_congr_le
    (reference reference' : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt roofAt' : Ladder.Stage (succ kappa) → Set V) (x v : V) :
    ∀ a : Ladder.Stage (succ kappa),
      (∀ b, b ≤ a → reference b = reference' b) →
      (∀ b, b ≤ a → roofAt b = roofAt' b) →
      chosenAt Gamma kappa reference roofAt x v a =
        chosenAt Gamma kappa reference' roofAt' x v a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih href hroof
  rw [at_eq, at_eq, href a le_rfl]
  have hP : Roofed Gamma kappa roofAt a = Roofed Gamma kappa roofAt' a := by
    unfold Roofed
    rw [hroof a le_rfl]
  rw [hP]
  apply congrArg (seededFilteredNondegenerateHammockExtension
    Gamma (reference' a) kappa x (.vertex v)
      (Roofed Gamma kappa roofAt' a))
  ext Q
  simp only [survivorSeed, Set.mem_ofPred_eq]
  have hprevious :
      (∃ b, ∃ hba : b < a,
        Q ∈ chosenAt Gamma kappa reference roofAt x v b) ↔
      ∃ b, ∃ hba : b < a,
        Q ∈ chosenAt Gamma kappa reference' roofAt' x v b := by
    constructor
    · rintro ⟨b, hba, hQ⟩
      refine ⟨b, hba, ?_⟩
      rw [← ih b hba
        (fun c hcb ↦ href c (hcb.trans hba.le))
        (fun c hcb ↦ hroof c (hcb.trans hba.le))]
      exact hQ
    · rintro ⟨b, hba, hQ⟩
      refine ⟨b, hba, ?_⟩
      rw [ih b hba
        (fun c hcb ↦ href c (hcb.trans hba.le))
        (fun c hcb ↦ hroof c (hcb.trans hba.le))]
      exact hQ
  rw [href a le_rfl, hP]
  exact and_congr hprevious Iff.rfl

/-- The filtered properties persist along the stage order for paths having
the fixed endpoints of the tracked hammock. -/
def FilteredPersistent
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V) (x v : V) : Prop :=
  ∀ a b, a ≤ b → ∀ Q : AltPath Gamma.graph,
    Q.initial = x → Q.terminal? = some v →
    ¬IsDegenerate (reference a) Q (.vertex v) →
    Roofed Gamma kappa roofAt a Q →
    ¬IsDegenerate (reference b) Q (.vertex v) ∧
      Roofed Gamma kappa roofAt b Q

/-- Stage validity and retention of every path satisfying the current
filtered conditions.  No unproved monotonicity is hidden here. -/
theorem at_spec (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (hconvex : CoherentHammockTracker.SafeConvex Gamma kappa reference)
    (x v : V)
    (hpersist : FilteredPersistent Gamma kappa reference roofAt x v) :
    ∀ a : Ladder.Stage (succ kappa),
      FilteredNondegenerateHammockMaximalUpTo Gamma (reference a)
        x (.vertex v) (Roofed Gamma kappa roofAt a) kappa
        (chosenAt Gamma kappa reference roofAt x v a) ∧
      ∀ b, b < a → ∀ Q ∈ chosenAt Gamma kappa reference roofAt x v b,
        IsSafe (reference a) Q →
        ¬IsDegenerate (reference a) Q (.vertex v) →
        Roofed Gamma kappa roofAt a Q →
        Q ∈ chosenAt Gamma kappa reference roofAt x v a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih
  let seed := survivorSeed Gamma kappa reference roofAt v a
    (fun b _hba ↦ chosenAt Gamma kappa reference roofAt x v b)
  have hseed : FilteredNondegenerateHammock Gamma (reference a)
      x (.vertex v) (Roofed Gamma kappa roofAt a) seed := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro Q ⟨⟨b, hba, hQb⟩, hsafe, _hnondeg, _hroof⟩
      exact ⟨hsafe,
        ((ih b hba).1.isFilteredNondegenerateHammock.1.1.1 Q hQb).2⟩
    · rintro Q ⟨⟨b, hba, hQb⟩, hQsafe, _hQnondeg, _hQroof⟩
        R ⟨⟨c, hca, hRc⟩, hRsafe, _hRnondeg, _hRroof⟩ hQR
      rcases lt_trichotomy b c with hbc | rfl | hcb
      · have hQsafeC := hconvex b c a hbc.le hca.le Q
          ((ih b hba).1.isFilteredNondegenerateHammock.1.1.1 Q hQb).1
          hQsafe
        have hQpersistent := hpersist b c hbc.le Q
          ((ih b hba).1.isFilteredNondegenerateHammock.1.1.1 Q hQb).2.1
          ((ih b hba).1.isFilteredNondegenerateHammock.1.1.1 Q hQb).2.2
          ((ih b hba).1.isFilteredNondegenerateHammock.1.2 Q hQb)
          ((ih b hba).1.isFilteredNondegenerateHammock.2 Q hQb)
        have hQc := (ih c hca).2 b hbc Q hQb hQsafeC
          hQpersistent.1 hQpersistent.2
        exact (ih c hca).1.isFilteredNondegenerateHammock.1.1.2
          hQc hRc hQR
      · exact (ih b hba).1.isFilteredNondegenerateHammock.1.1.2
          hQb hRc hQR
      · have hRsafeB := hconvex c b a hcb.le hba.le R
          ((ih c hca).1.isFilteredNondegenerateHammock.1.1.1 R hRc).1
          hRsafe
        have hRpersistent := hpersist c b hcb.le R
          ((ih c hca).1.isFilteredNondegenerateHammock.1.1.1 R hRc).2.1
          ((ih c hca).1.isFilteredNondegenerateHammock.1.1.1 R hRc).2.2
          ((ih c hca).1.isFilteredNondegenerateHammock.1.2 R hRc)
          ((ih c hca).1.isFilteredNondegenerateHammock.2 R hRc)
        have hRb := (ih b hba).2 c hcb R hRc hRsafeB
          hRpersistent.1 hRpersistent.2
        exact (ih b hba).1.isFilteredNondegenerateHammock.1.1.2
          hQb hRb hQR
    · rintro Q ⟨_hprior, _hsafe, hnondeg, _hroof⟩
      exact hnondeg
    · rintro Q ⟨_hprior, _hsafe, _hnondeg, hroof⟩
      exact hroof
  have hsmall : #seed ≤ kappa :=
    survivorSeed_card_le Gamma kappa hkappa reference roofAt v a _
      (fun b _hba ↦ card_at_le Gamma kappa hkappa reference roofAt x v b)
  have hchosen := seededFilteredNondegenerateHammockExtension_spec
    Gamma (reference a) kappa x (.vertex v)
      (Roofed Gamma kappa roofAt a) seed hkappa hseed hsmall
  rw [at_eq]
  refine ⟨hchosen.2, ?_⟩
  intro b hba Q hQ hsafe hnondeg hroof
  exact hchosen.1 ⟨⟨b, hba, hQ⟩, hsafe, hnondeg, hroof⟩

/-- The exact transport theorem proves filtered persistence for a deferred
ladder when the two fixed endpoints are distinct. -/
theorem filteredPersistent_of_deferred
    {L : Gamma.KappaLadder (succ kappa)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) :
    FilteredPersistent Gamma kappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c)) x v := by
  intro a b hab Q hstart hterminal hnondeg hroof
  have hpersist :=
    DWeb.KappaLadder.Deferred.roofedNondegenerate_warpAt_mono hL hab
      hterminal (hstart.trans_ne hne) hroof hnondeg
  exact ⟨hpersist.2, hpersist.1⟩

/-- On a deferred ladder, roofed nondegeneracy supplies the two filtered
conditions automatically at every later stage; only safeness remains as a
retention premise. -/
theorem retained_of_deferred
    {L : Gamma.KappaLadder (succ kappa)}
    (hkappa : aleph0 ≤ kappa)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x v : V} (hne : x ≠ v) {a b : Ladder.Stage (succ kappa)}
    (hab : a < b) {Q : AltPath Gamma.graph}
    (hQa : Q ∈ chosenAt Gamma kappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c)) x v a)
    (hsafe : IsSafe (L.warpAt b) Q) :
    Q ∈ chosenAt Gamma kappa L.warpAt
      (fun c ↦ Gamma.roof (L.frontier c)) x v b := by
  have hspec := at_spec Gamma kappa hkappa L.warpAt
    (fun c ↦ Gamma.roof (L.frontier c))
    (CoherentHammockTracker.safeConvex_of_deferred Gamma kappa hL)
    x v (filteredPersistent_of_deferred Gamma kappa hL hne)
  have hQaData := (hspec a).1.isFilteredNondegenerateHammock
  have hQend := (hQaData.1.1.1 Q hQa).2.2
  have hQstart := (hQaData.1.1.1 Q hQa).2.1
  have hneQ : Q.initial ≠ v := hQstart.trans_ne hne
  have hpersist :=
    DWeb.KappaLadder.Deferred.roofedNondegenerate_warpAt_mono hL hab.le
      hQend hneQ (hQaData.2 Q hQa) (hQaData.1.2 Q hQa)
  exact (hspec b).2 a hab Q hQa hsafe hpersist.2 hpersist.1

#print axioms at_congr_le
#print axioms at_spec
#print axioms filteredPersistent_of_deferred
#print axioms retained_of_deferred

end Erdos599.Blueprint.CoherentNondegenerateHammockTracker
