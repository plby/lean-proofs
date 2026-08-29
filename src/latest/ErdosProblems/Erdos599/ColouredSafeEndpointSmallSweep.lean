/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStableState

/-!
# Completing one small carrier by a bounded ordinal sweep

Each requested vertex is from the seed carrier, so it persists until its
turn. Proper limits use the actual endpoint graph and the checked accounting
invariants. This lemma is instantiated with the constructed causal successor
in `HalfwayCausalEndpointFairCompletion`.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

def HasCompletionSuccessor (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (Z : Set V) :
    Prop := ∀ (S : StableState C Z) x, x ∈ S.carrier →
      ∃ T : StableState C Z, S.Extends T ∧ x ∈ T.completed

def requestedStep (advance : HasCompletionSuccessor C Z) (S : StableState C Z)
    (request : Option V) : StableState C Z := by
  classical
  exact match request with
    | none => S
    | some x => if hx : x ∈ S.carrier then (advance S x hx).choose else S

theorem requestedStep_extends (advance : HasCompletionSuccessor C Z)
    (S : StableState C Z) (request : Option V) : S.Extends (requestedStep advance S request) := by
  classical
  cases request with
  | none => exact Extends.refl S
  | some x =>
      by_cases hx : x ∈ S.carrier
      · simpa only [requestedStep, dif_pos hx] using (advance S x hx).choose_spec.1
      · simpa only [requestedStep, dif_neg hx] using Extends.refl S

theorem requestedStep_completed (advance : HasCompletionSuccessor C Z)
    (S : StableState C Z) (x : V) (hx : x ∈ S.carrier) :
    x ∈ (requestedStep advance S (some x)).completed := by
  classical
  simpa only [requestedStep, dif_pos hx] using (advance S x hx).choose_spec.2

def ordinalUpper (o : Ordinal.{u}) (ho : IsSuccLimit o) (hcard : o.card ≤ kappa)
    (prior : Set.Iio o → StableState C Z)
    (hprior : ∀ ⦃i j⦄, i ≤ j → (prior i).Extends (prior j)) : StableState C Z :=
  (exists_ordinalUpper o ho hcard prior hprior).choose

theorem extends_ordinalUpper (o : Ordinal.{u}) (ho : IsSuccLimit o) (hcard : o.card ≤ kappa)
    (prior : Set.Iio o → StableState C Z)
    (hprior : ∀ ⦃i j⦄, i ≤ j → (prior i).Extends (prior j)) (i : Set.Iio o) :
    (prior i).Extends (ordinalUpper o ho hcard prior hprior) :=
  (exists_ordinalUpper o ho hcard prior hprior).choose_spec i

def limitOrSeed (seed : StableState C Z) (length : Ordinal.{u}) (hcard : length.card ≤ kappa)
    (o : Ordinal.{u}) (ho : IsSuccLimit o)
    (prior : ∀ a : Ordinal.{u}, a < o → StableState C Z) : StableState C Z := by
  classical
  let family : Set.Iio o → StableState C Z := fun a ↦ prior a.1 a.2
  exact if hb : o ≤ length then
    if hcoherent : ∀ ⦃i j⦄, i ≤ j → (family i).Extends (family j) then
      ordinalUpper o ho ((Ordinal.card_le_card hb).trans hcard) family hcoherent
    else seed
  else seed

def run (advance : HasCompletionSuccessor C Z) (seed : StableState C Z)
    (length : Ordinal.{u}) (hcard : length.card ≤ kappa)
    (request : Ordinal.{u} → Option V) (o : Ordinal.{u}) : StableState C Z :=
  Ordinal.limitRecOn o seed
    (fun a S ↦ requestedStep advance S (request a))
    (fun a ha prior ↦ limitOrSeed seed length hcard a ha prior)

@[simp] theorem run_zero (advance : HasCompletionSuccessor C Z) (seed : StableState C Z)
    (length : Ordinal.{u}) (hcard : length.card ≤ kappa) (request : Ordinal.{u} → Option V) :
    run advance seed length hcard request 0 = seed := by
  simp [run]

@[simp] theorem run_add_one (advance : HasCompletionSuccessor C Z) (seed : StableState C Z)
    (length : Ordinal.{u}) (hcard : length.card ≤ kappa) (request : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) : run advance seed length hcard request (o + 1) =
      requestedStep advance (run advance seed length hcard request o) (request o) := by
  simp [run]

theorem run_limit (advance : HasCompletionSuccessor C Z) (seed : StableState C Z)
    (length : Ordinal.{u}) (hcard : length.card ≤ kappa) (request : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) (ho : IsSuccLimit o) : run advance seed length hcard request o =
      limitOrSeed seed length hcard o ho (fun a _ha ↦ run advance seed length hcard request a) := by
  simpa [run] using
    (Ordinal.limitRecOn_limit o seed
      (fun a S ↦ requestedStep advance S (request a))
      (fun a ha prior ↦ limitOrSeed seed length hcard a ha prior) ho)

/-- The fallback in `limitOrSeed` never occurs on the actual bounded run.
Every pair of its states has the full extension invariant. -/
theorem run_extends (advance : HasCompletionSuccessor C Z) (seed : StableState C Z)
    (length : Ordinal.{u}) (hcard : length.card ≤ kappa) (request : Ordinal.{u} → Option V) :
    ∀ b, b ≤ length → ∀ a, a ≤ b →
      (run advance seed length hcard request a).Extends
        (run advance seed length hcard request b) := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact Extends.refl _
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := Order.lt_add_one_iff.mp hab
        rw [run_add_one]
        have hb : b < b + 1 := Order.lt_add_one_iff.mpr le_rfl
        exact (ih (hb.le.trans hbLength) a hab').trans
          (requestedStep_extends advance _ _)
      · exact Extends.refl _
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b → StableState C Z :=
          fun c ↦ run advance seed length hcard request c.1
        have hcoherent : ∀ ⦃i j⦄, i ≤ j → (prior i).Extends (prior j) := by
          intro i j hij
          exact ih j.1 j.2 (j.2.le.trans hbLength) i.1 hij
        rw [run_limit advance seed length hcard request b hb, limitOrSeed, dif_pos hbLength]
        change (run advance seed length hcard request a).Extends
          (if h : ∀ ⦃i j⦄, i ≤ j → (prior i).Extends (prior j) then
            ordinalUpper b hb ((Ordinal.card_le_card hbLength).trans hcard) prior h else seed)
        rw [dif_pos hcoherent]
        exact extends_ordinalUpper b hb _ prior hcoherent ⟨a, hab⟩
      · exact Extends.refl _

/-- One bounded sweep completes every seed vertex, without requiring the
larger containing set `Z` to have cardinality at most `kappa`. -/
theorem exists_completedBatch (advance : HasCompletionSuccessor C Z) (seed : StableState C Z) :
    ∃ T : StableState C Z, seed.Extends T ∧ seed.carrier ⊆ T.completed := by
  classical
  let : LinearOrder seed.carrier := WellOrderingRel.isWellOrder.linearOrder
  let : WellFoundedLT seed.carrier := ⟨WellOrderingRel.isWellOrder.wf⟩
  let length : Ordinal.{u} := Ordinal.type (fun a b : seed.carrier ↦ a < b)
  have hcard : length.card ≤ kappa := by
    dsimp only [length]
    rw [Ordinal.card_type]
    exact seed.blueprint.card_vertices
  let request : Ordinal.{u} → Option V := fun o ↦
    if h : o < length then some (Ordinal.enum (fun a b : seed.carrier ↦ a < b) ⟨o, h⟩).1
    else none
  let S := run advance seed length hcard request
  have hseed : ∀ o, o ≤ length → seed.Extends (S o) := by
    intro o ho
    simpa only [run_zero] using run_extends advance seed length hcard request o ho 0
      bot_le
  refine ⟨S length, hseed length le_rfl, ?_⟩
  intro x hx
  let v : seed.carrier := ⟨x, hx⟩
  let rank := Ordinal.typein (fun a b : seed.carrier ↦ a < b) v
  have hrank : rank < length := Ordinal.typein_lt_type _ v
  have hxS : x ∈ (S rank).carrier := (hseed rank hrank.le).vertices hx
  have hrequest : request rank = some x := by
    simp only [request, dif_pos hrank, rank, Ordinal.enum_typein, v]
  have hcompleted : x ∈ (S (rank + 1)).completed := by
    change x ∈ (run advance seed length hcard request (rank + 1)).completed
    rw [run_add_one, hrequest]
    exact requestedStep_completed advance _ x hxS
  exact (run_extends advance seed length hcard request length le_rfl (rank + 1)
    (add_one_le_iff.mpr hrank)).completed_mono hcompleted

#print axioms run_extends
#print axioms exists_completedBatch

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState
