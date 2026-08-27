/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FamilyTwoAwayWeight
import ErdosProblems.Erdos207.GreedyDeletionObstruction

/-!
# A deterministic deletion envelope for the greedy process

Pair collisions delete at most `3|V|` triangles.  Once the two-away threat
count is bounded by `K`, a legal greedy step therefore deletes at most
`3|V|+K` available triangles.  This gives the pathwise availability lower
envelope used to sum the one-point hazards.
-/

namespace Erdos207

open Finset

noncomputable section

@[simp]
lemma greedyAvailableIn_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) :
    greedyAvailableIn (univ : TripleSystemOn V) S = S.available := by
  ext T
  simp [greedyAvailableIn]

/-- A state has a uniform two-away deletion cutoff. -/
def HasTwoAwayCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (S : GreedyStateOn V) : Prop :=
  ∀ U ∈ S.available,
    (twoAwayForbiddenTriangles F S.chosen U).card ≤ K

/-- Under the cutoff, every legal choice deletes at most `3|V|+K`
currently available triangles. -/
theorem card_greedyDeleted_available_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) (hcut : HasTwoAwayCutoff F K S)
    {U : TripleOn V} (hU : U ∈ S.available) :
    (greedyDeletedIn F (univ : TripleSystemOn V) S U).card ≤
      3 * Fintype.card V + K := by
  calc
    (greedyDeletedIn F (univ : TripleSystemOn V) S U).card ≤
        (triplesSharingPair U).card +
          (twoAwayForbiddenTriangles F S.chosen U).card :=
      card_greedyDeletedIn_le_pairSharing_add_twoAway hInv hU
    _ ≤ 3 * Fintype.card V + K :=
      Nat.add_le_add (card_triplesSharingPair_le V U) (hcut U hU)

/-- One legal step cannot decrease total availability by more than the
deletion envelope. -/
theorem greedyStep_available_card_le_add_envelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) (hcut : HasTwoAwayCutoff F K S)
    {U : TripleOn V} (hU : U ∈ S.available) :
    S.available.card ≤
      (greedyStep F S U).available.card + (3 * Fintype.card V + K) := by
  have hpartition := greedyDeletedIn_card_add_step_card
    F (univ : TripleSystemOn V) S U
  rw [greedyAvailableIn_univ, greedyAvailableIn_univ] at hpartition
  have hdeleted := card_greedyDeleted_available_le hInv hcut hU
  omega

/-- After `t` consecutive good steps, the total availability has lost at
most `t(3|V|+K)`.  The statement is phrased for an arbitrary state sequence
so it can be reused by both deterministic and probabilistic path encodings. -/
theorem availability_card_le_add_mul_envelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ}
    (path : ℕ → GreedyStateOn V)
    (hstep : ∀ t, GreedyInvariant F (path t) →
      HasTwoAwayCutoff F K (path t) →
      (path t).available.Nonempty →
      ∃ U ∈ (path t).available, path (t + 1) = greedyStep F (path t) U)
    (hInv : ∀ t, GreedyInvariant F (path t))
    (hcut : ∀ t, HasTwoAwayCutoff F K (path t))
    (hne : ∀ t, (path t).available.Nonempty) :
    ∀ t, (path 0).available.card ≤
      (path t).available.card + t * (3 * Fintype.card V + K) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      obtain ⟨U, hU, hnext⟩ := hstep t (hInv t) (hcut t) (hne t)
      have hlocal := greedyStep_available_card_le_add_envelope
        (hInv t) (hcut t) hU
      rw [← hnext] at hlocal
      calc
        (path 0).available.card ≤
            (path t).available.card + t * (3 * Fintype.card V + K) := ih
        _ ≤ ((path (t + 1)).available.card +
              (3 * Fintype.card V + K)) +
            t * (3 * Fintype.card V + K) := by omega
        _ = (path (t + 1)).available.card +
            (t + 1) * (3 * Fintype.card V + K) := by ring

end

end Erdos207
