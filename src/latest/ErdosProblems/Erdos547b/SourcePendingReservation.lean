/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSaturatedPacking

/-!
# Source-only look-ahead reservation of a pending chunk

Append a prefix of future branches to the small current tail, fixing its
entire future pending list before choosing the threshold orientation.
The reservation is saturated unless it exhausts all remaining branches.
Reserved source mass, not yet embedded host mass, pays for its bin.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingReservation

open Finset Erdos547b.ZhaoLemma65 Erdos547b.ZhaoSourceSaturatedPacking

variable {Item Bin : Type*}

structure PendingReservation (weight : Item → ℝ) (pending future : List Item)
    (cap slack : ℝ) where
  count : ℕ
  count_le : count ≤ future.length
  fits : mass weight (pending ++ future.take count) ≤ cap
  saturated_or_terminal : cap - slack < mass weight (pending ++ future.take count) ∨
    future.drop count = []

def PendingReservation.reserved {weight : Item → ℝ} {pending future : List Item}
    {cap slack : ℝ} (R : PendingReservation weight pending future cap slack) : List Item :=
  pending ++ future.take R.count

def PendingReservation.remaining {weight : Item → ℝ} {pending future : List Item}
    {cap slack : ℝ} (R : PendingReservation weight pending future cap slack) : List Item :=
  future.drop R.count

/-- Fix a whole pending list using only source masses. The old small tail
is retained intact; every nonterminal new reservation is saturated. -/
theorem exists_pendingReservation
    (weight : Item → ℝ) (pending future : List Item) (cap slack : ℝ)
    (hslack : 0 ≤ slack) (hcap : slack < cap)
    (hsmall : ∀ i ∈ pending ++ future, 0 ≤ weight i ∧ weight i ≤ slack)
    (hpending : mass weight pending ≤ cap - slack) :
    Nonempty (PendingReservation weight pending future cap slack) := by
  by_cases hfinish : mass weight (pending ++ future) ≤ cap
  · refine ⟨⟨future.length, le_rfl, ?_, Or.inr ?_⟩⟩
    · simpa only [List.take_length] using hfinish
    · exact List.drop_length
  have hweights0 : ∀ a ∈ (pending ++ future).map weight, 0 ≤ a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact (hsmall i hi).1
  have hweightsSmall : ∀ a ∈ (pending ++ future).map weight, a ≤ slack := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact (hsmall i hi).2
  obtain ⟨k, hkLow, hkHigh⟩ := exists_prefix_sum_gt_sub_le
    ((pending ++ future).map weight) hweights0 hweightsSmall
    (hslack.trans_lt hcap) (le_of_not_ge hfinish)
  have hlow : cap - slack < mass weight ((pending ++ future).take k) := by
    simpa only [mass, List.map_take] using hkLow
  have hhigh : mass weight ((pending ++ future).take k) ≤ cap := by
    simpa only [mass, List.map_take] using hkHigh
  have hbefore := crossing_extends_pending weight pending future k cap slack
    (fun i hi => (hsmall i hi).1) hpending hlow
  have hk : k ≤ (pending ++ future).length := by
    by_contra h
    have hfull : (pending ++ future).take k = pending ++ future :=
      List.take_of_length_le (by omega)
    rw [hfull] at hhigh
    exact hfinish hhigh
  have htake : (pending ++ future).take k = pending ++ future.take (k - pending.length) := by
    rw [List.take_append, List.take_of_length_le hbefore.le]
  refine ⟨⟨k - pending.length, ?_, ?_, Or.inl ?_⟩⟩
  · simp only [List.length_append] at hk
    omega
  · simpa only [htake] using hhigh
  · simpa only [htake] using hlow

theorem PendingReservation.flatten
    {weight : Item → ℝ} {pending future : List Item} {cap slack : ℝ}
    (R : PendingReservation weight pending future cap slack) :
    R.reserved ++ R.remaining = pending ++ future := by
  simp only [PendingReservation.reserved, PendingReservation.remaining,
    List.append_assoc, List.take_append_drop]

theorem PendingReservation.pending_prefix
    {weight : Item → ℝ} {pending future : List Item} {cap slack : ℝ}
    (R : PendingReservation weight pending future cap slack) : pending.IsPrefix R.reserved :=
  ⟨future.take R.count, rfl⟩

/-- Exact source-mass bookkeeping, including the future reserved branches
which have not yet been embedded. -/
theorem PendingReservation.mass_accounting
    {weight : Item → ℝ} {pending future : List Item} {cap slack : ℝ}
    (R : PendingReservation weight pending future cap slack) :
    mass weight R.reserved + mass weight R.remaining = mass weight pending + mass weight future := by
  have h := congrArg (mass weight) R.flatten
  simpa only [mass, List.map_append, List.sum_append] using h

/-- Whenever unreserved demand remains, charging this fresh reserved edge
preserves the saturated source-mass ledger. Terminal deficits are never
silently charged against a later allocation. -/
theorem PendingReservation.extend_ledger [DecidableEq Bin]
    {weight : Item → ℝ} {pending future : List Item} {slack : ℝ}
    (capacity : Bin → ℝ) (used : Finset Bin) (e : Bin) (he : e ∉ used) (consumed : ℝ)
    (hledger : (∑ f ∈ used, (capacity f - slack)) ≤ consumed)
    (R : PendingReservation weight pending future (capacity e) slack)
    (hremaining : R.remaining ≠ []) :
    (∑ f ∈ insert e used, (capacity f - slack)) ≤ consumed + mass weight R.reserved := by
  have hsat : capacity e - slack < mass weight R.reserved := by
    rcases R.saturated_or_terminal with hs | ht
    · exact hs
    · exact (hremaining ht).elim
  rw [Finset.sum_insert he]
  linarith only [hledger, hsat]

end Erdos547b.ZhaoSourcePendingReservation

#print axioms Erdos547b.ZhaoSourcePendingReservation.exists_pendingReservation
#print axioms Erdos547b.ZhaoSourcePendingReservation.PendingReservation.mass_accounting
#print axioms Erdos547b.ZhaoSourcePendingReservation.PendingReservation.extend_ledger
