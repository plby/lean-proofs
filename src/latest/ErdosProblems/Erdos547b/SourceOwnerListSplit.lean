/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSortedBranchOrder

/-!
# Current-owner splitting of an unreserved source list

An owner-sorted list with no earlier owners splits into exactly the current
owner followed by strictly later owners. A current tail followed by later
owners has an exact literal owner cutoff, needed by active reservations.
-/

open scoped Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOwnerListSplit

open Finset Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoLemma58DynamicBatchAppend

structure OwnerSplit {b r : ℕ} (owner : Fin b → Fin r) (n : Fin r) (items : List (Fin b)) where
  current : List (Fin b)
  future : List (Fin b)
  flatten : current ++ future = items
  current_owner : ∀ i ∈ current, owner i = n
  future_after : ∀ i ∈ future, n.val < (owner i).val

theorem exists_ownerSplit {b r : ℕ} (owner : Fin b → Fin r) (n : Fin r) (items : List (Fin b))
    (horder : items.Pairwise (fun i j => owner i ≤ owner j))
    (hafter : ∀ i ∈ items, n.val ≤ (owner i).val) : Nonempty (OwnerSplit owner n items) := by
  induction items with
  | nil => exact ⟨⟨[], [], rfl, by simp, by simp⟩⟩
  | cons i items ih =>
      obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp horder
      by_cases hi : owner i = n
      · obtain ⟨R⟩ := ih htail (fun j hj => hafter j (List.mem_cons_of_mem i hj))
        refine ⟨{
          current := i :: R.current
          future := R.future
          flatten := by simp only [List.cons_append, R.flatten]
          current_owner := ?_
          future_after := R.future_after }⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact R.current_owner j hj
      · have hil : n.val < (owner i).val := by
          have hle := hafter i List.mem_cons_self
          have hne : (owner i).val ≠ n.val := fun h => hi (Fin.ext h)
          omega
        refine ⟨⟨[], i :: items, rfl, by simp, ?_⟩⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hil
        · exact hil.trans_le (hfirst j hj)

theorem OwnerSplit.current_sublist {b r : ℕ} {owner : Fin b → Fin r} {n : Fin r}
    {items : List (Fin b)} (R : OwnerSplit owner n items) : R.current.Sublist items :=
  (congrArg (fun l : List (Fin b) => R.current.Sublist l) R.flatten).mp
    (List.sublist_append_left R.current R.future)

theorem OwnerSplit.future_sublist {b r : ℕ} {owner : Fin b → Fin r} {n : Fin r}
    {items : List (Fin b)} (R : OwnerSplit owner n items) : R.future.Sublist items :=
  (congrArg (fun l : List (Fin b) => R.future.Sublist l) R.flatten).mp
    (List.sublist_append_right R.current R.future)

theorem OwnerSplit.current_nonempty {b r : ℕ} {owner : Fin b → Fin r} {n : Fin r}
    {items : List (Fin b)} (R : OwnerSplit owner n items)
    (hcurrent : ∃ i ∈ items, owner i = n) : R.current ≠ [] := by
  intro hnil
  obtain ⟨i, hi, hoi⟩ := hcurrent
  have hm : i ∈ R.current ++ R.future := R.flatten.symm ▸ hi
  rw [hnil, List.nil_append] at hm
  have h := R.future_after i hm
  rw [hoi] at h
  exact (lt_irrefl _ h)

theorem OwnerSplit.mass_split {b r : ℕ} {owner : Fin b → Fin r} {n : Fin r}
    {items : List (Fin b)} (R : OwnerSplit owner n items) (weight : Fin b → ℝ) :
    mass weight R.current + mass weight R.future = mass weight items := by
  have h := congrArg (mass weight) R.flatten
  simpa only [mass, List.map_append, List.sum_append] using h

theorem card_branchPrefix {b n : ℕ} (hn : n ≤ b) :
    (branchPrefix n : Finset (Fin b)).card = n := by
  by_cases heq : n = b
  · subst n
    simp
  · have hlt : n < b := by omega
    rw [branchPrefix_eq_Iio (⟨n, hlt⟩ : Fin b), Fin.card_Iio]

/-- The current-tail prefix is exactly the owner's global-stage prefix,
even when a look-ahead reservation includes many later owners. -/
theorem ownerCutoff_current_append {b r : ℕ} (owner : Fin b → Fin r) (n : Fin r)
    (current future : List (Fin b))
    (hcurrent : ∀ i ∈ current, owner i = n)
    (hfuture : ∀ i ∈ future, n.val < (owner i).val) :
    ownerCutoff (listOwner owner (current ++ future)) (n.val + 1) = current.length := by
  have hset : ownerPrefix Finset.univ (listOwner owner (current ++ future)) (n.val + 1) =
      branchPrefix current.length := by
    ext i
    simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and, mem_branchPrefix]
    change (owner (current ++ future)[i.val]).val < n.val + 1 ↔ i.val < current.length
    by_cases hi : i.val < current.length
    · rw [List.getElem_append_left hi, hcurrent _ (List.getElem_mem hi)]
      omega
    · have hidx : i.val - current.length < future.length := by
        have hh := i.isLt
        simp only [List.length_append] at hh
        omega
      rw [List.getElem_append_right (by omega : current.length ≤ i.val)]
      have ho := hfuture _ (List.getElem_mem hidx)
      omega
  unfold ownerCutoff
  rw [hset]
  apply card_branchPrefix
  simp only [List.length_append]
  omega

end Erdos547b.ZhaoSourceOwnerListSplit

#print axioms Erdos547b.ZhaoSourceOwnerListSplit.exists_ownerSplit
#print axioms Erdos547b.ZhaoSourceOwnerListSplit.OwnerSplit.mass_split
#print axioms Erdos547b.ZhaoSourceOwnerListSplit.ownerCutoff_current_append
