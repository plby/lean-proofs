/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingInterval

/-!
# Owner intervals in the literal pending branch order

A nondecreasing owner function gives genuine consecutive branch intervals.
Their boundaries count branches of earlier owners, including empty owner
fibers. Updating one root map value and extending that owner's interval
therefore preserves all earlier component copies.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingOwnerInterval

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoSourcePendingInterval

theorem initialSegment_eq_branchPrefix_card {b : ℕ} (s : Finset (Fin b))
    (hdown : ∀ i ∈ s, ∀ j, j ≤ i → j ∈ s) : s = branchPrefix s.card := by
  ext i
  rw [mem_branchPrefix]
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ s := fun j hj => hdown i hi j (Finset.mem_Iic.mp hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hn
    have hsub : s ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra h
      exact hn (hdown j hj i (le_of_not_gt h))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

def ownerCutoff {b r : ℕ} (owner : Fin b → Fin r) (n : ℕ) : ℕ :=
  (ownerPrefix Finset.univ owner n).card

theorem branchPrefix_ownerCutoff {b r : ℕ} (owner : Fin b → Fin r)
    (hmono : Monotone owner) (n : ℕ) :
    branchPrefix (ownerCutoff owner n) = ownerPrefix Finset.univ owner n := by
  symm
  apply initialSegment_eq_branchPrefix_card
  intro i hi j hji
  simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_le_of_lt (hmono hji) hi

theorem lt_ownerCutoff_iff {b r : ℕ} (owner : Fin b → Fin r)
    (hmono : Monotone owner) (i : Fin b) (n : ℕ) :
    i.val < ownerCutoff owner n ↔ (owner i).val < n := by
  rw [← mem_branchPrefix, branchPrefix_ownerCutoff owner hmono]
  simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ownerCutoff_mono {b r : ℕ} (owner : Fin b → Fin r) : Monotone (ownerCutoff owner) := by
  intro m n hmn
  apply Finset.card_le_card
  intro i hi
  simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem ownerCutoff_le {b r : ℕ} (owner : Fin b → Fin r) (n : ℕ) :
    ownerCutoff owner n ≤ b := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

@[simp] theorem ownerCutoff_zero {b r : ℕ} (owner : Fin b → Fin r) :
    ownerCutoff owner 0 = 0 := by
  simp [ownerCutoff]

@[simp] theorem ownerCutoff_full {b r : ℕ} (owner : Fin b → Fin r) :
    ownerCutoff owner r = b := by
  simp [ownerCutoff]

theorem owner_eq_of_mem_interval {b r : ℕ} (owner : Fin b → Fin r)
    (hmono : Monotone owner) (n : Fin r) (i : Fin b)
    (hlo : ownerCutoff owner n.val ≤ i.val)
    (hhi : i.val < ownerCutoff owner (n.val + 1)) : owner i = n := by
  have hu := (lt_ownerCutoff_iff owner hmono i (n.val + 1)).mp hhi
  have hl : ¬(owner i).val < n.val := by
    intro h
    have := (lt_ownerCutoff_iff owner hmono i n.val).mpr h
    omega
  exact Fin.ext (by omega)

variable {b r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V)
variable (owner : Fin b → Fin r) (hmono : Monotone owner)
variable (orient : Fin b → Fin 2 ≃ Fin 2) (available : Fin 2 → Finset V)

include hmono in
/-- Update one chosen outer root, then extend exactly its consecutive
branch interval. No parent value of any later owner is constrained. -/
theorem exists_owner_extension
    (n : Fin r) (rootImage : Fin r → V)
    (E : PartialDynamicAttachedForestEmbedding F H (fun i => rootImage (owner i)) orient available
      (branchPrefix (ownerCutoff owner n.val)))
    (z : V) (hstep : BranchStepAccess F H orient available z) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F H
        (fun i => Function.update rootImage n z (owner i)) orient available
        (branchPrefix (ownerCutoff owner (n.val + 1))),
      ∀ j hj, E'.forestCopy.componentCopy j
          (branchPrefix_mono (ownerCutoff_mono owner (Nat.le_succ n.val)) hj) =
        E.forestCopy.componentCopy j hj := by
  let parent' := fun i => Function.update rootImage n z (owner i)
  have hagrees : ∀ i ∈ branchPrefix (ownerCutoff owner n.val), parent' i = rootImage (owner i) := by
    intro i hi
    have hlt : (owner i).val < n.val :=
      (lt_ownerCutoff_iff owner hmono i n.val).mp ((mem_branchPrefix i).mp hi)
    have hne : owner i ≠ n := fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h)
    exact Function.update_of_ne hne z rootImage
  let old := partialReparent F H (fun i => rootImage (owner i)) parent' orient available
    (branchPrefix (ownerCutoff owner n.val)) E hagrees
  have hparent : ∀ i : Fin b, ownerCutoff owner n.val ≤ i.val →
      i.val < ownerCutoff owner (n.val + 1) → parent' i = z := by
    intro i hlo hhi
    dsimp only [parent']
    rw [owner_eq_of_mem_interval owner hmono n i hlo hhi, Function.update_self]
  obtain ⟨out, hout⟩ := exists_interval_extension F H parent' orient available z hstep
    (ownerCutoff owner n.val) (ownerCutoff owner (n.val + 1))
    (ownerCutoff_mono owner (Nat.le_succ n.val)) (ownerCutoff_le owner _) old hparent
  exact ⟨out, hout⟩

end Erdos547b.ZhaoSourcePendingOwnerInterval

#print axioms Erdos547b.ZhaoSourcePendingOwnerInterval.initialSegment_eq_branchPrefix_card
#print axioms Erdos547b.ZhaoSourcePendingOwnerInterval.owner_eq_of_mem_interval
#print axioms Erdos547b.ZhaoSourcePendingOwnerInterval.exists_owner_extension
