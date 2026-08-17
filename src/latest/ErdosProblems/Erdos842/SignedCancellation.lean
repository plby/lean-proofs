import ErdosProblems.Erdos842.Parity

/-!
# Finite sign-reversing cancellation

Abstract finite-sum lemmas used by the Petrov/Fleischner--Stiebitz parity
argument.  The statements deliberately separate cancellation from the
description of the surviving fibres, so the same infrastructure can be used
both for triangle-factor cancellation and for chord-selection fibres.
-/

open scoped BigOperators

namespace Erdos842.SignedCancellation

/-- A fixed-point-free, sign-reversing involution on a finite set cancels its
integer-weighted sum. -/
theorem sum_eq_zero_of_involution {α : Type*} (s : Finset α) (weight : α → ℤ)
    (ι : α → α)
    (map_mem : ∀ x ∈ s, ι x ∈ s)
    (involutive : ∀ x ∈ s, ι (ι x) = x)
    (fixedPointFree : ∀ x ∈ s, ι x ≠ x)
    (negates : ∀ x ∈ s, weight (ι x) = -weight x) :
    ∑ x ∈ s, weight x = 0 := by
  classical
  apply Finset.sum_involution (fun x _ ↦ ι x)
  · intro x hx
    rw [negates x hx]
    exact add_neg_cancel _
  · intro x hx _
    exact fixedPointFree x hx
  · exact map_mem
  · exact involutive

/-- If a sign-reversing involution pairs all elements outside a chosen
survivor set, the original sum is exactly the sum over the survivors. -/
theorem sum_eq_sum_survivors {α : Type*} [DecidableEq α]
    (s survivors : Finset α) (weight : α → ℤ)
    (ι : α → α) (survivors_subset : survivors ⊆ s)
    (map_mem : ∀ x ∈ s \ survivors, ι x ∈ s \ survivors)
    (involutive : ∀ x ∈ s \ survivors, ι (ι x) = x)
    (fixedPointFree : ∀ x ∈ s \ survivors, ι x ≠ x)
    (negates : ∀ x ∈ s \ survivors, weight (ι x) = -weight x) :
    ∑ x ∈ s, weight x = ∑ x ∈ survivors, weight x := by
  classical
  have hcancel : ∑ x ∈ s \ survivors, weight x = 0 :=
    sum_eq_zero_of_involution (s \ survivors) weight ι map_mem involutive fixedPointFree negates
  rw [← Finset.sum_sdiff survivors_subset, hcancel, zero_add]

/-- Reindex a survivor sum by a finite collection of fibres. -/
theorem sum_eq_sum_fibers {α β : Type*} [DecidableEq β]
    (survivors : Finset α) (good : Finset β) (key : α → β) (weight : α → ℤ)
    (mapsTo : ∀ x ∈ survivors, key x ∈ good) :
    (∑ x ∈ survivors, weight x) =
      ∑ g ∈ good, ∑ x ∈ survivors with key x = g, weight x := by
  simpa only using (Finset.sum_fiberwise_of_maps_to mapsTo weight).symm

/-- Two same-sign unit-weight survivors in every fibre give a contribution
of `2` or `-2` from that fibre. -/
theorem fiber_sum_eq_two_or_neg_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (survivors : Finset α) (key : α → β) (weight : α → ℤ) (g : β)
    (two : (survivors.filter fun x ↦ key x = g).card = 2)
    (sameUnitSign :
      (∀ x ∈ survivors, key x = g → weight x = 1) ∨
        (∀ x ∈ survivors, key x = g → weight x = -1)) :
    (∑ x ∈ survivors with key x = g, weight x) = 2 ∨
      (∑ x ∈ survivors with key x = g, weight x) = -2 := by
  rcases sameUnitSign with hpos | hneg
  · left
    calc
      (∑ x ∈ survivors with key x = g, weight x) =
          ∑ _x ∈ survivors.filter (fun x ↦ key x = g), (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpos x (Finset.filter_subset _ _ hx) (Finset.mem_filter.mp hx).2
      _ = 2 := by simp [two]
  · right
    calc
      (∑ x ∈ survivors with key x = g, weight x) =
          ∑ _x ∈ survivors.filter (fun x ↦ key x = g), (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hneg x (Finset.filter_subset _ _ hx) (Finset.mem_filter.mp hx).2
      _ = -2 := by simp [two]

/-- If an odd finite set of good indices parametrizes two equal-sign unit
survivors per fibre, their total sum is `2` modulo `4`. -/
theorem survivor_sum_modEq_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (survivors : Finset α) (good : Finset β) (key : α → β) (weight : α → ℤ)
    (mapsTo : ∀ x ∈ survivors, key x ∈ good)
    (two : ∀ g ∈ good, (survivors.filter fun x ↦ key x = g).card = 2)
    (sameUnitSign : ∀ g ∈ good,
      (∀ x ∈ survivors, key x = g → weight x = 1) ∨
        (∀ x ∈ survivors, key x = g → weight x = -1))
    (odd_good : Odd good.card) :
    (∑ x ∈ survivors, weight x) ≡ 2 [ZMOD 4] := by
  rw [sum_eq_sum_fibers survivors good key weight mapsTo]
  exact Erdos842.Parity.signed_two_sum_modEq_two good
    (fun g ↦ ∑ x ∈ survivors with key x = g, weight x)
    (fun g hg ↦ fiber_sum_eq_two_or_neg_two survivors key weight g
      (two g hg) (sameUnitSign g hg)) odd_good

/-- Combined cancellation-and-fibre theorem in the form needed by the
constant-term proof. -/
theorem sum_modEq_two_of_involution_and_survivor_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s survivors : Finset α) (good : Finset β) (key : α → β) (weight : α → ℤ)
    (ι : α → α) (survivors_subset : survivors ⊆ s)
    (map_mem : ∀ x ∈ s \ survivors, ι x ∈ s \ survivors)
    (involutive : ∀ x ∈ s \ survivors, ι (ι x) = x)
    (fixedPointFree : ∀ x ∈ s \ survivors, ι x ≠ x)
    (negates : ∀ x ∈ s \ survivors, weight (ι x) = -weight x)
    (mapsTo : ∀ x ∈ survivors, key x ∈ good)
    (two : ∀ g ∈ good, (survivors.filter fun x ↦ key x = g).card = 2)
    (sameUnitSign : ∀ g ∈ good,
      (∀ x ∈ survivors, key x = g → weight x = 1) ∨
        (∀ x ∈ survivors, key x = g → weight x = -1))
    (odd_good : Odd good.card) :
    (∑ x ∈ s, weight x) ≡ 2 [ZMOD 4] := by
  rw [sum_eq_sum_survivors s survivors weight ι survivors_subset map_mem involutive
    fixedPointFree negates]
  exact survivor_sum_modEq_two survivors good key weight mapsTo two sameUnitSign odd_good

/-- The combined hypotheses also imply that the full signed sum is nonzero. -/
theorem sum_ne_zero_of_involution_and_survivor_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s survivors : Finset α) (good : Finset β) (key : α → β) (weight : α → ℤ)
    (ι : α → α) (survivors_subset : survivors ⊆ s)
    (map_mem : ∀ x ∈ s \ survivors, ι x ∈ s \ survivors)
    (involutive : ∀ x ∈ s \ survivors, ι (ι x) = x)
    (fixedPointFree : ∀ x ∈ s \ survivors, ι x ≠ x)
    (negates : ∀ x ∈ s \ survivors, weight (ι x) = -weight x)
    (mapsTo : ∀ x ∈ survivors, key x ∈ good)
    (two : ∀ g ∈ good, (survivors.filter fun x ↦ key x = g).card = 2)
    (sameUnitSign : ∀ g ∈ good,
      (∀ x ∈ survivors, key x = g → weight x = 1) ∨
        (∀ x ∈ survivors, key x = g → weight x = -1))
    (odd_good : Odd good.card) :
    (∑ x ∈ s, weight x) ≠ 0 := by
  intro hz
  have hmod := sum_modEq_two_of_involution_and_survivor_fibers
    s survivors good key weight ι survivors_subset map_mem involutive fixedPointFree negates
      mapsTo two sameUnitSign odd_good
  rw [hz] at hmod
  norm_num at hmod

end Erdos842.SignedCancellation
