import Mathlib

/-!
# Exact counting for uniform random subsets

This file develops the finite counting language used in the proof of Erdős
Problem 622.  A uniformly random subset of a finite set `U` is represented by
an element of `U.powerset`; all probabilities are quotients of cardinalities.

The main calculation is `binomialDifference_count`.  Complementing every
coordinate in the second block is an involution, and changes
`X.card + (V.card - Y.card)` into `X.card + Y.card`.  Thus the former statistic
has exactly the binomial counting law on `U.card + V.card` coordinates.
-/

open scoped BigOperators

namespace Erdos622.Counting

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Number of subsets of `U` satisfying `P`. -/
def countEvent {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) [DecidablePred P] : ℕ :=
  (U.powerset.filter P).card

/-- Probability of an event in the uniform powerset of `U`. -/
def probEvent {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) [DecidablePred P] : ℝ :=
  countEvent U P / (2 : ℝ) ^ U.card

@[simp]
theorem countEvent_true {α : Type*} [DecidableEq α] (U : Finset α) :
    countEvent U (fun _ ↦ True) = 2 ^ U.card := by
  classical
  simp [countEvent]

@[simp]
theorem countEvent_false {α : Type*} [DecidableEq α] (U : Finset α) :
    countEvent U (fun _ ↦ False) = 0 := by
  classical
  simp [countEvent]

theorem countEvent_le_total {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) :
    countEvent U P ≤ 2 ^ U.card := by
  classical
  simpa [countEvent] using Finset.card_filter_le U.powerset P

theorem countEvent_mono {α : Type*} [DecidableEq α]
    {U : Finset α} {P Q : Finset α → Prop}
    (hPQ : ∀ S, S ⊆ U → P S → Q S) :
    countEvent U P ≤ countEvent U Q := by
  classical
  unfold countEvent
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨hS.1, hPQ S hS.1 hS.2⟩

theorem countEvent_or_le {α : Type*} [DecidableEq α]
    (U : Finset α) (P Q : Finset α → Prop) :
    countEvent U (fun S ↦ P S ∨ Q S) ≤ countEvent U P + countEvent U Q := by
  classical
  unfold countEvent
  calc
    (U.powerset.filter (fun S ↦ P S ∨ Q S)).card =
        (U.powerset.filter P ∪ U.powerset.filter Q).card := by
      congr 1
      ext S
      simp [and_or_left]
    _ ≤ (U.powerset.filter P).card + (U.powerset.filter Q).card :=
      Finset.card_union_le _ _

theorem countEvent_add_compl {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) :
    countEvent U P + countEvent U (fun S ↦ ¬ P S) = 2 ^ U.card := by
  classical
  unfold countEvent
  calc
    (U.powerset.filter P).card + (U.powerset.filter fun S ↦ ¬ P S).card =
        (U.powerset.filter P).card +
          (U.powerset.filter fun S ↦ ¬ P S).card := rfl
    _ = U.powerset.card := Finset.card_filter_add_card_filter_not P
    _ = 2 ^ U.card := Finset.card_powerset U

@[simp]
theorem probEvent_true {α : Type*} [DecidableEq α] (U : Finset α) :
    probEvent U (fun _ ↦ True) = 1 := by
  simp [probEvent]

theorem probEvent_nonneg {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) :
    0 ≤ probEvent U P := by
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem probEvent_le_one {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) :
    probEvent U P ≤ 1 := by
  rw [probEvent, div_le_one]
  · exact_mod_cast countEvent_le_total U P
  · positivity

theorem probEvent_mono {α : Type*} [DecidableEq α]
    {U : Finset α} {P Q : Finset α → Prop}
    (hPQ : ∀ S, S ⊆ U → P S → Q S) :
    probEvent U P ≤ probEvent U Q := by
  unfold probEvent
  gcongr
  exact_mod_cast countEvent_mono hPQ

theorem probEvent_or_le {α : Type*} [DecidableEq α]
    (U : Finset α) (P Q : Finset α → Prop) :
    probEvent U (fun S ↦ P S ∨ Q S) ≤ probEvent U P + probEvent U Q := by
  unfold probEvent
  rw [← add_div]
  gcongr
  exact_mod_cast countEvent_or_le U P Q

/-- Count pairs of subsets from two coordinate blocks satisfying `P`. -/
def pairCount {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (P : Finset α → Finset β → Prop)
    [DecidablePred (Function.uncurry P)] : ℕ :=
  ((U.powerset.product V.powerset).filter (Function.uncurry P)).card

@[simp]
theorem pairCount_true {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) :
    pairCount U V (fun _ _ ↦ True) = 2 ^ (U.card + V.card) := by
  classical
  unfold pairCount
  change ((U.powerset.product V.powerset).filter
    (fun _ : Finset α × Finset β ↦ True)).card = 2 ^ (U.card + V.card)
  simp [pow_add]

/-- Events supported on the two different blocks factor exactly.  Dividing
both sides by `2 ^ (U.card + V.card)` is the usual independence statement. -/
theorem pairCount_and_eq_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β)
    (P : Finset α → Prop) (Q : Finset β → Prop) :
    pairCount U V (fun X Y ↦ P X ∧ Q Y) =
      countEvent U P * countEvent V Q := by
  classical
  unfold pairCount countEvent
  calc
    ((U.powerset.product V.powerset).filter
        (fun p ↦ P p.1 ∧ Q p.2)).card =
        ((U.powerset.filter P).product (V.powerset.filter Q)).card := by
      congr 1
      ext p
      simp [and_assoc, and_left_comm, and_comm]
    _ = (U.powerset.filter P).card * (V.powerset.filter Q).card :=
      Finset.card_product _ _

/-- The exact binomial count of a predicate of subset cardinality. -/
def binomialCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  countEvent (Finset.univ : Finset (Fin N)) (fun S ↦ P S.card)

theorem binomialCount_eq_sum (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    binomialCount N P =
      ∑ k ∈ Finset.range (N + 1), if P k then N.choose k else 0 := by
  rw [binomialCount, countEvent, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h := Finset.sum_powerset_apply_card
    (x := (Finset.univ : Finset (Fin N))) (fun k ↦ if P k then (1 : ℕ) else 0)
  simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero, Nat.cast_id] using h

/-- Cardinality classes in a powerset are the binomial coefficients. -/
theorem countEvent_card_eq_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (P : ℕ → Prop) [DecidablePred P] :
    countEvent U (fun S ↦ P S.card) =
      ∑ k ∈ Finset.range (U.card + 1), if P k then U.card.choose k else 0 := by
  rw [countEvent, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h := Finset.sum_powerset_apply_card
    (x := U) (fun k ↦ if P k then (1 : ℕ) else 0)
  simpa only [nsmul_eq_mul, mul_ite, mul_one, mul_zero, Nat.cast_id] using h

/-- On two complete finite coordinate types, adding the two selected
cardinalities has the binomial counting law for the sum of the type sizes. -/
theorem pairCount_univ_card_add_eq_binomialCount
    (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : ℕ → Prop) :
    pairCount (Finset.univ : Finset α) (Finset.univ : Finset β)
        (fun X Y ↦ P (X.card + Y.card)) =
      binomialCount (Fintype.card α + Fintype.card β) P := by
  classical
  have hsplit :
      pairCount (Finset.univ : Finset α) (Finset.univ : Finset β)
          (fun X Y ↦ P (X.card + Y.card)) =
        countEvent (Finset.univ : Finset (α ⊕ β)) (fun S ↦ P S.card) := by
    rw [pairCount, countEvent]
    refine Finset.card_equiv Finset.sumEquiv.toEquiv.symm ?_
    intro p
    simp [Finset.sumEquiv_symm_apply, Finset.card_disjSum, Function.uncurry]
  rw [hsplit]
  calc
    countEvent (Finset.univ : Finset (α ⊕ β)) (fun S ↦ P S.card) =
        ∑ k ∈ Finset.range (Fintype.card (α ⊕ β) + 1),
          if P k then (Fintype.card (α ⊕ β)).choose k else 0 :=
      countEvent_card_eq_sum _ P
    _ = ∑ k ∈ Finset.range (Fintype.card α + Fintype.card β + 1),
          if P k then (Fintype.card α + Fintype.card β).choose k else 0 := by simp
    _ = binomialCount (Fintype.card α + Fintype.card β) P :=
      (binomialCount_eq_sum _ P).symm

/-- Complementing the second block is the finite, exact form of the identity
`X + s - Y ∼ B(r+s, 1/2)` for independent half-binomial variables. -/
theorem complementSecond_count
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (P : ℕ → Prop) :
    pairCount U V (fun X Y ↦ P (X.card + (V.card - Y.card))) =
      pairCount U V (fun X Y ↦ P (X.card + Y.card)) := by
  classical
  unfold pairCount
  refine Finset.card_bij' (fun p _ ↦ (p.1, V \ p.2))
      (fun p _ ↦ (p.1, V \ p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpP⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpU, hpV⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hpU, Finset.mem_powerset.mpr Finset.sdiff_subset⟩, ?_⟩
    change P (p.1.card + (V \ p.2).card)
    change P (p.1.card + (V.card - p.2.card)) at hpP
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hpV)]
    convert hpP using 1
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpP⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpU, hpV⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hpU, Finset.mem_powerset.mpr Finset.sdiff_subset⟩, ?_⟩
    change P (p.1.card + (V.card - (V \ p.2).card))
    change P (p.1.card + p.2.card) at hpP
    have hcard : p.2.card ≤ V.card :=
      Finset.card_mono (Finset.mem_powerset.mp hpV)
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hpV)]
    convert hpP using 1
    omega
  · intro p hp
    apply Prod.ext
    · rfl
    · apply Finset.sdiff_sdiff_eq_self
      exact Finset.mem_powerset.mp
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    apply Prod.ext
    · rfl
    · apply Finset.sdiff_sdiff_eq_self
      exact Finset.mem_powerset.mp
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2

/-- Lemma 3.12 in counting form: the complemented difference statistic has
the binomial law on the combined block. -/
theorem binomialDifference_count
    (r s : ℕ) (P : ℕ → Prop) :
    pairCount (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin s))
        (fun X Y ↦ P (X.card + (s - Y.card))) =
      binomialCount (r + s) P := by
  classical
  calc
    pairCount (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin s))
          (fun X Y ↦ P (X.card + (s - Y.card))) =
        pairCount (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin s))
          (fun X Y ↦ P (X.card + Y.card)) := by
      simpa using complementSecond_count
        (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin s)) P
    _ = binomialCount (r + s) P := by
      simpa using pairCount_univ_card_add_eq_binomialCount (Fin r) (Fin s) P

end

end Erdos622.Counting
