import Wikipedia.NoExoticSixSphere.ClosedTimeWindowCharts
import Mathlib.Data.Finite.Card

/-!
# Exact decomposition of the boundary of a closed time window

When the old boundary lies strictly between the cut times, it is disjoint
from both endpoint fibers. The actual boundary subtype is equivalent to
their disjoint sum. Its finite cardinality is therefore the sum of the
three actual cardinalities.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.ClosedTimeWindow

variable {X : Type*} [TopologicalSpace X] (τ : C(X, ℝ)) (B : Set X)
  (hB : ∀ x ∈ B, τ x ∈ Ioo (0 : ℝ) 1)

def partsToBoundary : (B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1}) → boundary τ B
  | .inl x => ⟨⟨x.val, Ioo_subset_Icc_self (hB x.val x.property)⟩, .inl x.property⟩
  | .inr (.inl x) => ⟨⟨x.val, by rw [space, mem_preimage, x.property]; norm_num⟩,
      .inr (.inl x.property)⟩
  | .inr (.inr x) => ⟨⟨x.val, by rw [space, mem_preimage, x.property]; norm_num⟩,
      .inr (.inr x.property)⟩

theorem partsToBoundary_injective : Injective (partsToBoundary τ B hB) := by
  intro a b h
  have he := congrArg (fun q : boundary τ B ↦ q.val.val) h
  rcases a with a | a | a <;> rcases b with b | b | b
  · exact congrArg Sum.inl (Subtype.ext he)
  · have hb : τ a.val = 0 := (congrArg τ he).trans b.property
    exact ((ne_of_gt (hB a.val a.property).1) hb).elim
  · have hb : τ a.val = 1 := (congrArg τ he).trans b.property
    exact ((ne_of_lt (hB a.val a.property).2) hb).elim
  · have ha : τ b.val = 0 := (congrArg τ he).symm.trans a.property
    exact ((ne_of_gt (hB b.val b.property).1) ha).elim
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext he)
  · have hab : (0 : ℝ) = 1 := a.property.symm.trans ((congrArg τ he).trans b.property)
    exact (zero_ne_one hab).elim
  · have ha : τ b.val = 1 := (congrArg τ he).symm.trans a.property
    exact ((ne_of_lt (hB b.val b.property).2) ha).elim
  · have hab : (1 : ℝ) = 0 := a.property.symm.trans ((congrArg τ he).trans b.property)
    exact (one_ne_zero hab).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext he)

theorem partsToBoundary_surjective : Surjective (partsToBoundary τ B hB) := by
  intro q
  rcases q.property with hb | hzero | hone
  · exact ⟨.inl ⟨q.val.val, hb⟩, rfl⟩
  · exact ⟨.inr (.inl ⟨q.val.val, hzero⟩), rfl⟩
  · exact ⟨.inr (.inr ⟨q.val.val, hone⟩), rfl⟩

def boundaryPartsEquiv : (B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1}) ≃ boundary τ B :=
  Equiv.ofBijective (partsToBoundary τ B hB)
    ⟨partsToBoundary_injective τ B hB, partsToBoundary_surjective τ B hB⟩

include hB in
theorem boundary_ncard (hfin : (boundary τ B).Finite) :
    (boundary τ B).ncard = Nat.card B +
      (Nat.card {x // τ x = 0} + Nat.card {x // τ x = 1}) := by
  let := hfin.to_subtype
  let E := boundaryPartsEquiv τ B hB
  let : Finite (B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1}) := Finite.of_equiv _ E.symm
  let : Finite B := Finite.of_injective
    (Sum.inl : B → B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1}) Sum.inl_injective
  let : Finite {x // τ x = 0} := Finite.of_injective
    (Sum.inr ∘ Sum.inl : {x // τ x = 0} → B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1})
    (Sum.inr_injective.comp Sum.inl_injective)
  let : Finite {x // τ x = 1} := Finite.of_injective
    (Sum.inr ∘ Sum.inr : {x // τ x = 1} → B ⊕ {x // τ x = 0} ⊕ {x // τ x = 1})
    (Sum.inr_injective.comp Sum.inr_injective)
  exact (Nat.card_congr E).symm.trans (by rw [Nat.card_sum, Nat.card_sum])

end NoExoticSixSphere.ClosedTimeWindow
