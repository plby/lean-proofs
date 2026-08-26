import Mathlib
import ErdosProblems.Erdos550.HPDirectInvariant
import ErdosProblems.Erdos550.HPMatchingState

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact load accounting on whole matching-edge families

Because the off--Turán split assigns complete matching edges, the sum of the
two side loads over a family is exactly the cardinality of the partial image
inside the union of that family.  Colour-assigned support then bounds this by
the corresponding source-side demand.
-/

open Finset

namespace Erdos550

open Classical

noncomputable def hpMatchingRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (left right : κ → Finset V) : Finset V :=
  K.biUnion fun k => left k ∪ right k

lemma left_subset_hpMatchingRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (left right : κ → Finset V)
    {k : κ} (hk : k ∈ K) :
    left k ⊆ hpMatchingRegion K left right := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_union_left _ hv⟩

lemma right_subset_hpMatchingRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (left right : κ → Finset V)
    {k : κ} (hk : k ∈ K) :
    right k ⊆ hpMatchingRegion K left right := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_union_right _ hv⟩

lemma disjoint_hpMatchingRegion_right
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (left right : κ → Finset V)
    (head : Finset V)
    (hdisj : ∀ k ∈ K, Disjoint head (left k ∪ right k)) :
    Disjoint head (hpMatchingRegion K left right) := by
  rw [Finset.disjoint_left]
  intro v hvHead hvRegion
  obtain ⟨k, hk, hvSide⟩ := Finset.mem_biUnion.mp hvRegion
  exact Finset.disjoint_left.mp (hdisj k hk) hvHead hvSide

lemma hpMatchingRegion_disjoint_of_disjoint_indices
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K J : Finset κ) (left right : κ → Finset V)
    (hKJ : Disjoint K J)
    (hedge : ∀ k j, k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j)) :
    Disjoint (hpMatchingRegion K left right)
      (hpMatchingRegion J left right) := by
  rw [Finset.disjoint_left]
  intro v hvK hvJ
  obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hvK
  obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvJ
  have hkj : k ≠ j := by
    intro h
    subst j
    exact Finset.disjoint_left.mp hKJ hk hj
  exact Finset.disjoint_left.mp (hedge k j hkj) hvk hvj

lemma matchingSideLoad_sum_eq_region
    {A V κ : Type*} [DecidableEq V] [DecidableEq κ]
    (P : Finset A) (f : A → V)
    (K : Finset κ) (left right : κ → Finset V)
    (hLR : ∀ k ∈ K, Disjoint (left k) (right k))
    (hedge : ∀ k ∈ K, ∀ j ∈ K, k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j)) :
    (∑ k ∈ K,
        (matchingSideLoad P f (left k) +
          matchingSideLoad P f (right k))) =
      (((P.image f) ∩ hpMatchingRegion K left right).card : ℝ) := by
  let I := P.image f
  have hside : ∀ k ∈ K,
      ((I ∩ (left k ∪ right k)).card : ℝ) =
        ((I ∩ left k).card : ℝ) + ((I ∩ right k).card : ℝ) := by
    intro k hk
    have hd :
        Disjoint (I ∩ left k) (I ∩ right k) :=
      (hLR k hk).mono Finset.inter_subset_right Finset.inter_subset_right
    have hu :
        (I ∩ left k) ∪ (I ∩ right k) =
          I ∩ (left k ∪ right k) := by
      ext v
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have hc := Finset.card_union_of_disjoint hd
    rw [hu] at hc
    exact_mod_cast hc
  have hdist : ∀ k ∈ K, ∀ j ∈ K, k ≠ j →
      Disjoint (I ∩ (left k ∪ right k))
        (I ∩ (left j ∪ right j)) := by
    intro k hk j hj hkj
    exact (hedge k hk j hj hkj).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hregion :
      I ∩ hpMatchingRegion K left right =
        K.biUnion (fun k => I ∩ (left k ∪ right k)) := by
    ext v
    simp only [hpMatchingRegion, Finset.mem_inter, Finset.mem_biUnion,
      Finset.mem_union]
    constructor
    · rintro ⟨hvI, k, hk, hvSide⟩
      exact ⟨k, hk, hvI, hvSide⟩
    · rintro ⟨k, hk, hvI, hvSide⟩
      exact ⟨hvI, k, hk, hvSide⟩
  calc
    (∑ k ∈ K,
        (matchingSideLoad P f (left k) +
          matchingSideLoad P f (right k))) =
      ∑ k ∈ K,
        (((I ∩ (left k ∪ right k)).card : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simpa [matchingSideLoad, I] using! (hside k hk).symm
    _ = ((K.biUnion
          (fun k => I ∩ (left k ∪ right k))).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion hdist).symm
    _ = ((I ∩ hpMatchingRegion K left right).card : ℝ) := by
      rw [hregion]

/-- Image points in the colour-`b` matching region come only from processed
nonseeds of route colour `b`. -/
lemma image_inter_matchingRegion_subset_route
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed P : Finset A) (f : A → V)
    (col routeColour : A → Bool)
    (headCore : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (hseed : ∀ s ∈ P, s ∈ Sseed → f s ∈ headCore (col s))
    (hnonseed : ∀ x ∈ P, x ∉ Sseed →
      f x ∈ matchingRegion (routeColour x))
    (hheadDisj : ∀ c b, Disjoint (headCore c) (matchingRegion b))
    (hregionDisj : Disjoint (matchingRegion false) (matchingRegion true))
    (b : Bool) :
    P.image f ∩ matchingRegion b ⊆
      (P.filter fun x => x ∉ Sseed ∧ routeColour x = b).image f := by
  intro v hv
  obtain ⟨hvImage, hvRegion⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.mp hvImage
  have hxNotSeed : x ∉ Sseed := by
    intro hxSeed
    exact Finset.disjoint_left.mp (hheadDisj (col x) b)
      (hseed x hxP hxSeed) hvRegion
  have hxRoute : routeColour x = b := by
    by_contra hne
    have hop : routeColour x = !b := by
      cases hb : b <;> cases hr : routeColour x <;> simp_all
    have hxOwn := hnonseed x hxP hxNotSeed
    cases hb : b <;> simp_all only [Bool.not_false, Bool.not_true]
    · exact Finset.disjoint_left.mp hregionDisj hvRegion hxOwn
    · exact Finset.disjoint_left.mp hregionDisj hxOwn hvRegion
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_filter.mpr ⟨hxP, hxNotSeed, hxRoute⟩, rfl⟩

/-- The summed matching load of one assigned edge family is bounded by the
number of processed nonseed vertices routed to that family. -/
lemma matching_load_sum_le_route_card
    {A V κ : Type*}
    [DecidableEq A] [DecidableEq V] [DecidableEq κ]
    (Sseed P : Finset A) (f : A → V)
    (col routeColour : A → Bool)
    (headCore : Bool → Finset V)
    (K : Bool → Finset κ)
    (left right : κ → Finset V)
    (hseed : ∀ s ∈ P, s ∈ Sseed → f s ∈ headCore (col s))
    (hnonseed : ∀ x ∈ P, x ∉ Sseed →
      f x ∈ hpMatchingRegion (K (routeColour x)) left right)
    (hheadDisj : ∀ c b,
      Disjoint (headCore c) (hpMatchingRegion (K b) left right))
    (hregionDisj :
      Disjoint (hpMatchingRegion (K false) left right)
        (hpMatchingRegion (K true) left right))
    (hLR : ∀ b k, k ∈ K b → Disjoint (left k) (right k))
    (hedge : ∀ b k, k ∈ K b → ∀ j, j ∈ K b → k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j))
    (b : Bool) :
    (∑ k ∈ K b,
        (matchingSideLoad P f (left k) +
          matchingSideLoad P f (right k))) ≤
      ((P.filter fun x => x ∉ Sseed ∧ routeColour x = b).card : ℝ) := by
  have himage :=
    image_inter_matchingRegion_subset_route
      Sseed P f col routeColour headCore
      (fun b => hpMatchingRegion (K b) left right)
      hseed hnonseed hheadDisj hregionDisj b
  rw [matchingSideLoad_sum_eq_region P f (K b) left right
    (hLR b) (hedge b)]
  exact_mod_cast
    (Finset.card_le_card himage).trans Finset.card_image_le

lemma matching_load_sum_le_route_card_on_subset
    {A V κ : Type*}
    [DecidableEq A] [DecidableEq V] [DecidableEq κ]
    (Sseed P : Finset A) (f : A → V)
    (col routeColour : A → Bool)
    (headCore : Bool → Finset V)
    (K : Bool → Finset κ) (Good : Finset κ)
    (left right : κ → Finset V)
    (b : Bool)
    (hGood : Good ⊆ K b)
    (hseed : ∀ s ∈ P, s ∈ Sseed → f s ∈ headCore (col s))
    (hnonseed : ∀ x ∈ P, x ∉ Sseed →
      f x ∈ hpMatchingRegion (K (routeColour x)) left right)
    (hheadDisj : ∀ c b,
      Disjoint (headCore c) (hpMatchingRegion (K b) left right))
    (hregionDisj :
      Disjoint (hpMatchingRegion (K false) left right)
        (hpMatchingRegion (K true) left right))
    (hLR : ∀ b k, k ∈ K b → Disjoint (left k) (right k))
    (hedge : ∀ b k, k ∈ K b → ∀ j, j ∈ K b → k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j)) :
    (∑ k ∈ Good,
        (matchingSideLoad P f (left k) +
          matchingSideLoad P f (right k))) ≤
      ((P.filter fun x =>
        x ∉ Sseed ∧ routeColour x = b).card : ℝ) := by
  have hsub :
      (∑ k ∈ Good,
          (matchingSideLoad P f (left k) +
            matchingSideLoad P f (right k))) ≤
        ∑ k ∈ K b,
          (matchingSideLoad P f (left k) +
            matchingSideLoad P f (right k)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hGood
      (fun _ _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact hsub.trans
    (matching_load_sum_le_route_card Sseed P f col routeColour
      headCore K left right hseed hnonseed hheadDisj
      hregionDisj hLR hedge b)

/-- Allocated total demand plus one local reserve per available matching edge
implies the aggregate surplus inequality at every intermediate state. -/
lemma matching_surplus_of_route_demand
    {κ : Type*} [DecidableEq κ]
    (Good : Finset κ)
    (l r L R : κ → ℝ) (demand reserve : ℝ)
    (hload : (∑ k ∈ Good, (l k + r k)) ≤ demand)
    (hallocated :
      demand + (Good.card : ℝ) * reserve ≤
        ∑ k ∈ Good, (L k + R k)) :
    (∑ k ∈ Good, (l k + r k)) +
        (Good.card : ℝ) * reserve ≤
      ∑ k ∈ Good, (L k + R k) := by
  linarith

end Erdos550
