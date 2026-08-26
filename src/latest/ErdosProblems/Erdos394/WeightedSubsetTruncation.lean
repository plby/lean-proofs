import ErdosProblems.Erdos394.GeneralEulerPower

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weighted subset cardinality truncation
-/

open Nat Finset

namespace Erdos394

/-- Subsets of cardinality at most `S`. -/
def boundedCardSubsets (P : Finset ℕ) (S : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun U ↦ U.card ≤ S)

/-- The first cardinality moment of powerset product weights is at most the
Euler product times the total one-point weight. -/
theorem sum_powerset_card_mul_prod_le
    (P : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ P, 0 ≤ x i) :
    (∑ U ∈ P.powerset, (U.card : ℝ) * ∏ i ∈ U, x i) ≤
      (∏ i ∈ P, (1 + x i)) * ∑ i ∈ P, x i := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      have hnonnegP : 0 ≤ ∏ i ∈ P, (1 + x i) := by
        apply Finset.prod_nonneg
        intro i hi
        exact add_nonneg zero_le_one
          (hx i (Finset.mem_insert_of_mem hi))
      have hsumP : 0 ≤ ∑ i ∈ P, x i :=
        Finset.sum_nonneg fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a P)
      have hPinj : Set.InjOn (insert a) (↑P.powerset : Set (Finset ℕ)) := by
        intro U hU V hV huv
        have hUa : a ∉ U := fun h ↦ ha (Finset.mem_powerset.mp hU h)
        have hVa : a ∉ V := fun h ↦ ha (Finset.mem_powerset.mp hV h)
        calc
          U = (insert a U).erase a := (Finset.erase_insert hUa).symm
          _ = (insert a V).erase a := by rw [huv]
          _ = V := Finset.erase_insert hVa
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro U hUP hUimg
        obtain ⟨V, hVP, hVU⟩ := Finset.mem_image.mp hUimg
        have haU : a ∈ U := hVU ▸ Finset.mem_insert_self a V
        exact ha (Finset.mem_powerset.mp hUP haU)
      have ih' := ih (fun i hi ↦ hx i (Finset.mem_insert_of_mem hi))
      rw [Finset.powerset_insert P a, Finset.sum_union hdisj,
        Finset.sum_image hPinj, Finset.prod_insert ha, Finset.sum_insert ha]
      have himage :
          (∑ U ∈ P.powerset,
            ((insert a U).card : ℝ) * ∏ i ∈ insert a U, x i) =
          x a * (∑ U ∈ P.powerset,
            (U.card : ℝ) * ∏ i ∈ U, x i) +
          x a * (∏ i ∈ P, (1 + x i)) := by
        calc
          (∑ U ∈ P.powerset,
            ((insert a U).card : ℝ) * ∏ i ∈ insert a U, x i) =
            ∑ U ∈ P.powerset,
              (x a * ((U.card : ℝ) * ∏ i ∈ U, x i) +
                x a * ∏ i ∈ U, x i) := by
              apply Finset.sum_congr rfl
              intro U hU
              have haU : a ∉ U := fun h ↦ ha (Finset.mem_powerset.mp hU h)
              rw [Finset.card_insert_of_notMem haU, Finset.prod_insert haU]
              push_cast
              ring
          _ = x a * (∑ U ∈ P.powerset,
                (U.card : ℝ) * ∏ i ∈ U, x i) +
              x a * (∑ U ∈ P.powerset, ∏ i ∈ U, x i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = x a * (∑ U ∈ P.powerset,
                (U.card : ℝ) * ∏ i ∈ U, x i) +
              x a * (∏ i ∈ P, (1 + x i)) := by
            rw [sum_powerset_prod_eq_prod_one_add]
      rw [himage]
      have hcoeff0 : 0 ≤ 1 + x a := by positivity
      have hscaled := mul_le_mul_of_nonneg_left ih' hcoeff0
      have hextra : 0 ≤ x a * x a * (∏ i ∈ P, (1 + x i)) := by positivity
      nlinarith

/-- Weight of subsets whose cardinality exceeds `S`. -/
def largeCardSubsetWeight (P : Finset ℕ) (S : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ U ∈ P.powerset.filter (fun U ↦ S < U.card), ∏ i ∈ U, x i

/-- A first-moment Markov bound for the large-cardinality subset weight. -/
theorem largeCardSubsetWeight_mul_le
    (P : Finset ℕ) (S : ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ P, 0 ≤ x i) :
    (S + 1 : ℝ) * largeCardSubsetWeight P S x ≤
      (∏ i ∈ P, (1 + x i)) * ∑ i ∈ P, x i := by
  apply le_trans ?_ (sum_powerset_card_mul_prod_le P x hx)
  unfold largeCardSubsetWeight
  rw [Finset.mul_sum]
  calc
    (∑ U ∈ P.powerset.filter (fun U ↦ S < U.card),
      (S + 1 : ℝ) * ∏ i ∈ U, x i) ≤
      ∑ U ∈ P.powerset.filter (fun U ↦ S < U.card),
        (U.card : ℝ) * ∏ i ∈ U, x i := by
      apply Finset.sum_le_sum
      intro U hU
      have hcard : S + 1 ≤ U.card := by
        exact Nat.succ_le_iff.mpr (Finset.mem_filter.mp hU).2
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · apply Finset.prod_nonneg
        intro i hi
        exact hx i (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hi)
    _ ≤ ∑ U ∈ P.powerset, (U.card : ℝ) * ∏ i ∈ U, x i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro U hU hnot
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i hi ↦
        hx i (Finset.mem_powerset.mp hU hi))

/-- If the cutoff is four times the total point weight, bounded-cardinality
subsets retain at least three quarters of the full Euler weight. -/
theorem three_mul_euler_le_four_mul_boundedSubsetWeight
    (P : Finset ℕ) (S : ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ P, 0 ≤ x i)
    (hcut : 4 * (∑ i ∈ P, x i) ≤ (S + 1 : ℝ)) :
    3 * (∏ i ∈ P, (1 + x i)) ≤
      4 * (∑ U ∈ boundedCardSubsets P S, ∏ i ∈ U, x i) := by
  let E : ℝ := ∏ i ∈ P, (1 + x i)
  let B : ℝ := ∑ U ∈ boundedCardSubsets P S, ∏ i ∈ U, x i
  let D : ℝ := largeCardSubsetWeight P S x
  have hE0 : 0 ≤ E := by
    dsimp [E]
    apply Finset.prod_nonneg
    intro i hi
    exact add_nonneg zero_le_one (hx i hi)
  have hD0 : 0 ≤ D := by
    dsimp [D, largeCardSubsetWeight]
    apply Finset.sum_nonneg
    intro U hU
    apply Finset.prod_nonneg
    intro i hi
    exact hx i (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hi)
  have hpartition : B + D = E := by
    dsimp [B, D, E, boundedCardSubsets, largeCardSubsetWeight]
    rw [← Finset.sum_union]
    · have hUnion :
          P.powerset.filter (fun U ↦ U.card ≤ S) ∪
            P.powerset.filter (fun U ↦ S < U.card) = P.powerset := by
        ext U
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro (⟨hUP, hs⟩ | ⟨hUP, hl⟩)
          · exact hUP
          · exact hUP
        · intro hUP
          by_cases hs : U.card ≤ S
          · exact Or.inl ⟨hUP, hs⟩
          · exact Or.inr ⟨hUP, Nat.lt_of_not_ge hs⟩
      rw [hUnion, sum_powerset_prod_eq_prod_one_add]
    · rw [Finset.disjoint_left]
      intro U hsmall hlarge
      have hs := (Finset.mem_filter.mp hsmall).2
      have hl := (Finset.mem_filter.mp hlarge).2
      omega
  have hmarkov := largeCardSubsetWeight_mul_le P S x hx
  have hSD : (S + 1 : ℝ) * D ≤ E * ∑ i ∈ P, x i := by
    simpa [D, E] using hmarkov
  have hquarter : 4 * D ≤ E := by
    have hcutD := mul_le_mul_of_nonneg_right hcut hD0
    nlinarith
  nlinarith

/-- After removing the empty subset, at least half the Euler weight remains
when the full product is at least four. -/
theorem two_mul_euler_le_four_mul_nonemptyBoundedSubsetWeight
    (P : Finset ℕ) (S : ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ P, 0 ≤ x i)
    (hcut : 4 * (∑ i ∈ P, x i) ≤ (S + 1 : ℝ))
    (hE4 : 4 ≤ ∏ i ∈ P, (1 + x i)) :
    2 * (∏ i ∈ P, (1 + x i)) ≤
      4 * (∑ U ∈ (boundedCardSubsets P S).erase ∅,
        ∏ i ∈ U, x i) := by
  have hthree := three_mul_euler_le_four_mul_boundedSubsetWeight P S x hx hcut
  have hempty : (∅ : Finset ℕ) ∈ boundedCardSubsets P S := by
    simp [boundedCardSubsets]
  have herase := Finset.sum_erase_add (s := boundedCardSubsets P S)
    (f := fun U ↦ ∏ i ∈ U, x i) hempty
  simp only [Finset.prod_empty] at herase
  nlinarith

end Erdos394
