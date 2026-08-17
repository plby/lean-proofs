import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# A finite sunflower bound

This file proves the classical elementary Erdős--Rado sunflower bound.  The
form used here is deliberately phrased for finite families of finite sets, so
that it can be used directly in the structural part of Problem 636.
-/

namespace Erdos636

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- A finite family is a sunflower with core `C` when every two distinct
members have intersection exactly `C`. -/
def IsSunflower (𝒜 : Finset (Finset α)) (C : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒜 → ∀ ⦃B⦄, B ∈ 𝒜 → A ≠ B → A ∩ B = C

lemma IsSunflower.mono {𝒜 ℬ : Finset (Finset α)} {C : Finset α}
    (h : IsSunflower 𝒜 C) (hℬ : ℬ ⊆ 𝒜) : IsSunflower ℬ C := by
  intro A hA B hB hne
  exact h (hℬ hA) (hℬ hB) hne

/-- The petals obtained by deleting the core of a sunflower are pairwise
disjoint. -/
lemma IsSunflower.pairwiseDisjoint_sdiff {𝒜 : Finset (Finset α)} {C : Finset α}
    (h : IsSunflower 𝒜 C) :
    (𝒜 : Set (Finset α)).PairwiseDisjoint (fun A => A \ C) := by
  intro A hA B hB hne
  change Disjoint (A \ C) (B \ C)
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hxAC := Finset.mem_sdiff.mp hxA
  have hxBC := Finset.mem_sdiff.mp hxB
  exact hxAC.2 (by
    rw [← h hA hB hne]
    exact Finset.mem_inter.mpr ⟨hxAC.1, hxBC.1⟩)

lemma isSunflower_empty_of_pairwiseDisjoint {𝒜 : Finset (Finset α)}
    (h𝒜 : (𝒜 : Set (Finset α)).PairwiseDisjoint id) :
    IsSunflower 𝒜 ∅ := by
  intro A hA B hB hne
  exact Finset.disjoint_iff_inter_eq_empty.mp (h𝒜 hA hB hne)

/-- A maximum-cardinality pairwise-disjoint subfamily. -/
private lemma exists_max_disjointSubfamily (𝒜 : Finset (Finset α)) :
    ∃ ℳ : Finset (Finset α),
      ℳ ⊆ 𝒜 ∧
      (ℳ : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ 𝒩 : Finset (Finset α), 𝒩 ⊆ 𝒜 →
        (𝒩 : Set (Finset α)).PairwiseDisjoint id → 𝒩.card ≤ ℳ.card := by
  classical
  let candidates := 𝒜.powerset.filter fun ℳ : Finset (Finset α) =>
    (ℳ : Set (Finset α)).PairwiseDisjoint id
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨ℳ, hℳ, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
  have hℳ' : ℳ ∈ 𝒜.powerset.filter fun ℳ : Finset (Finset α) =>
      (ℳ : Set (Finset α)).PairwiseDisjoint id := by
    simpa [candidates] using hℳ
  refine ⟨ℳ, ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hℳ').1
  · exact (Finset.mem_filter.mp hℳ').2
  · intro 𝒩 h𝒩𝒜 h𝒩disj
    have h𝒩mem : 𝒩 ∈ candidates := by
      change 𝒩 ∈ 𝒜.powerset.filter (fun 𝒦 : Finset (Finset α) =>
        (𝒦 : Set (Finset α)).PairwiseDisjoint id)
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h𝒩𝒜, h𝒩disj⟩
    exact hmax 𝒩 h𝒩mem

/-- Every member of a uniform family meets the union of a maximum disjoint
subfamily.  Uniformity is used only to exclude the empty set. -/
private lemma meets_biUnion_of_max_disjointSubfamily
    {𝒜 ℳ : Finset (Finset α)} {k : ℕ}
    (hk : 0 < k) (hunif : ∀ A ∈ 𝒜, A.card = k)
    (hℳ𝒜 : ℳ ⊆ 𝒜) (hℳdisj : (ℳ : Set (Finset α)).PairwiseDisjoint id)
    (hmax : ∀ 𝒩 : Finset (Finset α), 𝒩 ⊆ 𝒜 →
      (𝒩 : Set (Finset α)).PairwiseDisjoint id → 𝒩.card ≤ ℳ.card) :
    ∀ A ∈ 𝒜, ¬ Disjoint A (ℳ.biUnion id) := by
  intro A hA hdisj
  have hAne : A.Nonempty := Finset.card_pos.mp (hunif A hA ▸ hk)
  have hAnotmem : A ∉ ℳ := by
    intro hAℳ
    have hsub : A ⊆ ℳ.biUnion id := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨A, hAℳ, hx⟩
    obtain ⟨x, hxA⟩ := hAne
    exact Finset.disjoint_left.mp hdisj hxA (hsub hxA)
  have hinsSub : insert A ℳ ⊆ 𝒜 := by
    simpa [Finset.insert_subset_iff] using ⟨hA, hℳ𝒜⟩
  have hinsDisj : ((insert A ℳ : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id := by
    rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem]
    · refine ⟨hℳdisj, ?_⟩
      intro B hB
      exact hdisj.mono_right (Finset.subset_biUnion_of_mem id hB)
    · simpa using hAnotmem
  have hle := hmax (insert A ℳ) hinsSub hinsDisj
  simp [hAnotmem] at hle

/-- Removing a common point is injective on the sets which contain it. -/
private lemma erase_injOn_star (x : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (fun A : Finset α => A.erase x) {A | A ∈ 𝒜 ∧ x ∈ A} := by
  intro A hA B hB hEq
  calc
    A = insert x (A.erase x) := (Finset.insert_erase hA.2).symm
    _ = insert x (B.erase x) := congrArg (insert x) hEq
    _ = B := Finset.insert_erase hB.2

/-- If `𝒜` is a `k`-uniform family and
`k! (r-1)^k < |𝒜|`, then `𝒜` contains an `r`-member sunflower.

This is the elementary Erdős--Rado sunflower lemma.  The explicit polynomial
bound is convenient in asymptotic applications: for fixed `k`, it yields
sunflowers whose number of petals is of order `|𝒜|^(1/k)`. -/
theorem exists_sunflower_of_factorial_mul_pow_lt_card
    (k r : ℕ) (hr : 0 < r) (𝒜 : Finset (Finset α))
    (hunif : ∀ A ∈ 𝒜, A.card = k)
    (hcard : k.factorial * (r - 1) ^ k < 𝒜.card) :
    ∃ ℬ : Finset (Finset α), ℬ ⊆ 𝒜 ∧ ℬ.card = r ∧
      ∃ C : Finset α, IsSunflower ℬ C := by
  induction k generalizing 𝒜 with
  | zero =>
      have hsub : 𝒜 ⊆ {∅} := by
        intro A hA
        have hzero : A.card = 0 := hunif A hA
        simpa [Finset.card_eq_zero.mp hzero]
      have hle : 𝒜.card ≤ 1 := by
        simpa using Finset.card_le_card hsub
      simp at hcard
      omega
  | succ k ih =>
      obtain ⟨ℳ, hℳ𝒜, hℳdisj, hmax⟩ := exists_max_disjointSubfamily 𝒜
      by_cases hlarge : r ≤ ℳ.card
      · obtain ⟨ℬ, hℬℳ, hℬcard⟩ := Finset.exists_subset_card_eq hlarge
        refine ⟨ℬ, hℬℳ.trans hℳ𝒜, hℬcard, ∅, ?_⟩
        apply isSunflower_empty_of_pairwiseDisjoint
        intro A hA B hB hne
        exact hℳdisj (hℬℳ hA) (hℬℳ hB) hne
      · have hℳlt : ℳ.card < r := Nat.lt_of_not_ge hlarge
        let U : Finset α := ℳ.biUnion id
        let threshold : ℕ := k.factorial * (r - 1) ^ k
        have hUcard : U.card ≤ (k + 1) * (r - 1) := by
          calc
            U.card ≤ ℳ.card * (k + 1) := by
              apply Finset.card_biUnion_le_card_mul
              intro A hA
              simpa [Nat.add_comm] using (hunif A (hℳ𝒜 hA)).le
            _ ≤ (r - 1) * (k + 1) := by
              gcongr
              omega
            _ = (k + 1) * (r - 1) := Nat.mul_comm _ _
        have hmeet : ∀ A ∈ 𝒜, ¬ Disjoint A U := by
          simpa [U] using meets_biUnion_of_max_disjointSubfamily
            (𝒜 := 𝒜) (ℳ := ℳ) (k := k + 1) (by omega) hunif hℳ𝒜 hℳdisj hmax
        have hdegree : ∃ x ∈ U, threshold < (𝒜.filter fun A => x ∈ A).card := by
          by_contra hnone
          push Not at hnone
          have hcover : 𝒜 ⊆ U.biUnion (fun x => 𝒜.filter fun A => x ∈ A) := by
            intro A hA
            obtain ⟨x, hxA, hxU⟩ := Finset.not_disjoint_iff.mp (hmeet A hA)
            exact Finset.mem_biUnion.mpr ⟨x, hxU,
              Finset.mem_filter.mpr ⟨hA, hxA⟩⟩
          have hfamilyCard : 𝒜.card ≤ U.card * threshold :=
            (Finset.card_le_card hcover).trans
              (Finset.card_biUnion_le_card_mul U
                (fun x => 𝒜.filter fun A => x ∈ A) threshold hnone)
          have hthreshold : U.card * threshold ≤
              (k + 1).factorial * (r - 1) ^ (k + 1) := by
            calc
              U.card * threshold ≤ ((k + 1) * (r - 1)) * threshold := by
                gcongr
              _ = (k + 1).factorial * (r - 1) ^ (k + 1) := by
                simp only [threshold, Nat.factorial_succ, pow_succ]
                ring
          exact (not_lt_of_ge (hfamilyCard.trans hthreshold)) hcard
        obtain ⟨x, hxU, hxdegree⟩ := hdegree
        let star : Finset (Finset α) := 𝒜.filter fun A => x ∈ A
        let reduced : Finset (Finset α) := star.image fun A => A.erase x
        have hstarSub : star ⊆ 𝒜 := Finset.filter_subset _ _
        have hxstar : ∀ A ∈ star, x ∈ A := by
          intro A hA
          exact (Finset.mem_filter.mp hA).2
        have hreducedCard : reduced.card = star.card := by
          apply Finset.card_image_of_injOn
          intro A hA B hB hEq
          exact erase_injOn_star x 𝒜
            ⟨hstarSub hA, hxstar A hA⟩ ⟨hstarSub hB, hxstar B hB⟩ hEq
        have hreducedUnif : ∀ A ∈ reduced, A.card = k := by
          intro A hA
          obtain ⟨B, hBstar, rfl⟩ := Finset.mem_image.mp hA
          rw [Finset.card_erase_of_mem (hxstar B hBstar), hunif B (hstarSub hBstar)]
          omega
        have hreducedLarge : threshold < reduced.card := by
          rw [hreducedCard]
          simpa [star] using hxdegree
        obtain ⟨𝒟, h𝒟red, h𝒟card, C, h𝒟sun⟩ :=
          ih reduced hreducedUnif (by simpa [threshold] using hreducedLarge)
        let ℬ : Finset (Finset α) := 𝒟.image fun A => insert x A
        have hxnotmemReduced : ∀ A ∈ reduced, x ∉ A := by
          intro A hA
          obtain ⟨B, hBstar, rfl⟩ := Finset.mem_image.mp hA
          simp
        have hxnotmem𝒟 : ∀ A ∈ 𝒟, x ∉ A := fun A hA => hxnotmemReduced A (h𝒟red hA)
        have hinsertInj : Set.InjOn (fun A : Finset α => insert x A) 𝒟 := by
          intro A hA B hB hEq
          calc
            A = (insert x A).erase x := by simp [hxnotmem𝒟 A hA]
            _ = (insert x B).erase x := congrArg (fun S : Finset α => S.erase x) hEq
            _ = B := by simp [hxnotmem𝒟 B hB]
        have hℬcard : ℬ.card = r := by
          rw [Finset.card_image_of_injOn hinsertInj, h𝒟card]
        have hℬsub : ℬ ⊆ 𝒜 := by
          intro A hA
          obtain ⟨B, hB𝒟, rfl⟩ := Finset.mem_image.mp hA
          obtain ⟨D, hDstar, hDB⟩ := Finset.mem_image.mp (h𝒟red hB𝒟)
          rw [← hDB, Finset.insert_erase (hxstar D hDstar)]
          exact hstarSub hDstar
        refine ⟨ℬ, hℬsub, hℬcard, insert x C, ?_⟩
        intro A hA B hB hAB
        obtain ⟨A', hA'𝒟, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨B', hB'𝒟, rfl⟩ := Finset.mem_image.mp hB
        have hA'B' : A' ≠ B' := fun h => hAB (congrArg (insert x) h)
        have hinter : insert x A' ∩ insert x B' = insert x (A' ∩ B') := by
          ext y
          simp only [Finset.mem_inter, Finset.mem_insert]
          tauto
        rw [hinter, h𝒟sun hA'𝒟 hB'𝒟 hA'B']

end Erdos636
