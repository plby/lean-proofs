import Mathlib

/-!
# Finite monotone capacities for Erdős Problem 49

This file contains the purely finite part of Tao's decomposition argument.
The capacity of a finite set is the largest cardinality of a subset on which
Euler's totient is nondecreasing.  Capacity is monotone, bounded by ordinary
cardinality, and subadditive under unions.
-/

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Euler's totient is weakly increasing on `A` in the ambient order. -/
def TotientMonotoneOn (A : Finset ℕ) : Prop :=
  ∀ ⦃m⦄, m ∈ A → ∀ ⦃n⦄, n ∈ A → m ≤ n →
    Nat.totient m ≤ Nat.totient n

/-- Euler's totient is strictly increasing on `A` in the ambient order. -/
def TotientStrictOn (A : Finset ℕ) : Prop :=
  ∀ ⦃m⦄, m ∈ A → ∀ ⦃n⦄, n ∈ A → m < n →
    Nat.totient m < Nat.totient n

lemma TotientMonotoneOn.mono {A B : Finset ℕ}
    (hA : TotientMonotoneOn A) (hBA : B ⊆ A) :
    TotientMonotoneOn B := by
  intro m hm n hn hmn
  exact hA (hBA hm) (hBA hn) hmn

lemma TotientStrictOn.mono {A B : Finset ℕ}
    (hA : TotientStrictOn A) (hBA : B ⊆ A) :
    TotientStrictOn B := by
  intro m hm n hn hmn
  exact hA (hBA hm) (hBA hn) hmn

/-- The monotone subsets of an arbitrary finite ambient set. -/
def monotoneSubsets (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter (TotientMonotoneOn ·)

/-- The maximum size of a totient-nondecreasing subset of `S`. -/
def monotoneCapacity (S : Finset ℕ) : ℕ :=
  (monotoneSubsets S).sup Finset.card

@[simp] lemma mem_monotoneSubsets {S A : Finset ℕ} :
    A ∈ monotoneSubsets S ↔ A ⊆ S ∧ TotientMonotoneOn A := by
  simp [monotoneSubsets]

lemma monotoneSubsets_nonempty (S : Finset ℕ) :
    (monotoneSubsets S).Nonempty := by
  refine ⟨∅, ?_⟩
  rw [mem_monotoneSubsets]
  refine ⟨Finset.empty_subset S, ?_⟩
  intro m hm
  simp at hm

lemma card_le_monotoneCapacity {S A : Finset ℕ}
    (hAS : A ⊆ S) (hA : TotientMonotoneOn A) :
    A.card ≤ monotoneCapacity S := by
  exact Finset.le_sup (f := Finset.card)
    (mem_monotoneSubsets.mpr ⟨hAS, hA⟩)

lemma monotoneCapacity_le_card (S : Finset ℕ) :
    monotoneCapacity S ≤ S.card := by
  apply Finset.sup_le
  intro A hA
  exact Finset.card_le_card (mem_monotoneSubsets.mp hA).1

lemma monotoneCapacity_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    monotoneCapacity S ≤ monotoneCapacity T := by
  apply Finset.sup_le
  intro A hA
  have hdata := mem_monotoneSubsets.mp hA
  exact card_le_monotoneCapacity (hdata.1.trans hST) hdata.2

/-- The elementary subadditivity used to split Tao's primary, secondary, and
exceptional sets. -/
lemma monotoneCapacity_union_le (S T : Finset ℕ) :
    monotoneCapacity (S ∪ T) ≤
      monotoneCapacity S + monotoneCapacity T := by
  apply Finset.sup_le
  intro A hA
  have hdata := mem_monotoneSubsets.mp hA
  let AS := A ∩ S
  let AT := A \ S
  have hASsub : AS ⊆ S := Finset.inter_subset_right
  have hATsub : AT ⊆ T := by
    intro n hn
    have hnA : n ∈ A := (Finset.mem_sdiff.mp hn).1
    have hnUnion := hdata.1 hnA
    rcases Finset.mem_union.mp hnUnion with hnS | hnT
    · exact False.elim ((Finset.mem_sdiff.mp hn).2 hnS)
    · exact hnT
  have hASmono : TotientMonotoneOn AS :=
    hdata.2.mono Finset.inter_subset_left
  have hATmono : TotientMonotoneOn AT :=
    hdata.2.mono Finset.sdiff_subset
  have hcard : A.card = AS.card + AT.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext n
      by_cases hn : n ∈ S <;> simp [AS, AT, hn]
    · exact Finset.disjoint_left.mpr fun n hnAS hnAT ↦
        (Finset.mem_sdiff.mp hnAT).2 (Finset.mem_inter.mp hnAS).2
  rw [hcard]
  exact Nat.add_le_add
    (card_le_monotoneCapacity hASsub hASmono)
    (card_le_monotoneCapacity hATsub hATmono)

lemma monotoneCapacity_biUnion_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset ℕ) :
    monotoneCapacity (I.biUnion S) ≤
      ∑ i ∈ I, monotoneCapacity (S i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [monotoneCapacity, monotoneSubsets]
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (monotoneCapacity_union_le (S i) (I.biUnion S)).trans
        (Nat.add_le_add_left ih _)

/-! ## Finite interval-packing bounds -/

/-- Pairwise-disjoint finite pieces contained in `S` have total cardinality
at most `S.card`.  This is the exact finite form of the packing step used for
the primary hulls in Tao's proof. -/
lemma sum_card_le_card_of_pairwiseDisjoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (S : Finset ℕ)
    (hF : ∀ i ∈ I, F i ⊆ S)
    (hdisj : (I : Set ι).PairwiseDisjoint F) :
    ∑ i ∈ I, (F i).card ≤ S.card := by
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.2 hF)

/-- Bounded-overlap packing: if each point of `S` occurs in at most `r`
pieces, the sum of their cardinalities is at most `r * S.card`. -/
lemma sum_card_le_mul_card_of_boundedOverlap {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (S : Finset ℕ) (r : ℕ)
    (hF : ∀ i ∈ I, F i ⊆ S)
    (hoverlap : ∀ x ∈ S, (I.filter fun i ↦ x ∈ F i).card ≤ r) :
    ∑ i ∈ I, (F i).card ≤ r * S.card := by
  have hrow (i : ι) (hi : i ∈ I) :
      (F i).card = ∑ x ∈ S, if x ∈ F i then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp only [ite_self, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨hF i hi hx, hx⟩
    · exact And.right
  calc
    ∑ i ∈ I, (F i).card =
        ∑ i ∈ I, ∑ x ∈ S, if x ∈ F i then 1 else 0 := by
          apply Finset.sum_congr rfl
          exact hrow
    _ = ∑ x ∈ S, ∑ i ∈ I, if x ∈ F i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (I.filter fun i ↦ x ∈ F i).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ _x ∈ S, r := by
      exact Finset.sum_le_sum fun x hx ↦ hoverlap x hx
    _ = r * S.card := by simp [mul_comm]

/-- The ambient interval `[1,N]` has exactly `N` elements. -/
@[simp] lemma card_Icc_one (N : ℕ) : (Finset.Icc 1 N).card = N := by
  simp [Nat.add_one_sub_one]

lemma sum_card_Icc_le_of_pairwiseDisjoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (N : ℕ)
    (hF : ∀ i ∈ I, F i ⊆ Finset.Icc 1 N)
    (hdisj : (I : Set ι).PairwiseDisjoint F) :
    ∑ i ∈ I, (F i).card ≤ N := by
  simpa using sum_card_le_card_of_pairwiseDisjoint I F (Finset.Icc 1 N) hF hdisj

lemma sum_card_Icc_le_of_boundedOverlap {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (N r : ℕ)
    (hF : ∀ i ∈ I, F i ⊆ Finset.Icc 1 N)
    (hoverlap : ∀ x ∈ Finset.Icc 1 N,
      (I.filter fun i ↦ x ∈ F i).card ≤ r) :
    ∑ i ∈ I, (F i).card ≤ r * N := by
  simpa using sum_card_le_mul_card_of_boundedOverlap
    I F (Finset.Icc 1 N) r hF hoverlap

/-! ## Integer hulls -/

/-- The smallest closed integer interval containing a finite set; the hull of
the empty set is empty. -/
def intervalHull (S : Finset ℕ) : Finset ℕ :=
  if hS : S.Nonempty then Finset.Icc (S.min' hS) (S.max' hS) else ∅

lemma subset_intervalHull (S : Finset ℕ) : S ⊆ intervalHull S := by
  intro n hn
  have hS : S.Nonempty := ⟨n, hn⟩
  simp only [intervalHull, dif_pos hS, Finset.mem_Icc]
  exact ⟨S.min'_le n hn, S.le_max' n hn⟩

lemma intervalHull_subset_Icc {S : Finset ℕ} {a b : ℕ}
    (hS : S ⊆ Finset.Icc a b) : intervalHull S ⊆ Finset.Icc a b := by
  by_cases hne : S.Nonempty
  · intro n hn
    rw [intervalHull, dif_pos hne] at hn
    have hmin := hS (S.min'_mem hne)
    have hmax := hS (S.max'_mem hne)
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hmin).1.trans (Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans (Finset.mem_Icc.mp hmax).2⟩
  · simp [intervalHull, hne]

lemma intervalHull_disjoint_of_lt {S T : Finset ℕ}
    (hST : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    Disjoint (intervalHull S) (intervalHull T) := by
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · apply Finset.disjoint_left.mpr
      intro n hnS hnT
      rw [intervalHull, dif_pos hS] at hnS
      rw [intervalHull, dif_pos hT] at hnT
      have hgap := hST (S.max' hS) (S.max'_mem hS)
        (T.min' hT) (T.min'_mem hT)
      have hnUpper := (Finset.mem_Icc.mp hnS).2
      have hnLower := (Finset.mem_Icc.mp hnT).1
      omega
    · simp [intervalHull, hT]
  · simp [intervalHull, hS]

lemma card_le_card_intervalHull (S : Finset ℕ) :
    S.card ≤ (intervalHull S).card :=
  Finset.card_le_card (subset_intervalHull S)

end

end Erdos49
