import ErdosProblems.Erdos1161.CycleBounds
import ErdosProblems.Erdos1161.CycleRecursion
import ErdosProblems.Erdos1161.DivisorBounds
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Assigning prime powers to exposed cycles

This file formalizes the finite ``decrement chain'' estimate used as
Lemma 2.5 in Beker's proof.  A list in `positiveCompositions n ell` is a
possible sequence of cycle lengths obtained by repeatedly exposing the
cycle containing a distinguished remaining letter.  Its weight is the
product of the reciprocal sizes of the successive remaining sets.
-/

open scoped BigOperators

namespace Erdos1161

noncomputable section

/-- Positive compositions of `n` into exactly `ell` parts. -/
def positiveCompositions : (n ell : ℕ) → Finset (List ℕ)
  | n, 0 => if n = 0 then {[]} else ∅
  | n, ell + 1 =>
      (Finset.Icc 1 n).biUnion fun j ↦
        (positiveCompositions (n - j) ell).image (List.cons j)

@[simp] theorem mem_positiveCompositions_zero {n : ℕ} :
    [] ∈ positiveCompositions n 0 ↔ n = 0 := by
  unfold positiveCompositions
  by_cases hn : n = 0 <;> simp [hn]

@[simp] theorem mem_positiveCompositions_succ {n ell : ℕ} {xs : List ℕ} :
    xs ∈ positiveCompositions n (ell + 1) ↔
      ∃ j ∈ Finset.Icc 1 n, ∃ ys ∈ positiveCompositions (n - j) ell,
        j :: ys = xs := by
  simp [positiveCompositions]

theorem mem_positiveCompositions_iff {n ell : ℕ} {xs : List ℕ} :
    xs ∈ positiveCompositions n ell ↔
      xs.length = ell ∧ xs.sum = n ∧ ∀ j ∈ xs, 0 < j := by
  induction ell generalizing n xs with
  | zero =>
      cases xs with
      | nil => simp [eq_comm]
      | cons j js =>
          by_cases hn : n = 0 <;> simp [positiveCompositions, hn]
  | succ ell ih =>
      constructor
      · intro h
        rw [mem_positiveCompositions_succ] at h
        obtain ⟨j, hj, ys, hys, rfl⟩ := h
        have hdata := ih.mp hys
        rw [Finset.mem_Icc] at hj
        simp only [List.length_cons, List.sum_cons, List.mem_cons]
        refine ⟨congrArg Nat.succ hdata.1, ?_, ?_⟩
        · omega
        · rintro a (rfl | ha)
          · omega
          · exact hdata.2.2 a ha
      · rintro ⟨hlen, hsum, hpos⟩
        cases xs with
        | nil => simp at hlen
        | cons j ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.sum_cons] at hsum
          have hjpos : 0 < j := hpos j (by simp)
          have hjle : j ≤ n := by omega
          rw [mem_positiveCompositions_succ]
          refine ⟨j, Finset.mem_Icc.mpr ⟨hjpos, hjle⟩, ys, ih.mpr ?_, rfl⟩
          refine ⟨hlen, ?_, ?_⟩
          · omega
          · intro a ha
            exact hpos a (by simp [ha])

/-- The probability weight of an exposed sequence of cycle lengths. -/
def decrementWeight : (n : ℕ) → List ℕ → ℚ
  | _, [] => 1
  | n, j :: js => (1 / (n : ℚ)) * decrementWeight (n - j) js

theorem decrementWeight_nonneg (n : ℕ) (xs : List ℕ) :
    0 ≤ decrementWeight n xs := by
  induction xs generalizing n with
  | nil => simp [decrementWeight]
  | cons j js ih =>
      simp only [decrementWeight]
      exact mul_nonneg (by positivity) (ih _)

/-- Total decrement-chain mass subject to one divisibility requirement per
successive exposed cycle. -/
def constrainedDecrementMass : (n : ℕ) → List ℕ → ℚ
  | n, [] => if n = 0 then 1 else 0
  | n, q :: qs =>
      ∑ j ∈ (Finset.Icc 1 n).filter (q ∣ ·),
        (1 / (n : ℚ)) * constrainedDecrementMass (n - j) qs

theorem constrainedDecrementMass_nonneg (n : ℕ) (qs : List ℕ) :
    0 ≤ constrainedDecrementMass n qs := by
  induction qs generalizing n with
  | nil =>
      simp only [constrainedDecrementMass]
      split <;> norm_num
  | cons q qs ih =>
      simp only [constrainedDecrementMass]
      exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (by positivity) (ih _)

theorem constrainedDecrementMass_eq_sum (n : ℕ) (qs : List ℕ) :
    constrainedDecrementMass n qs =
      ∑ xs ∈ positiveCompositions n qs.length,
        if List.Forall₂ (· ∣ ·) qs xs then decrementWeight n xs else 0 := by
  induction qs generalizing n with
  | nil =>
      simp only [constrainedDecrementMass, List.length_nil]
      by_cases hn : n = 0
      · subst n
        simp [positiveCompositions, decrementWeight]
      · simp [positiveCompositions, hn]
  | cons q qs ih =>
      rw [constrainedDecrementMass, Finset.sum_filter]
      simp only [List.length_cons, positiveCompositions]
      have hdisj : Set.Pairwise (Finset.Icc 1 n : Set ℕ) fun a b ↦
          Disjoint
            ((positiveCompositions (n - a) qs.length).image (List.cons a))
            ((positiveCompositions (n - b) qs.length).image (List.cons b)) := by
        intro a _ b _ hab
        rw [Finset.disjoint_left]
        rintro xs hxa hxb
        rw [Finset.mem_image] at hxa hxb
        obtain ⟨ys, _, rfl⟩ := hxa
        obtain ⟨zs, _, hzs⟩ := hxb
        exact hab (by simpa using (congrArg List.head? hzs).symm)
      rw [Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_image]
      · simp only [List.forall₂_cons, decrementWeight]
        by_cases hq : q ∣ j
        · simp only [hq, true_and, if_true]
          rw [ih, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro xs hxs
          by_cases htail : List.Forall₂ (· ∣ ·) qs xs <;> simp [htail]
        · simp [hq]
      · intro a _ b _ hab
        exact (List.cons.inj hab).2

theorem card_positive_multiples (n q : ℕ) :
    ((Finset.Icc 1 n).filter (q ∣ ·)).card = n / q := by
  have hfin : (Finset.Icc 1 n).filter (q ∣ ·) =
      (Finset.range (n + 1)).filter fun k ↦ k ≠ 0 ∧ q ∣ k := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hfin]
  exact Nat.card_multiples' n q

/-- A fixed assignment of positive divisors to exposed cycles has mass at
most the reciprocal of their product. -/
theorem constrainedDecrementMass_le_inv_prod {n : ℕ} {qs : List ℕ}
    (hqs : ∀ q ∈ qs, 0 < q) :
    constrainedDecrementMass n qs ≤ 1 / (qs.prod : ℚ) := by
  induction qs generalizing n with
  | nil =>
      simp only [constrainedDecrementMass, List.prod_nil, Nat.cast_one, div_one]
      split <;> norm_num
  | cons q qs ih =>
      have hq : 0 < q := hqs q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hqs r (by simp [hr])
      have hprod : 0 < qs.prod := List.prod_pos htail
      rw [constrainedDecrementMass]
      calc
        (∑ j ∈ (Finset.Icc 1 n).filter (q ∣ ·),
            (1 / (n : ℚ)) * constrainedDecrementMass (n - j) qs) ≤
            ∑ _j ∈ (Finset.Icc 1 n).filter (q ∣ ·),
              (1 / (n : ℚ)) * (1 / (qs.prod : ℚ)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (ih htail) (by positivity)
        _ = (((Finset.Icc 1 n).filter (q ∣ ·)).card : ℚ) *
              ((1 / (n : ℚ)) * (1 / (qs.prod : ℚ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 / (q : ℚ)) * (1 / (qs.prod : ℚ)) := by
          rw [card_positive_multiples]
          by_cases hn : n = 0
          · subst n
            simp only [Nat.zero_div, Nat.cast_zero, zero_mul]
            exact mul_nonneg
              (div_nonneg (by norm_num)
                (show (0 : ℚ) ≤ (q : ℚ) by exact_mod_cast hq.le))
              (div_nonneg (by norm_num)
                (show (0 : ℚ) ≤ (qs.prod : ℚ) by exact_mod_cast hprod.le))
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hdiv : ((n / q : ℕ) : ℚ) ≤ (n : ℚ) / q := by
              apply (le_div_iff₀ (by exact_mod_cast hq)).2
              exact_mod_cast Nat.div_mul_le_self n q
            have hnR : (0 : ℚ) < n := by exact_mod_cast hnpos
            have hqR : (0 : ℚ) < q := by exact_mod_cast hq
            have hratio : ((n / q : ℕ) : ℚ) * (1 / (n : ℚ)) ≤ 1 / (q : ℚ) := by
              calc
                ((n / q : ℕ) : ℚ) * (1 / (n : ℚ)) ≤
                    ((n : ℚ) / q) * (1 / (n : ℚ)) :=
                  mul_le_mul_of_nonneg_right hdiv (by positivity)
                _ = 1 / (q : ℚ) := by field_simp
            calc
              ((n / q : ℕ) : ℚ) * ((1 / (n : ℚ)) * (1 / (qs.prod : ℚ))) =
                  (((n / q : ℕ) : ℚ) * (1 / (n : ℚ))) * (1 / (qs.prod : ℚ)) := by ring
              _ ≤ (1 / (q : ℚ)) * (1 / (qs.prod : ℚ)) :=
                mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = 1 / ((q :: qs).prod : ℚ) := by
          simp only [List.prod_cons, Nat.cast_mul]
          field_simp

/-! ## Exposed lists and complete cycle types -/

/-- The distinct list orderings of a multiset. -/
def multisetArrangements (mu : Multiset ℕ) : Finset (List ℕ) :=
  mu.toList.permutations.toFinset

@[simp] theorem mem_multisetArrangements {mu : Multiset ℕ} {xs : List ℕ} :
    xs ∈ multisetArrangements mu ↔ (xs : Multiset ℕ) = mu := by
  simp only [multisetArrangements, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact (Multiset.coe_eq_coe.mpr h).trans (Multiset.coe_toList mu)
  · intro h
    exact Multiset.coe_eq_coe.mp (h.trans (Multiset.coe_toList mu).symm)

theorem mem_multisetArrangements_length {mu : Multiset ℕ} {xs : List ℕ}
    (hxs : xs ∈ multisetArrangements mu) : xs.length = mu.card := by
  exact congrArg Multiset.card (mem_multisetArrangements.mp hxs)

theorem mem_multisetArrangements_sum {mu : Multiset ℕ} {xs : List ℕ}
    (hxs : xs ∈ multisetArrangements mu) : xs.sum = mu.sum := by
  exact congrArg Multiset.sum (mem_multisetArrangements.mp hxs)

theorem mem_multisetArrangements_pos {mu : Multiset ℕ} {xs : List ℕ}
    (hxs : xs ∈ multisetArrangements mu) (hpos : ∀ j ∈ mu, 0 < j) :
    ∀ j ∈ xs, 0 < j := by
  intro j hj
  exact hpos j (by
    rw [← mem_multisetArrangements.mp hxs]
    simpa using hj)

theorem multisetArrangements_subset_positiveCompositions
    {n ell : ℕ} {mu : Multiset ℕ}
    (hsum : mu.sum = n) (hcard : mu.card = ell)
    (hpos : ∀ j ∈ mu, 0 < j) :
    multisetArrangements mu ⊆ positiveCompositions n ell := by
  intro xs hxs
  rw [mem_positiveCompositions_iff]
  exact ⟨(mem_multisetArrangements_length hxs).trans hcard,
    (mem_multisetArrangements_sum hxs).trans hsum,
    mem_multisetArrangements_pos hxs hpos⟩

theorem multisetArrangements_eq_biUnion_erase {mu : Multiset ℕ}
    (hmu : mu ≠ 0) :
    multisetArrangements mu =
      mu.toFinset.biUnion fun j ↦
        (multisetArrangements (mu.erase j)).image (List.cons j) := by
  ext xs
  cases xs with
  | nil =>
      simp only [mem_multisetArrangements, Finset.mem_biUnion,
        Finset.mem_image]
      have hz : (0 : Multiset ℕ) ≠ mu := Ne.symm hmu
      simp [hz]
  | cons a xs =>
      simp only [mem_multisetArrangements,
        Finset.mem_biUnion, Finset.mem_image]
      constructor
      · intro h
        have ha : a ∈ mu := by rw [← h]; simp
        refine ⟨a, by simpa using ha, xs, ?_, rfl⟩
        rw [← h]
        simp
      · rintro ⟨j, hj, ys, hys, hcons⟩
        have hje : j ∈ mu := by simpa using hj
        rw [← hcons]
        change j ::ₘ (ys : Multiset ℕ) = mu
        rw [hys, Multiset.cons_erase hje]

theorem images_cons_pairwise_disjoint (mu : Multiset ℕ) :
    Set.Pairwise (mu.toFinset : Set ℕ) fun a b ↦
      Disjoint
        ((multisetArrangements (mu.erase a)).image (List.cons a))
        ((multisetArrangements (mu.erase b)).image (List.cons b)) := by
  intro a _ b _ hab
  rw [Finset.disjoint_left]
  rintro xs hxa hxb
  rw [Finset.mem_image] at hxa hxb
  obtain ⟨ys, _, rfl⟩ := hxa
  obtain ⟨zs, _, hzs⟩ := hxb
  have : a = b := by simpa using (congrArg List.head? hzs).symm
  exact hab this

/-- Splitting a complete cycle type according to the first exposed cycle
turns its cycle-index weight into decrement-chain weights. -/
theorem sum_decrementWeight_multisetArrangements (mu : Multiset ℕ)
    (hpos : ∀ j ∈ mu, 0 < j) :
    ∑ xs ∈ multisetArrangements mu, decrementWeight mu.sum xs =
      completeCycleWeight mu := by
  induction hcard : mu.card using Nat.strong_induction_on generalizing mu with
  | h k ih =>
      by_cases hmu : mu = 0
      · subst mu
        simp [multisetArrangements, decrementWeight, completeCycleWeight,
          completeCycleDenominator]
      · have hsumpos : 0 < mu.sum := by
          obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hmu
          exact (hpos j hj).trans_le (Multiset.le_sum_of_mem hj)
        rw [multisetArrangements_eq_biUnion_erase hmu]
        rw [Finset.sum_biUnion (images_cons_pairwise_disjoint mu)]
        have himage (j : ℕ) :
            (∑ xs ∈ (multisetArrangements (mu.erase j)).image (List.cons j),
                decrementWeight mu.sum xs) =
              ∑ xs ∈ multisetArrangements (mu.erase j),
                decrementWeight mu.sum (j :: xs) := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact (List.cons.inj hab).2
        simp_rw [himage]
        calc
            (∑ j ∈ mu.toFinset,
                ∑ xs ∈ multisetArrangements (mu.erase j),
                  decrementWeight mu.sum (j :: xs)) =
                ∑ j ∈ mu.toFinset,
                  (1 / (mu.sum : ℚ)) * completeCycleWeight (mu.erase j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjmu : j ∈ mu := by simpa using hj
              have hsum : mu.sum - j = (mu.erase j).sum := by
                rw [← Multiset.cons_erase hjmu]
                simp
              simp_rw [decrementWeight, hsum, ← Finset.mul_sum]
              rw [ih (mu.erase j).card]
              · have hkpos : 0 < k := by
                  rw [← hcard, Multiset.card_pos]
                  exact hmu
                rw [Multiset.card_erase_of_mem hjmu, hcard]
                exact Nat.pred_lt hkpos.ne'
              · intro a ha
                exact hpos a (Multiset.mem_of_mem_erase ha)
              · rfl
            _ = (1 / (mu.sum : ℚ)) *
                  ∑ j ∈ mu.toFinset, completeCycleWeight (mu.erase j) := by
              rw [Finset.mul_sum]
            _ = completeCycleWeight mu := by
              rw [sum_completeCycleWeight_erase mu hpos]
              have hs : (mu.sum : ℚ) ≠ 0 := by exact_mod_cast hsumpos.ne'
              field_simp

/-- Exposed cycle-length lists with exactly `ell` parts and lcm divisible
by `m`. -/
def multipleOrderCompositions (n m ell : ℕ) : Finset (List ℕ) :=
  (positiveCompositions n ell).filter fun xs ↦ m ∣ (xs : Multiset ℕ).lcm

/-- The same lists, first presented as the disjoint union of the list
arrangements of integer partitions. -/
def partitionArrangementEvent (n m ell : ℕ) : Finset (List ℕ) :=
  (Finset.univ : Finset (Nat.Partition n)).biUnion fun p ↦
    if p.parts.card = ell ∧ m ∣ p.parts.lcm then
      multisetArrangements p.parts
    else ∅

theorem partitionArrangementEvent_pairwise (n m ell : ℕ) :
    ((↑(Finset.univ : Finset (Nat.Partition n))) : Set (Nat.Partition n)).PairwiseDisjoint fun p ↦
        (if p.parts.card = ell ∧ m ∣ p.parts.lcm then
          multisetArrangements p.parts else ∅) := by
  intro p _ q _ hpq
  change Disjoint
    (if p.parts.card = ell ∧ m ∣ p.parts.lcm then
      multisetArrangements p.parts else ∅)
    (if q.parts.card = ell ∧ m ∣ q.parts.lcm then
      multisetArrangements q.parts else ∅)
  by_cases hp : p.parts.card = ell ∧ m ∣ p.parts.lcm
  · by_cases hq : q.parts.card = ell ∧ m ∣ q.parts.lcm
    · rw [if_pos hp, if_pos hq]
      rw [Finset.disjoint_left]
      intro xs hxp hxq
      apply hpq
      apply Nat.Partition.ext
      exact (mem_multisetArrangements.mp hxp).symm.trans
        (mem_multisetArrangements.mp hxq)
    · rw [if_pos hp, if_neg hq]
      simp
  · rw [if_neg hp]
    simp

theorem partitionArrangementEvent_eq (n m ell : ℕ) :
    partitionArrangementEvent n m ell = multipleOrderCompositions n m ell := by
  ext xs
  rw [partitionArrangementEvent, Finset.mem_biUnion]
  rw [multipleOrderCompositions, Finset.mem_filter,
    mem_positiveCompositions_iff]
  constructor
  · rintro ⟨p, _, hxs⟩
    by_cases hp : p.parts.card = ell ∧ m ∣ p.parts.lcm
    · rw [if_pos hp] at hxs
      have heq := mem_multisetArrangements.mp hxs
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact (congrArg Multiset.card heq).trans hp.1
      · exact (congrArg Multiset.sum heq).trans p.parts_sum
      · intro j hj
        exact p.parts_pos (by rw [← heq]; simpa using hj)
      · rw [heq]
        exact hp.2
    · simp [hp] at hxs
  · rintro ⟨⟨hlen, hsum, hpos⟩, hlcm⟩
    let p : Nat.Partition n :=
      { parts := (xs : Multiset ℕ)
        parts_pos := fun hi ↦ hpos _ (by simpa using hi)
        parts_sum := by simpa using hsum }
    refine ⟨p, Finset.mem_univ _, ?_⟩
    have hp : p.parts.card = ell ∧ m ∣ p.parts.lcm := by
      exact ⟨by simpa [p] using hlen, by simpa [p] using hlcm⟩
    rw [if_pos hp, mem_multisetArrangements]

/-- Exact composition expansion of the probability of having `ell` cycles
and order divisible by `m`. -/
theorem completeCycleTypeMass_multiple_eq_compositions (n m ell : ℕ) :
    completeCycleTypeMass n
        (fun mu ↦ mu.card = ell ∧ m ∣ mu.lcm) =
      ∑ xs ∈ multipleOrderCompositions n m ell, decrementWeight n xs := by
  classical
  rw [completeCycleTypeMass]
  calc
    (∑ p : Nat.Partition n,
        if p.parts.card = ell ∧ m ∣ p.parts.lcm then
          completeCycleWeight p.parts else 0) =
        ∑ p : Nat.Partition n,
          ∑ xs ∈ (if p.parts.card = ell ∧ m ∣ p.parts.lcm then
              multisetArrangements p.parts else ∅), decrementWeight n xs := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.parts.card = ell ∧ m ∣ p.parts.lcm
      · rw [if_pos hp, if_pos hp]
        simpa only [p.parts_sum] using
          (sum_decrementWeight_multisetArrangements p.parts
            (fun j hj ↦ p.parts_pos hj)).symm
      · rw [if_neg hp, if_neg hp]
        simp
    _ = ∑ xs ∈ partitionArrangementEvent n m ell, decrementWeight n xs := by
      rw [partitionArrangementEvent,
        Finset.sum_biUnion (partitionArrangementEvent_pairwise n m ell)]
    _ = ∑ xs ∈ multipleOrderCompositions n m ell, decrementWeight n xs := by
      rw [partitionArrangementEvent_eq]

/-! ## Maximal prime-power factors -/

/-- The maximal prime-power divisors of `m`, in an arbitrary list order. -/
def maximalPrimePowerFactors (m : ℕ) : List ℕ :=
  m.primeFactors.toList.map fun p ↦ p ^ m.factorization p

@[simp] theorem length_maximalPrimePowerFactors (m : ℕ) :
    (maximalPrimePowerFactors m).length = m.primeFactors.card := by
  simp [maximalPrimePowerFactors]

theorem prod_maximalPrimePowerFactors {m : ℕ} (hm : 0 < m) :
    (maximalPrimePowerFactors m).prod = m := by
  simpa [maximalPrimePowerFactors] using
    (Nat.prod_primeFactors_pow_factorization hm.ne').symm

theorem maximalPrimePowerFactors_pairwise_coprime (m : ℕ) :
    (maximalPrimePowerFactors m).Pairwise Nat.Coprime := by
  rw [maximalPrimePowerFactors, List.pairwise_map]
  apply m.primeFactors.nodup_toList.pairwise_of_forall_ne
  intro p hp q hq hpq
  exact Nat.coprime_pow_primes _ _
    (Nat.prime_of_mem_primeFactors (by simpa using hp))
    (Nat.prime_of_mem_primeFactors (by simpa using hq)) hpq

theorem mem_maximalPrimePowerFactors_iff {m q : ℕ} :
    q ∈ maximalPrimePowerFactors m ↔
      ∃ p ∈ m.primeFactors, p ^ m.factorization p = q := by
  simp [maximalPrimePowerFactors]

theorem maximalPrimePowerFactors_pos {m q : ℕ}
    (hq : q ∈ maximalPrimePowerFactors m) : 0 < q := by
  obtain ⟨p, hp, rfl⟩ := mem_maximalPrimePowerFactors_iff.mp hq
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

theorem prime_pow_dvd_positive_multiset_lcm_iff {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (mu : Multiset ℕ) (hmu : ∀ x ∈ mu, 0 < x) :
    p ^ a ∣ mu.lcm ↔ ∃ x ∈ mu, p ^ a ∣ x := by
  induction mu using Multiset.induction_on with
  | empty =>
      constructor
      · intro h
        have hone : p ^ a = 1 := Nat.dvd_one.mp (by simpa using h)
        exact ((Nat.one_lt_pow ha.ne' hp.one_lt).ne' hone).elim
      · simp
  | @cons x mu ih =>
      have hx : x ≠ 0 := (hmu x (by simp)).ne'
      have hrest : ∀ y ∈ mu, 0 < y := by
        intro y hy
        exact hmu y (by simp [hy])
      have hlcm : mu.lcm ≠ 0 := by
        rw [Ne, Multiset.lcm_eq_zero_iff]
        intro hz
        exact (hrest 0 hz).ne' rfl
      rw [Multiset.lcm_cons]
      constructor
      · intro hdiv
        have hval := (hp.pow_dvd_iff_le_factorization
          (Nat.lcm_ne_zero hx hlcm)).mp hdiv
        rw [Nat.factorization_lcm hx hlcm] at hval
        change a ≤ max (x.factorization p) (mu.lcm.factorization p) at hval
        rw [le_max_iff] at hval
        rcases hval with hxval | hmval
        · exact ⟨x, by simp,
            (hp.pow_dvd_iff_le_factorization hx).mpr hxval⟩
        · obtain ⟨y, hy, hydiv⟩ := (ih hrest).mp
            ((hp.pow_dvd_iff_le_factorization hlcm).mpr hmval)
          exact ⟨y, by simp [hy], hydiv⟩
      · rintro ⟨y, hy, hydiv⟩
        have hval :
            a ≤ max (x.factorization p) (mu.lcm.factorization p) := by
          rw [le_max_iff]
          rcases (by simpa using hy : y = x ∨ y ∈ mu) with rfl | hy
          · exact Or.inl ((hp.pow_dvd_iff_le_factorization hx).mp hydiv)
          · exact Or.inr ((hp.pow_dvd_iff_le_factorization hlcm).mp
              ((ih hrest).mpr ⟨y, hy, hydiv⟩))
        apply (hp.pow_dvd_iff_le_factorization
          (Nat.lcm_ne_zero hx hlcm)).mpr
        rw [Nat.factorization_lcm hx hlcm]
        exact hval

theorem maximalPrimePowerFactor_dvd {m p : ℕ} (hp : p ∈ m.primeFactors) :
    p ^ m.factorization p ∣ m := by
  apply (Nat.Prime.pow_dvd_iff_le_factorization (n := m)
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2).mpr
  exact le_rfl

theorem maximalPrimePowerFactors_dvd_some_of_dvd_lcm
    {m : ℕ} (hm : 0 < m) {mu : Multiset ℕ}
    (hmu : ∀ x ∈ mu, 0 < x) (hmlcm : m ∣ mu.lcm) :
    ∀ q ∈ maximalPrimePowerFactors m, ∃ x ∈ mu, q ∣ x := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_maximalPrimePowerFactors_iff.mp hq
  apply (prime_pow_dvd_positive_multiset_lcm_iff
    (Nat.prime_of_mem_primeFactors hp)
    ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm.ne'
      (Nat.dvd_of_mem_primeFactors hp)) mu hmu).mp
  exact (maximalPrimePowerFactor_dvd hp).trans hmlcm

/-! ## Assigning factors to exposed positions -/

/-- Group the entries of `factors` according to the exposed-cycle position
chosen by `assignment`.  Empty fibers contribute `1`. -/
def assignedDivisors (factors : List ℕ) (ell : ℕ)
    (assignment : Fin factors.length → Fin ell) : List ℕ :=
  List.ofFn fun i : Fin ell ↦
    ∏ a ∈ (Finset.univ : Finset (Fin factors.length)).filter
      (fun a ↦ assignment a = i), factors.get a

@[simp] theorem length_assignedDivisors (factors : List ℕ) (ell : ℕ)
    (assignment : Fin factors.length → Fin ell) :
    (assignedDivisors factors ell assignment).length = ell := by
  simp [assignedDivisors]

theorem prod_assignedDivisors (factors : List ℕ) (ell : ℕ)
    (assignment : Fin factors.length → Fin ell) :
    (assignedDivisors factors ell assignment).prod = factors.prod := by
  rw [assignedDivisors, List.prod_ofFn]
  rw [Finset.prod_fiberwise (Finset.univ : Finset (Fin factors.length))
    assignment factors.get]
  simpa using (List.prod_ofFn factors.get).symm

theorem assignedDivisors_pos {factors : List ℕ} {ell : ℕ}
    {assignment : Fin factors.length → Fin ell}
    (hpos : ∀ q ∈ factors, 0 < q) :
    ∀ q ∈ assignedDivisors factors ell assignment, 0 < q := by
  rw [assignedDivisors, List.forall_mem_ofFn_iff]
  intro i
  exact Finset.prod_pos fun a ha ↦ hpos _ (List.get_mem factors a)

theorem pairwise_get_coprime {factors : List ℕ}
    (hpair : factors.Pairwise Nat.Coprime) {a b : Fin factors.length}
    (hab : a ≠ b) : Nat.Coprime (factors.get a) (factors.get b) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact List.pairwise_iff_get.mp hpair a b hab
  · exact Nat.coprime_comm.mp (List.pairwise_iff_get.mp hpair b a hba)

theorem finset_prod_get_dvd_of_pairwise {factors : List ℕ}
    (hpair : factors.Pairwise Nat.Coprime) {s : Finset (Fin factors.length)}
    {x : ℕ} (hdvd : ∀ a ∈ s, factors.get a ∣ x) :
    ∏ a ∈ s, factors.get a ∣ x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro b hb
        exact pairwise_get_coprime hpair (by
          intro hab
          subst b
          exact ha hb)
      · exact hdvd a (Finset.mem_insert_self a s)
      · exact ih fun b hb ↦ hdvd b (Finset.mem_insert_of_mem hb)

theorem assignedDivisor_dvd_of_factors_dvd
    {factors xs : List ℕ} {ell : ℕ}
    (hpair : factors.Pairwise Nat.Coprime)
    (hlen : xs.length = ell)
    (assignment : Fin factors.length → Fin ell)
    (hdvd : ∀ a : Fin factors.length,
      factors.get a ∣ xs.get (Fin.cast hlen.symm (assignment a))) :
    List.Forall₂ (· ∣ ·) (assignedDivisors factors ell assignment) xs := by
  rw [assignedDivisors]
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hlen], ?_⟩
  intro i hiAssigned hiXs
  rw [List.get_ofFn]
  apply finset_prod_get_dvd_of_pairwise hpair
  intro a ha
  rw [Finset.mem_filter] at ha
  have hassignment : assignment a = ⟨i, by simpa using hiAssigned⟩ := ha.2
  simpa [hassignment] using hdvd a

theorem exists_assignment_for_multiple_composition {n m ell : ℕ}
    (hm : 0 < m) {xs : List ℕ}
    (hxs : xs ∈ multipleOrderCompositions n m ell) :
    ∃ assignment : Fin (maximalPrimePowerFactors m).length → Fin ell,
      List.Forall₂ (· ∣ ·)
        (assignedDivisors (maximalPrimePowerFactors m) ell assignment) xs := by
  rw [multipleOrderCompositions, Finset.mem_filter,
    mem_positiveCompositions_iff] at hxs
  rcases hxs with ⟨⟨hlen, hsum, hpos⟩, hmlcm⟩
  have hloc (a : Fin (maximalPrimePowerFactors m).length) :
      ∃ i : Fin xs.length, (maximalPrimePowerFactors m).get a ∣ xs.get i := by
    obtain ⟨x, hx, hdiv⟩ := maximalPrimePowerFactors_dvd_some_of_dvd_lcm hm
      (mu := (xs : Multiset ℕ))
      (by intro y hy; exact hpos y (by simpa using hy)) hmlcm
      ((maximalPrimePowerFactors m).get a)
      (List.get_mem _ _)
    have hxlist : x ∈ xs := by simpa using hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxlist
    exact ⟨i, hi.symm ▸ hdiv⟩
  choose position hposition using hloc
  let assignment : Fin (maximalPrimePowerFactors m).length → Fin ell :=
    fun a ↦ Fin.cast hlen (position a)
  refine ⟨assignment, assignedDivisor_dvd_of_factors_dvd
    (maximalPrimePowerFactors_pairwise_coprime m) hlen assignment ?_⟩
  intro a
  simpa [assignment] using hposition a

theorem assigned_composition_mass_le_inv {n m ell : ℕ} (hm : 0 < m)
    (assignment : Fin (maximalPrimePowerFactors m).length → Fin ell) :
    (∑ xs ∈ positiveCompositions n ell,
        if List.Forall₂ (· ∣ ·)
          (assignedDivisors (maximalPrimePowerFactors m) ell assignment) xs
        then decrementWeight n xs else 0) ≤ 1 / (m : ℚ) := by
  let qs := assignedDivisors (maximalPrimePowerFactors m) ell assignment
  have hlen : qs.length = ell := length_assignedDivisors _ _ _
  have hqpos : ∀ q ∈ qs, 0 < q :=
    assignedDivisors_pos fun q hq ↦ maximalPrimePowerFactors_pos hq
  calc
    (∑ xs ∈ positiveCompositions n ell,
        if List.Forall₂ (· ∣ ·) qs xs then decrementWeight n xs else 0) =
        constrainedDecrementMass n qs := by
      rw [constrainedDecrementMass_eq_sum, hlen]
    _ ≤ 1 / (qs.prod : ℚ) := constrainedDecrementMass_le_inv_prod hqpos
    _ = 1 / (m : ℚ) := by
      rw [prod_assignedDivisors, prod_maximalPrimePowerFactors hm]

/-- Beker's prime-power assignment estimate in exact rational form. -/
theorem multipleOrderCompositionMass_le {n m ell : ℕ} (hm : 0 < m) :
    (∑ xs ∈ multipleOrderCompositions n m ell, decrementWeight n xs) ≤
      (ell ^ (maximalPrimePowerFactors m).length : ℕ) / (m : ℚ) := by
  let factors := maximalPrimePowerFactors m
  let assignments := Fin factors.length → Fin ell
  let contribution (assignment : assignments) (xs : List ℕ) : ℚ :=
    if List.Forall₂ (· ∣ ·) (assignedDivisors factors ell assignment) xs then
      decrementWeight n xs else 0
  calc
    (∑ xs ∈ multipleOrderCompositions n m ell, decrementWeight n xs) ≤
        ∑ xs ∈ multipleOrderCompositions n m ell,
          ∑ assignment : assignments, contribution assignment xs := by
      apply Finset.sum_le_sum
      intro xs hxs
      obtain ⟨assignment, hassignment⟩ :=
        exists_assignment_for_multiple_composition hm hxs
      have hterm : contribution assignment xs = decrementWeight n xs := by
        simp [contribution, factors, hassignment]
      rw [← hterm]
      have hnonneg (a : assignments) : 0 ≤ contribution a xs := by
        dsimp [contribution]
        split <;> simp [decrementWeight_nonneg]
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun a : assignments ↦ contribution a xs)
        (fun a _ ↦ hnonneg a)
        (Finset.mem_univ assignment)
    _ ≤ ∑ xs ∈ positiveCompositions n ell,
          ∑ assignment : assignments, contribution assignment xs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro xs hxs hnot
      exact Finset.sum_nonneg fun assignment _ ↦ by
        unfold contribution
        split <;> simp [decrementWeight_nonneg]
    _ = ∑ assignment : assignments, ∑ xs ∈ positiveCompositions n ell,
          contribution assignment xs := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _assignment : assignments, (1 / (m : ℚ)) := by
      apply Finset.sum_le_sum
      intro assignment _
      simpa [contribution, factors] using
        assigned_composition_mass_le_inv (n := n) (ell := ell) hm assignment
    _ = (ell ^ (maximalPrimePowerFactors m).length : ℕ) / (m : ℚ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]
      have hcard : Fintype.card assignments = ell ^ (maximalPrimePowerFactors m).length := by
        simp [assignments, factors]
      rw [hcard]
      push_cast
      ring

/-! ## The permutation-count form of Beker's lemma -/

theorem completeCycleTypeMass_multiple_eq_cycleOrderMultipleProbability
    (n m ell : ℕ) :
    completeCycleTypeMass n (fun mu ↦ mu.card = ell ∧ m ∣ mu.lcm) =
      (cycleOrderMultipleCount n m ell : ℚ) / (n.factorial : ℚ) := by
  rw [completeCycleTypeMass_eq_cycleTypeEventProbability]
  have hcount :
      cycleTypeEventCount n
          (fun mu ↦ (completeCycleType n mu).card = ell ∧
            m ∣ (completeCycleType n mu).lcm) =
        cycleOrderMultipleCount n m ell := by
    unfold cycleTypeEventCount cycleOrderMultipleCount
    apply congrArg Finset.card
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have htype : completeCycleType n σ.cycleType = fullCycleType σ := by
      simp [completeCycleType, fullCycleType, fixedPointCount_eq]
    rw [htype, lcm_fullCycleType]
    simp [totalCycleCount, and_comm]
  rw [hcount]

/-- Beker's Lemma 2.5: among permutations with exactly `ell` cycles, the
probability that the order is divisible by `m` is at most
`ell ^ ω(m) / m`. -/
theorem cycleOrderMultipleProbability_le {n m ell : ℕ} (hm : 0 < m) :
    (cycleOrderMultipleCount n m ell : ℚ) / (n.factorial : ℚ) ≤
      (ell : ℚ) ^ distinctPrimeFactorCount m / (m : ℚ) := by
  rw [← completeCycleTypeMass_multiple_eq_cycleOrderMultipleProbability]
  rw [completeCycleTypeMass_multiple_eq_compositions]
  simpa [distinctPrimeFactorCount, length_maximalPrimePowerFactors,
    Nat.cast_pow] using (multipleOrderCompositionMass_le (n := n) (ell := ell) hm)

/-- Exact order is a subevent of the divisible-order event. -/
theorem cycleOrderProbability_le {n m ell : ℕ} (hm : 0 < m) :
    (cycleOrderCount n m ell : ℚ) / (n.factorial : ℚ) ≤
      (ell : ℚ) ^ distinctPrimeFactorCount m / (m : ℚ) := by
  calc
    (cycleOrderCount n m ell : ℚ) / (n.factorial : ℚ) ≤
        (cycleOrderMultipleCount n m ell : ℚ) / (n.factorial : ℚ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast cycleOrderCount_le_cycleOrderMultipleCount n m ell
      · positivity
    _ ≤ (ell : ℚ) ^ distinctPrimeFactorCount m / (m : ℚ) :=
      cycleOrderMultipleProbability_le hm

end

end Erdos1161
