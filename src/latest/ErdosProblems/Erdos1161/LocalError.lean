import ErdosProblems.Erdos1161.LocalEstimate
import ErdosProblems.Erdos1161.ExceptionalHalf
import ErdosProblems.Erdos1161.CycleRecursion
import ErdosProblems.Erdos1161.DivisorBounds
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The uniform local cycle-index error in Erdős Problem 1161

This file proves the analytic input in Beker's local estimate.  The first
lemmas separate the already-computed contribution of a complementary
`(n-r)`-cycle from the finite sum over the remaining cycle types.  Subsequent
lemmas isolate the exceptional pair of half-cycles and bound every other
cycle type uniformly over admissible remainders.
-/

namespace Erdos1161

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Marking a part of a full cycle partition -/

/-- Centralizer denominator of a full cycle partition, including its
one-parts. -/
def localCompleteCycleDenominator (mu : Multiset ℕ) : ℕ :=
  mu.prod * ∏ j ∈ mu.toFinset, (mu.count j).factorial

/-- Complete cycle-index weight of a full cycle partition. -/
def localCompleteCycleWeight (mu : Multiset ℕ) : ℚ :=
  1 / (localCompleteCycleDenominator mu : ℚ)

theorem localCompleteCycleDenominator_cons (j : ℕ) (mu : Multiset ℕ) :
    localCompleteCycleDenominator (j ::ₘ mu) =
      j * (mu.count j + 1) * localCompleteCycleDenominator mu := by
  classical
  unfold localCompleteCycleDenominator
  by_cases hj : j ∈ mu
  · have hjf : j ∈ mu.toFinset := by simpa
    rw [Multiset.toFinset_cons, Finset.insert_eq_of_mem hjf]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hjf]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hjf]
    simp only [Multiset.prod_cons, Multiset.count_cons_self]
    have hcounts : ∀ a ∈ mu.toFinset \ {j},
        (j ::ₘ mu).count a = mu.count a := by
      intro a ha
      exact Multiset.count_cons_of_ne (by
        simpa using (Finset.mem_sdiff.mp ha).2) mu
    rw [Finset.prod_congr rfl fun a ha ↦
      congrArg Nat.factorial (hcounts a ha)]
    rw [Nat.factorial_succ]
    ring
  · have hjf : j ∉ mu.toFinset := by simpa
    rw [Multiset.toFinset_cons, Finset.prod_insert hjf]
    simp only [Multiset.prod_cons, Multiset.count_cons_self,
      Multiset.count_eq_zero.mpr hj, zero_add]
    have hcounts : ∀ a ∈ mu.toFinset,
        (j ::ₘ mu).count a = mu.count a := by
      intro a ha
      exact Multiset.count_cons_of_ne (by
        intro h
        subst a
        exact hjf ha) mu
    rw [Finset.prod_congr rfl fun a ha ↦
      congrArg Nat.factorial (hcounts a ha)]
    norm_num
    ring

theorem localCompleteCycleDenominator_erase {j : ℕ} {mu : Multiset ℕ}
    (hj : j ∈ mu) :
    localCompleteCycleDenominator mu =
      j * mu.count j * localCompleteCycleDenominator (mu.erase j) := by
  nth_rewrite 1 [← Multiset.cons_erase hj]
  rw [localCompleteCycleDenominator_cons]
  have hc : 0 < mu.count j := Multiset.count_pos.mpr hj
  rw [Multiset.count_erase_self, Nat.sub_add_cancel hc]

theorem localCompleteCycleWeight_erase {j : ℕ} {mu : Multiset ℕ}
    (hj : j ∈ mu) (hpos : ∀ a ∈ mu, 0 < a) :
    localCompleteCycleWeight (mu.erase j) =
      (j * mu.count j : ℕ) * localCompleteCycleWeight mu := by
  have hden := localCompleteCycleDenominator_erase hj
  have herasePos : 0 < localCompleteCycleDenominator (mu.erase j) := by
    unfold localCompleteCycleDenominator
    have hprod : 0 < (mu.erase j).prod := by
      apply Multiset.prod_pos
      intro a ha
      exact hpos a (Multiset.mem_of_mem_erase ha)
    positivity
  have hcount : 0 < mu.count j := Multiset.count_pos.mpr hj
  unfold localCompleteCycleWeight
  rw [hden, Nat.cast_mul, Nat.cast_mul]
  have hjne : (j : ℚ) ≠ 0 := by exact_mod_cast (hpos j hj).ne'
  have hcne : (mu.count j : ℚ) ≠ 0 := by exact_mod_cast hcount.ne'
  have hene : (localCompleteCycleDenominator (mu.erase j) : ℚ) ≠ 0 := by
    exact_mod_cast herasePos.ne'
  push_cast
  field_simp

theorem sum_localCompleteCycleWeight_erase (mu : Multiset ℕ)
    (hpos : ∀ a ∈ mu, 0 < a) :
    ∑ j ∈ mu.toFinset, localCompleteCycleWeight (mu.erase j) =
      (mu.sum : ℚ) * localCompleteCycleWeight mu := by
  calc
    ∑ j ∈ mu.toFinset, localCompleteCycleWeight (mu.erase j) =
        ∑ j ∈ mu.toFinset,
          ((j * mu.count j : ℕ) : ℚ) * localCompleteCycleWeight mu := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [localCompleteCycleWeight_erase (by simpa using hj) hpos]
    _ = (∑ j ∈ mu.toFinset, ((j * mu.count j : ℕ) : ℚ)) *
        localCompleteCycleWeight mu := by
      rw [Finset.sum_mul]
    _ = (mu.sum : ℚ) * localCompleteCycleWeight mu := by
      have hsum : ∑ j ∈ mu.toFinset, j * mu.count j = mu.sum := by
        have h := (Finset.sum_multiset_map_count mu id).symm
        simp only [id_eq, nsmul_eq_mul, Nat.cast_id, mul_comm] at h
        simpa only [Multiset.map_id'] using h
      rw [show (∑ j ∈ mu.toFinset,
          ((j * mu.count j : ℕ) : ℚ)) = (mu.sum : ℚ) by
        exact_mod_cast hsum]

/-- Total complete-cycle-index mass of partitions of `n` satisfying `A`. -/
def localPartitionMass (n : ℕ) (A : Multiset ℕ → Prop)
    [DecidablePred A] : ℚ :=
  ∑ p : Nat.Partition n, if A p.parts then localCompleteCycleWeight p.parts else 0

theorem localPartitionMass_eq_completeCycleTypeMass
    (n : ℕ) (A : Multiset ℕ → Prop) [DecidablePred A] :
    localPartitionMass n A = completeCycleTypeMass n A := by
  rfl

/-- Exact distinguished-part recurrence for `localPartitionMass`. -/
theorem localPartitionMass_recursion (n : ℕ) (A : Multiset ℕ → Prop)
    [DecidablePred A] :
    (n : ℚ) * localPartitionMass n A =
      ∑ j ∈ Finset.Icc 1 n, ∑ q : Nat.Partition (n - j),
        if A (j ::ₘ q.parts) then localCompleteCycleWeight q.parts else 0 := by
  classical
  calc
    (n : ℚ) * localPartitionMass n A =
        ∑ p : Nat.Partition n, (n : ℚ) *
          (if A p.parts then localCompleteCycleWeight p.parts else 0) := by
      simp [localPartitionMass, Finset.mul_sum]
    _ = ∑ p : Nat.Partition n, ∑ j ∈ Finset.Icc 1 n,
          if j ∈ p.parts then
            (if A p.parts then localCompleteCycleWeight (p.parts.erase j) else 0)
          else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hA : A p.parts
      · simp only [hA, if_true]
        rw [← Finset.sum_filter]
        have hfilter :
            (Finset.Icc 1 n).filter (fun j ↦ j ∈ p.parts) =
              p.parts.toFinset := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_Icc,
            Multiset.mem_toFinset]
          constructor
          · exact fun h ↦ h.2
          · intro hj
            exact ⟨⟨p.parts_pos hj,
              (Multiset.le_sum_of_mem hj).trans_eq p.parts_sum⟩, hj⟩
        rw [hfilter]
        rw [show (n : ℚ) = (p.parts.sum : ℚ) by
          exact_mod_cast p.parts_sum.symm]
        exact (sum_localCompleteCycleWeight_erase p.parts
          (fun a ha ↦ p.parts_pos ha)).symm
      · simp [hA]
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
          if j ∈ p.parts then
            (if A p.parts then localCompleteCycleWeight (p.parts.erase j) else 0)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 n,
          ∑ p : {p : Nat.Partition n // j ∈ p.parts},
            if A p.1.parts then localCompleteCycleWeight (p.1.parts.erase j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ q : Nat.Partition (n - j),
          if A (j ::ₘ q.parts) then localCompleteCycleWeight q.parts else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      apply Fintype.sum_equiv
        (Nat.Partition.partitionWithPartEquiv hj'.1 hj'.2)
      intro p
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
      rw [Multiset.cons_erase p.2]

/-- Every part of `mu` belongs to the finite set `D`. -/
def AllPartsIn (D : Finset ℕ) (mu : Multiset ℕ) : Prop :=
  ∀ d ∈ mu, d ∈ D

instance (D : Finset ℕ) : DecidablePred (AllPartsIn D) :=
  fun mu ↦ by
    unfold AllPartsIn
    infer_instance

/-- Cycle-index mass of full cycle partitions all of whose parts lie in
`D`.  Fixed points are parts of length one here. -/
noncomputable def restrictedPartitionMass (D : Finset ℕ) (n : ℕ) : ℚ := by
  classical
  exact localPartitionMass n (AllPartsIn D)

theorem restrictedPartitionMass_nonneg (D : Finset ℕ) (n : ℕ) :
    0 ≤ restrictedPartitionMass D n := by
  unfold restrictedPartitionMass localPartitionMass
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · unfold localCompleteCycleWeight
    positivity
  · exact le_rfl

/-- Exact distinguished-cycle recursion for a restricted full-cycle mass. -/
theorem restrictedPartitionMass_recursion (D : Finset ℕ) {n : ℕ}
    (hn : 0 < n) :
    restrictedPartitionMass D n =
      (1 / (n : ℚ)) * ∑ j ∈ Finset.Icc 1 n,
        if j ∈ D then restrictedPartitionMass D (n - j) else 0 := by
  classical
  have hrec := localPartitionMass_recursion n (AllPartsIn D)
  have hrhs :
      (∑ j ∈ Finset.Icc 1 n, ∑ q : Nat.Partition (n - j),
        if AllPartsIn D (j ::ₘ q.parts) then localCompleteCycleWeight q.parts else 0) =
      ∑ j ∈ Finset.Icc 1 n,
        if j ∈ D then restrictedPartitionMass D (n - j) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ D
    · simp only [hj, if_true]
      unfold restrictedPartitionMass localPartitionMass AllPartsIn
      apply Finset.sum_congr rfl
      intro q _
      simp only [Multiset.mem_cons, forall_eq_or_imp]
      simp [hj]
    · simp only [hj, if_false]
      apply Finset.sum_eq_zero
      intro q _
      simp [AllPartsIn, hj]
  rw [hrhs] at hrec
  rw [restrictedPartitionMass]
  rw [one_div_mul_eq_div]
  exact (eq_div_iff (by exact_mod_cast hn.ne')).2 (by
    simpa [mul_comm] using hrec)

/-- A restricted cycle-index mass is a subprobability.  This proof uses only
the distinguished-cycle recurrence, so no measure-theoretic probability
space is needed. -/
theorem restrictedPartitionMass_le_one (D : Finset ℕ) (n : ℕ) :
    restrictedPartitionMass D n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp only [restrictedPartitionMass, localPartitionMass,
          localCompleteCycleWeight, localCompleteCycleDenominator,
          Fintype.sum_unique, Nat.cast_zero]
        split_ifs <;> norm_num
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [restrictedPartitionMass_recursion D hnpos]
        have hterm : ∀ j ∈ Finset.Icc 1 n,
            (if j ∈ D then restrictedPartitionMass D (n - j) else 0) ≤ 1 := by
          intro j hj
          split_ifs
          · apply ih
            exact Nat.sub_lt hnpos (Finset.mem_Icc.mp hj).1
          · norm_num
        have hsum :
            (∑ j ∈ Finset.Icc 1 n,
              if j ∈ D then restrictedPartitionMass D (n - j) else 0) ≤
              (n : ℚ) := by
          calc
            _ ≤ ∑ _j ∈ Finset.Icc 1 n, (1 : ℚ) := by
              exact Finset.sum_le_sum fun j hj ↦ hterm j hj
            _ = (n : ℚ) := by simp
        have hinv : 0 ≤ (1 / (n : ℚ)) := by positivity
        calc
          (1 / (n : ℚ)) *
              (∑ j ∈ Finset.Icc 1 n,
                if j ∈ D then restrictedPartitionMass D (n - j) else 0) ≤
              (1 / (n : ℚ)) * n :=
            mul_le_mul_of_nonneg_left hsum hinv
          _ = 1 := by field_simp

/-- One exposure of a distinguished cycle bounds restricted mass by the
number of allowed lengths divided by the degree. -/
theorem restrictedPartitionMass_le_card_div (D : Finset ℕ) {n : ℕ}
    (hn : 0 < n) :
    restrictedPartitionMass D n ≤ (D.card : ℚ) / n := by
  rw [restrictedPartitionMass_recursion D hn]
  have hsum :
      (∑ j ∈ Finset.Icc 1 n,
        if j ∈ D then restrictedPartitionMass D (n - j) else 0) ≤
        (D.card : ℚ) := by
    rw [← Finset.sum_filter]
    calc
      ∑ j ∈ (Finset.Icc 1 n).filter (fun j ↦ j ∈ D),
          restrictedPartitionMass D (n - j) ≤
          ∑ _j ∈ (Finset.Icc 1 n).filter (fun j ↦ j ∈ D),
            (1 : ℚ) := by
        exact Finset.sum_le_sum fun j _ ↦ restrictedPartitionMass_le_one D (n - j)
      _ = (((Finset.Icc 1 n).filter (fun j ↦ j ∈ D)).card : ℚ) := by simp
      _ ≤ (D.card : ℚ) := by
        exact_mod_cast Finset.card_le_card (fun j hj ↦ (Finset.mem_filter.mp hj).2)
  calc
    (1 / (n : ℚ)) *
        (∑ j ∈ Finset.Icc 1 n,
          if j ∈ D then restrictedPartitionMass D (n - j) else 0) ≤
        (1 / (n : ℚ)) * D.card :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (D.card : ℚ) / n := by field_simp

private theorem sum_Icc_if_mem_le_card_mul
    (D : Finset ℕ) (n : ℕ) (f : ℕ → ℚ) {B : ℚ}
    (hB : 0 ≤ B)
    (hf : ∀ j ∈ Finset.Icc 1 n, j ∈ D → f j ≤ B) :
    (∑ j ∈ Finset.Icc 1 n, if j ∈ D then f j else 0) ≤
      (D.card : ℚ) * B := by
  rw [← Finset.sum_filter]
  calc
    ∑ j ∈ (Finset.Icc 1 n).filter (fun j ↦ j ∈ D), f j ≤
        ∑ _j ∈ (Finset.Icc 1 n).filter (fun j ↦ j ∈ D), B := by
      apply Finset.sum_le_sum
      intro j hj
      exact hf j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    _ = (((Finset.Icc 1 n).filter (fun j ↦ j ∈ D)).card : ℚ) * B := by
      simp
    _ ≤ (D.card : ℚ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast Finset.card_le_card
        (fun j hj ↦ (Finset.mem_filter.mp hj).2)

/-- Two iterations of the distinguished-cycle recurrence with a uniform
lower bound on the residual degree. -/
theorem restrictedPartitionMass_le_card_sq_div
    (D : Finset ℕ) {n L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (hres : ∀ d ∈ Finset.Icc 1 n, d ∈ D → L ≤ n - d) :
    restrictedPartitionMass D n ≤
      (D.card : ℚ) ^ 2 / ((n : ℚ) * L) := by
  rw [restrictedPartitionMass_recursion D hn]
  have hcard : (0 : ℚ) ≤ D.card := by positivity
  have hB : (0 : ℚ) ≤ (D.card : ℚ) / L := by positivity
  have hterm : ∀ d ∈ Finset.Icc 1 n, d ∈ D →
      restrictedPartitionMass D (n - d) ≤ (D.card : ℚ) / L := by
    intro d hd hdD
    have hresNat := hres d hd hdD
    have hnd : 0 < n - d := hL.trans_le hresNat
    refine (restrictedPartitionMass_le_card_div D hnd).trans ?_
    have hresQ : (L : ℚ) ≤ ((n - d : ℕ) : ℚ) := by exact_mod_cast hresNat
    exact div_le_div_of_nonneg_left hcard (by positivity) hresQ
  have hsum := sum_Icc_if_mem_le_card_mul D n
    (fun d ↦ restrictedPartitionMass D (n - d)) hB hterm
  calc
    (1 / (n : ℚ)) *
        (∑ d ∈ Finset.Icc 1 n,
          if d ∈ D then restrictedPartitionMass D (n - d) else 0) ≤
        (1 / (n : ℚ)) * ((D.card : ℚ) * (D.card / L)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (D.card : ℚ) ^ 2 / ((n : ℚ) * L) := by field_simp

/-- Three recurrence iterations, with uniform lower bounds after the first
and second exposed cycle. -/
theorem restrictedPartitionMass_le_card_cube_div
    (D : Finset ℕ) {n L₁ L₂ : ℕ}
    (hn : 0 < n) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hres₁ : ∀ d ∈ Finset.Icc 1 n, d ∈ D → L₁ ≤ n - d)
    (hres₂ : ∀ d ∈ Finset.Icc 1 n, d ∈ D →
      ∀ e ∈ Finset.Icc 1 (n - d), e ∈ D → L₂ ≤ n - d - e) :
    restrictedPartitionMass D n ≤
      (D.card : ℚ) ^ 3 / ((n : ℚ) * L₁ * L₂) := by
  rw [restrictedPartitionMass_recursion D hn]
  have hcardSq : (0 : ℚ) ≤ (D.card : ℚ) ^ 2 := sq_nonneg _
  have hB : (0 : ℚ) ≤ (D.card : ℚ) ^ 2 / (L₁ * L₂) := by positivity
  have hterm : ∀ d ∈ Finset.Icc 1 n, d ∈ D →
      restrictedPartitionMass D (n - d) ≤
        (D.card : ℚ) ^ 2 / (L₁ * L₂) := by
    intro d hd hdD
    have hres₁Nat := hres₁ d hd hdD
    have hnd : 0 < n - d := hL₁.trans_le hres₁Nat
    have htwo := restrictedPartitionMass_le_card_sq_div D hnd hL₂
      (hres₂ d hd hdD)
    refine htwo.trans ?_
    have hres₁Q : (L₁ : ℚ) ≤ ((n - d : ℕ) : ℚ) := by exact_mod_cast hres₁Nat
    apply div_le_div_of_nonneg_left hcardSq (by positivity)
    exact mul_le_mul_of_nonneg_right hres₁Q (by positivity)
  have hsum := sum_Icc_if_mem_le_card_mul D n
    (fun d ↦ restrictedPartitionMass D (n - d)) hB hterm
  calc
    (1 / (n : ℚ)) *
        (∑ d ∈ Finset.Icc 1 n,
          if d ∈ D then restrictedPartitionMass D (n - d) else 0) ≤
        (1 / (n : ℚ)) *
          ((D.card : ℚ) * ((D.card : ℚ) ^ 2 / (L₁ * L₂))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (D.card : ℚ) ^ 3 / ((n : ℚ) * L₁ * L₂) := by
      field_simp

/-! ## Divisors other than the long and half-long lengths -/

/-- Positive divisors of `m`, with `m` and the possible half-divisor `m/2`
removed. -/
def reducedDivisors (m : ℕ) : Finset ℕ :=
  m.divisors.filter fun d ↦ d < m ∧ 2 * d ≠ m

@[simp] theorem mem_reducedDivisors {m d : ℕ} :
    d ∈ reducedDivisors m ↔ d ∣ m ∧ d < m ∧ 2 * d ≠ m := by
  by_cases hm : m = 0
  · subst m
    simp [reducedDivisors]
  · simp [reducedDivisors, hm, and_assoc]

theorem reducedDivisors_card_le_divisors_card (m : ℕ) :
    (reducedDivisors m).card ≤ m.divisors.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- A proper divisor other than `m/2` is at most `m/3`. -/
theorem three_mul_le_of_mem_reducedDivisors {m d : ℕ}
    (hm : 0 < m) (hd : d ∈ reducedDivisors m) :
    3 * d ≤ m := by
  rcases (mem_reducedDivisors.mp hd) with ⟨hdvd, hdlt, hdhalf⟩
  obtain ⟨k, rfl⟩ := hdvd
  have hdpos : 0 < d := by
    by_contra hdz
    simp only [Nat.not_lt, Nat.le_zero] at hdz
    subst d
    simp at hm
  have hk : 1 < k := by
    have : d * 1 < d * k := by simpa using hdlt
    exact (Nat.mul_lt_mul_left hdpos).mp this
  have hkne : k ≠ 2 := by
    intro hk2
    subst k
    apply hdhalf
    omega
  have hkthree : 3 ≤ k := by omega
  simpa [mul_comm, mul_left_comm] using Nat.mul_le_mul_left d hkthree

/-- Three-step bound for a full degree `m+r` using only reduced divisors. -/
theorem reducedDivisorMass_full_bound {m r : ℕ} (hm : 6 ≤ m) :
    restrictedPartitionMass (reducedDivisors m) (m + r) ≤
      ((reducedDivisors m).card : ℚ) ^ 3 /
        (((m + r : ℕ) : ℚ) * (m / 2 : ℕ) * (m / 6 : ℕ)) := by
  apply restrictedPartitionMass_le_card_cube_div
      (hn := by omega) (hL₁ := by omega) (hL₂ := by omega)
  · intro d hd hdD
    have hdsmall := three_mul_le_of_mem_reducedDivisors (by omega) hdD
    omega
  · intro d hd hdD e he heD
    have hdsmall := three_mul_le_of_mem_reducedDivisors (by omega) hdD
    have hesmall := three_mul_le_of_mem_reducedDivisors (by omega) heD
    omega

/-- Two-step bound at the residual degree after one half-cycle. -/
theorem reducedDivisorMass_half_bound {m h r : ℕ}
    (hm : 7 ≤ m) (hmh : m = 2 * h) (hr : 2 * r < m) :
    restrictedPartitionMass (reducedDivisors m) (h + r) ≤
      ((reducedDivisors m).card : ℚ) ^ 2 /
        (((h + r : ℕ) : ℚ) * (m / 7 : ℕ)) := by
  apply restrictedPartitionMass_le_card_sq_div
      (hn := by omega) (hL := by omega)
  intro d hd hdD
  have hdsmall := three_mul_le_of_mem_reducedDivisors (by omega) hdD
  omega

/-- Three recurrence exposures, with the integer-rounding losses absorbed
into the sharp constant `9/2`. -/
theorem restrictedPartitionMass_small_parts_full_bound
    (D : Finset ℕ) {m r : ℕ} (hm : 0 < m)
    (hsmall : ∀ d ∈ D, 3 * d ≤ m) :
    restrictedPartitionMass D (m + r) ≤
      9 * (D.card : ℚ) ^ 3 / (2 * (m : ℚ) ^ 3) := by
  let L₁ := m - m / 3
  let L₂ := m - 2 * (m / 3)
  have hmulDiv : 3 * (m / 3) ≤ m := Nat.mul_div_le m 3
  have hL₁pos : 0 < L₁ := by
    dsimp [L₁]
    omega
  have hL₂pos : 0 < L₂ := by
    dsimp [L₂]
    omega
  have hbase := restrictedPartitionMass_le_card_cube_div D
    (n := m + r) (L₁ := L₁) (L₂ := L₂)
    (by omega) hL₁pos hL₂pos
    (by
      intro d hd hdD
      have hdsmall := hsmall d hdD
      dsimp [L₁]
      omega)
    (by
      intro d hd hdD e he heD
      have hdsmall := hsmall d hdD
      have hesmall := hsmall e heD
      dsimp [L₂]
      omega)
  refine hbase.trans ?_
  have hL₁Nat : 2 * m ≤ 3 * L₁ := by
    dsimp [L₁]
    omega
  have hL₂Nat : m ≤ 3 * L₂ := by
    dsimp [L₂]
    omega
  have hnNat : m ≤ m + r := Nat.le_add_right m r
  have hL₁Q : (2 : ℚ) * m ≤ 3 * L₁ := by exact_mod_cast hL₁Nat
  have hL₂Q : (m : ℚ) ≤ 3 * L₂ := by exact_mod_cast hL₂Nat
  have hnQ : (m : ℚ) ≤ m + r := by exact_mod_cast hnNat
  have hab : (2 : ℚ) * m * m ≤ (3 * L₁) * (3 * L₂) :=
    mul_le_mul hL₁Q hL₂Q (by positivity) (by positivity)
  have hden : (2 : ℚ) * m ^ 3 ≤
      9 * (((m + r : ℕ) : ℚ) * L₁ * L₂) := by
    have h := mul_le_mul hnQ hab (by positivity) (by positivity)
    calc
      (2 : ℚ) * m ^ 3 = (m : ℚ) * (2 * m * m) := by ring
      _ ≤ ((m : ℚ) + r) * ((3 : ℚ) * L₁ * (3 * L₂)) := h
      _ = 9 * (((m + r : ℕ) : ℚ) * L₁ * L₂) := by
        push_cast
        ring
  have hden' : (2 / 9 : ℚ) * m ^ 3 ≤
      (((m + r : ℕ) : ℚ) * L₁ * L₂) := by
    nlinarith
  calc
    (D.card : ℚ) ^ 3 /
          (((m + r : ℕ) : ℚ) * L₁ * L₂) ≤
        (D.card : ℚ) ^ 3 / ((2 / 9 : ℚ) * m ^ 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden'
    _ = 9 * (D.card : ℚ) ^ 3 / (2 * (m : ℚ) ^ 3) := by
      field_simp

/-- Two recurrence exposures after removing one half-cycle. -/
theorem restrictedPartitionMass_small_parts_half_bound
    (D : Finset ℕ) {m h r : ℕ} (hm : 0 < m) (hmh : m = 2 * h)
    (_hr : 2 * r < m) (hsmall : ∀ d ∈ D, 3 * d ≤ m) :
    restrictedPartitionMass D (h + r) ≤
      12 * (D.card : ℚ) ^ 2 / (m : ℚ) ^ 2 := by
  let L := h - m / 3
  have hmulDiv : 3 * (m / 3) ≤ m := Nat.mul_div_le m 3
  have hLpos : 0 < L := by
    dsimp [L]
    omega
  have hbase := restrictedPartitionMass_le_card_sq_div D
    (n := h + r) (L := L) (by omega) hLpos
    (by
      intro d hd hdD
      have hdsmall := hsmall d hdD
      dsimp [L]
      omega)
  refine hbase.trans ?_
  have hnNat : m ≤ 2 * (h + r) := by omega
  have hLNat : m ≤ 6 * L := by
    dsimp [L]
    omega
  have hnQ : (m : ℚ) ≤ 2 * (h + r : ℕ) := by exact_mod_cast hnNat
  have hLQ : (m : ℚ) ≤ 6 * L := by exact_mod_cast hLNat
  have hden : (m : ℚ) ^ 2 ≤
      12 * (((h + r : ℕ) : ℚ) * L) := by
    have hmul := mul_le_mul hnQ hLQ (by positivity) (by positivity)
    nlinarith
  have hden' : (1 / 12 : ℚ) * m ^ 2 ≤
      (((h + r : ℕ) : ℚ) * L) := by
    nlinarith
  calc
    (D.card : ℚ) ^ 2 / (((h + r : ℕ) : ℚ) * L) ≤
        (D.card : ℚ) ^ 2 / ((1 / 12 : ℚ) * m ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden'
    _ = 12 * (D.card : ℚ) ^ 2 / (m : ℚ) ^ 2 := by
      field_simp

theorem reducedDivisorMass_full_sharp {m r : ℕ} (hm : 0 < m) :
    restrictedPartitionMass (reducedDivisors m) (m + r) ≤
      9 * ((reducedDivisors m).card : ℚ) ^ 3 /
        (2 * (m : ℚ) ^ 3) :=
  restrictedPartitionMass_small_parts_full_bound (reducedDivisors m) hm
    (fun _d hd ↦ three_mul_le_of_mem_reducedDivisors hm hd)

theorem reducedDivisorMass_half_sharp {m h r : ℕ} (hm : 0 < m)
    (hmh : m = 2 * h) (hr : 2 * r < m) :
    restrictedPartitionMass (reducedDivisors m) (h + r) ≤
      12 * ((reducedDivisors m).card : ℚ) ^ 2 / (m : ℚ) ^ 2 :=
  restrictedPartitionMass_small_parts_half_bound (reducedDivisors m)
    hm hmh hr (fun _d hd ↦ three_mul_le_of_mem_reducedDivisors hm hd)

/-! ## Rewriting the non-long contribution with full cycle partitions -/

def NonLongFullCycleEvent (m : ℕ) (mu : Multiset ℕ) : Prop :=
  mu.lcm = m ∧ m ∉ mu

instance (m : ℕ) : DecidablePred (NonLongFullCycleEvent m) :=
  fun mu ↦ by
    unfold NonLongFullCycleEvent
    infer_instance

private theorem lcm_replicate_one (k : ℕ) :
    (Multiset.replicate k 1).lcm = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [Multiset.replicate_succ, ih]

theorem lcm_completeCycleType {n : ℕ} {mu : Multiset ℕ}
    (_hmu : mu ∈ cycleTypes n) :
    (completeCycleType n mu).lcm = mu.lcm := by
  rw [completeCycleType, Multiset.lcm_add, lcm_replicate_one]
  simp

theorem mem_completeCycleType_iff_of_two_le {n m : ℕ}
    {mu : Multiset ℕ} (hm : 2 ≤ m) :
    m ∈ completeCycleType n mu ↔ m ∈ mu := by
  rw [completeCycleType, Multiset.mem_add]
  constructor
  · rintro (h | h)
    · exact h
    · rw [Multiset.mem_replicate] at h
      omega
  · exact Or.inl

/-- The rational non-long contribution is exactly the mass of full cycle
partitions of lcm `m` that contain no part `m`. -/
theorem nonLongCycleContribution_eq_localPartitionMass
    {n m : ℕ} (hm : 2 ≤ m) :
    nonLongCycleContribution n m =
      localPartitionMass n (NonLongFullCycleEvent m) := by
  rw [localPartitionMass_eq_completeCycleTypeMass,
    completeCycleTypeMass_eq_sum_cycleTypes]
  unfold nonLongCycleContribution nonLongOrderCycleTypes
  rw [← Finset.sum_filter]
  congr 1
  ext mu
  simp only [Finset.mem_filter, mem_orderCycleTypes]
  constructor
  · rintro ⟨⟨hvalid, hlcm⟩, hnot⟩
    exact ⟨hvalid, by
      simp [NonLongFullCycleEvent, lcm_completeCycleType hvalid,
        mem_completeCycleType_iff_of_two_le hm, hlcm, hnot]⟩
  · rintro ⟨hvalid, hevent⟩
    rw [NonLongFullCycleEvent, lcm_completeCycleType hvalid,
      mem_completeCycleType_iff_of_two_le hm] at hevent
    exact ⟨⟨hvalid, hevent.1⟩, hevent.2⟩

theorem localCompleteCycleWeight_cons_of_not_mem {h : ℕ}
    {mu : Multiset ℕ} (hh : 0 < h) (hnot : h ∉ mu)
    (hpos : ∀ a ∈ mu, 0 < a) :
    localCompleteCycleWeight (h ::ₘ mu) =
      (1 / (h : ℚ)) * localCompleteCycleWeight mu := by
  rw [localCompleteCycleWeight, localCompleteCycleWeight,
    localCompleteCycleDenominator_cons]
  have hden : 0 < localCompleteCycleDenominator mu := by
    unfold localCompleteCycleDenominator
    have : 0 < mu.prod := Multiset.prod_pos hpos
    positivity
  rw [Multiset.count_eq_zero.mpr hnot]
  norm_num
  field_simp

theorem localCompleteCycleWeight_cons_cons_of_not_mem {h : ℕ}
    {mu : Multiset ℕ} (hh : 0 < h) (hnot : h ∉ mu)
    (hpos : ∀ a ∈ mu, 0 < a) :
    localCompleteCycleWeight (h ::ₘ h ::ₘ mu) =
      (1 / (2 * (h : ℚ) ^ 2)) * localCompleteCycleWeight mu := by
  rw [localCompleteCycleWeight, localCompleteCycleWeight,
    localCompleteCycleDenominator_cons,
    localCompleteCycleDenominator_cons]
  have hden : 0 < localCompleteCycleDenominator mu := by
    unfold localCompleteCycleDenominator
    have : 0 < mu.prod := Multiset.prod_pos hpos
    positivity
  simp [Multiset.count_eq_zero.mpr hnot]
  field_simp

/-- Mass of full partitions with exactly one distinguished `h`-part and all
remaining parts reduced. -/
def oneHalfReducedMass (D : Finset ℕ) (n h : ℕ) : ℚ :=
  ∑ p : Nat.Partition n,
    if h ∈ p.parts then
      if p.parts.count h = 1 ∧ AllPartsIn D (p.parts.erase h) then
        localCompleteCycleWeight p.parts else 0
    else 0

/-- Removing the unique `h`-part factors its cycle-index weight by `1/h`. -/
theorem oneHalfReducedMass_eq {D : Finset ℕ} {n h : ℕ}
    (hh : 0 < h) (hhn : h ≤ n) :
    oneHalfReducedMass D n h =
      (1 / (h : ℚ)) * ∑ q : Nat.Partition (n - h),
        if h ∉ q.parts ∧ AllPartsIn D q.parts then
          localCompleteCycleWeight q.parts else 0 := by
  classical
  unfold oneHalfReducedMass
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv
    (Nat.Partition.partitionWithPartEquiv hh hhn)
  intro p
  rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
  have hpcons : h ::ₘ p.1.parts.erase h = p.1.parts :=
    Multiset.cons_erase p.2
  have hpos : ∀ a ∈ p.1.parts.erase h, 0 < a := by
    intro a ha
    exact p.1.parts_pos (Multiset.mem_of_mem_erase ha)
  by_cases hone : p.1.parts.count h = 1
  · have hnot : h ∉ p.1.parts.erase h := by
      intro hmem
      have hcpos := Multiset.count_pos.mpr hmem
      rw [Multiset.count_erase_self] at hcpos
      omega
    simp only [hone, true_and]
    simp only [hnot, not_false_eq_true, true_and]
    rw [← hpcons, localCompleteCycleWeight_cons_of_not_mem hh hnot hpos]
    simp [hnot]
  · have hmemErase : h ∈ p.1.parts.erase h := by
      rw [← Multiset.count_pos, Multiset.count_erase_self]
      have hcpos : 0 < p.1.parts.count h := Multiset.count_pos.mpr p.2
      omega
    simp [hone, hmemErase]

theorem oneHalfReducedMass_le {D : Finset ℕ} {n h : ℕ}
    (hh : 0 < h) (hhn : h ≤ n) :
    oneHalfReducedMass D n h ≤
      (1 / (h : ℚ)) * restrictedPartitionMass D (n - h) := by
  rw [oneHalfReducedMass_eq hh hhn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold restrictedPartitionMass localPartitionMass
  apply Finset.sum_le_sum
  intro q _
  split_ifs <;> simp_all
  unfold localCompleteCycleWeight
  positivity

/-- Exact mass of the order event with exactly two half-length parts. -/
def twoHalfOrderMass (n m h : ℕ) : ℚ :=
  ∑ p : Nat.Partition n,
    if h ∈ p.parts then
      if NonLongFullCycleEvent m p.parts ∧ p.parts.count h = 2 then
        localCompleteCycleWeight p.parts else 0
    else 0

private theorem mem_reducedDivisors_of_nonLongEvent_of_ne_half
    {m h d : ℕ} (hm : 0 < m) (hmh : m = 2 * h)
    {mu : Multiset ℕ} (hevent : NonLongFullCycleEvent m mu)
    (hd : d ∈ mu) (hdh : d ≠ h) : d ∈ reducedDivisors m := by
  rw [mem_reducedDivisors]
  have hdvd : d ∣ m := by
    rw [← hevent.1]
    exact Multiset.dvd_lcm hd
  have hdle : d ≤ m := Nat.le_of_dvd hm hdvd
  have hdne : d ≠ m := fun hdm ↦ hevent.2 (hdm ▸ hd)
  refine ⟨hdvd, lt_of_le_of_ne hdle hdne, ?_⟩
  omega

private theorem allPartsIn_reduced_of_count_half_zero
    {m h : ℕ} (hm : 0 < m) (hmh : m = 2 * h)
    {mu : Multiset ℕ} (hevent : NonLongFullCycleEvent m mu)
    (hcount : mu.count h = 0) : AllPartsIn (reducedDivisors m) mu := by
  intro d hd
  apply mem_reducedDivisors_of_nonLongEvent_of_ne_half hm hmh hevent hd
  intro hdh
  subst d
  exact (Multiset.count_pos.mpr hd).ne' hcount

private theorem allPartsIn_erase_reduced_of_count_half_one
    {m h : ℕ} (hm : 0 < m) (hmh : m = 2 * h)
    {mu : Multiset ℕ} (hevent : NonLongFullCycleEvent m mu)
    (hcount : mu.count h = 1) :
    AllPartsIn (reducedDivisors m) (mu.erase h) := by
  intro d hd
  have hdmu := Multiset.mem_of_mem_erase hd
  apply mem_reducedDivisors_of_nonLongEvent_of_ne_half hm hmh hevent hdmu
  intro hdh
  subst d
  have hcpos : 0 < (mu.erase h).count h := Multiset.count_pos.mpr hd
  rw [Multiset.count_erase_self, hcount] at hcpos
  omega

/-- Split every non-long type into zero, one, or two half-cycles. -/
theorem nonLongPartitionMass_le_reduced_add_one_add_two
    {m h r : ℕ} (hm : 0 < m) (hmh : m = 2 * h)
    (hr : 2 * r < m) :
    localPartitionMass (m + r) (NonLongFullCycleEvent m) ≤
      restrictedPartitionMass (reducedDivisors m) (m + r) +
        oneHalfReducedMass (reducedDivisors m) (m + r) h +
          twoHalfOrderMass (m + r) m h := by
  unfold restrictedPartitionMass oneHalfReducedMass twoHalfOrderMass
  unfold localPartitionMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  by_cases hevent : NonLongFullCycleEvent m p.parts
  · have hhpos : 0 < h := by omega
    have hcountle : p.parts.count h ≤ 2 := by
      have hsumle : p.parts.count h * h ≤ p.parts.sum := by
        by_cases hhmem : h ∈ p.parts
        · have hhmem' : h ∈ p.parts.toFinset := by simpa
          calc
            p.parts.count h * h = h * p.parts.count h := Nat.mul_comm _ _
            _ ≤ ∑ j ∈ p.parts.toFinset, j * p.parts.count j := by
              exact Finset.single_le_sum
                (fun j _ ↦ Nat.zero_le (j * p.parts.count j)) hhmem'
            _ = p.parts.sum := by
              have hsum := (Finset.sum_multiset_map_count p.parts id).symm
              simp only [id_eq, nsmul_eq_mul, Nat.cast_id, mul_comm] at hsum
              simpa only [Multiset.map_id'] using hsum
        · rw [Multiset.count_eq_zero.mpr hhmem]
          simp
      rw [p.parts_sum] at hsumle
      by_contra hnot
      have hthree : 3 ≤ p.parts.count h := by omega
      have hthreeMul : 3 * h ≤ p.parts.count h * h := by
        exact Nat.mul_le_mul_right h hthree
      omega
    rcases Nat.eq_zero_or_pos (p.parts.count h) with hzero | hpos
    · have hall := allPartsIn_reduced_of_count_half_zero hm hmh hevent hzero
      simp [hevent, hzero, hall]
    · rcases Nat.eq_or_lt_of_le hcountle with htwo | hlt
      · have hhmem : h ∈ p.parts := Multiset.count_pos.mp (by omega)
        simp [hevent, htwo, hhmem]
        split_ifs <;> simp [localCompleteCycleWeight] <;> positivity
      · have hone : p.parts.count h = 1 := by omega
        have hhmem : h ∈ p.parts := Multiset.count_pos.mp (by omega)
        have hall := allPartsIn_erase_reduced_of_count_half_one hm hmh hevent hone
        simp [hevent, hone, hhmem, hall]
        split_ifs <;> simp [localCompleteCycleWeight] <;> positivity
  · simp [hevent]
    split_ifs <;> simp [localCompleteCycleWeight] <;> positivity

open scoped BigOperators Finset

def TwoHalfCycleEvent (m h : ℕ) (mu : Multiset ℕ) : Prop :=
  NonLongFullCycleEvent m mu ∧ mu.count h = 2

instance (m h : ℕ) : DecidablePred (TwoHalfCycleEvent m h) := fun _ ↦ by
  unfold TwoHalfCycleEvent
  infer_instance

def twoHalfCycleTypes (n m h : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes n).filter (TwoHalfCycleEvent m h)

def consTwoMultisetEmbedding (h : ℕ) : Multiset ℕ ↪ Multiset ℕ where
  toFun mu := h ::ₘ h ::ₘ mu
  inj' := by
    intro mu nu heq
    exact (Multiset.cons_inj_right h).mp ((Multiset.cons_inj_right h).mp heq)

theorem twoHalfOrderMass_eq_sum_twoHalfCycleTypes {n m h : ℕ}
    (hm : 2 ≤ m) (hh : 2 ≤ h) :
    twoHalfOrderMass n m h =
      ∑ mu ∈ twoHalfCycleTypes n m h, cycleWeight n mu := by
  have hmass : twoHalfOrderMass n m h =
      localPartitionMass n (TwoHalfCycleEvent m h) := by
    unfold twoHalfOrderMass localPartitionMass TwoHalfCycleEvent
    apply Finset.sum_congr rfl
    intro p _
    by_cases hc : p.parts.count h = 2
    · have hhmem : h ∈ p.parts := Multiset.count_pos.mp (by omega)
      simp [hc, hhmem]
    · simp [hc]
  rw [hmass, localPartitionMass_eq_completeCycleTypeMass,
    completeCycleTypeMass_eq_sum_cycleTypes]
  unfold twoHalfCycleTypes
  rw [← Finset.sum_filter]
  congr 1
  ext mu
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hmu, hevent⟩
    refine ⟨hmu, ?_⟩
    have hlcm := lcm_completeCycleType hmu
    have hhmem := mem_completeCycleType_iff_of_two_le (n := n) (mu := mu) hh
    have hmmem := mem_completeCycleType_iff_of_two_le (n := n) (mu := mu) hm
    have hcount : (completeCycleType n mu).count h = mu.count h := by
      have hnot : h ∉ Multiset.replicate (n - mu.sum) 1 := by
        simp only [Multiset.mem_replicate, not_and_or]
        right
        omega
      unfold completeCycleType
      rw [Multiset.count_add]
      rw [Multiset.count_eq_zero.mpr hnot]
      simp
    simpa only [TwoHalfCycleEvent, NonLongFullCycleEvent, hlcm, hmmem,
      hcount] using hevent
  · rintro ⟨hmu, hevent⟩
    refine ⟨hmu, ?_⟩
    have hlcm := lcm_completeCycleType hmu
    have hhmem := mem_completeCycleType_iff_of_two_le (n := n) (mu := mu) hh
    have hmmem := mem_completeCycleType_iff_of_two_le (n := n) (mu := mu) hm
    have hcount : (completeCycleType n mu).count h = mu.count h := by
      have hnot : h ∉ Multiset.replicate (n - mu.sum) 1 := by
        simp only [Multiset.mem_replicate, not_and_or]
        right
        omega
      unfold completeCycleType
      rw [Multiset.count_add]
      rw [Multiset.count_eq_zero.mpr hnot]
      simp
    simpa only [TwoHalfCycleEvent, NonLongFullCycleEvent, hlcm, hmmem,
      hcount] using hevent

theorem twoHalfCycleTypes_eq_map_exceptional {m h r : ℕ}
    (hmh : m = 2 * h) (hh : 2 ≤ h) (hr : r < h) :
    twoHalfCycleTypes (m + r) m h =
      (exceptionalHalfResidualTypes r m).map (consTwoMultisetEmbedding h) := by
  classical
  have hmpos : 0 < m := by omega
  ext nu
  constructor
  · intro hnu
    rw [Finset.mem_map]
    rw [show nu ∈ twoHalfCycleTypes (m + r) m h ↔
        nu ∈ cycleTypes (m + r) ∧ TwoHalfCycleEvent m h nu by
      simp [twoHalfCycleTypes]] at hnu
    let mu := (nu.erase h).erase h
    have hhmem : h ∈ nu := Multiset.count_pos.mp (by
      rw [hnu.2.2]
      norm_num)
    have hherase : h ∈ nu.erase h := Multiset.count_pos.mp (by
      rw [Multiset.count_erase_self, hnu.2.2]
      norm_num)
    have hcons1 : h ::ₘ nu.erase h = nu := Multiset.cons_erase hhmem
    have hcons2 : h ::ₘ mu = nu.erase h := Multiset.cons_erase hherase
    have hdecomp : h ::ₘ h ::ₘ mu = nu := by rw [hcons2, hcons1]
    have hmucycle : mu ∈ cycleTypes r := by
      rw [mem_cycleTypes]
      constructor
      · have hnusum := (mem_cycleTypes.mp hnu.1).1
        have hsum := congrArg Multiset.sum hdecomp
        simp only [Multiset.sum_cons] at hsum
        omega
      · intro a ha
        exact (mem_cycleTypes.mp hnu.1).2 a
          (by rw [← hdecomp]; simp [ha])
    refine ⟨mu, ?_, hdecomp⟩
    rw [mem_exceptionalHalfResidualTypes]
    refine ⟨hmucycle, ?_⟩
    have hlcm := hnu.2.1.1
    rw [← hdecomp] at hlcm
    simp only [Multiset.lcm_cons] at hlcm
    have hhalf : m / 2 = h := by omega
    rw [hhalf]
    calc
      Nat.lcm h mu.lcm = Nat.lcm (Nat.lcm h h) mu.lcm := by rw [Nat.lcm_self]
      _ = Nat.lcm h (Nat.lcm h mu.lcm) := Nat.lcm_assoc h h mu.lcm
      _ = m := hlcm
  · rw [Finset.mem_map]
    rintro ⟨mu, hmu, rfl⟩
    change h ::ₘ h ::ₘ mu ∈ twoHalfCycleTypes (m + r) m h
    rw [show h ::ₘ h ::ₘ mu ∈ twoHalfCycleTypes (m + r) m h ↔
        h ::ₘ h ::ₘ mu ∈ cycleTypes (m + r) ∧
      TwoHalfCycleEvent m h (h ::ₘ h ::ₘ mu) by
      simp [twoHalfCycleTypes]]
    have hmudata := mem_exceptionalHalfResidualTypes.mp hmu
    have hmucycle := mem_cycleTypes.mp hmudata.1
    have hhnot : h ∉ mu := by
      intro hhmu
      have hle : h ≤ mu.sum := Multiset.le_sum_of_mem hhmu
      omega
    have hmnot : m ∉ mu := by
      intro hmmu
      have hmle : m ≤ mu.sum := Multiset.le_sum_of_mem hmmu
      omega
    constructor
    · rw [mem_cycleTypes]
      constructor
      · simp only [Multiset.sum_cons]
        omega
      · intro a ha
        rcases Multiset.mem_cons.mp ha with rfl | ha
        · exact hh
        · rcases Multiset.mem_cons.mp ha with rfl | ha
          · exact hh
          · exact hmucycle.2 a ha
    · unfold TwoHalfCycleEvent NonLongFullCycleEvent
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [Multiset.lcm_cons]
        calc
          Nat.lcm h (Nat.lcm h mu.lcm) = Nat.lcm (Nat.lcm h h) mu.lcm :=
            (Nat.lcm_assoc h h mu.lcm).symm
          _ = Nat.lcm h mu.lcm := by rw [Nat.lcm_self]
          _ = m := by simpa [show m / 2 = h by omega] using hmudata.2
      · intro hmmem
        rcases Multiset.mem_cons.mp hmmem with hmh' | hmmem
        · omega
        · rcases Multiset.mem_cons.mp hmmem with hmh' | hmmem
          · omega
          · exact hmnot hmmem
      · simp [Multiset.count_cons, hhnot]

theorem twoHalfOrderMass_cast_eq_exceptionalHalfContribution {m h r : ℕ}
    (hmh : m = 2 * h) (hh : 2 ≤ h) (hr : r < h) :
    (twoHalfOrderMass (m + r) m h : ℝ) = exceptionalHalfContribution r m := by
  rw [twoHalfOrderMass_eq_sum_twoHalfCycleTypes (by omega) hh]
  rw [twoHalfCycleTypes_eq_map_exceptional hmh hh hr, Finset.sum_map]
  unfold exceptionalHalfContribution
  push_cast
  apply Finset.sum_congr rfl
  intro mu hmu
  change ((cycleWeight (m + r) (h ::ₘ h ::ₘ mu) : ℚ) : ℝ) = _
  rw [show m / 2 = h by omega]
  simp [cycleWeight, cycleWeightReal]

/-! ## Exact form of the error after removing the long cycle -/

/-- After the distinguished `(n-r)`-cycle has been removed, the local error
is exactly the non-long cycle-index contribution minus Beker's half-cycle
correction.  This identity contains no asymptotics. -/
theorem localError_eq_nonLong_sub_halfCycleCorrection
    {n r : ℕ} (hm : 2 ≤ n - r) (hrm : r < n - r)
    (hadm : Nat.lcmUpto r ∣ n - r) :
    orderProbability n (n - r) - localMainTerm n r =
      (nonLongCycleContribution n (n - r) : ℝ) -
        halfCycleCorrection n r := by
  have hsum : (n - r) + r = n :=
    Nat.sub_add_cancel (hrm.trans_le (Nat.sub_le n r)).le
  have hlong := orderProbability_eq_one_div_add_nonLong
    (r := r) (m := n - r) hm hrm hadm
  rw [hsum] at hlong
  rw [hlong, localMainTerm]
  ring

/-- The absolute local error is bounded by the non-long contribution plus
the (nonnegative) exceptional correction. -/
theorem abs_localError_le_nonLong_add_halfCycleCorrection
    {n r : ℕ} (hm : 2 ≤ n - r) (hrm : r < n - r)
    (hadm : Nat.lcmUpto r ∣ n - r) :
    |orderProbability n (n - r) - localMainTerm n r| ≤
      (nonLongCycleContribution n (n - r) : ℝ) +
        halfCycleCorrection n r := by
  rw [localError_eq_nonLong_sub_halfCycleCorrection hm hrm hadm]
  have hnonLongQ := nonLongCycleContribution_nonneg n (n - r)
  have hnonLong : 0 ≤ (nonLongCycleContribution n (n - r) : ℝ) := by
    exact_mod_cast hnonLongQ
  exact abs_sub_le_iff.mpr ⟨by linarith [halfCycleCorrection_nonneg n r], by linarith⟩

theorem twoHalfOrderMass_le_nonLongPartitionMass (n m h : ℕ) :
    twoHalfOrderMass n m h ≤
      localPartitionMass n (NonLongFullCycleEvent m) := by
  unfold twoHalfOrderMass localPartitionMass
  apply Finset.sum_le_sum
  intro p _
  by_cases hh : h ∈ p.parts <;>
    by_cases he : NonLongFullCycleEvent m p.parts <;>
      by_cases hc : p.parts.count h = 2 <;>
        simp [hh, he, hc, localCompleteCycleWeight] <;> positivity

theorem even_nonLong_sub_halfCycleCorrection_bound
    {m h r : ℕ} (hm : 4 ≤ m) (hmh : m = 2 * h)
    (hr : 2 * r < m) (hadm : Nat.lcmUpto r ∣ m) :
    0 ≤ (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ∧
      (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ≤
        29 * (divisorCount m : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
  have hmpos : 0 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have hh : 2 ≤ h := by omega
  have hrh : r < h := by omega
  have hhalf : m / 2 = h := by omega
  have hlocal := nonLongCycleContribution_eq_localPartitionMass
    (n := m + r) hm2
  have hsplit := nonLongPartitionMass_le_reduced_add_one_add_two
    hmpos hmh hr
  have hone := oneHalfReducedMass_le
    (D := reducedDivisors m) (n := m + r) (h := h) (by omega) (by omega)
  rw [show m + r - h = h + r by omega] at hone
  have hfull := reducedDivisorMass_full_sharp (m := m) (r := r) hmpos
  have hhalfmass := reducedDivisorMass_half_sharp hmpos hmh hr
  have htwoCorr :
      (twoHalfOrderMass (m + r) m h : ℝ) =
        halfCycleCorrection (m + r) r := by
    rw [twoHalfOrderMass_cast_eq_exceptionalHalfContribution hmh hh hrh]
    exact exceptionalHalfContribution_eq_halfCycleCorrection
      (by simpa [hhalf] using hrh) hadm
  have htwoLe := twoHalfOrderMass_le_nonLongPartitionMass (m + r) m h
  have hlower : 0 ≤ (nonLongCycleContribution (m + r) m : ℝ) -
      halfCycleCorrection (m + r) r := by
    rw [hlocal]
    exact sub_nonneg.mpr (by
      rw [← htwoCorr]
      exact_mod_cast htwoLe)
  have hupperRaw :
      (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ≤
        (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) +
          (oneHalfReducedMass (reducedDivisors m) (m + r) h : ℝ) := by
    rw [hlocal]
    have hsplitR :
        (localPartitionMass (m + r) (NonLongFullCycleEvent m) : ℝ) ≤
          (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) +
            (oneHalfReducedMass (reducedDivisors m) (m + r) h : ℝ) +
              (twoHalfOrderMass (m + r) m h : ℝ) := by
      exact_mod_cast hsplit
    rw [htwoCorr] at hsplitR
    linarith
  have hupperMass :
      (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) +
          (oneHalfReducedMass (reducedDivisors m) (m + r) h : ℝ) ≤
        9 * ((reducedDivisors m).card : ℝ) ^ 3 /
            (2 * (m : ℝ) ^ 3) +
          (1 / (h : ℝ)) *
            (12 * ((reducedDivisors m).card : ℝ) ^ 2 / (m : ℝ) ^ 2) := by
    have hfullR :
        (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) ≤
          9 * ((reducedDivisors m).card : ℝ) ^ 3 /
            (2 * (m : ℝ) ^ 3) := by
      have hc :
          ((restrictedPartitionMass (reducedDivisors m) (m + r) : ℚ) : ℝ) ≤
            ((9 * ((reducedDivisors m).card : ℚ) ^ 3 /
              (2 * (m : ℚ) ^ 3) : ℚ) : ℝ) := Rat.cast_le.mpr hfull
      push_cast at hc
      simpa using hc
    have honeR :
        (oneHalfReducedMass (reducedDivisors m) (m + r) h : ℝ) ≤
          (1 / (h : ℝ)) *
            (restrictedPartitionMass (reducedDivisors m) (h + r) : ℝ) := by
      have hc :
          ((oneHalfReducedMass (reducedDivisors m) (m + r) h : ℚ) : ℝ) ≤
            (((1 / (h : ℚ)) *
              restrictedPartitionMass (reducedDivisors m) (h + r) : ℚ) : ℝ) :=
        Rat.cast_le.mpr hone
      push_cast at hc
      simpa using hc
    have hhalfmassR :
        (restrictedPartitionMass (reducedDivisors m) (h + r) : ℝ) ≤
          12 * ((reducedDivisors m).card : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      have hc :
          ((restrictedPartitionMass (reducedDivisors m) (h + r) : ℚ) : ℝ) ≤
            ((12 * ((reducedDivisors m).card : ℚ) ^ 2 /
              (m : ℚ) ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr hhalfmass
      push_cast at hc
      simpa using hc
    exact add_le_add hfullR
      (honeR.trans (mul_le_mul_of_nonneg_left hhalfmassR (by positivity)))
  have honeMem : 1 ∈ reducedDivisors m := by
    rw [mem_reducedDivisors]
    simp
    omega
  have hTOneNat : 1 ≤ (reducedDivisors m).card :=
    Finset.one_le_card.mpr ⟨1, honeMem⟩
  have hTOne : (1 : ℝ) ≤ ((reducedDivisors m).card : ℝ) := by
    exact_mod_cast hTOneNat
  have hTtauNat : (reducedDivisors m).card ≤ divisorCount m := by
    exact reducedDivisors_card_le_divisors_card m
  have hTtau : ((reducedDivisors m).card : ℝ) ≤ (divisorCount m : ℝ) := by
    exact_mod_cast hTtauNat
  have hT3 : ((reducedDivisors m).card : ℝ) ^ 3 ≤
      (divisorCount m : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hTtau 3
  have hT2T3 : ((reducedDivisors m).card : ℝ) ^ 2 ≤
      ((reducedDivisors m).card : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (((reducedDivisors m).card : ℝ) - 1)]
  have henvelope :
      9 * ((reducedDivisors m).card : ℝ) ^ 3 /
            (2 * (m : ℝ) ^ 3) +
          (1 / (h : ℝ)) *
            (12 * ((reducedDivisors m).card : ℝ) ^ 2 / (m : ℝ) ^ 2) ≤
        29 * (divisorCount m : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hhR : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hmhR : (m : ℝ) = 2 * h := by exact_mod_cast hmh
    field_simp [hhR.ne', hmR.ne']
    nlinarith
  exact ⟨hlower, hupperRaw.trans (hupperMass.trans henvelope)⟩

private theorem odd_nonLongPartitionMass_le_reduced {m r : ℕ}
    (hm : 0 < m) (hodd : ¬ 2 ∣ m) :
    localPartitionMass (m + r) (NonLongFullCycleEvent m) ≤
      restrictedPartitionMass (reducedDivisors m) (m + r) := by
  unfold restrictedPartitionMass localPartitionMass
  apply Finset.sum_le_sum
  intro p _
  by_cases hevent : NonLongFullCycleEvent m p.parts
  · have hall : AllPartsIn (reducedDivisors m) p.parts := by
      intro d hd
      rw [mem_reducedDivisors]
      have hdvd : d ∣ m := by
        rw [← hevent.1]
        exact Multiset.dvd_lcm hd
      have hdle := Nat.le_of_dvd hm hdvd
      have hdne : d ≠ m := fun hdm ↦ hevent.2 (hdm ▸ hd)
      refine ⟨hdvd, lt_of_le_of_ne hdle hdne, ?_⟩
      intro hdm
      apply hodd
      exact ⟨d, by omega⟩
    simp [hevent, hall]
  · simp [hevent]
    split_ifs <;> simp [localCompleteCycleWeight] <;> positivity

private theorem halfCycleCorrection_eq_zero_of_odd {m r : ℕ}
    (hodd : ¬ 2 ∣ m) (hadm : Nat.lcmUpto r ∣ m) :
    halfCycleCorrection (m + r) r = 0 := by
  have hrsmall : r ≤ 1 := by
    by_contra hr
    have htwo : 2 ∣ Nat.lcmUpto r :=
      Nat.dvd_lcmUpto (by omega) (by omega)
    exact hodd (htwo.trans hadm)
  simp [halfCycleCorrection, hrsmall]

theorem odd_nonLong_sub_halfCycleCorrection_bound
    {m r : ℕ} (hm : 4 ≤ m) (hodd : ¬ 2 ∣ m)
    (hadm : Nat.lcmUpto r ∣ m) :
    0 ≤ (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ∧
      (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ≤
        29 * (divisorCount m : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
  have hmpos : 0 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have hcorr := halfCycleCorrection_eq_zero_of_odd hodd hadm
  have hlocal := nonLongCycleContribution_eq_localPartitionMass
    (n := m + r) hm2
  have hsubset := odd_nonLongPartitionMass_le_reduced (r := r) hmpos hodd
  have hfull := reducedDivisorMass_full_sharp (m := m) (r := r) hmpos
  have hnonnegQ := nonLongCycleContribution_nonneg (m + r) m
  have hnonneg : 0 ≤ (nonLongCycleContribution (m + r) m : ℝ) := by
    exact_mod_cast hnonnegQ
  have hmass : (nonLongCycleContribution (m + r) m : ℝ) ≤
      9 * ((reducedDivisors m).card : ℝ) ^ 3 /
        (2 * (m : ℝ) ^ 3) := by
    rw [hlocal]
    have hsubsetR :
        (localPartitionMass (m + r) (NonLongFullCycleEvent m) : ℝ) ≤
          (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) := by
      exact_mod_cast hsubset
    have hfullR :
        (restrictedPartitionMass (reducedDivisors m) (m + r) : ℝ) ≤
          9 * ((reducedDivisors m).card : ℝ) ^ 3 /
            (2 * (m : ℝ) ^ 3) := by
      have hc :
          ((restrictedPartitionMass (reducedDivisors m) (m + r) : ℚ) : ℝ) ≤
            ((9 * ((reducedDivisors m).card : ℚ) ^ 3 /
              (2 * (m : ℚ) ^ 3) : ℚ) : ℝ) := Rat.cast_le.mpr hfull
      push_cast at hc
      simpa using hc
    exact hsubsetR.trans hfullR
  have hTtau : ((reducedDivisors m).card : ℝ) ≤ (divisorCount m : ℝ) := by
    exact_mod_cast reducedDivisors_card_le_divisors_card m
  have hT3 : ((reducedDivisors m).card : ℝ) ^ 3 ≤
      (divisorCount m : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hTtau 3
  have henvelope :
      9 * ((reducedDivisors m).card : ℝ) ^ 3 /
          (2 * (m : ℝ) ^ 3) ≤
        29 * (divisorCount m : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    field_simp [hmR.ne']
    nlinarith [show 0 ≤ (divisorCount m : ℝ) ^ 3 by positivity]
  rw [hcorr]
  simp only [sub_zero]
  exact ⟨hnonneg, hmass.trans henvelope⟩

theorem nonLong_sub_halfCycleCorrection_bound
    {m r : ℕ} (hm : 4 ≤ m) (hr : 2 * r < m)
    (hadm : Nat.lcmUpto r ∣ m) :
    0 ≤ (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ∧
      (nonLongCycleContribution (m + r) m : ℝ) -
          halfCycleCorrection (m + r) r ≤
        29 * (divisorCount m : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
  by_cases heven : 2 ∣ m
  · let h := m / 2
    have hmh : m = 2 * h := by
      dsimp [h]
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel heven).symm
    exact even_nonLong_sub_halfCycleCorrection_bound hm hmh hr hadm
  · exact odd_nonLong_sub_halfCycleCorrection_bound hm heven hadm

theorem abs_localError_le_divisor_envelope
    {n r : ℕ} (hm : 4 ≤ n - r) (hr : 2 * r < n - r)
    (hadm : Nat.lcmUpto r ∣ n - r) :
    |orderProbability n (n - r) - localMainTerm n r| ≤
      29 * (divisorCount (n - r) : ℝ) ^ 3 / ((n - r : ℕ) : ℝ) ^ 3 := by
  have hrn : r < n := by omega
  have hrm : r < n - r := by omega
  have hsum : (n - r) + r = n := Nat.sub_add_cancel hrn.le
  rw [localError_eq_nonLong_sub_halfCycleCorrection (by omega) hrm hadm]
  have hb := nonLong_sub_halfCycleCorrection_bound hm hr hadm
  rw [hsum] at hb
  rw [abs_of_nonneg hb.1]
  exact hb.2

/-- A uniform majorant for all admissible local errors in degree `n`. -/
noncomputable def localUniformError (n : ℕ) : ℝ :=
  232 * (n : ℝ) ^ (1 / 8 : ℝ) / (n : ℝ) ^ 3

theorem localUniformError_nonneg (n : ℕ) : 0 ≤ localUniformError n := by
  unfold localUniformError
  positivity

theorem tendsto_sq_mul_localUniformError :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * localUniformError n)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (7 / 8 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦
      (232 : ℝ) / (n : ℝ) ^ (7 / 8 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpow
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold localUniformError
  have hsumpow :
      (n : ℝ) ^ (7 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  field_simp [hnR.ne']
  simpa [mul_comm] using hsumpow.symm

theorem eventually_abs_localError_le_localUniformError :
    ∀ᶠ n : ℕ in atTop, ∀ r, r < n → Nat.lcmUpto r ∣ n - r →
      |orderProbability n (n - r) - localMainTerm n r| ≤
        localUniformError n := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_divisorCount_power_le_eighth 3 (by norm_num)
  filter_upwards [Nat.eventually_const_mul_lt_of_lcmUpto_dvd 3,
    eventually_ge_atTop (max N₀ 8)] with n hn hlarge
  intro r hrn hadm
  have h3r := hn r hrn hadm
  have hN₀n : N₀ ≤ n := (le_max_left N₀ 8).trans hlarge
  have hn8 : 8 ≤ n := (le_max_right N₀ 8).trans hlarge
  have hmpos : 1 ≤ n - r := by omega
  have hm4 : 4 ≤ n - r := by omega
  have htwor : 2 * r < n - r := by omega
  have hmn3 : n - r ≤ n ^ 3 := by
    have hn1 : 1 ≤ n := by omega
    calc
      n - r ≤ n := Nat.sub_le n r
      _ ≤ n ^ 3 := Nat.le_pow (by norm_num)
  have htau := hN₀ n hN₀n (n - r) hmpos hmn3
  have hfinite := abs_localError_le_divisor_envelope hm4 htwor hadm
  refine hfinite.trans ?_
  unfold localUniformError
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmR : (0 : ℝ) < ((n - r : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hnmNat : n ≤ 2 * (n - r) := by omega
  have hnm : (n : ℝ) ≤ 2 * ((n - r : ℕ) : ℝ) := by exact_mod_cast hnmNat
  have hcube : (n : ℝ) ^ 3 ≤ 8 * ((n - r : ℕ) : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n) hnm 3
    nlinarith
  have hinv : 1 / ((n - r : ℕ) : ℝ) ^ 3 ≤
      8 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hmR 3) (pow_pos hnR 3)]
    simpa [mul_comm] using hcube
  calc
    29 * (divisorCount (n - r) : ℝ) ^ 3 /
          ((n - r : ℕ) : ℝ) ^ 3 ≤
        29 * (n : ℝ) ^ (1 / 8 : ℝ) /
          ((n - r : ℕ) : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htau (by norm_num)) (by positivity)
    _ = (29 * (n : ℝ) ^ (1 / 8 : ℝ)) *
          (1 / ((n - r : ℕ) : ℝ) ^ 3) := by ring
    _ ≤ (29 * (n : ℝ) ^ (1 / 8 : ℝ)) *
          (8 / (n : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 232 * (n : ℝ) ^ (1 / 8 : ℝ) / (n : ℝ) ^ 3 := by ring

theorem orderProbability_hasUniformLocalExpansion :
    HasUniformLocalExpansion orderProbability := by
  refine ⟨localUniformError, localUniformError_nonneg,
    tendsto_sq_mul_localUniformError, ?_⟩
  exact eventually_abs_localError_le_localUniformError

/-! ## Uniform finite envelope -/

/-- The largest actual local error over the finite set of admissible
remainders.  This is the canonical error sequence for the uniform estimate. -/
def localErrorEnvelope (n : ℕ) : ℝ :=
  (admissibleRemainders n).fold max 0 fun r ↦
    |orderProbability n (n - r) - localMainTerm n r|

theorem localErrorEnvelope_nonneg (n : ℕ) : 0 ≤ localErrorEnvelope n := by
  classical
  unfold localErrorEnvelope
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem abs_localError_le_localErrorEnvelope {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    |orderProbability n (n - r) - localMainTerm n r| ≤
      localErrorEnvelope n := by
  classical
  unfold localErrorEnvelope
  rw [Finset.le_fold_max]
  exact Or.inr ⟨r, hr, le_rfl⟩

end

end Erdos1161
