import ErdosProblems.Erdos1161.CycleIndex

/-!
# Distinguished-cycle recursion for Erdős Problem 1161

This file records the finite counting form of the standard ``expose the
cycle through a distinguished letter'' argument.  The complete cycle type
includes the fixed points (parts of size one).  Marking one part of a
complete type and then deleting it is the exact finite version of exposing
that cycle.  No probability space is needed.
-/

open scoped BigOperators

namespace Erdos1161

open Equiv

/-- Add the omitted one-cycles to Mathlib's nontrivial `cycleType`. -/
def completeCycleType (n : ℕ) (mu : Multiset ℕ) : Multiset ℕ :=
  mu + Multiset.replicate (n - mu.sum) 1

/-- Denominator of the cycle-index weight when *all* cycles, including
fixed points, are recorded. -/
def completeCycleDenominator (mu : Multiset ℕ) : ℕ :=
  mu.prod * ∏ j ∈ mu.toFinset, (mu.count j).factorial

/-- The complete cycle-index weight. -/
def completeCycleWeight (mu : Multiset ℕ) : ℚ :=
  1 / (completeCycleDenominator mu : ℚ)

@[simp]
theorem sum_completeCycleType {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) : (completeCycleType n mu).sum = n := by
  rw [mem_cycleTypes] at hmu
  simp [completeCycleType, Nat.add_sub_of_le hmu.1]

theorem completeCycleType_count_one {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) :
    (completeCycleType n mu).count 1 = n - mu.sum := by
  have hnot : 1 ∉ mu := by
    intro h
    have := (mem_cycleTypes.mp hmu).2 1 h
    omega
  simp [completeCycleType, Multiset.count_eq_zero.mpr hnot]

theorem completeCycleType_count_of_two_le {n j : ℕ} {mu : Multiset ℕ}
    (hj : 2 ≤ j) :
    (completeCycleType n mu).count j = mu.count j := by
  have hj1 : j ≠ 1 := by omega
  have hrep : j ∉ Multiset.replicate (n - mu.sum) 1 := by
    intro h
    exact hj1 (Multiset.eq_of_mem_replicate h)
  simp [completeCycleType, Multiset.count_eq_zero.mpr hrep]

theorem completeCycleDenominator_cons (j : ℕ) (mu : Multiset ℕ) :
    completeCycleDenominator (j ::ₘ mu) =
      j * (mu.count j + 1) * completeCycleDenominator mu := by
  classical
  unfold completeCycleDenominator
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
    rw [Finset.prod_congr rfl fun a ha ↦ congrArg Nat.factorial (hcounts a ha)]
    rw [Nat.factorial_succ]
    ring
  · have hjf : j ∉ mu.toFinset := by simpa
    rw [Multiset.toFinset_cons, Finset.prod_insert hjf]
    simp only [Multiset.prod_cons, Multiset.count_cons_self,
      Multiset.count_eq_zero.mpr hj, zero_add]
    have hcounts : ∀ a ∈ mu.toFinset, (j ::ₘ mu).count a = mu.count a := by
      intro a ha
      exact Multiset.count_cons_of_ne (by
        intro h
        subst a
        exact hjf ha) mu
    rw [Finset.prod_congr rfl fun a ha ↦ congrArg Nat.factorial (hcounts a ha)]
    norm_num
    ring

theorem completeCycleDenominator_add_ones (mu : Multiset ℕ) (k : ℕ)
    (hone : 1 ∉ mu) :
    completeCycleDenominator (mu + Multiset.replicate k 1) =
      k.factorial * completeCycleDenominator mu := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Multiset.replicate_succ, Multiset.add_cons]
      rw [completeCycleDenominator_cons, ih]
      have hcount : (mu + Multiset.replicate k 1).count 1 = k := by
        simp [Multiset.count_eq_zero.mpr hone]
      rw [hcount, Nat.factorial_succ]
      ring

theorem completeCycleDenominator_completeCycleType {n : ℕ}
    {mu : Multiset ℕ} (hmu : mu ∈ cycleTypes n) :
    completeCycleDenominator (completeCycleType n mu) =
      cycleDenominator n mu := by
  have hone : 1 ∉ mu := by
    intro h
    have := (mem_cycleTypes.mp hmu).2 1 h
    omega
  rw [completeCycleType, completeCycleDenominator_add_ones mu (n - mu.sum) hone]
  unfold cycleDenominator completeCycleDenominator
  ring

theorem completeCycleWeight_completeCycleType {n : ℕ}
    {mu : Multiset ℕ} (hmu : mu ∈ cycleTypes n) :
    completeCycleWeight (completeCycleType n mu) = cycleWeight n mu := by
  rw [completeCycleWeight, cycleWeight,
    completeCycleDenominator_completeCycleType hmu]

theorem completeCycleDenominator_eq_mul_erase {j : ℕ} {mu : Multiset ℕ}
    (hj : j ∈ mu) :
    completeCycleDenominator mu =
      j * mu.count j * completeCycleDenominator (mu.erase j) := by
  nth_rewrite 1 [← Multiset.cons_erase hj]
  rw [completeCycleDenominator_cons]
  have hc : 0 < mu.count j := Multiset.count_pos.mpr hj
  rw [Multiset.count_erase_self, Nat.sub_add_cancel hc]

theorem completeCycleWeight_erase {j : ℕ} {mu : Multiset ℕ}
    (hj : j ∈ mu) (hpos : ∀ a ∈ mu, 0 < a) :
    completeCycleWeight (mu.erase j) =
      (j * mu.count j : ℕ) * completeCycleWeight mu := by
  have hden := completeCycleDenominator_eq_mul_erase hj
  have herase_pos : 0 < completeCycleDenominator (mu.erase j) := by
    unfold completeCycleDenominator
    have hprod : 0 < (mu.erase j).prod := by
      apply Multiset.prod_pos
      intro a ha
      exact hpos a (Multiset.mem_of_mem_erase ha)
    positivity
  have hcount : 0 < mu.count j := Multiset.count_pos.mpr hj
  unfold completeCycleWeight
  rw [hden, Nat.cast_mul, Nat.cast_mul]
  have hjpos := hpos j hj
  have hjne : (j : ℚ) ≠ 0 := by exact_mod_cast hjpos.ne'
  have hcne : (mu.count j : ℚ) ≠ 0 := by exact_mod_cast hcount.ne'
  have hene : (completeCycleDenominator (mu.erase j) : ℚ) ≠ 0 := by
    exact_mod_cast herase_pos.ne'
  push_cast
  field_simp

/-- Marking a distinguished cycle: the sum of the weights obtained by
deleting one cycle of each occurring length is `n` times the original
weight.  Multiplicities are exactly absorbed by the factorial in the cycle
index denominator. -/
theorem sum_completeCycleWeight_erase (mu : Multiset ℕ)
    (hpos : ∀ a ∈ mu, 0 < a) :
    ∑ j ∈ mu.toFinset, completeCycleWeight (mu.erase j) =
      (mu.sum : ℚ) * completeCycleWeight mu := by
  calc
    ∑ j ∈ mu.toFinset, completeCycleWeight (mu.erase j) =
        ∑ j ∈ mu.toFinset,
          ((j * mu.count j : ℕ) : ℚ) * completeCycleWeight mu := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [completeCycleWeight_erase (by simpa using hj) hpos]
    _ = (∑ j ∈ mu.toFinset, ((j * mu.count j : ℕ) : ℚ)) *
          completeCycleWeight mu := by
            rw [Finset.sum_mul]
    _ = (mu.sum : ℚ) * completeCycleWeight mu := by
          have hsum : ∑ j ∈ mu.toFinset, j * mu.count j = mu.sum := by
            have h := (Finset.sum_multiset_map_count mu id).symm
            simp only [id_eq, nsmul_eq_mul, Nat.cast_id, mul_comm] at h
            simpa only [Multiset.map_id'] using h
          rw [show (∑ j ∈ mu.toFinset,
              ((j * mu.count j : ℕ) : ℚ)) = (mu.sum : ℚ) by
                exact_mod_cast hsum]

/-! ## The exact first-cycle recurrence on complete cycle types -/

/-- Total cycle-index mass of partitions of `n` satisfying `A`.

Every positive partition is a complete cycle type of a permutation.  Thus
this is the probability of the cycle-type event `A`; the bridge to the
actual permutation count is proved below. -/
def completeCycleTypeMass (n : ℕ) (A : Multiset ℕ → Prop)
    [DecidablePred A] : ℚ :=
  ∑ p : Nat.Partition n,
    if A p.parts then completeCycleWeight p.parts else 0

/-- Exact distinguished-cycle decomposition for an arbitrary predicate on
complete cycle types.  On the right, `j` is the length of the exposed
cycle and `q` is the complete type of the remaining `n-j` letters. -/
theorem completeCycleTypeMass_recursion (n : ℕ)
    (A : Multiset ℕ → Prop) [DecidablePred A] :
    (n : ℚ) * completeCycleTypeMass n A =
      ∑ j ∈ Finset.Icc 1 n, ∑ q : Nat.Partition (n - j),
        if A (j ::ₘ q.parts) then completeCycleWeight q.parts else 0 := by
  classical
  calc
    (n : ℚ) * completeCycleTypeMass n A =
        ∑ p : Nat.Partition n, (n : ℚ) *
          (if A p.parts then completeCycleWeight p.parts else 0) := by
            simp [completeCycleTypeMass, Finset.mul_sum]
    _ = ∑ p : Nat.Partition n, ∑ j ∈ Finset.Icc 1 n,
          if j ∈ p.parts then
            (if A p.parts then completeCycleWeight (p.parts.erase j) else 0)
          else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hA : A p.parts
      · simp only [hA, if_true]
        rw [← Finset.sum_filter]
        have hfilter :
            (Finset.Icc 1 n).filter (fun j ↦ j ∈ p.parts) = p.parts.toFinset := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_Icc, Multiset.mem_toFinset]
          constructor
          · exact fun h ↦ h.2
          · intro hj
            exact ⟨⟨p.parts_pos hj,
              (Multiset.le_sum_of_mem hj).trans_eq p.parts_sum⟩, hj⟩
        rw [hfilter]
        rw [show (n : ℚ) = (p.parts.sum : ℚ) by
          exact_mod_cast p.parts_sum.symm]
        exact (sum_completeCycleWeight_erase p.parts
          (fun a ha ↦ p.parts_pos ha)).symm
      · simp [hA]
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
          if j ∈ p.parts then
            (if A p.parts then completeCycleWeight (p.parts.erase j) else 0)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 n,
          ∑ p : {p : Nat.Partition n // j ∈ p.parts},
            if A p.1.parts then completeCycleWeight (p.1.parts.erase j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ q : Nat.Partition (n - j),
          if A (j ::ₘ q.parts) then completeCycleWeight q.parts else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      apply Fintype.sum_equiv
        (Nat.Partition.partitionWithPartEquiv hj'.1 hj'.2)
      intro p
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
      rw [Multiset.cons_erase p.2]

/-! ## Identifying complete types with integer partitions -/

/-- Delete the parts of size one from an integer partition. -/
def nontrivialParts {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (2 ≤ ·)

theorem nontrivialParts_mem_cycleTypes {n : ℕ} (p : Nat.Partition n) :
    nontrivialParts p ∈ cycleTypes n := by
  rw [mem_cycleTypes]
  constructor
  · have hsplit := Multiset.filter_add_not (2 ≤ ·) p.parts
    have hs := congrArg Multiset.sum hsplit
    simp only [Multiset.sum_add] at hs
    rw [p.parts_sum] at hs
    dsimp [nontrivialParts]
    omega
  · intro a ha
    exact (Multiset.mem_filter.mp ha).2

theorem filter_not_two_le_eq_replicate_one {n : ℕ} (p : Nat.Partition n) :
    p.parts.filter (fun a ↦ ¬ 2 ≤ a) =
      Multiset.replicate (p.parts.count 1) 1 := by
  ext a
  by_cases ha1 : a = 1
  · subst a
    simp
  · by_cases ha0 : a = 0
    · subst a
      have hzero : 0 ∉ p.parts := by
        intro h
        exact (Nat.not_lt_zero 0) (p.parts_pos h)
      simp [Multiset.count_eq_zero.mpr hzero, Multiset.count_replicate]
    · have htwo : 2 ≤ a := by omega
      simp only [Multiset.count_filter, Multiset.count_replicate]
      rw [if_neg (not_not.mpr htwo), if_neg (fun h ↦ ha1 h.symm)]

theorem sum_nontrivialParts_add_count_one {n : ℕ} (p : Nat.Partition n) :
    (nontrivialParts p).sum + p.parts.count 1 = n := by
  have hsplit := Multiset.filter_add_not (2 ≤ ·) p.parts
  have hs := congrArg Multiset.sum hsplit
  rw [filter_not_two_le_eq_replicate_one] at hs
  simpa [nontrivialParts, p.parts_sum] using hs

theorem completeCycleType_nontrivialParts {n : ℕ} (p : Nat.Partition n) :
    completeCycleType n (nontrivialParts p) = p.parts := by
  unfold completeCycleType
  have hcount : n - (nontrivialParts p).sum = p.parts.count 1 := by
    have hs := sum_nontrivialParts_add_count_one p
    omega
  rw [hcount, ← filter_not_two_le_eq_replicate_one p]
  exact Multiset.filter_add_not (2 ≤ ·) p.parts

/-- Valid nontrivial cycle types on `n` letters are equivalent to the
integer partitions of `n`, by adding/removing the omitted one-cycles. -/
def cycleTypesEquivPartitions (n : ℕ) :
    {mu : Multiset ℕ // mu ∈ cycleTypes n} ≃ Nat.Partition n where
  toFun mu :=
    ⟨completeCycleType n mu.1,
      by
        intro a ha
        rw [completeCycleType, Multiset.mem_add] at ha
        rcases ha with ha | ha
        · exact (mem_cycleTypes.mp mu.2).2 a ha |>.trans' (by omega)
        · rw [Multiset.mem_replicate] at ha
          omega,
      sum_completeCycleType mu.2⟩
  invFun p := ⟨nontrivialParts p, nontrivialParts_mem_cycleTypes p⟩
  left_inv mu := by
    apply Subtype.ext
    dsimp [nontrivialParts]
    rw [completeCycleType, Multiset.filter_add]
    have hself : mu.1.filter (2 ≤ ·) = mu.1 :=
      Multiset.filter_eq_self.mpr (mem_cycleTypes.mp mu.2).2
    rw [hself]
    have hones : (Multiset.replicate (n - mu.1.sum) 1).filter (2 ≤ ·) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro a ha
      rw [Multiset.mem_replicate] at ha
      omega
    rw [hones, add_zero]
  right_inv p := by
    apply Nat.Partition.ext
    exact completeCycleType_nontrivialParts p

theorem completeCycleTypeMass_eq_sum_cycleTypes (n : ℕ)
    (A : Multiset ℕ → Prop) [DecidablePred A] :
    completeCycleTypeMass n A =
      ∑ mu ∈ cycleTypes n,
        if A (completeCycleType n mu) then cycleWeight n mu else 0 := by
  classical
  have heq :
      (∑ mu : {mu : Multiset ℕ // mu ∈ cycleTypes n},
        if A (completeCycleType n mu.1) then cycleWeight n mu.1 else 0) =
      completeCycleTypeMass n A := by
    apply Fintype.sum_equiv (cycleTypesEquivPartitions n)
    intro mu
    simp only [cycleTypesEquivPartitions]
    by_cases hA : A (completeCycleType n mu.1)
    · simp [hA, completeCycleWeight_completeCycleType mu.2]
    · simp [hA]
  rw [← heq]
  have hatt :
      (Finset.univ : Finset {mu : Multiset ℕ // mu ∈ cycleTypes n}) =
        (cycleTypes n).attach := by
    ext mu
    simp
  rw [hatt]
  exact Finset.sum_attach (cycleTypes n)
    (fun mu ↦ if A (completeCycleType n mu) then cycleWeight n mu else 0)

theorem completeCycleTypeMass_eq_cycleTypeEventProbability (n : ℕ)
    (A : Multiset ℕ → Prop) [DecidablePred A] :
    completeCycleTypeMass n A =
      (cycleTypeEventCount n (fun mu ↦ A (completeCycleType n mu)) : ℚ) /
        (n.factorial : ℚ) := by
  rw [cycleTypeEventProbability_eq_sum_cycleWeight]
  rw [completeCycleTypeMass_eq_sum_cycleTypes]
  rw [← Finset.sum_filter]
  simp [cycleTypeEventTypes]

end Erdos1161
