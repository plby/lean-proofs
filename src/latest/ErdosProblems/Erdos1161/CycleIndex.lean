import ErdosProblems.Erdos1161.Basic
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-!
# Exact cycle-index identities for Erdős Problem 1161

Mathlib's `Equiv.Perm.cycleType` records the lengths of the nontrivial cycles
of a permutation; fixed points are deliberately omitted.  Thus a multiset
`mu` represents a cycle-count vector on `Fin n` precisely when `mu.sum ≤ n`
and all its members are at least two.  The missing `n - mu.sum` letters are
the fixed points.

This file packages the exact finite identities needed in the proof of
Problem 1161.  In particular, `cycleDenominator n mu` is

`(number of fixed points)! * ∏_j j^(a_j) * ∏_j a_j!`,

with repeated members of `mu` supplying the powers in the middle product.
The theorem `cycleTypeProbability_eq_cycleWeight` is the normalized
cycle-index formula, while
`orderCountRationalProbability_eq_sum_cycleWeight` is its specialization to
permutations of prescribed order.
-/

open scoped BigOperators Finset

namespace Erdos1161

open Equiv

/-! ## Finite cycle types and their exact cardinalities -/

/-- The finite set of cycle types which actually occur on `Fin n`.

Fixed points do not occur in `Equiv.Perm.cycleType`; they are recovered as
`n - mu.sum` below. -/
def cycleTypes (n : ℕ) : Finset (Multiset ℕ) :=
  Finset.univ.image fun σ : Perm (Fin n) ↦ σ.cycleType

@[simp]
theorem mem_cycleTypes {n : ℕ} {mu : Multiset ℕ} :
    mu ∈ cycleTypes n ↔ mu.sum ≤ n ∧ ∀ a ∈ mu, 2 ≤ a := by
  classical
  simp only [cycleTypes, Finset.mem_image, Finset.mem_univ, true_and]
  simpa using (Equiv.Perm.exists_with_cycleType_iff (α := Fin n) (m := mu))

/-- The permutations on `Fin n` having exactly the given (nontrivial)
cycle type. -/
def permutationsOfCycleType (n : ℕ) (mu : Multiset ℕ) : Finset (Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.cycleType = mu

@[simp]
theorem mem_permutationsOfCycleType {n : ℕ} {mu : Multiset ℕ} {σ : Perm (Fin n)} :
    σ ∈ permutationsOfCycleType n mu ↔ σ.cycleType = mu := by
  simp [permutationsOfCycleType]

/-- The denominator of the cycle-index weight associated to `mu` on
`Fin n`.  The first factorial accounts for the omitted fixed points. -/
def cycleDenominator (n : ℕ) (mu : Multiset ℕ) : ℕ :=
  (n - mu.sum).factorial * mu.prod *
    ∏ j ∈ mu.toFinset, (mu.count j).factorial

/-- The rational cycle-index weight associated to a nontrivial cycle type.
It is intended for valid types `mu ∈ cycleTypes n`. -/
def cycleWeight (n : ℕ) (mu : Multiset ℕ) : ℚ :=
  1 / (cycleDenominator n mu : ℚ)

/-- The same exact weight, embedded in the real numbers for analytic
estimates. -/
noncomputable def cycleWeightReal (n : ℕ) (mu : Multiset ℕ) : ℝ :=
  1 / (cycleDenominator n mu : ℝ)

theorem cycleDenominator_pos {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) : 0 < cycleDenominator n mu := by
  rw [mem_cycleTypes] at hmu
  unfold cycleDenominator
  have hprod : 0 < mu.prod :=
    Multiset.prod_pos fun a ha ↦ (Nat.zero_lt_two.trans_le (hmu.2 a ha))
  positivity

theorem card_permutationsOfCycleType (n : ℕ) (mu : Multiset ℕ) :
    #(permutationsOfCycleType n mu) =
      if mu.sum ≤ n ∧ ∀ a ∈ mu, 2 ≤ a then
        n.factorial / cycleDenominator n mu
      else 0 := by
  simpa [permutationsOfCycleType, cycleDenominator] using
    (Equiv.Perm.card_of_cycleType (Fin n) mu)

/-- The integral, division-free form of the cycle-index cardinality formula. -/
theorem card_permutationsOfCycleType_mul_cycleDenominator (n : ℕ)
    (mu : Multiset ℕ) :
    #(permutationsOfCycleType n mu) * cycleDenominator n mu =
      if mu.sum ≤ n ∧ ∀ a ∈ mu, 2 ≤ a then n.factorial else 0 := by
  simpa [permutationsOfCycleType, cycleDenominator] using
    (Equiv.Perm.card_of_cycleType_mul_eq (Fin n) mu)

theorem card_permutationsOfCycleType_mul_cycleDenominator_of_mem
    {n : ℕ} {mu : Multiset ℕ} (hmu : mu ∈ cycleTypes n) :
    #(permutationsOfCycleType n mu) * cycleDenominator n mu = n.factorial := by
  rw [card_permutationsOfCycleType_mul_cycleDenominator, if_pos]
  simpa using (mem_cycleTypes.mp hmu)

theorem card_permutationsOfCycleType_pos {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) : 0 < #(permutationsOfCycleType n mu) := by
  rw [Finset.card_pos]
  rw [mem_cycleTypes] at hmu
  have hmu' :
      mu.sum ≤ Fintype.card (Fin n) ∧ ∀ a ∈ mu, 2 ≤ a := by
    simpa using hmu
  obtain ⟨σ, hσ⟩ :=
    (Equiv.Perm.exists_with_cycleType_iff (α := Fin n) (m := mu)).mpr hmu'
  exact ⟨σ, by simpa using hσ⟩

/-- The normalized form of the cycle-index cardinality formula. -/
theorem cycleTypeProbability_eq_cycleWeight {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) :
    (#(permutationsOfCycleType n mu) : ℚ) / (n.factorial : ℚ) = cycleWeight n mu := by
  have hcard := card_permutationsOfCycleType_mul_cycleDenominator_of_mem hmu
  have hden : (cycleDenominator n mu : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (cycleDenominator_pos hmu))
  have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [cycleWeight, div_eq_iff hfac]
  rw [one_div]
  calc
    (#(permutationsOfCycleType n mu) : ℚ) =
        ((#(permutationsOfCycleType n mu) : ℕ) : ℚ) := rfl
    _ = ((#(permutationsOfCycleType n mu) : ℕ) : ℚ) *
          (cycleDenominator n mu : ℚ) * (cycleDenominator n mu : ℚ)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hden, mul_one]
    _ = (cycleDenominator n mu : ℚ)⁻¹ * (n.factorial : ℚ) := by
        rw [← Nat.cast_mul, hcard]
        ring

/-- Real-valued normalized cycle-index cardinality formula. -/
theorem cycleTypeRealProbability_eq_cycleWeightReal {n : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes n) :
    (#(permutationsOfCycleType n mu) : ℝ) / (n.factorial : ℝ) =
      cycleWeightReal n mu := by
  have hcard := card_permutationsOfCycleType_mul_cycleDenominator_of_mem hmu
  have hden : (cycleDenominator n mu : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (cycleDenominator_pos hmu))
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [cycleWeightReal, div_eq_iff hfac, one_div]
  calc
    (#(permutationsOfCycleType n mu) : ℝ) =
        ((#(permutationsOfCycleType n mu) : ℕ) : ℝ) := rfl
    _ = ((#(permutationsOfCycleType n mu) : ℕ) : ℝ) *
          (cycleDenominator n mu : ℝ) * (cycleDenominator n mu : ℝ)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hden, mul_one]
    _ = (cycleDenominator n mu : ℝ)⁻¹ * (n.factorial : ℝ) := by
        rw [← Nat.cast_mul, hcard]
        ring

/-- Summing the cardinalities of all cycle-type fibers gives all `n!`
permutations. -/
theorem sum_card_permutationsOfCycleType (n : ℕ) :
    ∑ mu ∈ cycleTypes n, #(permutationsOfCycleType n mu) = n.factorial := by
  classical
  have h := Finset.card_eq_sum_card_image
    (fun σ : Perm (Fin n) ↦ σ.cycleType) Finset.univ
  simpa [cycleTypes, permutationsOfCycleType, Fintype.card_perm] using h.symm

/-- The weights of all cycle types on `Fin n` sum to one. -/
theorem sum_cycleWeight (n : ℕ) :
    ∑ mu ∈ cycleTypes n, cycleWeight n mu = 1 := by
  classical
  calc
    ∑ mu ∈ cycleTypes n, cycleWeight n mu =
        ∑ mu ∈ cycleTypes n,
          (#(permutationsOfCycleType n mu) : ℚ) / (n.factorial : ℚ) := by
      apply Finset.sum_congr rfl
      intro mu hmu
      exact (cycleTypeProbability_eq_cycleWeight hmu).symm
    _ = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, sum_card_permutationsOfCycleType]
      exact div_self (by exact_mod_cast Nat.factorial_ne_zero n)

/-! ## The cycle-index formula for an arbitrary event -/

/-- The number of permutations whose nontrivial cycle type satisfies `A`. -/
def cycleTypeEventCount (n : ℕ) (A : Multiset ℕ → Prop) [DecidablePred A] : ℕ :=
  #(Finset.univ.filter fun σ : Perm (Fin n) ↦ A σ.cycleType)

/-- The occurring cycle types satisfying `A`. -/
def cycleTypeEventTypes (n : ℕ) (A : Multiset ℕ → Prop) [DecidablePred A] :
    Finset (Multiset ℕ) :=
  (cycleTypes n).filter A

@[simp]
theorem mem_cycleTypeEventTypes {n : ℕ} {A : Multiset ℕ → Prop} [DecidablePred A]
    {mu : Multiset ℕ} :
    mu ∈ cycleTypeEventTypes n A ↔ mu ∈ cycleTypes n ∧ A mu := by
  simp [cycleTypeEventTypes]

/-- Unnormalized cycle-index formula for an arbitrary predicate on cycle
types. -/
theorem cycleTypeEventCount_eq_sum (n : ℕ) (A : Multiset ℕ → Prop)
    [DecidablePred A] :
    cycleTypeEventCount n A =
      ∑ mu ∈ cycleTypeEventTypes n A, #(permutationsOfCycleType n mu) := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Perm (Fin n))) (cycleTypeEventTypes n A)
      (fun σ ↦ σ.cycleType)
  simpa [cycleTypeEventCount, cycleTypeEventTypes, cycleTypes,
    permutationsOfCycleType] using h.symm

/-- Normalized cycle-index formula for an arbitrary predicate on cycle
types.  This is the exact finite form of equation (2.2) in the mathematical
writeup. -/
theorem cycleTypeEventProbability_eq_sum_cycleWeight
    (n : ℕ) (A : Multiset ℕ → Prop) [DecidablePred A] :
    (cycleTypeEventCount n A : ℚ) / (n.factorial : ℚ) =
      ∑ mu ∈ cycleTypeEventTypes n A, cycleWeight n mu := by
  classical
  rw [cycleTypeEventCount_eq_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact cycleTypeProbability_eq_cycleWeight (mem_cycleTypeEventTypes.mp hmu).1

/-- Real-valued form of the arbitrary-event cycle-index formula. -/
theorem cycleTypeEventRealProbability_eq_sum_cycleWeightReal
    (n : ℕ) (A : Multiset ℕ → Prop) [DecidablePred A] :
    (cycleTypeEventCount n A : ℝ) / (n.factorial : ℝ) =
      ∑ mu ∈ cycleTypeEventTypes n A, cycleWeightReal n mu := by
  classical
  rw [cycleTypeEventCount_eq_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact cycleTypeRealProbability_eq_cycleWeightReal
    (mem_cycleTypeEventTypes.mp hmu).1

/-! ## Prescribed order -/

@[simp]
theorem mem_permutationOrderFiber {n k : ℕ} {σ : Perm (Fin n)} :
    σ ∈ (Finset.univ.filter fun τ : Perm (Fin n) ↦ orderOf τ = k) ↔
      orderOf σ = k := by
  simp

/-- The occurring cycle types whose least common multiple is `k`. -/
def orderCycleTypes (n k : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes n).filter fun mu ↦ mu.lcm = k

@[simp]
theorem mem_orderCycleTypes {n k : ℕ} {mu : Multiset ℕ} :
    mu ∈ orderCycleTypes n k ↔ mu ∈ cycleTypes n ∧ mu.lcm = k := by
  simp [orderCycleTypes]

theorem orderOf_eq_iff_lcm_cycleType_eq {n k : ℕ} {σ : Perm (Fin n)} :
    orderOf σ = k ↔ σ.cycleType.lcm = k := by
  rw [Equiv.Perm.lcm_cycleType]

/-- Exact decomposition of the `orderCount` from `Erdos1161.Basic` into its
cycle-type fibers. -/
theorem orderCount_eq_sum_cycleTypes (n k : ℕ) :
    orderCount n k =
      ∑ mu ∈ orderCycleTypes n k, #(permutationsOfCycleType n mu) := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Perm (Fin n))) (orderCycleTypes n k)
      (fun σ ↦ σ.cycleType)
  simpa [orderCount_eq_card_filter, orderCycleTypes, cycleTypes,
    permutationsOfCycleType, Equiv.Perm.lcm_cycleType] using h.symm

/-- The exact rational cycle-index identity for the order-`k` event. -/
theorem orderCountRationalProbability_eq_sum_cycleWeight (n k : ℕ) :
    (orderCount n k : ℚ) / (n.factorial : ℚ) =
      ∑ mu ∈ orderCycleTypes n k, cycleWeight n mu := by
  classical
  rw [orderCount_eq_sum_cycleTypes, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact cycleTypeProbability_eq_cycleWeight (mem_orderCycleTypes.mp hmu).1

/-- The exact real cycle-index expansion of `orderProbability`. -/
theorem orderProbability_eq_sum_cycleWeightReal (n k : ℕ) :
    orderProbability n k =
      ∑ mu ∈ orderCycleTypes n k, cycleWeightReal n mu := by
  classical
  rw [orderProbability, orderCount_eq_sum_cycleTypes, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact cycleTypeRealProbability_eq_cycleWeightReal (mem_orderCycleTypes.mp hmu).1

/-! ## Residual fixed points and the full cycle-count vector -/

/-- The number of fixed points of a permutation. -/
def fixedPointCount {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  Fintype.card (Function.fixedPoints σ)

@[simp]
theorem fixedPointCount_eq {n : ℕ} (σ : Perm (Fin n)) :
    fixedPointCount σ = n - σ.cycleType.sum := by
  simpa [fixedPointCount] using Equiv.Perm.card_fixedPoints σ

theorem cycleType_sum_add_fixedPointCount {n : ℕ} (σ : Perm (Fin n)) :
    σ.cycleType.sum + fixedPointCount σ = n := by
  rw [fixedPointCount_eq, Nat.add_sub_of_le]
  simpa using σ.sum_cycleType_le

theorem fixedPointCount_of_mem_permutationsOfCycleType
    {n : ℕ} {mu : Multiset ℕ} {σ : Perm (Fin n)}
    (hσ : σ ∈ permutationsOfCycleType n mu) :
    fixedPointCount σ = n - mu.sum := by
  rw [fixedPointCount_eq, (mem_permutationsOfCycleType.mp hσ)]

/-- The complete multiset of cycle lengths, including one copy of `1` for
each fixed point. -/
def fullCycleType {n : ℕ} (σ : Perm (Fin n)) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (fixedPointCount σ) 1

@[simp]
theorem sum_fullCycleType {n : ℕ} (σ : Perm (Fin n)) :
    (fullCycleType σ).sum = n := by
  simpa only [fullCycleType, Multiset.sum_add, Multiset.sum_replicate,
    nsmul_eq_mul, Nat.cast_id, mul_one] using
      cycleType_sum_add_fixedPointCount σ

@[simp]
theorem lcm_fullCycleType {n : ℕ} (σ : Perm (Fin n)) :
    (fullCycleType σ).lcm = orderOf σ := by
  have hone : (Multiset.replicate (fixedPointCount σ) 1).lcm = 1 := by
    induction fixedPointCount σ with
    | zero => simp
    | succ c ih => simp [Multiset.replicate_succ, ih]
  rw [fullCycleType, Multiset.lcm_add, hone, Equiv.Perm.lcm_cycleType]
  simp

@[simp]
theorem count_one_fullCycleType {n : ℕ} (σ : Perm (Fin n)) :
    (fullCycleType σ).count 1 = fixedPointCount σ := by
  have hone : 1 ∉ σ.cycleType := by
    intro h
    have htwo := Equiv.Perm.two_le_of_mem_cycleType h
    omega
  simp [fullCycleType, Multiset.count_eq_zero.mpr hone]

@[simp]
theorem count_fullCycleType_of_two_le {n j : ℕ} (σ : Perm (Fin n)) (hj : 2 ≤ j) :
    (fullCycleType σ).count j = σ.cycleType.count j := by
  have hjone : j ≠ 1 := by omega
  have honej : 1 ≠ j := hjone.symm
  rw [fullCycleType, Multiset.count_add, Multiset.count_replicate]
  simp [honej]

theorem one_le_of_mem_fullCycleType {n a : ℕ} {σ : Perm (Fin n)}
    (ha : a ∈ fullCycleType σ) : 1 ≤ a := by
  rw [fullCycleType, Multiset.mem_add] at ha
  rcases ha with ha | ha
  · exact (Equiv.Perm.two_le_of_mem_cycleType ha).trans' (by omega)
  · rw [Multiset.mem_replicate] at ha
    omega

theorem orderOf_dvd_iff_forall_mem_fullCycleType_dvd
    {n k : ℕ} (σ : Perm (Fin n)) :
    orderOf σ ∣ k ↔ ∀ j ∈ fullCycleType σ, j ∣ k := by
  rw [← lcm_fullCycleType]
  exact Multiset.lcm_dvd

end Erdos1161
