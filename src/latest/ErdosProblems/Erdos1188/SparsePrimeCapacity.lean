import ErdosProblems.Erdos1188.SparseClosing
import ErdosProblems.Erdos1188.PrimeLinearLog

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit prime and cross-pair capacity bounds for sparse frames
-/

namespace Erdos1188

open scoped BigOperators

/-- Binary-log parameter used throughout the sparse construction. -/
def sparseLog (i : ℕ) : ℕ := Nat.log 2 (i + 1) + 1

/-- Number of low coordinates allowed in a cross pair. -/
def sparseHeight (i : ℕ) : ℕ := 2048 * sparseLog i

/-- A fixed threshold after which binary logarithms are dominated by the
coordinate index with ample room for the cross-pair argument. -/
def sparseSeed : ℕ := 2 ^ 21 - 1

/-- Exponential domination needed for the explicit threshold. -/
theorem linear_le_two_pow_sub_one {k : ℕ} (hk : 21 ≤ k) :
    4096 * (k + 1) ≤ 2 ^ k - 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk hrec =>
      rw [pow_succ]
      have hp0 : 0 < 2 ^ k := pow_pos (by decide) k
      omega

set_option maxRecDepth 100000 in
/-- Past `sparseSeed`, twice the low-coordinate budget is at most the current
index. -/
theorem two_sparseHeight_le {i : ℕ} (hi : sparseSeed ≤ i) :
    2 * sparseHeight i ≤ i := by
  set k := Nat.log 2 (i + 1) with hkdef
  have hs : 2 ^ 21 ≤ i + 1 := by
    unfold sparseSeed at hi
    omega
  have hk : 21 ≤ k := by
    rw [hkdef]
    exact Nat.le_log_of_pow_le (by decide) hs
  have hlin := linear_le_two_pow_sub_one hk
  have hs0 : i + 1 ≠ 0 := by omega
  have hp0 := Nat.pow_log_le_self 2 hs0
  have hp : 2 ^ k ≤ i + 1 := by simpa [hkdef] using hp0
  unfold sparseHeight sparseLog
  rw [← hkdef]
  clear hkdef hp0 hs0 hs hk
  omega

/-- In particular the cross-pair split is proper and nonempty. -/
theorem sparseHeight_pos (i : ℕ) : 0 < sparseHeight i := by
  simp [sparseHeight, sparseLog]

theorem sparseHeight_lt {i : ℕ} (hi : sparseSeed ≤ i) :
    sparseHeight i < i := by
  have htwo := two_sparseHeight_le hi
  have hpos := sparseHeight_pos i
  omega

/-- Convenient upper bound replacing `2^sparseLog` by twice the index. -/
theorem two_pow_sparseLog_le (i : ℕ) :
    2 ^ sparseLog i ≤ 2 * (i + 1) := by
  have hs0 : i + 1 ≠ 0 := by omega
  have hp := Nat.pow_log_le_self 2 hs0
  unfold sparseLog
  rw [pow_succ]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hp

/-- The cross-pair pool contains at least twice as many supports as needed for
the nonzero residues of the indexed prime. -/
theorem twice_nthPrime_sub_one_le_crossCapacity {i : ℕ}
    (hi : sparseSeed ≤ i) :
    2 * (nthPrime i - 1) ≤ sparseHeight i * (i - sparseHeight i) := by
  let r := sparseLog i
  let h := sparseHeight i
  have hp0 := nthPrime_le_binary_log i
  have hpow := two_pow_sparseLog_le i
  have hp : nthPrime i ≤ 256 * r * (i + 1) := by
    calc
      nthPrime i ≤ 128 * r * 2 ^ r := by simpa [r, sparseLog] using hp0
      _ ≤ 128 * r * (2 * (i + 1)) := Nat.mul_le_mul_left (128 * r) hpow
      _ = 256 * r * (i + 1) := by ring
  have htwo : 2 * h ≤ i := by simpa [h] using two_sparseHeight_le hi
  have hi1 : 1 ≤ i := by
    unfold sparseSeed at hi
    omega
  have hlin : i + 1 ≤ 4 * (i - h) := by omega
  calc
    2 * (nthPrime i - 1) ≤ 2 * nthPrime i :=
      Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
    _ ≤ 512 * r * (i + 1) := by
      have := Nat.mul_le_mul_left 2 hp
      nlinarith
    _ ≤ 512 * r * (4 * (i - h)) := Nat.mul_le_mul_left (512 * r) hlin
    _ = h * (i - h) := by simp [h, sparseHeight]; ring

/-- Indexed primes grow at least one per index. -/
theorem index_add_two_le_nthPrime (i : ℕ) : i + 2 ≤ nthPrime i := by
  induction i with
  | zero => simp [nthPrime, Nat.nth_prime_zero_eq_two]
  | succ i ih =>
      have hs : nthPrime i < nthPrime (i + 1) :=
        nthPrime_strictMono (Nat.lt_succ_self i)
      omega

/-- Indexed primes are nonzero, exposed as an instance for dependent products. -/
instance nthPrime_neZero (i : ℕ) : NeZero (nthPrime i) :=
  ⟨(nthPrime_prime i).ne_zero⟩

/-- Pairwise coprimality after adjoining the next indexed prime as the closing
factor. -/
theorem sparseNthPrime_pairwise_coprime (m : ℕ) :
    Pairwise (Function.onFun Nat.Coprime
      (sparseFactors (fun i : Fin m => nthPrime i.val) (nthPrime m))) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some j =>
          exact nthPrime_pairwise_coprime (by omega)
  | some i =>
      cases b with
      | none =>
          exact nthPrime_pairwise_coprime (by omega)
      | some j =>
          apply nthPrime_pairwise_coprime
          intro hij
          apply hab
          congr
          exact Fin.ext hij

/-- The indexed-prime frame always has an unrestricted default assignment. -/
noncomputable def primeDefaultAssignment (m : ℕ) :
    FrameAssignment (fun i : Fin m => nthPrime i.val) :=
  Classical.choice (frameAssignment_nonempty
    (fun i : Fin m => nthPrime i.val)
    (fun i => nthPrime_sub_one_le_two_pow i.val))

/-- The sparse mixed support family for indexed primes. -/
noncomputable abbrev PrimeSparsePool (m : ℕ) (i : Fin m) :=
  SparseSupportPool (fun j : Fin m => nthPrime j.val)
    sparseSeed sparseHeight
    (fun j hj => (sparseHeight_lt hj).le)
    (primeDefaultAssignment m) i

/-- Its canonical support embedding. -/
noncomputable def primeSparsePoolSupport (m : ℕ) (i : Fin m) :
    PrimeSparsePool m i ↪ Finset (Fin i.val) :=
  sparsePoolSupport (fun j : Fin m => nthPrime j.val)
    sparseSeed sparseHeight
    (fun j hj => (sparseHeight_lt hj).le)
    (primeDefaultAssignment m) i

/-- Exact late pool cardinality and its useful capacity bound. -/
theorem primeSparsePool_late_capacity {m : ℕ} (i : Fin m)
    (hi : sparseSeed ≤ i.val) :
    2 * (nthPrime i.val - 1) ≤ Fintype.card (PrimeSparsePool m i) := by
  rw [card_sparseSupportPool_of_late
    (fun j : Fin m => nthPrime j.val) sparseSeed sparseHeight
    (fun j hj => (sparseHeight_lt hj).le) (primeDefaultAssignment m) i hi]
  exact twice_nthPrime_sub_one_le_crossCapacity hi

/-- Early pools have exactly the required size. -/
theorem primeSparsePool_early_card {m : ℕ} (i : Fin m)
    (hi : ¬ sparseSeed ≤ i.val) :
    Fintype.card (PrimeSparsePool m i) = nthPrime i.val - 1 := by
  exact card_sparseSupportPool_of_early
    (fun j : Fin m => nthPrime j.val) sparseSeed sparseHeight
    (fun j hj => (sparseHeight_lt hj).le) (primeDefaultAssignment m) i hi

end Erdos1188
