import ErdosProblems.Erdos121.BinLattice
import ErdosProblems.Erdos121.SmallFactors

/-!
# Size bounds for the small-prime factors

The global small-prime assignment is restricted by a logarithmic budget.
This file converts that real logarithmic restriction into the natural-number
base-two logarithm bound needed when the dyadic large-prime bins are chosen.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

lemma log_smallAssignedProduct {Y : ℕ} (σ : SmallAssignment Y) :
    Real.log (smallAssignedProduct σ : ℝ) = smallAssignedLog σ := by
  rw [smallAssignedProduct, smallAssignedLog, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro q hq
    by_cases hzero : σ q = 0 <;> simp [hzero]
  · intro q hq
    split
    · norm_num
    · exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.ne_zero

lemma k5Tuple_smallEdgeFactor_dvd_assigned {Y : ℕ}
    (σ : SmallAssignment Y) (v : Fin 5) :
    k5Tuple (smallEdgeFactor σ) v ∣ smallAssignedProduct σ := by
  rw [← prod_smallEdgeFactor]
  fin_cases v
  · simp [k5Tuple, Fin.prod_univ_succ]
    refine ⟨smallEdgeFactor σ 4 * smallEdgeFactor σ 5 * smallEdgeFactor σ 6 *
      smallEdgeFactor σ 7 * smallEdgeFactor σ 8 * smallEdgeFactor σ 9, ?_⟩
    ring
  · simp [k5Tuple, Fin.prod_univ_succ]
    refine ⟨smallEdgeFactor σ 1 * smallEdgeFactor σ 2 * smallEdgeFactor σ 3 *
      smallEdgeFactor σ 7 * smallEdgeFactor σ 8 * smallEdgeFactor σ 9, ?_⟩
    ring
  · simp [k5Tuple, Fin.prod_univ_succ]
    refine ⟨smallEdgeFactor σ 0 * smallEdgeFactor σ 2 * smallEdgeFactor σ 3 *
      smallEdgeFactor σ 5 * smallEdgeFactor σ 6 * smallEdgeFactor σ 9, ?_⟩
    ring
  · simp [k5Tuple, Fin.prod_univ_succ]
    refine ⟨smallEdgeFactor σ 0 * smallEdgeFactor σ 1 * smallEdgeFactor σ 3 *
      smallEdgeFactor σ 4 * smallEdgeFactor σ 6 * smallEdgeFactor σ 8, ?_⟩
    ring
  · simp [k5Tuple, Fin.prod_univ_succ]
    refine ⟨smallEdgeFactor σ 0 * smallEdgeFactor σ 1 * smallEdgeFactor σ 2 *
      smallEdgeFactor σ 4 * smallEdgeFactor σ 5 * smallEdgeFactor σ 7, ?_⟩
    ring

lemma k5Tuple_smallEdgeFactor_le_assigned {Y : ℕ}
    (σ : SmallAssignment Y) (v : Fin 5) :
    k5Tuple (smallEdgeFactor σ) v ≤ smallAssignedProduct σ := by
  exact Nat.le_of_dvd (smallAssignedProduct_pos σ)
    (k5Tuple_smallEdgeFactor_dvd_assigned σ v)

lemma log_k5Tuple_smallEdgeFactor_le {Y : ℕ}
    (σ : SmallAssignment Y) (v : Fin 5) :
    Real.log (k5Tuple (smallEdgeFactor σ) v : ℝ) ≤ smallAssignedLog σ := by
  rw [← log_smallAssignedProduct]
  apply Real.log_le_log
  · exact_mod_cast (by
      fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos σ] :
        0 < k5Tuple (smallEdgeFactor σ) v)
  · exact_mod_cast k5Tuple_smallEdgeFactor_le_assigned σ v

lemma natLog_two_mul_log_two_le_log (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have hpow := Nat.pow_log_le_self 2 hn.ne'
  have hpowPos : (0 : ℝ) < ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by positivity
  have hpowCast : (((2 ^ Nat.log 2 n : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hpow
  have hlog := Real.log_le_log hpowPos hpowCast
  rw [show (((2 ^ Nat.log 2 n : ℕ) : ℝ)) = (2 : ℝ) ^ Nat.log 2 n by
    norm_num, Real.log_pow] at hlog
  simpa using hlog

/-- Every vertex small factor consumes at most one thousandth of the dyadic
logarithmic scale. -/
lemma controlled_smallFactor_log_le {U : ℕ}
    {σ : SmallAssignment (smallCutoff U)}
    (hσ : smallAssignedLog σ ≤ smallLogBudget U) (v : Fin 5) :
    Nat.log 2 (k5Tuple (smallEdgeFactor σ) v) ≤ U / 1000 := by
  let d := k5Tuple (smallEdgeFactor σ) v
  have hdPos : 0 < d := by
    dsimp [d]
    fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos σ]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hchain : (Nat.log 2 d : ℝ) * Real.log 2 ≤
      (U : ℝ) * Real.log 2 / 1000 :=
    (natLog_two_mul_log_two_le_log d hdPos).trans
      ((log_k5Tuple_smallEdgeFactor_le σ v).trans hσ)
  have hreal : (Nat.log 2 d : ℝ) ≤ (U : ℝ) / 1000 := by
    nlinarith
  have hcast : (1000 * Nat.log 2 d : ℝ) ≤ (U : ℝ) := by
    nlinarith
  have hnat : 1000 * Nat.log 2 d ≤ U := by exact_mod_cast hcast
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 1000)).2 (by
    simpa [Nat.mul_comm] using hnat)

/-- A fixed dyadic offset that places the five output coordinates in pairwise
disjoint magnitude windows. -/
def k5VertexOffset (v : Fin 5) : ℕ := 100 * v.val + 6

/-- Target row sum for the four large-prime bins incident to a vertex.  The
vertex-dependent offset is mathematically inessential, but makes injectivity
of every resulting tuple immediate from its size bounds. -/
def k5Target (U : ℕ) {σ : SmallAssignment (smallCutoff U)} (v : Fin 5) : ℕ :=
  U - Nat.log 2 (k5Tuple (smallEdgeFactor σ) v) - k5VertexOffset v

lemma k5Target_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    {σ : SmallAssignment (smallCutoff U)}
    (hσ : smallAssignedLog σ ≤ smallLogBudget U) (v : Fin 5) :
    998 * U / 1000 ≤ k5Target (σ := σ) U v ∧
      k5Target (σ := σ) U v ≤ U := by
  have hlog := controlled_smallFactor_log_le hσ v
  have hv : v.val ≤ 4 := by omega
  unfold k5Target
  simp only [k5VertexOffset]
  omega

end

end Erdos121
