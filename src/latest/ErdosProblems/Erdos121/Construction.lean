import ErdosProblems.Erdos121.Fiber
import ErdosProblems.Erdos121.PrimeBins

/-!
# The finite weighted `K₅` construction

An outcome consists of a controlled global assignment of small primes, a
point in the explicit five-dimensional bin lattice, and one prime in each of
the ten resulting dyadic bins.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

abbrev K5ControlledAssignment (U : ℕ) :=
  {σ : SmallAssignment (smallCutoff U) //
    smallAssignedLog σ ≤ smallLogBudget U}

def k5OutcomeTarget (U : ℕ) (σ : K5ControlledAssignment U) : Fin 5 → ℕ :=
  fun v => k5Target (σ := σ.1) U v

def k5OutcomeBins (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) : Fin 10 → ℕ :=
  k5SolvedBins U (k5OutcomeTarget U σ) t.1

abbrev K5LargePrime (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) (e : Fin 10) :=
  ↥(Erdos888.dyadicPrimes (2 ^ k5OutcomeBins U σ t e))

abbrev K5LargeChoice (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) := ∀ e : Fin 10, K5LargePrime U σ t e

abbrev K5Outcome (U : ℕ) :=
  Σ σ : K5ControlledAssignment U,
    Σ t : K5Parameter U, K5LargeChoice U σ t

def k5OutcomeWeight {U : ℕ} (ω : K5Outcome U) : ℝ :=
  smallAssignmentWeight ω.1.1 * ∏ e, ((ω.2.2 e : ℕ) : ℝ)⁻¹

def k5OutcomeEdge {U : ℕ} (ω : K5Outcome U) (e : Fin 10) : ℕ :=
  smallEdgeFactor ω.1.1 e * (ω.2.2 e : ℕ)

def k5OutcomeTuple {U : ℕ} (ω : K5Outcome U) : Fin 5 → ℕ :=
  k5Tuple (k5OutcomeEdge ω)

def k5Weight (U : ℕ) : FiniteWeight (K5Outcome U) := by
  classical
  exact
    { support := Finset.univ
      weight := k5OutcomeWeight
      weight_nonneg := by
        intro ω hω
        exact mul_nonneg (smallAssignmentWeight_nonneg ω.1.1)
          (Finset.prod_nonneg fun e he => inv_nonneg.mpr (by positivity)) }

lemma k5Outcome_square {U : ℕ} (ω : K5Outcome U) :
    IsSquare (∏ v, k5OutcomeTuple ω v) :=
  isSquare_prod_k5Tuple (k5OutcomeEdge ω)

lemma k5Outcome_target_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    (σ : K5ControlledAssignment U) (v : Fin 5) :
    998 * U / 1000 ≤ k5OutcomeTarget U σ v ∧
      k5OutcomeTarget U σ v ≤ U :=
  k5Target_bounds hU σ.2 v

lemma k5Outcome_bin_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    (σ : K5ControlledAssignment U) (t : K5Parameter U) (e : Fin 10) :
    U / 100 ≤ k5OutcomeBins U σ t e ∧
      k5OutcomeBins U σ t e ≤ U / 2 := by
  have hs := k5Outcome_target_bounds hU σ
  have hi :=
    k5SolvedBinsInt_bounds hU (fun i => (hs i).1) (fun i => (hs i).2) t.2 e
  have hn :=
    k5SolvedBinsInt_nonneg hU (fun i => (hs i).1) (fun i => (hs i).2) t.2 e
  have heq : (k5OutcomeBins U σ t e : ℤ) =
      k5SolvedBinsInt (k5OutcomeTarget U σ) (k5FreeBins U t.1) e := by
    simp [k5OutcomeBins, k5SolvedBins, Int.toNat_of_nonneg hn]
  rw [← heq] at hi
  exact_mod_cast hi

lemma k5Outcome_row_bounds {U : ℕ} (hU : 1000000000 ≤ U)
    (σ : K5ControlledAssignment U) (t : K5Parameter U) (v : Fin 5) :
    k5OutcomeTarget U σ v - 2 ≤ k5BinRow (k5OutcomeBins U σ t) v ∧
      k5BinRow (k5OutcomeBins U σ t) v ≤ k5OutcomeTarget U σ v := by
  have hs := k5Outcome_target_bounds hU σ
  simpa [k5OutcomeBins] using
    k5SolvedBins_row_bounds hU (fun i => (hs i).1) (fun i => (hs i).2) t.2 v

lemma k5Outcome_bins_cross_separated {U : ℕ} (hU : 1000000000 ≤ U)
    (σ σ' : K5ControlledAssignment U) (t t' : K5Parameter U)
    {e f : Fin 10} (hef : e ≠ f) :
    k5OutcomeBins U σ t e + 1 < k5OutcomeBins U σ' t' f ∨
      k5OutcomeBins U σ' t' f + 1 < k5OutcomeBins U σ t e := by
  have hs := k5Outcome_target_bounds hU σ
  have hs' := k5Outcome_target_bounds hU σ'
  exact k5SolvedBinsInt_cross_separated hU
    (fun i => (hs i).1) (fun i => (hs i).2)
    (fun i => (hs' i).1) (fun i => (hs' i).2) t.2 t'.2 hef

lemma sum_inv_k5LargePrime (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) (e : Fin 10) :
    (∑ p : K5LargePrime U σ t e, ((p : ℕ) : ℝ)⁻¹) =
      dyadicPrimeMass (k5OutcomeBins U σ t e) := by
  change (∑ p : ↥(Erdos888.dyadicPrimes (2 ^ k5OutcomeBins U σ t e)),
      ((p.1 : ℕ) : ℝ)⁻¹) = _
  simpa [dyadicPrimeMass] using
    (Finset.sum_attach (Erdos888.dyadicPrimes (2 ^ k5OutcomeBins U σ t e))
      (fun p : ℕ => (p : ℝ)⁻¹))

lemma sum_k5LargeChoice_weight (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) :
    (∑ p : K5LargeChoice U σ t, ∏ e, ((p e : ℕ) : ℝ)⁻¹) =
      ∏ e, dyadicPrimeMass (k5OutcomeBins U σ t e) := by
  calc
    (∑ p : K5LargeChoice U σ t, ∏ e, ((p e : ℕ) : ℝ)⁻¹) =
        ∏ e, ∑ p : K5LargePrime U σ t e, ((p : ℕ) : ℝ)⁻¹ := by
      exact (Fintype.prod_sum (fun e (p : K5LargePrime U σ t e) =>
        ((p : ℕ) : ℝ)⁻¹)).symm
    _ = ∏ e, dyadicPrimeMass (k5OutcomeBins U σ t e) := by
      apply Finset.prod_congr rfl
      intro e he
      exact sum_inv_k5LargePrime U σ t e

def k5LargeVertexProduct {U : ℕ} (ω : K5Outcome U) (v : Fin 5) : ℕ :=
  k5Tuple (fun e => (ω.2.2 e : ℕ)) v

lemma k5OutcomeTuple_factor {U : ℕ} (ω : K5Outcome U) (v : Fin 5) :
    k5OutcomeTuple ω v =
      k5Tuple (smallEdgeFactor ω.1.1) v * k5LargeVertexProduct ω v := by
  fin_cases v <;> simp [k5OutcomeTuple, k5OutcomeEdge,
    k5LargeVertexProduct, k5Tuple] <;> ring

lemma pow_k5BinRow (b : Fin 10 → ℕ) (v : Fin 5) :
    2 ^ k5BinRow b v = k5Tuple (fun e => 2 ^ b e) v := by
  fin_cases v <;> simp [k5BinRow, k5Tuple, pow_add]

lemma pow_k5BinRow_add_four (b : Fin 10 → ℕ) (v : Fin 5) :
    2 ^ (k5BinRow b v + 4) = k5Tuple (fun e => 2 ^ (b e + 1)) v := by
  fin_cases v <;> simp [k5BinRow, k5Tuple, pow_add] <;> ring

private lemma mul_four_lt {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℕ}
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (h₃ : a₃ < b₃) :
    a₀ * a₁ * a₂ * a₃ < b₀ * b₁ * b₂ * b₃ := by
  have hb₀ : 0 < b₀ := ha₀.trans h₀
  have hb₁ : 0 < b₁ := ha₁.trans h₁
  have hb₂ : 0 < b₂ := ha₂.trans h₂
  calc
    a₀ * a₁ * a₂ * a₃ < b₀ * a₁ * a₂ * a₃ := by gcongr
    _ < b₀ * b₁ * a₂ * a₃ := by gcongr
    _ < b₀ * b₁ * b₂ * a₃ := by gcongr
    _ < b₀ * b₁ * b₂ * b₃ := by gcongr

private lemma mul_four_le {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℕ}
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) :
    a₀ * a₁ * a₂ * a₃ ≤ b₀ * b₁ * b₂ * b₃ := by
  gcongr

lemma k5LargeVertexProduct_lower {U : ℕ} (ω : K5Outcome U) (v : Fin 5) :
    2 ^ k5BinRow (k5OutcomeBins U ω.1 ω.2.1) v <
      k5LargeVertexProduct ω v := by
  rw [pow_k5BinRow]
  fin_cases v <;>
    simp only [k5Tuple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue, k5LargeVertexProduct] <;>
    apply mul_four_lt <;>
    first | positivity |
      exact (Erdos888.mem_dyadicPrimes.mp (ω.2.2 _).property).2.1

lemma k5LargeVertexProduct_upper {U : ℕ} (ω : K5Outcome U) (v : Fin 5) :
    k5LargeVertexProduct ω v ≤
      2 ^ (k5BinRow (k5OutcomeBins U ω.1 ω.2.1) v + 4) := by
  rw [pow_k5BinRow_add_four]
  fin_cases v <;>
    simp only [k5Tuple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue, k5LargeVertexProduct] <;>
    apply mul_four_le <;>
    simpa [pow_succ, Nat.mul_comm] using
      (Erdos888.mem_dyadicPrimes.mp (ω.2.2 _).property).2.2

/-- Every coordinate lies in its prescribed vertex-dependent dyadic window. -/
theorem k5OutcomeTuple_window {U : ℕ} (hU : 1000000000 ≤ U)
    (ω : K5Outcome U) (v : Fin 5) :
    2 ^ (U - (100 * v.val + 8)) < k5OutcomeTuple ω v ∧
      k5OutcomeTuple ω v < 2 ^ (U - (100 * v.val + 1)) := by
  let d := k5Tuple (smallEdgeFactor ω.1.1) v
  let l := Nat.log 2 d
  let s := k5OutcomeTarget U ω.1 v
  let r := k5BinRow (k5OutcomeBins U ω.1 ω.2.1) v
  let P := k5LargeVertexProduct ω v
  have hdPos : 0 < d := by
    dsimp [d]
    fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos]
  have hlog := controlled_smallFactor_log_le ω.1.2 v
  have hv : v.val ≤ 4 := by omega
  have hoff : 100 * v.val + 6 ≤ U := by omega
  have hls : l + s + (100 * v.val + 6) = U := by
    dsimp [l, d, s, k5OutcomeTarget, k5Target, k5VertexOffset]
    omega
  have hsBounds := k5Outcome_target_bounds hU ω.1 v
  have hsTwo : 2 ≤ s := by dsimp [s]; omega
  have hrBounds := k5Outcome_row_bounds hU ω.1 ω.2.1 v
  have hdLower : 2 ^ l ≤ d := by
    exact Nat.pow_log_le_self 2 hdPos.ne'
  have hdUpper : d < 2 ^ (l + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
  have hPLower : 2 ^ r < P := by
    exact k5LargeVertexProduct_lower ω v
  have hPUpper : P ≤ 2 ^ (r + 4) := by
    exact k5LargeVertexProduct_upper ω v
  have hpowMonoLower : 2 ^ (s - 2) ≤ 2 ^ r := by
    exact Nat.pow_le_pow_right (by norm_num) hrBounds.1
  have hpowMonoUpper : 2 ^ (r + 4) ≤ 2 ^ (s + 4) := by
    exact Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hrBounds.2 4)
  have hexpLower : l + (s - 2) = U - (100 * v.val + 8) := by omega
  have hexpUpper : (l + 1) + (s + 4) = U - (100 * v.val + 1) := by omega
  rw [k5OutcomeTuple_factor]
  change 2 ^ (U - (100 * v.val + 8)) < d * P ∧
    d * P < 2 ^ (U - (100 * v.val + 1))
  constructor
  · rw [← hexpLower, pow_add]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul hdLower hpowMonoLower)
      (Nat.mul_lt_mul_of_pos_left hPLower hdPos)
  · rw [← hexpUpper, pow_add]
    exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hdUpper
        ((pow_pos (by norm_num : 0 < 2) r).trans hPLower))
      (Nat.mul_le_mul_left _ (hPUpper.trans hpowMonoUpper))

theorem k5OutcomeTuple_le_pow {U : ℕ} (hU : 1000000000 ≤ U)
    (ω : K5Outcome U) (v : Fin 5) : k5OutcomeTuple ω v ≤ 2 ^ U := by
  have h := (k5OutcomeTuple_window hU ω v).2
  exact h.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem k5OutcomeTuple_ge_window {U : ℕ} (hU : 1000000000 ≤ U)
    (ω : K5Outcome U) (v : Fin 5) :
    2 ^ (U - 408) < k5OutcomeTuple ω v := by
  have h := (k5OutcomeTuple_window hU ω v).1
  exact lt_of_le_of_lt
    (Nat.pow_le_pow_right (by norm_num) (by omega)) h

/-- The five magnitude windows are disjoint, so every outcome is injective. -/
theorem k5OutcomeTuple_injective {U : ℕ} (hU : 1000000000 ≤ U)
    (ω : K5Outcome U) : Function.Injective (k5OutcomeTuple ω) := by
  intro v w heq
  apply Fin.ext
  by_contra hvw
  have hvltw : v.val < w.val ∨ w.val < v.val := lt_or_gt_of_ne hvw
  rcases hvltw with hvltw | hwltv
  · have hvLower := (k5OutcomeTuple_window hU ω v).1
    have hwUpper := (k5OutcomeTuple_window hU ω w).2
    have hExp : U - (100 * w.val + 1) ≤ U - (100 * v.val + 8) := by omega
    have hPow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hExp
    omega
  · have hwLower := (k5OutcomeTuple_window hU ω w).1
    have hvUpper := (k5OutcomeTuple_window hU ω v).2
    have hExp : U - (100 * v.val + 1) ≤ U - (100 * w.val + 8) := by omega
    have hPow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hExp
    omega

end

end Erdos121
