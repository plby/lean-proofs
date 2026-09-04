/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueRamsey
import ErdosProblems.Erdos570.OddArithmetic
import ErdosProblems.Erdos570.Support

/-!
# The dense connected-target input

The EFRS polynomial cycle--clique bound is subquadratic for every fixed
cycle of length at least five.  This file records explicit natural-number
constants and proves that it is below `2m` whenever the target order is at
most the square-root scale used by the main induction.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

def oddDenseA (D k : ℕ) : ℕ := 2 * D * k

def oddDenseK (D k : ℕ) : ℕ :=
  (k * (oddDenseA D k + 2) + 1) * oddDenseA D k

def oddDenseThreshold (D k : ℕ) : ℕ :=
  (oddDenseK D k + 1) ^ 4

/-- The EFRS numerical bound is at most `2m` in the dense regime, above an
explicit fourth-power threshold. -/
theorem efrs_dense_numeric
    {D k m n : ℕ} (hD : 2 ≤ D) (hk : 5 ≤ k)
    (hm : oddDenseThreshold D k < m)
    (hn : n < 2 * D * (k * Nat.sqrt (2 * m))) :
    let q := Nat.sqrt (2 * m)
    let a := oddDenseA D k * (Nat.sqrt q + 1)
    n ≤ a ^ ((k - 1) / 2) ∧
      ((k - 2) * (a + 2) + 1) * (n - 1) ≤ 2 * m := by
  dsimp only
  let A := oddDenseA D k
  let K := oddDenseK D k
  let q := Nat.sqrt (2 * m)
  let s := Nat.sqrt q + 1
  have hApos : 0 < A := by
    dsimp [A, oddDenseA]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hKpos : 0 < K := by
    dsimp [K, oddDenseK]
    exact Nat.mul_pos (by positivity) hApos
  have hnAq : n ≤ A * q := by
    simp only [A, q, oddDenseA]
    simpa [mul_assoc] using hn.le
  have hq_lt_s2 : q < s ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' q
  have hn_a2 : n ≤ (A * s) ^ 2 := by
    calc
      n ≤ A * q := hnAq
      _ ≤ A * (s ^ 2) := Nat.mul_le_mul_left A hq_lt_s2.le
      _ ≤ A ^ 2 * s ^ 2 := by
        have hAA : A ≤ A ^ 2 := by
          simp only [pow_two]
          nlinarith
        nlinarith
      _ = (A * s) ^ 2 := by ring
  have ht : 2 ≤ (k - 1) / 2 := by omega
  have haPos : 0 < A * s := Nat.mul_pos hApos (by simp [s])
  have hnPow : n ≤ (A * s) ^ ((k - 1) / 2) :=
    hn_a2.trans (Nat.pow_le_pow_right haPos ht)
  have hKsq_q : (K + 1) ^ 2 ≤ q := by
    rw [show q = Nat.sqrt (2 * m) by rfl]
    apply Nat.le_sqrt.mpr
    have hthreshold : (K + 1) ^ 4 < m := by
      simpa [K, oddDenseThreshold] using hm
    nlinarith [hthreshold]
  have hK_sqrtq : K + 1 ≤ Nat.sqrt q := Nat.le_sqrt'.mpr hKsq_q
  have hsqrtqSq : Nat.sqrt q ^ 2 ≤ q := Nat.sqrt_le' q
  have hKs : K * s ≤ q := by
    simp only [s]
    nlinarith
  have hcoef : (k - 2) * (A * s + 2) + 1 ≤
      (k * (A + 2) + 1) * s := by
    have hspos : 1 ≤ s := by simp [s]
    have hsmall : (2 * k + 1) ≤ (2 * k + 1) * s := by
      simpa using Nat.mul_le_mul_left (2 * k + 1) hspos
    calc
      (k - 2) * (A * s + 2) + 1 ≤ k * (A * s + 2) + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (A * s + 2) (Nat.sub_le k 2)) 1
      _ = k * A * s + (2 * k + 1) := by ring
      _ ≤ k * A * s + (2 * k + 1) * s := Nat.add_le_add_left hsmall _
      _ = (k * (A + 2) + 1) * s := by ring
  have hcoefName : (k * (A + 2) + 1) * A = K := by
    simp [K, oddDenseK, A]
  have hbound : ((k - 2) * (A * s + 2) + 1) * (n - 1) ≤ q * q := by
    calc
      ((k - 2) * (A * s + 2) + 1) * (n - 1) ≤
          ((k * (A + 2) + 1) * s) * (A * q) :=
        Nat.mul_le_mul hcoef (by omega)
      _ = K * s * q := by rw [← hcoefName]; ring
      _ ≤ q * q := Nat.mul_le_mul_right q hKs
  have hqSq : q * q ≤ 2 * m := by
    exact Nat.sqrt_le (2 * m)
  simpa [A, s] using And.intro hnPow (hbound.trans hqSq)

/-- The dense connected-target hypothesis required by
`strongOddCycleBound_of_connected_extremes`, now proved from EFRS. -/
theorem odd_dense_connected_input
    {k D B s M₀ : ℕ} (hk : 5 ≤ k) (hD : 2 ≤ D)
    (hthreshold : oddDenseThreshold D k ≤ M₀) :
    ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      H.vertexCount < 2 * D *
        (k * Nat.sqrt (2 * H.edgeCount)) →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget B s H.edgeCount := by
  intro H hH hconn hm horder
  let n := H.vertexCount
  let q := Nat.sqrt (2 * H.edgeCount)
  let a := oddDenseA D k * (Nat.sqrt q + 1)
  have hn₂ : 2 ≤ n := by
    let : Nonempty (Fin n) := by simpa [n] using hconn.nonempty
    let v : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
    obtain ⟨w, hvw⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH v)
    let : Nontrivial (Fin n) := ⟨⟨v, w, hvw.ne⟩⟩
    have h := Fintype.one_lt_card (α := Fin n)
    simp only [Fintype.card_fin] at h
    omega
  have ha : 1 ≤ a := by
    have hA : 0 < oddDenseA D k := by
      simp only [oddDenseA]
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have : 0 < a := by
      exact Nat.mul_pos hA (by simp [a])
    omega
  have hnumeric := efrs_dense_numeric hD hk
    (hthreshold.trans_lt hm) (by simpa [n] using horder)
  have hnPow : n ≤ a ^ ((k - 1) / 2) := by
    simpa [a, q] using hnumeric.1
  have hramComplete := graphRamseyNumber_cycle_complete_le_efrs
    (m := k) (a := a) (n := n) (by omega) ha hn₂ hnPow
  have hramTarget := graphRamseyNumber_le_complete_of_vertexCount_le
    (cycleCode k) H (n := n) (by simp [n])
  have hpoly : ((k - 2) * (a + 2) + 1) * (n - 1) ≤
      2 * H.edgeCount := by
    simpa [a, q, n] using hnumeric.2
  exact hramTarget.trans (hramComplete.trans (hpoly.trans (by
    unfold oddBudget
    omega)))

end Erdos570
