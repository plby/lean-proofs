/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Averaging

/-! # The sparse half of the target graph -/

namespace Erdos569

open Erdos79 Erdos570

theorem edgeCount_le_choose (H : GraphCode) :
    H.edgeCount ≤ H.vertexCount.choose 2 := by
  classical
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  simpa using H.graph.card_edgeFinset_le_card_choose_two

/-- The partition chosen by averaging in the manuscript, without a
probability space or division in the conclusion. -/
theorem exists_sparse_half_exact (H : GraphCode) (hn : 3 ≤ H.vertexCount)
    (hm : 0 < H.edgeCount) :
    ∃ S : Finset (Fin H.vertexCount),
      S.card = H.vertexCount - (H.vertexCount / 2 + 1) ∧
      4 * (inducedCode H S).edgeCount < H.edgeCount ∧
      (inducedCode H S).edgeCount * (H.vertexCount * (H.vertexCount - 1)) ≤
        H.edgeCount * ((H.vertexCount - (H.vertexCount / 2 + 1)) *
          (H.vertexCount - (H.vertexCount / 2 + 1) - 1)) := by
  let n := H.vertexCount
  let r := n - (n / 2 + 1)
  have hrn : r ≤ H.vertexCount := Nat.sub_le _ _
  by_cases hr2 : 2 ≤ r
  · obtain ⟨S, hS, havg⟩ := exists_inducedCode_edgeCount_mul_order_le H hr2 hrn
    refine ⟨S, hS, ?_, havg⟩
    have hnp : 0 < n - 1 := by dsimp [n]; omega
    have hr : 2 * r ≤ n - 1 := by dsimp [r]; omega
    have hrp : 2 * (r - 1) ≤ n - 3 := by omega
    have hprod : 4 * (r * (r - 1)) < n * (n - 1) := by
      calc
        4 * (r * (r - 1)) = (2 * r) * (2 * (r - 1)) := by ring
        _ ≤ (n - 1) * (n - 3) := Nat.mul_le_mul hr hrp
        _ < (n - 1) * n := Nat.mul_lt_mul_of_pos_left (by dsimp [n]; omega) hnp
        _ = n * (n - 1) := by ring
    have hstrict := Nat.mul_lt_mul_of_pos_left hprod hm
    have hscaled := Nat.mul_le_mul_left 4 havg
    have hdenom : 0 < n * (n - 1) := Nat.mul_pos (by dsimp [n]; omega) hnp
    have hresult : (4 * (inducedCode H S).edgeCount) * (n * (n - 1)) <
        H.edgeCount * (n * (n - 1)) := by
      dsimp only [n] at *
      nlinarith [hscaled, hstrict]
    exact (Nat.mul_lt_mul_right hdenom).mp hresult
  · obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin H.vertexCount))) (by simpa using hrn)
    refine ⟨S, hS, ?_⟩
    have he := edgeCount_le_choose (inducedCode H S)
    rw [inducedCode_vertexCount, hS] at he
    have hchoose : r.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose] at he
    have he0 : (inducedCode H S).edgeCount = 0 := Nat.eq_zero_of_le_zero he
    constructor
    · simpa only [he0, mul_zero] using hm
    · simp only [he0, zero_mul, Nat.zero_le]

end Erdos569
