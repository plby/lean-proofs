import ErdosProblems.Erdos720.Tripartite
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Erdos720

lemma linear_le_pow_two (C t : ℕ) (hC : 1 ≤ C) (ht : 16 * C ≤ t) :
    C * (4 * t + 3) ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base =>
      calc
        C * (4 * (16 * C) + 3) ≤ 2 * (8 * C) ^ 2 + 1 := by nlinarith
        _ ≤ 2 ^ (2 * (8 * C)) := Nat.two_mul_sq_add_one_le_two_pow_two_mul _
        _ = 2 ^ (16 * C) := by congr 1 <;> omega
  | succ t ht ih =>
      calc
        C * (4 * (t + 1) + 3) ≤ 2 * (C * (4 * t + 3)) := by nlinarith
        _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (t + 1) := by rw [pow_succ]; omega

lemma mul_le_two_pow_quarter {C n : ℕ} (hC : 1 ≤ C)
    (hn : 64 * C ≤ n) : C * n ≤ 2 ^ (n / 4) := by
  have ht : 16 * C ≤ n / 4 := by omega
  calc
    C * n ≤ C * (4 * (n / 4) + 3) := by
      apply Nat.mul_le_mul_left
      omega
    _ ≤ 2 ^ (n / 4) := linear_le_pow_two C (n / 4) hC ht

lemma clog_mul_le_quarter {c n : ℕ} (hc : c ≤ 258) (hn : 16512 ≤ n) :
    Nat.clog 2 (c * n) ≤ n / 4 := by
  apply Nat.clog_le_of_le_pow
  calc
    c * n ≤ 258 * n := Nat.mul_le_mul_right n hc
    _ ≤ 2 ^ (n / 4) := mul_le_two_pow_quarter (C := 258) (by omega) (by omega)

lemma pow_clog_two_bounds {m : ℕ} (hm : 2 ≤ m) :
    m ≤ 2 ^ Nat.clog 2 m ∧ 2 ^ Nat.clog 2 m ≤ 2 * m := by
  have hlo : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by omega) m
  have hh : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) (by omega)
  have hpred : 2 ^ (Nat.clog 2 m).pred < m :=
    Nat.pow_pred_clog_lt_self (by omega) (by omega)
  have hsucc : (Nat.clog 2 m).pred + 1 = Nat.clog 2 m := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hh
  refine ⟨hlo, ?_⟩
  rw [← hsucc, pow_succ]
  omega

lemma clog_height_data {c n : ℕ} (hcpos : 1 ≤ c) (hc : c ≤ 258)
    (hn : 16512 ≤ n) :
    let m := c * n
    let height := Nat.clog 2 m
    1 ≤ m ∧ n ≤ m ∧ 0 < height ∧
      m ≤ 2 ^ height ∧ 2 ^ height ≤ 2 * m ∧ 2 * height + 2 < n := by
  dsimp
  have hm : 2 ≤ c * n := by nlinarith
  have hb := pow_clog_two_bounds hm
  have hheight := clog_mul_le_quarter hc hn
  have hh : 0 < Nat.clog 2 (c * n) := Nat.clog_pos (by omega) (by nlinarith)
  refine ⟨by omega, by nlinarith, hh, hb.1, hb.2, ?_⟩
  omega

lemma clog_height_data_between {m n : ℕ} (hn : 16512 ≤ n)
    (hnm : n ≤ m) (hmn : m ≤ 258 * n) :
    let height := Nat.clog 2 m
    1 ≤ m ∧ n ≤ m ∧ 0 < height ∧
      m ≤ 2 ^ height ∧ 2 ^ height ≤ 2 * m ∧ 2 * height + 2 < n := by
  dsimp
  have hm : 2 ≤ m := by omega
  have hb := pow_clog_two_bounds hm
  have hheight : Nat.clog 2 m ≤ n / 4 := by
    apply Nat.clog_le_of_le_pow
    exact hmn.trans (mul_le_two_pow_quarter (C := 258) (by omega) (by omega))
  have hh : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) (by omega)
  refine ⟨by omega, hnm, hh, hb.1, hb.2, ?_⟩
  omega

lemma clog_height_data_linear {C m n : ℕ} (hC : 1 ≤ C)
    (hn : 64 * C ≤ n) (hnm : n ≤ m) (hmn : m ≤ C * n) :
    let height := Nat.clog 2 m
    1 ≤ m ∧ n ≤ m ∧ 0 < height ∧
      m ≤ 2 ^ height ∧ 2 ^ height ≤ 2 * m ∧ 2 * height + 2 < n := by
  dsimp
  have hm : 2 ≤ m := by omega
  have hb := pow_clog_two_bounds hm
  have hheight : Nat.clog 2 m ≤ n / 4 := by
    apply Nat.clog_le_of_le_pow
    exact hmn.trans (mul_le_two_pow_quarter hC hn)
  have hh : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) (by omega)
  refine ⟨by omega, hnm, hh, hb.1, hb.2, ?_⟩
  omega

end Erdos720
