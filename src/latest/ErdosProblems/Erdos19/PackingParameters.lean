import Mathlib.Tactic

/-! # Integer parameter margins for prescribed matching packing -/

namespace Erdos19

theorem packing_parameter_margins (n k m a L : ℕ) (hk : 8 ≤ k)
    (hn : 10000 * k * k ≤ n)
    (hm : k * m + 4 * n ≤ k * n)
    (ha : 10000 * k * k * a ≤ n) (hL : 10000 * k * k * L ≤ n) :
    let r := n / k + 1
    let q := n / (100 * k) + 1
    let b := n / (1000 * k * k)
    r + m + 3 * a ≤ n ∧
    n ≤ k * (n - r - m - 3 * a + 1) ∧
    n ≤ (1000 * k * k) * (b + 1) ∧
    b ≤ n - r - m - 3 * a ∧
    2 * q + 2 * b + 7 * (k * (5 * a + L + 1)) + 2 * a + L + 1 ≤ r ∧
    2 * k * (L + 1) ≤ q := by
  dsimp only
  let r := n / k + 1
  let q := n / (100 * k) + 1
  let b := n / (1000 * k * k)
  have hkpos : 0 < k := by omega
  have hk100 : 100 * k ≤ n := by
    have hc : 100 * k ≤ 10000 * k * k := by nlinarith
    exact hc.trans hn
  have hkr : k * r ≤ n + k := by
    have hd := Nat.div_mul_le_self n k
    dsimp only [r]
    nlinarith only [hd]
  have hrk : n ≤ k * r := by
    have hd := Nat.lt_mul_div_succ n hkpos
    exact hd.le
  have hqa : 100 * k * q ≤ n + 100 * k := by
    have hd := Nat.div_mul_le_self n (100 * k)
    dsimp only [q]
    nlinarith only [hd]
  have hqlo : n < 100 * k * q := Nat.lt_mul_div_succ n (by positivity)
  have hba : (1000 * k * k) * b ≤ n := by
    dsimp only [b]
    nlinarith only [Nat.div_mul_le_self n (1000 * k * k)]
  have hbad : n ≤ (1000 * k * k) * (b + 1) :=
    (Nat.lt_mul_div_succ n (by positivity)).le
  have hka : 3 * k * a ≤ n := by
    have hc : 3 * k ≤ 10000 * k * k := by nlinarith
    exact (Nat.mul_le_mul_right a hc).trans ha
  have hkn : k ≤ n := by omega
  have htotal : k * (r + m + 3 * a) + n ≤ k * n := by
    nlinarith only [hkr, hm, hka, hkn]
  have hri : r + m + 3 * a ≤ n := by
    have hm' : k * (r + m + 3 * a) ≤ k * n := by omega
    exact Nat.le_of_mul_le_mul_left hm' hkpos
  have hsub : n - r - m - 3 * a + r + m + 3 * a = n := by omega
  have hsize : n ≤ k * (n - r - m - 3 * a) := by
    have heq := congrArg (fun x ↦ k * x) hsub
    nlinarith only [htotal, heq]
  have hbk : k * b ≤ n := by
    have hc : k ≤ 1000 * k * k := by nlinarith
    exact (Nat.mul_le_mul_right b hc).trans hba
  have hb : b ≤ n - r - m - 3 * a :=
    Nat.le_of_mul_le_mul_left (hbk.trans hsize) hkpos
  have hqsmall : 8 * k * q ≤ n := by nlinarith only [hqa, hk100]
  have hbsmall : 8 * k * b ≤ n := by
    have hc : 8 * k ≤ 1000 * k * k := by nlinarith
    exact (Nat.mul_le_mul_right b hc).trans hba
  have hrepair : 28 * k * k * (5 * a + L + 1) ≤ n := by
    nlinarith only [ha, hL, hn]
  have herror' : 4 * k * k * (2 * a + L + 1) ≤ n := by
    nlinarith only [ha, hL, hn]
  have herror : 4 * k * (2 * a + L + 1) ≤ n := by
    have hc : 4 * k ≤ 4 * k * k := by nlinarith
    exact (Nat.mul_le_mul_right (2 * a + L + 1) hc).trans herror'
  have hmargin : 2 * q + 2 * b + 7 * (k * (5 * a + L + 1)) + 2 * a + L + 1 ≤ r := by
    have hmul : k * (2 * q + 2 * b + 7 * (k * (5 * a + L + 1)) + 2 * a + L + 1) ≤ k * r := by
      nlinarith only [hqsmall, hbsmall, hrepair, herror, hrk]
    exact Nat.le_of_mul_le_mul_left hmul hkpos
  have hcut' : 200 * k * k * (L + 1) ≤ n := by nlinarith only [hL, hn]
  have hcut : 2 * k * (L + 1) ≤ q := by
    have hmul : (100 * k) * (2 * k * (L + 1)) ≤ (100 * k) * q := by
      nlinarith only [hcut', hqlo]
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  exact ⟨hri, hsize.trans (Nat.mul_le_mul_left k (Nat.le_succ _)), hbad, hb, hmargin, hcut⟩

#print axioms packing_parameter_margins

end Erdos19
