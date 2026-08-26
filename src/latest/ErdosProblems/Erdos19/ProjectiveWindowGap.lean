import ErdosProblems.Erdos19.Core

/-! # Separating a narrow rank window from the projective threshold -/

namespace Erdos19

theorem projectiveScale_ge_of_large_card (K n : ℕ) (hn : K * K + K + 2 ≤ n) :
    K ≤ projectiveScale n := by
  by_contra hnot
  have hk : projectiveScale n ≤ K := by omega
  have hupper := le_projectiveScale_sq_add n
  have hsq := Nat.mul_le_mul hk hk
  omega

theorem subprojective_window_gap_arithmetic (n k r b : ℕ)
    (hk : 65536 ≤ k) (hb : 8192 ≤ b)
    (hn : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hr : r < k - k / 1024) :
    8192 * (r + r / b) ^ 2 ≤ (8192 - 2) * n := by
  have hkdiv := Nat.lt_mul_div_succ k (by norm_num : 0 < 1024)
  have hr' : r + k / 1024 + 1 ≤ k := by omega
  have hrscale : 1024 * r ≤ 1023 * k := by nlinarith only [hkdiv, hr']
  have hwidth : 8192 * (r / b) ≤ r :=
    (Nat.mul_le_mul_right _ hb).trans (Nat.mul_div_le r b)
  have hR : 2048 * (r + r / b) ≤ 2047 * k := by nlinarith only [hrscale, hwidth]
  have hR2 := Nat.pow_le_pow_left hR 2
  have hksub : k - 1 + 1 = k := by omega
  have hn' : k ^ 2 + 2 ≤ n + k := by nlinarith only [hn, hksub]
  have hksq : 65536 * k ≤ k ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right k hk
  norm_num only [Nat.reduceSub]
  nlinarith only [hR2, hn', hksq]

theorem subprojective_window_gap (n r b : ℕ)
    (hk : 65536 ≤ projectiveScale n) (hb : 8192 ≤ b)
    (hr : r < projectiveScale n - projectiveScale n / 1024) :
    8192 * (r + r / b) ^ 2 ≤ (8192 - 2) * n := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  exact subprojective_window_gap_arithmetic n (projectiveScale n) r b hk hb
    (projectiveScale_pred_sq_add_le hn) hr

#print axioms subprojective_window_gap

/-- Tunable version of the separation estimate: the gap `1/t` below the
projective scale is arbitrary, with all constants explicit. -/
theorem subprojective_window_gap_arithmetic_parametric (n k r b t : ℕ)
    (ht : 1024 ≤ t) (hk : 64 * t ≤ k) (hb : 8 * t ≤ b)
    (hn : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hr : r < k - k / t) :
    (8 * t) * (r + r / b) ^ 2 ≤ (8 * t - 2) * n := by
  have htpos : 0 < t := by omega
  have hfloor := Nat.lt_mul_div_succ k htpos
  have hr' : r + k / t + 1 ≤ k := by omega
  have hrmul := Nat.mul_le_mul_left t hr'
  have hpred : (t - 1) * k + k = t * k := by
    rw [← add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ t)]
  have hrscale : t * r ≤ (t - 1) * k := by
    nlinarith only [hfloor, hrmul, hpred]
  have hwidth : 8 * t * (r / b) ≤ r :=
    (Nat.mul_le_mul_right _ hb).trans (Nat.mul_div_le r b)
  have hpred2 : (2 * t - 1) * k + k = 2 * t * k := by
    rw [← add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ 2 * t)]
  have hR : 2 * t * (r + r / b) ≤ (2 * t - 1) * k := by
    have hrk : r ≤ k := (Nat.le_of_lt hr).trans (Nat.sub_le _ _)
    nlinarith only [hrscale, hwidth, hpred, hpred2, hrk]
  have hR2 := Nat.pow_le_pow_left hR 2
  have hkpred : k - 1 + 1 = k := by omega
  have hn' : k ^ 2 + 2 ≤ n + k := by nlinarith only [hn, hkpred]
  let a := t * (4 * t - 1)
  let c := 3 * t - 1
  have hc : 0 < c := by dsimp only [c]; omega
  have h1 : 2 * t - 1 + 1 = 2 * t := by omega
  have h2 : 4 * t - 1 + 1 = 4 * t := by omega
  have h3 : c + 1 = 3 * t := by dsimp only [c]; omega
  have hid : (2 * t - 1) ^ 2 + c = a := by
    dsimp only [a]
    nlinarith only [h1, h2, h3]
  have hcoeff : a ≤ c * k := by
    have hmul := Nat.mul_le_mul_left c hk
    have hc2 : 2 * t ≤ c := by omega
    have hc2mul := Nat.mul_le_mul_right (64 * t) hc2
    dsimp only [a]
    nlinarith only [hmul, hc2mul, h2]
  have hcoeffk := Nat.mul_le_mul_right k hcoeff
  have hnscaled := Nat.mul_le_mul_left a hn'
  have hidk := congrArg (fun x : ℕ ↦ x * k ^ 2) hid
  have hfinal : 4 * t ^ 2 * (r + r / b) ^ 2 ≤ a * n := by
    nlinarith only [hR2, hnscaled, hcoeffk, hidk]
  have hfinal' : 4 * t * (r + r / b) ^ 2 ≤ (4 * t - 1) * n := by
    apply Nat.le_of_mul_le_mul_left (c := t) _ htpos
    simpa only [a, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfinal
  have hlast : 2 * (4 * t - 1) = 8 * t - 2 := by omega
  have h := Nat.mul_le_mul_left 2 hfinal'
  simpa only [← Nat.mul_assoc, hlast] using h

theorem subprojective_window_gap_parametric (n r b t : ℕ)
    (ht : 1024 ≤ t) (hk : 64 * t ≤ projectiveScale n) (hb : 8 * t ≤ b)
    (hr : r < projectiveScale n - projectiveScale n / t) :
    (8 * t) * (r + r / b) ^ 2 ≤ (8 * t - 2) * n := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  exact subprojective_window_gap_arithmetic_parametric n (projectiveScale n) r b t
    ht hk hb (projectiveScale_pred_sq_add_le hn) hr

#print axioms subprojective_window_gap_parametric

end Erdos19
