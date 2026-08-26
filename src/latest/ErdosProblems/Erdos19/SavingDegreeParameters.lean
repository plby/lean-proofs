import ErdosProblems.Erdos19.ReservoirDegreePartition
import ErdosProblems.Erdos19.LowIncidenceParameters

/-! # Integer degree estimates for the saved-palette branch

The same reservoir lower bound yields the degree cap both at vertices already
covered by special colors and at vertices with a sufficient pair-degree deficit.
-/

namespace Erdos19

theorem reservoir_high_degree_bound (n k f e q r x j h : ℕ)
    (hk : 2 ≤ k) (hf : k * f ≤ n) (hq : q ≤ n)
    (hres : q ≤ k * (r + e)) (hbudget : 2 * (x + j + r) ≤ n + q + 1)
    (hj : h ≤ j + 1) : x + h + f ≤ n + e + 2 := by
  have hbudget' := Nat.mul_le_mul_left k hbudget
  have hj' := Nat.mul_le_mul_left (2 * k) hj
  have hq' := Nat.mul_le_mul_left (k - 2) hq
  have hdiff : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have hf' := Nat.mul_le_mul_left 2 hf
  apply Nat.le_of_mul_le_mul_left (c := 2 * k) _ (by omega)
  nlinarith only [hbudget', hj', hq', hdiff, hf', hres]

theorem reservoir_low_degree_bound (n k f e q r x j h slack deficit : ℕ)
    (hk : 4 ≤ k) (hf : k * f ≤ n) (hq : q + deficit ≤ n)
    (hres : q ≤ k * (r + e)) (hbudget : 2 * (x + j + r) ≤ n + q + 1)
    (hdeficit : 4 * (h + slack) ≤ deficit) :
    x + h + f + slack ≤ n + e + 1 := by
  have hbudget' := Nat.mul_le_mul_left k hbudget
  have hq' := Nat.mul_le_mul_left (k - 2) hq
  have hd' := Nat.mul_le_mul_left (k - 2) hdeficit
  have hdiff : k - 2 + 2 = k := Nat.sub_add_cancel (by omega : 2 ≤ k)
  have hroom := Nat.mul_le_mul_right (h + slack) (show 2 * k ≤ 4 * (k - 2) by omega)
  have hf' := Nat.mul_le_mul_left 2 hf
  have hj : 0 ≤ 2 * k * j := Nat.zero_le _
  apply Nat.le_of_mul_le_mul_left (c := 2 * k) _ (by omega)
  nlinarith only [hbudget', hq', hd', hdiff, hroom, hf', hres, hj]

theorem saving_palette_arithmetic (n h f e : ℕ)
    (hroom : 2 * (h + f) ≤ n) (hslack : 8 * e ≤ f) :
    let fresh := f - 8 * e
    let m := n - fresh
    let D := n - h - f + 2 * e
    fresh ≤ n ∧ h ≤ m ∧ m + fresh = n ∧ n ≤ 2 * D ∧ D ≤ n ∧
      m - h = D + 6 * e := by
  dsimp only
  omega

theorem saving_approximate_palette_slack (n L D e : ℕ) (hL : 0 < L)
    (hD : D ≤ n) (he : e = n / L) (hn : L ≤ n) :
    (1 + 1 / (2 * (L : ℝ))) * D ≤ (D + 6 * e : ℕ) := by
  have hepos : 1 ≤ e := by rw [he]; exact (Nat.le_div_iff_mul_le hL).mpr (by simpa using hn)
  have hfloor := Nat.lt_mul_div_succ n hL
  rw [← he] at hfloor
  have hdouble := Nat.mul_le_mul_left L (show e + 1 ≤ 2 * e by omega)
  have hbound : D ≤ 2 * L * e := by nlinarith only [hD, hfloor, hdouble]
  have hboundR : (D : ℝ) ≤ 2 * L * e := by exact_mod_cast hbound
  have hden : (0 : ℝ) < 2 * L := by positivity
  have hdiv : (D : ℝ) / (2 * L) ≤ e := (div_le_iff₀ hden).mpr (by
    simpa only [mul_comm (e : ℝ)] using hboundR)
  push_cast
  rw [add_mul, one_mul, one_div_mul_eq_div]
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  linarith only [hdiv, heR]

theorem reservoir_degree_upper (n k e q r : ℕ) (hk : 0 < k)
    (hq : q ≤ n) (hupper : k * r ≤ q + k * e) : r ≤ n / k + e := by
  have hfloor := Nat.lt_mul_div_succ n hk
  by_contra hnot
  have hr : n / k + e + 1 ≤ r := by omega
  have hr' := Nat.mul_le_mul_left k hr
  nlinarith only [hfloor, hupper, hq, hr']

theorem reservoir_request_bound (n k e delta q r m : ℕ) (hk : 0 < k)
    (hq : q ≤ n) (hupper : k * r ≤ q + k * e)
    (hnear : n ≤ q + delta) (hslack : 8 * e ≤ n / k)
    (hm : m + (n / k - 8 * e) = n) : m + r ≤ q + (delta + 9 * e) := by
  have hbound := reservoir_degree_upper n k e q r hk hq hupper
  omega

theorem reservoir_outside_degree_bound (n k e delta q r : ℕ) (hk : 0 < k)
    (hupper : k * r ≤ q + k * e) (hfar : q + delta + 1 ≤ n)
    (hdelta : 9 * k * e + k ≤ delta) (hslack : 8 * e ≤ n / k) :
    r < n / k - 8 * e := by
  have hfloor := Nat.lt_mul_div_succ n hk
  have hsub := Nat.sub_add_cancel hslack
  have hsub' := congrArg (fun a ↦ k * a) hsub
  apply Nat.lt_of_mul_lt_mul_left (a := k)
  nlinarith only [hfloor, hupper, hfar, hdelta, hsub']

#print axioms reservoir_high_degree_bound
#print axioms reservoir_low_degree_bound
#print axioms saving_palette_arithmetic
#print axioms saving_approximate_palette_slack
#print axioms reservoir_outside_degree_bound

end Erdos19
