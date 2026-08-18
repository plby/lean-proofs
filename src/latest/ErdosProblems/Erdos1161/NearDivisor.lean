import ErdosProblems.Erdos1161.FirstCycle
import ErdosProblems.Erdos1161.DivisorBounds

/-!
# Concentration on a divisor close to the degree

This file isolates the short-interval arithmetic in the structural part of
Beker's argument.  The analytic large-order estimate supplies the integral
bound `m ^ 3 ≤ n ^ 4`.  Under that bound, two divisors of `m` cannot both
belong to the final `sqrt n` integers below `n`.

The second half of the file combines this uniqueness with the exact
distinguished-cycle recursion.  It is kept separate from the later
prime-power argument: its conclusion is the quantified statement that the
unique long first-cycle length has residual success probability close to one.
-/

open scoped BigOperators
open Filter

namespace Erdos1161

/-! ## The short divisor interval -/

/-- Two divisors of `m` in `(w,n]` coincide if `m` times an upper bound for
the interval width is smaller than `(w+1)^2`. -/
theorem eq_of_dvd_of_mem_short_interval
    {m n w s a b : ℕ}
    (hm_pos : 0 < m) (ha : a ∣ m) (hb : b ∣ m)
    (hwa : w < a) (hwb : w < b)
    (han : a ≤ n) (hbn : b ≤ n)
    (hwidth : n - w ≤ s)
    (hsmall : m * s < (w + 1) ^ 2) :
    a = b := by
  by_contra hab
  have hlcm_le : Nat.lcm a b ≤ m :=
    Nat.le_of_dvd hm_pos (Nat.lcm_dvd ha hb)
  have hgcd_le : Nat.gcd a b ≤ s := by
    rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
    · have hdiff_pos : 0 < b - a := by omega
      have hgcd_diff : Nat.gcd a b ∣ b - a :=
        Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b)
      have hgcd_diff_le : Nat.gcd a b ≤ b - a :=
        Nat.le_of_dvd hdiff_pos hgcd_diff
      have hdiff_width : b - a ≤ n - w := by omega
      exact hgcd_diff_le.trans (hdiff_width.trans hwidth)
    · have hdiff_pos : 0 < a - b := by omega
      have hgcd_diff : Nat.gcd a b ∣ a - b :=
        Nat.dvd_sub (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
      have hgcd_diff_le : Nat.gcd a b ≤ a - b :=
        Nat.le_of_dvd hdiff_pos hgcd_diff
      have hdiff_width : a - b ≤ n - w := by omega
      exact hgcd_diff_le.trans (hdiff_width.trans hwidth)
  have hab_le : a * b ≤ m * s := by
    rw [← Nat.lcm_mul_gcd]
    exact Nat.mul_le_mul hlcm_le hgcd_le
  have hw1a : w + 1 ≤ a := by omega
  have hw1b : w + 1 ≤ b := by omega
  have hsq_le : (w + 1) ^ 2 ≤ a * b := by
    rw [pow_two]
    exact Nat.mul_le_mul hw1a hw1b
  omega

/-- The preceding interval lemma specialized to `(n - sqrt n,n]`. -/
theorem eq_of_dvd_of_mem_top_sqrt_interval
    {m n a b : ℕ}
    (hm_pos : 0 < m) (ha : a ∣ m) (hb : b ∣ m)
    (ha_lower : n - n.sqrt < a) (hb_lower : n - n.sqrt < b)
    (ha_upper : a ≤ n) (hb_upper : b ≤ n)
    (hsmall : m * n.sqrt < (n - n.sqrt + 1) ^ 2) :
    a = b := by
  exact eq_of_dvd_of_mem_short_interval (s := n.sqrt) hm_pos ha hb
    ha_lower hb_lower ha_upper hb_upper (by
      have hsqrt := Nat.sqrt_le_self n
      omega) hsmall

/-- The integral form of `m ≤ n^(4/3)` implies the separation inequality
once `64 * sqrt n < n`. -/
theorem mul_sqrt_lt_sq_sub_sqrt_add_one_of_cube_le_fourth
    {m n : ℕ} (hm_cube : m ^ 3 ≤ n ^ 4)
    (hn_large : 64 * n.sqrt < n) :
    m * n.sqrt < (n - n.sqrt + 1) ^ 2 := by
  set s := n.sqrt
  set t := n - s + 1
  have hs_sq : s ^ 2 ≤ n := by
    simpa [s] using Nat.sqrt_le' n
  have hs_cube : s ^ 3 ≤ n * s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ n * s := Nat.mul_le_mul_right s hs_sq
  have htwo : 2 * s ≤ n := by
    simpa [s] using (show 2 * n.sqrt ≤ n by omega)
  have hnt : n ≤ 2 * t := by
    dsimp [t]
    omega
  by_contra hnot
  have hcontra : t ^ 2 ≤ m * s := Nat.le_of_not_gt hnot
  have ht_bound : t ^ 6 ≤ n ^ 5 * s := by
    calc
      t ^ 6 = (t ^ 2) ^ 3 := by ring
      _ ≤ (m * s) ^ 3 := Nat.pow_le_pow_left hcontra 3
      _ = m ^ 3 * s ^ 3 := by ring
      _ ≤ n ^ 4 * (n * s) := Nat.mul_le_mul hm_cube hs_cube
      _ = n ^ 5 * s := by ring
  have hn_lower : n ^ 6 ≤ 64 * t ^ 6 := by
    calc
      n ^ 6 ≤ (2 * t) ^ 6 := Nat.pow_le_pow_left hnt 6
      _ = 64 * t ^ 6 := by ring
  have hn_upper : 64 * t ^ 6 < n ^ 6 := by
    calc
      64 * t ^ 6 ≤ 64 * (n ^ 5 * s) := Nat.mul_le_mul_left 64 ht_bound
      _ = n ^ 5 * (64 * s) := by ring
      _ < n ^ 5 * n := by
        apply (Nat.mul_lt_mul_left (show 0 < n ^ 5 by
          have : 0 < n := by omega
          positivity)).2
        simpa [s] using hn_large
      _ = n ^ 6 := by ring
  omega

/-- The explicit cutoff `4096 < n` guarantees `64 * sqrt n < n`. -/
theorem sixtyFour_mul_sqrt_lt_of_4096_lt {n : ℕ} (hn : 4096 < n) :
    64 * n.sqrt < n := by
  have hs_lower : 64 ≤ n.sqrt := by
    rw [Nat.le_sqrt']
    norm_num
    omega
  rcases hs_lower.eq_or_lt with hs | hs
  · omega
  · have hs_sq : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n
    nlinarith

/-- Under the cubed integral form of `m ≤ n^(4/3)`, the divisors of `m`
in `(n - sqrt n,n]` form a subsingleton. -/
theorem nearDivisors_subsingleton_of_cube_le_fourth
    {m n : ℕ} (hm_pos : 0 < m) (hm_cube : m ^ 3 ≤ n ^ 4)
    (hn_large : 4096 < n) :
    Set.Subsingleton {d : ℕ | d ∣ m ∧ n - n.sqrt < d ∧ d ≤ n} := by
  intro a ha b hb
  exact eq_of_dvd_of_mem_top_sqrt_interval hm_pos ha.1 hb.1
    ha.2.1 hb.2.1 ha.2.2 hb.2.2
    (mul_sqrt_lt_sq_sub_sqrt_add_one_of_cube_le_fourth hm_cube
      (sixtyFour_mul_sqrt_lt_of_4096_lt hn_large))

/-! ## An exact finite concentration lemma -/

/-- The positive divisors of `m` which can occur as first-cycle lengths in
degree `n`. -/
def boundedDivisors (n m : ℕ) : Finset ℕ :=
  m.divisors.filter fun d ↦ d ≤ n

/-- The first-cycle lengths in the final `sqrt n` integers. -/
def nearDivisors (n m : ℕ) : Finset ℕ :=
  (boundedDivisors n m).filter fun d ↦ n - n.sqrt < d

/-- The complementary first-cycle lengths, whose residual degree is at
least `sqrt n`. -/
def farDivisors (n m : ℕ) : Finset ℕ :=
  (boundedDivisors n m).filter fun d ↦ d ≤ n - n.sqrt

@[simp]
theorem mem_boundedDivisors {n m d : ℕ} (hm : 0 < m) :
    d ∈ boundedDivisors n m ↔ d ∣ m ∧ d ≤ n := by
  simp [boundedDivisors, Nat.mem_divisors, hm.ne']

@[simp]
theorem mem_nearDivisors {n m d : ℕ} (hm : 0 < m) :
    d ∈ nearDivisors n m ↔ d ∣ m ∧ n - n.sqrt < d ∧ d ≤ n := by
  simp only [nearDivisors, Finset.mem_filter, mem_boundedDivisors hm]
  aesop

@[simp]
theorem mem_farDivisors {n m d : ℕ} (hm : 0 < m) :
    d ∈ farDivisors n m ↔ d ∣ m ∧ d ≤ n ∧ d ≤ n - n.sqrt := by
  simp only [farDivisors, Finset.mem_filter, mem_boundedDivisors hm]
  aesop

theorem sum_farDivisors_add_sum_nearDivisors
    (n m : ℕ) (f : ℕ → ℚ) :
    ∑ d ∈ farDivisors n m, f d
      + ∑ d ∈ nearDivisors n m, f d
      = ∑ d ∈ boundedDivisors n m, f d := by
  simpa only [farDivisors, nearDivisors, not_le] using
    (Finset.sum_filter_add_sum_filter_not (boundedDivisors n m)
      (fun d ↦ d ≤ n - n.sqrt) f)

/-- Reindex the filtered distinguished-cycle recursion by the exposed cycle
length `d`, rather than by the residual degree `r=n-d`. -/
theorem sum_boundedDivisors_residualOrderProbability_eq
    {n m : ℕ} (hm : 0 < m) :
    ∑ d ∈ boundedDivisors n m, residualOrderProbability (n - d) d m =
      ∑ r ∈ (Finset.range n).filter (fun r ↦ n - r ∣ m),
        residualOrderProbability r (n - r) m := by
  classical
  apply Finset.sum_bij (fun d _ ↦ n - d)
  · intro d hd
    have hdata := (mem_boundedDivisors hm).mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdata.1 hm
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · simpa [Nat.sub_sub_self hdata.2] using hdata.1
  · intro d₁ hd₁ d₂ hd₂ heq
    have h₁ := (mem_boundedDivisors hm).mp hd₁ |>.2
    have h₂ := (mem_boundedDivisors hm).mp hd₂ |>.2
    omega
  · intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hrn := Finset.mem_range.mp hr'.1
    refine ⟨n - r, (mem_boundedDivisors hm).mpr ⟨hr'.2, Nat.sub_le n r⟩, ?_⟩
    omega
  · intro d hd
    have hdle := (mem_boundedDivisors hm).mp hd |>.2
    simp only [Nat.sub_sub_self hdle]

/-- The factorial threshold, after the exact first-cycle recursion, says
that the total residual success mass indexed by bounded divisors is at least
one. -/
theorem one_le_sum_boundedDivisors_residualOrderProbability
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hthreshold :
      (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ)) :
    1 ≤ ∑ d ∈ boundedDivisors n m,
      residualOrderProbability (n - d) d m := by
  rw [orderRationalProbability_recursion_filtered hn,
    ← sum_boundedDivisors_residualOrderProbability_eq hm] at hthreshold
  have hpos : (0 : ℚ) < 1 / n := by positivity
  nlinarith

/-- The precise tail estimate used after the first-cycle recursion.  There
are at most `τ(m)` possible first-cycle lengths, and for a far length `d`
the residual degree `n-d` is at least `sqrt n`. -/
theorem sum_farDivisors_le_divisorCount_sq_div_sqrt
    {n m : ℕ} {f : ℕ → ℚ}
    (hn : 0 < n) (hm : 0 < m)
    (hf : ∀ d ∈ farDivisors n m,
      f d ≤ (divisorCount m : ℚ) / (n - d : ℕ)) :
    ∑ d ∈ farDivisors n m, f d ≤
      (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) := by
  have hsqrt_nat : 0 < n.sqrt := Nat.sqrt_pos.2 hn
  have hsqrt_rat : (0 : ℚ) < n.sqrt := by exact_mod_cast hsqrt_nat
  have hpoint : ∀ d ∈ farDivisors n m,
      f d ≤ (divisorCount m : ℚ) / (n.sqrt : ℕ) := by
    intro d hd
    have hd_le : d ≤ n - n.sqrt := (mem_farDivisors hm).mp hd |>.2.2
    have hsqrt_le_n : n.sqrt ≤ n := Nat.sqrt_le_self n
    have hsqrt_le : n.sqrt ≤ n - d := by omega
    calc
      f d ≤ (divisorCount m : ℚ) / (n - d : ℕ) := hf d hd
      _ ≤ (divisorCount m : ℚ) / (n.sqrt : ℕ) := by
        have hres_rat : (0 : ℚ) < (n - d : ℕ) := by
          exact_mod_cast (hsqrt_nat.trans_le hsqrt_le)
        rw [div_le_div_iff₀ hres_rat hsqrt_rat]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsqrt_le)
          (by positivity)
  have hcard_nat : (farDivisors n m).card ≤ m.divisors.card := by
    apply Finset.card_le_card
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_farDivisors hm).mp hd |>.1, hm.ne'⟩
  calc
    ∑ d ∈ farDivisors n m, f d ≤
          (farDivisors n m).card •
          ((divisorCount m : ℚ) / (n.sqrt : ℕ)) :=
      Finset.sum_le_card_nsmul _ _ _ hpoint
    _ = ((farDivisors n m).card : ℚ) *
          ((divisorCount m : ℚ) / (n.sqrt : ℕ)) := by
      simp [nsmul_eq_mul]
    _ ≤ (divisorCount m : ℚ) *
          ((divisorCount m : ℚ) / (n.sqrt : ℕ)) := by
      apply mul_le_mul_of_nonneg_right (by
        simpa [divisorCount] using (show
          ((farDivisors n m).card : ℚ) ≤ (m.divisors.card : ℚ) by
            exact_mod_cast hcard_nat))
      positivity
    _ = (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) := by ring

/-- A convenient integral criterion ensuring that the rational tail error is
strictly smaller than one. -/
theorem divisorCount_sq_lt_sqrt_of_four_mul_fourth_lt
    {m n : ℕ} (hm : 0 < m)
    (hsmall : 4 * divisorCount m ^ 4 < n) :
    divisorCount m ^ 2 < n.sqrt := by
  have ht : 1 ≤ divisorCount m := by
    have hmem : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr hm.ne'
    have hcard : 0 < divisorCount m := by
      exact Finset.card_pos.mpr ⟨1, hmem⟩
    omega
  by_contra hnot
  have hsqrt : n.sqrt ≤ divisorCount m ^ 2 := Nat.le_of_not_gt hnot
  have hnlt : n < (n.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hupp : (n.sqrt + 1) ^ 2 ≤ 4 * divisorCount m ^ 4 := by
    have hadd : n.sqrt + 1 ≤ 2 * divisorCount m ^ 2 := by
      have hone : 1 ≤ divisorCount m ^ 2 :=
        Nat.one_le_pow 2 (divisorCount m) (by omega)
      omega
    calc
      (n.sqrt + 1) ^ 2 ≤ (2 * divisorCount m ^ 2) ^ 2 :=
        Nat.pow_le_pow_left hadd 2
      _ = 4 * divisorCount m ^ 4 := by ring
  omega

theorem divisorCount_sq_div_sqrt_lt_one_of_four_mul_fourth_lt
    {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hsmall : 4 * divisorCount m ^ 4 < n) :
    (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) < 1 := by
  have hsqrt : (0 : ℚ) < (n.sqrt : ℕ) := by
    exact_mod_cast (Nat.sqrt_pos.2 hn)
  rw [div_lt_one hsqrt]
  exact_mod_cast divisorCount_sq_lt_sqrt_of_four_mul_fourth_lt hm hsmall

/-- Uniformly on the polynomial box `m ^ 3 ≤ n ^ 4`, the divisor estimate
makes the explicit fourth-power criterion hold eventually. -/
theorem eventually_four_mul_divisorCount_fourth_lt_of_cube_le_fourth :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ^ 3 ≤ n ^ 4 →
      4 * divisorCount m ^ 4 < n := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_divisorCount_power_le_eighth 4 (by norm_num)
  have htend : Tendsto (fun n : ℕ ↦
      4 * (n : ℝ) ^ (-(7 / 8 : ℝ))) atTop (nhds 0) := by
    convert (tendsto_const_nhds (x := (4 : ℝ))).mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp
        tendsto_natCast_atTop_atTop) using 1 <;> simp
  have hratio : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (-(7 / 8 : ℝ)) < 1 :=
    htend.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ), hratio]
    with n hnN hn1 hratio_n
  intro m hm hm_cube
  have hm1 : 1 ≤ m := hm
  have hm_le : m ≤ n ^ 4 := by
    calc
      m = m ^ 1 := by simp
      _ ≤ m ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
      _ ≤ n ^ 4 := hm_cube
  have htau := hN₀ n hnN m hm1 hm_le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpower : 4 * (n : ℝ) ^ (1 / 8 : ℝ) < n := by
    rw [← div_lt_one hnR]
    calc
      4 * (n : ℝ) ^ (1 / 8 : ℝ) / n =
          4 * (n : ℝ) ^ (-(7 / 8 : ℝ)) := by
        rw [mul_div_assoc, ← Real.rpow_sub_one hnR.ne']
        congr 2
        norm_num
      _ < 1 := hratio_n
  have hreal : (4 : ℝ) * (divisorCount m : ℝ) ^ 4 < n := by
    calc
      (4 : ℝ) * (divisorCount m : ℝ) ^ 4 ≤
          4 * (n : ℝ) ^ (1 / 8 : ℝ) := by gcongr
      _ < n := hpower
  exact_mod_cast hreal

/-- The standard residual divisibility bound, specialized to one of the far
first-cycle lengths. -/
theorem residualOrderProbability_le_divisorCount_div_of_mem_far
    {n m d : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hd : d ∈ farDivisors n m) :
    residualOrderProbability (n - d) d m ≤
      (divisorCount m : ℚ) / (n - d : ℕ) := by
  have hdle : d ≤ n - n.sqrt := (mem_farDivisors hm).mp hd |>.2.2
  have hsqrt_pos : 0 < n.sqrt := Nat.sqrt_pos.2 hn
  have hsqrt_le_n : n.sqrt ≤ n := Nat.sqrt_le_self n
  have hres : 0 < n - d := by omega
  simpa [divisorCount] using
    (residualOrderProbability_le_divisors_card_div hres hm :
      residualOrderProbability (n - d) d m ≤
        ((m.divisors.card : ℕ) : ℚ) / (n - d : ℕ))

/-- Pure finite-mass form of the near-divisor step.  If the full normalized
first-cycle sum is at least one, its far part is at most `error < 1`, and
`m ^ 3 ≤ n ^ 4`, then there is a unique admissible first-cycle length in
`(n - sqrt n,n]`; its individual residual success is at least
`1 - error`.

The distinguished-cycle recursion supplies `htotal`, and the divisor bound
supplies `hfar`, in the application below. -/
theorem exists_unique_nearDivisor_of_sum_ge_one
    {n m : ℕ} {f : ℕ → ℚ} {error : ℚ}
    (hm : 0 < m) (hm_cube : m ^ 3 ≤ n ^ 4) (hn_large : 4096 < n)
    (htotal : 1 ≤ ∑ d ∈ boundedDivisors n m, f d)
    (hfar : ∑ d ∈ farDivisors n m, f d ≤ error)
    (herror : error < 1) :
    ∃ d : ℕ,
      d ∈ nearDivisors n m ∧
      (∀ e ∈ nearDivisors n m, e = d) ∧
      1 - error ≤ f d := by
  classical
  have hsplit := sum_farDivisors_add_sum_nearDivisors n m f
  have hnear_unique : ∀ a ∈ nearDivisors n m,
      ∀ b ∈ nearDivisors n m, a = b := by
    intro a ha b hb
    apply nearDivisors_subsingleton_of_cube_le_fourth hm hm_cube hn_large
    · change a ∣ m ∧ n - n.sqrt < a ∧ a ≤ n
      exact (mem_nearDivisors hm).mp ha
    · change b ∣ m ∧ n - n.sqrt < b ∧ b ≤ n
      exact (mem_nearDivisors hm).mp hb
  have hnear_nonempty : (nearDivisors n m).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hsplit
    simp only [Finset.sum_empty, add_zero] at hsplit
    rw [← hsplit] at htotal
    exact (not_le_of_gt herror) (htotal.trans hfar)
  obtain ⟨d, hd⟩ := hnear_nonempty
  have hnear_eq : nearDivisors n m = {d} := by
    ext e
    simp only [Finset.mem_singleton]
    constructor
    · intro he
      exact hnear_unique e he d hd
    · intro he
      simpa [he] using hd
  refine ⟨d, hd, ?_, ?_⟩
  · intro e he
    exact hnear_unique e he d hd
  · rw [hnear_eq] at hsplit
    simp only [Finset.sum_singleton] at hsplit
    linarith

/-- A pointwise residual bound together with the exact first-cycle mass
identity gives the quantified near-divisor conclusion directly. -/
theorem exists_unique_nearDivisor_of_pointwise_far_bound
    {n m : ℕ} {f : ℕ → ℚ}
    (hn : 0 < n) (hm : 0 < m)
    (hm_cube : m ^ 3 ≤ n ^ 4) (hn_large : 4096 < n)
    (htotal : 1 ≤ ∑ d ∈ boundedDivisors n m, f d)
    (hf : ∀ d ∈ farDivisors n m,
      f d ≤ (divisorCount m : ℚ) / (n - d : ℕ))
    (herror : (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) < 1) :
    ∃ d : ℕ,
      d ∈ nearDivisors n m ∧
      (∀ e ∈ nearDivisors n m, e = d) ∧
      1 - (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) ≤ f d := by
  exact exists_unique_nearDivisor_of_sum_ge_one hm hm_cube hn_large htotal
    (sum_farDivisors_le_divisorCount_sq_div_sqrt hn hm hf) herror

/-- Concrete near-divisor output of the exact distinguished-cycle
recursion.  The only remaining input is the standard pointwise estimate for
the residual divisibility event, which is proved from the same recursion in
`FirstCycle`.

In particular, the last conjunct is the quantified high-success statement
used by the prime-power witness argument. -/
theorem exists_unique_nearDivisor_of_rational_order_threshold
    {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hm_cube : m ^ 3 ≤ n ^ 4) (hn_large : 4096 < n)
    (hthreshold :
      (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ))
    (hresidual : ∀ d ∈ farDivisors n m,
      residualOrderProbability (n - d) d m ≤
        (divisorCount m : ℚ) / (n - d : ℕ))
    (herror : (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) < 1) :
    ∃ d : ℕ,
      d ∈ nearDivisors n m ∧
      (∀ e ∈ nearDivisors n m, e = d) ∧
      1 - (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) ≤
        residualOrderProbability (n - d) d m := by
  apply exists_unique_nearDivisor_of_pointwise_far_bound hn hm hm_cube hn_large
  · exact one_le_sum_boundedDivisors_residualOrderProbability hn hm hthreshold
  · exact hresidual
  · exact herror

/-- Fully integral error criterion for the preceding theorem. -/
theorem exists_unique_nearDivisor_of_rational_order_threshold_of_fourth_bound
    {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hm_cube : m ^ 3 ≤ n ^ 4) (hn_large : 4096 < n)
    (hthreshold :
      (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ))
    (hsmall : 4 * divisorCount m ^ 4 < n) :
    ∃ d : ℕ,
      d ∈ nearDivisors n m ∧
      (∀ e ∈ nearDivisors n m, e = d) ∧
      1 - (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) ≤
        residualOrderProbability (n - d) d m := by
  exact exists_unique_nearDivisor_of_rational_order_threshold hn hm hm_cube
    hn_large hthreshold (fun d hd ↦
      residualOrderProbability_le_divisorCount_div_of_mem_far hn hm hd)
      (divisorCount_sq_div_sqrt_lt_one_of_four_mul_fourth_lt hn hm hsmall)

/-- Eventual near-divisor concentration in the exact form used in the
structural theorem.  All tail estimates are discharged here: only the
large-order output `m ^ 3 ≤ n ^ 4` and the original probability threshold
remain as hypotheses. -/
theorem eventually_exists_unique_nearDivisor_of_rational_order_threshold :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ^ 3 ≤ n ^ 4 →
      (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ) →
      ∃ d : ℕ,
        d ∈ nearDivisors n m ∧
        (∀ e ∈ nearDivisors n m, e = d) ∧
        1 - (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) ≤
          residualOrderProbability (n - d) d m := by
  filter_upwards
    [eventually_four_mul_divisorCount_fourth_lt_of_cube_le_fourth,
      eventually_gt_atTop (4096 : ℕ)] with n hdiv hnlarge
  intro m hm hmcube hthreshold
  exact exists_unique_nearDivisor_of_rational_order_threshold_of_fourth_bound
    (by omega) hm hmcube hnlarge hthreshold (hdiv m hm hmcube)

end Erdos1161
