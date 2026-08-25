import ErdosProblems.Erdos1141b.BurgessAveraging
import ErdosProblems.Erdos1141b.BurgessParameters
import ErdosProblems.Erdos1141b.CompositeCharacterSums
import ErdosProblems.Erdos1141b.CoprimeCounting

/-!
# A weak Burgess estimate for squarefree quadratic characters

Only a fixed power saving below the square-root threshold is needed.
-/

open scoped BigOperators

namespace Erdos1141b

open CharacterSums

variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise fun i j ↦ (p i).Coprime (p j))

/-- The parameter choice only needs the indicated fourth-moment estimate. -/
theorem weak_burgess_prefix_fourth_le_of_moment
    (q A B N : ℕ) [NeZero q] (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1)
    (hbound : ∀ x, |χ x| ≤ 1)
    (hq : 2 ≤ q)
    (hdiv : ∀ n : ℕ, n ≠ 0 → n ≤ q → (n.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 2048 : ℝ))
    (hlarge : (4 : ℝ) ≤ (q : ℝ) ^ (319 / 1024 : ℝ))
    (hAlo : (q : ℝ) ^ (5 / 16 : ℝ) / 2 ≤ (A : ℝ))
    (hAhi : (A : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ))
    (hBlo : (q : ℝ) ^ (1 / 8 : ℝ) / 2 ≤ (B : ℝ))
    (hBhi : (B : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ))
    (hNlo : (q : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ))
    (hNhi : (N : ℝ) ≤ (q : ℝ) ^ (5 / 8 : ℝ))
    (hmoment : (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) ≤
      4 * (q : ℝ) ^ (1 / 1024 : ℝ) * (B : ℝ) ^ 2 * q) :
    |∑ n ∈ Finset.Icc 1 N, χ n| ^ 4 ≤
      4224 * (N : ℝ) ^ 4 * (q : ℝ) ^ (-3 / 128 : ℝ) := by
  classical
  let Q : ℝ := (2 : ℝ) ^ q.primeFactors.card
  let w : ℝ := (q : ℝ) ^ (1 / 1024 : ℝ)
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hw : 0 < w := by dsimp [w]; positivity
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hAlo
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by positivity) hBlo
  have hBnat : 0 < B := by exact_mod_cast hBpos
  have hbox : A * N < q := burgess_short_box (by omega) hAhi hNhi
  have hQcard : Q ≤ (q.divisors.card : ℝ) := by
    dsimp [Q]
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card q hq0
  have hQ : Q ≤ (q : ℝ) ^ (1 / 2048 : ℝ) := hQcard.trans (hdiv q hq0 le_rfl)
  have hQsq : Q ^ 2 ≤ w := by
    calc
      _ ≤ ((q : ℝ) ^ (1 / 2048 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hQ 2
      _ = w := by dsimp [w]; rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
  have hQw : Q ≤ w := hQ.trans
    (Real.rpow_le_rpow_of_exponent_le hqone (by norm_num))
  have hAcount : 2 * (2 ^ q.primeFactors.card) ^ 2 ≤ A := by
    have hscale : 4 * w ≤ (q : ℝ) ^ (5 / 16 : ℝ) := by
      calc
        _ ≤ (q : ℝ) ^ (319 / 1024 : ℝ) * w :=
          mul_le_mul_of_nonneg_right hlarge hw.le
        _ = _ := by dsimp [w]; rw [← Real.rpow_add hqpos]; norm_num
    have hAr : 2 * Q ^ 2 ≤ (A : ℝ) := by linarith
    dsimp [Q] at hAr
    exact_mod_cast hAr
  have hcount : (A : ℝ) / (2 * w) ≤
      (((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card : ℝ) := by
    apply le_trans _ (Sieve.count_coprime_Icc_ge q A hq hAcount)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg A) (by positivity)
      (mul_le_mul_of_nonneg_left hQw (by norm_num))
  have henergy : (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ≤
      (A : ℝ) * N * w := by
    have hraw : (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (A * N), (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast sum_ratioFiber_card_sq_le q A N hbox
    apply hraw.trans
    calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 (A * N), w := by
        apply Finset.sum_le_sum
        intro n hn
        have hnn := Finset.mem_Icc.mp hn
        have hnq : n ≤ q := hnn.2.trans hbox.le
        have hd := hdiv n (by omega) hnq
        calc
          _ ≤ ((q : ℝ) ^ (1 / 2048 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
          _ = w := by dsimp [w]; rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
      _ = _ := by simp
  have hbound := character_prefix_fourth_le_of_estimates q A B N χ hmul hunit hbound
    ((A : ℝ) / (2 * w)) ((A : ℝ) * N * w) (4 * w * (B : ℝ) ^ 2 * q)
    (by positivity) (by positivity) (by positivity) hBnat hcount henergy hmoment
  have hpow : (q : ℝ) ^ (129 / 128 : ℝ) = w ^ 8 * q := by
    dsimp [w]
    calc
      _ = (q : ℝ) ^ ((1 / 1024 : ℝ) * (8 : ℕ) + 1) := by norm_num
      _ = (q : ℝ) ^ ((1 / 1024 : ℝ) * (8 : ℕ)) * (q : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hqpos _ _
      _ = _ := by rw [Real.rpow_mul_natCast hqpos.le, Real.rpow_one]
  have hid : 8 * ((A : ℝ) * N * w) ^ 3 * (4 * w * (B : ℝ) ^ 2 * q) /
      ((A : ℝ) / (2 * w) * B) ^ 4 =
        512 * (N : ℝ) ^ 3 * (q : ℝ) ^ (129 / 128 : ℝ) / ((A : ℝ) * B ^ 2) := by
    rw [hpow]
    field_simp
    ring
  rw [hid] at hbound
  exact hbound.trans (burgess_parameter_bound hqone hAlo hAhi hBlo hBhi hNlo)

theorem weak_burgess_prefix_fourth_le
    (hodd : ∀ i, p i ≠ 2) (A B N : ℕ) (hq : 2 ≤ ∏ i, p i)
    (hdiv : ∀ n : ℕ, n ≠ 0 → n ≤ ∏ i, p i →
      (n.divisors.card : ℝ) ≤ (∏ i, p i : ℕ) ^ (1 / 2048 : ℝ))
    (hlarge : (4 : ℝ) ≤ (∏ i, p i : ℕ) ^ (319 / 1024 : ℝ))
    (hAlo : (∏ i, p i : ℕ) ^ (5 / 16 : ℝ) / 2 ≤ (A : ℝ))
    (hAhi : (A : ℝ) ≤ (∏ i, p i : ℕ) ^ (5 / 16 : ℝ))
    (hBlo : (∏ i, p i : ℕ) ^ (1 / 8 : ℝ) / 2 ≤ (B : ℝ))
    (hBhi : (B : ℝ) ≤ (∏ i, p i : ℕ) ^ (1 / 8 : ℝ))
    (hNlo : (∏ i, p i : ℕ) ^ (15 / 32 : ℝ) ≤ (N : ℝ))
    (hNhi : (N : ℝ) ≤ (∏ i, p i : ℕ) ^ (5 / 8 : ℝ)) :
    |∑ n ∈ Finset.Icc 1 N, (primeProductCharacter p hc (n : ZMod (∏ i, p i)) : ℝ)| ^ 4 ≤
      4224 * (N : ℝ) ^ 4 * (∏ i, p i : ℕ) ^ (-3 / 128 : ℝ) := by
  let q := ∏ i, p i
  let w : ℝ := (q : ℝ) ^ (1 / 1024 : ℝ)
  have hq0 : q ≠ 0 := by dsimp [q]; positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hwone : 1 ≤ w := Real.one_le_rpow hqone (by norm_num)
  have htwo : (2 : ℝ) ^ Fintype.card ι ≤ (q : ℝ) ^ (1 / 2048 : ℝ) := by
    rw [← primeProduct_primeFactors_card p hc]
    have hd : (2 : ℝ) ^ q.primeFactors.card ≤ (q.divisors.card : ℝ) := by
      exact_mod_cast two_pow_primeFactors_card_le_divisors_card q hq0
    exact hd.trans (hdiv q hq0 le_rfl)
  have hthree : (3 : ℝ) ^ Fintype.card ι ≤ w := by
    calc
      _ ≤ ((2 : ℝ) ^ 2) ^ Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2 : ℝ) ^ Fintype.card ι) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((q : ℝ) ^ (1 / 2048 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) htwo 2
      _ = w := by dsimp [w]; rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
  have hmoment :
      (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x + b) : ℝ)) ^ 4) ≤
        4 * w * (B : ℝ) ^ 2 * q := by
    apply (primeProductCharacter_fourth_moment_short_le p hc hodd B
      (burgess_seventh_power_le (by omega) hBhi)).trans
    gcongr
    linarith
  exact weak_burgess_prefix_fourth_le_of_moment q A B N
    (fun x ↦ (primeProductCharacter p hc x : ℝ))
    (fun x y ↦ by rw [primeProductCharacter_mul, Int.cast_mul])
    (abs_primeProductCharacter_of_coprime p hc) (abs_primeProductCharacter_le_one p hc)
    hq hdiv hlarge hAlo hAhi hBlo hBhi hNlo hNhi hmoment

/-- Uniform cancellation below the square-root threshold, with an absolute cutoff. -/
theorem exists_weak_burgess_cutoff :
    ∃ q0 : ℕ, ∀ {κ : Type*} [Fintype κ] (p : κ → ℕ) [∀ i, Fact (p i).Prime]
      (hc : Pairwise fun i j ↦ (p i).Coprime (p j)),
      (∀ i, p i ≠ 2) → q0 ≤ ∏ i, p i →
      ∀ N : ℕ, (∏ i, p i : ℕ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
        (N : ℝ) ≤ (∏ i, p i : ℕ) ^ (5 / 8 : ℝ) →
        |∑ n ∈ Finset.Icc 1 N, (primeProductCharacter p hc (n : ZMod (∏ i, p i)) : ℝ)| ≤
          (N : ℝ) * (∏ i, p i : ℕ) ^ (-1 / 256 : ℝ) := by
  have hcut : ∀ᶠ q : ℕ in Filter.atTop,
      (∀ n : ℕ, n ≠ 0 → n ≤ q → (n.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 2048 : ℝ)) ∧
      (4 : ℝ) ≤ (q : ℝ) ^ (319 / 1024 : ℝ) ∧
      (2 : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) ∧
      (4224 : ℝ) ≤ (q : ℝ) ^ (1 / 128 : ℝ) ∧ 2 ≤ q := by
    have hdiv := eventually_divisors_card_le_rpow_uniform 4096 (by norm_num)
    norm_num only [Nat.cast_ofNat, div_eq_mul_inv, mul_one, one_mul] at hdiv
    filter_upwards [hdiv,
      eventually_const_le_rpow 4 (319 / 1024) (by norm_num),
      eventually_const_le_rpow 2 (1 / 8) (by norm_num),
      eventually_const_le_rpow 4224 (1 / 128) (by norm_num),
      Filter.eventually_ge_atTop 2] with q hd hlarge htwo hconstant hq
    refine ⟨?_, hlarge, htwo, hconstant, hq⟩
    intro n hn hnq
    convert hd n hn hnq using 1
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.mp hcut
  refine ⟨q0, ?_⟩
  intro κ _ p _ hc hodd hq N hNlo hNhi
  let q := ∏ i, p i
  obtain ⟨hdiv, hlarge, htwo, hconstant, hq2⟩ := hq0 q hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  let A := ⌊(q : ℝ) ^ (5 / 16 : ℝ)⌋₊
  let B := ⌊(q : ℝ) ^ (1 / 8 : ℝ)⌋₊
  have hAtwo : (2 : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ) :=
    htwo.trans (Real.rpow_le_rpow_of_exponent_le hqone (by norm_num))
  have hAlo : (q : ℝ) ^ (5 / 16 : ℝ) / 2 ≤ A := half_le_nat_floor hAtwo
  have hAhi : (A : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ) := Nat.floor_le (by positivity)
  have hBlo : (q : ℝ) ^ (1 / 8 : ℝ) / 2 ≤ B := half_le_nat_floor htwo
  have hBhi : (B : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
  have hfourth := weak_burgess_prefix_fourth_le p hc hodd A B N hq2 hdiv hlarge
    hAlo hAhi hBlo hBhi hNlo hNhi
  apply le_of_pow_le_pow_left₀ (show (4 : ℕ) ≠ 0 by norm_num) (by positivity)
  apply hfourth.trans
  calc
    _ ≤ (q : ℝ) ^ (1 / 128 : ℝ) * (N : ℝ) ^ 4 * (q : ℝ) ^ (-3 / 128 : ℝ) := by
      gcongr
    _ = (N : ℝ) ^ 4 * (q : ℝ) ^ (-1 / 64 : ℝ) := by
      rw [mul_right_comm, ← Real.rpow_add hqpos]
      norm_num
      ring
    _ = ((N : ℝ) * (q : ℝ) ^ (-1 / 256 : ℝ)) ^ 4 := by
      rw [mul_pow, ← Real.rpow_mul_natCast hqpos.le]
      norm_num

/-- A character with the stated fourth moment has the same uniform power saving. -/
theorem exists_weak_burgess_cutoff_of_moment :
    ∃ q0 : ℕ, ∀ (q : ℕ) [NeZero q], q0 ≤ q →
      ∀ χ : ZMod q → ℝ,
        (∀ x y, χ (x * y) = χ x * χ y) →
        (∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1) →
        (∀ x, |χ x| ≤ 1) →
        (let B := ⌊(q : ℝ) ^ (1 / 8 : ℝ)⌋₊;
          (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) ≤
            (3 + (q.divisors.card : ℝ) ^ 2) * (B : ℝ) ^ 2 * q) →
        ∀ N : ℕ, (q : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
          (N : ℝ) ≤ (q : ℝ) ^ (5 / 8 : ℝ) →
          |∑ n ∈ Finset.Icc 1 N, χ n| ≤ (N : ℝ) * (q : ℝ) ^ (-1 / 256 : ℝ) := by
  have hcut : ∀ᶠ q : ℕ in Filter.atTop,
      (∀ n : ℕ, n ≠ 0 → n ≤ q → (n.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 2048 : ℝ)) ∧
      (4 : ℝ) ≤ (q : ℝ) ^ (319 / 1024 : ℝ) ∧
      (2 : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) ∧
      (4224 : ℝ) ≤ (q : ℝ) ^ (1 / 128 : ℝ) ∧ 2 ≤ q := by
    have hdiv := eventually_divisors_card_le_rpow_uniform 4096 (by norm_num)
    norm_num only [Nat.cast_ofNat, div_eq_mul_inv, mul_one, one_mul] at hdiv
    filter_upwards [hdiv,
      eventually_const_le_rpow 4 (319 / 1024) (by norm_num),
      eventually_const_le_rpow 2 (1 / 8) (by norm_num),
      eventually_const_le_rpow 4224 (1 / 128) (by norm_num),
      Filter.eventually_ge_atTop 2] with q hd hlarge htwo hconstant hq
    refine ⟨?_, hlarge, htwo, hconstant, hq⟩
    intro n hn hnq
    convert hd n hn hnq using 1
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.mp hcut
  refine ⟨q0, ?_⟩
  intro q _ hq χ hmul hunit hbound hmoment N hNlo hNhi
  obtain ⟨hdiv, hlarge, htwo, hconstant, hq2⟩ := hq0 q hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  let A := ⌊(q : ℝ) ^ (5 / 16 : ℝ)⌋₊
  let B := ⌊(q : ℝ) ^ (1 / 8 : ℝ)⌋₊
  have hAtwo : (2 : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ) :=
    htwo.trans (Real.rpow_le_rpow_of_exponent_le hqone (by norm_num))
  have hAlo : (q : ℝ) ^ (5 / 16 : ℝ) / 2 ≤ A := half_le_nat_floor hAtwo
  have hAhi : (A : ℝ) ≤ (q : ℝ) ^ (5 / 16 : ℝ) := Nat.floor_le (by positivity)
  have hBlo : (q : ℝ) ^ (1 / 8 : ℝ) / 2 ≤ B := half_le_nat_floor htwo
  have hBhi : (B : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
  have hdivsq : (q.divisors.card : ℝ) ^ 2 ≤ (q : ℝ) ^ (1 / 1024 : ℝ) := by
    calc
      _ ≤ ((q : ℝ) ^ (1 / 2048 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hdiv q (NeZero.ne q) le_rfl) 2
      _ = _ := by rw [← Real.rpow_mul_natCast hqpos.le]; norm_num
  have hmoment' : (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) ≤
      4 * (q : ℝ) ^ (1 / 1024 : ℝ) * (B : ℝ) ^ 2 * q := by
    apply hmoment.trans
    gcongr
    have hone := Real.one_le_rpow hqone (by norm_num : 0 ≤ (1 / 1024 : ℝ))
    linarith
  have hfourth := weak_burgess_prefix_fourth_le_of_moment q A B N χ hmul hunit hbound
    hq2 hdiv hlarge hAlo hAhi hBlo hBhi hNlo hNhi hmoment'
  apply le_of_pow_le_pow_left₀ (show (4 : ℕ) ≠ 0 by norm_num) (by positivity)
  apply hfourth.trans
  calc
    _ ≤ (q : ℝ) ^ (1 / 128 : ℝ) * (N : ℝ) ^ 4 * (q : ℝ) ^ (-3 / 128 : ℝ) := by gcongr
    _ = (N : ℝ) ^ 4 * (q : ℝ) ^ (-1 / 64 : ℝ) := by
      rw [mul_right_comm, ← Real.rpow_add hqpos]
      norm_num
      ring
    _ = ((N : ℝ) * (q : ℝ) ^ (-1 / 256 : ℝ)) ^ 4 := by
      rw [mul_pow, ← Real.rpow_mul_natCast hqpos.le]
      norm_num

end Erdos1141b
