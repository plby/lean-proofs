import ErdosProblems.Erdos285.Basic
import ErdosProblems.Erdos285.PrimePowers
import PrimeNumberTheoremAnd.Consequences

/-!
# Low-growth exact-cardinality padding for Erdős Problem 285

This file records a backup padding construction which only splits the current
largest denominator.  A three-way split adds two terms and multiplies the
largest denominator by six.  A final secondary split adds one further term.
The second half of the file proves the elementary counting estimate needed to
show that the number of prime powers up to `y` is `o(y)`.
-/

open Filter Finset Asymptotics
open scoped BigOperators Topology Real

namespace Erdos285.LinearPadding

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Replace `n` by `2n,3n,6n`. -/
def tripleSplit (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  insert (2 * n) (insert (3 * n) (insert (6 * n) (A.erase n)))

/-- After a three-way split at `n`, replace `6n` by `9n,18n`. -/
def secondarySplit (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  insert (9 * n) (insert (18 * n) (A.erase (6 * n)))

/-- The three-way unit-fraction identity used for an increment of two. -/
lemma one_div_eq_tripleSplit (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / n = 1 / (2 * n) + 1 / (3 * n) + 1 / (6 * n) := by
  field_simp
  ring

/-- The secondary identity used to turn an even increment into an odd one. -/
lemma one_div_six_eq_secondarySplit (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (6 * n) = 1 / (9 * n) + 1 / (18 * n) := by
  field_simp
  ring

private lemma new_not_mem_of_max {A : Finset ℕ} {n c : ℕ}
    (hn : 0 < n) (hmax : ∀ a ∈ A, a ≤ n) (hc : 2 ≤ c) : c * n ∉ A := by
  intro hmem
  have := hmax _ hmem
  nlinarith

lemma tripleSplit_card {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hnA : n ∈ A) (hmax : ∀ a ∈ A, a ≤ n) :
    (tripleSplit A n).card = A.card + 2 := by
  have h2 : 2 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h3 : 3 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h6 : 6 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h23 : 2 * n ≠ 3 * n := by nlinarith
  have h26 : 2 * n ≠ 6 * n := by nlinarith
  have h36 : 3 * n ≠ 6 * n := by nlinarith
  simp [tripleSplit, h2, h3, h6, h23, h26, h36,
    Finset.card_erase_of_mem hnA]
  have : 0 < A.card := Finset.card_pos.mpr ⟨n, hnA⟩
  omega

lemma tripleSplit_zero_not_mem {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hzero : 0 ∉ A) : 0 ∉ tripleSplit A n := by
  simp [tripleSplit, hn.ne', hzero]

lemma tripleSplit_sum {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hnA : n ∈ A) (hmax : ∀ a ∈ A, a ≤ n) :
    ∑ a ∈ tripleSplit A n, (1 : ℝ) / a = ∑ a ∈ A, (1 : ℝ) / a := by
  have h2 : 2 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h3 : 3 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h6 : 6 * n ∉ A.erase n := fun h ↦
    new_not_mem_of_max hn hmax (by omega) (Finset.mem_of_mem_erase h)
  have h23 : 2 * n ≠ 3 * n := by nlinarith
  have h26 : 2 * n ≠ 6 * n := by nlinarith
  have h36 : 3 * n ≠ 6 * n := by nlinarith
  have hid : (1 : ℝ) / (n : ℝ) =
      1 / ((2 * n : ℕ) : ℝ) + 1 / ((3 * n : ℕ) : ℝ) +
        1 / ((6 * n : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using one_div_eq_tripleSplit n hn
  rw [tripleSplit, Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert, ← Finset.sum_erase_add A (fun a ↦ (1 : ℝ) / a) hnA]
      · rw [hid]
        ring
      · exact h6
    · simp only [Finset.mem_insert]
      exact fun h ↦ h.elim (fun heq ↦ h36 heq) h3
  · simp only [Finset.mem_insert]
    rintro (h | h | h)
    · exact h23 h
    · exact h26 h
    · exact h2 h

lemma tripleSplit_mem_bound {A : Finset ℕ} {n b : ℕ} (hn : 0 < n)
    (hmax : ∀ a ∈ A, a ≤ n) (hb : b ∈ tripleSplit A n) : b ≤ 6 * n := by
  simp only [tripleSplit, Finset.mem_insert, Finset.mem_erase] at hb
  rcases hb with rfl | rfl | rfl | ⟨_, hb⟩
  · omega
  · omega
  · exact le_rfl
  · exact (hmax _ hb).trans (by omega)

lemma six_mul_mem_tripleSplit (A : Finset ℕ) (n : ℕ) :
    6 * n ∈ tripleSplit A n := by simp [tripleSplit]

lemma secondarySplit_card {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (h6A : 6 * n ∈ A) (hmax : ∀ a ∈ A, a ≤ 6 * n) :
    (secondarySplit A n).card = A.card + 1 := by
  have h9 : 9 * n ∉ A.erase (6 * n) := by
    intro h
    have := hmax _ (Finset.mem_of_mem_erase h)
    nlinarith
  have h18 : 18 * n ∉ A.erase (6 * n) := by
    intro h
    have := hmax _ (Finset.mem_of_mem_erase h)
    nlinarith
  have hne : 9 * n ≠ 18 * n := by nlinarith
  have h9' : 9 * n ∉ insert (18 * n) (A.erase (6 * n)) := by
    simpa [hne] using h9
  rw [secondarySplit, Finset.card_insert_of_notMem h9',
    Finset.card_insert_of_notMem h18, Finset.card_erase_of_mem h6A]
  have : 0 < A.card := Finset.card_pos.mpr ⟨6 * n, h6A⟩
  omega

lemma secondarySplit_zero_not_mem {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hzero : 0 ∉ A) : 0 ∉ secondarySplit A n := by
  simp [secondarySplit, hn.ne', hzero]

lemma secondarySplit_sum {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (h6A : 6 * n ∈ A) (hmax : ∀ a ∈ A, a ≤ 6 * n) :
    ∑ a ∈ secondarySplit A n, (1 : ℝ) / a = ∑ a ∈ A, (1 : ℝ) / a := by
  have h9 : 9 * n ∉ A.erase (6 * n) := by
    intro h
    have := hmax _ (Finset.mem_of_mem_erase h)
    nlinarith
  have h18 : 18 * n ∉ A.erase (6 * n) := by
    intro h
    have := hmax _ (Finset.mem_of_mem_erase h)
    nlinarith
  have hne : 9 * n ≠ 18 * n := by nlinarith
  have hid : (1 : ℝ) / ((6 * n : ℕ) : ℝ) =
      1 / ((9 * n : ℕ) : ℝ) + 1 / ((18 * n : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      one_div_six_eq_secondarySplit n hn
  rw [secondarySplit, Finset.sum_insert]
  · rw [Finset.sum_insert, ← Finset.sum_erase_add A (fun a ↦ (1 : ℝ) / a) h6A]
    · rw [hid]
      ring
    · exact h18
  · simp only [Finset.mem_insert]
    exact fun h ↦ h.elim hne h9

lemma secondarySplit_mem_bound {A : Finset ℕ} {n b : ℕ} (hn : 0 < n)
    (hmax : ∀ a ∈ A, a ≤ 6 * n) (hb : b ∈ secondarySplit A n) :
    b ≤ 18 * n := by
  simp only [secondarySplit, Finset.mem_insert, Finset.mem_erase] at hb
  rcases hb with rfl | rfl | ⟨_, hb⟩
  · omega
  · exact le_rfl
  · exact (hmax _ hb).trans (by omega)

lemma eighteen_mul_mem_secondarySplit (A : Finset ℕ) (n : ℕ) :
    18 * n ∈ secondarySplit A n := by simp [secondarySplit]

/-- Iterate the three-way split.  The construction adds exactly `2r` terms,
preserves the reciprocal sum, and has largest denominator `6^r n`. -/
lemma exists_iteratedTriple {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hnA : n ∈ A) (hmax : ∀ a ∈ A, a ≤ n) (hzero : 0 ∉ A) :
    ∀ r : ℕ, ∃ B : Finset ℕ,
      B.card = A.card + 2 * r ∧
      0 ∉ B ∧
      (∑ b ∈ B, (1 : ℝ) / b) = ∑ a ∈ A, (1 : ℝ) / a ∧
      6 ^ r * n ∈ B ∧
      ∀ b ∈ B, b ≤ 6 ^ r * n
  | 0 => by
      refine ⟨A, by simp, hzero, rfl, ?_, ?_⟩
      · simpa using hnA
      · simpa using hmax
  | r + 1 => by
      obtain ⟨B, hcard, hzeroB, hsum, htop, hbound⟩ :=
        exists_iteratedTriple hn hnA hmax hzero r
      let N := 6 ^ r * n
      have hN : 0 < N := by positivity
      let C := tripleSplit B N
      refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show C.card = B.card + 2 from tripleSplit_card hN htop hbound, hcard]
        omega
      · exact tripleSplit_zero_not_mem hN hzeroB
      · rw [tripleSplit_sum hN htop hbound, hsum]
      · change 6 ^ (r + 1) * n ∈ tripleSplit B N
        simpa [N, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          six_mul_mem_tripleSplit B N
      · intro b hb
        have := tripleSplit_mem_bound hN hbound hb
        change b ≤ 6 * N at this
        simpa [N, pow_succ, mul_assoc, mul_left_comm, mul_comm] using this

/-- A three-way split followed by the secondary split adds exactly three
terms and changes the largest denominator from `n` to `18n`. -/
lemma exists_plus_three {A : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hnA : n ∈ A) (hmax : ∀ a ∈ A, a ≤ n) (hzero : 0 ∉ A) :
    ∃ B : Finset ℕ,
      B.card = A.card + 3 ∧
      0 ∉ B ∧
      (∑ b ∈ B, (1 : ℝ) / b) = ∑ a ∈ A, (1 : ℝ) / a ∧
      18 * n ∈ B ∧
      ∀ b ∈ B, b ≤ 18 * n := by
  let C := tripleSplit A n
  let B := secondarySplit C n
  have hCcard : C.card = A.card + 2 := tripleSplit_card hn hnA hmax
  have hCzero : 0 ∉ C := tripleSplit_zero_not_mem hn hzero
  have hCsum : (∑ c ∈ C, (1 : ℝ) / c) = ∑ a ∈ A, (1 : ℝ) / a :=
    tripleSplit_sum hn hnA hmax
  have hCtop : 6 * n ∈ C := six_mul_mem_tripleSplit A n
  have hCbound : ∀ c ∈ C, c ≤ 6 * n := fun c hc ↦
    tripleSplit_mem_bound hn hmax hc
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show B.card = C.card + 1 from secondarySplit_card hn hCtop hCbound, hCcard]
  · exact secondarySplit_zero_not_mem hn hCzero
  · rw [secondarySplit_sum hn hCtop hCbound, hCsum]
  · exact eighteen_mul_mem_secondarySplit C n
  · intro b hb
    exact secondarySplit_mem_bound hn hCbound hb

/-- Padding by every increment `m ≥ 2`.  The stated bound is deliberately
uniform in the parity of `m`; the construction itself gives the sharper
largest denominators `6^(m/2)n` in the even case and
`18*6^((m-3)/2)n` in the odd case. -/
theorem exists_linearPadding {A : Finset ℕ} {n m : ℕ} (hn : 0 < n)
    (hnA : n ∈ A) (hmax : ∀ a ∈ A, a ≤ n) (hzero : 0 ∉ A)
    (hm : 2 ≤ m) :
    ∃ (B : Finset ℕ) (hB : B.Nonempty),
      B.card = A.card + m ∧
      0 ∉ B ∧
      (∑ b ∈ B, (1 : ℝ) / b) = ∑ a ∈ A, (1 : ℝ) / a ∧
      B.max' hB ≤ 18 * 6 ^ ((m + 1) / 2) * n := by
  rcases Nat.even_or_odd' m with ⟨r, hr | hr⟩
  · subst m
    obtain ⟨B, hcard, hzeroB, hsum, htop, hbound⟩ :=
      exists_iteratedTriple hn hnA hmax hzero r
    have hrpos : 0 < r := by omega
    have hB : B.Nonempty := ⟨6 ^ r * n, htop⟩
    refine ⟨B, hB, ?_, hzeroB, hsum, ?_⟩
    · simpa [Nat.mul_comm] using hcard
    · rw [Finset.max'_le_iff]
      intro b hb
      have hbtop := hbound b hb
      have hceil : (2 * r + 1) / 2 = r := by omega
      rw [hceil]
      calc
        b ≤ 6 ^ r * n := hbtop
        _ ≤ 18 * (6 ^ r * n) := by omega
        _ = 18 * 6 ^ r * n := by ring
  · subst m
    have hrpos : 0 < r := by omega
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrpos.ne'
    obtain ⟨C, hCcard, hCzero, hCsum, hCtop, hCbound⟩ :=
      exists_iteratedTriple hn hnA hmax hzero s
    let N := 6 ^ s * n
    have hN : 0 < N := by positivity
    obtain ⟨B, hBcard, hBzero, hBsum, hBtop, hBbound⟩ :=
      exists_plus_three hN hCtop hCbound hCzero
    have hB : B.Nonempty := ⟨18 * N, hBtop⟩
    refine ⟨B, hB, ?_, hBzero, ?_, ?_⟩
    · rw [hBcard, hCcard]
      omega
    · rw [hBsum, hCsum]
    · rw [Finset.max'_le_iff]
      intro b hb
      have hbtop := hBbound b hb
      have hceil : (2 * (s + 1) + 1 + 1) / 2 = s + 2 := by omega
      rw [hceil]
      calc
        b ≤ 18 * N := hbtop
        _ ≤ 18 * (6 ^ (s + 2) * n) := by
          dsimp [N]
          exact Nat.mul_le_mul_left 18 <|
            Nat.mul_le_mul_right n <|
              Nat.pow_le_pow_right (by omega) (by omega)
        _ = 18 * 6 ^ (s + 2) * n := by ring

/-! ## The prime-power count is sublinear -/

open Erdos285.PrimePowers

/-- Parameter pairs which can produce a proper prime power at most `y`.
The base is at most `√y` and the exponent is at most `log₂ y`. -/
def properPowerPairs (y : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 2 y.sqrt) ×ˢ (Icc 2 (Nat.log 2 y))

/-- The image of the parameter box of proper powers. -/
def properPowerValues (y : ℕ) : Finset ℕ :=
  (properPowerPairs y).image fun z ↦ z.1 ^ z.2

lemma card_properPowerPairs_le (y : ℕ) :
    (properPowerPairs y).card ≤ y.sqrt * Nat.log 2 y := by
  rw [properPowerPairs, Finset.card_product]
  exact Nat.mul_le_mul (by simp) (by simp)

lemma card_properPowerValues_le (y : ℕ) :
    (properPowerValues y).card ≤ y.sqrt * Nat.log 2 y :=
  (Finset.card_image_le.trans (card_properPowerPairs_le y))

lemma mem_properPowerValues_of_isPrimePow_not_prime {y q : ℕ}
    (hqpow : IsPrimePow q) (hqprime : ¬q.Prime) (hqy : q ≤ y) :
    q ∈ properPowerValues y := by
  rcases (isPrimePow_nat_iff_bounded_log q).mp hqpow with
    ⟨k, hklog, hkpos, p, hpq, hqeq, hp⟩
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk1 : k = 1 := by omega
    subst k
    simp only [pow_one] at hqeq
    exact hqprime (hqeq ▸ hp)
  have hpsq : p * p ≤ q := by
    rw [hqeq, ← pow_two]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hpsqrt : p ≤ y.sqrt := Nat.le_sqrt.mpr (hpsq.trans hqy)
  have hklogy : k ≤ Nat.log 2 y :=
    hklog.trans (Nat.log_mono (by omega) (by omega) hqy)
  rw [properPowerValues, Finset.mem_image]
  refine ⟨(p, k), ?_, hqeq.symm⟩
  simp [properPowerPairs, hp.two_le, hpsqrt, hk2, hklogy]

lemma primePowersUpTo_subset_primes_union_proper (y : ℕ) :
    primePowersUpTo y ⊆ y.primesLE ∪ properPowerValues y := by
  intro q hq
  have hspec := (mem_primePowersUpTo.mp hq)
  by_cases hp : q.Prime
  · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hspec.2, hp⟩)
  · exact Finset.mem_union_right _
      (mem_properPowerValues_of_isPrimePow_not_prime hspec.1 hp hspec.2)

/-- Quantitative decomposition of `π⋆`: primes contribute `π(y)`, while
proper prime powers are parametrized by at most `√y log₂ y` pairs. -/
lemma piStar_le_primeCounting_add (y : ℕ) :
    piStar y ≤ Nat.primeCounting y + y.sqrt * Nat.log 2 y := by
  calc
    piStar y = (primePowersUpTo y).card := rfl
    _ ≤ (y.primesLE ∪ properPowerValues y).card :=
      Finset.card_le_card (primePowersUpTo_subset_primes_union_proper y)
    _ ≤ y.primesLE.card + (properPowerValues y).card :=
      Finset.card_union_le _ _
    _ ≤ Nat.primeCounting y + y.sqrt * Nat.log 2 y := by
      rw [Nat.primesLE_card_eq_primeCounting]
      exact Nat.add_le_add_left (card_properPowerValues_le y) _

private lemma primeCounting_isLittleO_id :
    (fun n : ℕ ↦ (Nat.primeCounting n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hmain : (fun x : ℝ ↦ x / Real.log x) =o[atTop] id := by
    apply Asymptotics.IsLittleO.of_tendsto_div_atTop
    apply Real.tendsto_log_atTop.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    simp only [id_eq]
    field
  have hreal : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) =o[atTop] id :=
    pi_alt'.trans_isLittleO hmain
  simpa [Function.comp_def] using
    hreal.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))

private lemma sqrt_mul_logb_isLittleO_id :
    (fun x : ℝ ↦ Real.sqrt x * Real.logb 2 x) =o[atTop] id := by
  have hlog : (fun x : ℝ ↦ Real.log x ^ (1 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 1 (by norm_num)
  have hmul := hlog.mul_isBigO
    (isBigO_refl (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop)
  have hsqrtlog : (fun x : ℝ ↦ Real.sqrt x * Real.log x) =o[atTop] id := by
    apply hmul.congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp [Real.sqrt_eq_rpow, mul_comm]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      norm_num
  apply (hsqrtlog.const_mul_left (Real.log 2)⁻¹).congr'
  · filter_upwards with x
    simp only [Real.logb]
    ring
  · rfl

private lemma properPowerError_isLittleO_id :
    (fun n : ℕ ↦ (n.sqrt * Nat.log 2 n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have href : (fun n : ℕ ↦ Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    simpa [Function.comp_def] using sqrt_mul_logb_isLittleO_id.natCast_atTop
  have hcomparison : (fun n : ℕ ↦ (n.sqrt * Nat.log 2 n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards with n
    rw [Real.norm_of_nonneg (by positivity)]
    have hsqrt : (n.sqrt : ℝ) ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      have hsquare : ((n.sqrt * n.sqrt : ℕ) : ℝ) ≤ n := by
        exact_mod_cast Nat.sqrt_le n
      simpa [pow_two] using hsquare
    have hlog : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
    exact mul_le_mul hsqrt hlog (by positivity) (by positivity)
  exact hcomparison.trans_isLittleO href

/-- Martin's prime-power counting function satisfies `π⋆(y) = o(y)`.
The proof uses the local prime-number theorem for the prime contribution and
the `O(√y log y)` parameter count for proper prime powers. -/
theorem piStar_isLittleO :
    (fun y : ℕ ↦ (piStar y : ℝ)) =o[atTop] (fun y : ℕ ↦ (y : ℝ)) := by
  have hsum : (fun y : ℕ ↦ (Nat.primeCounting y : ℝ) +
      (y.sqrt * Nat.log 2 y : ℝ)) =o[atTop] (fun y : ℕ ↦ (y : ℝ)) :=
    primeCounting_isLittleO_id.add properPowerError_isLittleO_id
  have hbound : (fun y : ℕ ↦ (piStar y : ℝ)) =O[atTop]
      (fun y : ℕ ↦ (Nat.primeCounting y : ℝ) +
        (y.sqrt * Nat.log 2 y : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    exact_mod_cast piStar_le_primeCounting_add y
  exact hbound.trans_isLittleO hsum

lemma tendsto_natLog_two :
    Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop := by
  have hlogb : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).comp hlogb
  convert hfloor using 1
  funext n
  change Nat.log 2 n = ⌊Real.logb 2 (n : ℝ)⌋₊
  simpa using (Real.natFloor_logb_natCast 2 n).symm

/-- Any exponent bounded by a constant multiple of `π⋆(log₂ y)` is
`o(log y)`.  This is the exact analytic input for low-growth padding. -/
lemma exponent_isLittleO_log_of_isBigO_piStar {m : ℕ → ℕ}
    (hm : (fun y : ℕ ↦ (m y : ℝ)) =O[atTop]
      (fun y : ℕ ↦ (piStar (Nat.log 2 y) : ℝ))) :
    (fun y : ℕ ↦ (m y : ℝ)) =o[atTop]
      (fun y : ℕ ↦ Real.log (y : ℝ)) := by
  have hpiLog : (fun y : ℕ ↦ (piStar (Nat.log 2 y) : ℝ)) =o[atTop]
      (fun y : ℕ ↦ (Nat.log 2 y : ℝ)) := by
    simpa [Function.comp_def] using
      piStar_isLittleO.comp_tendsto tendsto_natLog_two
  have hnatLogO : (fun y : ℕ ↦ (Nat.log 2 y : ℝ)) =O[atTop]
      (fun y : ℕ ↦ Real.log (y : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (Real.log 2)⁻¹
    filter_upwards [eventually_ge_atTop 2] with y hy
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc
      (Nat.log 2 y : ℝ) ≤ Real.logb 2 y := Real.natLog_le_logb y 2
      _ = (Real.log 2)⁻¹ * Real.log y := by rw [Real.logb]; ring
  exact hm.trans_isLittleO hpiLog |>.trans_isBigO hnatLogO

/-- The numerical multiplier in `exists_linearPadding` is `y^ε` eventually
whenever the requested increment is `O(π⋆(log₂ y))`. -/
theorem eventually_paddingMultiplier_le_rpow {m : ℕ → ℕ}
    (hm : (fun y : ℕ ↦ (m y : ℝ)) =O[atTop]
      (fun y : ℕ ↦ (piStar (Nat.log 2 y) : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,
      ((18 * 6 ^ ((m y + 1) / 2) : ℕ) : ℝ) ≤ (y : ℝ) ^ ε := by
  have hexp := exponent_isLittleO_log_of_isBigO_piStar hm
  let δ : ℝ := ε / (2 * Real.log 6)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall := hexp.def hδ
  have hlogtend : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let C : ℝ := 2 * (Real.log 18 + Real.log 6) / ε
  have hlarge := hlogtend.eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop 2, hsmall, hlarge] with y hy hmy hylarge
  have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ y by omega))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hlogy] at hmy
  have hmterm : (m y : ℝ) * Real.log 6 ≤ ε / 2 * Real.log y := by
    calc
      (m y : ℝ) * Real.log 6 ≤ (δ * Real.log y) * Real.log 6 :=
        mul_le_mul_of_nonneg_right hmy hlog6.le
      _ = ε / 2 * Real.log y := by dsimp [δ]; field_simp
  have hconstant : Real.log 18 + Real.log 6 ≤ ε / 2 * Real.log y := by
    calc
      Real.log 18 + Real.log 6 =
          (ε / 2) * (2 * (Real.log 18 + Real.log 6) / ε) := by
            field_simp
      _ ≤ (ε / 2) * Real.log y := by
        apply mul_le_mul_of_nonneg_left
        · simpa [C] using hylarge
        · positivity
  have hexple : (((m y + 1) / 2 : ℕ) : ℝ) ≤ (m y : ℝ) + 1 := by
    exact_mod_cast Nat.div_le_self (m y + 1) 2
  have hlogbound :
      Real.log (((18 * 6 ^ ((m y + 1) / 2) : ℕ) : ℝ)) ≤
        ε * Real.log (y : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    calc
      Real.log 18 + (((m y + 1) / 2 : ℕ) : ℝ) * Real.log 6
          ≤ Real.log 18 + ((m y : ℝ) + 1) * Real.log 6 := by
            gcongr
      _ = (Real.log 18 + Real.log 6) + (m y : ℝ) * Real.log 6 := by ring
      _ ≤ ε / 2 * Real.log y + ε / 2 * Real.log y :=
        add_le_add hconstant hmterm
      _ = ε * Real.log y := by ring
  exact Real.le_rpow_of_log_le (by positivity) hlogbound

/-- If a preliminary denominator bound is `y²`, low-growth padding changes it
to at most `y^(2+ε)` eventually. -/
theorem eventually_sq_mul_paddingMultiplier_le_rpow {m : ℕ → ℕ}
    (hm : (fun y : ℕ ↦ (m y : ℝ)) =O[atTop]
      (fun y : ℕ ↦ (piStar (Nat.log 2 y) : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,
      (y : ℝ) ^ 2 * (18 * 6 ^ ((m y + 1) / 2) : ℕ) ≤
        (y : ℝ) ^ (2 + ε) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_paddingMultiplier_le_rpow hm hε] with y hy hpad
  calc
    (y : ℝ) ^ 2 * (18 * 6 ^ ((m y + 1) / 2) : ℕ)
        ≤ (y : ℝ) ^ 2 * (y : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpad (by positivity)
    _ = (y : ℝ) ^ (2 + ε) := by
      rw [Real.rpow_add (by positivity)]
      norm_num

end

end Erdos285.LinearPadding

#print axioms Erdos285.LinearPadding.tripleSplit_sum
#print axioms Erdos285.LinearPadding.secondarySplit_sum
#print axioms Erdos285.LinearPadding.exists_linearPadding
#print axioms Erdos285.LinearPadding.piStar_isLittleO
#print axioms Erdos285.LinearPadding.eventually_paddingMultiplier_le_rpow
#print axioms Erdos285.LinearPadding.eventually_sq_mul_paddingMultiplier_le_rpow
