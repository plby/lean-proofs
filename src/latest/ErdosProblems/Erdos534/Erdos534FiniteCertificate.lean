import Mathlib

/-! Proof-producing finite certificate for the bounded prime-counting range. -/

def divisorBlockB (n lo len : ℕ) : Bool :=
  (List.range len).all fun k ↦
    decide (lo + k < 2 ∨ n < (lo + k) * (lo + k) ∨ ¬lo + k ∣ n)

def noDivisorsB (n : ℕ) : Bool :=
  divisorBlockB n 0 50 && divisorBlockB n 50 50 &&
  divisorBlockB n 100 50 && divisorBlockB n 150 50 &&
  divisorBlockB n 200 50 && divisorBlockB n 250 50 &&
  divisorBlockB n 300 17

def fastPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && noDivisorsB n

lemma fastPrimeB_eq_true_iff {n : ℕ} (hnBound : n ≤ 100000) :
    fastPrimeB n = true ↔ n.Prime := by
  simp only [fastPrimeB, Bool.and_eq_true, decide_eq_true_eq, noDivisorsB,
    divisorBlockB, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hn, h⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hn, fun m hm2 hmsqrt ↦ ?_⟩
    have hsqrt : n.sqrt < 317 := by
      nlinarith [Nat.sqrt_le n]
    have hm317 : m < 317 := hmsqrt.trans_lt hsqrt
    have hmPred : m < 2 ∨ n < m * m ∨ ¬m ∣ n := by
      rcases h with ⟨⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩
      by_cases hm50 : m < 50
      · simpa using h₀ m hm50
      by_cases hm100 : m < 100
      · have heq : 50 + (m - 50) = m := by omega
        simpa only [heq] using h₁ (m - 50) (by omega)
      by_cases hm150 : m < 150
      · have heq : 100 + (m - 100) = m := by omega
        simpa only [heq] using h₂ (m - 100) (by omega)
      by_cases hm200 : m < 200
      · have heq : 150 + (m - 150) = m := by omega
        simpa only [heq] using h₃ (m - 150) (by omega)
      by_cases hm250 : m < 250
      · have heq : 200 + (m - 200) = m := by omega
        simpa only [heq] using h₄ (m - 200) (by omega)
      by_cases hm300 : m < 300
      · have heq : 250 + (m - 250) = m := by omega
        simpa only [heq] using h₅ (m - 250) (by omega)
      · have heq : 300 + (m - 300) = m := by omega
        simpa only [heq] using h₆ (m - 300) (by omega)
    rcases hmPred with hm | hm | hm
    · omega
    · exact (not_lt_of_ge (Nat.le_sqrt.mp hmsqrt) hm).elim
    · exact hm
  · intro hn
    have hdef := Nat.prime_def_le_sqrt.mp hn
    have hpred (m : ℕ) : m < 2 ∨ n < m * m ∨ ¬m ∣ n := by
      by_cases hm2 : m < 2
      · exact Or.inl hm2
      by_cases hsq : n < m * m
      · exact Or.inr (Or.inl hsq)
      · exact Or.inr (Or.inr
          (hdef.2 m (by omega) (Nat.le_sqrt.mpr (by omega))))
    refine ⟨hdef.1, ?_⟩
    exact ⟨⟨⟨⟨⟨⟨
      (fun k _ ↦ by simpa using hpred k),
      (fun k _ ↦ hpred (50 + k))⟩,
      (fun k _ ↦ hpred (100 + k))⟩,
      (fun k _ ↦ hpred (150 + k))⟩,
      (fun k _ ↦ hpred (200 + k))⟩,
      (fun k _ ↦ hpred (250 + k))⟩,
      (fun k _ ↦ hpred (300 + k))⟩

def smallPrimes0 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def smallPrimes1 : List ℕ :=
  [53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
def smallPrimes2 : List ℕ :=
  [101, 103, 107, 109, 113, 127, 131, 137, 139, 149]
def smallPrimes3 : List ℕ :=
  [151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]
def smallPrimes4 : List ℕ :=
  [211, 223, 227, 229, 233, 239, 241]
def smallPrimes5 : List ℕ :=
  [251, 257, 263, 269, 271, 277, 281, 283, 293]
def smallPrimes6 : List ℕ := [307, 311, 313]

def smallPrimes : List ℕ :=
  smallPrimes0 ++ smallPrimes1 ++ smallPrimes2 ++ smallPrimes3 ++
    smallPrimes4 ++ smallPrimes5 ++ smallPrimes6

lemma prime_of_mem_smallPrimes {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · have hp_le : p ≤ 47 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes0] at *
  · have hp_lo : 53 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 97 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes1] at *
  · have hp_lo : 101 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 149 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes2] at *
  · have hp_lo : 151 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 199 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes3] at *
  · have hp_lo : 211 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 241 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes4] at *
  · have hp_lo : 251 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 293 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes5] at *
  · have hp_lo : 307 ≤ p := List.minimum_le_of_mem hp (by decide)
    have hp_le : p ≤ 313 := List.le_maximum_of_mem hp (by decide)
    interval_cases p <;> norm_num [smallPrimes6] at *

lemma mem_smallPrimes_of_prime_lt {p : ℕ} (hp : p.Prime) (hlt : p < 317) :
    p ∈ smallPrimes := by
  have hp2 := hp.two_le
  by_cases h50 : p < 50
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  by_cases h100 : p < 100
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  by_cases h150 : p < 150
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  by_cases h200 : p < 200
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  by_cases h250 : p < 250
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  by_cases h300 : p < 300
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *
  · interval_cases p <;> norm_num [smallPrimes, smallPrimes0, smallPrimes1,
      smallPrimes2, smallPrimes3, smallPrimes4, smallPrimes5, smallPrimes6] at *

def listedPrimeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes.all fun p ↦ decide (p = n ∨ ¬p ∣ n)

lemma listedPrimeB_eq_true_iff {n : ℕ} (hnBound : n ≤ 100000) :
    listedPrimeB n = true ↔ n.Prime := by
  simp only [listedPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hn2, hall⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hn2, fun m hm2 hmsqrt ↦ ?_⟩
    intro hmn
    obtain ⟨p, hpPrime, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hp_le_m : p ≤ m := Nat.le_of_dvd (by omega) hpm
    have hp_sqrt : p ≤ n.sqrt := hp_le_m.trans hmsqrt
    have hp_lt : p < 317 := by
      have hsqrt : n.sqrt < 317 := by nlinarith [Nat.sqrt_le n]
      exact hp_sqrt.trans_lt hsqrt
    have hpMem := mem_smallPrimes_of_prime_lt hpPrime hp_lt
    rcases hall p hpMem with hpn | hpndvd
    · subst p
      have hn_sqrt : n ≤ n.sqrt := hp_sqrt
      exact (not_le_of_gt (Nat.sqrt_lt_self (by omega))) hn_sqrt
    · exact hpndvd (hpm.trans hmn)
  · intro hn
    refine ⟨hn.two_le, ?_⟩
    intro p hpMem
    have hp := prime_of_mem_smallPrimes hpMem
    by_cases hpn : p = n
    · exact Or.inl hpn
    · exact Or.inr fun hpdvd ↦ hpn ((Nat.prime_dvd_prime_iff_eq hp hn).mp hpdvd)

def primeStep (x : ℕ) : ℤ :=
  (if listedPrimeB (5 * x + 1) then 1 else 0) +
  (if listedPrimeB (5 * x + 2) then 1 else 0) +
  (if listedPrimeB (5 * x + 3) then 1 else 0) +
  (if listedPrimeB (5 * x + 4) then 1 else 0) +
  (if listedPrimeB (5 * x + 5) then 1 else 0) -
  3 * (if listedPrimeB (x + 1) then 1 else 0)

def checkBlock : ℕ → ℕ → ℤ → Option ℤ
  | _, 0, d => some d
  | x, n + 1, d =>
      let d' := d + primeStep x
      if 0 ≤ d' then checkBlock (x + 1) n d' else none

def primeMargin (x : ℕ) : ℤ :=
  (Nat.primeCounting (5 * x) : ℤ) - 3 * Nat.primeCounting x

lemma primeCounting_succ_int (n : ℕ) :
    (Nat.primeCounting (n + 1) : ℤ) =
      Nat.primeCounting n + (if (n + 1).Prime then 1 else 0) := by
  change (Nat.count Nat.Prime ((n + 1) + 1) : ℤ) =
    Nat.count Nat.Prime (n + 1) + _
  rw [Nat.count_succ]
  split <;> simp

lemma primeStep_eq_margin_sub {x : ℕ} (hx : x + 1 ≤ 20000) :
    primeStep x = primeMargin (x + 1) - primeMargin x := by
  have h₁ := listedPrimeB_eq_true_iff (n := 5 * x + 1) (by omega)
  have h₂ := listedPrimeB_eq_true_iff (n := 5 * x + 2) (by omega)
  have h₃ := listedPrimeB_eq_true_iff (n := 5 * x + 3) (by omega)
  have h₄ := listedPrimeB_eq_true_iff (n := 5 * x + 4) (by omega)
  have h₅ := listedPrimeB_eq_true_iff (n := 5 * x + 5) (by omega)
  have hx₁ := listedPrimeB_eq_true_iff (n := x + 1) (by omega)
  simp only [primeStep, primeMargin]
  rw [show 5 * (x + 1) = 5 * x + 5 by omega]
  rw [show 5 * x + 5 = ((((5 * x + 1) + 1) + 1) + 1) + 1 by omega]
  rw [primeCounting_succ_int, primeCounting_succ_int,
    primeCounting_succ_int, primeCounting_succ_int,
    primeCounting_succ_int]
  rw [primeCounting_succ_int]
  simp only [show 5 * x + 1 + 1 = 5 * x + 2 by omega,
    show 5 * x + 2 + 1 = 5 * x + 3 by omega,
    show 5 * x + 3 + 1 = 5 * x + 4 by omega,
    show 5 * x + 4 + 1 = 5 * x + 5 by omega,
    ← h₁, ← h₂, ← h₃, ← h₄, ← h₅, ← hx₁]
  ring

lemma checkBlock_sound {x n : ℕ} {d d' : ℤ}
    (hcheck : checkBlock x n d = some d')
    (hd : d = primeMargin x) (hbound : x + n ≤ 20000) :
    d' = primeMargin (x + n) ∧
      ∀ y, x < y → y ≤ x + n → 0 ≤ primeMargin y := by
  induction n generalizing x d d' with
  | zero =>
      simp only [checkBlock, Option.some.injEq] at hcheck
      subst d'
      constructor
      · simpa [hd]
      · intro y hxy hy
        omega
  | succ n ih =>
      have hxnext : x + 1 ≤ 20000 := by omega
      have hstep := primeStep_eq_margin_sub hxnext
      have hdnext : d + primeStep x = primeMargin (x + 1) := by
        rw [hd, hstep]
        ring
      have hnonneg : 0 ≤ d + primeStep x := by
        by_contra hneg
        simp [checkBlock, hneg] at hcheck
      have htail : checkBlock (x + 1) n (d + primeStep x) = some d' := by
        simpa [checkBlock, hnonneg] using hcheck
      have hih := ih htail hdnext (by omega)
      constructor
      · rw [show x + (n + 1) = x + 1 + n by omega]
        exact hih.1
      · intro y hxy hy
        by_cases hyEq : y = x + 1
        · subst y
          simpa [hdnext] using hnonneg
        · apply hih.2 y <;> omega

def checkBlocks : ℕ → ℕ → ℤ → Option ℤ
  | _, 0, d => some d
  | x, k + 1, d =>
      match checkBlock x 100 d with
      | none => none
      | some d' => checkBlocks (x + 100) k d'

lemma checkBlocks_sound {x k : ℕ} {d d' : ℤ}
    (hcheck : checkBlocks x k d = some d')
    (hd : d = primeMargin x) (hbound : x + 100 * k ≤ 20000) :
    d' = primeMargin (x + 100 * k) ∧
      ∀ y, x < y → y ≤ x + 100 * k → 0 ≤ primeMargin y := by
  induction k generalizing x d d' with
  | zero =>
      simp only [checkBlocks, Option.some.injEq, mul_zero, add_zero] at hcheck ⊢
      subst d'
      exact ⟨hd, by omega⟩
  | succ k ih =>
      cases hfirst : checkBlock x 100 d with
      | none => simp [checkBlocks, hfirst] at hcheck
      | some dnext =>
          have hfirstSound := checkBlock_sound hfirst hd (by omega)
          have htail : checkBlocks (x + 100) k dnext = some d' := by
            simpa [checkBlocks, hfirst] using hcheck
          have htailSound := ih htail hfirstSound.1 (by omega)
          constructor
          · rw [show x + 100 * (k + 1) = x + 100 + 100 * k by omega]
            exact htailSound.1
          · intro y hxy hy
            by_cases hyFirst : y ≤ x + 100
            · exact hfirstSound.2 y hxy hyFirst
            · apply htailSound.2 y <;> omega

structure MarginCertificate (x : ℕ) (d : ℤ) : Prop where
  eq_margin : d = primeMargin x
  nonneg : ∀ y, 8 ≤ y → y ≤ x → 0 ≤ primeMargin y

lemma MarginCertificate.extend {x n : ℕ} {d d' : ℤ}
    (h : MarginCertificate x d) (hcheck : checkBlock x n d = some d')
    (hbound : x + n ≤ 20000) : MarginCertificate (x + n) d' := by
  have hs := checkBlock_sound hcheck h.eq_margin hbound
  refine ⟨hs.1, ?_⟩
  intro y hy8 hyend
  by_cases hyx : y ≤ x
  · exact h.nonneg y hy8 hyx
  · exact hs.2 y (by omega) hyend

lemma marginCertificate0 : MarginCertificate 8 0 := by
  constructor
  · decide
  · intro y hy8 hy
    have : y = 8 := by omega
    subst y
    have hmargin : primeMargin 8 = 0 := by decide
    omega

lemma marginCertificate1 : MarginCertificate 108 15 := by
  exact MarginCertificate.extend marginCertificate0
    (by decide : checkBlock 8 100 0 = some 15) (by norm_num)

lemma marginCertificate2 : MarginCertificate 208 37 := by
  exact MarginCertificate.extend marginCertificate1
    (by decide : checkBlock 108 100 15 = some 37) (by norm_num)

lemma marginCertificate3 : MarginCertificate 308 53 := by
  exact MarginCertificate.extend marginCertificate2
    (by decide : checkBlock 208 100 37 = some 53) (by norm_num)

lemma marginCertificate4 : MarginCertificate 408 72 := by
  exact MarginCertificate.extend marginCertificate3
    (by decide : checkBlock 308 100 53 = some 72) (by norm_num)

lemma marginCertificate5 : MarginCertificate 508 83 := by
  exact MarginCertificate.extend marginCertificate4
    (by decide : checkBlock 408 100 72 = some 83) (by norm_num)

lemma marginCertificate6 : MarginCertificate 608 102 := by
  exact MarginCertificate.extend marginCertificate5
    (by decide : checkBlock 508 100 83 = some 102) (by norm_num)

lemma marginCertificate7 : MarginCertificate 708 117 := by
  exact MarginCertificate.extend marginCertificate6
    (by decide : checkBlock 608 100 102 = some 117) (by norm_num)

lemma marginCertificate8 : MarginCertificate 808 140 := by
  exact MarginCertificate.extend marginCertificate7
    (by decide : checkBlock 708 100 117 = some 140) (by norm_num)

lemma marginCertificate9 : MarginCertificate 908 150 := by
  exact MarginCertificate.extend marginCertificate8
    (by decide : checkBlock 808 100 140 = some 150) (by norm_num)

lemma marginCertificate10 : MarginCertificate 1008 171 := by
  exact MarginCertificate.extend marginCertificate9
    (by decide : checkBlock 908 100 150 = some 171) (by norm_num)

lemma marginCertificate11 : MarginCertificate 1108 177 := by
  exact MarginCertificate.extend marginCertificate10
    (by decide : checkBlock 1008 100 171 = some 177) (by norm_num)

lemma marginCertificate12 : MarginCertificate 1208 196 := by
  exact MarginCertificate.extend marginCertificate11
    (by decide : checkBlock 1108 100 177 = some 196) (by norm_num)

lemma marginCertificate13 : MarginCertificate 1308 202 := by
  exact MarginCertificate.extend marginCertificate12
    (by decide : checkBlock 1208 100 196 = some 202) (by norm_num)

lemma marginCertificate14 : MarginCertificate 1408 239 := by
  exact MarginCertificate.extend marginCertificate13
    (by decide : checkBlock 1308 100 202 = some 239) (by norm_num)

lemma marginCertificate15 : MarginCertificate 1508 238 := by
  exact MarginCertificate.extend marginCertificate14
    (by decide : checkBlock 1408 100 239 = some 238) (by norm_num)

lemma marginCertificate16 : MarginCertificate 1608 252 := by
  exact MarginCertificate.extend marginCertificate15
    (by decide : checkBlock 1508 100 238 = some 252) (by norm_num)

lemma marginCertificate17 : MarginCertificate 1708 267 := by
  exact MarginCertificate.extend marginCertificate16
    (by decide : checkBlock 1608 100 252 = some 267) (by norm_num)

lemma marginCertificate18 : MarginCertificate 1808 285 := by
  exact MarginCertificate.extend marginCertificate17
    (by decide : checkBlock 1708 100 267 = some 285) (by norm_num)

lemma marginCertificate19 : MarginCertificate 1908 305 := by
  exact MarginCertificate.extend marginCertificate18
    (by decide : checkBlock 1808 100 285 = some 305) (by norm_num)

lemma marginCertificate20 : MarginCertificate 2008 321 := by
  exact MarginCertificate.extend marginCertificate19
    (by decide : checkBlock 1908 100 305 = some 321) (by norm_num)

lemma marginCertificate21 : MarginCertificate 2108 337 := by
  exact MarginCertificate.extend marginCertificate20
    (by decide : checkBlock 2008 100 321 = some 337) (by norm_num)

lemma marginCertificate22 : MarginCertificate 2208 350 := by
  exact MarginCertificate.extend marginCertificate21
    (by decide : checkBlock 2108 100 337 = some 350) (by norm_num)

lemma marginCertificate23 : MarginCertificate 2308 364 := by
  exact MarginCertificate.extend marginCertificate22
    (by decide : checkBlock 2208 100 350 = some 364) (by norm_num)

lemma marginCertificate24 : MarginCertificate 2408 370 := by
  exact MarginCertificate.extend marginCertificate23
    (by decide : checkBlock 2308 100 364 = some 370) (by norm_num)

lemma marginCertificate25 : MarginCertificate 2508 393 := by
  exact MarginCertificate.extend marginCertificate24
    (by decide : checkBlock 2408 100 370 = some 393) (by norm_num)

lemma marginCertificate26 : MarginCertificate 2608 419 := by
  exact MarginCertificate.extend marginCertificate25
    (by decide : checkBlock 2508 100 393 = some 419) (by norm_num)

lemma marginCertificate27 : MarginCertificate 2708 421 := by
  exact MarginCertificate.extend marginCertificate26
    (by decide : checkBlock 2608 100 419 = some 421) (by norm_num)

lemma marginCertificate28 : MarginCertificate 2808 429 := by
  exact MarginCertificate.extend marginCertificate27
    (by decide : checkBlock 2708 100 421 = some 429) (by norm_num)

lemma marginCertificate29 : MarginCertificate 2908 442 := by
  exact MarginCertificate.extend marginCertificate28
    (by decide : checkBlock 2808 100 429 = some 442) (by norm_num)

lemma marginCertificate30 : MarginCertificate 3008 464 := by
  exact MarginCertificate.extend marginCertificate29
    (by decide : checkBlock 2908 100 442 = some 464) (by norm_num)

lemma marginCertificate31 : MarginCertificate 3108 486 := by
  exact MarginCertificate.extend marginCertificate30
    (by decide : checkBlock 3008 100 464 = some 486) (by norm_num)

lemma marginCertificate32 : MarginCertificate 3208 506 := by
  exact MarginCertificate.extend marginCertificate31
    (by decide : checkBlock 3108 100 486 = some 506) (by norm_num)

lemma marginCertificate33 : MarginCertificate 3308 519 := by
  exact MarginCertificate.extend marginCertificate32
    (by decide : checkBlock 3208 100 506 = some 519) (by norm_num)

lemma marginCertificate34 : MarginCertificate 3408 528 := by
  exact MarginCertificate.extend marginCertificate33
    (by decide : checkBlock 3308 100 519 = some 528) (by norm_num)

lemma marginCertificate35 : MarginCertificate 3508 550 := by
  exact MarginCertificate.extend marginCertificate34
    (by decide : checkBlock 3408 100 528 = some 550) (by norm_num)

lemma marginCertificate36 : MarginCertificate 3608 553 := by
  exact MarginCertificate.extend marginCertificate35
    (by decide : checkBlock 3508 100 550 = some 553) (by norm_num)

lemma marginCertificate37 : MarginCertificate 3708 572 := by
  exact MarginCertificate.extend marginCertificate36
    (by decide : checkBlock 3608 100 553 = some 572) (by norm_num)

lemma marginCertificate38 : MarginCertificate 3808 576 := by
  exact MarginCertificate.extend marginCertificate37
    (by decide : checkBlock 3708 100 572 = some 576) (by norm_num)

lemma marginCertificate39 : MarginCertificate 3908 595 := by
  exact MarginCertificate.extend marginCertificate38
    (by decide : checkBlock 3808 100 576 = some 595) (by norm_num)

lemma marginCertificate40 : MarginCertificate 4008 607 := by
  exact MarginCertificate.extend marginCertificate39
    (by decide : checkBlock 3908 100 595 = some 607) (by norm_num)

lemma marginCertificate41 : MarginCertificate 4108 622 := by
  exact MarginCertificate.extend marginCertificate40
    (by decide : checkBlock 4008 100 607 = some 622) (by norm_num)

lemma marginCertificate42 : MarginCertificate 4208 642 := by
  exact MarginCertificate.extend marginCertificate41
    (by decide : checkBlock 4108 100 622 = some 642) (by norm_num)

lemma marginCertificate43 : MarginCertificate 4308 647 := by
  exact MarginCertificate.extend marginCertificate42
    (by decide : checkBlock 4208 100 642 = some 647) (by norm_num)

lemma marginCertificate44 : MarginCertificate 4408 673 := by
  exact MarginCertificate.extend marginCertificate43
    (by decide : checkBlock 4308 100 647 = some 673) (by norm_num)

lemma marginCertificate45 : MarginCertificate 4508 685 := by
  exact MarginCertificate.extend marginCertificate44
    (by decide : checkBlock 4408 100 673 = some 685) (by norm_num)

lemma marginCertificate46 : MarginCertificate 4608 702 := by
  exact MarginCertificate.extend marginCertificate45
    (by decide : checkBlock 4508 100 685 = some 702) (by norm_num)

lemma marginCertificate47 : MarginCertificate 4708 712 := by
  exact MarginCertificate.extend marginCertificate46
    (by decide : checkBlock 4608 100 702 = some 712) (by norm_num)

lemma marginCertificate48 : MarginCertificate 4808 732 := by
  exact MarginCertificate.extend marginCertificate47
    (by decide : checkBlock 4708 100 712 = some 732) (by norm_num)

lemma marginCertificate49 : MarginCertificate 4908 757 := by
  exact MarginCertificate.extend marginCertificate48
    (by decide : checkBlock 4808 100 732 = some 757) (by norm_num)

lemma marginCertificate50 : MarginCertificate 5008 756 := by
  exact MarginCertificate.extend marginCertificate49
    (by decide : checkBlock 4908 100 757 = some 756) (by norm_num)

lemma marginCertificate51 : MarginCertificate 5108 763 := by
  exact MarginCertificate.extend marginCertificate50
    (by decide : checkBlock 5008 100 756 = some 763) (by norm_num)

lemma marginCertificate52 : MarginCertificate 5208 788 := by
  exact MarginCertificate.extend marginCertificate51
    (by decide : checkBlock 5108 100 763 = some 788) (by norm_num)

lemma marginCertificate53 : MarginCertificate 5308 804 := by
  exact MarginCertificate.extend marginCertificate52
    (by decide : checkBlock 5208 100 788 = some 804) (by norm_num)

lemma marginCertificate54 : MarginCertificate 5408 825 := by
  exact MarginCertificate.extend marginCertificate53
    (by decide : checkBlock 5308 100 804 = some 825) (by norm_num)

lemma marginCertificate55 : MarginCertificate 5508 824 := by
  exact MarginCertificate.extend marginCertificate54
    (by decide : checkBlock 5408 100 825 = some 824) (by norm_num)

lemma marginCertificate56 : MarginCertificate 5608 845 := by
  exact MarginCertificate.extend marginCertificate55
    (by decide : checkBlock 5508 100 824 = some 845) (by norm_num)

lemma marginCertificate57 : MarginCertificate 5708 850 := by
  exact MarginCertificate.extend marginCertificate56
    (by decide : checkBlock 5608 100 845 = some 850) (by norm_num)

lemma marginCertificate58 : MarginCertificate 5808 873 := by
  exact MarginCertificate.extend marginCertificate57
    (by decide : checkBlock 5708 100 850 = some 873) (by norm_num)

lemma marginCertificate59 : MarginCertificate 5908 876 := by
  exact MarginCertificate.extend marginCertificate58
    (by decide : checkBlock 5808 100 873 = some 876) (by norm_num)

lemma marginCertificate60 : MarginCertificate 6008 896 := by
  exact MarginCertificate.extend marginCertificate59
    (by decide : checkBlock 5908 100 876 = some 896) (by norm_num)

lemma marginCertificate61 : MarginCertificate 6108 909 := by
  exact MarginCertificate.extend marginCertificate60
    (by decide : checkBlock 6008 100 896 = some 909) (by norm_num)

lemma marginCertificate62 : MarginCertificate 6208 923 := by
  exact MarginCertificate.extend marginCertificate61
    (by decide : checkBlock 6108 100 909 = some 923) (by norm_num)

lemma marginCertificate63 : MarginCertificate 6308 933 := by
  exact MarginCertificate.extend marginCertificate62
    (by decide : checkBlock 6208 100 923 = some 933) (by norm_num)

lemma marginCertificate64 : MarginCertificate 6408 934 := by
  exact MarginCertificate.extend marginCertificate63
    (by decide : checkBlock 6308 100 933 = some 934) (by norm_num)

lemma marginCertificate65 : MarginCertificate 6508 966 := by
  exact MarginCertificate.extend marginCertificate64
    (by decide : checkBlock 6408 100 934 = some 966) (by norm_num)

lemma marginCertificate66 : MarginCertificate 6608 980 := by
  exact MarginCertificate.extend marginCertificate65
    (by decide : checkBlock 6508 100 966 = some 980) (by norm_num)

lemma marginCertificate67 : MarginCertificate 6708 995 := by
  exact MarginCertificate.extend marginCertificate66
    (by decide : checkBlock 6608 100 980 = some 995) (by norm_num)

lemma marginCertificate68 : MarginCertificate 6808 1014 := by
  exact MarginCertificate.extend marginCertificate67
    (by decide : checkBlock 6708 100 995 = some 1014) (by norm_num)

lemma marginCertificate69 : MarginCertificate 6908 1026 := by
  exact MarginCertificate.extend marginCertificate68
    (by decide : checkBlock 6808 100 1014 = some 1026) (by norm_num)

lemma marginCertificate70 : MarginCertificate 7008 1031 := by
  exact MarginCertificate.extend marginCertificate69
    (by decide : checkBlock 6908 100 1026 = some 1031) (by norm_num)

lemma marginCertificate71 : MarginCertificate 7108 1055 := by
  exact MarginCertificate.extend marginCertificate70
    (by decide : checkBlock 7008 100 1031 = some 1055) (by norm_num)

lemma marginCertificate72 : MarginCertificate 7208 1069 := by
  exact MarginCertificate.extend marginCertificate71
    (by decide : checkBlock 7108 100 1055 = some 1069) (by norm_num)

lemma marginCertificate73 : MarginCertificate 7308 1080 := by
  exact MarginCertificate.extend marginCertificate72
    (by decide : checkBlock 7208 100 1069 = some 1080) (by norm_num)

lemma marginCertificate74 : MarginCertificate 7408 1111 := by
  exact MarginCertificate.extend marginCertificate73
    (by decide : checkBlock 7308 100 1080 = some 1111) (by norm_num)

lemma marginCertificate75 : MarginCertificate 7508 1121 := by
  exact MarginCertificate.extend marginCertificate74
    (by decide : checkBlock 7408 100 1111 = some 1121) (by norm_num)

lemma marginCertificate76 : MarginCertificate 7608 1118 := by
  exact MarginCertificate.extend marginCertificate75
    (by decide : checkBlock 7508 100 1121 = some 1118) (by norm_num)

lemma marginCertificate77 : MarginCertificate 7708 1125 := by
  exact MarginCertificate.extend marginCertificate76
    (by decide : checkBlock 7608 100 1118 = some 1125) (by norm_num)

lemma marginCertificate78 : MarginCertificate 7808 1148 := by
  exact MarginCertificate.extend marginCertificate77
    (by decide : checkBlock 7708 100 1125 = some 1148) (by norm_num)

lemma marginCertificate79 : MarginCertificate 7908 1162 := by
  exact MarginCertificate.extend marginCertificate78
    (by decide : checkBlock 7808 100 1148 = some 1162) (by norm_num)

lemma marginCertificate80 : MarginCertificate 8008 1187 := by
  exact MarginCertificate.extend marginCertificate79
    (by decide : checkBlock 7908 100 1162 = some 1187) (by norm_num)

lemma marginCertificate81 : MarginCertificate 8108 1193 := by
  exact MarginCertificate.extend marginCertificate80
    (by decide : checkBlock 8008 100 1187 = some 1193) (by norm_num)

lemma marginCertificate82 : MarginCertificate 8208 1211 := by
  exact MarginCertificate.extend marginCertificate81
    (by decide : checkBlock 8108 100 1193 = some 1211) (by norm_num)

lemma marginCertificate83 : MarginCertificate 8308 1218 := by
  exact MarginCertificate.extend marginCertificate82
    (by decide : checkBlock 8208 100 1211 = some 1218) (by norm_num)

lemma marginCertificate84 : MarginCertificate 8408 1243 := by
  exact MarginCertificate.extend marginCertificate83
    (by decide : checkBlock 8308 100 1218 = some 1243) (by norm_num)

lemma marginCertificate85 : MarginCertificate 8508 1269 := by
  exact MarginCertificate.extend marginCertificate84
    (by decide : checkBlock 8408 100 1243 = some 1269) (by norm_num)

lemma marginCertificate86 : MarginCertificate 8608 1285 := by
  exact MarginCertificate.extend marginCertificate85
    (by decide : checkBlock 8508 100 1269 = some 1285) (by norm_num)

lemma marginCertificate87 : MarginCertificate 8708 1280 := by
  exact MarginCertificate.extend marginCertificate86
    (by decide : checkBlock 8608 100 1285 = some 1280) (by norm_num)

lemma marginCertificate88 : MarginCertificate 8808 1292 := by
  exact MarginCertificate.extend marginCertificate87
    (by decide : checkBlock 8708 100 1280 = some 1292) (by norm_num)

lemma marginCertificate89 : MarginCertificate 8908 1306 := by
  exact MarginCertificate.extend marginCertificate88
    (by decide : checkBlock 8808 100 1292 = some 1306) (by norm_num)

lemma marginCertificate90 : MarginCertificate 9008 1320 := by
  exact MarginCertificate.extend marginCertificate89
    (by decide : checkBlock 8908 100 1306 = some 1320) (by norm_num)

lemma marginCertificate91 : MarginCertificate 9108 1333 := by
  exact MarginCertificate.extend marginCertificate90
    (by decide : checkBlock 9008 100 1320 = some 1333) (by norm_num)

lemma marginCertificate92 : MarginCertificate 9208 1340 := by
  exact MarginCertificate.extend marginCertificate91
    (by decide : checkBlock 9108 100 1333 = some 1340) (by norm_num)

lemma marginCertificate93 : MarginCertificate 9308 1356 := by
  exact MarginCertificate.extend marginCertificate92
    (by decide : checkBlock 9208 100 1340 = some 1356) (by norm_num)

lemma marginCertificate94 : MarginCertificate 9408 1363 := by
  exact MarginCertificate.extend marginCertificate93
    (by decide : checkBlock 9308 100 1356 = some 1363) (by norm_num)

lemma marginCertificate95 : MarginCertificate 9508 1370 := by
  exact MarginCertificate.extend marginCertificate94
    (by decide : checkBlock 9408 100 1363 = some 1370) (by norm_num)

lemma marginCertificate96 : MarginCertificate 9608 1394 := by
  exact MarginCertificate.extend marginCertificate95
    (by decide : checkBlock 9508 100 1370 = some 1394) (by norm_num)

lemma marginCertificate97 : MarginCertificate 9708 1403 := by
  exact MarginCertificate.extend marginCertificate96
    (by decide : checkBlock 9608 100 1394 = some 1403) (by norm_num)

lemma marginCertificate98 : MarginCertificate 9808 1414 := by
  exact MarginCertificate.extend marginCertificate97
    (by decide : checkBlock 9708 100 1403 = some 1414) (by norm_num)

lemma marginCertificate99 : MarginCertificate 9908 1424 := by
  exact MarginCertificate.extend marginCertificate98
    (by decide : checkBlock 9808 100 1414 = some 1424) (by norm_num)

lemma marginCertificate100 : MarginCertificate 10008 1446 := by
  exact MarginCertificate.extend marginCertificate99
    (by decide : checkBlock 9908 100 1424 = some 1446) (by norm_num)

lemma marginCertificate101 : MarginCertificate 10108 1460 := by
  exact MarginCertificate.extend marginCertificate100
    (by decide : checkBlock 10008 100 1446 = some 1460) (by norm_num)

lemma marginCertificate102 : MarginCertificate 10208 1468 := by
  exact MarginCertificate.extend marginCertificate101
    (by decide : checkBlock 10108 100 1460 = some 1468) (by norm_num)

lemma marginCertificate103 : MarginCertificate 10308 1483 := by
  exact MarginCertificate.extend marginCertificate102
    (by decide : checkBlock 10208 100 1468 = some 1483) (by norm_num)

lemma marginCertificate104 : MarginCertificate 10408 1500 := by
  exact MarginCertificate.extend marginCertificate103
    (by decide : checkBlock 10308 100 1483 = some 1500) (by norm_num)

lemma marginCertificate105 : MarginCertificate 10508 1508 := by
  exact MarginCertificate.extend marginCertificate104
    (by decide : checkBlock 10408 100 1500 = some 1508) (by norm_num)

lemma marginCertificate106 : MarginCertificate 10608 1528 := by
  exact MarginCertificate.extend marginCertificate105
    (by decide : checkBlock 10508 100 1508 = some 1528) (by norm_num)

lemma marginCertificate107 : MarginCertificate 10708 1543 := by
  exact MarginCertificate.extend marginCertificate106
    (by decide : checkBlock 10608 100 1528 = some 1543) (by norm_num)

lemma marginCertificate108 : MarginCertificate 10808 1559 := by
  exact MarginCertificate.extend marginCertificate107
    (by decide : checkBlock 10708 100 1543 = some 1559) (by norm_num)

lemma marginCertificate109 : MarginCertificate 10908 1571 := by
  exact MarginCertificate.extend marginCertificate108
    (by decide : checkBlock 10808 100 1559 = some 1571) (by norm_num)

lemma marginCertificate110 : MarginCertificate 11008 1585 := by
  exact MarginCertificate.extend marginCertificate109
    (by decide : checkBlock 10908 100 1571 = some 1585) (by norm_num)

lemma marginCertificate111 : MarginCertificate 11108 1600 := by
  exact MarginCertificate.extend marginCertificate110
    (by decide : checkBlock 11008 100 1585 = some 1600) (by norm_num)

lemma marginCertificate112 : MarginCertificate 11208 1618 := by
  exact MarginCertificate.extend marginCertificate111
    (by decide : checkBlock 11108 100 1600 = some 1618) (by norm_num)

lemma marginCertificate113 : MarginCertificate 11308 1637 := by
  exact MarginCertificate.extend marginCertificate112
    (by decide : checkBlock 11208 100 1618 = some 1637) (by norm_num)

lemma marginCertificate114 : MarginCertificate 11408 1655 := by
  exact MarginCertificate.extend marginCertificate113
    (by decide : checkBlock 11308 100 1637 = some 1655) (by norm_num)

lemma marginCertificate115 : MarginCertificate 11508 1666 := by
  exact MarginCertificate.extend marginCertificate114
    (by decide : checkBlock 11408 100 1655 = some 1666) (by norm_num)

lemma marginCertificate116 : MarginCertificate 11608 1688 := by
  exact MarginCertificate.extend marginCertificate115
    (by decide : checkBlock 11508 100 1666 = some 1688) (by norm_num)

lemma marginCertificate117 : MarginCertificate 11708 1709 := by
  exact MarginCertificate.extend marginCertificate116
    (by decide : checkBlock 11608 100 1688 = some 1709) (by norm_num)

lemma marginCertificate118 : MarginCertificate 11808 1723 := by
  exact MarginCertificate.extend marginCertificate117
    (by decide : checkBlock 11708 100 1709 = some 1723) (by norm_num)

lemma marginCertificate119 : MarginCertificate 11908 1741 := by
  exact MarginCertificate.extend marginCertificate118
    (by decide : checkBlock 11808 100 1723 = some 1741) (by norm_num)

lemma marginCertificate120 : MarginCertificate 12008 1744 := by
  exact MarginCertificate.extend marginCertificate119
    (by decide : checkBlock 11908 100 1741 = some 1744) (by norm_num)

lemma marginCertificate121 : MarginCertificate 12108 1757 := by
  exact MarginCertificate.extend marginCertificate120
    (by decide : checkBlock 12008 100 1744 = some 1757) (by norm_num)

lemma marginCertificate122 : MarginCertificate 12208 1772 := by
  exact MarginCertificate.extend marginCertificate121
    (by decide : checkBlock 12108 100 1757 = some 1772) (by norm_num)

lemma marginCertificate123 : MarginCertificate 12308 1776 := by
  exact MarginCertificate.extend marginCertificate122
    (by decide : checkBlock 12208 100 1772 = some 1776) (by norm_num)

lemma marginCertificate124 : MarginCertificate 12408 1796 := by
  exact MarginCertificate.extend marginCertificate123
    (by decide : checkBlock 12308 100 1776 = some 1796) (by norm_num)

lemma marginCertificate125 : MarginCertificate 12508 1800 := by
  exact MarginCertificate.extend marginCertificate124
    (by decide : checkBlock 12408 100 1796 = some 1800) (by norm_num)

lemma marginCertificate126 : MarginCertificate 12608 1807 := by
  exact MarginCertificate.extend marginCertificate125
    (by decide : checkBlock 12508 100 1800 = some 1807) (by norm_num)

lemma marginCertificate127 : MarginCertificate 12708 1817 := by
  exact MarginCertificate.extend marginCertificate126
    (by decide : checkBlock 12608 100 1807 = some 1817) (by norm_num)

lemma marginCertificate128 : MarginCertificate 12808 1840 := by
  exact MarginCertificate.extend marginCertificate127
    (by decide : checkBlock 12708 100 1817 = some 1840) (by norm_num)

lemma marginCertificate129 : MarginCertificate 12908 1846 := by
  exact MarginCertificate.extend marginCertificate128
    (by decide : checkBlock 12808 100 1840 = some 1846) (by norm_num)

lemma marginCertificate130 : MarginCertificate 13008 1848 := by
  exact MarginCertificate.extend marginCertificate129
    (by decide : checkBlock 12908 100 1846 = some 1848) (by norm_num)

lemma marginCertificate131 : MarginCertificate 13108 1867 := by
  exact MarginCertificate.extend marginCertificate130
    (by decide : checkBlock 13008 100 1848 = some 1867) (by norm_num)

lemma marginCertificate132 : MarginCertificate 13208 1883 := by
  exact MarginCertificate.extend marginCertificate131
    (by decide : checkBlock 13108 100 1867 = some 1883) (by norm_num)

lemma marginCertificate133 : MarginCertificate 13308 1897 := by
  exact MarginCertificate.extend marginCertificate132
    (by decide : checkBlock 13208 100 1883 = some 1897) (by norm_num)

lemma marginCertificate134 : MarginCertificate 13408 1911 := by
  exact MarginCertificate.extend marginCertificate133
    (by decide : checkBlock 13308 100 1897 = some 1911) (by norm_num)

lemma marginCertificate135 : MarginCertificate 13508 1929 := by
  exact MarginCertificate.extend marginCertificate134
    (by decide : checkBlock 13408 100 1911 = some 1929) (by norm_num)

lemma marginCertificate136 : MarginCertificate 13608 1951 := by
  exact MarginCertificate.extend marginCertificate135
    (by decide : checkBlock 13508 100 1929 = some 1951) (by norm_num)

lemma marginCertificate137 : MarginCertificate 13708 1956 := by
  exact MarginCertificate.extend marginCertificate136
    (by decide : checkBlock 13608 100 1951 = some 1956) (by norm_num)

lemma marginCertificate138 : MarginCertificate 13808 1960 := by
  exact MarginCertificate.extend marginCertificate137
    (by decide : checkBlock 13708 100 1956 = some 1960) (by norm_num)

lemma marginCertificate139 : MarginCertificate 13908 1971 := by
  exact MarginCertificate.extend marginCertificate138
    (by decide : checkBlock 13808 100 1960 = some 1971) (by norm_num)

lemma marginCertificate140 : MarginCertificate 14008 1984 := by
  exact MarginCertificate.extend marginCertificate139
    (by decide : checkBlock 13908 100 1971 = some 1984) (by norm_num)

lemma marginCertificate141 : MarginCertificate 14108 2000 := by
  exact MarginCertificate.extend marginCertificate140
    (by decide : checkBlock 14008 100 1984 = some 2000) (by norm_num)

lemma marginCertificate142 : MarginCertificate 14208 2023 := by
  exact MarginCertificate.extend marginCertificate141
    (by decide : checkBlock 14108 100 2000 = some 2023) (by norm_num)

lemma marginCertificate143 : MarginCertificate 14308 2051 := by
  exact MarginCertificate.extend marginCertificate142
    (by decide : checkBlock 14208 100 2023 = some 2051) (by norm_num)

lemma marginCertificate144 : MarginCertificate 14408 2066 := by
  exact MarginCertificate.extend marginCertificate143
    (by decide : checkBlock 14308 100 2051 = some 2066) (by norm_num)

lemma marginCertificate145 : MarginCertificate 14508 2077 := by
  exact MarginCertificate.extend marginCertificate144
    (by decide : checkBlock 14408 100 2066 = some 2077) (by norm_num)

lemma marginCertificate146 : MarginCertificate 14608 2093 := by
  exact MarginCertificate.extend marginCertificate145
    (by decide : checkBlock 14508 100 2077 = some 2093) (by norm_num)

lemma marginCertificate147 : MarginCertificate 14708 2100 := by
  exact MarginCertificate.extend marginCertificate146
    (by decide : checkBlock 14608 100 2093 = some 2100) (by norm_num)

lemma marginCertificate148 : MarginCertificate 14808 2102 := by
  exact MarginCertificate.extend marginCertificate147
    (by decide : checkBlock 14708 100 2100 = some 2102) (by norm_num)

lemma marginCertificate149 : MarginCertificate 14908 2114 := by
  exact MarginCertificate.extend marginCertificate148
    (by decide : checkBlock 14808 100 2102 = some 2114) (by norm_num)

lemma marginCertificate150 : MarginCertificate 15008 2136 := by
  exact MarginCertificate.extend marginCertificate149
    (by decide : checkBlock 14908 100 2114 = some 2136) (by norm_num)

lemma marginCertificate151 : MarginCertificate 15108 2146 := by
  exact MarginCertificate.extend marginCertificate150
    (by decide : checkBlock 15008 100 2136 = some 2146) (by norm_num)

lemma marginCertificate152 : MarginCertificate 15208 2163 := by
  exact MarginCertificate.extend marginCertificate151
    (by decide : checkBlock 15108 100 2146 = some 2163) (by norm_num)

lemma marginCertificate153 : MarginCertificate 15308 2165 := by
  exact MarginCertificate.extend marginCertificate152
    (by decide : checkBlock 15208 100 2163 = some 2165) (by norm_num)

lemma marginCertificate154 : MarginCertificate 15408 2171 := by
  exact MarginCertificate.extend marginCertificate153
    (by decide : checkBlock 15308 100 2165 = some 2171) (by norm_num)

lemma marginCertificate155 : MarginCertificate 15508 2187 := by
  exact MarginCertificate.extend marginCertificate154
    (by decide : checkBlock 15408 100 2171 = some 2187) (by norm_num)

lemma marginCertificate156 : MarginCertificate 15608 2205 := by
  exact MarginCertificate.extend marginCertificate155
    (by decide : checkBlock 15508 100 2187 = some 2205) (by norm_num)

lemma marginCertificate157 : MarginCertificate 15708 2213 := by
  exact MarginCertificate.extend marginCertificate156
    (by decide : checkBlock 15608 100 2205 = some 2213) (by norm_num)

lemma marginCertificate158 : MarginCertificate 15808 2216 := by
  exact MarginCertificate.extend marginCertificate157
    (by decide : checkBlock 15708 100 2213 = some 2216) (by norm_num)

lemma marginCertificate159 : MarginCertificate 15908 2229 := by
  exact MarginCertificate.extend marginCertificate158
    (by decide : checkBlock 15808 100 2216 = some 2229) (by norm_num)

lemma marginCertificate160 : MarginCertificate 16008 2247 := by
  exact MarginCertificate.extend marginCertificate159
    (by decide : checkBlock 15908 100 2229 = some 2247) (by norm_num)

lemma marginCertificate161 : MarginCertificate 16108 2257 := by
  exact MarginCertificate.extend marginCertificate160
    (by decide : checkBlock 16008 100 2247 = some 2257) (by norm_num)

lemma marginCertificate162 : MarginCertificate 16208 2282 := by
  exact MarginCertificate.extend marginCertificate161
    (by decide : checkBlock 16108 100 2257 = some 2282) (by norm_num)

lemma marginCertificate163 : MarginCertificate 16308 2298 := by
  exact MarginCertificate.extend marginCertificate162
    (by decide : checkBlock 16208 100 2282 = some 2298) (by norm_num)

lemma marginCertificate164 : MarginCertificate 16408 2325 := by
  exact MarginCertificate.extend marginCertificate163
    (by decide : checkBlock 16308 100 2298 = some 2325) (by norm_num)

lemma marginCertificate165 : MarginCertificate 16508 2332 := by
  exact MarginCertificate.extend marginCertificate164
    (by decide : checkBlock 16408 100 2325 = some 2332) (by norm_num)

lemma marginCertificate166 : MarginCertificate 16608 2346 := by
  exact MarginCertificate.extend marginCertificate165
    (by decide : checkBlock 16508 100 2332 = some 2346) (by norm_num)

lemma marginCertificate167 : MarginCertificate 16708 2354 := by
  exact MarginCertificate.extend marginCertificate166
    (by decide : checkBlock 16608 100 2346 = some 2354) (by norm_num)

lemma marginCertificate168 : MarginCertificate 16808 2375 := by
  exact MarginCertificate.extend marginCertificate167
    (by decide : checkBlock 16708 100 2354 = some 2375) (by norm_num)

lemma marginCertificate169 : MarginCertificate 16908 2392 := by
  exact MarginCertificate.extend marginCertificate168
    (by decide : checkBlock 16808 100 2375 = some 2392) (by norm_num)

lemma marginCertificate170 : MarginCertificate 17008 2401 := by
  exact MarginCertificate.extend marginCertificate169
    (by decide : checkBlock 16908 100 2392 = some 2401) (by norm_num)

lemma marginCertificate171 : MarginCertificate 17108 2409 := by
  exact MarginCertificate.extend marginCertificate170
    (by decide : checkBlock 17008 100 2401 = some 2409) (by norm_num)

lemma marginCertificate172 : MarginCertificate 17208 2420 := by
  exact MarginCertificate.extend marginCertificate171
    (by decide : checkBlock 17108 100 2409 = some 2420) (by norm_num)

lemma marginCertificate173 : MarginCertificate 17308 2449 := by
  exact MarginCertificate.extend marginCertificate172
    (by decide : checkBlock 17208 100 2420 = some 2449) (by norm_num)

lemma marginCertificate174 : MarginCertificate 17408 2447 := by
  exact MarginCertificate.extend marginCertificate173
    (by decide : checkBlock 17308 100 2449 = some 2447) (by norm_num)

lemma marginCertificate175 : MarginCertificate 17508 2455 := by
  exact MarginCertificate.extend marginCertificate174
    (by decide : checkBlock 17408 100 2447 = some 2455) (by norm_num)

lemma marginCertificate176 : MarginCertificate 17608 2476 := by
  exact MarginCertificate.extend marginCertificate175
    (by decide : checkBlock 17508 100 2455 = some 2476) (by norm_num)

lemma marginCertificate177 : MarginCertificate 17708 2480 := by
  exact MarginCertificate.extend marginCertificate176
    (by decide : checkBlock 17608 100 2476 = some 2480) (by norm_num)

lemma marginCertificate178 : MarginCertificate 17808 2494 := by
  exact MarginCertificate.extend marginCertificate177
    (by decide : checkBlock 17708 100 2480 = some 2494) (by norm_num)

lemma marginCertificate179 : MarginCertificate 17908 2518 := by
  exact MarginCertificate.extend marginCertificate178
    (by decide : checkBlock 17808 100 2494 = some 2518) (by norm_num)

lemma marginCertificate180 : MarginCertificate 18008 2528 := by
  exact MarginCertificate.extend marginCertificate179
    (by decide : checkBlock 17908 100 2518 = some 2528) (by norm_num)

lemma marginCertificate181 : MarginCertificate 18108 2544 := by
  exact MarginCertificate.extend marginCertificate180
    (by decide : checkBlock 18008 100 2528 = some 2544) (by norm_num)

lemma marginCertificate182 : MarginCertificate 18208 2550 := by
  exact MarginCertificate.extend marginCertificate181
    (by decide : checkBlock 18108 100 2544 = some 2550) (by norm_num)

lemma marginCertificate183 : MarginCertificate 18308 2556 := by
  exact MarginCertificate.extend marginCertificate182
    (by decide : checkBlock 18208 100 2550 = some 2556) (by norm_num)

lemma marginCertificate184 : MarginCertificate 18408 2566 := by
  exact MarginCertificate.extend marginCertificate183
    (by decide : checkBlock 18308 100 2556 = some 2566) (by norm_num)

lemma marginCertificate185 : MarginCertificate 18508 2580 := by
  exact MarginCertificate.extend marginCertificate184
    (by decide : checkBlock 18408 100 2566 = some 2580) (by norm_num)

lemma marginCertificate186 : MarginCertificate 18608 2601 := by
  exact MarginCertificate.extend marginCertificate185
    (by decide : checkBlock 18508 100 2580 = some 2601) (by norm_num)

lemma marginCertificate187 : MarginCertificate 18708 2628 := by
  exact MarginCertificate.extend marginCertificate186
    (by decide : checkBlock 18608 100 2601 = some 2628) (by norm_num)

lemma marginCertificate188 : MarginCertificate 18808 2635 := by
  exact MarginCertificate.extend marginCertificate187
    (by decide : checkBlock 18708 100 2628 = some 2635) (by norm_num)

lemma marginCertificate189 : MarginCertificate 18908 2666 := by
  exact MarginCertificate.extend marginCertificate188
    (by decide : checkBlock 18808 100 2635 = some 2666) (by norm_num)

lemma marginCertificate190 : MarginCertificate 19008 2684 := by
  exact MarginCertificate.extend marginCertificate189
    (by decide : checkBlock 18908 100 2666 = some 2684) (by norm_num)

lemma marginCertificate191 : MarginCertificate 19108 2703 := by
  exact MarginCertificate.extend marginCertificate190
    (by decide : checkBlock 19008 100 2684 = some 2703) (by norm_num)

lemma marginCertificate192 : MarginCertificate 19208 2724 := by
  exact MarginCertificate.extend marginCertificate191
    (by decide : checkBlock 19108 100 2703 = some 2724) (by norm_num)

lemma marginCertificate193 : MarginCertificate 19308 2733 := by
  exact MarginCertificate.extend marginCertificate192
    (by decide : checkBlock 19208 100 2724 = some 2733) (by norm_num)

lemma marginCertificate194 : MarginCertificate 19408 2750 := by
  exact MarginCertificate.extend marginCertificate193
    (by decide : checkBlock 19308 100 2733 = some 2750) (by norm_num)

lemma marginCertificate195 : MarginCertificate 19508 2736 := by
  exact MarginCertificate.extend marginCertificate194
    (by decide : checkBlock 19408 100 2750 = some 2736) (by norm_num)

lemma marginCertificate196 : MarginCertificate 19608 2749 := by
  exact MarginCertificate.extend marginCertificate195
    (by decide : checkBlock 19508 100 2736 = some 2749) (by norm_num)

lemma marginCertificate197 : MarginCertificate 19708 2772 := by
  exact MarginCertificate.extend marginCertificate196
    (by decide : checkBlock 19608 100 2749 = some 2772) (by norm_num)

lemma marginCertificate198 : MarginCertificate 19808 2785 := by
  exact MarginCertificate.extend marginCertificate197
    (by decide : checkBlock 19708 100 2772 = some 2785) (by norm_num)

lemma marginCertificate199 : MarginCertificate 19908 2800 := by
  exact MarginCertificate.extend marginCertificate198
    (by decide : checkBlock 19808 100 2785 = some 2800) (by norm_num)

lemma marginCertificate200 : MarginCertificate 20000 2806 := by
  exact MarginCertificate.extend marginCertificate199
    (by decide : checkBlock 19908 92 2800 = some 2806) (by norm_num)

lemma primeMargin_nonneg_eight_to_20000 {y : ℕ} (hy8 : 8 ≤ y)
    (hy20000 : y ≤ 20000) : 0 ≤ primeMargin y :=
  marginCertificate200.nonneg y hy8 hy20000
