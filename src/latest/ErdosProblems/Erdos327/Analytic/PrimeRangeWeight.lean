import ErdosProblems.Erdos327.Analytic.PrimeWeight

namespace Erdos327.Analytic

open Finset

/-- Prime factors of `n` in the closed interval `[L, X]`, counted with
multiplicity. -/
def primeFactorCountBetween (L X n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p ↦ L ≤ p ∧ p ≤ X).length

private theorem filter_length_mono_pred
    {α : Type*} (l : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a ∈ l, P a → Q a) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have ih' : (l.filter P).length ≤ (l.filter Q).length :=
        ih (fun a ha ↦ hPQ a (by simp [ha]))
      by_cases hp : P p
      · have hq : Q p := hPQ p (by simp) hp
        simp [hp, hq, ih']
      · by_cases hq : Q p
        · have hsucc := Nat.le_succ_of_le ih'
          simpa [hp, hq, Nat.succ_eq_add_one] using hsucc
        · simp [hp, hq, ih']

private theorem filter_primeRange_length_mono
    (l : List ℕ) (L X X' : ℕ) (hXX' : X ≤ X') :
    (l.filter fun p ↦ L ≤ p ∧ p ≤ X).length ≤
      (l.filter fun p ↦ L ≤ p ∧ p ≤ X').length := by
  apply filter_length_mono_pred
  intro p hp hpRange
  exact ⟨hpRange.1, hpRange.2.trans hXX'⟩

/-- Enlarging the upper cutoff can only add prime factors to the localized
count. -/
theorem primeFactorCountBetween_mono_right
    (L n : ℕ) {X X' : ℕ} (hXX' : X ≤ X') :
    primeFactorCountBetween L X n ≤
      primeFactorCountBetween L X' n := by
  unfold primeFactorCountBetween
  exact filter_primeRange_length_mono n.primeFactorsList L X X' hXX'

/-- The cutoff prime-factor count is completely additive away from zero. -/
theorem primeFactorCountBetween_mul
    {L X a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeFactorCountBetween L X (a * b) =
      primeFactorCountBetween L X a +
        primeFactorCountBetween L X b := by
  unfold primeFactorCountBetween
  have hperm :=
    (Nat.perm_primeFactorsList_mul ha hb).filter
      (fun p ↦ L ≤ p ∧ p ≤ X)
  simpa using hperm.length_eq

/-- Multiplication by two does not change a cutoff count whose lower
endpoint is at least three. -/
theorem primeFactorCountBetween_two_mul
    {L X n : ℕ} (hL : 3 ≤ L) (hn : n ≠ 0) :
    primeFactorCountBetween L X (2 * n) =
      primeFactorCountBetween L X n := by
  rw [primeFactorCountBetween_mul (by norm_num) hn]
  have htwo : primeFactorCountBetween L X 2 = 0 := by
    unfold primeFactorCountBetween
    simp
    omega
  rw [htwo, zero_add]

/-- Local prime weight which equals `q` on `[L, X]` and one elsewhere. -/
def intervalPrimeWeight (L X : ℕ) (q : ℝ) (p : ℕ) : ℝ :=
  if L ≤ p ∧ p ≤ X then q else 1

private theorem list_prod_intervalPrimeWeight
    (L X : ℕ) (q : ℝ) (l : List ℕ) :
    (l.map (intervalPrimeWeight L X q)).prod =
      q ^ (l.filter fun p ↦ L ≤ p ∧ p ≤ X).length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hp : L ≤ p ∧ p ≤ X
      · simp [intervalPrimeWeight, hp, ih, pow_succ']
      · simp [intervalPrimeWeight, hp, ih]

/-- The prime-factor weight is exactly the exponential moment of the
cutoff prime-factor count. -/
theorem factorWeight_intervalPrimeWeight
    {L X n : ℕ} {q : ℝ} (hn : n ≠ 0) :
    factorWeight (intervalPrimeWeight L X q) n =
      q ^ primeFactorCountBetween L X n := by
  rw [factorWeight_apply hn]
  exact list_prod_intervalPrimeWeight L X q n.primeFactorsList

/-- The residual local weight used after extracting odd primes below `L`:
such primes receive weight zero, primes in `[L,X]` receive `q`, and all
remaining primes receive weight one. -/
def residualPrimeWeight (L X : ℕ) (q : ℝ) (p : ℕ) : ℝ :=
  if 2 < p ∧ p < L then 0
  else if L ≤ p ∧ p ≤ X then q
  else 1

theorem residualPrimeWeight_nonneg
    {L X : ℕ} {q : ℝ} (hq : 0 ≤ q) (p : ℕ) :
    0 ≤ residualPrimeWeight L X q p := by
  simp only [residualPrimeWeight]
  split_ifs <;> positivity

theorem residualPrimeWeight_le
    {L X : ℕ} {q C : ℝ} (hq : q ≤ C) (hC : 1 ≤ C) (p : ℕ) :
    residualPrimeWeight L X q p ≤ C := by
  simp only [residualPrimeWeight]
  split_ifs <;> linarith

@[simp] theorem residualPrimeWeight_two
    {L X : ℕ} {q : ℝ} (hL : 2 < L) :
    residualPrimeWeight L X q 2 = 1 := by
  simp [residualPrimeWeight, Nat.not_le.mpr hL]

theorem residualPrimeWeight_eq_zero_of_oddPrimeBelow
    {L X p : ℕ} {q : ℝ} (hp2 : 2 < p) (hpL : p < L) :
    residualPrimeWeight L X q p = 0 := by
  simp [residualPrimeWeight, hp2, hpL]

theorem residualPrimeWeight_eq_q_of_mem
    {L X p : ℕ} {q : ℝ} (hL : L ≤ p) (hpX : p ≤ X) :
    residualPrimeWeight L X q p = q := by
  simp [residualPrimeWeight, hL, hpX]

theorem residualPrimeWeight_eq_one_of_above
    {L X p : ℕ} {q : ℝ} (hLp : L ≤ p) (hXp : X < p) :
    residualPrimeWeight L X q p = 1 := by
  simp [residualPrimeWeight, Nat.not_lt_of_ge hLp, Nat.not_le.mpr hXp]

/-- Predicate saying that no odd prime below `L` divides `n`. -/
def OddRough (L n : ℕ) : Prop :=
  ∀ p, p.Prime → 2 < p → p < L → ¬p ∣ n

noncomputable instance oddRoughDecidable (L n : ℕ) :
    Decidable (OddRough L n) :=
  Classical.propDecidable _

private theorem list_prod_residualPrimeWeight
    {L X : ℕ} {q : ℝ} (l : List ℕ)
    (hlPrime : ∀ p ∈ l, p.Prime) :
    (l.map (residualPrimeWeight L X q)).prod =
      if ∃ p ∈ l, 2 < p ∧ p < L then 0
      else q ^ (l.filter fun p ↦ L ≤ p ∧ p ≤ X).length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hpPrime : p.Prime := hlPrime p (by simp)
      have hlPrime' : ∀ r ∈ l, r.Prime := by
        intro r hr
        exact hlPrime r (by simp [hr])
      simp only [List.map_cons, List.prod_cons]
      rw [ih hlPrime']
      by_cases hpSmall : 2 < p ∧ p < L
      · simp [residualPrimeWeight, hpSmall]
      · by_cases hlSmall : ∃ r ∈ l, 2 < r ∧ r < L
        · simp [hlSmall]
        · by_cases hpRange : L ≤ p ∧ p ≤ X
          · simp [residualPrimeWeight, hpSmall, hpRange, hlSmall, pow_succ']
          · simp [residualPrimeWeight, hpSmall, hpRange, hlSmall]

/-- Exact residual-weight formula: the support condition is an indicator,
and on its support the weight is `q` to the cutoff factor count. -/
theorem factorWeight_residualPrimeWeight
    {L X n : ℕ} {q : ℝ} (hn : n ≠ 0) :
    factorWeight (residualPrimeWeight L X q) n =
      if OddRough L n then q ^ primeFactorCountBetween L X n else 0 := by
  rw [factorWeight_apply hn]
  have hprime :
      ∀ p ∈ n.primeFactorsList, p.Prime :=
    fun p hp ↦ Nat.prime_of_mem_primeFactorsList hp
  rw [list_prod_residualPrimeWeight n.primeFactorsList hprime]
  by_cases hrough : OddRough L n
  · rw [if_pos hrough]
    rw [if_neg]
    · simp [primeFactorCountBetween]
    · rintro ⟨p, hpList, hp2, hpL⟩
      exact hrough p
        (Nat.prime_of_mem_primeFactorsList hpList) hp2 hpL
        (Nat.dvd_of_mem_primeFactorsList hpList)
  · rw [if_neg hrough]
    simp only [OddRough] at hrough
    push Not at hrough
    rcases hrough with ⟨p, hpPrime, hp2, hpL, hpdvd⟩
    have hex :
        ∃ p ∈ n.primeFactorsList, 2 < p ∧ p < L :=
      ⟨p, (Nat.mem_primeFactorsList hn).mpr ⟨hpPrime, hpdvd⟩, hp2, hpL⟩
    rw [if_pos hex]

end Erdos327.Analytic
