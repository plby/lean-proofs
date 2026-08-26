/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.KummerTransition

/-!
# Erdős 730: exact consecutive support-transition criterion

This module formalizes Proposition 1 of the positive-density proof.  For
`n ≥ 1`, equality of the prime supports of the two consecutive central
binomial coefficients is equivalent to the two exact-valuation cofactor
conditions (5) and (6).

The predicate `ExactPrimePowerCofactor p a c N` is the fully quantified
meaning of `p^a ∥ N` together with the named cofactor `c`: `a` is positive,
`N = p^a*c`, and `p ∤ c`.
-/

namespace Erdos730
namespace ConsecutiveTransition

open KummerTransition

/-- `p^a ∥ N`, with the cofactor explicitly named as `c` and with the
positive-exponent convention used in Proposition 1. -/
def ExactPrimePowerCofactor (p a c N : ℕ) : Prop :=
  0 < a ∧ N = p ^ a * c ∧ ¬p ∣ c

/-- The exact quantified condition (5). -/
def DropCondition (n : ℕ) : Prop :=
  ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
    ExactPrimePowerCofactor p a c (n + 1) →
      ¬LowerHalfDigits p c

/-- The exact quantified condition (6). -/
def EntryCondition (n : ℕ) : Prop :=
  ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
    ExactPrimePowerCofactor p a c (2 * n + 1) →
      ¬LowerHalfDigits p ((c - 1) / 2)

/-- The two exact obstruction-exclusion conditions in Proposition 1. -/
def TransitionConditions (n : ℕ) : Prop :=
  DropCondition n ∧ EntryCondition n

/-- Every nonzero number admits an exact positive-exponent `p`-power
decomposition once `p` divides it. -/
theorem exists_exactPrimePowerCofactor_of_dvd
    {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hpd : p ∣ N) :
    ∃ a c, ExactPrimePowerCofactor p a c N := by
  obtain ⟨a, c, hpc, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  refine ⟨a, c, ?_, hfac, hpc⟩
  by_contra ha
  have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
  subst a
  simp only [pow_zero, one_mul] at hfac
  exact hpc (hfac ▸ hpd)

/-- The two adjacent linear factors are coprime. -/
theorem coprime_succ_two_mul_add_one (n : ℕ) :
    Nat.Coprime (n + 1) (2 * n + 1) := by
  rw [two_mul, add_assoc, Nat.coprime_add_self_right,
    Nat.coprime_self_add_left]
  exact Nat.coprime_one_left n

/-- Hence a prime dividing `n+1` cannot divide `2n+1`. -/
theorem not_dvd_two_mul_add_one_of_dvd_succ
    {p n : ℕ} (hp : p.Prime) (hpd : p ∣ n + 1) :
    ¬p ∣ 2 * n + 1 := by
  intro hpd'
  apply hp.not_dvd_one
  rw [← coprime_succ_two_mul_add_one n]
  exact Nat.dvd_gcd hpd hpd'

/-- Symmetric coprimality consequence. -/
theorem not_dvd_succ_of_dvd_two_mul_add_one
    {p n : ℕ} (hp : p.Prime) (hpd : p ∣ 2 * n + 1) :
    ¬p ∣ n + 1 := by
  intro hpd'
  apply hp.not_dvd_one
  rw [← coprime_succ_two_mul_add_one n]
  exact Nat.dvd_gcd hpd' hpd

/-- Away from the two factors in the central-binomial recurrence, an odd
prime has the same divisibility status at `n` and `n+1`. -/
theorem dvd_centralBinom_succ_iff_of_away
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsucc : ¬p ∣ n + 1) (htwo : ¬p ∣ 2 * n + 1) :
    p ∣ (n + 1).centralBinom ↔ p ∣ n.centralBinom := by
  constructor
  · intro h
    have hprod : p ∣ 2 * (2 * n + 1) * n.centralBinom := by
      rw [← Nat.succ_mul_centralBinom_succ]
      exact dvd_mul_of_dvd_right h (n + 1)
    rcases hp.dvd_mul.mp hprod with hleft | hbinom
    · rcases hp.dvd_mul.mp hleft with htwo' | hlinear
      · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp htwo')).elim
      · exact (htwo hlinear).elim
    · exact hbinom
  · intro h
    have hprod : p ∣ (n + 1) * (n + 1).centralBinom := by
      rw [Nat.succ_mul_centralBinom_succ]
      exact dvd_mul_of_dvd_right h (2 * (2 * n + 1))
    rcases hp.dvd_mul.mp hprod with hlinear | hbinom
    · exact (hsucc hlinear).elim
    · exact hbinom

/-- Odd-factor arithmetic behind equation (7). -/
theorem lower_endpoint_decomposition
    {n q c : ℕ} (hq : Odd q) (hc : Odd c)
    (h : 2 * n + 1 = q * c) :
    n = q * ((c - 1) / 2) + (q - 1) / 2 := by
  rcases hq with ⟨r, rfl⟩
  rcases hc with ⟨s, rfl⟩
  simp at h ⊢
  nlinarith [h]

/-- The adjacent upper endpoint corresponding to equation (7). -/
theorem upper_endpoint_decomposition
    {n q c : ℕ} (hq : Odd q) (hc : Odd c)
    (h : 2 * n + 1 = q * c) :
    n + 1 = q * ((c - 1) / 2) + (q + 1) / 2 := by
  rcases hq with ⟨r, rfl⟩
  rcases hc with ⟨s, rfl⟩
  simp at h ⊢
  have hhalf : (2 * r + 1 + 1) / 2 = r + 1 := by omega
  rw [hhalf]
  nlinarith [h]

/-- In the `p^a ∥ n+1` case, the prime is always present at the lower
endpoint and is absent at the upper endpoint exactly for a `D_p` cofactor. -/
theorem drop_transition_of_exact
    {p a c n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexact : ExactPrimePowerCofactor p a c (n + 1)) :
    p ∣ n.centralBinom ∧
      (¬p ∣ (n + 1).centralBinom ↔ LowerHalfDigits p c) := by
  rcases hexact with ⟨ha, hfac, hpc⟩
  constructor
  · have hpPow : p ∣ p ^ a := dvd_pow_self p ha.ne'
    have hpsucc : p ∣ n + 1 := by
      rw [hfac]
      exact dvd_mul_of_dvd_left hpPow c
    exact dvd_trans hpsucc (Nat.succ_dvd_centralBinom n)
  · simpa [hfac] using
      (not_dvd_centralBinom_primePow_mul_iff hp hp2
        (Nat.pos_of_ne_zero (fun hc0 ↦ hpc (hc0 ▸ dvd_zero p))) :
        ¬p ∣ (p ^ a * c).centralBinom ↔ LowerHalfDigits p c)

/-- In the `p^a ∥ 2n+1` case, the prime is always present at the upper
endpoint and is absent at the lower endpoint exactly for the cofactor test
in (6). -/
theorem entry_transition_of_exact
    {p a c n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexact : ExactPrimePowerCofactor p a c (2 * n + 1)) :
    (¬p ∣ n.centralBinom ↔ LowerHalfDigits p ((c - 1) / 2)) ∧
      p ∣ (n + 1).centralBinom := by
  rcases hexact with ⟨ha, hfac, hpc⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpowodd : Odd (p ^ a) := hpodd.pow
  have htotalOdd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hcodd : Odd c := by
    rw [hfac] at htotalOdd
    exact (Nat.odd_mul.mp htotalOdd).2
  have hnform :
      n = p ^ a * ((c - 1) / 2) + (p ^ a - 1) / 2 :=
    lower_endpoint_decomposition hpowodd hcodd hfac
  have hsuccform :
      n + 1 = p ^ a * ((c - 1) / 2) + (p ^ a + 1) / 2 :=
    upper_endpoint_decomposition hpowodd hcodd hfac
  constructor
  · simpa [hnform] using
      (not_dvd_centralBinom_lowerHalfBlock_iff hp hp2 a ((c - 1) / 2))
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    simpa [hsuccform, Nat.succ_eq_add_one] using
      (dvd_centralBinom_upperHalfBlock hp hp2 b ((c - 1) / 2))

/-! ## Proposition 1 -/

/-- Prime-by-prime divisibility agrees at the two endpoints exactly when
the two quantified transition conditions hold. -/
theorem prime_dvd_agrees_iff_transitionConditions
    {n : ℕ} (hn : 0 < n) :
    (∀ p, p.Prime →
        (p ∣ n.centralBinom ↔ p ∣ (n + 1).centralBinom)) ↔
      TransitionConditions n := by
  constructor
  · intro hagree
    constructor
    · intro p hp hp2 a c hexact hlow
      have htransition := drop_transition_of_exact hp hp2 hexact
      have hupper : p ∣ (n + 1).centralBinom :=
        (hagree p hp).mp htransition.1
      exact (htransition.2.mpr hlow) hupper
    · intro p hp hp2 a c hexact hlow
      have htransition := entry_transition_of_exact hp hp2 hexact
      have hlower : p ∣ n.centralBinom :=
        (hagree p hp).mpr htransition.2
      exact (htransition.1.mpr hlow) hlower
  · rintro ⟨hdrop, hentry⟩ p hp
    by_cases hp2 : p = 2
    · subst p
      constructor
      · intro _
        exact Nat.two_dvd_centralBinom_of_one_le (by omega)
      · intro _
        exact Nat.two_dvd_centralBinom_of_one_le hn
    · by_cases hsucc : p ∣ n + 1
      · obtain ⟨a, c, hexact⟩ :=
          exists_exactPrimePowerCofactor_of_dvd hp (by omega) hsucc
        have htransition := drop_transition_of_exact hp hp2 hexact
        have hnotlow : ¬LowerHalfDigits p c := hdrop hp hp2 hexact
        have hupper : p ∣ (n + 1).centralBinom := by
          by_contra hnot
          exact hnotlow (htransition.2.mp hnot)
        exact ⟨fun _ ↦ hupper, fun _ ↦ htransition.1⟩
      · by_cases htwo : p ∣ 2 * n + 1
        · obtain ⟨a, c, hexact⟩ :=
            exists_exactPrimePowerCofactor_of_dvd hp (by omega) htwo
          have htransition := entry_transition_of_exact hp hp2 hexact
          have hnotlow : ¬LowerHalfDigits p ((c - 1) / 2) :=
            hentry hp hp2 hexact
          have hlower : p ∣ n.centralBinom := by
            by_contra hnot
            exact hnotlow (htransition.1.mp hnot)
          exact ⟨fun _ ↦ htransition.2, fun _ ↦ hlower⟩
        · exact (dvd_centralBinom_succ_iff_of_away hp hp2 hsucc htwo).symm

/-- Equality of central-binomial prime-factor sets is the same as
prime-by-prime agreement of divisibility. -/
theorem primeFactors_eq_iff_prime_dvd_agrees (n : ℕ) :
    n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors ↔
      ∀ p, p.Prime →
        (p ∣ n.centralBinom ↔ p ∣ (n + 1).centralBinom) := by
  have hn0 : n.centralBinom ≠ 0 := Nat.centralBinom_ne_zero n
  have hsucc0 : (n + 1).centralBinom ≠ 0 := Nat.centralBinom_ne_zero (n + 1)
  constructor
  · intro heq p hp
    have hmem :
        p ∈ n.centralBinom.primeFactors ↔
          p ∈ (n + 1).centralBinom.primeFactors := by
      rw [heq]
    simpa [Nat.mem_primeFactors_of_ne_zero hn0,
      Nat.mem_primeFactors_of_ne_zero hsucc0, hp] using hmem
  · intro hagree
    ext p
    simp only [Nat.mem_primeFactors_of_ne_zero hn0,
      Nat.mem_primeFactors_of_ne_zero hsucc0]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (hagree p hp).mp hdvd⟩
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (hagree p hp).mpr hdvd⟩

/-- **Proposition 1 (equations (5) and (6)).**  For every `n ≥ 1`, the
supports of `B(n)` and `B(n+1)` agree if and only if every exact odd-prime
valuation of `n+1` and `2n+1` passes its respective cofactor test. -/
theorem consecutive_primeFactors_eq_iff_transitionConditions
    {n : ℕ} (hn : 0 < n) :
    n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors ↔
      TransitionConditions n := by
  rw [primeFactors_eq_iff_prime_dvd_agrees]
  exact prime_dvd_agrees_iff_transitionConditions hn

/-! ## Event coverage -/

/-- A witnessed equation-(5) obstruction event. -/
def DropObstruction (n p a c : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a c (n + 1) ∧
      LowerHalfDigits p c

/-- A witnessed equation-(6) obstruction event. -/
def EntryObstruction (n p a c : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a c (2 * n + 1) ∧
      LowerHalfDigits p ((c - 1) / 2)

/-- Exact event-coverage theorem underlying `Bad(X) ≤ E(X)`: if the two
supports differ, some fully quantified drop or entry obstruction occurs.
No injectivity of the witness assignment is asserted or needed. -/
theorem exists_obstruction_of_primeFactors_ne
    {n : ℕ} (hn : 0 < n)
    (hbad : n.centralBinom.primeFactors ≠
      (n + 1).centralBinom.primeFactors) :
    (∃ p a c, DropObstruction n p a c) ∨
      (∃ p a c, EntryObstruction n p a c) := by
  classical
  have hnot : ¬TransitionConditions n := by
    intro hconditions
    exact hbad
      ((consecutive_primeFactors_eq_iff_transitionConditions hn).mpr hconditions)
  by_cases hdrop : DropCondition n
  · have hnotentry : ¬EntryCondition n := by
      intro hentry
      exact hnot ⟨hdrop, hentry⟩
    unfold EntryCondition at hnotentry
    push Not at hnotentry
    right
    rcases hnotentry with ⟨p, hp, hp2, a, c, hexact, hlow⟩
    exact ⟨p, a, c, hp, hp2, hexact, hlow⟩
  · unfold DropCondition at hdrop
    push Not at hdrop
    left
    rcases hdrop with ⟨p, hp, hp2, a, c, hexact, hlow⟩
    exact ⟨p, a, c, hp, hp2, hexact, hlow⟩

#print axioms exists_exactPrimePowerCofactor_of_dvd
#print axioms dvd_centralBinom_succ_iff_of_away
#print axioms drop_transition_of_exact
#print axioms entry_transition_of_exact
#print axioms consecutive_primeFactors_eq_iff_transitionConditions
#print axioms exists_obstruction_of_primeFactors_ne

end ConsecutiveTransition
end Erdos730
