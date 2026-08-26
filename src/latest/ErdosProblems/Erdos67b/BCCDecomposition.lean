import ErdosProblems.Erdos67b.WeightedTransfer
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.Divisors

/-!
# The good-residue divisor decomposition

This file proves the exact arithmetic identity that converts a unit-circle-valued
completely multiplicative function agreeing with a Dirichlet character away from
the conductor into the scaled-character family used by the BCC argument.
-/

open scoped BigOperators ZMod
open Finset

namespace Erdos67b

noncomputable section

/-- On a good short translate, removing the gcd with `q ^ (k - 1)` removes
every prime factor of `q`. -/
theorem GoodResidue.coprime_div_gcd_pow_pred {q k H a m : ℕ} [NeZero q]
    (ha : GoodResidue q k H a) (hm : m ∈ Finset.Icc 1 (2 * H)) :
    ((a + m) / Nat.gcd (a + m) (q ^ (k - 1))).Coprime q := by
  apply Nat.coprime_of_dvd
  intro p hp hpdiv hpq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hn0 : a + m ≠ 0 := by
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    omega
  have hQ0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ hq0
  have hgdiv : Nat.gcd (a + m) (q ^ (k - 1)) ∣ a + m := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd (a + m) (q ^ (k - 1)) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0)
  have hquot0 : (a + m) / Nat.gcd (a + m) (q ^ (k - 1)) ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hn0)) hgpos
  have hpquotpos :
      0 < ((a + m) / Nat.gcd (a + m) (q ^ (k - 1))).factorization p :=
    hp.factorization_pos_of_dvd hquot0 hpdiv
  rw [Nat.factorization_div hgdiv, Nat.factorization_gcd hn0 hQ0,
    Nat.factorization_pow] at hpquotpos
  change 0 < (a + m).factorization p -
    min ((a + m).factorization p) ((k - 1) * q.factorization p) at hpquotpos
  have hpqfac : 1 ≤ q.factorization p :=
    (hp.dvd_iff_one_le_factorization hq0).mp hpq
  have hpred_le : k - 1 ≤ (k - 1) * q.factorization p :=
    Nat.le_mul_of_pos_right _ hpqfac
  have hkfac : k ≤ (a + m).factorization p := by omega
  have hpk : p ^ k ∣ a + m :=
    (hp.pow_dvd_iff_le_factorization hn0).mpr hkfac
  exact (ha p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩) m hm) hpk

/-- A divisor of a power of `q` which removes all `q`-factors from `n` is
necessarily the gcd of `n` with that power. -/
theorem eq_gcd_of_dvd_pow_of_dvd_of_div_coprime {q r n d : ℕ} [NeZero q]
    (_hn : n ≠ 0) (hdQ : d ∣ q ^ r) (hdn : d ∣ n)
    (hcop : (n / d).Coprime q) :
    d = Nat.gcd n (q ^ r) := by
  have hqpow0 : q ^ r ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hdg : d ∣ Nat.gcd n (q ^ r) := Nat.dvd_gcd hdn hdQ
  let t := Nat.gcd n (q ^ r) / d
  have ht_n : t ∣ n / d := by
    apply (Nat.dvd_div_iff_mul_dvd hdn).mpr
    simpa only [t, Nat.mul_div_cancel' hdg] using Nat.gcd_dvd_left n (q ^ r)
  have ht_qpow : t ∣ q ^ r := by
    exact (Nat.div_dvd_of_dvd hdg).trans (Nat.gcd_dvd_right n (q ^ r))
  have ht_one : t = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop.pow_right r) ht_n ht_qpow
  apply Nat.dvd_antisymm hdg
  have hmul : d * t = Nat.gcd n (q ^ r) := by
    simp only [t, Nat.mul_div_cancel' hdg]
  simpa only [ht_one, mul_one] using hmul.symm.dvd

/-- A prime assignment agrees with a Dirichlet character away from the
character's level.  Values at primes dividing `q` are intentionally free. -/
def AgreesWithCharacterAway (z : PrimeAssignment)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ p : PrimeNat, ¬(p : ℕ) ∣ q →
    (z p : ℂ) = χ (((p : ℕ) : ZMod q))

/-- Primewise agreement away from `q` extends to every integer coprime to
`q`. -/
theorem primeExtension_eq_dirichletCharacter_of_coprime
    (z : PrimeAssignment) {q n : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hn : n ≠ 0) (hcop : n.Coprime q) :
    (primeExtension z n : ℂ) = χ ((n : ℕ) : ZMod q) := by
  induction n using induction_on_primes with
  | zero => exact (hn rfl).elim
  | one => simp [primeExtension_one]
  | prime_mul p a hp ih =>
      have hpq : p.Coprime q :=
        hcop.coprime_dvd_left (dvd_mul_right p a)
      have haq : a.Coprime q :=
        hcop.coprime_dvd_left (dvd_mul_left a p)
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        simp at hn
      have hpExt : (primeExtension z p : ℂ) = χ (p : ZMod q) := by
        rw [show primeExtension z p = z ⟨p, hp⟩ from
          primeExtension_prime z ⟨p, hp⟩]
        exact hagree ⟨p, hp⟩ ((hp.coprime_iff_not_dvd).mp hpq)
      calc
        (primeExtension z (p * a) : ℂ) =
            (primeExtension z p : ℂ) * (primeExtension z a : ℂ) :=
          congrArg (fun w : Circle ↦ (w : ℂ))
            (primeExtension_mul z hp.ne_zero ha0)
        _ = χ (p : ZMod q) * χ (a : ZMod q) := by rw [hpExt, ih ha0 haq]
        _ = χ ((p * a : ℕ) : ZMod q) := by simp

/-- The natural-number version of a scaled character: it is supported on
multiples of `d`, and on that support evaluates the quotient modulo `q`. -/
def naturalScaledCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (d n : ℕ) : ℂ :=
  if _hd : d ∣ n then χ (((n / d : ℕ) : ZMod q)) else 0

@[simp]
theorem naturalScaledCharacter_of_dvd {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {d n : ℕ} (hd : d ∣ n) :
    naturalScaledCharacter χ d n = χ (((n / d : ℕ) : ZMod q)) := by
  simp [naturalScaledCharacter, hd]

@[simp]
theorem naturalScaledCharacter_of_not_dvd {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {d n : ℕ} (hd : ¬d ∣ n) :
    naturalScaledCharacter χ d n = 0 := by
  simp [naturalScaledCharacter, hd]

/-- Exact good-residue gcd decomposition.  Of all divisors of
`q ^ (k - 1)`, precisely `gcd (a + m) (q ^ (k - 1))` has a quotient which is
a unit modulo `q`; all other scaled-character terms vanish. -/
theorem GoodResidue.primeExtension_eq_sum_scaledCharacter
    (z : PrimeAssignment) {q k H a m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (ha : GoodResidue q k H a) (hm : m ∈ Finset.Icc 1 (2 * H)) :
    (primeExtension z (a + m) : ℂ) =
      ∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * naturalScaledCharacter χ d (a + m) := by
  let n := a + m
  let Q := q ^ (k - 1)
  let g := Nat.gcd n Q
  have hq0 : q ≠ 0 := NeZero.ne q
  have hQ0 : Q ≠ 0 := by
    exact pow_ne_zero _ hq0
  have hn0 : n ≠ 0 := by
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    dsimp only [n]
    omega
  have hgQ : g ∣ Q := Nat.gcd_dvd_right n Q
  have hgn : g ∣ n := Nat.gcd_dvd_left n Q
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hn0
  have hquot0 : n / g ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.gcd_le_left Q (Nat.pos_of_ne_zero hn0))
      (Nat.gcd_pos_of_pos_left Q (Nat.pos_of_ne_zero hn0))
  have hcop : (n / g).Coprime q := by
    simpa only [n, Q, g] using ha.coprime_div_gcd_pow_pred hm
  have hmain :
      (primeExtension z n : ℂ) =
        (primeExtension z g : ℂ) * naturalScaledCharacter χ g n := by
    rw [naturalScaledCharacter_of_dvd χ hgn]
    have hmul : primeExtension z n =
        primeExtension z g * primeExtension z (n / g) := by
      rw [← primeExtension_mul z hg0 hquot0, Nat.mul_div_cancel' hgn]
    calc
      (primeExtension z n : ℂ) =
          (primeExtension z g : ℂ) * (primeExtension z (n / g) : ℂ) :=
        congrArg (fun w : Circle ↦ (w : ℂ)) hmul
      _ = (primeExtension z g : ℂ) * χ (((n / g : ℕ) : ZMod q)) := by
        rw [primeExtension_eq_dirichletCharacter_of_coprime z χ hagree hquot0 hcop]
  rw [hmain]
  symm
  change (∑ d ∈ Q.divisors,
      (primeExtension z d : ℂ) * naturalScaledCharacter χ d n) =
    (primeExtension z g : ℂ) * naturalScaledCharacter χ g n
  apply Finset.sum_eq_single g
  · intro d hddiv hdne
    by_cases hdn : d ∣ n
    · rw [naturalScaledCharacter_of_dvd χ hdn]
      have hnotcop : ¬(n / d).Coprime q := by
        intro hdcop
        have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hddiv
        have hdg : d = g := by
          simpa only [g] using
            (eq_gcd_of_dvd_pow_of_dvd_of_div_coprime hn0 hdQ hdn hdcop)
        exact hdne hdg
      have hnonunit : ¬IsUnit (((n / d : ℕ) : ZMod q)) :=
        (not_congr (ZMod.isUnit_iff_coprime (n / d) q)).mpr hnotcop
      rw [χ.map_nonunit hnonunit, mul_zero]
    · rw [naturalScaledCharacter_of_not_dvd χ hdn, mul_zero]
  · intro hgnot
    exact (hgnot (Nat.mem_divisors.mpr ⟨hgQ, hQ0⟩)).elim

/-- No conductor prime occurs to exponent `k` in `n`. -/
def AvoidsConductorPrimePowers (q k n : ℕ) : Prop :=
  ∀ p ∈ q.primeFactors, ¬p ^ k ∣ n

theorem coprime_div_gcd_pow_pred_of_avoids {q k n : ℕ} [NeZero q]
    (hn : n ≠ 0) (ha : AvoidsConductorPrimePowers q k n) :
    (n / Nat.gcd n (q ^ (k - 1))).Coprime q := by
  apply Nat.coprime_of_dvd
  intro p hp hpdiv hpq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hQ0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ hq0
  have hgdiv : Nat.gcd n (q ^ (k - 1)) ∣ n := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd n (q ^ (k - 1)) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  have hquot0 : n / Nat.gcd n (q ^ (k - 1)) ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hn)) hgpos
  have hpquotpos :
      0 < (n / Nat.gcd n (q ^ (k - 1))).factorization p :=
    hp.factorization_pos_of_dvd hquot0 hpdiv
  rw [Nat.factorization_div hgdiv, Nat.factorization_gcd hn hQ0,
    Nat.factorization_pow] at hpquotpos
  change 0 < n.factorization p -
    min (n.factorization p) ((k - 1) * q.factorization p) at hpquotpos
  have hpqfac : 1 ≤ q.factorization p :=
    (hp.dvd_iff_one_le_factorization hq0).mp hpq
  have hpred_le : k - 1 ≤ (k - 1) * q.factorization p :=
    Nat.le_mul_of_pos_right _ hpqfac
  have hkfac : k ≤ n.factorization p := by omega
  have hpk : p ^ k ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr hkfac
  exact (ha p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩)) hpk

/-- Pointwise divisor decomposition from the prime-power avoidance condition. -/
theorem primeExtension_eq_sum_scaledCharacter_of_avoids
    (z : PrimeAssignment) {q k n : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hn : n ≠ 0) (ha : AvoidsConductorPrimePowers q k n) :
    (primeExtension z n : ℂ) =
      ∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * naturalScaledCharacter χ d n := by
  let Q := q ^ (k - 1)
  let g := Nat.gcd n Q
  have hQ0 : Q ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hgQ : g ∣ Q := Nat.gcd_dvd_right n Q
  have hgn : g ∣ n := Nat.gcd_dvd_left n Q
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hn
  have hquot0 : n / g ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.gcd_le_left Q (Nat.pos_of_ne_zero hn))
      (Nat.gcd_pos_of_pos_left Q (Nat.pos_of_ne_zero hn))
  have hcop : (n / g).Coprime q := by
    simpa only [Q, g] using coprime_div_gcd_pow_pred_of_avoids hn ha
  have hmain :
      (primeExtension z n : ℂ) =
        (primeExtension z g : ℂ) * naturalScaledCharacter χ g n := by
    rw [naturalScaledCharacter_of_dvd χ hgn]
    have hmul : primeExtension z n =
        primeExtension z g * primeExtension z (n / g) := by
      rw [← primeExtension_mul z hg0 hquot0, Nat.mul_div_cancel' hgn]
    calc
      (primeExtension z n : ℂ) =
          (primeExtension z g : ℂ) * (primeExtension z (n / g) : ℂ) :=
        congrArg (fun w : Circle ↦ (w : ℂ)) hmul
      _ = (primeExtension z g : ℂ) * χ (((n / g : ℕ) : ZMod q)) := by
        rw [primeExtension_eq_dirichletCharacter_of_coprime z χ hagree hquot0 hcop]
  rw [hmain]
  symm
  change (∑ d ∈ Q.divisors,
      (primeExtension z d : ℂ) * naturalScaledCharacter χ d n) =
    (primeExtension z g : ℂ) * naturalScaledCharacter χ g n
  apply Finset.sum_eq_single g
  · intro d hddiv hdne
    by_cases hdn : d ∣ n
    · rw [naturalScaledCharacter_of_dvd χ hdn]
      have hnotcop : ¬(n / d).Coprime q := by
        intro hdcop
        have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hddiv
        have hdg : d = g := by
          simpa only [g, Q] using
            (eq_gcd_of_dvd_pow_of_dvd_of_div_coprime hn hdQ hdn hdcop)
        exact hdne hdg
      have hnonunit : ¬IsUnit (((n / d : ℕ) : ZMod q)) :=
        (not_congr (ZMod.isUnit_iff_coprime (n / d) q)).mpr hnotcop
      rw [χ.map_nonunit hnonunit, mul_zero]
    · rw [naturalScaledCharacter_of_not_dvd χ hdn, mul_zero]
  · intro hgnot
    exact (hgnot (Nat.mem_divisors.mpr ⟨hgQ, hQ0⟩)).elim

/-- Membership in the cyclic good set gives the pointwise prime-power
avoidance condition for every prescribed positive short shift. -/
theorem avoids_of_mem_cyclicGoodResidues {q k H : ℕ} [NeZero q]
    {a : ZMod (q ^ k)} (ha : a ∈ cyclicGoodResidues q k H)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    AvoidsConductorPrimePowers q k (a + (m : ZMod (q ^ k))).val := by
  intro p hp hdiv
  have hnotbad : a ∉ cyclicBadResidues q k H :=
    (Finset.mem_sdiff.mp ha).2
  apply hnotbad
  simp only [cyclicBadResidues, Finset.mem_biUnion]
  refine ⟨p, hp, m, hm, ?_⟩
  simp only [cyclicBadAt, hp, dite_true, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact castHom_eq_zero_of_dvd_val
    (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) k) hdiv

/-- A cyclic good translate is represented exactly by the full family of
scaled character layers. -/
theorem primeExtension_shiftVal_eq_sum_scaledShiftedCharacter
    (z : PrimeAssignment) {q k H : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) {a : ZMod (q ^ k)}
    (ha : a ∈ cyclicGoodResidues q k H)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H)) :
    (primeExtension z (a + (m : ZMod (q ^ k))).val : ℂ) =
      ∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * scaledShiftedCharacter χ d m a := by
  let n := (a + (m : ZMod (q ^ k))).val
  have hav := avoids_of_mem_cyclicGoodResidues ha hm
  have hn : n ≠ 0 := by
    intro hn0
    have hp : q.minFac.Prime := Nat.minFac_prime hq.ne'
    have hpq : q.minFac ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd q, (NeZero.ne q)⟩
    exact (hav q.minFac hpq) (by simp [n, hn0])
  have h := primeExtension_eq_sum_scaledCharacter_of_avoids
    z χ hagree hn hav
  simpa only [n, naturalScaledCharacter, scaledShiftedCharacter,
    scaledCharacter] using h

/-- Summing the preceding pointwise identity gives the exact full-family
prefix representation.  The spatial argument is shifted by one because the
cyclic good set controls shifts `1, ..., 2H`. -/
theorem fullDivisorPrefix_eq_primeExtensionPrefix
    (z : PrimeAssignment) {q k H L : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) {a : ZMod (q ^ k)}
    (ha : a ∈ cyclicGoodResidues q k H) (hL : L ≤ 2 * H) :
    (∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) *
          scaledCharacterPrefix χ d L (a + 1)) =
      ∑ m ∈ Finset.range L,
        (primeExtension z (a + ((m + 1 : ℕ) : ZMod (q ^ k))).val : ℂ) := by
  classical
  simp only [scaledCharacterPrefix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmIcc : m + 1 ∈ Finset.Icc 1 (2 * H) := by
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_Icc]
    omega
  have hpoint := primeExtension_shiftVal_eq_sum_scaledShiftedCharacter
    z χ hagree hq ha hmIcc
  symm
  simpa [scaledShiftedCharacter, add_assoc, add_comm, add_left_comm]
    using hpoint

private theorem sum_Icc_one_eq_sum_range_succ {E : Type*} [AddCommMonoid E]
    (F : ℕ → E) (L : ℕ) :
    (∑ m ∈ Finset.Icc 1 L, F m) =
      ∑ m ∈ Finset.range L, F (m + 1) := by
  symm
  apply Finset.sum_bij (fun m _ ↦ m + 1)
  · intro m hm
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_Icc]
    omega
  · intro m₁ hm₁ m₂ hm₂ h
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨m - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

/-- The same prefix identity with its target in the exact `1 ≤ m ≤ L`
form used for discrepancy sums. -/
theorem fullDivisorPrefix_eq_primeExtensionPrefix_Icc
    (z : PrimeAssignment) {q k H L : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) {a : ZMod (q ^ k)}
    (ha : a ∈ cyclicGoodResidues q k H) (hL : L ≤ 2 * H) :
    (∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) *
          scaledCharacterPrefix χ d L (a + 1)) =
      ∑ m ∈ Finset.Icc 1 L,
        (primeExtension z (a + (m : ZMod (q ^ k))).val : ℂ) := by
  rw [fullDivisorPrefix_eq_primeExtensionPrefix z χ hagree hq ha hL,
    sum_Icc_one_eq_sum_range_succ]

@[simp]
theorem norm_primeExtension_coe (z : PrimeAssignment) (n : ℕ) :
    ‖(primeExtension z n : ℂ)‖ = 1 := Circle.norm_coe _

@[simp]
theorem normSq_primeExtension_coe (z : PrimeAssignment) (n : ℕ) :
    Complex.normSq (primeExtension z n : ℂ) = 1 := Circle.normSq_coe _

/-- Divisor-index data for the BCC Fourier consumer: if
`d ∣ q ^ (k - 1)` and `k > 0`, then `q * d` divides the ambient modulus
`q ^ k`. -/
theorem q_mul_dvd_pow_of_dvd_pow_pred {q k d : ℕ} (hk : 0 < k)
    (hd : d ∣ q ^ (k - 1)) : q * d ∣ q ^ k := by
  obtain ⟨e, he⟩ := hd
  refine ⟨e, ?_⟩
  rw [show k = (k - 1) + 1 by omega, pow_succ, he]
  ring

theorem pow_eq_div_q_mul_mul_q_mul {q k d : ℕ} (hk : 0 < k)
    (hd : d ∣ q ^ (k - 1)) :
    q ^ k = (q ^ k / (q * d)) * (q * d) := by
  exact (Nat.div_mul_cancel (q_mul_dvd_pow_of_dvd_pow_pred hk hd)).symm

theorem neZero_pow_div_q_mul {q k d : ℕ} [NeZero q] [NeZero d]
    (hk : 0 < k) (hd : d ∣ q ^ (k - 1)) :
    NeZero (q ^ k / (q * d)) := by
  have hdiv := q_mul_dvd_pow_of_dvd_pow_pred hk hd
  have hdenpos : 0 < q * d := mul_pos (NeZero.pos q) (NeZero.pos d)
  have hdenle : q * d ≤ q ^ k :=
    Nat.le_of_dvd (pow_pos (NeZero.pos q) k) hdiv
  exact ⟨Nat.ne_of_gt (Nat.div_pos hdenle hdenpos)⟩

/-- For an arbitrary integer, at most one divisor layer can have a unit
quotient modulo `q`.  Consequently the full pointwise divisor sum has norm at
most one, even without a good-residue assumption. -/
theorem norm_sum_naturalScaledCharacter_le_one
    (z : PrimeAssignment) {q r n : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) :
    ‖∑ d ∈ (q ^ r).divisors,
        (primeExtension z d : ℂ) * naturalScaledCharacter χ d n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    have hnonunit : ¬IsUnit ((0 : ℕ) : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      simpa using hq.ne'
    have hzero (d : ℕ) : naturalScaledCharacter χ d 0 = 0 := by
      rw [naturalScaledCharacter_of_dvd χ (dvd_zero d), Nat.zero_div,
        χ.map_nonunit hnonunit]
    simp_rw [hzero, mul_zero]
    simp
  · let Q := q ^ r
    let g := Nat.gcd n Q
    have hQ0 : Q ≠ 0 := pow_ne_zero _ (NeZero.ne q)
    have hgQ : g ∣ Q := Nat.gcd_dvd_right n Q
    have hgn : g ∣ n := Nat.gcd_dvd_left n Q
    have hsum :
        (∑ d ∈ Q.divisors,
            (primeExtension z d : ℂ) * naturalScaledCharacter χ d n) =
          (primeExtension z g : ℂ) * naturalScaledCharacter χ g n := by
      apply Finset.sum_eq_single g
      · intro d hddiv hdne
        by_cases hdn : d ∣ n
        · rw [naturalScaledCharacter_of_dvd χ hdn]
          by_cases hcop : (n / d).Coprime q
          · have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hddiv
            have hdg : d = g := by
              simpa only [g, Q] using
                (eq_gcd_of_dvd_pow_of_dvd_of_div_coprime hn hdQ hdn hcop)
            exact (hdne hdg).elim
          · have hnonunit : ¬IsUnit (((n / d : ℕ) : ZMod q)) :=
              (not_congr (ZMod.isUnit_iff_coprime (n / d) q)).mpr hcop
            rw [χ.map_nonunit hnonunit, mul_zero]
        · rw [naturalScaledCharacter_of_not_dvd χ hdn, mul_zero]
      · intro hgnot
        exact (hgnot (Nat.mem_divisors.mpr ⟨hgQ, hQ0⟩)).elim
    change ‖∑ d ∈ Q.divisors,
        (primeExtension z d : ℂ) * naturalScaledCharacter χ d n‖ ≤ 1
    rw [hsum, naturalScaledCharacter_of_dvd χ hgn, norm_mul,
      norm_primeExtension_coe, one_mul]
    exact χ.norm_le_one _

/-- Cyclic form of the preceding all-residue pointwise bound. -/
theorem norm_sum_scaledCharacter_le_one
    (z : PrimeAssignment) {q k : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) (a : ZMod (q ^ k)) :
    ‖∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * scaledCharacter χ d a‖ ≤ 1 := by
  simpa only [naturalScaledCharacter, scaledCharacter] using
    (norm_sum_naturalScaledCharacter_le_one z χ hq
      (r := k - 1) (n := a.val))

/-- The complete coefficient-weighted divisor prefix has the sharp trivial
bound `L`, independent of the number of divisor layers. -/
theorem norm_fullDivisor_scaledCharacterPrefix_le
    (z : PrimeAssignment) {q k L : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) (a : ZMod (q ^ k)) :
    ‖∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L a‖ ≤ L := by
  classical
  simp only [scaledCharacterPrefix, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ‖∑ m ∈ Finset.range L,
        ∑ d ∈ (q ^ (k - 1)).divisors,
          (primeExtension z d : ℂ) * scaledShiftedCharacter χ d m a‖ ≤
        ∑ m ∈ Finset.range L,
          ‖∑ d ∈ (q ^ (k - 1)).divisors,
            (primeExtension z d : ℂ) * scaledShiftedCharacter χ d m a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m _hm
      simpa only [scaledShiftedCharacter] using
        norm_sum_scaledCharacter_le_one z χ hq (a + (m : ZMod (q ^ k)))
    _ = L := by simp

theorem normSq_fullDivisor_scaledCharacterPrefix_le
    (z : PrimeAssignment) {q k L : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) (a : ZMod (q ^ k)) :
    Complex.normSq
        (∑ d ∈ (q ^ (k - 1)).divisors,
          (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L a) ≤
      (L : ℝ) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_fullDivisor_scaledCharacterPrefix_le z χ hq (L := L) a,
    norm_nonneg
      (∑ d ∈ (q ^ (k - 1)).divisors,
        (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L a)]

end

end Erdos67b
