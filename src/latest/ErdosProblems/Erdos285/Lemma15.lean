import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.Lemma14

/-!
# Martin's prime-power elimination lemma

This file formalizes the bounded two-term (or one-term at the prime `2`)
denominator correction used in the exact-correction stage of the proof of
Erdős Problem 285.
-/

namespace Erdos285.MartinCorrection

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

/-- Every exact prime-power part of an LCM is already an exact part of one of
the two inputs.  The exponent in an LCM is the maximum of the two exponents. -/
lemma primePowerParts_lcm_subset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primePowerParts (Nat.lcm a b) ⊆ primePowerParts a ∪ primePowerParts b := by
  intro q hq
  rcases (mem_primePowerParts (Nat.lcm_ne_zero ha hb)).mp hq with
    ⟨hqpp, hqdiv, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hlcmfac : (Nat.lcm a b).factorization p = k :=
    (UnitFractions.factorization_eq_iff hp hk.ne').mp ⟨hqdiv, hqcop⟩
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply] at hlcmfac
  have hcases : a.factorization p = k ∨ b.factorization p = k := by
    omega
  rw [Finset.mem_union]
  rcases hcases with hafac | hbfac
  · left
    apply (mem_primePowerParts ha).mpr
    exact ⟨hp.isPrimePow.pow hk.ne',
      (UnitFractions.factorization_eq_iff hp hk.ne').mpr hafac⟩
  · right
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow hk.ne',
      (UnitFractions.factorization_eq_iff hp hk.ne').mpr hbfac⟩

/-- Taking an LCM preserves a common upper bound for exact prime-power parts. -/
lemma largestPrimePowerPart_lcm_le {a b y : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_bound : largestPrimePowerPart a ≤ y)
    (hb_bound : largestPrimePowerPart b ≤ y) :
    largestPrimePowerPart (Nat.lcm a b) ≤ y := by
  rw [largestPrimePowerPart_le_iff] at ha_bound hb_bound ⊢
  intro q hq
  rcases Finset.mem_union.mp (primePowerParts_lcm_subset ha hb hq) with hqa | hqb
  · exact ha_bound q hqa
  · exact hb_bound q hqb

/-- A positive prime power is its own largest exact prime-power part. -/
lemma largestPrimePowerPart_primePower {q : ℕ} (hq : IsPrimePow q) :
    largestPrimePowerPart q = q := by
  apply le_antisymm largestPrimePowerPart_le
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts hq.ne_zero).mpr
  refine ⟨hq, dvd_rfl, ?_⟩
  rw [Nat.div_self hq.pos]
  exact (Nat.coprime_one_right_iff q).mpr trivial

/-- Multiplying a prime power by a smaller coprime factor leaves that prime
power as the largest exact prime-power part. -/
lemma largestPrimePowerPart_mul_eq_left {q m : ℕ} (hq : IsPrimePow q)
    (hm : m < q) (hcop : Nat.Coprime q m) :
    largestPrimePowerPart (q * m) = q := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    simp at hcop
    exact hq.ne_one hcop
  have hmul : Nat.lcm q m = q * m := hcop.lcm_eq_mul
  have hle : largestPrimePowerPart (q * m) ≤ q := by
    rw [← hmul]
    apply largestPrimePowerPart_lcm_le hq0 hm0
    · exact (largestPrimePowerPart_primePower hq).le
    · exact largestPrimePowerPart_le.trans (Nat.le_of_lt hm)
  apply le_antisymm hle
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts (mul_ne_zero hq0 hm0)).mpr
  refine ⟨hq, dvd_mul_right q m, ?_⟩
  simpa [Nat.mul_div_cancel_left _ hq.pos] using hcop

/-- If the first input has no exact prime-power part larger than the prime
power `q`, then `q` is an exact part of its LCM with `q`. -/
lemma primePower_mem_parts_lcm_right {a q : ℕ} (ha : a ≠ 0)
    (hq : IsPrimePow q) (ha_bound : largestPrimePowerPart a ≤ q) :
    q ∈ primePowerParts (Nat.lcm a q) := by
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, ν, hp, hν, rfl⟩
  have hfac_le : a.factorization p ≤ ν := by
    by_cases hfac0 : a.factorization p = 0
    · omega
    · have hpart : p ^ a.factorization p ∈ primePowerParts a := by
        apply (mem_primePowerParts ha).mpr
        exact ⟨hp.isPrimePow.pow hfac0,
          (UnitFractions.factorization_eq_iff hp hfac0).mpr rfl⟩
      have hpw_le : p ^ a.factorization p ≤ p ^ ν :=
        (le_largestPrimePowerPart hpart).trans ha_bound
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpw_le
  have hlcm0 : Nat.lcm a (p ^ ν) ≠ 0 :=
    Nat.lcm_ne_zero ha (pow_ne_zero _ hp.ne_zero)
  apply (mem_primePowerParts hlcm0).mpr
  refine ⟨hp.isPrimePow.pow hν.ne', ?_⟩
  apply (UnitFractions.factorization_eq_iff hp hν.ne').mpr
  rw [Nat.factorization_lcm ha (pow_ne_zero _ hp.ne_zero),
    Finsupp.sup_apply, hp.factorization_pow]
  simp [hfac_le]

/-- If all exact parts are at most `q`, but `q` itself does not divide the
integer, then the largest exact part is strictly smaller than `q`. -/
lemma largestPrimePowerPart_lt_of_le_of_not_dvd {n q : ℕ}
    (hq : IsPrimePow q) (hbound : largestPrimePowerPart n ≤ q)
    (hnotdvd : ¬ q ∣ n) : largestPrimePowerPart n < q := by
  by_cases hn : n < 2
  · have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hn
    simp [largestPrimePowerPart, hempty, hq.pos]
  · have hn2 : 2 ≤ n := Nat.le_of_not_gt hn
    have hmem := largestPrimePowerPart_mem hn2
    have hne : largestPrimePowerPart n ≠ q := by
      intro heq
      have hspec := (mem_primePowerParts (by omega)).mp hmem
      exact hnotdvd (heq ▸ hspec.2.1)
    omega

/-- Exact prime-power parts can only decrease on passing to a divisor. -/
lemma largestPrimePowerPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0)
    (hab : a ∣ b) : largestPrimePowerPart a ≤ largestPrimePowerPart b := by
  rw [largestPrimePowerPart_le_iff]
  intro q hqa
  rcases (mem_primePowerParts (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab)))).mp hqa with
    ⟨hqpp, hqdiva, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hafac : a.factorization p = k :=
    (UnitFractions.factorization_eq_iff hp hk.ne').mp ⟨hqdiva, hqcop⟩
  have hfac_le : a.factorization p ≤ b.factorization p := by
    exact (Nat.factorization_le_iff_dvd
      (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab))) hb).mpr hab p
  let K := b.factorization p
  have hK : K ≠ 0 := by
    dsimp [K]
    omega
  have hpart : p ^ K ∈ primePowerParts b := by
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow hK,
      (UnitFractions.factorization_eq_iff hp hK).mpr rfl⟩
  calc
    p ^ k ≤ p ^ K := Nat.pow_le_pow_right hp.pos (by simpa [K, hafac] using hfac_le)
    _ ≤ largestPrimePowerPart b := le_largestPrimePowerPart hpart

/-- A finite LCM has bounded exact prime-power parts when every member does. -/
lemma largestPrimePowerPart_finset_lcm_le {A : Finset ℕ} {q : ℕ}
    (hzero : 0 ∉ A) (hA : ∀ n ∈ A, largestPrimePowerPart n ≤ q) :
    largestPrimePowerPart (A.lcm id) ≤ q := by
  induction A using Finset.induction with
  | empty =>
      have hparts : primePowerParts 1 = ∅ := primePowerParts_empty_iff.mpr (by omega)
      simp [largestPrimePowerPart, hparts]
  | @insert n A hn ih =>
      have hn0 : n ≠ 0 := by
        intro hn0
        exact hzero (hn0 ▸ Finset.mem_insert_self n A)
      have hA0 : 0 ∉ A := fun h ↦ hzero (Finset.mem_insert_of_mem h)
      rw [Finset.lcm_insert]
      apply largestPrimePowerPart_lcm_le hn0 (UnitFractions.lcm_ne_zero_of_zero_not_mem hA0)
      · exact hA n (Finset.mem_insert_self n A)
      · apply ih hA0
        intro m hm
        exact hA m (Finset.mem_insert_of_mem hm)

/-- The residual denominator remains `q`-smooth after subtracting a finite
sum whose displayed denominators all have largest exact part `q`. -/
lemma residual_largestPrimePowerPart_le (q : ℕ) (r : ℚ) (U : Finset ℕ)
    (hq : IsPrimePow q) (hr : largestPrimePowerPart r.den ≤ q)
    (hU : ∀ n ∈ U, largestPrimePowerPart n = q) :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q := by
  have hzero : 0 ∉ U := by
    intro h0
    have hz := hU 0 h0
    simp [largestPrimePowerPart, primePowerParts] at hz
    exact hq.ne_zero hz.symm
  have hlcm0 : U.lcm id ≠ 0 := UnitFractions.lcm_ne_zero_of_zero_not_mem hzero
  have hUlcm : largestPrimePowerPart (U.lcm id) ≤ q := by
    apply largestPrimePowerPart_finset_lcm_le hzero
    intro n hn
    rw [hU n hn]
  let L := Nat.lcm r.den (U.lcm id)
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hlcm0
  have hLbound : largestPrimePowerPart L ≤ q :=
    largestPrimePowerPart_lcm_le r.den_ne_zero hlcm0 hr hUlcm
  have hrec : (UnitFractions.rec_sum U).den ∣ U.lcm id :=
    recSum_den_dvd_lcm U
  have hden : (r - UnitFractions.rec_sum U).den ∣ L := by
    exact (Rat.sub_den_dvd_lcm r (UnitFractions.rec_sum U)).trans
      (lcm_dvd_lcm dvd_rfl hrec)
  exact (largestPrimePowerPart_le_of_dvd hL0 hden).trans hLbound

/-- Put a rational and two unit fractions over a common displayed
denominator.  The LCM applications below take `D = lcm r.den q`. -/
lemma two_term_residual_eq_divInt (r : ℚ) (q m₁ m₂ D : ℕ)
    (hq : q ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hD0 : D ≠ 0)
    (hdenD : r.den ∣ D) (hqD : q ∣ D) :
    r - ((1 : ℚ) / (q * m₁) + 1 / (q * m₂)) =
      Rat.divInt
        (r.num * (D / r.den : ℕ) * m₁ * m₂ -
          ((D / q : ℕ) * (m₁ + m₂) : ℕ))
        (D * m₁ * m₂ : ℕ) := by
  have hden0 : r.den ≠ 0 := r.den_ne_zero
  have hDden : r.den * (D / r.den) = D := Nat.mul_div_cancel' hdenD
  have hDq : q * (D / q) = D := Nat.mul_div_cancel' hqD
  have hDdenQ : (r.den : ℚ) * (D / r.den : ℕ) = D := by exact_mod_cast hDden
  have hDqQ : (q : ℚ) * (D / q : ℕ) = D := by exact_mod_cast hDq
  have hcastDen : (D : ℚ) / r.den = (D / r.den : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDden.symm.trans (mul_comm _ _)
    · exact_mod_cast hden0
  have hcastQ : (D : ℚ) / q = (D / q : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDq.symm.trans (mul_comm _ _)
    · exact_mod_cast hq
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_add]
  field_simp
  simp only [Int.cast_add, Int.cast_natCast]
  ring_nf at hDdenQ hDqQ ⊢
  rw [hDdenQ]
  linear_combination ((r.den : ℚ) * m₁ + r.den * m₂) * hDqQ

/-- One-term version of the displayed-denominator identity. -/
lemma one_term_residual_eq_divInt (r : ℚ) (q m : ℕ)
    (hq : q ≠ 0) (hm : m ≠ 0) (hqd : q ∣ r.den) :
    r - (1 : ℚ) / (q * m : ℕ) =
      Rat.divInt (r.num * m - (r.den / q : ℕ)) (r.den * m) := by
  let d := r.den / q
  change r - (1 : ℚ) / (q * m : ℕ) =
    Rat.divInt (r.num * m - (d : ℕ)) (r.den * m)
  have hden : q * d = r.den := Nat.mul_div_cancel' hqd
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hdenQ : (q : ℚ) * d = r.den := by exact_mod_cast hden
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  push_cast
  field_simp
  rw [← hdenQ]
  ring

/-- Cancelling one copy of the underlying prime from a displayed denominator
whose exact `p`-part is `p^ν` makes that prime power cease to divide. -/
lemma primePow_not_dvd_mul_div_prime {p ν q D m : ℕ} (hp : p.Prime)
    (hν : 0 < ν) (hq : q = p ^ ν) (hpart : q ∈ primePowerParts D)
    (hpm : ¬ p ∣ m) : ¬ q ∣ (D * m) / p := by
  subst q
  have hD0 : D ≠ 0 := by
    intro h
    subst D
    simp [primePowerParts] at hpart
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hpm (dvd_zero p)
  have hDfac : D.factorization p = ν := by
    have hs := (mem_primePowerParts hD0).mp hpart
    exact (UnitFractions.factorization_eq_iff hp hν.ne').mp hs.2
  have hpD : p ∣ D := by
    exact (dvd_pow_self p hν.ne').trans ((mem_primePowerParts hD0).mp hpart).2.1
  have hpDm : p ∣ D * m := hpD.trans (dvd_mul_right D m)
  have hDm0 : D * m ≠ 0 := mul_ne_zero hD0 hm0
  have hB0 : (D * m) / p ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hDm0.bot_lt hpDm) hp.pos)
  have hfac : ((D * m) / p).factorization p = ν - 1 := by
    rw [Nat.factorization_div hpDm]
    simp [Nat.factorization_mul hD0 hm0, hDfac,
      Nat.factorization_eq_zero_of_not_dvd hpm, hp.factorization_self]
  intro hdvd
  have hνle : ν ≤ ((D * m) / p).factorization p :=
    (hp.pow_dvd_iff_le_factorization hB0).mp hdvd
  rw [hfac] at hνle
  omega

/-- Martin's prime-power elimination step.  The inequalities
`q^2 ≤ 5*n` and `n ≤ q^2` are the integral form of
`n ∈ [q^2/5,q^2]`. -/
theorem exists_elimination_set (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2) ∧
      (Odd q → U.card = 2) ∧
      (Even q → U.card ≤ 1) ∧
      (∀ n ∈ U, largestPrimePowerPart n = q) ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, ν, hp, hν, hqpow⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := hqpp.ne_zero
  by_cases hqodd : Odd q
  · have hq5 : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      omega
    let D := Nat.lcm r.den q
    have hD0 : D ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hq0
    have hdenD : r.den ∣ D := Nat.dvd_lcm_left _ _
    have hqD : q ∣ D := Nat.dvd_lcm_right _ _
    have hDpart : q ∈ primePowerParts D :=
      primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
    have hDspec := (mem_primePowerParts hD0).mp hDpart
    have hpq : p ∣ q := by
      rw [← hqpow]
      exact dvd_pow_self p hν.ne'
    have hpe : ¬ p ∣ D / q := by
      exact hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left hpq hDspec.2.2)
    let C : ℤ := r.num * (D / r.den : ℕ)
    let a : ZMod p := (C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹
    obtain ⟨m₁, m₂, hm₁lo, hm₁m₂, hm₂q, hpm, hinv⟩ :=
      martin_lemma14 hp hν hqpow.symm hqodd hq5 a
    have hm₁pos : 0 < m₁ := by
      have : 1 ≤ (q - 3) / 2 := by omega
      omega
    have hm₂pos : 0 < m₂ := hm₁pos.trans hm₁m₂
    have hpm₁ : ¬ p ∣ m₁ := fun h ↦ hpm (h.trans (dvd_mul_right m₁ m₂))
    have hpm₂ : ¬ p ∣ m₂ := fun h ↦ hpm (h.trans (dvd_mul_left m₂ m₁))
    have hcop₁ : Nat.Coprime q m₁ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₁).symm
    have hcop₂ : Nat.Coprime q m₂ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₂).symm
    let n₁ := q * m₁
    let n₂ := q * m₂
    have hn₁ne : n₁ ≠ n₂ := by
      dsimp [n₁, n₂]
      intro h
      exact (Nat.ne_of_lt hm₁m₂) (mul_left_cancel₀ hq0 h)
    let U : Finset ℕ := {n₁, n₂}
    have hn₁largest : largestPrimePowerPart n₁ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp (hm₁m₂.trans hm₂q) hcop₁
    have hn₂largest : largestPrimePowerPart n₂ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp hm₂q hcop₂
    have hUlargest : ∀ n ∈ U, largestPrimePowerPart n = q := by
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hn₁largest
      · exact hn₂largest
    have hinterval : ∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2 := by
      have hbase : q ≤ 5 * ((q - 3) / 2) := by
        obtain ⟨t, ht⟩ := hqodd
        omega
      have hqm₁ : q ≤ 5 * m₁ :=
        hbase.trans (Nat.mul_le_mul_left 5 hm₁lo)
      have hqm₂ : q ≤ 5 * m₂ := hqm₁.trans (Nat.mul_le_mul_left 5 hm₁m₂.le)
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · dsimp [n₁]
        constructor <;> nlinarith
      · dsimp [n₂]
        constructor <;> nlinarith
    let z : ℤ := C * m₁ * m₂ - ((D / q) * (m₁ + m₂) : ℕ)
    have hecast : ((D / q : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpe
    have hm₁cast : (m₁ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₁
    have hm₂cast : (m₂ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₂
    have hzcast : (z : ZMod p) = 0 := by
      simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Nat.cast_mul,
        Nat.cast_add]
      calc
        (C : ZMod p) * m₁ * m₂ -
            (D / q : ℕ) * ((m₁ : ZMod p) + (m₂ : ZMod p)) =
            (D / q : ℕ) * m₁ * m₂ *
              ((C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹ -
                ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹)) := by
                  field_simp
                  ring
        _ = 0 := by rw [hinv]; simp [a]
    have hpz : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzcast
    have hrepr : r - UnitFractions.rec_sum U =
        Rat.divInt z (D * m₁ * m₂) := by
      have hraw := two_term_residual_eq_divInt r q m₁ m₂ D hq0
        hm₁pos.ne' hm₂pos.ne' hD0 hdenD hqD
      dsimp [z, C]
      simpa [U, n₁, n₂, UnitFractions.rec_sum, hn₁ne, sub_eq_add_neg,
        add_assoc] using hraw
    have hpB : p ∣ D * m₁ * m₂ := by
      exact (hpq.trans hDspec.2.1).trans
        (dvd_mul_of_dvd_left (dvd_mul_right D m₁) m₂)
    have hdenDiv : (r - UnitFractions.rec_sum U).den ∣
        (D * (m₁ * m₂)) / p := by
      have := ExactCorrection.rat_den_dvd_div_of_eq_divInt
        (r := r - UnitFractions.rec_sum U) (a := z)
        (b := D * m₁ * m₂) (p := p)
        (mul_ne_zero (mul_ne_zero hD0 hm₁pos.ne') hm₂pos.ne') hp.ne_zero hpB hpz hrepr
      simpa [mul_assoc] using this
    have hqnotB : ¬ q ∣ (D * (m₁ * m₂)) / p :=
      primePow_not_dvd_mul_div_prime hp hν hqpow.symm hDpart hpm
    have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
      fun h ↦ hqnotB (h.trans hdenDiv)
    have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
      residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
    refine ⟨U, hinterval, ?_, ?_, hUlargest,
      largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
    · intro _
      simp [U, hn₁ne]
    · intro heven
      exact ((Nat.not_even_iff_odd.mpr hqodd) heven).elim
  · have hqeven : Even q := Nat.not_odd_iff_even.mp hqodd
    by_cases hqd : q ∣ r.den
    · -- The even correction is the single denominator `q(q-1)`.
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd' with hp2 | hpodd
        · exact hp2
        · exfalso
          apply hqodd
          rw [← hqpow]
          exact hpodd.pow
      subst p
      have hqpow2 : q = 2 ^ ν := hqpow.symm
      have h2q : 2 ∣ q := by
        rw [hqpow2]
        exact dvd_pow_self 2 hν.ne'
      let m := q - 1
      have hmpos : 0 < m := by dsimp [m]; omega
      have hcop : Nat.Coprime q m := by
        apply (Nat.coprime_sub_self_left (Nat.sub_le q 1)).mp
        have hsub : q - (q - 1) = 1 := by omega
        rw [hsub]
        exact (Nat.coprime_one_left_iff (q - 1)).mpr trivial
      have h2m : ¬ 2 ∣ m := by
        exact Nat.prime_two.coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_left h2q hcop)
      let n := q * m
      let U : Finset ℕ := {n}
      have hnlargest : largestPrimePowerPart n = q := by
        apply largestPrimePowerPart_mul_eq_left hqpp
        · dsimp [m]
          omega
        · exact hcop
      have hUlargest : ∀ x ∈ U, largestPrimePowerPart x = q := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        rw [hx']
        exact hnlargest
      have hinterval : ∀ x ∈ U, q ^ 2 ≤ 5 * x ∧ x ≤ q ^ 2 := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        subst x
        dsimp [n, m]
        constructor
        · have hsmall : q ≤ 5 * (q - 1) := by omega
          have := Nat.mul_le_mul_left q hsmall
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
        · have := Nat.mul_le_mul_left q (Nat.sub_le q 1)
          simpa [pow_two] using this
      have hlcm : Nat.lcm r.den q = r.den := by
        apply Nat.dvd_antisymm
        · exact Nat.lcm_dvd dvd_rfl hqd
        · exact Nat.dvd_lcm_left _ _
      have hdenpart : q ∈ primePowerParts r.den := by
        have h := primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
        rwa [hlcm] at h
      have hdenspec := (mem_primePowerParts r.den_ne_zero).mp hdenpart
      have h2den : 2 ∣ r.den := h2q.trans hqd
      have hnumcop : Nat.Coprime 2 r.num.natAbs :=
        Nat.Coprime.of_dvd_left h2den r.reduced.symm
      have hquotcop : Nat.Coprime 2 (r.den / q) :=
        Nat.Coprime.of_dvd_left h2q hdenspec.2.2
      have hnumcast : (r.num : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact fun hdiv ↦ (Nat.prime_two.coprime_iff_not_dvd.mp hnumcop)
          (Int.natCast_dvd.mp hdiv)
      have hmcast : (m : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact h2m
      have hquotcast : ((r.den / q : ℕ) : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.prime_two.coprime_iff_not_dvd.mp hquotcop
      have hnum1 : (r.num : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hnumcast
      have hm1 : (m : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hmcast
      have hquot1 : ((r.den / q : ℕ) : ZMod 2) = 1 :=
        Fin.eq_one_of_ne_zero _ hquotcast
      let z : ℤ := r.num * m - (r.den / q : ℕ)
      have hzcast : (z : ZMod 2) = 0 := by
        simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        rw [hnum1, hm1, hquot1]
        ring
      have h2z : (2 : ℤ) ∣ z :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hzcast
      have hrepr : r - UnitFractions.rec_sum U =
          Rat.divInt z (r.den * m) := by
        have hraw := one_term_residual_eq_divInt r q m hq0 hmpos.ne' hqd
        dsimp [z]
        simpa [U, n, UnitFractions.rec_sum] using hraw
      have h2B : 2 ∣ r.den * m := h2den.trans (dvd_mul_right r.den m)
      have hdenDiv : (r - UnitFractions.rec_sum U).den ∣ (r.den * m) / 2 :=
        ExactCorrection.rat_den_dvd_div_of_eq_divInt
          (r := r - UnitFractions.rec_sum U) (a := z) (b := r.den * m) (p := 2)
          (mul_ne_zero r.den_ne_zero hmpos.ne') (by norm_num) h2B h2z hrepr
      have hqnotB : ¬ q ∣ (r.den * m) / 2 :=
        primePow_not_dvd_mul_div_prime Nat.prime_two hν hqpow2 hdenpart h2m
      have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
        fun h ↦ hqnotB (h.trans hdenDiv)
      have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
        residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
      refine ⟨U, hinterval, ?_, ?_, hUlargest,
        largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
      · intro h
        exact (hqodd h).elim
      · intro _
        simp [U]
    · refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro h
        exact (hqodd h).elim
      · simp
      · simp
      · simpa using largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hr hqd

#print axioms Erdos285.MartinCorrection.exists_elimination_set

end

end Erdos285.MartinCorrection
