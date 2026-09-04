/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.Selector

/-!
Canonical factorization of a denominator into the prime-power factors that are
`1 mod 4` and the complementary (anisotropic) factors.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full factorization of `d`, restricted to primes that are `1 mod 4`. -/
def nontrivialFactorization (d : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p ↦ p % 4 = 1) d.factorization

/-- The complementary full factorization of `d`. -/
def trivialFactorization (d : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p ↦ p % 4 ≠ 1) d.factorization

/-- Product of the full prime-power factors of `d` whose primes are `1 mod 4`. -/
def nontrivialPart (d : ℕ) : ℕ :=
  (nontrivialFactorization d).prod fun p e ↦ p ^ e

/-- Product of the complementary full prime-power factors of `d`. -/
def trivialPart (d : ℕ) : ℕ :=
  (trivialFactorization d).prod fun p e ↦ p ^ e

lemma nontrivialFactorization_le (d : ℕ) :
    nontrivialFactorization d ≤ d.factorization := by
  intro p
  simp only [nontrivialFactorization, Finsupp.filter_apply]
  split <;> simp_all

lemma trivialFactorization_le (d : ℕ) :
    trivialFactorization d ≤ d.factorization := by
  intro p
  simp only [trivialFactorization, Finsupp.filter_apply]
  split <;> simp_all

@[simp] theorem factorization_nontrivialPart (d : ℕ) :
    (nontrivialPart d).factorization = nontrivialFactorization d := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (nontrivialFactorization_le d)

@[simp] theorem factorization_trivialPart (d : ℕ) :
    (trivialPart d).factorization = trivialFactorization d := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (trivialFactorization_le d)

/-- The two products partition all prime-power factors of a nonzero denominator. -/
theorem nontrivialPart_mul_trivialPart (d : ℕ) (hd : d ≠ 0) :
    nontrivialPart d * trivialPart d = d := by
  rw [nontrivialPart, trivialPart,
    ← Finsupp.prod_add_index' (fun _ ↦ by simp) (fun p a b ↦ Nat.pow_add p a b)]
  rw [nontrivialFactorization, trivialFactorization,
    Finsupp.filter_add_filter_not]
  exact Nat.prod_factorization_pow_eq_self hd

lemma nontrivialPart_ne_zero (d : ℕ) (hd : d ≠ 0) : nontrivialPart d ≠ 0 := by
  intro h
  have hprod := nontrivialPart_mul_trivialPart d hd
  rw [h, zero_mul] at hprod
  exact hd hprod.symm

lemma trivialPart_ne_zero (d : ℕ) (hd : d ≠ 0) : trivialPart d ≠ 0 := by
  intro h
  have hprod := nontrivialPart_mul_trivialPart d hd
  rw [h, mul_zero] at hprod
  exact hd hprod.symm

@[simp] theorem factorization_nontrivialPart_apply (d q : ℕ) :
    (nontrivialPart d).factorization q =
      if q % 4 = 1 then d.factorization q else 0 := by
  rw [factorization_nontrivialPart, nontrivialFactorization, Finsupp.filter_apply]

@[simp] theorem factorization_trivialPart_apply (d q : ℕ) :
    (trivialPart d).factorization q =
      if q % 4 ≠ 1 then d.factorization q else 0 := by
  rw [factorization_trivialPart, trivialFactorization, Finsupp.filter_apply]

lemma prime_mod_four_ne_one_iff (q : ℕ) (hq : q.Prime) :
    q % 4 ≠ 1 ↔ q = 2 ∨ q % 4 = 3 := by
  constructor
  · intro hn1
    rcases hq.eq_two_or_odd with rfl | hodd
    · exact Or.inl rfl
    · right
      have hpar : q % 4 % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 4)]
        exact hodd
      have hlt : q % 4 < 4 := Nat.mod_lt _ (by omega)
      omega
  · rintro (rfl | h3)
    · norm_num
    · omega

theorem prime_dvd_nontrivialPart_iff (d q : ℕ) (hd : d ≠ 0) (hq : q.Prime) :
    q ∣ nontrivialPart d ↔ q ∣ d ∧ q % 4 = 1 := by
  rw [hq.dvd_iff_one_le_factorization (nontrivialPart_ne_zero d hd)]
  simp only [factorization_nontrivialPart_apply]
  by_cases hq1 : q % 4 = 1
  · simp [hq1, hq.dvd_iff_one_le_factorization hd]
  · simp [hq1]

theorem prime_dvd_trivialPart_iff (d q : ℕ) (hd : d ≠ 0) (hq : q.Prime) :
    q ∣ trivialPart d ↔ q ∣ d ∧ (q = 2 ∨ q % 4 = 3) := by
  rw [hq.dvd_iff_one_le_factorization (trivialPart_ne_zero d hd)]
  simp only [factorization_trivialPart_apply]
  rw [← prime_mod_four_ne_one_iff q hq]
  by_cases hq1 : q % 4 ≠ 1
  · simp [hq1, hq.dvd_iff_one_le_factorization hd]
  · simp [hq1]

theorem coprime_nontrivialPart_trivialPart (d : ℕ) (hd : d ≠ 0) :
    (nontrivialPart d).Coprime (trivialPart d) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨q, hq, hqgcd⟩ := Nat.exists_prime_and_dvd hgcd
  have hqP : q ∣ nontrivialPart d := (Nat.dvd_gcd_iff.mp hqgcd).1
  have hqQ : q ∣ trivialPart d := (Nat.dvd_gcd_iff.mp hqgcd).2
  have hP := (prime_dvd_nontrivialPart_iff d q hd hq).mp hqP
  have hQ := (prime_dvd_trivialPart_iff d q hd hq).mp hqQ
  rcases hQ.2 with rfl | hq3
  · norm_num at hP
  · omega

@[simp] theorem nontrivialPart_one : nontrivialPart 1 = 1 := by
  simp only [nontrivialPart, nontrivialFactorization, Nat.factorization_one,
    Finsupp.filter_zero, Finsupp.prod_zero_index]

@[simp] theorem trivialPart_one : trivialPart 1 = 1 := by
  simp only [trivialPart, trivialFactorization, Nat.factorization_one,
    Finsupp.filter_zero, Finsupp.prod_zero_index]

/-! ### Rigidity of the norm at the trivial denominator -/

def SquareNormRigid (Q : ℕ) : Prop :=
  ∀ A B : ℤ, (Q : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 → (Q : ℤ) ∣ A ∧ (Q : ℤ) ∣ B

@[simp] theorem squareNormRigid_one : SquareNormRigid 1 := by
  intro A B _
  simp

theorem SquareNormRigid.mul {m n : ℕ} (hmn : m.Coprime n)
    (hm : SquareNormRigid m) (hn : SquareNormRigid n) :
    SquareNormRigid (m * n) := by
  intro A B hnorm
  have hmSq : (m : ℤ) ^ 2 ∣ ((m * n : ℕ) : ℤ) ^ 2 := by
    refine ⟨(n : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  have hnSq : (n : ℤ) ^ 2 ∣ ((m * n : ℕ) : ℤ) ^ 2 := by
    refine ⟨(m : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  rcases hm A B (hmSq.trans hnorm) with ⟨hmA, hmB⟩
  rcases hn A B (hnSq.trans hnorm) with ⟨hnA, hnB⟩
  constructor
  · simpa only [Int.natCast_mul] using hmn.isCoprime.mul_dvd hmA hnA
  · simpa only [Int.natCast_mul] using hmn.isCoprime.mul_dvd hmB hnB

theorem squareNormRigid_two : SquareNormRigid 2 := by
  intro A B hnorm
  rcases Int.even_or_odd A with hAe | hAo
  · have hA : (2 : ℤ) ∣ A := even_iff_two_dvd.mp hAe
    rcases Int.even_or_odd B with hBe | hBo
    · exact ⟨hA, even_iff_two_dvd.mp hBe⟩
    · exfalso
      rcases hAe with ⟨a, rfl⟩
      rcases hBo with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega
  · rcases Int.even_or_odd B with hBe | hBo
    · exfalso
      rcases hAo with ⟨a, rfl⟩
      rcases hBe with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega
    · exfalso
      rcases hAo with ⟨a, rfl⟩
      rcases hBo with ⟨b, rfl⟩
      rcases hnorm with ⟨z, hz⟩
      norm_num at hz
      ring_nf at hz
      omega

theorem squareNormRigid_prime_mod_four_eq_three (q : ℕ) (hq : q.Prime)
    (hq3 : q % 4 = 3) : SquareNormRigid q := by
  let : Fact q.Prime := ⟨hq⟩
  intro A B hnorm
  have hqSq : (q : ℤ) ∣ (q : ℤ) ^ 2 := dvd_pow_self (q : ℤ) (by omega)
  have hqnorm : (q : ℤ) ∣ A ^ 2 + B ^ 2 := hqSq.trans hnorm
  have hzero : ((A ^ 2 + B ^ 2 : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hqnorm
  push_cast at hzero
  rcases normAnisotropic_of_prime_mod_four_eq_three q hq3 (A : ZMod q) (B : ZMod q)
      hzero with ⟨hA, hB⟩
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp hA,
    (ZMod.intCast_zmod_eq_zero_iff_dvd B q).mp hB⟩

theorem squareNormRigid_trivial_prime (q : ℕ) (hq : q.Prime)
    (htriv : q = 2 ∨ q % 4 = 3) : SquareNormRigid q := by
  rcases htriv with rfl | hq3
  · exact squareNormRigid_two
  · exact squareNormRigid_prime_mod_four_eq_three q hq hq3

theorem squareNormRigid_trivial_prime_pow (q e : ℕ) (hq : q.Prime)
    (htriv : q = 2 ∨ q % 4 = 3) : SquareNormRigid (q ^ e) := by
  induction e with
  | zero => simpa using squareNormRigid_one
  | succ e ih =>
      intro A B hnorm
      have hqSqDvd : (q : ℤ) ^ 2 ∣ ((q ^ (e + 1) : ℕ) : ℤ) ^ 2 := by
        refine ⟨((q ^ e : ℕ) : ℤ) ^ 2, ?_⟩
        push_cast
        rw [pow_succ]
        ring
      rcases squareNormRigid_trivial_prime q hq htriv A B (hqSqDvd.trans hnorm) with
        ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hcancel : ((q ^ e : ℕ) : ℤ) ^ 2 ∣ a ^ 2 + b ^ 2 := by
        have hnorm' : (q : ℤ) ^ 2 * ((q ^ e : ℕ) : ℤ) ^ 2 ∣
            (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2) := by
          rw [ha, hb] at hnorm
          convert hnorm using 1 <;> push_cast <;> rw [pow_succ] <;> ring
        exact (Int.mul_dvd_mul_iff_left
          (pow_ne_zero 2 (by exact_mod_cast hq.ne_zero : (q : ℤ) ≠ 0))).mp hnorm'
      rcases ih a b hcancel with ⟨hae, hbe⟩
      rw [ha, hb]
      constructor
      · simpa only [Int.natCast_pow, pow_succ, Int.natCast_mul, mul_comm] using
          mul_dvd_mul_left (q : ℤ) hae
      · simpa only [Int.natCast_pow, pow_succ, Int.natCast_mul, mul_comm] using
          mul_dvd_mul_left (q : ℤ) hbe

theorem squareNormRigid_finset_prod {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    (hrigid : ∀ i ∈ s, SquareNormRigid (f i)) :
    SquareNormRigid (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using squareNormRigid_one
  | @insert i s his ih =>
      have hiCop : (f i).Coprime (∏ j ∈ s, f j) := by
        rw [Nat.coprime_prod_right_iff]
        intro j hj
        exact hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (fun hij ↦ his (hij ▸ hj))
      have hsRigid : SquareNormRigid (∏ j ∈ s, f j) := by
        apply ih
        · intro a ha b hb hab
          exact hcop a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
        · intro a ha
          exact hrigid a (Finset.mem_insert_of_mem ha)
      simpa [his] using SquareNormRigid.mul hiCop
        (hrigid i (Finset.mem_insert_self i s)) hsRigid

theorem squareNormRigid_trivialPart (d : ℕ) (hd : d ≠ 0) :
    SquareNormRigid (trivialPart d) := by
  let Q := trivialPart d
  have hQ : Q ≠ 0 := trivialPart_ne_zero d hd
  have hprod : Q = ∏ q ∈ Q.primeFactors, q ^ Q.factorization q :=
    Nat.prod_primeFactors_pow_factorization hQ
  change SquareNormRigid Q
  rw [hprod]
  apply squareNormRigid_finset_prod
  · intro p hp q hq hpq
    exact Nat.coprime_pow_primes _ _
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq) hpq
  · intro q hq
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqDvd : q ∣ trivialPart d := Nat.dvd_of_mem_primeFactors hq
    exact squareNormRigid_trivial_prime_pow q (Q.factorization q) hqPrime
      ((prime_dvd_trivialPart_iff d q hd hqPrime).mp hqDvd).2

/-! ### Reduced rational differences -/

/-- The two integer numerators are jointly reduced against their common
positive denominator. -/
def JointlyReduced (d : ℕ) (A B : ℤ) : Prop :=
  d.Coprime (Nat.gcd A.natAbs B.natAbs)

lemma trivialPart_dvd_denominator (d : ℕ) (hd : d ≠ 0) : trivialPart d ∣ d := by
  refine ⟨nontrivialPart d, ?_⟩
  calc
    d = nontrivialPart d * trivialPart d := (nontrivialPart_mul_trivialPart d hd).symm
    _ = trivialPart d * nontrivialPart d := Nat.mul_comm _ _

lemma not_both_trivialPart_dvd_of_jointlyReduced (d : ℕ) (hd : d ≠ 0)
    (A B : ℤ) (hred : JointlyReduced d A B) (hQ : trivialPart d ≠ 1) :
    ¬((trivialPart d : ℤ) ∣ A ∧ (trivialPart d : ℤ) ∣ B) := by
  rintro ⟨hA, hB⟩
  have hAn : trivialPart d ∣ A.natAbs := by
    simpa only [Int.natAbs_natCast] using
      (Int.natAbs_dvd_natAbs (a := (trivialPart d : ℤ)) (b := A)).2 hA
  have hBn : trivialPart d ∣ B.natAbs := by
    simpa only [Int.natAbs_natCast] using
      (Int.natAbs_dvd_natAbs (a := (trivialPart d : ℤ)) (b := B)).2 hB
  have hQgcd : trivialPart d ∣ Nat.gcd A.natAbs B.natAbs := Nat.dvd_gcd hAn hBn
  exact hQ (Nat.eq_one_of_dvd_coprimes hred (trivialPart_dvd_denominator d hd) hQgcd)

/-- If the trivial denominator component does not divide both numerators, the
corresponding rational squared norm cannot be an integer. -/
theorem div_sq_norm_not_int_of_trivialPart_not_both_dvd
    (d : ℕ) (hd : d ≠ 0) (A B : ℤ)
    (hcross : ¬((trivialPart d : ℤ) ∣ A ∧ (trivialPart d : ℤ) ∣ B)) :
    ¬∃ z : ℤ, ((A ^ 2 + B ^ 2 : ℤ) : ℚ) / (d : ℚ) ^ 2 = z := by
  intro hint
  have hdiv : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 :=
    (div_sq_isInt_iff d hd (A ^ 2 + B ^ 2)).mp hint
  have hprodZ : (nontrivialPart d : ℤ) * (trivialPart d : ℤ) = d := by
    exact_mod_cast nontrivialPart_mul_trivialPart d hd
  have hQSq : (trivialPart d : ℤ) ^ 2 ∣ (d : ℤ) ^ 2 := by
    refine ⟨(nontrivialPart d : ℤ) ^ 2, ?_⟩
    rw [← hprodZ]
    ring
  exact hcross (squareNormRigid_trivialPart d hd A B (hQSq.trans hdiv))

/-- Coordinate form of the preceding result. -/
theorem rational_sq_norm_not_int_of_trivialPart_not_both_dvd
    (d : ℕ) (hd : d ≠ 0) (A B : ℤ)
    (hcross : ¬((trivialPart d : ℤ) ∣ A ∧ (trivialPart d : ℤ) ∣ B)) :
    ¬∃ z : ℤ, ((A : ℚ) / d) ^ 2 + ((B : ℚ) / d) ^ 2 = z := by
  have heq : ((A : ℚ) / d) ^ 2 + ((B : ℚ) / d) ^ 2 =
      ((A ^ 2 + B ^ 2 : ℤ) : ℚ) / (d : ℚ) ^ 2 := by
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp [hdq]
  rw [heq]
  exact div_sq_norm_not_int_of_trivialPart_not_both_dvd d hd A B hcross

/-- A jointly reduced rational coordinate difference whose denominator has a
nonunit trivial component has nonintegral squared norm. -/
theorem rational_sq_norm_not_int_of_jointlyReduced
    (d : ℕ) (hd : d ≠ 0) (A B : ℤ) (hred : JointlyReduced d A B)
    (hQ : trivialPart d ≠ 1) :
    ¬∃ z : ℤ, ((A : ℚ) / d) ^ 2 + ((B : ℚ) / d) ^ 2 = z := by
  exact rational_sq_norm_not_int_of_trivialPart_not_both_dvd d hd A B
    (not_both_trivialPart_dvd_of_jointlyReduced d hd A B hred hQ)

end

end Erdos215.Selector
