import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058PrimeGapBatch210
import ErdosProblems.Erdos1058.Erdos1058PeriodicCertificates
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Erdos1058

open Nat

noncomputable section

lemma cubicCRTLocalForm_of_isCubeMod
    {d kind r p q : ℕ} (hrmem : r ∈ cubicModuli)
    (hkind : kind ≤ 2) (hp433 : 433 < p) (hp : p.Prime)
    (hq : q.Prime) (hqp : q = p + d)
    (hcube : IsCubeMod r (cubicCRTLocalBase d kind r p)) :
    cubicCRTLocalForm d kind r p = true := by
  have hr := prime_of_mem_cubicModuli hrmem
  have hr433 := le_433_of_mem_cubicModuli hrmem
  have hr2 : 2 ≤ r := hr.two_le
  have hrp : r < p := by omega
  have hpq : p ≤ q := by rw [hqp]; omega
  have hrq : r < q := hrp.trans_le hpq
  have hpnonzero : p % r ≠ 0 := by
    intro hzero
    have hdiv : r ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
    rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega
  have hqnonzero : (p + d) % r ≠ 0 := by
    rw [← hqp]
    intro hzero
    have hdiv : r ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hzero
    rcases (Nat.dvd_prime hq).mp hdiv with h | h <;> omega
  have hpunit : IsUnit (p : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hp (Nat.not_dvd_of_pos_of_lt hr.pos hrp)
  have hqunit : IsUnit (q : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hq (Nat.not_dvd_of_pos_of_lt hr.pos hrq)
  have hbaseunit : IsUnit ((cubicCRTLocalBase d kind r p : ℕ) : ZMod r) := by
    interval_cases kind
    · rw [cast_cubicCRTLocalBase_zero, ← hqp]
      exact hpunit.mul hqunit
    · rw [cast_cubicCRTLocalBase_one, ← hqp]
      exact hpunit.mul (hqunit.pow 2)
    · rw [cast_cubicCRTLocalBase_two]
      exact hpunit
  rw [cubicCRTLocalForm_eq_true_iff hr.one_lt]
  exact ⟨hpnonzero, hqnonzero,
    pow_div_three_eq_one_of_isCubeMod hr
      (three_dvd_sub_one_of_mem_cubicModuli hrmem) hbaseunit hcube⟩

lemma exists_not_isCubeMod_cubicCRTLocalBase_of_obstruction
    {d kind p q : ℕ} (hkind : kind ≤ 2)
    (hp433 : 433 < p) (hp36 : p < 36000000)
    (hp : p.Prime) (hq : q.Prime) (hqp : q = p + d)
    (hobstruction : PeriodicSieveCertificate.Obstruction d kind) :
    ∃ r ∈ cubicModuli, ¬IsCubeMod r (cubicCRTLocalBase d kind r p) := by
  by_contra hnone
  push_neg at hnone
  apply hobstruction p hp433 hp36 hp (by simpa only [hqp] using hq)
  intro r hr
  have hrmem := mem_cubicModuli_of_mem_list hr
  exact cubicCRTLocalForm_of_isCubeMod hrmem hkind hp433 hp hq hqp
    (hnone r hrmem)

lemma isCubeMod_of_cast_eq {m x y : ℕ}
    (hxy : (x : ZMod m) = (y : ZMod m)) (hx : IsCubeMod m x) :
    IsCubeMod m y := by
  rcases hx with ⟨z, hz⟩
  exact ⟨z, hz.trans hxy⟩

lemma isCubeMod_iff_of_cast_eq {m x y : ℕ}
    (hxy : (x : ZMod m) = (y : ZMod m)) :
    IsCubeMod m x ↔ IsCubeMod m y := by
  constructor
  · exact isCubeMod_of_cast_eq hxy
  · exact isCubeMod_of_cast_eq hxy.symm

lemma isCubeMod_of_square_isCubeMod {m z : ℕ}
    (hzunit : IsUnit (z : ZMod m)) (hsq : IsCubeMod m (z ^ 2)) :
    IsCubeMod m z := by
  change IsCube (z : ZMod m)
  apply isCube_of_sq hzunit
  change IsCube (((z ^ 2 : ℕ) : ZMod m)) at hsq
  simpa only [Nat.cast_pow] using hsq

lemma cubicSieveHolds_of_periodic_obstructions
    {p q d : ℕ} (hp433 : 433 < p) (hpq : p < q) (hq36 : q < 36000000)
    (hp : p.Prime) (hq : q.Prime) (hqp : q = p + d)
    (hzero : PeriodicSieveCertificate.Obstruction d 0)
    (hone : PeriodicSieveCertificate.Obstruction d 1)
    (hsingle : PeriodicSieveCertificate.Obstruction 0 2) :
    CubicSieveHolds p q := by
  have hp36 : p < 36000000 := hpq.trans hq36
  have hq433 : 433 < q := hp433.trans hpq
  have hbaseP :=
    exists_not_isCubeMod_cubicCRTLocalBase_of_obstruction
      (d := 0) (kind := 2) (p := p) (q := p) (by omega)
      hp433 hp36 hp hp (by omega) hsingle
  have hbaseQ :=
    exists_not_isCubeMod_cubicCRTLocalBase_of_obstruction
      (d := 0) (kind := 2) (p := q) (q := q) (by omega)
      hq433 hq36 hq hq (by omega) hsingle
  have hbaseZero :=
    exists_not_isCubeMod_cubicCRTLocalBase_of_obstruction
      (d := d) (kind := 0) (p := p) (q := q) (by omega)
      hp433 hp36 hp hq hqp hzero
  have hbaseOne :=
    exists_not_isCubeMod_cubicCRTLocalBase_of_obstruction
      (d := d) (kind := 1) (p := p) (q := q) (by omega)
      hp433 hp36 hp hq hqp hone
  have hpOne : ∃ r ∈ cubicModuli, ¬IsCubeMod r p := by
    obtain ⟨r, hr, hnot⟩ := hbaseP
    refine ⟨r, hr, ?_⟩
    intro hcube
    apply hnot
    exact isCubeMod_of_cast_eq (cast_cubicCRTLocalBase_two 0 r p).symm hcube
  have hpTwo : ∃ r ∈ cubicModuli, ¬IsCubeMod r (p ^ 2) := by
    obtain ⟨r, hr, hnot⟩ := hbaseP
    have hrprime := prime_of_mem_cubicModuli hr
    have hrp : r < p := by
      have := le_433_of_mem_cubicModuli hr
      omega
    have hpunit : IsUnit (p : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hp
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrp)
    refine ⟨r, hr, ?_⟩
    intro hcube
    apply hnot
    exact isCubeMod_of_cast_eq (cast_cubicCRTLocalBase_two 0 r p).symm
      (isCubeMod_of_square_isCubeMod hpunit hcube)
  have hqOne : ∃ r ∈ cubicModuli, ¬IsCubeMod r q := by
    obtain ⟨r, hr, hnot⟩ := hbaseQ
    refine ⟨r, hr, ?_⟩
    intro hcube
    apply hnot
    exact isCubeMod_of_cast_eq (cast_cubicCRTLocalBase_two 0 r q).symm hcube
  have hqTwo : ∃ r ∈ cubicModuli, ¬IsCubeMod r (q ^ 2) := by
    obtain ⟨r, hr, hnot⟩ := hbaseQ
    have hrprime := prime_of_mem_cubicModuli hr
    have hrq : r < q := by
      have := le_433_of_mem_cubicModuli hr
      omega
    have hqunit : IsUnit (q : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hq
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrq)
    refine ⟨r, hr, ?_⟩
    intro hcube
    apply hnot
    exact isCubeMod_of_cast_eq (cast_cubicCRTLocalBase_two 0 r q).symm
      (isCubeMod_of_square_isCubeMod hqunit hcube)
  have hpqOneOne : ∃ r ∈ cubicModuli, ¬IsCubeMod r (p * q) := by
    obtain ⟨r, hr, hnot⟩ := hbaseZero
    have hcast : ((cubicCRTLocalBase d 0 r p : ℕ) : ZMod r) =
        ((p * q : ℕ) : ZMod r) := by
      rw [cast_cubicCRTLocalBase_zero, ← hqp]
      simp
    refine ⟨r, hr, ?_⟩
    intro hcube
    exact hnot (isCubeMod_of_cast_eq hcast.symm hcube)
  have hpqTwoTwo : ∃ r ∈ cubicModuli,
      ¬IsCubeMod r (p ^ 2 * q ^ 2) := by
    obtain ⟨r, hr, hnot⟩ := hbaseZero
    have hrprime := prime_of_mem_cubicModuli hr
    have hrp : r < p := by
      have := le_433_of_mem_cubicModuli hr
      omega
    have hrq : r < q := hrp.trans hpq
    have hpunit : IsUnit (p : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hp
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrp)
    have hqunit : IsUnit (q : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hq
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrq)
    have hpqunit : IsUnit (((p * q : ℕ) : ZMod r)) := by
      push_cast
      exact hpunit.mul hqunit
    have hcast : ((cubicCRTLocalBase d 0 r p : ℕ) : ZMod r) =
        ((p * q : ℕ) : ZMod r) := by
      rw [cast_cubicCRTLocalBase_zero, ← hqp]
      simp
    refine ⟨r, hr, ?_⟩
    intro hcube
    have hsquare : IsCubeMod r ((p * q) ^ 2) :=
      isCubeMod_of_cast_eq (by push_cast; ring) hcube
    have hone := isCubeMod_of_square_isCubeMod hpqunit hsquare
    exact hnot (isCubeMod_of_cast_eq hcast.symm hone)
  have hpqOneTwo : ∃ r ∈ cubicModuli,
      ¬IsCubeMod r (p * q ^ 2) := by
    obtain ⟨r, hr, hnot⟩ := hbaseOne
    have hcast : ((cubicCRTLocalBase d 1 r p : ℕ) : ZMod r) =
        ((p * q ^ 2 : ℕ) : ZMod r) := by
      rw [cast_cubicCRTLocalBase_one, ← hqp]
      simp
    refine ⟨r, hr, ?_⟩
    intro hcube
    exact hnot (isCubeMod_of_cast_eq hcast.symm hcube)
  have hpqTwoOne : ∃ r ∈ cubicModuli,
      ¬IsCubeMod r (p ^ 2 * q) := by
    obtain ⟨r, hr, hnot⟩ := hbaseOne
    have hrprime := prime_of_mem_cubicModuli hr
    have hrp : r < p := by
      have := le_433_of_mem_cubicModuli hr
      omega
    have hrq : r < q := hrp.trans hpq
    have hpunit : IsUnit (p : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hp
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrp)
    have hqunit : IsUnit (q : ZMod r) :=
      ZMod.isUnit_prime_of_not_dvd hq
        (Nat.not_dvd_of_pos_of_lt hrprime.pos hrq)
    have hpq2unit : IsUnit (((p * q ^ 2 : ℕ) : ZMod r)) := by
      push_cast
      exact hpunit.mul (hqunit.pow 2)
    have hcast : ((cubicCRTLocalBase d 1 r p : ℕ) : ZMod r) =
        ((p * q ^ 2 : ℕ) : ZMod r) := by
      rw [cast_cubicCRTLocalBase_one, ← hqp]
      simp
    refine ⟨r, hr, ?_⟩
    intro hcube
    have hproduct : IsCubeMod r ((p ^ 2 * q) * q ^ 3) :=
      isCubeMod_mul hcube (isCubeMod_cube r q)
    have hsquare : IsCubeMod r ((p * q ^ 2) ^ 2) :=
      isCubeMod_of_cast_eq (by push_cast; ring) hproduct
    have hone := isCubeMod_of_square_isCubeMod
      hpq2unit hsquare
    exact hnot (isCubeMod_of_cast_eq hcast.symm hone)
  intro i hi j hj hnonzero
  interval_cases i <;> interval_cases j
  · simp_all
  · simpa using hqOne
  · simpa using hqTwo
  · simpa using hpOne
  · simpa using hpqOneOne
  · simpa using hpqOneTwo
  · simpa using hpTwo
  · simpa using hpqTwoOne
  · simpa using hpqTwoTwo

/-- The batched prime cover bounds the gap; periodic character-set certificates
exclude the four nonzero cubic-character directions. -/
theorem largeCubicCertificate : LargeCubicCertificate := by
  intro p q hp433 hp hqfirst hq36
  have hpq : p < q := hqfirst.1
  have hq : q.Prime := hqfirst.2.1
  let d := q - p
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hdle : d ≤ 210 := by
    exact PrimeGapBatch210Certificate.prime_gap_le_210_below_36000000
      hp433 hp hqfirst hq36
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  obtain ⟨u, hu⟩ := hpodd
  obtain ⟨v, hv⟩ := hqodd
  have hdeven : d % 2 = 0 := by
    dsimp [d]
    omega
  have hqp : q = p + d := by
    dsimp [d]
    omega
  obtain ⟨hzero, hone⟩ := PeriodicSieveCertificate.gap_obstructions hdpos hdle hdeven
  exact cubicSieveHolds_of_periodic_obstructions hp433 hpq hq36 hp hq hqp
    hzero hone PeriodicSieveCertificate.periodic_0_2

/-- The purely algebraic conclusion of the finite cubic sieve. -/
lemma mod_three_eq_zero_of_cubicSieveHolds
    {p q a b : ℕ} (hsieve : CubicSieveHolds p q)
    (hcube : ∀ r ∈ cubicModuli,
      IsCubeMod r (p ^ (a % 3) * q ^ (b % 3))) :
    a % 3 = 0 ∧ b % 3 = 0 := by
  have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_contra hne
  have hpair : a % 3 ≠ 0 ∨ b % 3 ≠ 0 := by omega
  obtain ⟨r, hr, hnot⟩ := hsieve (a % 3) ha (b % 3) hb hpair
  exact hnot (hcube r hr)

/-- Above `433`, the factorial equation makes every residual exponent pair a
cube at every modulus in `cubicModuli`. -/
lemma residual_cubes_at_cubicModuli
    {n p q a b : ℕ} (hn : 433 < n) (hp : p.Prime) (hnp : n < p)
    (hq : q.Prime) (hnq : n < q)
    (heq : n.factorial + 1 = p ^ a * q ^ b) :
    ∀ r ∈ cubicModuli, IsCubeMod r (p ^ (a % 3) * q ^ (b % 3)) := by
  intro r hr
  exact residual_isCubeMod_of_factorial_add_one_eq (prime_of_mem_cubicModuli hr)
    (by have := le_433_of_mem_cubicModuli hr; omega)
    hp (by have := le_433_of_mem_cubicModuli hr; omega)
    hq (by have := le_433_of_mem_cubicModuli hr; omega) heq

lemma factorial_eq_cube_sub_one_of_mod_three
    {n p q a b : ℕ} (heq : n.factorial + 1 = p ^ a * q ^ b)
    (ha : a % 3 = 0) (hb : b % 3 = 0) :
    n.factorial = (p ^ (a / 3) * q ^ (b / 3)) ^ 3 - 1 := by
  have hpa := pow_eq_cube_mul_pow_mod_three p a
  have hqb := pow_eq_cube_mul_pow_mod_three q b
  simp only [ha, hb, pow_zero, mul_one] at hpa hqb
  have hcube : n.factorial + 1 = (p ^ (a / 3) * q ^ (b / 3)) ^ 3 := by
    rw [heq, hpa, hqb, mul_pow]
  omega

/-- Combining the modular reduction with a checked instance of the finite
sieve turns the original equation into the special Erdős--Obláth equation. -/
lemma exists_cube_sub_one_of_cubicSieve
    {n p q a b : ℕ} (hn : 433 < n) (hp : p.Prime) (hnp : n < p)
    (hq : q.Prime) (hnq : n < q)
    (heq : n.factorial + 1 = p ^ a * q ^ b)
    (hsieve : CubicSieveHolds p q) :
    ∃ x, n.factorial = x ^ 3 - 1 := by
  have hresidual := residual_cubes_at_cubicModuli hn hp hnp hq hnq heq
  obtain ⟨ha, hb⟩ := mod_three_eq_zero_of_cubicSieveHolds hsieve hresidual
  exact ⟨p ^ (a / 3) * q ^ (b / 3),
    factorial_eq_cube_sub_one_of_mod_three heq ha hb⟩

/-! ## The Erdős--Obláth cubic equation

For the special equation `n! = x³ - 1`, the second factor is the third
cyclotomic polynomial.  Its prime divisors, apart from `3`, lie in the
progression `1 mod 3`.  This is the algebraic starting point of the
Erdős--Obláth estimate used by Luca. -/

/-- Every prime divisor of the third cyclotomic value `x²+x+1` is either
`3` or congruent to `1` modulo `3`. -/
lemma prime_eq_three_or_modEq_one_of_dvd_sq_add_self_add_one
    {r x : ℕ} (hr : r.Prime) (hdiv : r ∣ x ^ 2 + x + 1) :
    r = 3 ∨ r ≡ 1 [MOD 3] := by
  by_cases hr3 : r = 3
  · exact Or.inl hr3
  right
  letI : Fact r.Prime := ⟨hr⟩
  have hz : ((x ^ 2 + x + 1 : ℕ) : ZMod r) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdiv
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic 3 (ZMod r)) (x : ZMod r) := by
    simpa [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] using hz
  have hx0 : (x : ZMod r) ≠ 0 := by
    intro hx
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_three] at hroot
    simp [hx] at hroot
  have h3nz : NeZero (3 : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) (by
      intro h
      exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h))
  have hord : 3 = orderOf (x : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  have hdvd : orderOf (x : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hx0
  rw [← hord] at hdvd
  exact ((Nat.modEq_iff_dvd' hr.pos).2 hdvd).symm

/-- The third cyclotomic value is never divisible by `3²`. -/
lemma nine_not_dvd_sq_add_self_add_one (x : ℕ) :
    ¬9 ∣ x ^ 2 + x + 1 := by
  intro hdiv
  have hz : ((x ^ 2 + x + 1 : ℕ) : ZMod 9) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdiv
  have hall : ∀ y : ZMod 9, y ^ 2 + y + 1 ≠ 0 := by decide
  exact hall (x : ZMod 9) (by simpa using hz)

lemma factorization_three_sq_add_self_add_one_le_one (x : ℕ) :
    (x ^ 2 + x + 1).factorization 3 ≤ 1 := by
  have hne : x ^ 2 + x + 1 ≠ 0 := by omega
  by_contra h
  have htwo : 2 ≤ (x ^ 2 + x + 1).factorization 3 := by omega
  have hdvd : 3 ^ 2 ∣ x ^ 2 + x + 1 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hne).2 htwo
  exact nine_not_dvd_sq_add_self_add_one x (by simpa using hdvd)

/-- The part of `n!` supported on primes congruent to `1` modulo `a`. -/
def factorialAPPart (n a : ℕ) : ℕ :=
  (n.factorial.factorization.filter fun r ↦ r % a = 1).prod (fun r e ↦ r ^ e)

/-- Product of the prime powers at most `x`, restricted to `1 mod a`.  This
is the arithmetic function denoted `Ψ(x,a)` in the Erdős--Obláth proof. -/
def APPrimePowerProduct (x a : ℕ) : ℕ :=
  ((Nat.lcmUpto x).factorization.filter fun r ↦ r % a = 1).prod
    (fun r e ↦ r ^ e)

lemma APPrimePowerProduct_factorization (x a : ℕ) :
    (APPrimePowerProduct x a).factorization =
      (Nat.lcmUpto x).factorization.filter fun r ↦ r % a = 1 := by
  unfold APPrimePowerProduct
  apply Nat.factorization_prod_pow_eq_self_of_le_factorization (n := Nat.lcmUpto x)
  intro r
  simp only [Finsupp.filter_apply]
  split <;> omega

lemma APPrimePowerProduct_factorization_apply_of_prime
    (x a : ℕ) {r : ℕ} (hr : r.Prime) :
    (APPrimePowerProduct x a).factorization r =
      if r % a = 1 then r.log x else 0 := by
  rw [APPrimePowerProduct_factorization, Finsupp.filter_apply]
  split
  · exact Nat.factorization_lcmUpto x hr
  · rfl

lemma log_div_eq_card_filter_pow_le {p n s : ℕ} (hp : 1 < p)
    (hs : s ∈ Finset.Icc 1 n) :
    p.log (n / s) =
      Finset.card {i ∈ Finset.Ico 1 (p.log n + 1) | p ^ i ≤ n / s} := by
  have hs' := Finset.mem_Icc.mp hs
  have hdivpos : 0 < n / s := Nat.div_pos hs'.2 (by omega)
  have hcard : (Finset.Ico 1 (p.log (n / s) + 1)).card = p.log (n / s) := by
    simp
  rw [← hcard]
  congr 1
  ext i
  simp only [Finset.mem_Ico, Finset.mem_filter]
  constructor
  · intro hi
    have hi_le : i ≤ p.log (n / s) := by omega
    have hpow : p ^ i ≤ n / s := Nat.pow_le_of_le_log hdivpos.ne' hi_le
    have hlogmono : p.log (n / s) ≤ p.log n :=
      Nat.log_mono_right (Nat.div_le_self n s)
    exact ⟨⟨hi.1, by omega⟩, hpow⟩
  · rintro ⟨hi, hpow⟩
    have hilog : i ≤ p.log (n / s) := Nat.le_log_of_pow_le hp hpow
    exact ⟨hi.1, by omega⟩

lemma sum_log_div_eq_sum_div_pow {p n : ℕ} (hp : 1 < p) :
    ∑ s ∈ Finset.Icc 1 n, p.log (n / s) =
      ∑ i ∈ Finset.Ico 1 (p.log n + 1), n / p ^ i := by
  let S := Finset.Icc 1 n
  let I := Finset.Ico 1 (p.log n + 1)
  have hfiber (i : ℕ) :
      {s ∈ S | p ^ i ≤ n / s} = Finset.Icc 1 (n / p ^ i) := by
    ext s
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hs1, hsn⟩, hpred⟩
      refine ⟨hs1, ?_⟩
      rw [Nat.le_div_iff_mul_le (pow_pos (by omega) i)]
      rw [Nat.le_div_iff_mul_le (by omega)] at hpred
      simpa [mul_comm] using hpred
    · rintro ⟨hs1, hsbound⟩
      have hsn : s ≤ n := hsbound.trans (Nat.div_le_self n (p ^ i))
      refine ⟨⟨hs1, hsn⟩, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.le_div_iff_mul_le (pow_pos (by omega) i)] at hsbound
      simpa [mul_comm] using hsbound
  calc
    ∑ s ∈ S, p.log (n / s) =
        ∑ s ∈ S, Finset.card {i ∈ I | p ^ i ≤ n / s} := by
          apply Finset.sum_congr rfl
          intro s hs
          exact log_div_eq_card_filter_pow_le hp hs
    _ = ∑ s ∈ S, ∑ i ∈ I, if p ^ i ≤ n / s then 1 else 0 := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ I, ∑ s ∈ S, if p ^ i ≤ n / s then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ I, Finset.card {s ∈ S | p ^ i ≤ n / s} := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ I, n / p ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hfiber]
          simp

lemma sum_log_div_eq_factorization_factorial {r n : ℕ} (hr : r.Prime) :
    ∑ s ∈ Finset.Icc 1 n, r.log (n / s) = n.factorial.factorization r := by
  rw [sum_log_div_eq_sum_div_pow hr.one_lt]
  exact (Nat.factorization_factorial hr (Nat.lt_succ_self _)).symm

lemma APPrimePowerProduct_ne_zero (x a : ℕ) :
    APPrimePowerProduct x a ≠ 0 := by
  unfold APPrimePowerProduct
  rw [Finsupp.prod_ne_zero_iff]
  intro r hr
  apply pow_ne_zero
  have hr' : r ∈ (Nat.lcmUpto x).factorization.support := by
    rw [Finsupp.support_filter, Finset.mem_filter] at hr
    exact hr.1
  rw [Nat.support_factorization] at hr'
  exact (Nat.mem_primeFactors.mp hr').1.ne_zero

lemma exists_progression_residue (d : ℕ) (hd : 1 < d)
    (hcop : Nat.Coprime 6 d) :
    ∃ c : ℕ, 1 ≤ c ∧ c < d ∧ d ∣ 6 * c + 1 := by
  letI : NeZero d := ⟨by omega⟩
  let c := (-(6 : ZMod d)⁻¹).val
  have hclt : c < d := ZMod.val_lt _
  have hmul : (6 : ZMod d) * (c : ZMod d) + 1 = 0 := by
    have hi : (6 : ZMod d) * (6 : ZMod d)⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one 6 hcop
    rw [show (c : ZMod d) = -(6 : ZMod d)⁻¹ by
      exact ZMod.natCast_zmod_val _]
    rw [mul_neg, hi]
    simp
  have hcpos : 1 ≤ c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    rw [hc0] at hmul
    have hval := congrArg ZMod.val (show (1 : ZMod d) = 0 by simpa using hmul)
    simpa [ZMod.val_one'' (by omega : d ≠ 1)] using hval
  refine ⟨c, hcpos, hclt, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simpa [Nat.cast_add, Nat.cast_mul] using hmul

lemma div_le_card_progression_dvd (m d : ℕ) (hd : 1 < d)
    (hcop : Nat.Coprime 6 d) :
    m / d ≤ Finset.card {j ∈ Finset.Icc 1 m | d ∣ 6 * j + 1} := by
  obtain ⟨c, hc1, hcd, hcdiv⟩ := exists_progression_residue d hd hcop
  let T : Finset ℕ := {j ∈ Finset.Icc 1 m | d ∣ 6 * j + 1}
  have hdm : d * (m / d) ≤ m := Nat.mul_div_le m d
  have hmaps : Set.MapsTo (fun t ↦ d * t + c) (Finset.range (m / d))
      (T : Set ℕ) := by
    intro t ht
    have htlt : t < m / d := Finset.mem_range.mp ht
    have hjle : d * t + c ≤ m := by
      have : d * t + c < d * (m / d) := by
        calc
          d * t + c < d * t + d := Nat.add_lt_add_left hcd _
          _ = d * (t + 1) := by simp [mul_add]
          _ ≤ d * (m / d) := Nat.mul_le_mul_left d (by omega)
      exact this.le.trans hdm
    have hj1 : 1 ≤ d * t + c := hc1.trans (Nat.le_add_left c (d * t))
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hjle⟩, ?_⟩
    obtain ⟨z, hz⟩ := hcdiv
    refine ⟨6 * t + z, ?_⟩
    calc
      6 * (d * t + c) + 1 = d * (6 * t) + (6 * c + 1) := by ring
      _ = d * (6 * t) + d * z := by rw [hz]
      _ = d * (6 * t + z) := by ring
  have hinj : Set.InjOn (fun t ↦ d * t + c) (Finset.range (m / d)) := by
    intro x _ y _ hxy
    have hmul : d * x = d * y := Nat.add_right_cancel hxy
    exact Nat.mul_left_cancel (by omega) hmul
  have hcard := Finset.card_le_card_of_injOn (fun t ↦ d * t + c) hmaps hinj
  simpa [T] using hcard

def progressionProduct (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 m, (6 * j + 1)

lemma progressionProduct_ne_zero (m : ℕ) : progressionProduct m ≠ 0 := by
  unfold progressionProduct
  positivity

lemma coprime_six_of_prime_ne_two_ne_three {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) : Nat.Coprime 6 r := by
  rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
  intro hdiv
  have hdiv' : r ∣ 2 * 3 := by norm_num at hdiv ⊢; exact hdiv
  rcases (hr.dvd_mul).mp hdiv' with h2 | h3
  · exact hr2 ((Nat.dvd_prime_two_le Nat.prime_two hr.two_le).mp h2)
  · exact hr3 ((Nat.dvd_prime_two_le Nat.prime_three hr.two_le).mp h3)

lemma factorization_factorial_le_progressionProduct {m r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    m.factorial.factorization r ≤ (progressionProduct m).factorization r := by
  let b := 6 * m + 2
  have hbpos : 0 < b := by simp [b]
  have hlog : r.log m < b := by
    by_cases hm : m = 0
    · simp [hm, b]
    · exact (Nat.log_lt_self r hm).trans (by omega)
  have hcop : Nat.Coprime 6 r := coprime_six_of_prime_ne_two_ne_three hr hr2 hr3
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
      (6 * j + 1).factorization r =
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
    apply Nat.factorization_eq_card_pow_dvd_of_lt hr (by omega)
    have hjle : 6 * j + 1 < b := by
      simp only [Finset.mem_Icc] at hj
      simp [b]
      omega
    calc
      6 * j + 1 < b := hjle
      _ < 2 ^ b := Nat.lt_two_pow_self
      _ ≤ r ^ b := Nat.pow_le_pow_left hr.two_le _
  rw [progressionProduct, Nat.factorization_prod_apply (fun j hj ↦ by omega)]
  calc
    m.factorial.factorization r = ∑ i ∈ Finset.Ico 1 b, m / r ^ i :=
      Nat.factorization_factorial hr hlog
    _ ≤ ∑ i ∈ Finset.Ico 1 b,
        Finset.card {j ∈ Finset.Icc 1 m | r ^ i ∣ 6 * j + 1} := by
      apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
      exact div_le_card_progression_dvd m (r ^ i)
        (one_lt_pow₀ hr.one_lt (by omega)) (Nat.Coprime.pow_right i hcop)
    _ = ∑ j ∈ Finset.Icc 1 m,
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 m, (6 * j + 1).factorization r := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).symm

def progressionCorrection (m : ℕ) : ℕ :=
  2 ^ m.factorial.factorization 2 * 3 ^ m.factorial.factorization 3

lemma progressionCorrection_ne_zero (m : ℕ) : progressionCorrection m ≠ 0 := by
  unfold progressionCorrection
  positivity

lemma factorial_dvd_progressionProduct_mul_correction (m : ℕ) :
    m.factorial ∣ progressionProduct m * progressionCorrection m := by
  have hright : progressionProduct m * progressionCorrection m ≠ 0 :=
    mul_ne_zero (progressionProduct_ne_zero m) (progressionCorrection_ne_zero m)
  apply (Nat.factorization_le_iff_dvd m.factorial_ne_zero hright).1
  intro r
  rw [Nat.factorization_mul (progressionProduct_ne_zero m)
    (progressionCorrection_ne_zero m), Finsupp.add_apply]
  by_cases hr : r.Prime
  · rcases eq_or_ne r 2 with rfl | hr2
    · unfold progressionCorrection
      rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
        Nat.factorization_pow, Nat.factorization_pow]
      norm_num [Nat.Prime.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd]
    · rcases eq_or_ne r 3 with rfl | hr3
      · unfold progressionCorrection
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
          Nat.factorization_pow, Nat.factorization_pow]
        norm_num [Nat.Prime.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd]
      · exact (factorization_factorial_le_progressionProduct hr hr2 hr3).trans
          (Nat.le_add_right _ _)
  · have hz : m.factorial.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hz]

def progressionQuotient (m : ℕ) : ℕ :=
  progressionProduct m * progressionCorrection m / m.factorial

lemma progressionQuotient_mul_factorial (m : ℕ) :
    progressionQuotient m * m.factorial =
      progressionProduct m * progressionCorrection m := by
  unfold progressionQuotient
  exact Nat.div_mul_cancel (factorial_dvd_progressionProduct_mul_correction m)

lemma progressionProduct_le_seven_pow_mul_factorial (m : ℕ) :
    progressionProduct m ≤ 7 ^ m * m.factorial := by
  induction m with
  | zero => simp [progressionProduct]
  | succ m ih =>
      rw [progressionProduct, Finset.prod_Icc_succ_top (by omega)]
      change progressionProduct m * (6 * (m + 1) + 1) ≤
        7 ^ (m + 1) * (m + 1).factorial
      calc
        progressionProduct m * (6 * (m + 1) + 1) ≤
            (7 ^ m * m.factorial) * (7 * (m + 1)) :=
          Nat.mul_le_mul ih (by omega)
        _ = 7 ^ (m + 1) * (m + 1).factorial := by
          rw [pow_succ, Nat.factorial_succ]
          ring

lemma pow_sq_comm (a m : ℕ) : (a ^ m) ^ 2 = (a ^ 2) ^ m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

lemma progressionCorrection_sq_le (m : ℕ) :
    progressionCorrection m ^ 2 ≤ 12 ^ m := by
  let e2 := m.factorial.factorization 2
  let e3 := m.factorial.factorization 3
  have he2 : e2 ≤ m := by
    simpa [e2] using Nat.factorization_factorial_le_div_pred Nat.prime_two m
  have he3div : e3 ≤ m / 2 := by
    simpa [e3] using Nat.factorization_factorial_le_div_pred Nat.prime_three m
  have he3 : 2 * e3 ≤ m := by
    exact (Nat.mul_le_mul_left 2 he3div).trans (Nat.mul_div_le m 2)
  have h2 : 4 ^ e2 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) he2
  have h3 : 9 ^ e3 ≤ 3 ^ m := by
    rw [show 9 = 3 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) he3
  unfold progressionCorrection
  change (2 ^ e2 * 3 ^ e3) ^ 2 ≤ 12 ^ m
  calc
    (2 ^ e2 * 3 ^ e3) ^ 2 = 4 ^ e2 * 9 ^ e3 := by
      rw [mul_pow, pow_sq_comm, pow_sq_comm]
      norm_num
    _ ≤ 4 ^ m * 3 ^ m := Nat.mul_le_mul h2 h3
    _ = 12 ^ m := by rw [← mul_pow]; norm_num

lemma seven_pow_mul_progressionCorrection_le (m : ℕ) :
    7 ^ m * progressionCorrection m ≤ 25 ^ m := by
  have hs : (7 ^ m * progressionCorrection m) ^ 2 ≤ (25 ^ m) ^ 2 := by
    calc
      (7 ^ m * progressionCorrection m) ^ 2 =
          49 ^ m * progressionCorrection m ^ 2 := by
        rw [mul_pow, pow_sq_comm]
        norm_num
      _ ≤ 49 ^ m * 12 ^ m :=
        Nat.mul_le_mul_left _ (progressionCorrection_sq_le m)
      _ = 588 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ 625 ^ m := Nat.pow_le_pow_left (by norm_num) _
      _ = (25 ^ m) ^ 2 := by rw [pow_sq_comm]; norm_num
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hs

lemma progressionQuotient_le_twentyfive_pow (m : ℕ) :
    progressionQuotient m ≤ 25 ^ m := by
  apply Nat.le_of_mul_le_mul_right _ m.factorial_pos
  rw [progressionQuotient_mul_factorial]
  calc
    progressionProduct m * progressionCorrection m ≤
        (7 ^ m * m.factorial) * progressionCorrection m :=
      Nat.mul_le_mul_right _ (progressionProduct_le_seven_pow_mul_factorial m)
    _ = (7 ^ m * progressionCorrection m) * m.factorial := by ring
    _ ≤ 25 ^ m * m.factorial :=
      Nat.mul_le_mul_right _ (seven_pow_mul_progressionCorrection_le m)

lemma one_le_card_progression_dvd_of_mod_six (m d : ℕ)
    (hdone : 1 < d) (hdmod : d % 6 = 1) (hdgt : m < d)
    (hdle : d ≤ 6 * m + 1) :
    1 ≤ Finset.card {j ∈ Finset.Icc 1 m | d ∣ 6 * j + 1} := by
  let c := d / 6
  have hdc : 6 * c + 1 = d := by
    have h := Nat.mod_add_div d 6
    simp only [hdmod] at h
    omega
  have hc1 : 1 ≤ c := by
    by_contra h
    have hc0 : c = 0 := by omega
    rw [hc0] at hdc
    omega
  have hcm : c ≤ m := by omega
  apply Finset.card_pos.mpr
  refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hc1, hcm⟩, ?_⟩⟩
  exact ⟨1, by simpa [hdc]⟩

lemma prime_power_mod_six_eq_one {r i : ℕ} (hmod : r % 6 = 1) :
    r ^ i % 6 = 1 := by
  rw [Nat.pow_mod]
  simp [hmod]

lemma factorization_factorial_add_log_sub_le_progressionProduct
    {m r : ℕ} (hr : r.Prime) (hmod : r % 6 = 1) :
    m.factorial.factorization r + (r.log (6 * m + 1) - r.log m) ≤
      (progressionProduct m).factorization r := by
  let b := 6 * m + 2
  have hhighpos : 0 < 6 * m + 1 := by omega
  have hlogm_le : r.log m ≤ r.log (6 * m + 1) :=
    Nat.log_mono_right (by omega)
  have hlogfac : r.log m < b := by
    by_cases hm : m = 0
    · simp [hm, b]
    · exact (Nat.log_lt_self r hm).trans (by omega)
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
      (6 * j + 1).factorization r =
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
    apply Nat.factorization_eq_card_pow_dvd_of_lt hr (by omega)
    have hjle : 6 * j + 1 < b := by
      simp only [Finset.mem_Icc] at hj
      simp [b]
      omega
    calc
      6 * j + 1 < b := hjle
      _ < 2 ^ b := Nat.lt_two_pow_self
      _ ≤ r ^ b := Nat.pow_le_pow_left hr.two_le _
  have hextra :
      Finset.card {i ∈ Finset.Ico 1 b |
          m < r ^ i ∧ r ^ i ≤ 6 * m + 1} =
        r.log (6 * m + 1) - r.log m := by
    have hset : {i ∈ Finset.Ico 1 b | m < r ^ i ∧ r ^ i ≤ 6 * m + 1} =
        Finset.Ico (r.log m + 1) (r.log (6 * m + 1) + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hi1, hib⟩, hmri, hri⟩
        have hlow : r.log m < i := by
          by_cases hm : m = 0
          · simp [hm]
            omega
          · exact (Nat.log_lt_iff_lt_pow hr.one_lt hm).2 hmri
        have hupper : i ≤ r.log (6 * m + 1) :=
          (Nat.le_log_iff_pow_le hr.one_lt hhighpos.ne').2 hri
        omega
      · rintro ⟨hlow, hupper⟩
        have hmri : m < r ^ i := by
          by_cases hm : m = 0
          · subst m
            exact pow_pos hr.pos _
          · exact (Nat.log_lt_iff_lt_pow hr.one_lt hm).1 (by omega)
        have hri : r ^ i ≤ 6 * m + 1 :=
          (Nat.le_log_iff_pow_le hr.one_lt hhighpos.ne').1 (by omega)
        have hi_le : i ≤ r.log (6 * m + 1) := by omega
        have hib : i < b := hi_le.trans_lt
          ((Nat.log_lt_self r hhighpos.ne').trans (by simp [b]))
        exact ⟨⟨by omega, hib⟩, hmri, hri⟩
    rw [hset]
    simp [hlogm_le]
  rw [progressionProduct, Nat.factorization_prod_apply (fun j hj ↦ by omega)]
  calc
    m.factorial.factorization r + (r.log (6 * m + 1) - r.log m) =
        (∑ i ∈ Finset.Ico 1 b, m / r ^ i) +
          Finset.card {i ∈ Finset.Ico 1 b |
            m < r ^ i ∧ r ^ i ≤ 6 * m + 1} := by
      rw [Nat.factorization_factorial hr hlogfac, hextra]
    _ = ∑ i ∈ Finset.Ico 1 b,
        (m / r ^ i + if m < r ^ i ∧ r ^ i ≤ 6 * m + 1 then 1 else 0) := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.Ico 1 b,
        Finset.card {j ∈ Finset.Icc 1 m | r ^ i ∣ 6 * j + 1} := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hinterval : m < r ^ i ∧ r ^ i ≤ 6 * m + 1
      · simp only [if_pos hinterval]
        have hdivzero : m / r ^ i = 0 := Nat.div_eq_of_lt hinterval.1
        rw [hdivzero, zero_add]
        exact one_le_card_progression_dvd_of_mod_six m (r ^ i)
          (one_lt_pow₀ hr.one_lt (by
            have := (Finset.mem_Ico.mp hi).1
            omega))
          (prime_power_mod_six_eq_one hmod) hinterval.1 hinterval.2
      · simp only [if_neg hinterval, add_zero]
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        exact div_le_card_progression_dvd m (r ^ i)
          (one_lt_pow₀ hr.one_lt (by omega))
          (Nat.Coprime.pow_right i
            (coprime_six_of_prime_ne_two_ne_three hr (by omega) (by omega)))
    _ = ∑ j ∈ Finset.Icc 1 m,
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 m, (6 * j + 1).factorization r := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).symm

lemma progressionQuotient_ne_zero (m : ℕ) : progressionQuotient m ≠ 0 := by
  intro hzero
  have heq := progressionQuotient_mul_factorial m
  rw [hzero, zero_mul] at heq
  exact (mul_ne_zero (progressionProduct_ne_zero m)
    (progressionCorrection_ne_zero m)) heq.symm

lemma progressionCorrection_factorization_eq_zero_of_mod_six
    {m r : ℕ} (hr : r.Prime) (hmod : r % 6 = 1) :
    (progressionCorrection m).factorization r = 0 := by
  have hr2 : r ≠ 2 := by
    intro h
    subst r
    norm_num at hmod
  have hr3 : r ≠ 3 := by
    intro h
    subst r
    norm_num at hmod
  have hrd2 : ¬r ∣ 2 := by
    intro hd
    exact hr2 ((Nat.dvd_prime_two_le Nat.prime_two hr.two_le).mp hd)
  have hrd3 : ¬r ∣ 3 := by
    intro hd
    exact hr3 ((Nat.dvd_prime_two_le Nat.prime_three hr.two_le).mp hd)
  unfold progressionCorrection
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  rcases (hr.dvd_mul).mp hd with h2 | h3
  · exact hrd2 (hr.dvd_of_dvd_pow h2)
  · exact hrd3 (hr.dvd_of_dvd_pow h3)

lemma APPrimePowerProduct_progression_step_dvd (m : ℕ) :
    APPrimePowerProduct (6 * m + 1) 6 ∣
      APPrimePowerProduct m 6 * progressionQuotient m := by
  have hleft := APPrimePowerProduct_ne_zero (6 * m + 1) 6
  have hright : APPrimePowerProduct m 6 * progressionQuotient m ≠ 0 :=
    mul_ne_zero (APPrimePowerProduct_ne_zero m 6) (progressionQuotient_ne_zero m)
  apply (Nat.factorization_le_iff_dvd hleft hright).1
  intro r
  rw [Nat.factorization_mul (APPrimePowerProduct_ne_zero m 6)
    (progressionQuotient_ne_zero m), Finsupp.add_apply]
  by_cases hr : r.Prime
  · rw [APPrimePowerProduct_factorization_apply_of_prime _ _ hr,
      APPrimePowerProduct_factorization_apply_of_prime _ _ hr]
    by_cases hmod : r % 6 = 1
    · simp only [if_pos hmod]
      have hqfac :
          (progressionQuotient m).factorization r + m.factorial.factorization r =
            (progressionProduct m).factorization r +
              (progressionCorrection m).factorization r := by
        calc
          (progressionQuotient m).factorization r + m.factorial.factorization r =
              (progressionQuotient m * m.factorial).factorization r := by
            rw [Nat.factorization_mul (progressionQuotient_ne_zero m)
              m.factorial_ne_zero, Finsupp.add_apply]
          _ = (progressionProduct m * progressionCorrection m).factorization r := by
            rw [progressionQuotient_mul_factorial]
          _ = (progressionProduct m).factorization r +
                (progressionCorrection m).factorization r := by
            rw [Nat.factorization_mul (progressionProduct_ne_zero m)
              (progressionCorrection_ne_zero m), Finsupp.add_apply]
      rw [progressionCorrection_factorization_eq_zero_of_mod_six hr hmod,
        add_zero] at hqfac
      have hprog :=
        factorization_factorial_add_log_sub_le_progressionProduct (m := m) hr hmod
      have hlogle : r.log m ≤ r.log (6 * m + 1) := Nat.log_mono_right (by omega)
      omega
    · simp [hmod]
  · have hzleft : (APPrimePowerProduct (6 * m + 1) 6).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hzleft]

/-! A shifted progression gives the sharp constant used below.  Its first
term is `1`, which saves one full factor in the exponential estimate. -/

def shiftedProgressionProduct (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.range m, (6 * j + 1)

lemma shiftedProgressionProduct_ne_zero (m : ℕ) :
    shiftedProgressionProduct m ≠ 0 := by
  unfold shiftedProgressionProduct
  positivity

lemma div_le_card_shifted_progression_dvd (m d : ℕ) (hd : 1 < d)
    (hcop : Nat.Coprime 6 d) :
    m / d ≤ Finset.card {j ∈ Finset.range m | d ∣ 6 * j + 1} := by
  obtain ⟨c, hc1, hcd, hcdiv⟩ := exists_progression_residue d hd hcop
  let T : Finset ℕ := {j ∈ Finset.range m | d ∣ 6 * j + 1}
  have hdm : d * (m / d) ≤ m := Nat.mul_div_le m d
  have hmaps : Set.MapsTo (fun t ↦ d * t + c) (Finset.range (m / d))
      (T : Set ℕ) := by
    intro t ht
    have htlt : t < m / d := Finset.mem_range.mp ht
    have hjlt : d * t + c < m := by
      calc
        d * t + c < d * t + d := Nat.add_lt_add_left hcd _
        _ = d * (t + 1) := by simp [mul_add]
        _ ≤ d * (m / d) := Nat.mul_le_mul_left d (by omega)
        _ ≤ m := hdm
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, ?_⟩
    obtain ⟨z, hz⟩ := hcdiv
    refine ⟨6 * t + z, ?_⟩
    calc
      6 * (d * t + c) + 1 = d * (6 * t) + (6 * c + 1) := by ring
      _ = d * (6 * t) + d * z := by rw [hz]
      _ = d * (6 * t + z) := by ring
  have hinj : Set.InjOn (fun t ↦ d * t + c) (Finset.range (m / d)) := by
    intro x _ y _ hxy
    have hmul : d * x = d * y := Nat.add_right_cancel hxy
    exact Nat.mul_left_cancel (by omega) hmul
  have hcard := Finset.card_le_card_of_injOn (fun t ↦ d * t + c) hmaps hinj
  simpa [T] using hcard

lemma one_le_card_shifted_progression_dvd_of_mod_six (m d : ℕ)
    (hm : 1 ≤ m) (hdone : 1 < d) (hdmod : d % 6 = 1)
    (hdle : d ≤ 6 * m - 5) :
    1 ≤ Finset.card {j ∈ Finset.range m | d ∣ 6 * j + 1} := by
  let c := d / 6
  have hdc : 6 * c + 1 = d := by
    have h := Nat.mod_add_div d 6
    simp only [hdmod] at h
    omega
  have hclt : c < m := by omega
  apply Finset.card_pos.mpr
  refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hclt, ?_⟩⟩
  exact ⟨1, by simpa [hdc]⟩

def shiftedProgressionCorrection (m : ℕ) : ℕ :=
  progressionCorrection m

def shiftedProgressionQuotient (m : ℕ) : ℕ :=
  shiftedProgressionProduct m * shiftedProgressionCorrection m / m.factorial

lemma shiftedProgressionCorrection_ne_zero (m : ℕ) :
    shiftedProgressionCorrection m ≠ 0 := progressionCorrection_ne_zero m

lemma factorization_factorial_le_shiftedProgressionProduct {m r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    m.factorial.factorization r ≤ (shiftedProgressionProduct m).factorization r := by
  let b := 6 * m + 2
  have hlog : r.log m < b := by
    by_cases hm : m = 0
    · simp [hm, b]
    · exact (Nat.log_lt_self r hm).trans (by omega)
  have hcop : Nat.Coprime 6 r := coprime_six_of_prime_ne_two_ne_three hr hr2 hr3
  have hterm (j : ℕ) (hj : j ∈ Finset.range m) :
      (6 * j + 1).factorization r =
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
    apply Nat.factorization_eq_card_pow_dvd_of_lt hr (by omega)
    have hjle : 6 * j + 1 < b := by
      have := Finset.mem_range.mp hj
      simp [b]
      omega
    calc
      6 * j + 1 < b := hjle
      _ < 2 ^ b := Nat.lt_two_pow_self
      _ ≤ r ^ b := Nat.pow_le_pow_left hr.two_le _
  rw [shiftedProgressionProduct,
    Nat.factorization_prod_apply (fun j hj ↦ by omega)]
  calc
    m.factorial.factorization r = ∑ i ∈ Finset.Ico 1 b, m / r ^ i :=
      Nat.factorization_factorial hr hlog
    _ ≤ ∑ i ∈ Finset.Ico 1 b,
        Finset.card {j ∈ Finset.range m | r ^ i ∣ 6 * j + 1} := by
      apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
      exact div_le_card_shifted_progression_dvd m (r ^ i)
        (one_lt_pow₀ hr.one_lt (by omega)) (Nat.Coprime.pow_right i hcop)
    _ = ∑ j ∈ Finset.range m,
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range m, (6 * j + 1).factorization r := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).symm

lemma factorial_dvd_shiftedProgressionProduct_mul_correction (m : ℕ) :
    m.factorial ∣ shiftedProgressionProduct m * shiftedProgressionCorrection m := by
  have hright : shiftedProgressionProduct m * shiftedProgressionCorrection m ≠ 0 :=
    mul_ne_zero (shiftedProgressionProduct_ne_zero m)
      (shiftedProgressionCorrection_ne_zero m)
  apply (Nat.factorization_le_iff_dvd m.factorial_ne_zero hright).1
  intro r
  rw [Nat.factorization_mul (shiftedProgressionProduct_ne_zero m)
    (shiftedProgressionCorrection_ne_zero m), Finsupp.add_apply]
  by_cases hr : r.Prime
  · rcases eq_or_ne r 2 with rfl | hr2
    · unfold shiftedProgressionCorrection progressionCorrection
      rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
        Nat.factorization_pow, Nat.factorization_pow]
      norm_num [Nat.Prime.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd]
    · rcases eq_or_ne r 3 with rfl | hr3
      · unfold shiftedProgressionCorrection progressionCorrection
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
          Nat.factorization_pow, Nat.factorization_pow]
        norm_num [Nat.Prime.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd]
      · exact (factorization_factorial_le_shiftedProgressionProduct hr hr2 hr3).trans
          (Nat.le_add_right _ _)
  · have hz : m.factorial.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hz]

lemma shiftedProgressionQuotient_mul_factorial (m : ℕ) :
    shiftedProgressionQuotient m * m.factorial =
      shiftedProgressionProduct m * shiftedProgressionCorrection m := by
  unfold shiftedProgressionQuotient
  exact Nat.div_mul_cancel (factorial_dvd_shiftedProgressionProduct_mul_correction m)

lemma shiftedProgressionQuotient_ne_zero (m : ℕ) :
    shiftedProgressionQuotient m ≠ 0 := by
  intro hzero
  have heq := shiftedProgressionQuotient_mul_factorial m
  rw [hzero, zero_mul] at heq
  exact (mul_ne_zero (shiftedProgressionProduct_ne_zero m)
    (shiftedProgressionCorrection_ne_zero m)) heq.symm

lemma sub_one_mul_factorization_factorial_lt {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) : (p - 1) * m.factorial.factorization p < m := by
  rw [Nat.sub_one_mul_factorization_factorial hp]
  refine Nat.sub_lt_self ?_ (Nat.digit_sum_le p m)
  have hnil : p.digits m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil,
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hm)⟩

lemma shiftedProgressionProduct_le_six_pow_pred_mul_factorial (m : ℕ) :
    shiftedProgressionProduct m ≤ 6 ^ (m - 1) * m.factorial := by
  induction m with
  | zero => simp [shiftedProgressionProduct]
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        norm_num [shiftedProgressionProduct]
      · rw [shiftedProgressionProduct, Finset.prod_range_succ]
        change shiftedProgressionProduct m * (6 * m + 1) ≤
          6 ^ (m + 1 - 1) * (m + 1).factorial
        calc
          shiftedProgressionProduct m * (6 * m + 1) ≤
              (6 ^ (m - 1) * m.factorial) * (6 * (m + 1)) :=
            Nat.mul_le_mul ih (by omega)
          _ = 6 ^ (m + 1 - 1) * (m + 1).factorial := by
            rw [Nat.factorial_succ]
            have hmpos : 0 < m := Nat.pos_of_ne_zero hm
            have hp : 6 ^ (m - 1) * 6 = 6 ^ m := by
              rw [← pow_succ, show m - 1 + 1 = m by omega]
            rw [show m + 1 - 1 = m by omega]
            calc
              6 ^ (m - 1) * m.factorial * (6 * (m + 1)) =
                  (6 ^ (m - 1) * 6) * ((m + 1) * m.factorial) := by ring
              _ = 6 ^ m * ((m + 1) * m.factorial) := by rw [hp]

lemma shiftedProgressionCorrection_sq_le (m : ℕ) :
    shiftedProgressionCorrection m ^ 2 ≤ 12 ^ (m - 1) := by
  by_cases hm : m = 0
  · subst m
    norm_num [shiftedProgressionCorrection, progressionCorrection]
  let e2 := m.factorial.factorization 2
  let e3 := m.factorial.factorization 3
  have he2lt : e2 < m := by
    have h := sub_one_mul_factorization_factorial_lt Nat.prime_two hm
    simpa [e2] using h
  have he3lt : 2 * e3 < m := by
    have h := sub_one_mul_factorization_factorial_lt Nat.prime_three hm
    simpa [e3] using h
  have he2 : e2 ≤ m - 1 := by omega
  have he3 : 2 * e3 ≤ m - 1 := by omega
  have h2 : 4 ^ e2 ≤ 4 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) he2
  have h3 : 9 ^ e3 ≤ 3 ^ (m - 1) := by
    rw [show 9 = 3 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) he3
  unfold shiftedProgressionCorrection progressionCorrection
  change (2 ^ e2 * 3 ^ e3) ^ 2 ≤ 12 ^ (m - 1)
  calc
    (2 ^ e2 * 3 ^ e3) ^ 2 = 4 ^ e2 * 9 ^ e3 := by
      rw [mul_pow, pow_sq_comm, pow_sq_comm]
      norm_num
    _ ≤ 4 ^ (m - 1) * 3 ^ (m - 1) := Nat.mul_le_mul h2 h3
    _ = 12 ^ (m - 1) := by rw [← mul_pow]; norm_num

lemma six_pow_pred_mul_shiftedCorrection_le (m : ℕ) :
    6 ^ (m - 1) * shiftedProgressionCorrection m ≤ 21 ^ (m - 1) := by
  have hs : (6 ^ (m - 1) * shiftedProgressionCorrection m) ^ 2 ≤
      (21 ^ (m - 1)) ^ 2 := by
    calc
      (6 ^ (m - 1) * shiftedProgressionCorrection m) ^ 2 =
          36 ^ (m - 1) * shiftedProgressionCorrection m ^ 2 := by
        rw [mul_pow, pow_sq_comm]
        norm_num
      _ ≤ 36 ^ (m - 1) * 12 ^ (m - 1) :=
        Nat.mul_le_mul_left _ (shiftedProgressionCorrection_sq_le m)
      _ = 432 ^ (m - 1) := by rw [← mul_pow]; norm_num
      _ ≤ 441 ^ (m - 1) := Nat.pow_le_pow_left (by norm_num) _
      _ = (21 ^ (m - 1)) ^ 2 := by rw [pow_sq_comm]; norm_num
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hs

lemma shiftedProgressionQuotient_le_twentyone_pow_pred (m : ℕ) :
    shiftedProgressionQuotient m ≤ 21 ^ (m - 1) := by
  apply Nat.le_of_mul_le_mul_right _ m.factorial_pos
  rw [shiftedProgressionQuotient_mul_factorial]
  calc
    shiftedProgressionProduct m * shiftedProgressionCorrection m ≤
        (6 ^ (m - 1) * m.factorial) * shiftedProgressionCorrection m :=
      Nat.mul_le_mul_right _
        (shiftedProgressionProduct_le_six_pow_pred_mul_factorial m)
    _ = (6 ^ (m - 1) * shiftedProgressionCorrection m) * m.factorial := by ring
    _ ≤ 21 ^ (m - 1) * m.factorial :=
      Nat.mul_le_mul_right _ (six_pow_pred_mul_shiftedCorrection_le m)

lemma factorization_factorial_add_log_sub_le_shiftedProgressionProduct
    {m r : ℕ} (hm : 1 ≤ m) (hr : r.Prime) (hmod : r % 6 = 1) :
    m.factorial.factorization r + (r.log (6 * m - 5) - r.log m) ≤
      (shiftedProgressionProduct m).factorization r := by
  let high := 6 * m - 5
  let b := 6 * m + 1
  have hhigh : high = 6 * m - 5 := rfl
  have hhighpos : 0 < high := by simp [high]; omega
  have hmhigh : m ≤ high := by simp [high]; omega
  have hlogm_le : r.log m ≤ r.log high := Nat.log_mono_right hmhigh
  have hlogfac : r.log m < b := by
    exact (Nat.log_lt_self r (by omega)).trans (by simp [b]; omega)
  have hterm (j : ℕ) (hj : j ∈ Finset.range m) :
      (6 * j + 1).factorization r =
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
    apply Nat.factorization_eq_card_pow_dvd_of_lt hr (by omega)
    have hjle : 6 * j + 1 < b := by
      have := Finset.mem_range.mp hj
      simp [b]
      omega
    calc
      6 * j + 1 < b := hjle
      _ < 2 ^ b := Nat.lt_two_pow_self
      _ ≤ r ^ b := Nat.pow_le_pow_left hr.two_le _
  have hextra :
      Finset.card {i ∈ Finset.Ico 1 b | m < r ^ i ∧ r ^ i ≤ high} =
        r.log high - r.log m := by
    have hset : {i ∈ Finset.Ico 1 b | m < r ^ i ∧ r ^ i ≤ high} =
        Finset.Ico (r.log m + 1) (r.log high + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hi1, hib⟩, hmri, hri⟩
        have hlow : r.log m < i :=
          (Nat.log_lt_iff_lt_pow hr.one_lt (by omega : m ≠ 0)).2 hmri
        have hupper : i ≤ r.log high :=
          (Nat.le_log_iff_pow_le hr.one_lt hhighpos.ne').2 hri
        omega
      · rintro ⟨hlow, hupper⟩
        have hmri : m < r ^ i :=
          (Nat.log_lt_iff_lt_pow hr.one_lt (by omega : m ≠ 0)).1 (by omega)
        have hri : r ^ i ≤ high :=
          (Nat.le_log_iff_pow_le hr.one_lt hhighpos.ne').1 (by omega)
        have hi_le : i ≤ r.log high := by omega
        have hib : i < b := hi_le.trans_lt
          ((Nat.log_lt_self r hhighpos.ne').trans (by simp [high, b]))
        exact ⟨⟨by omega, hib⟩, hmri, hri⟩
    rw [hset]
    simp
  rw [shiftedProgressionProduct,
    Nat.factorization_prod_apply (fun j hj ↦ by omega)]
  calc
    m.factorial.factorization r + (r.log high - r.log m) =
        (∑ i ∈ Finset.Ico 1 b, m / r ^ i) +
          Finset.card {i ∈ Finset.Ico 1 b | m < r ^ i ∧ r ^ i ≤ high} := by
      rw [Nat.factorization_factorial hr hlogfac, hextra]
    _ = ∑ i ∈ Finset.Ico 1 b,
        (m / r ^ i + if m < r ^ i ∧ r ^ i ≤ high then 1 else 0) := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.Ico 1 b,
        Finset.card {j ∈ Finset.range m | r ^ i ∣ 6 * j + 1} := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hinterval : m < r ^ i ∧ r ^ i ≤ high
      · simp only [if_pos hinterval]
        have hdivzero : m / r ^ i = 0 := Nat.div_eq_of_lt hinterval.1
        rw [hdivzero, zero_add]
        exact one_le_card_shifted_progression_dvd_of_mod_six m (r ^ i) hm
          (one_lt_pow₀ hr.one_lt (by
            have := (Finset.mem_Ico.mp hi).1
            omega))
          (prime_power_mod_six_eq_one hmod) (by simpa [high] using hinterval.2)
      · simp only [if_neg hinterval, add_zero]
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        exact div_le_card_shifted_progression_dvd m (r ^ i)
          (one_lt_pow₀ hr.one_lt (by omega))
          (Nat.Coprime.pow_right i
            (coprime_six_of_prime_ne_two_ne_three hr (by omega) (by omega)))
    _ = ∑ j ∈ Finset.range m,
        Finset.card {i ∈ Finset.Ico 1 b | r ^ i ∣ 6 * j + 1} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range m, (6 * j + 1).factorization r := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).symm

lemma shiftedProgressionCorrection_factorization_eq_zero_of_mod_six
    {m r : ℕ} (hr : r.Prime) (hmod : r % 6 = 1) :
    (shiftedProgressionCorrection m).factorization r = 0 := by
  exact progressionCorrection_factorization_eq_zero_of_mod_six hr hmod

lemma APPrimePowerProduct_shifted_progression_step_dvd (m : ℕ) (hm : 1 ≤ m) :
    APPrimePowerProduct (6 * m - 5) 6 ∣
      APPrimePowerProduct m 6 * shiftedProgressionQuotient m := by
  have hleft := APPrimePowerProduct_ne_zero (6 * m - 5) 6
  have hright : APPrimePowerProduct m 6 * shiftedProgressionQuotient m ≠ 0 :=
    mul_ne_zero (APPrimePowerProduct_ne_zero m 6) (shiftedProgressionQuotient_ne_zero m)
  apply (Nat.factorization_le_iff_dvd hleft hright).1
  intro r
  rw [Nat.factorization_mul (APPrimePowerProduct_ne_zero m 6)
    (shiftedProgressionQuotient_ne_zero m), Finsupp.add_apply]
  by_cases hr : r.Prime
  · rw [APPrimePowerProduct_factorization_apply_of_prime _ _ hr,
      APPrimePowerProduct_factorization_apply_of_prime _ _ hr]
    by_cases hmod : r % 6 = 1
    · simp only [if_pos hmod]
      have hqfac :
          (shiftedProgressionQuotient m).factorization r + m.factorial.factorization r =
            (shiftedProgressionProduct m).factorization r +
              (shiftedProgressionCorrection m).factorization r := by
        calc
          (shiftedProgressionQuotient m).factorization r + m.factorial.factorization r =
              (shiftedProgressionQuotient m * m.factorial).factorization r := by
            rw [Nat.factorization_mul (shiftedProgressionQuotient_ne_zero m)
              m.factorial_ne_zero, Finsupp.add_apply]
          _ = (shiftedProgressionProduct m *
                shiftedProgressionCorrection m).factorization r := by
            rw [shiftedProgressionQuotient_mul_factorial]
          _ = (shiftedProgressionProduct m).factorization r +
                (shiftedProgressionCorrection m).factorization r := by
            rw [Nat.factorization_mul (shiftedProgressionProduct_ne_zero m)
              (shiftedProgressionCorrection_ne_zero m), Finsupp.add_apply]
      rw [shiftedProgressionCorrection_factorization_eq_zero_of_mod_six hr hmod,
        add_zero] at hqfac
      have hprog :=
        factorization_factorial_add_log_sub_le_shiftedProgressionProduct hm hr hmod
      have hlogle : r.log m ≤ r.log (6 * m - 5) :=
        Nat.log_mono_right (by omega)
      omega
    · simp [hmod]
  · have hzleft : (APPrimePowerProduct (6 * m - 5) 6).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hzleft]

def ceilDivSix (x : ℕ) : ℕ := (x + 5) / 6

lemma ceilDivSix_bounds {x : ℕ} (hx : 7 ≤ x) :
    1 ≤ ceilDivSix x ∧ 6 * ceilDivSix x - 5 ≤ x ∧ x ≤ 6 * ceilDivSix x := by
  have hdecomp := Nat.mod_add_div (x + 5) 6
  have hrem : (x + 5) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  simp only [ceilDivSix]
  omega

lemma ceilDivSix_lt {x : ℕ} (hx : 7 ≤ x) : ceilDivSix x < x := by
  have hb := ceilDivSix_bounds hx
  omega

lemma mod_six_eq_one_le_shifted_endpoint {d m : ℕ} (hm : 1 ≤ m)
    (hmod : d % 6 = 1) (hdle : d ≤ 6 * m) : d ≤ 6 * m - 5 := by
  have hdecomp := Nat.mod_add_div d 6
  simp only [hmod] at hdecomp
  omega

lemma APPrimePowerProduct_eq_shifted_endpoint {x : ℕ} (hx : 7 ≤ x) :
    APPrimePowerProduct x 6 =
      APPrimePowerProduct (6 * ceilDivSix x - 5) 6 := by
  let m := ceilDivSix x
  have hb := ceilDivSix_bounds hx
  have hm : 1 ≤ m := hb.1
  have hhighx : 6 * m - 5 ≤ x := hb.2.1
  have hxupper : x ≤ 6 * m := hb.2.2
  apply Nat.eq_of_factorization_eq (APPrimePowerProduct_ne_zero x 6)
    (APPrimePowerProduct_ne_zero (6 * m - 5) 6)
  intro r
  by_cases hr : r.Prime
  · rw [APPrimePowerProduct_factorization_apply_of_prime _ _ hr,
      APPrimePowerProduct_factorization_apply_of_prime _ _ hr]
    by_cases hmod : r % 6 = 1
    · simp only [if_pos hmod]
      apply le_antisymm
      · have hpow : r ^ r.log x ≤ x := Nat.pow_log_le_self r (by omega)
        have hpmod : (r ^ r.log x) % 6 = 1 := prime_power_mod_six_eq_one hmod
        have hpowhigh : r ^ r.log x ≤ 6 * m - 5 :=
          mod_six_eq_one_le_shifted_endpoint hm hpmod (hpow.trans hxupper)
        exact Nat.le_log_of_pow_le hr.one_lt hpowhigh
      · exact Nat.log_mono_right hhighx
    · simp [hmod]
  · have hz1 : (APPrimePowerProduct x 6).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    have hz2 : (APPrimePowerProduct (6 * m - 5) 6).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hz1, hz2]

lemma APPrimePowerProduct_eq_one_of_lt_seven {x : ℕ} (hx : x < 7) :
    APPrimePowerProduct x 6 = 1 := by
  apply Nat.eq_of_factorization_eq (APPrimePowerProduct_ne_zero x 6) (by norm_num)
  intro r
  rw [Nat.factorization_one]
  by_cases hr : r.Prime
  · rw [APPrimePowerProduct_factorization_apply_of_prime _ _ hr]
    by_cases hmod : r % 6 = 1
    · have hr7 : 7 ≤ r := by
        by_contra h
        have hrlt : r < 7 := by omega
        have hr2 := hr.two_le
        interval_cases r <;> norm_num at hmod
      simp [hmod, (Nat.log_eq_zero_iff.2 (Or.inl (hx.trans_le hr7)))]
    · simp [hmod]
  · exact Nat.factorization_eq_zero_of_not_prime _ hr

def progressionExponent (x : ℕ) : ℕ :=
  if hx : 7 ≤ x then
    let m := ceilDivSix x
    (m - 1) + progressionExponent m
  else 0
termination_by x
decreasing_by
  exact ceilDivSix_lt hx

lemma progressionExponent_eq {x : ℕ} (hx : 7 ≤ x) :
    progressionExponent x =
      (ceilDivSix x - 1) + progressionExponent (ceilDivSix x) := by
  rw [progressionExponent]
  simp [hx]

lemma progressionExponent_eq_zero {x : ℕ} (hx : x < 7) :
    progressionExponent x = 0 := by
  rw [progressionExponent]
  simp [show ¬7 ≤ x by omega]

lemma APPrimePowerProduct_le_twentyone_pow_progressionExponent (x : ℕ) :
    APPrimePowerProduct x 6 ≤ 21 ^ progressionExponent x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hx : 7 ≤ x
      · let m := ceilDivSix x
        have hm : 1 ≤ m := (ceilDivSix_bounds hx).1
        have hmx : m < x := ceilDivSix_lt hx
        have hstep := APPrimePowerProduct_shifted_progression_step_dvd m hm
        have hdiv : APPrimePowerProduct x 6 ∣
            APPrimePowerProduct m 6 * shiftedProgressionQuotient m := by
          rw [APPrimePowerProduct_eq_shifted_endpoint hx]
          exact hstep
        have hle : APPrimePowerProduct x 6 ≤
            APPrimePowerProduct m 6 * shiftedProgressionQuotient m :=
          Nat.le_of_dvd
            (mul_pos
              (Nat.pos_of_ne_zero (APPrimePowerProduct_ne_zero m 6))
              (Nat.pos_of_ne_zero (shiftedProgressionQuotient_ne_zero m))) hdiv
        calc
          APPrimePowerProduct x 6 ≤
              APPrimePowerProduct m 6 * shiftedProgressionQuotient m := hle
          _ ≤ 21 ^ progressionExponent m * 21 ^ (m - 1) :=
            Nat.mul_le_mul (ih m hmx)
              (shiftedProgressionQuotient_le_twentyone_pow_pred m)
          _ = 21 ^ progressionExponent x := by
            rw [progressionExponent_eq hx]
            rw [pow_add]
            ring
      · have hxlt : x < 7 := by omega
        rw [APPrimePowerProduct_eq_one_of_lt_seven hxlt,
          progressionExponent_eq_zero hxlt]
        norm_num

lemma five_mul_progressionExponent_le_pred (x : ℕ) :
    5 * progressionExponent x ≤ x - 1 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hx : 7 ≤ x
      · let m := ceilDivSix x
        have hm : 1 ≤ m := (ceilDivSix_bounds hx).1
        have hmx : m < x := ceilDivSix_lt hx
        have hrec := ih m hmx
        have hceil : 6 * m ≤ x + 5 := by
          have hlow : 6 * m - 5 ≤ x := by
            simpa [m] using (ceilDivSix_bounds hx).2.1
          omega
        rw [progressionExponent_eq hx]
        change 5 * ((m - 1) + progressionExponent m) ≤ x - 1
        omega
      · have hxlt : x < 7 := by omega
        rw [progressionExponent_eq_zero hxlt]
        simp

def progressionExponentSum (n : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (n / 7), progressionExponent (n / s)

lemma sum_progressionExponent_eq_cutoff (n : ℕ) :
    ∑ s ∈ Finset.Icc 1 n, progressionExponent (n / s) =
      progressionExponentSum n := by
  unfold progressionExponentSum
  symm
  apply Finset.sum_subset
  · intro s hs
    simp only [Finset.mem_Icc] at hs ⊢
    exact ⟨hs.1, hs.2.trans (Nat.div_le_self n 7)⟩
  · intro s hsn hsnot
    simp only [Finset.mem_Icc] at hsn
    have hsgt : n / 7 < s := by
      by_contra h
      exact hsnot (by simp only [Finset.mem_Icc]; omega)
    have hspos : 0 < s := by omega
    have hnlt : n < 7 * s := by
      rw [mul_comm]
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 7)).mp hsgt
    have hdivlt : n / s < 7 :=
      (Nat.div_lt_iff_lt_mul hspos).2 (by simpa [mul_comm] using hnlt)
    exact progressionExponent_eq_zero hdivlt

lemma five_mul_progressionExponentSum_le (n : ℕ) :
    5 * progressionExponentSum n ≤
      ∑ s ∈ Finset.Icc 1 (n / 7), (n / s - 1) := by
  unfold progressionExponentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  exact five_mul_progressionExponent_le_pred (n / s)

lemma cast_sum_div_sub_le_log_bound {n : ℕ} (hn : 7 ≤ n) :
    ((∑ s ∈ Finset.Icc 1 (n / 7), (n / s - 1) : ℕ) : ℝ) ≤
      (n : ℝ) * (1 + Real.log ((n / 7 : ℕ) : ℝ)) - (n / 7 : ℕ) := by
  let M := n / 7
  have hMpos : 0 < M := by simp [M]; omega
  have hterm (s : ℕ) (hs : s ∈ Finset.Icc 1 M) :
      (((n / s - 1 : ℕ) : ℝ)) ≤ (n : ℝ) * (s : ℝ)⁻¹ - 1 := by
    have hs' := Finset.mem_Icc.mp hs
    have hseven : 7 ≤ n / s := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have hsM : s ≤ n / 7 := by simpa [M] using hs'.2
      exact (Nat.mul_le_mul_left 7 hsM).trans (Nat.mul_div_le n 7)
    rw [Nat.cast_sub (by omega : 1 ≤ n / s), Nat.cast_one]
    have hcast : ((n / s : ℕ) : ℝ) ≤ (n : ℝ) / (s : ℝ) := Nat.cast_div_le
    simpa [div_eq_mul_inv] using sub_le_sub_right hcast 1
  calc
    ((∑ s ∈ Finset.Icc 1 M, (n / s - 1) : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc 1 M, (((n / s - 1 : ℕ) : ℝ)) := by simp
    _ ≤ ∑ s ∈ Finset.Icc 1 M, ((n : ℝ) * (s : ℝ)⁻¹ - 1) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s hs
    _ = (n : ℝ) * (harmonic M : ℝ) - M := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      simp
    _ ≤ (n : ℝ) * (1 + Real.log M) - M := by
      gcongr
      exact harmonic_le_one_add_log M
    _ = (n : ℝ) * (1 + Real.log ((n / 7 : ℕ) : ℝ)) - (n / 7 : ℕ) := by
      simp [M]

lemma log_twentyone_lt : Real.log 21 < (61 / 20 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 21)]
  calc
    (21 : ℝ) < ∑ i ∈ Finset.range 9, (61 / 20 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (61 / 20 : ℝ) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 9

lemma nineteen_tenths_lt_log_seven : (19 / 10 : ℝ) < Real.log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 7)]
  have he : Real.exp (19 / 20 : ℝ) < 13 / 5 := by
    refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 3) (by norm_num)).trans_lt ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp (19 / 10 : ℝ) = Real.exp (2 * (19 / 20 : ℝ)) := by norm_num
    _ = Real.exp (19 / 20 : ℝ) ^ 2 := Real.exp_nat_mul _ _
    _ < (13 / 5 : ℝ) ^ 2 := by gcongr
    _ < 7 := by norm_num

lemma twenty_six_fifths_lt_log_one_ninetyfour :
    (26 / 5 : ℝ) < Real.log 194 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 194)]
  have he : Real.exp (13 / 20 : ℝ) < 48 / 25 := by
    refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 4) (by norm_num)).trans_lt ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp (26 / 5 : ℝ) = Real.exp (8 * (13 / 20 : ℝ)) := by norm_num
    _ = Real.exp (13 / 20 : ℝ) ^ 8 := Real.exp_nat_mul _ _
    _ < (48 / 25 : ℝ) ^ 8 := by gcongr
    _ < 194 := by norm_num

lemma log_twentyseven_lt : Real.log 27 < (10 / 3 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 27)]
  calc
    (27 : ℝ) < ∑ i ∈ Finset.range 8, (10 / 3 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (10 / 3 : ℝ) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 8

lemma final_EO_log_inequality {n : ℕ} (hn : 194 ≤ n) :
    Real.log 27 + (3 * (n : ℝ) / 5) *
        (Real.log 21 * (1 + Real.log ((n : ℝ) / 7))) <
      2 * (n : ℝ) * (Real.log n - 1) := by
  let N : ℝ := n
  let L : ℝ := Real.log N
  let A : ℝ := 1 + Real.log (N / 7)
  let B : ℝ := L - 9 / 10
  have hN : (194 : ℝ) ≤ N := by
    simp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by nlinarith
  have hlogN : (26 / 5 : ℝ) < L := by
    have hmono : Real.log (194 : ℝ) ≤ Real.log N :=
      Real.log_le_log (by norm_num) hN
    exact twenty_six_fifths_lt_log_one_ninetyfour.trans_le hmono
  have hratio : 1 < N / 7 := by nlinarith
  have hApos : 0 < A := by
    have := Real.log_pos hratio
    simp only [A]
    linarith
  have hBpos : 0 < B := by simp only [B]; nlinarith
  have hAB : A < B := by
    have hdiv : Real.log (N / 7) = L - Real.log 7 := by
      simp only [L]
      exact Real.log_div hNpos.ne' (by norm_num)
    simp only [A, B]
    rw [hdiv]
    nlinarith [nineteen_tenths_lt_log_seven]
  have hlog21pos : 0 < Real.log 21 := Real.log_pos (by norm_num)
  have hprod : Real.log 21 * A < (61 / 20 : ℝ) * B := by
    calc
      Real.log 21 * A < Real.log 21 * B :=
        mul_lt_mul_of_pos_left hAB hlog21pos
      _ < (61 / 20 : ℝ) * B :=
        mul_lt_mul_of_pos_right log_twentyone_lt hBpos
  have hcoef : 0 < 3 * N / 5 := by positivity
  have hupper :
      Real.log 27 + (3 * N / 5) * (Real.log 21 * A) <
        10 / 3 + (3 * N / 5) * ((61 / 20 : ℝ) * B) :=
    add_lt_add log_twentyseven_lt (mul_lt_mul_of_pos_left hprod hcoef)
  have hNL : N * (26 / 5 : ℝ) < N * L :=
    mul_lt_mul_of_pos_left hlogN hNpos
  have hfinal :
      10 / 3 + (3 * N / 5) * ((61 / 20 : ℝ) * B) <
        2 * N * (L - 1) := by
    simp only [B]
    nlinarith
  simpa [N, L, A] using hupper.trans hfinal

lemma mul_log_sub_one_le_log_factorial {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log n - 1) ≤ Real.log (n.factorial : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (calc
      (1 : ℝ) ≤ 6 * n := by nlinarith
      _ < 2 * Real.pi * n := by
        exact mul_lt_mul_of_pos_right (by nlinarith) hnpos).le
  have hpowpos : (0 : ℝ) ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hpowfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n = 1 * ((n : ℝ) / Real.exp 1) ^ n := by simp
      _ ≤ Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n :=
        mul_le_mul_of_nonneg_right hsqrt hpowpos
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
      ((n : ℝ) / Real.exp 1) ^ n) hpowfac
  rw [Real.log_pow, Real.log_div hnpos.ne' (Real.exp_ne_zero 1), Real.log_exp] at hlog
  norm_num at hlog ⊢
  simpa [mul_sub] using hlog

lemma cast_progressionExponentSum_le_log_bound {n : ℕ} (hn : 194 ≤ n) :
    (progressionExponentSum n : ℝ) ≤
      (n : ℝ) / 5 * (1 + Real.log ((n : ℝ) / 7)) := by
  let M := n / 7
  have hn7 : 7 ≤ n := hn.trans' (by norm_num)
  have hMpos : 0 < M := by simp [M]; omega
  have hfiveNat := five_mul_progressionExponentSum_le n
  have hfive : (5 : ℝ) * progressionExponentSum n ≤
      ((∑ s ∈ Finset.Icc 1 (n / 7), (n / s - 1) : ℕ) : ℝ) := by
    exact_mod_cast hfiveNat
  have hsum := cast_sum_div_sub_le_log_bound hn7
  have hdrop :
      ((∑ s ∈ Finset.Icc 1 (n / 7), (n / s - 1) : ℕ) : ℝ) ≤
        (n : ℝ) * (1 + Real.log (M : ℝ)) := by
    calc
      ((∑ s ∈ Finset.Icc 1 (n / 7), (n / s - 1) : ℕ) : ℝ) ≤
          (n : ℝ) * (1 + Real.log ((n / 7 : ℕ) : ℝ)) - (n / 7 : ℕ) := hsum
      _ ≤ (n : ℝ) * (1 + Real.log (M : ℝ)) := by simp [M]
  have hMcast : (M : ℝ) ≤ (n : ℝ) / 7 := by
    simpa [M] using (Nat.cast_div_le : ((n / 7 : ℕ) : ℝ) ≤ (n : ℝ) / 7)
  have hlogmono : Real.log (M : ℝ) ≤ Real.log ((n : ℝ) / 7) :=
    Real.log_le_log (by positivity) hMcast
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hupper : (n : ℝ) * (1 + Real.log (M : ℝ)) ≤
      (n : ℝ) * (1 + Real.log ((n : ℝ) / 7)) := by gcongr
  have htotal := hfive.trans (hdrop.trans hupper)
  nlinarith


lemma factorialAPPart_factorization (n a : ℕ) :
    (factorialAPPart n a).factorization =
      n.factorial.factorization.filter fun r ↦ r % a = 1 := by
  unfold factorialAPPart
  apply Nat.factorization_prod_pow_eq_self_of_le_factorization (n := n.factorial)
  intro r
  simp only [Finsupp.filter_apply]
  split <;> omega

lemma factorialAPPart_dvd_factorial (n a : ℕ) :
    factorialAPPart n a ∣ n.factorial := by
  unfold factorialAPPart
  apply Nat.prod_pow_dvd_of_le_factorization (n := n.factorial)
  intro r
  simp only [Finsupp.filter_apply]
  split <;> omega

lemma factorialAPPart_ne_zero (n a : ℕ) : factorialAPPart n a ≠ 0 := by
  intro hzero
  have hd := factorialAPPart_dvd_factorial n a
  rw [hzero, zero_dvd_iff] at hd
  exact n.factorial_ne_zero hd

lemma factorialAPPart_eq_prod_APPrimePowerProduct (n a : ℕ) :
    factorialAPPart n a =
      ∏ s ∈ Finset.Icc 1 n, APPrimePowerProduct (n / s) a := by
  have hprodne : (∏ s ∈ Finset.Icc 1 n,
      APPrimePowerProduct (n / s) a) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun s hs ↦
      APPrimePowerProduct_ne_zero (n / s) a
  apply Nat.eq_of_factorization_eq (factorialAPPart_ne_zero n a) hprodne
  intro r
  rw [factorialAPPart_factorization, Finsupp.filter_apply,
    Nat.factorization_prod_apply (fun s hs ↦ APPrimePowerProduct_ne_zero (n / s) a)]
  by_cases hr : r.Prime
  · simp_rw [APPrimePowerProduct_factorization_apply_of_prime _ _ hr]
    by_cases hmod : r % a = 1
    · simp only [if_pos hmod]
      exact (sum_log_div_eq_factorization_factorial hr).symm
    · simp [hmod]
  · have hfac : n.factorial.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    have hpiece (s : ℕ) :
        (APPrimePowerProduct (n / s) a).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hfac, hpiece]

lemma factorialAPPart_le_twentyone_pow_progressionExponentSum (n : ℕ) :
    factorialAPPart n 6 ≤ 21 ^ progressionExponentSum n := by
  rw [factorialAPPart_eq_prod_APPrimePowerProduct]
  calc
    (∏ s ∈ Finset.Icc 1 n, APPrimePowerProduct (n / s) 6) ≤
        ∏ s ∈ Finset.Icc 1 n, 21 ^ progressionExponent (n / s) := by
      apply Finset.prod_le_prod
      · intro s hs
        exact Nat.zero_le _
      intro s hs
      exact APPrimePowerProduct_le_twentyone_pow_progressionExponent (n / s)
    _ = 21 ^ (∑ s ∈ Finset.Icc 1 n, progressionExponent (n / s)) := by
      exact Finset.prod_pow_eq_pow_sum (Finset.Icc 1 n)
        (fun s ↦ progressionExponent (n / s)) 21
    _ = 21 ^ progressionExponentSum n := by rw [sum_progressionExponent_eq_cutoff]

lemma not_factorial_sq_lt_twentyseven_mul_APPart_cube {n : ℕ} (hn : 194 ≤ n) :
    ¬n.factorial ^ 2 < 27 * factorialAPPart n 6 ^ 3 := by
  intro hineq
  let E := progressionExponentSum n
  let T := factorialAPPart n 6
  have hTne : T ≠ 0 := factorialAPPart_ne_zero n 6
  have hTbound : T ≤ 21 ^ E := by
    simpa [T, E] using factorialAPPart_le_twentyone_pow_progressionExponentSum n
  have hlogT : Real.log (T : ℝ) ≤ (E : ℝ) * Real.log 21 := by
    have hcast : (T : ℝ) ≤ ((21 ^ E : ℕ) : ℝ) := by exact_mod_cast hTbound
    have hlog := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hTne) hcast
    simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hE : (E : ℝ) ≤ (n : ℝ) / 5 * (1 + Real.log ((n : ℝ) / 7)) := by
    simpa [E] using cast_progressionExponentSum_le_log_bound hn
  have hlog21pos : 0 < Real.log 21 := Real.log_pos (by norm_num)
  have hlogTupper : Real.log (T : ℝ) ≤
      ((n : ℝ) / 5 * (1 + Real.log ((n : ℝ) / 7))) * Real.log 21 :=
    hlogT.trans (mul_le_mul_of_nonneg_right hE hlog21pos.le)
  have hcastineq : ((n.factorial ^ 2 : ℕ) : ℝ) <
      ((27 * T ^ 3 : ℕ) : ℝ) := by exact_mod_cast hineq
  have hrhspos : (0 : ℝ) < (27 : ℝ) * (T : ℝ) ^ 3 := by positivity
  have hlogs := (Real.log_lt_log_iff (by positivity : (0 : ℝ) <
      ((n.factorial ^ 2 : ℕ) : ℝ)) hrhspos).2 (by
        simpa [Nat.cast_mul, Nat.cast_pow] using hcastineq)
  have hlogs' : 2 * Real.log (n.factorial : ℝ) <
      Real.log 27 + 3 * Real.log (T : ℝ) := by
    calc
      2 * Real.log (n.factorial : ℝ) = Real.log ((n.factorial ^ 2 : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        ring
      _ < Real.log ((27 : ℝ) * (T : ℝ) ^ 3) := hlogs
      _ = Real.log 27 + 3 * Real.log (T : ℝ) := by
        rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0)
          (by positivity : (T : ℝ) ^ 3 ≠ 0), Real.log_pow]
        ring
  have hfaclower := mul_log_sub_one_le_log_factorial (hn.trans' (by norm_num))
  have hlower : 2 * (n : ℝ) * (Real.log n - 1) ≤
      2 * Real.log (n.factorial : ℝ) := by nlinarith
  have hupper : Real.log 27 + 3 * Real.log (T : ℝ) ≤
      Real.log 27 + (3 * (n : ℝ) / 5) *
        (Real.log 21 * (1 + Real.log ((n : ℝ) / 7))) := by
    nlinarith
  have hfinal := final_EO_log_inequality hn
  linarith


lemma prime_mod_three_eq_one_iff_mod_six_eq_one {r : ℕ} (hr : r.Prime) :
    r % 3 = 1 ↔ r % 6 = 1 := by
  constructor
  · intro h3
    have hodd : r % 2 = 1 := by
      rcases hr.eq_two_or_odd with rfl | hodd
      · norm_num at h3
      · exact hodd
    have h6 : r % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have h3' : (r % 6) % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd r (by norm_num : 3 ∣ 6)]
      exact h3
    have h2' : (r % 6) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd r (by norm_num : 2 ∣ 6)]
      exact hodd
    omega
  · intro h6
    have h3' : (r % 6) % 3 = r % 3 :=
      Nat.mod_mod_of_dvd r (by norm_num : 3 ∣ 6)
    calc
      r % 3 = (r % 6) % 3 := h3'.symm
      _ = 1 := by simpa [h6]

/-- On prime support, the progressions `1 mod 3` and `1 mod 6` coincide. -/
lemma factorialAPPart_three_eq_six (n : ℕ) :
    factorialAPPart n 3 = factorialAPPart n 6 := by
  apply Nat.eq_of_factorization_eq (factorialAPPart_ne_zero n 3)
    (factorialAPPart_ne_zero n 6)
  rw [factorialAPPart_factorization, factorialAPPart_factorization]
  intro r
  simp only [Finsupp.filter_apply]
  by_cases hr : r.Prime
  · by_cases h3 : r % 3 = 1
    · have h6 := (prime_mod_three_eq_one_iff_mod_six_eq_one hr).1 h3
      simp [h3, h6]
    · have h6 : r % 6 ≠ 1 :=
        mt (prime_mod_three_eq_one_iff_mod_six_eq_one hr).2 h3
      simp [h3, h6]
  · have hz : n.factorial.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hr
    simp [hz]

/-- The cyclotomic factor of a cubic-minus-one factorial divides three
times the `1 mod 3` part of that factorial. -/
lemma sq_add_self_add_one_dvd_three_mul_factorialAPPart
    {n x : ℕ} (hdiv : x ^ 2 + x + 1 ∣ n.factorial) :
    x ^ 2 + x + 1 ∣ 3 * factorialAPPart n 3 := by
  have hBne : x ^ 2 + x + 1 ≠ 0 := by omega
  have hfacle : (x ^ 2 + x + 1).factorization ≤ n.factorial.factorization :=
    (Nat.factorization_le_iff_dvd hBne n.factorial_ne_zero).2 hdiv
  have hTne : factorialAPPart n 3 ≠ 0 := by
    intro hzero
    have hd := factorialAPPart_dvd_factorial n 3
    rw [hzero, zero_dvd_iff] at hd
    exact n.factorial_ne_zero hd
  apply (Nat.factorization_le_iff_dvd hBne (mul_ne_zero (by norm_num) hTne)).1
  intro r
  by_cases hfac0 : (x ^ 2 + x + 1).factorization r = 0
  · simp [hfac0]
  have hr : r.Prime := by
    by_contra hnot
    exact hfac0 (Nat.factorization_eq_zero_of_not_prime _ hnot)
  have hrdvd : r ∣ x ^ 2 + x + 1 := by
    by_contra hnot
    exact hfac0 (Nat.factorization_eq_zero_of_not_dvd hnot)
  rcases prime_eq_three_or_modEq_one_of_dvd_sq_add_self_add_one hr hrdvd with rfl | hmod
  · rw [Nat.factorization_mul (by norm_num) hTne]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three]
    exact (factorization_three_sq_add_self_add_one_le_one x).trans (Nat.le_add_right 1 _)
  · have hrem : r % 3 = 1 := by
      simpa [Nat.ModEq] using hmod
    rw [Nat.factorization_mul (by norm_num) hTne, Finsupp.add_apply,
      factorialAPPart_factorization, Finsupp.filter_apply, if_pos hrem]
    exact (hfacle r).trans (Nat.le_add_left _ _)

lemma cube_sub_one_factorization {x : ℕ} (hx : 1 ≤ x) :
    x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by
  apply (Nat.sub_eq_iff_eq_add (by
    simpa using Nat.pow_le_pow_left hx 3)).2
  have hxy : x = (x - 1) + 1 := (Nat.sub_add_cancel hx).symm
  rw [hxy]
  simp only [Nat.add_sub_cancel]
  ring

lemma cyclotomic_factor_dvd_three_mul_factorialAPPart_of_cube_sub_one
    {n x : ℕ} (heq : n.factorial = x ^ 3 - 1) :
    x ^ 2 + x + 1 ∣ 3 * factorialAPPart n 3 := by
  have hx : 1 ≤ x := by
    by_contra h
    have hx0 : x = 0 := by omega
    subst x
    norm_num at heq
    exact n.factorial_ne_zero heq
  apply sq_add_self_add_one_dvd_three_mul_factorialAPPart
  rw [heq, cube_sub_one_factorization hx]
  exact dvd_mul_left _ _

lemma sub_one_sq_lt_sq_add_self_add_one {x : ℕ} (hx : 1 ≤ x) :
    (x - 1) ^ 2 < x ^ 2 + x + 1 := by
  have hxy : x = (x - 1) + 1 := (Nat.sub_add_cancel hx).symm
  rw [hxy]
  simp only [Nat.add_sub_cancel]
  nlinarith

/-- The elementary inequality extracted from the cubic
Erdős--Obláth factorization, ready to be combined with the progression
estimate proved above. -/
lemma factorial_sq_lt_twenty_seven_mul_APPart_cube_of_cube_sub_one
    {n x : ℕ} (heq : n.factorial = x ^ 3 - 1) :
    n.factorial ^ 2 < 27 * factorialAPPart n 3 ^ 3 := by
  have hx : 1 ≤ x := by
    by_contra h
    have hx0 : x = 0 := by omega
    subst x
    norm_num at heq
    exact n.factorial_ne_zero heq
  have hfactor : n.factorial = (x - 1) * (x ^ 2 + x + 1) := by
    rw [heq, cube_sub_one_factorization hx]
  have hdvd := cyclotomic_factor_dvd_three_mul_factorialAPPart_of_cube_sub_one heq
  have hTpos : 0 < factorialAPPart n 3 :=
    Nat.pos_of_ne_zero (factorialAPPart_ne_zero n 3)
  have hBle : x ^ 2 + x + 1 ≤ 3 * factorialAPPart n 3 :=
    Nat.le_of_dvd (mul_pos (by norm_num) hTpos) hdvd
  calc
    n.factorial ^ 2 = (x - 1) ^ 2 * (x ^ 2 + x + 1) ^ 2 := by
      rw [hfactor, mul_pow]
    _ < (x ^ 2 + x + 1) * (x ^ 2 + x + 1) ^ 2 := by
      exact Nat.mul_lt_mul_of_pos_right (sub_one_sq_lt_sq_add_self_add_one hx)
        (pow_pos (by omega) 2)
    _ = (x ^ 2 + x + 1) ^ 3 := by ring
    _ ≤ (3 * factorialAPPart n 3) ^ 3 := Nat.pow_le_pow_left hBle 3
    _ = 27 * factorialAPPart n 3 ^ 3 := by ring

/-- The cubic special case of the Erdős--Obláth factorial-power theorem in
the range needed by Luca's proof. -/
theorem factorial_ne_cube_sub_one_of_ge_194 {n x : ℕ} (hn : 194 ≤ n) :
    n.factorial ≠ x ^ 3 - 1 := by
  intro heq
  have hineq :=
    factorial_sq_lt_twenty_seven_mul_APPart_cube_of_cube_sub_one heq
  rw [factorialAPPart_three_eq_six] at hineq
  exact not_factorial_sq_lt_twentyseven_mul_APPart_cube hn hineq

/-- The sum of the binary digits is at most the number of binary digits. -/
lemma sum_binary_digits_le_length (n : ℕ) :
    (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length := by
  have hlist : ∀ L : List ℕ, (∀ d ∈ L, d ≤ 1) → L.sum ≤ L.length := by
    intro L hdigits
    induction L with
    | nil => simp
    | cons d L ih =>
        rw [List.sum_cons, List.length_cons]
        have hd : d ≤ 1 := hdigits d (by simp)
        have htail : L.sum ≤ L.length := by
          apply ih
          intro x hx
          exact hdigits x (by simp [hx])
        omega
  apply hlist
  intro d hd
  have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
  omega

/-- Legendre's digit-sum identity gives the near-linear lower bound for the
two-adic valuation used in Luca's numerical absorption. -/
lemma factorial_factorization_two_ge_sub_log (n : ℕ) :
    n - (Nat.log 2 n + 1) ≤ n.factorial.factorization 2 := by
  have hid := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  norm_num at hid
  by_cases hn : n = 0
  · simp [hn]
  have hsum : (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 := by
    calc
      (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length :=
        sum_binary_digits_le_length n
      _ = Nat.log 2 n + 1 := Nat.length_digits 2 n (by norm_num) hn
  omega

/-- The natural base-two logarithm is bounded by the corresponding real
logarithm ratio. -/
lemma cast_log_two_le_real_log_div {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have hpowReal : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n)
    hpowReal
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog2).2
  simpa [mul_comm] using hlog

/-- Real-valued form of Luca's lower estimate for `v₂(n!)`. -/
lemma real_factorial_factorization_two_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) - (Real.log n / Real.log 2 + 1) ≤
      (n.factorial.factorization 2 : ℝ) := by
  have hnat := factorial_factorization_two_ge_sub_log n
  have hloglt : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hcast : ((n - (Nat.log 2 n + 1) : ℕ) : ℝ) ≤
      (n.factorial.factorization 2 : ℝ) := by exact_mod_cast hnat
  rw [Nat.cast_sub (by omega : Nat.log 2 n + 1 ≤ n), Nat.cast_add, Nat.cast_one] at hcast
  have hlog := cast_log_two_le_real_log_div (by omega : n ≠ 0)
  linarith

/-- A binary number with `s` one-digits is at least `2^s - 1`. -/
lemma two_pow_sum_le_ofDigits_add_one (L : List ℕ)
    (hL : ∀ d ∈ L, d ≤ 1) :
    2 ^ L.sum ≤ Nat.ofDigits 2 L + 1 := by
  induction L with
  | nil => simp
  | cons d L ih =>
      have hd : d ≤ 1 := hL d (by simp)
      have htail : ∀ x ∈ L, x ≤ 1 := by
        intro x hx
        exact hL x (by simp [hx])
      have hih := ih htail
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
      · simp only [List.sum_cons, zero_add, Nat.ofDigits_cons, zero_add]
        omega
      · simp only [List.sum_cons, Nat.ofDigits_cons]
        rw [add_comm 1 L.sum, pow_succ]
        omega

lemma two_pow_binary_digit_sum_le_succ (n : ℕ) :
    2 ^ (Nat.digits 2 n).sum ≤ n + 1 := by
  calc
    2 ^ (Nat.digits 2 n).sum ≤ Nat.ofDigits 2 (Nat.digits 2 n) + 1 := by
      apply two_pow_sum_le_ofDigits_add_one
      intro d hd
      have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
      omega
    _ = n + 1 := by rw [Nat.ofDigits_digits]

/-- The binary digit sum is bounded by the real base-two logarithm of the
successor. -/
lemma cast_binary_digit_sum_le_real_log_succ (n : ℕ) :
    ((Nat.digits 2 n).sum : ℝ) ≤ Real.log (n + 1) / Real.log 2 := by
  have hpowNat := two_pow_binary_digit_sum_le_succ n
  have hpowReal : ((2 : ℝ) ^ (Nat.digits 2 n).sum) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.digits 2 n).sum) hpowReal
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog2).2
  simpa [mul_comm] using hlog

/-- Luca's sharp real lower bound
`n - log(n+1)/log 2 ≤ v₂(n!)`. -/
lemma real_factorial_factorization_two_lower_sharp (n : ℕ) :
    (n : ℝ) - Real.log (n + 1) / Real.log 2 ≤
      (n.factorial.factorization 2 : ℝ) := by
  have hid := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  norm_num at hid
  have hsumNat : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hcastId := congrArg (fun z : ℕ ↦ (z : ℝ)) hid
  rw [Nat.cast_sub hsumNat] at hcastId
  have hsum := cast_binary_digit_sum_le_real_log_succ n
  nlinarith

lemma factorial_add_one_lt_pow_self {n : ℕ} (hn : 3 ≤ n) :
    n.factorial + 1 < n ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Nat.factorial_succ, Nat.pow_succ]
      calc
        (n + 1) * n.factorial + 1 ≤ (n + 1) * (n.factorial + 1) := by
          nlinarith
        _ < (n + 1) * n ^ n :=
          (Nat.mul_lt_mul_left (by omega : 0 < n + 1)).mpr ih
        _ ≤ (n + 1) * (n + 1) ^ n := by
          exact Nat.mul_le_mul_left _ (pow_le_pow_left' (Nat.le_succ n) n)
        _ = (n + 1) ^ n * (n + 1) := Nat.mul_comm _ _

noncomputable def blEnvelope (x : ℝ) : ℝ :=
  (781 / 5 : ℝ) * (x - 271 / 100) ^ 2 * (x + 347 / 500) * (x + 347 / 250)

noncomputable def blRatio (x : ℝ) : ℝ := blEnvelope x * Real.exp (-x)

lemma hasDerivAt_blEnvelope (x : ℝ) :
    HasDerivAt blEnvelope
      ((781 / 5 : ℝ) *
        (2 * (x - 271 / 100) * (x + 347 / 500) * (x + 347 / 250) +
          (x - 271 / 100) ^ 2 * (x + 347 / 250) +
          (x - 271 / 100) ^ 2 * (x + 347 / 500))) x := by
  have hA := (hasDerivAt_id x).sub_const (271 / 100 : ℝ)
  have hB := (hasDerivAt_id x).add_const (347 / 500 : ℝ)
  have hC := (hasDerivAt_id x).add_const (347 / 250 : ℝ)
  unfold blEnvelope
  apply ((((hA.pow 2).const_mul (781 / 5 : ℝ)).mul hB).mul hC).congr_deriv
  norm_num
  ring

lemma hasDerivAt_blRatio (x : ℝ) :
    HasDerivAt blRatio
      (((781 / 5 : ℝ) *
          (2 * (x - 271 / 100) * (x + 347 / 500) * (x + 347 / 250) +
            (x - 271 / 100) ^ 2 * (x + 347 / 250) +
            (x - 271 / 100) ^ 2 * (x + 347 / 500)) - blEnvelope x) *
        Real.exp (-x)) x := by
  have hnegexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa only [id_eq, Pi.neg_apply, mul_neg, mul_one] using (hasDerivAt_id x).neg.exp
  unfold blRatio
  apply ((hasDerivAt_blEnvelope x).mul hnegexp).congr_deriv
  ring

lemma blEnvelope_deriv_sub_self_neg {x : ℝ} (hx : 16 ≤ x) :
    (781 / 5 : ℝ) *
        (2 * (x - 271 / 100) * (x + 347 / 500) * (x + 347 / 250) +
          (x - 271 / 100) ^ 2 * (x + 347 / 250) +
          (x - 271 / 100) ^ 2 * (x + 347 / 500)) - blEnvelope x < 0 := by
  let y := x - 16
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3 : 0 ≤ y ^ 3 := mul_nonneg hy2 hy
  have hbracket :
      0 < (x + 347 / 500) * (x + 347 / 250) * (x - 271 / 100 - 2) -
        (x - 271 / 100) * ((x + 347 / 500) + (x + 347 / 250)) := by
    rw [show
      (x + 347 / 500) * (x + 347 / 250) * (x - 271 / 100 - 2) -
          (x - 271 / 100) * ((x + 347 / 500) + (x + 347 / 250)) =
        y ^ 3 + (10843 / 250 : ℝ) * y ^ 2 +
          (153599763 / 250000 : ℝ) * y + 35303225511 / 12500000 by
        dsimp [y]
        ring]
    positivity
  have hA : 0 < x - 271 / 100 := by linarith
  have hconst : 0 < (781 / 5 : ℝ) := by norm_num
  rw [show
    (781 / 5 : ℝ) *
          (2 * (x - 271 / 100) * (x + 347 / 500) * (x + 347 / 250) +
            (x - 271 / 100) ^ 2 * (x + 347 / 250) +
            (x - 271 / 100) ^ 2 * (x + 347 / 500)) - blEnvelope x =
      -(781 / 5 : ℝ) * (x - 271 / 100) *
        ((x + 347 / 500) * (x + 347 / 250) * (x - 271 / 100 - 2) -
          (x - 271 / 100) * ((x + 347 / 500) + (x + 347 / 250))) by
      simp only [blEnvelope]
      ring]
  have hprod : 0 < (781 / 5 : ℝ) * (x - 271 / 100) *
      ((x + 347 / 500) * (x + 347 / 250) * (x - 271 / 100 - 2) -
        (x - 271 / 100) * ((x + 347 / 500) + (x + 347 / 250))) :=
    mul_pos (mul_pos hconst hA) hbracket
  linarith

lemma blRatio_strictAntiOn : StrictAntiOn blRatio (Set.Ici 16) := by
  apply strictAntiOn_of_deriv_neg (D := Set.Ici 16) (convex_Ici 16)
  · unfold blRatio blEnvelope
    fun_prop
  · intro x hx
    have hx16 : 16 ≤ x := interior_subset hx
    rw [(hasDerivAt_blRatio x).deriv]
    exact mul_neg_of_neg_of_pos (blEnvelope_deriv_sub_self_neg hx16) (Real.exp_pos _)

lemma blRatio_sixteen_lt : blRatio 16 < (91 / 100 : ℝ) := by
  have hsum :
      ∑ i ∈ Finset.range 27, (16 : ℝ) ^ i / i.factorial ≤ Real.exp 16 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 27
  have hpoly : blEnvelope 16 < (91 / 100 : ℝ) * Real.exp 16 := by
    calc
      blEnvelope 16 < (91 / 100 : ℝ) *
          ∑ i ∈ Finset.range 27, (16 : ℝ) ^ i / i.factorial := by
        norm_num [blEnvelope, Finset.sum_range_succ, Nat.factorial]
      _ ≤ (91 / 100 : ℝ) * Real.exp 16 :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
  calc
    blRatio 16 = blEnvelope 16 * Real.exp (-16) := rfl
    _ < ((91 / 100 : ℝ) * Real.exp 16) * Real.exp (-16) := by
      exact mul_lt_mul_of_pos_right hpoly (Real.exp_pos _)
    _ = 91 / 100 := by rw [mul_assoc, ← Real.exp_add]; norm_num

lemma blEnvelope_lt_ninety_one_percent_exp {x : ℝ} (hx : 16 ≤ x) :
    blEnvelope x < (91 / 100 : ℝ) * Real.exp x := by
  have hratio : blRatio x ≤ blRatio 16 :=
    blRatio_strictAntiOn.antitoneOn (by norm_num) hx hx
  have hlt : blRatio x < (91 / 100 : ℝ) := hratio.trans_lt blRatio_sixteen_lt
  have hexp : 0 < Real.exp x := Real.exp_pos _
  have hmul := mul_lt_mul_of_pos_right hlt hexp
  rw [blRatio, mul_assoc, ← Real.exp_add] at hmul
  norm_num at hmul
  exact hmul

lemma six_hundred_ninety_three_thousandths_lt_log_two :
    (693 / 1000 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 5) (by norm_num)).trans_lt ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma log_two_lt_six_hundred_ninety_four_thousandths :
    Real.log 2 < (694 / 1000 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  calc
    (2 : ℝ) < ∑ i ∈ Finset.range 5, (694 / 1000 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (694 / 1000 : ℝ) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 5

lemma log_log_two_lt_neg_seven_twentieths :
    Real.log (Real.log 2) < (-7 / 20 : ℝ) := by
  have hexp : Real.exp (7 / 20 : ℝ) < 10 / 7 := by
    refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 3) (by norm_num)).trans_lt ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hneg : (7 / 10 : ℝ) < Real.exp (-7 / 20 : ℝ) := by
    rw [show (-7 / 20 : ℝ) = -(7 / 20) by norm_num, Real.exp_neg]
    have hinv := (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 10 / 7)
      (Real.exp_pos (7 / 20 : ℝ))).2 hexp
    norm_num at hinv ⊢
    exact hinv
  rw [Real.log_lt_iff_lt_exp (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact log_two_lt_six_hundred_ninety_four_thousandths.trans
    (by norm_num : (694 / 1000 : ℝ) < 7 / 10) |>.trans hneg

lemma sixteen_lt_log_nine_million : (16 : ℝ) < Real.log 9000000 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 9000000)]
  have he : Real.exp (1 / 2 : ℝ) < 1649 / 1000 := by
    refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 5) (by norm_num)).trans_lt ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp 16 = Real.exp (32 * (1 / 2 : ℝ)) := by norm_num
    _ = Real.exp (1 / 2 : ℝ) ^ 32 := Real.exp_nat_mul _ _
    _ < (1649 / 1000 : ℝ) ^ 32 := by gcongr
    _ < 9000000 := by norm_num

lemma sixteen_mul_add_fifteen_le_two_pow {m : ℕ} (hm : 8 ≤ m) :
    16 * m + 15 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [Nat.pow_succ]
      nlinarith [show 1 ≤ 16 * m by omega]

lemma self_le_two_pow_div_sixteen {n : ℕ} (hn : 128 ≤ n) :
    n ≤ 2 ^ (n / 16) := by
  have hdiv : 8 ≤ n / 16 := by omega
  have hmod : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hdecomp := Nat.mod_add_div n 16
  have hgrowth := sixteen_mul_add_fifteen_le_two_pow hdiv
  omega

lemma log_succ_div_log_two_le_div_sixteen {n : ℕ} (hn : 127 ≤ n) :
    Real.log (n + 1) / Real.log 2 ≤ (((n + 1) / 16 : ℕ) : ℝ) := by
  have hpowNat := self_le_two_pow_div_sixteen (n := n + 1) (by omega)
  have hpowReal : (((n + 1 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ ((n + 1) / 16)) := by exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hpowReal
  rw [Real.log_pow] at hlog
  exact (div_le_iff₀ (Real.log_pos (by norm_num))).2 (by simpa [mul_comm] using hlog)

lemma factorial_factorization_two_gt_ninety_one_percent {n : ℕ}
    (hn : 9000000 ≤ n) :
    (91 / 100 : ℝ) * n < (n.factorial.factorization 2 : ℝ) := by
  have hlower := real_factorial_factorization_two_lower_sharp n
  have hratio := log_succ_div_log_two_le_div_sixteen (n := n) (by omega)
  have hdivCast : ((((n + 1) / 16 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) / 16 :=
    Nat.cast_div_le
  push_cast at hdivCast
  have hnreal : (9000000 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at hdivCast ⊢
  nlinarith

lemma not_ge_nine_million_of_factorization_two_le_blEnvelope
    {n : ℕ} (hn : 9000000 ≤ n)
    (hupper : (n.factorial.factorization 2 : ℝ) ≤ blEnvelope (Real.log n)) : False := by
  have hlogmono : Real.log 9000000 ≤ Real.log n := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog16 : 16 ≤ Real.log n := sixteen_lt_log_nine_million.le.trans hlogmono
  have henvelope := blEnvelope_lt_ninety_one_percent_exp hlog16
  rw [Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ))] at henvelope
  have hlower := factorial_factorization_two_gt_ninety_one_percent hn
  linarith

/-- The specialized numerical consequence of the Bugeaud--Laurent estimate
needed by the final proof.  It is stated separately so that the analytic
determinant argument and its numerical absorption have an exact interface:
the second prime is below `36,000,000`. -/
def LargePrimeBound : Prop :=
  ∀ n p q a b : ℕ, 433 < n → IsFirstPrimeAfter n p → IsFirstPrimeAfter p q →
    0 < a → 0 < b → n.factorial + 1 = p ^ a * q ^ b → q < 36000000

noncomputable def blBPrime (p q : ℕ) (a b : ℕ) : ℝ :=
  (a : ℝ) / Real.log q + (b : ℝ) / Real.log p

noncomputable def blMaximum (p q : ℕ) (a b : ℕ) : ℝ :=
  max (Real.log (blBPrime p q a b) + Real.log (Real.log 2) + 2 / 5)
    (15 * Real.log 2)

/-- The exact rational specialization of Bugeaud--Laurent Théorème 4 used by
Luca.  This is the remaining analytic theorem to prove from interpolation
determinants. -/
def BugeaudLaurentSpecial : Prop :=
  ∀ p q a b : ℕ, p.Prime → q.Prime → p < q → 0 < a → 0 < b →
    (((p ^ a * q ^ b - 1).factorization 2 : ℕ) : ℝ) ≤
      36 / (Real.log 2) ^ 4 * (blMaximum p q a b) ^ 2 *
        Real.log p * Real.log q

lemma blBPrime_lt_n_div_log
    {n p q a b : ℕ} (hn : 3 ≤ n) (hnp : n < p) (hnq : n < q)
    (heq : n.factorial + 1 = p ^ a * q ^ b) :
    blBPrime p q a b < (n : ℝ) / Real.log n := by
  have hprodlt : p ^ a * q ^ b < n ^ n := by
    rw [← heq]
    exact factorial_add_one_lt_pow_self hn
  have hcast : (((p ^ a * q ^ b : ℕ) : ℝ)) < (((n ^ n : ℕ) : ℝ)) := by
    exact_mod_cast hprodlt
  have hnNatPos : 0 < n := by omega
  have hpNatPos : 0 < p := by omega
  have hqNatPos : 0 < q := by omega
  have hlog := Real.strictMonoOn_log
    (by positivity : (0 : ℝ) < ((p ^ a * q ^ b : ℕ) : ℝ))
    (by positivity : (0 : ℝ) < ((n ^ n : ℕ) : ℝ)) hcast
  push_cast at hlog
  rw [Real.log_mul (by positivity : (p : ℝ) ^ a ≠ 0)
      (by positivity : (q : ℝ) ^ b ≠ 0),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn.trans_lt' (by norm_num))
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogq : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hnpLog : Real.log n < Real.log p :=
    Real.strictMonoOn_log (by positivity : (0 : ℝ) < (n : ℝ))
      (by positivity : (0 : ℝ) < (p : ℝ)) (by exact_mod_cast hnp)
  have hnqLog : Real.log n < Real.log q :=
    Real.strictMonoOn_log (by positivity : (0 : ℝ) < (n : ℝ))
      (by positivity : (0 : ℝ) < (q : ℝ)) (by exact_mod_cast hnq)
  have hden : Real.log n * Real.log n < Real.log p * Real.log q := by
    calc
      Real.log n * Real.log n < Real.log p * Real.log n :=
        mul_lt_mul_of_pos_right hnpLog hlogn
      _ < Real.log p * Real.log q := mul_lt_mul_of_pos_left hnqLog hlogp
  rw [blBPrime]
  calc
    (a : ℝ) / Real.log q + (b : ℝ) / Real.log p =
        ((a : ℝ) * Real.log p + (b : ℝ) * Real.log q) /
          (Real.log p * Real.log q) := by field_simp
    _ < ((n : ℝ) * Real.log n) / (Real.log p * Real.log q) :=
      div_lt_div_of_pos_right (by simpa [mul_comm] using hlog)
        (mul_pos hlogp hlogq)
    _ < (n : ℝ) / Real.log n := by
      rw [div_lt_iff₀ (mul_pos hlogp hlogq), div_mul_eq_mul_div,
        lt_div_iff₀ hlogn]
      have hnpos : (0 : ℝ) < n := by positivity
      nlinarith [mul_lt_mul_of_pos_left hden hnpos]

lemma thirty_six_div_log_two_pow_four_lt :
    36 / (Real.log 2) ^ 4 < (781 / 5 : ℝ) := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ (pow_pos hlogpos 4)]
  have hpow := pow_lt_pow_left₀ six_hundred_ninety_three_thousandths_lt_log_two
    (by norm_num : (0 : ℝ) ≤ 693 / 1000) (by norm_num : 4 ≠ 0)
  norm_num at hpow ⊢
  nlinarith

lemma blMaximum_lt_log_sub
    {n p q a b : ℕ} (hn : 9000000 ≤ n) (hnp : n < p) (hnq : n < q)
    (ha : 0 < a) (hb : 0 < b) (heq : n.factorial + 1 = p ^ a * q ^ b) :
    blMaximum p q a b < Real.log n - 271 / 100 := by
  have hlogn16 : 16 < Real.log n := by
    exact sixteen_lt_log_nine_million.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hB := blBPrime_lt_n_div_log (by omega : 3 ≤ n) hnp hnq heq
  have hlogn : 0 < Real.log n := by linarith
  have hBpos : 0 < blBPrime p q a b := by
    rw [blBPrime]
    have hpLog : 0 < Real.log p :=
      Real.log_pos (by exact_mod_cast (show 1 < p by omega))
    have hqLog : 0 < Real.log q :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    positivity
  have hnDivPos : 0 < (n : ℝ) / Real.log n := div_pos (by positivity) hlogn
  have hlogB := Real.strictMonoOn_log hBpos hnDivPos hB
  rw [Real.log_div (by positivity) hlogn.ne'] at hlogB
  have hloglogn : (2772 / 1000 : ℝ) < Real.log (Real.log n) := by
    calc
      (2772 / 1000 : ℝ) = 4 * (693 / 1000 : ℝ) := by norm_num
      _ < 4 * Real.log 2 := by
        exact mul_lt_mul_of_pos_left six_hundred_ninety_three_thousandths_lt_log_two
          (by norm_num)
      _ = Real.log 16 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
        norm_num
      _ ≤ Real.log (Real.log n) :=
        Real.log_le_log (by norm_num) hlogn16.le
  have hfirst :
      Real.log (blBPrime p q a b) + Real.log (Real.log 2) + 2 / 5 <
        Real.log n - 271 / 100 := by
    nlinarith [log_log_two_lt_neg_seven_twentieths]
  have hsecond : 15 * Real.log 2 < Real.log n - 271 / 100 := by
    nlinarith [log_two_lt_six_hundred_ninety_four_thousandths]
  simp only [blMaximum, max_lt_iff]
  exact ⟨hfirst, hsecond⟩

lemma bl_rhs_lt_envelope
    {n p q a b : ℕ} (hn : 9000000 ≤ n)
    (hpfirst : IsFirstPrimeAfter n p) (hqfirst : IsFirstPrimeAfter p q)
    (ha : 0 < a) (hb : 0 < b) (heq : n.factorial + 1 = p ^ a * q ^ b) :
    36 / (Real.log 2) ^ 4 * (blMaximum p q a b) ^ 2 * Real.log p * Real.log q <
      blEnvelope (Real.log n) := by
  have hbounds := first_two_primes_le_four_mul hpfirst hqfirst (by omega)
  have hnpos : 0 < n := (by norm_num : 0 < 9000000).trans_le hn
  have hn0 : n ≠ 0 := hnpos.ne'
  have hp0 : 0 < p := hnpos.trans hpfirst.1
  have hq0 : 0 < q := hp0.trans hqfirst.1
  have hn1 : 1 < n := (by norm_num : 1 < 9000000).trans_le hn
  have hp1 : 1 < p := hn1.trans hpfirst.1
  have hq1 : 1 < q := hp1.trans hqfirst.1
  have hn0Real : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hlogn16 : 16 < Real.log n := sixteen_lt_log_nine_million.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hM := blMaximum_lt_log_sub hn hpfirst.1
    (hpfirst.1.trans hqfirst.1) ha hb heq
  have hMpos : 0 < blMaximum p q a b := by
    rw [blMaximum]
    exact lt_max_of_lt_right (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  have hApos : 0 < Real.log n - 271 / 100 := by linarith
  have hlogp : Real.log p < Real.log n + 347 / 500 := by
    have hcast : (p : ℝ) ≤ 2 * n := by exact_mod_cast hbounds.1
    have hlog := Real.log_le_log
      (by exact_mod_cast hp0 : (0 : ℝ) < p) hcast
    rw [Real.log_mul (by norm_num) hn0Real] at hlog
    nlinarith [log_two_lt_six_hundred_ninety_four_thousandths]
  have hlogq : Real.log q < Real.log n + 347 / 250 := by
    have hcast : (q : ℝ) ≤ 4 * n := by exact_mod_cast hbounds.2
    have hlog := Real.log_le_log
      (by exact_mod_cast hq0 : (0 : ℝ) < q) hcast
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc,
      Real.log_mul (by norm_num) (mul_ne_zero (by norm_num) hn0Real),
      Real.log_mul (by norm_num) hn0Real] at hlog
    nlinarith [log_two_lt_six_hundred_ninety_four_thousandths]
  have hlogppos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp1)
  have hlogqpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  calc
    36 / (Real.log 2) ^ 4 * (blMaximum p q a b) ^ 2 * Real.log p * Real.log q <
        (781 / 5 : ℝ) * (blMaximum p q a b) ^ 2 * Real.log p * Real.log q := by
      rw [show
        36 / (Real.log 2) ^ 4 * (blMaximum p q a b) ^ 2 * Real.log p * Real.log q =
          (36 / (Real.log 2) ^ 4) *
            ((blMaximum p q a b) ^ 2 * Real.log p * Real.log q) by ring,
        show
        (781 / 5 : ℝ) * (blMaximum p q a b) ^ 2 * Real.log p * Real.log q =
          (781 / 5 : ℝ) *
            ((blMaximum p q a b) ^ 2 * Real.log p * Real.log q) by ring]
      exact mul_lt_mul_of_pos_right thirty_six_div_log_two_pow_four_lt (by positivity)
    _ < (781 / 5 : ℝ) * (Real.log n - 271 / 100) ^ 2 *
        Real.log p * Real.log q := by gcongr
    _ < (781 / 5 : ℝ) * (Real.log n - 271 / 100) ^ 2 *
        (Real.log n + 347 / 500) * Real.log q := by gcongr
    _ < (781 / 5 : ℝ) * (Real.log n - 271 / 100) ^ 2 *
        (Real.log n + 347 / 500) * (Real.log n + 347 / 250) := by gcongr
    _ = blEnvelope (Real.log n) := rfl

theorem largePrimeBound_of_bugeaudLaurentSpecial
    (hBL : BugeaudLaurentSpecial) : LargePrimeBound := by
  intro n p q a b hn hpfirst hqfirst ha hb heq
  by_contra hqbound
  have hn9 : 9000000 ≤ n := by
    have hbounds := first_two_primes_le_four_mul hpfirst hqfirst (by omega)
    omega
  have hfacEq : n.factorial = p ^ a * q ^ b - 1 := Nat.eq_sub_of_add_eq heq
  have hBLupper := hBL p q a b hpfirst.2.1 hqfirst.2.1 hqfirst.1 ha hb
  have henvelope := bl_rhs_lt_envelope hn9 hpfirst hqfirst ha hb heq
  apply not_ge_nine_million_of_factorization_two_le_blEnvelope hn9
  rw [hfacEq]
  exact hBLupper.trans henvelope.le

/-- The elementary half of Legendre's formula: at least `n / 2` factors of
two occur in `n!`. -/
lemma factorial_factorization_two_ge_half (n : ℕ) :
    n / 2 ≤ n.factorial.factorization 2 := by
  by_cases hn2 : 2 ≤ n
  · have hlog : Nat.log 2 n < Nat.log 2 n + 1 := Nat.lt_succ_self _
    rw [Nat.factorization_factorial Nat.prime_two hlog]
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log 2 n + 1) := by
      simp only [Finset.mem_Ico, le_refl, true_and]
      exact Nat.succ_le_succ
        (Nat.le_log_of_pow_le (by norm_num) (by simpa using hn2))
    simpa using
      (Finset.single_le_sum (s := Finset.Ico 1 (Nat.log 2 n + 1))
        (f := fun i => n / 2 ^ i) (fun _ _ => Nat.zero_le _) hmem)
  · have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num

lemma factorization_two_le_clog (m : ℕ) :
    m.factorization 2 ≤ Nat.clog 2 m :=
  Nat.factorization_le_of_le_pow (Nat.le_pow_clog (by norm_num) m)

/-- A deliberately coarse lifting-the-exponent bound.  Passing from `a` to
the even exponent `2a` avoids a parity split. -/
lemma factorization_two_pow_sub_one_le
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : a ≠ 0) :
    (p ^ a - 1).factorization 2 ≤
      Nat.clog 2 (p + 1) + Nat.clog 2 (p - 1) + Nat.clog 2 (2 * a) := by
  have hpodd : ¬2 ∣ p := by
    intro h2p
    rcases (Nat.dvd_prime hp).mp h2p with h | h
    · norm_num at h
    · exact hp2 h.symm
  have hpowpos : 0 < p ^ a - 1 := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow ha hp.one_lt)
  have hpow2pos : 0 < p ^ (2 * a) - 1 := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hp.one_lt)
  have hdvd : p ^ a - 1 ∣ p ^ (2 * a) - 1 := by
    apply Nat.pow_sub_one_dvd_pow_sub_one
    exact ⟨2, by omega⟩
  have hfacdvd : (p ^ a - 1).factorization 2 ≤
      (p ^ (2 * a) - 1).factorization 2 :=
    (Nat.factorization_le_iff_dvd hpowpos.ne' hpow2pos.ne').mpr hdvd 2
  have hlte := padicValNat.pow_two_sub_one hp.one_lt hpodd (by omega : 2 * a ≠ 0)
    (⟨a, by omega⟩ : Even (2 * a))
  rw [← Nat.factorization_def _ Nat.prime_two,
    ← Nat.factorization_def _ Nat.prime_two,
    ← Nat.factorization_def _ Nat.prime_two,
    ← Nat.factorization_def _ Nat.prime_two] at hlte
  have hterms :
      (p ^ (2 * a) - 1).factorization 2 + 1 ≤
        Nat.clog 2 (p + 1) + Nat.clog 2 (p - 1) + Nat.clog 2 (2 * a) := by
    rw [hlte]
    exact Nat.add_le_add
      (Nat.add_le_add (factorization_two_le_clog (p + 1))
        (factorization_two_le_clog (p - 1)))
      (factorization_two_le_clog (2 * a))
  omega

lemma pure_power_exponent_lt {n p a : ℕ}
    (hn : 3 ≤ n) (hnp : n < p) (heq : n.factorial + 1 = p ^ a) :
    a < n := by
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    simp only [pow_zero] at heq
    have := Nat.factorial_pos n
    omega
  have hpow : n ^ a < p ^ a := Nat.pow_lt_pow_left hnp ha
  have hlt : p ^ a < n ^ n := by
    rw [← heq]
    exact factorial_add_one_lt_pow_self hn
  exact (Nat.pow_lt_pow_iff_right (by omega : 1 < n)).mp (hpow.trans hlt)

lemma eight_mul_add_seven_le_two_pow {m : ℕ} (hm : 8 ≤ m) :
    8 * m + 7 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [Nat.pow_succ]
      nlinarith [show 1 ≤ 8 * m by omega]

lemma self_le_two_pow_div_eight {n : ℕ} (hn : 64 ≤ n) :
    n ≤ 2 ^ (n / 8) := by
  have hdiv : 8 ≤ n / 8 := by omega
  have hmod : n % 8 < 8 := Nat.mod_lt n (by norm_num)
  have hdecomp := Nat.mod_add_div n 8
  have hgrowth := eight_mul_add_seven_le_two_pow hdiv
  omega

lemma clog_two_le_div_eight_add_three {n x : ℕ}
    (hn : 64 ≤ n) (hx : x ≤ 4 * n + 1) :
    Nat.clog 2 x ≤ n / 8 + 3 := by
  apply Nat.clog_le_of_le_pow
  calc
    x ≤ 4 * n + 1 := hx
    _ ≤ 8 * n := by omega
    _ ≤ 8 * 2 ^ (n / 8) := Nat.mul_le_mul_left 8 (self_le_two_pow_div_eight hn)
    _ = 2 ^ (n / 8 + 3) := by simp [pow_add, Nat.mul_comm]

lemma clog_two_le_div_eight_add_one {n x : ℕ}
    (hn : 64 ≤ n) (hx : x ≤ 2 * n) :
    Nat.clog 2 x ≤ n / 8 + 1 := by
  apply Nat.clog_le_of_le_pow
  calc
    x ≤ 2 * n := hx
    _ ≤ 2 * 2 ^ (n / 8) := Nat.mul_le_mul_left 2 (self_le_two_pow_div_eight hn)
    _ = 2 ^ (n / 8 + 1) := by simp [pow_add, Nat.mul_comm]

/-- Luca's elementary lemma for the large range: once `p` lies between `n`
and `4n`, `n!+1` cannot be a power of `p`. -/
lemma no_large_factorial_add_one_prime_power {n p a : ℕ}
    (hn : 64 ≤ n) (hp : p.Prime) (hnp : n < p) (hpbound : p ≤ 4 * n)
    (heq : n.factorial + 1 = p ^ a) : False := by
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    simp only [pow_zero] at heq
    have := Nat.factorial_pos n
    omega
  have ha_lt : a < n := pure_power_exponent_lt (by omega) hnp heq
  have hp2 : p ≠ 2 := by omega
  have hnat : n.factorial = p ^ a - 1 := Nat.eq_sub_of_add_eq heq
  have hfacEq : n.factorial.factorization 2 = (p ^ a - 1).factorization 2 := by
    rw [hnat]
  have hlower := factorial_factorization_two_ge_half n
  have hupper := factorization_two_pow_sub_one_le hp hp2 ha
  have hpplus : p + 1 ≤ 4 * n + 1 := by omega
  have hpminus : p - 1 ≤ 4 * n + 1 := by omega
  have hatwo : 2 * a ≤ 2 * n := by omega
  have hclogp := clog_two_le_div_eight_add_three hn hpplus
  have hclogm := clog_two_le_div_eight_add_three hn hpminus
  have hcloga := clog_two_le_div_eight_add_one hn hatwo
  have hgrowth : 3 * (n / 8) + 7 < n / 2 := by omega
  omega

/-- Kernel-evaluated certificates for the finite prefix left by the coarse
large-range estimate. -/
private def purePowerCheckBlock (start len : ℕ) : Bool :=
  (List.range' start len).all fun n =>
    let p := boundedFirstPrimeAfter 400 n
    let q := boundedFirstPrimeAfter 400 p
    (List.range n).all fun a =>
      decide (n.factorial + 1 ≠ p ^ a ∧ n.factorial + 1 ≠ q ^ a)

private theorem purePowerCheckBlock_12 : purePowerCheckBlock 12 8 = true := by decide
private theorem purePowerCheckBlock_20 : purePowerCheckBlock 20 8 = true := by decide
private theorem purePowerCheckBlock_28 : purePowerCheckBlock 28 8 = true := by decide
private theorem purePowerCheckBlock_36 : purePowerCheckBlock 36 8 = true := by decide
private theorem purePowerCheckBlock_44 : purePowerCheckBlock 44 8 = true := by decide
private theorem purePowerCheckBlock_52 : purePowerCheckBlock 52 8 = true := by decide
private theorem purePowerCheckBlock_60 : purePowerCheckBlock 60 4 = true := by decide

private lemma purePowerCheckBlock_spec {start len n a : ℕ}
    (hcheck : purePowerCheckBlock start len = true)
    (hn : n ∈ List.range' start len) (ha : a < n) :
    let p := boundedFirstPrimeAfter 400 n
    let q := boundedFirstPrimeAfter 400 p
    n.factorial + 1 ≠ p ^ a ∧ n.factorial + 1 ≠ q ^ a := by
  have hncheck := (List.all_eq_true.mp hcheck) n hn
  have hamem : a ∈ List.range n := by simp [ha]
  have hacomputed := (List.all_eq_true.mp hncheck) a hamem
  exact of_decide_eq_true hacomputed

lemma finite_no_pure_power {n a : ℕ} (hnlo : 12 ≤ n) (hnhi : n < 64) (ha : a < n) :
    let p := boundedFirstPrimeAfter 400 n
    let q := boundedFirstPrimeAfter 400 p
    n.factorial + 1 ≠ p ^ a ∧ n.factorial + 1 ≠ q ^ a := by
  by_cases h20 : n < 20
  · apply purePowerCheckBlock_spec purePowerCheckBlock_12 (a := a) (by simp; omega) ha
  by_cases h28 : n < 28
  · apply purePowerCheckBlock_spec purePowerCheckBlock_20 (a := a) (by simp; omega) ha
  by_cases h36 : n < 36
  · apply purePowerCheckBlock_spec purePowerCheckBlock_28 (a := a) (by simp; omega) ha
  by_cases h44 : n < 44
  · apply purePowerCheckBlock_spec purePowerCheckBlock_36 (a := a) (by simp; omega) ha
  by_cases h52 : n < 52
  · apply purePowerCheckBlock_spec purePowerCheckBlock_44 (a := a) (by simp; omega) ha
  by_cases h60 : n < 60
  · apply purePowerCheckBlock_spec purePowerCheckBlock_52 (a := a) (by simp; omega) ha
  · apply purePowerCheckBlock_spec purePowerCheckBlock_60 (a := a) (by simp; omega) ha

lemma indexed_finite_no_pure_power {n k a : ℕ}
    (hnlo : 12 ≤ n) (hnhi : n < 64)
    (hlo : lowerEndpoint k ≤ n) (hhi : n < primeAt k) (ha : a < n) :
    n.factorial + 1 ≠ primeAt k ^ a ∧
      n.factorial + 1 ≠ primeAt (k + 1) ^ a := by
  let p := boundedFirstPrimeAfter 400 n
  have hp : IsFirstPrimeAfter n p := boundedFirstPrimeAfter_spec n (by omega)
  have hindexed : IsFirstPrimeAfter n (primeAt k) :=
    primeAt_isFirstPrimeAfter hlo hhi
  have hpEq : p = primeAt k := IsFirstPrimeAfter.unique hp hindexed
  have hp197 : p ≤ 197 := hp.2.2 197 (by norm_num) (by omega)
  let q := boundedFirstPrimeAfter 400 p
  have hq : IsFirstPrimeAfter p q := boundedFirstPrimeAfter_spec p (by omega)
  have hnext : IsFirstPrimeAfter p (primeAt (k + 1)) := by
    simpa [hpEq] using next_primeAt_isFirstPrimeAfter k
  have hqEq : q = primeAt (k + 1) := IsFirstPrimeAfter.unique hq hnext
  have hqEq' : boundedFirstPrimeAfter 400 (primeAt k) = primeAt (k + 1) := by
    simpa [q, hpEq] using hqEq
  simpa [p, q, hpEq, hqEq'] using finite_no_pure_power hnlo hnhi ha

private lemma firstPrimeAfter_six : IsFirstPrimeAfter 6 7 := by
  have hsearch : boundedFirstPrimeAfter 400 6 = 7 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 6 (by norm_num)

private lemma firstPrimeAfter_seven : IsFirstPrimeAfter 7 11 := by
  have hsearch : boundedFirstPrimeAfter 400 7 = 11 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 7 (by norm_num)

private lemma firstPrimeAfter_eight : IsFirstPrimeAfter 8 11 := by
  have hsearch : boundedFirstPrimeAfter 400 8 = 11 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 8 (by norm_num)

private lemma firstPrimeAfter_nine : IsFirstPrimeAfter 9 11 := by
  have hsearch : boundedFirstPrimeAfter 400 9 = 11 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 9 (by norm_num)

private lemma firstPrimeAfter_ten : IsFirstPrimeAfter 10 11 := by
  have hsearch : boundedFirstPrimeAfter 400 10 = 11 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 10 (by norm_num)

private lemma firstPrimeAfter_eleven : IsFirstPrimeAfter 11 13 := by
  have hsearch : boundedFirstPrimeAfter 400 11 = 13 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 11 (by norm_num)

private lemma firstPrimeAfter_thirteen : IsFirstPrimeAfter 13 17 := by
  have hsearch : boundedFirstPrimeAfter 400 13 = 17 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 13 (by norm_num)

private lemma firstPrimeAfter_eighteen : IsFirstPrimeAfter 18 19 := by
  have hsearch : boundedFirstPrimeAfter 400 18 = 19 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 18 (by norm_num)

private lemma firstPrimeAfter_nineteen : IsFirstPrimeAfter 19 23 := by
  have hsearch : boundedFirstPrimeAfter 400 19 = 23 := by decide
  simpa [hsearch] using boundedFirstPrimeAfter_spec 19 (by norm_num)

/-- A prime divisor other than the first two primes after `n` rules out a
solution.  This packages the interval-index bookkeeping for the explicit
small cases. -/
lemma not_isSolution_of_bad_prime {n p q r : ℕ}
    (hp : IsFirstPrimeAfter n p) (hq : IsFirstPrimeAfter p q)
    (hr : r.Prime) (hrdvd : r ∣ n.factorial + 1) (hrp : r ≠ p) (hrq : r ≠ q) :
    ¬IsSolution n := by
  intro hn
  rcases hn with ⟨_, k, hlo, hhi, hdiv⟩
  have hpk : primeAt k = p :=
    IsFirstPrimeAfter.unique (primeAt_isFirstPrimeAfter hlo hhi) hp
  have hq' : IsFirstPrimeAfter (primeAt k) q := by simpa [hpk] using hq
  have hqk : primeAt (k + 1) = q :=
    IsFirstPrimeAfter.unique (next_primeAt_isFirstPrimeAfter k) hq'
  rcases hdiv r hr hrdvd with hbad | hbad
  · exact hrp (hbad.trans hpk)
  · exact hrq (hbad.trans hqk)

lemma erdos1058_not_solution_six : ¬IsSolution 6 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_six firstPrimeAfter_seven
      (r := 103)
  all_goals norm_num

lemma erdos1058_not_solution_seven : ¬IsSolution 7 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_seven firstPrimeAfter_eleven
      (r := 71)
  all_goals norm_num

lemma erdos1058_not_solution_eight : ¬IsSolution 8 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_eight firstPrimeAfter_eleven
      (r := 61)
  all_goals norm_num

lemma erdos1058_not_solution_nine : ¬IsSolution 9 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_nine firstPrimeAfter_eleven
      (r := 19)
  all_goals norm_num

lemma erdos1058_not_solution_ten : ¬IsSolution 10 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_ten firstPrimeAfter_eleven
      (r := 329891)
  all_goals norm_num

lemma erdos1058_not_solution_eleven : ¬IsSolution 11 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_eleven firstPrimeAfter_thirteen
      (r := 39916801)
  all_goals norm_num

lemma erdos1058_not_solution_eighteen : ¬IsSolution 18 := by
  apply not_isSolution_of_bad_prime firstPrimeAfter_eighteen firstPrimeAfter_nineteen
      (r := 29)
  all_goals norm_num

/-- A literal table of the least prime after each integer from `12` through
`197`.  It is split into three arrays so that all kernel reductions remain
comfortably within Lean's ordinary recursion limit. -/
private def certifiedPrimeAfterTable0 : Array ℕ :=
  #[13, 17, 17, 17, 17, 19, 19, 23, 23, 23, 23, 29, 29, 29, 29, 29, 29, 31,
    31, 37, 37, 37, 37, 37, 37, 41, 41, 41, 41, 43, 43, 47, 47, 47, 47, 53,
    53, 53, 53, 53, 53, 59, 59, 59, 59, 59, 59, 61, 61, 67, 67, 67, 67, 67,
    67, 71, 71, 71, 71, 73, 73, 79, 79, 79]

private def certifiedPrimeAfterTable1 : Array ℕ :=
  #[79, 79, 79, 83, 83, 83, 83, 89, 89, 89, 89, 89, 89, 97, 97, 97, 97, 97,
    97, 97, 97, 101, 101, 101, 101, 103, 103, 107, 107, 107, 107, 109, 109, 113,
    113, 113, 113, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127,
    127, 127, 131, 131, 131, 131, 137, 137, 137, 137, 137, 137, 139, 139, 149]

private def certifiedPrimeAfterTable2 : Array ℕ :=
  #[149, 149, 149, 149, 149, 149, 149, 149, 149, 151, 151, 157, 157, 157, 157,
    157, 157, 163, 163, 163, 163, 163, 163, 167, 167, 167, 167, 173, 173, 173,
    173, 173, 173, 179, 179, 179, 179, 179, 179, 181, 181, 191, 191, 191, 191,
    191, 191, 191, 191, 191, 191, 193, 193, 197, 197, 197, 197, 199]

private def certifiedPrimeAfter (n : ℕ) : ℕ :=
  if n < 76 then (certifiedPrimeAfterTable0[n - 12]?).getD 211
  else if n < 140 then (certifiedPrimeAfterTable1[n - 76]?).getD 211
  else (certifiedPrimeAfterTable2[n - 140]?).getD 211

private lemma certifiedPrimeAfter_spec0 {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n < 76) :
    IsFirstPrimeAfter n (certifiedPrimeAfter n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfter, certifiedPrimeAfterTable0,
      certifiedPrimeAfterTable1, certifiedPrimeAfterTable2] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfter_spec1 {n : ℕ} (hnlo : 76 ≤ n) (hnhi : n < 140) :
    IsFirstPrimeAfter n (certifiedPrimeAfter n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfter, certifiedPrimeAfterTable0,
      certifiedPrimeAfterTable1, certifiedPrimeAfterTable2] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfter_spec2 {n : ℕ} (hnlo : 140 ≤ n) (hnhi : n < 198) :
    IsFirstPrimeAfter n (certifiedPrimeAfter n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfter, certifiedPrimeAfterTable0,
      certifiedPrimeAfterTable1, certifiedPrimeAfterTable2] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfter_spec {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n < 198) :
    IsFirstPrimeAfter n (certifiedPrimeAfter n) := by
  by_cases h76 : n < 76
  · exact certifiedPrimeAfter_spec0 hnlo h76
  by_cases h140 : n < 140
  · exact certifiedPrimeAfter_spec1 (by omega) h140
  · exact certifiedPrimeAfter_spec2 (by omega) hnhi

private lemma boundedFirstPrimeAfter_eq_certified {n : ℕ}
    (hnlo : 12 ≤ n) (hnhi : n < 198) :
    boundedFirstPrimeAfter 400 n = certifiedPrimeAfter n :=
  IsFirstPrimeAfter.unique (boundedFirstPrimeAfter_spec n (by omega))
    (certifiedPrimeAfter_spec hnlo hnhi)

/-- The six pieces of the divisibility certificate are proved by ordinary
kernel-checked normalization of concrete factorials. -/
private lemma certifiedSmallNSieve0a {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n < 44) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve0b {n : ℕ} (hnlo : 44 ≤ n) (hnhi : n < 76) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve1a {n : ℕ} (hnlo : 76 ≤ n) (hnhi : n < 108) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve1b {n : ℕ} (hnlo : 108 ≤ n) (hnhi : n < 140) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve2a {n : ℕ} (hnlo : 140 ≤ n) (hnhi : n < 167) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve2b {n : ℕ} (hnlo : 167 ≤ n) (hnhi : n ≤ 193) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfter, certifiedPrimeAfterTable0, certifiedPrimeAfterTable1,
      certifiedPrimeAfterTable2]

private lemma certifiedSmallNSieve {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n ≤ 193) :
    n = 18 ∨ ¬certifiedPrimeAfter n * certifiedPrimeAfter (certifiedPrimeAfter n) ∣
      n.factorial + 1 := by
  by_cases h44 : n < 44
  · exact certifiedSmallNSieve0a hnlo h44
  by_cases h76 : n < 76
  · exact certifiedSmallNSieve0b (by omega) h76
  by_cases h108 : n < 108
  · exact certifiedSmallNSieve1a (by omega) h108
  by_cases h140 : n < 140
  · exact certifiedSmallNSieve1b (by omega) h140
  by_cases h167 : n < 167
  · exact certifiedSmallNSieve2a (by omega) h167
  · exact certifiedSmallNSieve2b (by omega) hnhi

/-- The corrected finite check from Luca's small range.  The product of the
first two primes after `n` fails to divide `n!+1` throughout `[12,193]`,
except at `n=18`.  That exceptional integer is eliminated separately by the
prime divisor `29`. -/
lemma finiteSmallNSieve {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n ≤ 193) :
    let p := boundedFirstPrimeAfter 400 n
    let q := boundedFirstPrimeAfter 400 p
    n = 18 ∨ ¬p * q ∣ n.factorial + 1 := by
  have hpEq := boundedFirstPrimeAfter_eq_certified hnlo (by omega : n < 198)
  have hpSpec := certifiedPrimeAfter_spec hnlo (by omega : n < 198)
  have hpgt : n < certifiedPrimeAfter n := hpSpec.1
  have hple : certifiedPrimeAfter n ≤ 197 :=
    hpSpec.2.2 197 (by norm_num) (by omega)
  have hpBounds : 12 ≤ certifiedPrimeAfter n ∧ certifiedPrimeAfter n < 198 := by
    omega
  have hqEq := boundedFirstPrimeAfter_eq_certified hpBounds.1 hpBounds.2
  rw [hpEq]
  dsimp only
  rw [hqEq]
  exact certifiedSmallNSieve hnlo hnhi

lemma indexedFiniteSmallNSieve {n k : ℕ}
    (hnlo : 12 ≤ n) (hnhi : n ≤ 193)
    (hlo : lowerEndpoint k ≤ n) (hhi : n < primeAt k) :
    n = 18 ∨ ¬primeAt k * primeAt (k + 1) ∣ n.factorial + 1 := by
  let p := boundedFirstPrimeAfter 400 n
  have hp : IsFirstPrimeAfter n p := boundedFirstPrimeAfter_spec n (by omega)
  have hindexed : IsFirstPrimeAfter n (primeAt k) :=
    primeAt_isFirstPrimeAfter hlo hhi
  have hpEq : p = primeAt k := IsFirstPrimeAfter.unique hp hindexed
  have hp197 : p ≤ 197 := hp.2.2 197 (by norm_num) (by omega)
  let q := boundedFirstPrimeAfter 400 p
  have hq : IsFirstPrimeAfter p q := boundedFirstPrimeAfter_spec p (by omega)
  have hnext : IsFirstPrimeAfter p (primeAt (k + 1)) := by
    simpa [hpEq] using next_primeAt_isFirstPrimeAfter k
  have hqEq : q = primeAt (k + 1) := IsFirstPrimeAfter.unique hq hnext
  have hqEq' : boundedFirstPrimeAfter 400 (primeAt k) = primeAt (k + 1) := by
    simpa [q, hpEq] using hqEq
  simpa [p, q, hpEq, hqEq'] using finiteSmallNSieve hnlo hnhi

/-- A literal table of the least prime after each integer from `194` through
`449`.  This extends the direct finite certificate past all of the moduli used
in the cubic-character argument. -/
private def certifiedPrimeAfterLargeTable0 : Array ℕ :=
  #[197, 197, 197, 199, 199, 211, 211, 211, 211, 211, 211, 211, 211, 211,
    211, 211, 211, 223, 223, 223, 223, 223, 223, 223, 223, 223, 223, 223,
    223, 227, 227, 227, 227, 229, 229, 233, 233, 233, 233, 239, 239, 239,
    239, 239, 239, 241, 241, 251, 251, 251, 251, 251, 251, 251, 251, 251,
    251, 257, 257, 257, 257, 257, 257, 263]

private def certifiedPrimeAfterLargeTable1 : Array ℕ :=
  #[263, 263, 263, 263, 263, 269, 269, 269, 269, 269, 269, 271, 271, 277,
    277, 277, 277, 277, 277, 281, 281, 281, 281, 283, 283, 293, 293, 293,
    293, 293, 293, 293, 293, 293, 293, 307, 307, 307, 307, 307, 307, 307,
    307, 307, 307, 307, 307, 307, 307, 311, 311, 311, 311, 313, 313, 317,
    317, 317, 317, 331, 331, 331, 331, 331]

private def certifiedPrimeAfterLargeTable2 : Array ℕ :=
  #[331, 331, 331, 331, 331, 331, 331, 331, 331, 337, 337, 337, 337, 337,
    337, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 349, 349, 353,
    353, 353, 353, 359, 359, 359, 359, 359, 359, 367, 367, 367, 367, 367,
    367, 367, 367, 373, 373, 373, 373, 373, 373, 379, 379, 379, 379, 379,
    379, 383, 383, 383, 383, 389, 389, 389]

private def certifiedPrimeAfterLargeTable3 : Array ℕ :=
  #[389, 389, 389, 397, 397, 397, 397, 397, 397, 397, 397, 401, 401, 401,
    401, 409, 409, 409, 409, 409, 409, 409, 409, 419, 419, 419, 419, 419,
    419, 419, 419, 419, 419, 421, 421, 431, 431, 431, 431, 431, 431, 431,
    431, 431, 431, 433, 433, 439, 439, 439, 439, 439, 439, 443, 443, 443,
    443, 449, 449, 449, 449, 449, 449, 457]

private def certifiedPrimeAfterLarge (n : ℕ) : ℕ :=
  if n < 258 then (certifiedPrimeAfterLargeTable0[n - 194]?).getD 461
  else if n < 322 then (certifiedPrimeAfterLargeTable1[n - 258]?).getD 461
  else if n < 386 then (certifiedPrimeAfterLargeTable2[n - 322]?).getD 461
  else (certifiedPrimeAfterLargeTable3[n - 386]?).getD 461

private lemma certifiedPrimeAfterLarge_spec0 {n : ℕ}
    (hnlo : 194 ≤ n) (hnhi : n < 258) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec1a {n : ℕ}
    (hnlo : 258 ≤ n) (hnhi : n < 290) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec1b {n : ℕ}
    (hnlo : 290 ≤ n) (hnhi : n < 322) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec2a {n : ℕ}
    (hnlo : 322 ≤ n) (hnhi : n < 354) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec2b {n : ℕ}
    (hnlo : 354 ≤ n) (hnhi : n < 386) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec3a {n : ℕ}
    (hnlo : 386 ≤ n) (hnhi : n < 418) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec3b {n : ℕ}
    (hnlo : 418 ≤ n) (hnhi : n < 450) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  interval_cases n <;>
    norm_num [IsFirstPrimeAfter, certifiedPrimeAfterLarge,
      certifiedPrimeAfterLargeTable0, certifiedPrimeAfterLargeTable1,
      certifiedPrimeAfterLargeTable2, certifiedPrimeAfterLargeTable3] <;> try norm_num
  all_goals
    intro r hr hnr
    by_contra h
    interval_cases r <;> norm_num at hr

private lemma certifiedPrimeAfterLarge_spec {n : ℕ}
    (hnlo : 194 ≤ n) (hnhi : n < 450) :
    IsFirstPrimeAfter n (certifiedPrimeAfterLarge n) := by
  by_cases h258 : n < 258
  · exact certifiedPrimeAfterLarge_spec0 hnlo h258
  by_cases h290 : n < 290
  · exact certifiedPrimeAfterLarge_spec1a (by omega) h290
  by_cases h322 : n < 322
  · exact certifiedPrimeAfterLarge_spec1b (by omega) h322
  by_cases h354 : n < 354
  · exact certifiedPrimeAfterLarge_spec2a (by omega) h354
  by_cases h386 : n < 386
  · exact certifiedPrimeAfterLarge_spec2b (by omega) h386
  by_cases h418 : n < 418
  · exact certifiedPrimeAfterLarge_spec3a (by omega) h418
  · exact certifiedPrimeAfterLarge_spec3b (by omega) hnhi

private lemma certifiedLargeSmallSieve0 {n : ℕ} (hnlo : 194 ≤ n) (hnhi : n < 224) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve1 {n : ℕ} (hnlo : 224 ≤ n) (hnhi : n < 254) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve2 {n : ℕ} (hnlo : 254 ≤ n) (hnhi : n < 284) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve3 {n : ℕ} (hnlo : 284 ≤ n) (hnhi : n < 314) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve4a {n : ℕ} (hnlo : 314 ≤ n) (hnhi : n < 324) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve4b {n : ℕ} (hnlo : 324 ≤ n) (hnhi : n < 334) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve4c {n : ℕ} (hnlo : 334 ≤ n) (hnhi : n < 344) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve5a {n : ℕ} (hnlo : 344 ≤ n) (hnhi : n < 354) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve5b {n : ℕ} (hnlo : 354 ≤ n) (hnhi : n < 364) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve5c {n : ℕ} (hnlo : 364 ≤ n) (hnhi : n < 374) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve6a {n : ℕ} (hnlo : 374 ≤ n) (hnhi : n < 384) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve6b {n : ℕ} (hnlo : 384 ≤ n) (hnhi : n < 394) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve6c {n : ℕ} (hnlo : 394 ≤ n) (hnhi : n < 404) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve7a {n : ℕ} (hnlo : 404 ≤ n) (hnhi : n < 414) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve7b {n : ℕ} (hnlo : 414 ≤ n) (hnhi : n < 424) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve7c {n : ℕ} (hnlo : 424 ≤ n) (hnhi : n ≤ 433) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  interval_cases n <;>
    norm_num [certifiedPrimeAfterLarge, certifiedPrimeAfterLargeTable0,
      certifiedPrimeAfterLargeTable1, certifiedPrimeAfterLargeTable2,
      certifiedPrimeAfterLargeTable3]

private lemma certifiedLargeSmallSieve {n : ℕ} (hnlo : 194 ≤ n) (hnhi : n ≤ 433) :
    ¬certifiedPrimeAfterLarge n * certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) ∣
      n.factorial + 1 := by
  by_cases h224 : n < 224
  · exact certifiedLargeSmallSieve0 hnlo h224
  by_cases h254 : n < 254
  · exact certifiedLargeSmallSieve1 (by omega) h254
  by_cases h284 : n < 284
  · exact certifiedLargeSmallSieve2 (by omega) h284
  by_cases h314 : n < 314
  · exact certifiedLargeSmallSieve3 (by omega) h314
  by_cases h324 : n < 324
  · exact certifiedLargeSmallSieve4a (by omega) h324
  by_cases h334 : n < 334
  · exact certifiedLargeSmallSieve4b (by omega) h334
  by_cases h344 : n < 344
  · exact certifiedLargeSmallSieve4c (by omega) h344
  by_cases h354 : n < 354
  · exact certifiedLargeSmallSieve5a (by omega) h354
  by_cases h364 : n < 364
  · exact certifiedLargeSmallSieve5b (by omega) h364
  by_cases h374 : n < 374
  · exact certifiedLargeSmallSieve5c (by omega) h374
  by_cases h384 : n < 384
  · exact certifiedLargeSmallSieve6a (by omega) h384
  by_cases h394 : n < 394
  · exact certifiedLargeSmallSieve6b (by omega) h394
  by_cases h404 : n < 404
  · exact certifiedLargeSmallSieve6c (by omega) h404
  by_cases h414 : n < 414
  · exact certifiedLargeSmallSieve7a (by omega) h414
  by_cases h424 : n < 424
  · exact certifiedLargeSmallSieve7b (by omega) h424
  · exact certifiedLargeSmallSieve7c (by omega) hnhi

/-- Kernel-checked exclusion of the intermediate range `194 ≤ n ≤ 433`. -/
lemma indexedFiniteSmallSieveThrough433 {n k : ℕ}
    (hnlo : 194 ≤ n) (hnhi : n ≤ 433)
    (hlo : lowerEndpoint k ≤ n) (hhi : n < primeAt k) :
    ¬primeAt k * primeAt (k + 1) ∣ n.factorial + 1 := by
  have hpSpec := certifiedPrimeAfterLarge_spec hnlo (by omega : n < 450)
  have hpIndexed : IsFirstPrimeAfter n (primeAt k) :=
    primeAt_isFirstPrimeAfter hlo hhi
  have hpEq : certifiedPrimeAfterLarge n = primeAt k :=
    IsFirstPrimeAfter.unique hpSpec hpIndexed
  have hp439 : certifiedPrimeAfterLarge n ≤ 439 :=
    hpSpec.2.2 439 (by norm_num) (by omega)
  have hpBounds : 194 ≤ certifiedPrimeAfterLarge n ∧ certifiedPrimeAfterLarge n < 450 := by
    omega
  have hqSpec := certifiedPrimeAfterLarge_spec hpBounds.1 hpBounds.2
  have hqIndexed : IsFirstPrimeAfter (primeAt k) (primeAt (k + 1)) :=
    next_primeAt_isFirstPrimeAfter k
  have hqEq : certifiedPrimeAfterLarge (certifiedPrimeAfterLarge n) =
      primeAt (k + 1) := by
    apply IsFirstPrimeAfter.unique hqSpec
    simpa [hpEq] using hqIndexed
  have hqEq' : certifiedPrimeAfterLarge (primeAt k) = primeAt (k + 1) := by
    rw [← hpEq]
    exact hqEq
  simpa only [hpEq, hqEq'] using certifiedLargeSmallSieve hnlo hnhi

/-- Unique factorization specialized to a number whose prime divisors belong to a
two-element set.  Exponents are allowed to be zero; positivity is proved later
from Luca's elementary size estimates. -/
lemma eq_prime_pow_mul_prime_pow_of_prime_divisors
    {N p q : ℕ} (hN : N ≠ 0) (hpq : p ≠ q)
    (hdiv : ∀ r, r.Prime → r ∣ N → r = p ∨ r = q) :
    ∃ a b : ℕ, N = p ^ a * q ^ b := by
  classical
  let a := N.factorization p
  let b := N.factorization q
  have hfac : N.factorization = Finsupp.single p a + Finsupp.single q b := by
    ext r
    by_cases hrp : r = p
    · subst r
      simp [a, b, hpq]
    by_cases hrq : r = q
    · subst r
      simp [a, b, hrp]
    have hrzero : N.factorization r = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hrprime : r.Prime
      · right
        left
        intro hrdvd
        exact (hdiv r hrprime hrdvd).elim hrp hrq
      · exact Or.inl hrprime
    simp [hrzero, hrp, hrq]
  refine ⟨a, b, ?_⟩
  calc
    N = N.factorization.prod (fun r e => r ^ e) :=
      (Nat.prod_factorization_pow_eq_self hN).symm
    _ = (Finsupp.single p a + Finsupp.single q b).prod (fun r e => r ^ e) := by
      rw [hfac]
    _ = (Finsupp.single p a).prod (fun r e => r ^ e) *
        (Finsupp.single q b).prod (fun r e => r ^ e) := by
      apply Finsupp.prod_add_index
      · simp
      · intro r _ x y
        exact pow_add r x y
    _ = p ^ a * q ^ b := by simp

/-- The divisor formulation of a solution yields Luca's equation
`n! + 1 = p_k^a p_{k+1}^b`, without yet asserting that the exponents are
positive. -/
lemma IsSolution.exists_factorization {n : ℕ} (hn : IsSolution n) :
    ∃ k a b : ℕ,
      lowerEndpoint k ≤ n ∧ n < primeAt k ∧
        n.factorial + 1 = primeAt k ^ a * primeAt (k + 1) ^ b := by
  rcases hn with ⟨_, k, hkn, hnk, hdiv⟩
  have hne : n.factorial + 1 ≠ 0 := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_ne_zero n.factorial
  obtain ⟨a, b, hab⟩ :=
    eq_prime_pow_mul_prime_pow_of_prime_divisors hne (primeAt_ne_succ k) hdiv
  exact ⟨k, a, b, hkn, hnk, hab⟩

/-- Luca's elementary lemma in the exact indexed formulation: for a solution
with `n ≥ 12`, both exponents in the two-prime factorization are positive. -/
lemma IsSolution.exists_positive_factorization {n : ℕ}
    (hnlo : 12 ≤ n) (hn : IsSolution n) :
    ∃ k a b : ℕ,
      lowerEndpoint k ≤ n ∧ n < primeAt k ∧
        0 < a ∧ 0 < b ∧
          n.factorial + 1 = primeAt k ^ a * primeAt (k + 1) ^ b := by
  obtain ⟨k, a, b, hlo, hhi, heq⟩ := hn.exists_factorization
  have hpfirst : IsFirstPrimeAfter n (primeAt k) :=
    primeAt_isFirstPrimeAfter hlo hhi
  have hqfirst : IsFirstPrimeAfter (primeAt k) (primeAt (k + 1)) :=
    next_primeAt_isFirstPrimeAfter k
  have hbounds := first_two_primes_le_four_mul hpfirst hqfirst (by omega)
  have hp4 : primeAt k ≤ 4 * n := by omega
  have hnq : n < primeAt (k + 1) :=
    hhi.trans (primeAt_strictMono (Nat.lt_succ_self k))
  have haPos : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    simp only [pow_zero, one_mul] at heq
    have hbLt : b < n := pure_power_exponent_lt (by omega) hnq heq
    by_cases hn64 : n < 64
    · exact (indexed_finite_no_pure_power hnlo hn64 hlo hhi hbLt).2 heq
    · exact no_large_factorial_add_one_prime_power (by omega)
        (primeAt_prime (k + 1)) hnq hbounds.2 heq
  have hbPos : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
    subst b
    simp only [pow_zero, mul_one] at heq
    have haLt : a < n := pure_power_exponent_lt (by omega) hhi heq
    by_cases hn64 : n < 64
    · exact (indexed_finite_no_pure_power hnlo hn64 hlo hhi haLt).1 heq
    · exact no_large_factorial_add_one_prime_power (by omega)
        (primeAt_prime k) hhi hp4 heq
  exact ⟨k, a, b, hlo, hhi, haPos, hbPos, heq⟩

lemma erdos1058_not_solution_twelve_to_193 {n : ℕ}
    (hnlo : 12 ≤ n) (hnhi : n ≤ 193) : ¬IsSolution n := by
  intro hn
  obtain ⟨k, a, b, hlo, hhi, ha, hb, heq⟩ := hn.exists_positive_factorization hnlo
  have hpdiv : primeAt k ∣ primeAt k ^ a := dvd_pow_self _ ha.ne'
  have hqdiv : primeAt (k + 1) ∣ primeAt (k + 1) ^ b := dvd_pow_self _ hb.ne'
  have hpqdiv : primeAt k * primeAt (k + 1) ∣ n.factorial + 1 := by
    rw [heq]
    exact Nat.mul_dvd_mul hpdiv hqdiv
  rcases indexedFiniteSmallNSieve hnlo hnhi hlo hhi with hn18 | hnot
  · subst n
    exact erdos1058_not_solution_eighteen hn
  · exact hnot hpqdiv

lemma erdos1058_not_solution_194_to_433 {n : ℕ}
    (hnlo : 194 ≤ n) (hnhi : n ≤ 433) : ¬IsSolution n := by
  intro hn
  obtain ⟨k, a, b, hlo, hhi, ha, hb, heq⟩ := hn.exists_positive_factorization (by omega)
  have hpdiv : primeAt k ∣ primeAt k ^ a := dvd_pow_self _ ha.ne'
  have hqdiv : primeAt (k + 1) ∣ primeAt (k + 1) ^ b := dvd_pow_self _ hb.ne'
  have hpqdiv : primeAt k * primeAt (k + 1) ∣ n.factorial + 1 := by
    rw [heq]
    exact Nat.mul_dvd_mul hpdiv hqdiv
  exact indexedFiniteSmallSieveThrough433 hnlo hnhi hlo hhi hpqdiv

lemma erdos1058_solution_one : IsSolution 1 := by
  refine ⟨by norm_num, 0, by norm_num [lowerEndpoint], by norm_num [primeAt], ?_⟩
  intro r hr hrdvd
  left
  have hr2 : r ∣ 2 := by
    norm_num at hrdvd ⊢
    exact hrdvd
  simpa [primeAt] using (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hr2

lemma erdos1058_solution_two : IsSolution 2 := by
  refine ⟨by norm_num, 1, by norm_num [lowerEndpoint, primeAt],
    by norm_num [primeAt], ?_⟩
  intro r hr hrdvd
  left
  have hr3 : r ∣ 3 := by
    norm_num at hrdvd ⊢
    exact hrdvd
  simpa [primeAt] using (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hr3

lemma erdos1058_solution_three : IsSolution 3 := by
  refine ⟨by norm_num, 2, by norm_num [lowerEndpoint, primeAt],
    by norm_num [primeAt], ?_⟩
  intro r hr hrdvd
  right
  have hr7 : r ∣ 7 := by
    norm_num at hrdvd ⊢
    exact hrdvd
  simpa [primeAt] using (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hr7

lemma erdos1058_solution_four : IsSolution 4 := by
  refine ⟨by norm_num, 2, by norm_num [lowerEndpoint, primeAt],
    by norm_num [primeAt], ?_⟩
  intro r hr hrdvd
  left
  have hr25 : r ∣ 5 ^ 2 := by
    norm_num at hrdvd ⊢
    exact hrdvd
  simpa [primeAt] using Nat.prime_eq_prime_of_dvd_pow hr (by norm_num) hr25

lemma erdos1058_solution_five : IsSolution 5 := by
  refine ⟨by norm_num, 3, by norm_num [lowerEndpoint, primeAt],
    by norm_num [primeAt], ?_⟩
  intro r hr hrdvd
  right
  have hr121 : r ∣ 11 ^ 2 := by
    norm_num at hrdvd ⊢
    exact hrdvd
  simpa [primeAt] using Nat.prime_eq_prime_of_dvd_pow hr (by norm_num) hr121

theorem erdos1058_small_solutions {n : ℕ} (hnpos : 0 < n) (hn : n ≤ 5) :
    IsSolution n := by
  interval_cases n <;>
    simp_all only [erdos1058_solution_one, erdos1058_solution_two,
      erdos1058_solution_three, erdos1058_solution_four, erdos1058_solution_five]

/-- Final assembly with the two remaining substantial inputs exposed at their
exact types.  Once `LargePrimeBound` and `LargeCubicCertificate` are proved,
this theorem immediately yields the unconditional classification. -/
theorem erdos1058_classification_of_large_certificates
    (hbound : LargePrimeBound) (hcertificate : LargeCubicCertificate) (n : ℕ) :
    IsSolution n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
  constructor
  · intro hn
    have hnpos : 0 < n := hn.1
    by_cases hn5 : n ≤ 5
    · omega
    have hn6 : 6 ≤ n := by omega
    by_cases hn12 : n < 12
    · interval_cases n
      · exact (erdos1058_not_solution_six hn).elim
      · exact (erdos1058_not_solution_seven hn).elim
      · exact (erdos1058_not_solution_eight hn).elim
      · exact (erdos1058_not_solution_nine hn).elim
      · exact (erdos1058_not_solution_ten hn).elim
      · exact (erdos1058_not_solution_eleven hn).elim
    have hnlo : 12 ≤ n := by omega
    by_cases hn194 : n < 194
    · exact (erdos1058_not_solution_twelve_to_193 hnlo (by omega) hn).elim
    by_cases hn434 : n < 434
    · exact (erdos1058_not_solution_194_to_433 (by omega) (by omega) hn).elim
    obtain ⟨k, a, b, hlo, hhi, ha, hb, heq⟩ :=
      hn.exists_positive_factorization hnlo
    have hpfirst : IsFirstPrimeAfter n (primeAt k) :=
      primeAt_isFirstPrimeAfter hlo hhi
    have hqfirst : IsFirstPrimeAfter (primeAt k) (primeAt (k + 1)) :=
      next_primeAt_isFirstPrimeAfter k
    have hqbound : primeAt (k + 1) < 36000000 :=
      hbound n (primeAt k) (primeAt (k + 1)) a b (by omega)
        hpfirst hqfirst ha hb heq
    have hsieve : CubicSieveHolds (primeAt k) (primeAt (k + 1)) :=
      hcertificate (primeAt k) (primeAt (k + 1)) (by omega) (primeAt_prime k)
        hqfirst hqbound
    obtain ⟨x, hx⟩ := exists_cube_sub_one_of_cubicSieve (by omega)
      (primeAt_prime k) hhi (primeAt_prime (k + 1))
      (hhi.trans (primeAt_strictMono (Nat.lt_succ_self k))) heq hsieve
    exact (factorial_ne_cube_sub_one_of_ge_194 (by omega) hx).elim
  · intro hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact erdos1058_solution_one
    · exact erdos1058_solution_two
    · exact erdos1058_solution_three
    · exact erdos1058_solution_four
    · exact erdos1058_solution_five

end

end Erdos1058
