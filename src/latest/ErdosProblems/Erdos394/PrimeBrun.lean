import ErdosProblems.Erdos394.FiniteBrun
import ErdosProblems.Erdos394.ProgressionSum
import ErdosProblems.Erdos394.SymmetricTail

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Specializing the finite Brun sieve to prime divisibility in a progression
-/

open Nat Finset

namespace Erdos394

/-- For a set of distinct primes, divisibility by the product is equivalent to
divisibility by every prime in the set. -/
theorem prod_dvd_iff_forall_prime {P T : Finset ℕ} (hTP : T ⊆ P)
    (hprime : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (∏ p ∈ T, p) ∣ m ↔ ∀ p ∈ T, p ∣ m := by
  constructor
  · intro hprod p hp
    exact (Finset.dvd_prod_of_mem (fun r : ℕ ↦ r) hp).trans hprod
  · intro hall
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp r hr hne
      apply Nat.coprime_iff_isRelPrime.mp
      rw [(hprime p (hTP hp)).coprime_iff_not_dvd]
      intro hpr
      rcases (Nat.dvd_prime (hprime r (hTP hr))).mp hpr with hp1 | hpeq
      · exact (hprime p (hTP hp)).ne_one hp1
      · exact hne hpeq
    · exact hall

/-- Prime divisors from `P` that divide `m`. -/
def badPrimeSet (P : Finset ℕ) (m : ℕ) : Finset ℕ :=
  P.filter (fun p ↦ p ∣ m)

/-- A subset lies in the bad-prime set exactly when its prime product divides
`m`. -/
theorem subset_badPrimeSet_iff_prod_dvd {P T : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (m : ℕ) :
    T ⊆ badPrimeSet P m ↔ T ⊆ P ∧ (∏ p ∈ T, p) ∣ m := by
  constructor
  · intro hT
    have hTP : T ⊆ P := by
      intro p hp
      exact (Finset.mem_filter.mp (hT hp)).1
    refine ⟨hTP, (prod_dvd_iff_forall_prime hTP hprime m).2 ?_⟩
    intro p hp
    exact (Finset.mem_filter.mp (hT hp)).2
  · rintro ⟨hTP, hprod⟩ p hp
    exact Finset.mem_filter.mpr ⟨hTP hp,
      (prod_dvd_iff_forall_prime hTP hprime m).1 hprod p hp⟩

/-- CRT representative for `m≡h (mod q)` and `m≡0 (mod d)`. -/
def intersectionResidue {q d : ℕ} (hcop : q.Coprime d) (h : ℕ) : ℕ :=
  (Nat.chineseRemainder hcop h 0).1

/-- The CRT representative lies below the product modulus. -/
theorem intersectionResidue_lt_mul {q d : ℕ} (hcop : q.Coprime d)
    (hq : 0 < q) (hd : 0 < d) (h : ℕ) :
    intersectionResidue hcop h < q * d := by
  exact Nat.chineseRemainder_lt_mul hcop h 0 hq.ne' hd.ne'

/-- The conjunction of a residue condition and a coprime divisibility
condition is one residue class modulo the product. -/
theorem mod_eq_and_dvd_iff_mod_mul_eq {q d h m : ℕ}
    (hcop : q.Coprime d) (hq : 0 < q) (hd : 0 < d) (hh : h < q) :
    (m % q = h ∧ d ∣ m) ↔
      m % (q * d) = intersectionResidue hcop h := by
  let r := intersectionResidue hcop h
  have hr : r < q * d := intersectionResidue_lt_mul hcop hq hd h
  have hrq : r ≡ h [MOD q] := (Nat.chineseRemainder hcop h 0).2.1
  have hrd : r ≡ 0 [MOD d] := (Nat.chineseRemainder hcop h 0).2.2
  constructor
  · rintro ⟨hmq, hdm⟩
    have hmq' : m ≡ h [MOD q] := by
      change m % q = h % q
      simpa [Nat.mod_eq_of_lt hh] using hmq
    have hmd' : m ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdm
    have hmr : m ≡ r [MOD q * d] :=
      Nat.chineseRemainder_modEq_unique hcop hmq' hmd'
    change m % (q * d) = r % (q * d) at hmr
    simpa [Nat.mod_eq_of_lt hr] using hmr
  · intro hm
    have hmr : m ≡ r [MOD q * d] := by
      change m % (q * d) = r % (q * d)
      simpa [Nat.mod_eq_of_lt hr] using hm
    have hmq' : m ≡ h [MOD q] :=
      (hmr.of_dvd (dvd_mul_right q d)).trans hrq
    have hmd' : m ≡ 0 [MOD d] :=
      (hmr.of_dvd (dvd_mul_left d q)).trans hrd
    refine ⟨?_, Nat.modEq_zero_iff_dvd.mp hmd'⟩
    change m % q = h % q at hmq'
    simpa [Nat.mod_eq_of_lt hh] using hmq'

/-- Filtering a progression by divisibility by a prime product produces the
CRT progression modulo the product modulus. -/
theorem filter_residueClass_bad_eq_residueClass_mul
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcop : q.Coprime (∏ p ∈ T, p)) :
    (residueClassUpTo M q h).filter (fun m ↦ T ⊆ badPrimeSet P m) =
      residueClassUpTo M (q * ∏ p ∈ T, p)
        (intersectionResidue hcop h) := by
  let d := ∏ p ∈ T, p
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hTP hp)).pos
  ext m
  simp only [Finset.mem_filter, residueClassUpTo, Finset.mem_range]
  constructor
  · rintro ⟨⟨hmM, hmq⟩, hmT⟩
    have hdm : d ∣ m :=
      (subset_badPrimeSet_iff_prod_dvd hprime m).mp hmT |>.2
    refine ⟨hmM, ?_⟩
    exact (mod_eq_and_dvd_iff_mod_mul_eq hcop hq hd hh).mp ⟨hmq, hdm⟩
  · rintro ⟨hmM, hmqd⟩
    have hpair := (mod_eq_and_dvd_iff_mod_mul_eq hcop hq hd hh).mpr hmqd
    refine ⟨⟨hmM, hpair.1⟩, ?_⟩
    exact (subset_badPrimeSet_iff_prod_dvd hprime m).mpr ⟨hTP, hpair.2⟩

/-- The subset mass in the prime sieve is one weighted CRT residue-class sum. -/
theorem subsetMass_prime_progression_eq
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcop : q.Coprime (∏ p ∈ T, p)) :
    subsetMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) T =
      ∑ m ∈ residueClassUpTo M (q * ∏ p ∈ T, p)
        (intersectionResidue hcop h), (m : ℝ) := by
  unfold subsetMass
  rw [← Finset.sum_filter]
  rw [filter_residueClass_bad_eq_residueClass_mul hTP hprime hq hh hcop]

/-- A modulus coprime to every prime in `P` is coprime to every subset
product. -/
theorem coprime_prod_of_subset_primes {P T : Finset ℕ} (hTP : T ⊆ P)
    {q : ℕ} (hcopP : ∀ p ∈ P, q.Coprime p) :
    q.Coprime (∏ p ∈ T, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  exact hcopP p (hTP hp)

/-- The subset form of a truncated Euler product equals the alternating
sum of elementary symmetric functions. -/
theorem sum_truncatedSubsets_mul_prod_eq_alternatingPartial
    [DecidableEq α] (P : Finset α) (x : α → ℝ) (R : ℕ) :
    (∑ T ∈ truncatedSubsets P R,
      (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) =
      alternatingPartial P x R := by
  classical
  trans ∑ j ∈ Finset.range (R + 1),
      ∑ T ∈ (truncatedSubsets P R).filter (fun T ↦ T.card = j),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro T hT
    simp only [truncatedSubsets, Finset.mem_filter] at hT
    simp [hT.2]
  · unfold alternatingPartial
    apply Finset.sum_congr rfl
    intro j hj
    have hjR : j ≤ R := by simpa using hj
    have hfiber : (truncatedSubsets P R).filter (fun T ↦ T.card = j) =
        P.powersetCard j := by
      ext T
      simp only [truncatedSubsets, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hTP, _⟩, hcard⟩
        exact ⟨hTP, hcard⟩
      · rintro ⟨hTP, hcard⟩
        exact ⟨⟨hTP, hcard ▸ hjR⟩, hcard⟩
    rw [hfiber]
    unfold elementarySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [(Finset.mem_powersetCard.mp hT).2]

/-- Uniform main-term approximation for every subset mass in the prime sieve. -/
theorem subsetMass_prime_progression_approx
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {M q h : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) :
    |subsetMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
          (badPrimeSet P) T -
        ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          (1 / ((∏ p ∈ T, p : ℕ) : ℝ))| ≤ 2 * (M : ℝ) := by
  let d := ∏ p ∈ T, p
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hTP hp)).pos
  have hcop : q.Coprime d := coprime_prod_of_subset_primes hTP hcopP
  rw [subsetMass_prime_progression_eq hTP hprime hq hh hcop]
  have hres := abs_sum_residueClassUpTo_sub_area_le M (q * d)
    (intersectionResidue hcop h) (mul_pos hq hd)
    (intersectionResidue_lt_mul hcop hq hd h)
  have hmain : ((M : ℝ) ^ 2 / (2 * (q : ℝ))) * (1 / (d : ℝ)) =
      (M : ℝ) ^ 2 / (2 * ((q * d : ℕ) : ℝ)) := by
    have hqr : (q : ℝ) ≠ 0 := by positivity
    have hdr : (d : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    <;> ring
  rw [hmain]
  exact hres

/-- Reciprocal of a cast finite product is the product of reciprocals. -/
theorem one_div_cast_prod_eq_prod_one_div (T : Finset ℕ) :
    1 / ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, (1 / (p : ℝ)) := by
  push_cast
  simp [one_div, Finset.prod_inv_distrib]

/-- Fully explicit finite Brun inequality for prime divisibility inside one
residue class.  The remaining main factor is the alternating Euler truncation. -/
theorem primeSiftedMass_le_alternatingPartial_add_error
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q h R : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R) :
    siftedMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) ≤
      ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
  let A := residueClassUpTo M q h
  let w : ℕ → ℝ := fun m ↦ (m : ℝ)
  let bad := badPrimeSet P
  have hbad : ∀ m ∈ A, bad m ⊆ P := by
    intro m hm p hp
    exact (Finset.mem_filter.mp hp).1
  have hw : ∀ m ∈ A, 0 ≤ w m := by
    intro m _
    positivity
  have hbrun := siftedMass_le_brun P A w bad hbad hw R hR
  let I := truncatedSubsets P R
  let mass : Finset ℕ → ℝ := fun T ↦ subsetMass A w bad T
  let density : Finset ℕ → ℝ := fun T ↦
    1 / ((∏ p ∈ T, p : ℕ) : ℝ)
  let sign : Finset ℕ → ℝ := fun T ↦ (-1 : ℝ) ^ T.card
  let X : ℝ := (M : ℝ) ^ 2 / (2 * (q : ℝ))
  let E : ℝ := 2 * (M : ℝ)
  have hsign : ∀ T ∈ I, |sign T| = 1 := by
    intro T _
    simp [sign]
  have happrox : ∀ T ∈ I, |mass T - X * density T| ≤ E := by
    intro T hT
    have hTP : T ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact subsetMass_prime_progression_approx hTP hprime hq hh hcopP
  have herr := brun_signed_sum_le_main_add_error mass density sign X E
    (by dsimp [E]; positivity) hsign happrox
  have hdensity : (∑ T ∈ I, sign T * density T) =
      alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R := by
    calc
      (∑ T ∈ I, sign T * density T) =
          ∑ T ∈ truncatedSubsets P R,
            (-1 : ℝ) ^ T.card * ∏ p ∈ T, (1 / (p : ℝ)) := by
              apply Finset.sum_congr rfl
              intro T _
              simp only [sign, density]
              rw [one_div_cast_prod_eq_prod_one_div]
      _ = alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R :=
        sum_truncatedSubsets_mul_prod_eq_alternatingPartial P _ R
  change siftedMass A w bad ≤ _
  calc
    siftedMass A w bad ≤ ∑ T ∈ I, sign T * mass T := hbrun
    _ ≤ X * (∑ T ∈ I, sign T * density T) + I.card * E := herr
    _ = ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          alternatingPartial P (fun p ↦ 1 / (p : ℝ)) R +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
          rw [hdensity]

/-- Exact cardinality of the retained subset family. -/
theorem card_truncatedSubsets_eq_sum_choose [DecidableEq α]
    (P : Finset α) (R : ℕ) :
    (truncatedSubsets P R).card =
      ∑ j ∈ Finset.range (R + 1), P.card.choose j := by
  have h := sum_powerset_card_le P R (fun _j ↦ (1 : ℕ))
  simpa [truncatedSubsets] using h

/-- Crude but uniform retained-subset count used for the Brun error term. -/
theorem card_truncatedSubsets_le [DecidableEq α] (P : Finset α) (R y : ℕ)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) :
    (truncatedSubsets P R).card ≤ (R + 1) * y ^ R := by
  classical
  rw [card_truncatedSubsets_eq_sum_choose]
  calc
    (∑ j ∈ Finset.range (R + 1), P.card.choose j) ≤
        ∑ _j ∈ Finset.range (R + 1), y ^ R := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : j ≤ R := by simpa using hj
      exact (Nat.choose_le_pow P.card j).trans <|
        (Nat.pow_le_pow_left hPy j).trans
          (Nat.pow_le_pow_right (by omega : 0 < y) hjR)
    _ = (R + 1) * y ^ R := by simp

/-- If the factorial tail is below the local Euler product, the finite prime
sieve has main term at most twice the local density. -/
theorem primeSiftedMass_le_two_product_add_error
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {M q h R : ℕ} (hq : 0 < q) (hh : h < q)
    (hcopP : ∀ p ∈ P, q.Coprime p) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    siftedMass (residueClassUpTo M q h) (fun m : ℕ ↦ (m : ℝ))
        (badPrimeSet P) ≤
      ((M : ℝ) ^ 2 / (2 * (q : ℝ))) *
          (2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ))) +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
  have hbase := primeSiftedMass_le_alternatingPartial_add_error
    P hprime (M := M) (q := q) (h := h) (R := R) hq hh hcopP hR
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ P, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (hprime p hp).one_le
    exact (div_le_one (by positivity)).2 hp1
  have hpartial := alternatingPartial_le_two_mul_product_of_tail_le
    P (fun p ↦ 1 / (p : ℝ)) hx0 hx1 R hR htail
  have hX : 0 ≤ (M : ℝ) ^ 2 / (2 * (q : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpartial hX]

end Erdos394
