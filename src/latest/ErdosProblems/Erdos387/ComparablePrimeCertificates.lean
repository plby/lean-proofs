/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoprimeClassSieve
import ErdosProblems.Erdos387.AlmostPrimeExhaustion

/-!
# Two-prime CRT certificates

The comparable-prime event supplies distinct primes `q,r` and forbidden
residues `i,j`.  Their product is represented as a `TupleCertificate`: if
the residues agree, `q*r` occupies one coordinate; otherwise the two primes
occupy their respective coordinates.  This lets the generic rough-class
sieve count every resulting progression.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ

def primePairFactor {k : ℕ} (i j : Fin k) (q r : ℕ) (a : Fin k) : ℕ :=
  (if a = i then q else 1) * (if a = j then r else 1)

theorem primePairFactor_pos {k : ℕ} (i j : Fin k) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (a : Fin k) :
    0 < primePairFactor i j q r a := by
  unfold primePairFactor
  positivity

theorem primePairFactor_le_mul {k : ℕ} (i j : Fin k) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (a : Fin k) :
    primePairFactor i j q r a ≤ q * r := by
  unfold primePairFactor
  split_ifs <;> simp_all <;> nlinarith

theorem primePairFactor_pairwise {k : ℕ} (i j : Fin k) {q r : ℕ}
    (hqr : Nat.Coprime q r) (a b : Fin k) (hab : a ≠ b) :
    Nat.Coprime (primePairFactor i j q r a)
      (primePairFactor i j q r b) := by
  unfold primePairFactor
  split_ifs <;> simp_all
  · exact hqr
  · exact hqr.symm

theorem prod_primePairFactor {k : ℕ} (hk : 0 < k)
    (i j : Fin k) (q r : ℕ) :
    ∏ a : Fin k, primePairFactor i j q r a = q * r := by
  unfold primePairFactor
  rw [Finset.prod_mul_distrib]
  simp

noncomputable def primePairTupleCertificate
    {k X : ℕ} (hk : 0 < k) (i j : Fin k) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : Nat.Coprime q r)
    (hqrX : q * r ≤ X) : TupleCertificate k X := by
  classical
  refine ⟨fun a => ⟨primePairFactor i j q r a, ?_⟩, ?_, ?_⟩
  · exact Nat.lt_succ_iff.mpr
      ((primePairFactor_le_mul i j hq hr a).trans hqrX)
  · intro a
    exact primePairFactor_pos i j hq hr a
  · intro a b hab
    exact primePairFactor_pairwise i j hqr a b hab

theorem primePairTupleCertificate_factor
    {k X : ℕ} (hk : 0 < k) (i j : Fin k) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : Nat.Coprime q r)
    (hqrX : q * r ≤ X) (a : Fin k) :
    (primePairTupleCertificate hk i j hq hr hqr hqrX).factor a =
      primePairFactor i j q r a := rfl

theorem primePairTupleCertificate_value
    {k X : ℕ} (hk : 0 < k) (i j : Fin k) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : Nat.Coprime q r)
    (hqrX : q * r ≤ X) :
    (primePairTupleCertificate hk i j hq hr hqr hqrX).value = q * r := by
  unfold TupleCertificate.value
  simp only [primePairTupleCertificate_factor]
  exact prod_primePairFactor hk i j q r

theorem coprime_refinementModulus_prime_of_two_mul_k_le
    {B K q : ℕ} (S : BPZSection6Input B K) (hq : q.Prime)
    (hlower : 2 * S.k ≤ q) :
    Nat.Coprime (refinementModulus S) q := by
  rw [Nat.coprime_comm]
  exact hq.coprime_iff_not_dvd.mpr fun hqM =>
    (not_lt_of_ge hlower)
      (prime_lt_two_mul_k_of_dvd_refinementModulus S hq hqM)

noncomputable def primePairRefinedTupleCertificate
    {B K X q r : ℕ} (S : BPZSection6Input B K)
    (i j : Fin S.k) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hlowerQ : 2 * S.k ≤ q) (hlowerR : 2 * S.k ≤ r)
    (hqrX : q * r ≤ X) : RefinedTupleCertificate S X := by
  let C := primePairTupleCertificate (by have := S.hk3; omega) i j
    hq.pos hr.pos ((Nat.coprime_primes hq hr).2 hqr) hqrX
  refine ⟨C, ?_⟩
  rw [primePairTupleCertificate_value]
  exact Nat.Coprime.mul_right
    (coprime_refinementModulus_prime_of_two_mul_k_le S hq hlowerQ)
    (coprime_refinementModulus_prime_of_two_mul_k_le S hr hlowerR)

/-- The finite parameter space used to cover the comparable-prime event.
The two residue coordinates are retained even when they coincide; in that
case both primes are placed in the same tuple coordinate. -/
structure ComparablePrimeSource (k secondMin gap medium : ℕ) where
  i : Fin k
  j : Fin k
  r : Fin (medium + 1)
  q : Fin (medium + 1)
  r_prime : r.val.Prime
  q_prime : q.val.Prime
  second_lt_r : secondMin < r.val
  r_lt_q : r.val < q.val
  q_lt_gap_mul_r : q.val < gap * r.val

noncomputable instance comparablePrimeSourceFintype
    (k secondMin gap medium : ℕ) :
    Fintype (ComparablePrimeSource k secondMin gap medium) := by
  classical
  let f : ComparablePrimeSource k secondMin gap medium →
      Fin k × Fin k × Fin (medium + 1) × Fin (medium + 1) :=
    fun s => (s.i, s.j, s.r, s.q)
  exact Fintype.ofInjective f (by
    intro a b hab
    cases a
    cases b
    simp only [f, Prod.mk.injEq] at hab
    simp_all)

theorem card_comparablePrimeSource_le
    (k secondMin gap medium : ℕ) :
    Fintype.card (ComparablePrimeSource k secondMin gap medium) ≤
      k ^ 2 * (medium + 1) ^ 2 := by
  classical
  let encode : ComparablePrimeSource k secondMin gap medium →
      Fin k × Fin k × Fin (medium + 1) × Fin (medium + 1) :=
    fun s => (s.i, s.j, s.r, s.q)
  have hencode : Function.Injective encode := by
    intro a b hab
    cases a
    cases b
    simp only [encode, Prod.mk.injEq] at hab
    simp_all
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [Fintype.card_prod, Fintype.card_fin, pow_two, mul_assoc,
    mul_left_comm, mul_comm] using hcard

theorem ComparablePrimeSource.r_le_medium
    {k secondMin gap medium : ℕ}
    (s : ComparablePrimeSource k secondMin gap medium) :
    s.r.val ≤ medium := by
  exact Nat.lt_succ_iff.mp s.r.isLt

theorem ComparablePrimeSource.q_le_medium
    {k secondMin gap medium : ℕ}
    (s : ComparablePrimeSource k secondMin gap medium) :
    s.q.val ≤ medium := by
  exact Nat.lt_succ_iff.mp s.q.isLt

theorem ComparablePrimeSource.product_le
    {k secondMin gap medium X : ℕ}
    (s : ComparablePrimeSource k secondMin gap medium)
    (hmedium : medium * medium ≤ X) :
    s.q.val * s.r.val ≤ X := by
  exact (Nat.mul_le_mul s.q_le_medium s.r_le_medium).trans hmedium

noncomputable def ComparablePrimeSource.certificate
    {B K X secondMin gap medium : ℕ} (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin) (hmedium : medium * medium ≤ X)
    (s : ComparablePrimeSource S.k secondMin gap medium) :
    RefinedTupleCertificate S X :=
  primePairRefinedTupleCertificate S s.i s.j s.q_prime s.r_prime
    (Nat.ne_of_gt s.r_lt_q)
    (hsecond.trans (s.second_lt_r.le.trans s.r_lt_q.le))
    (hsecond.trans s.second_lt_r.le)
    (s.product_le hmedium)

theorem ComparablePrimeSource.certificate_value
    {B K X secondMin gap medium : ℕ} (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin) (hmedium : medium * medium ≤ X)
    (s : ComparablePrimeSource S.k secondMin gap medium) :
    (s.certificate S hsecond hmedium).val.value = s.q.val * s.r.val := by
  unfold ComparablePrimeSource.certificate primePairRefinedTupleCertificate
  simp only [primePairTupleCertificate_value]

theorem ComparablePrimeSource.certificate_rough
    {B K X z secondMin gap medium : ℕ} (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin) (hmedium : medium * medium ≤ X)
    (hz : z ≤ secondMin)
    (s : ComparablePrimeSource S.k secondMin gap medium) :
    IsZRough z (s.certificate S hsecond hmedium).val.value := by
  rw [s.certificate_value S hsecond hmedium]
  intro p hp hpz hpqr
  rcases hp.dvd_mul.mp hpqr with hpq | hpr
  · have hpEq : p = s.q.val :=
      ((s.q_prime.dvd_iff_eq hp.ne_one).mp hpq).symm
    exact (not_lt_of_ge
      (hz.trans (s.second_lt_r.le.trans s.r_lt_q.le)))
      (hpEq ▸ hpz)
  · have hpEq : p = s.r.val :=
      ((s.r_prime.dvd_iff_eq hp.ne_one).mp hpr).symm
    exact (not_lt_of_ge (hz.trans s.second_lt_r.le)) (hpEq ▸ hpz)

/-- Every comparable-prime error belongs to one of the finite two-prime
CRT classes.  This is the exact set-theoretic reduction preceding the
reciprocal prime-pair estimate. -/
theorem refinedComparablePrimeErrors_subset_primePairClasses
    {B K X z secondMin gap medium : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin)
    (hmediumHalf : medium * medium ≤ X / 2) :
    RefinedComparablePrimeErrors S X z secondMin gap medium ⊆
      (Finset.univ : Finset
        (ComparablePrimeSource S.k secondMin gap medium)).biUnion
        (fun s => SiftedSwitchedClassCandidates
          (s.certificate S hsecond
            (hmediumHalf.trans (Nat.div_le_self X 2))) z) := by
  classical
  intro n hn
  rw [RefinedComparablePrimeErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hn
  obtain ⟨⟨⟨hnIoc, hkn, hnRefined⟩, hnRough⟩,
    r, q, hr, hq, hsecondR, hrq, hqMedium, hqGap,
      hrChoose, hqChoose⟩ := hn
  have hkr : S.k < r := by omega
  have hkq : S.k < q := by omega
  obtain ⟨ir, hir, hirMod⟩ :=
    (prime_dvd_choose_iff_exists_mod_eq hr hkr hkn.le).mp hrChoose
  obtain ⟨iq, hiq, hiqMod⟩ :=
    (prime_dvd_choose_iff_exists_mod_eq hq hkq hkn.le).mp hqChoose
  let i : Fin S.k := ⟨iq, hiq⟩
  let j : Fin S.k := ⟨ir, hir⟩
  let r' : Fin (medium + 1) := ⟨r, by omega⟩
  let q' : Fin (medium + 1) := ⟨q, by omega⟩
  let s : ComparablePrimeSource S.k secondMin gap medium :=
    ⟨i, j, r', q', hr, hq, hsecondR, hrq, hqGap⟩
  have hmediumX : medium * medium ≤ X :=
    hmediumHalf.trans (Nat.div_le_self X 2)
  have hqShift : q ∣ n - i.val := by
    apply (Nat.modEq_iff_dvd' (Nat.le_of_lt (i.isLt.trans hkn))).mp
    simpa [i, hiqMod] using Nat.mod_modEq n q
  have hrShift : r ∣ n - j.val := by
    apply (Nat.modEq_iff_dvd' (Nat.le_of_lt (j.isLt.trans hkn))).mp
    simpa [j, hirMod] using Nat.mod_modEq n r
  have hvalueLeN :
      (s.certificate S hsecond hmediumX).val.value ≤ n := by
    rw [s.certificate_value S hsecond hmediumX]
    exact (s.product_le hmediumHalf).trans
      (Finset.mem_Ioc.mp hnIoc).1.le
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_univ s, ?_⟩
  rw [SiftedSwitchedClassCandidates, Finset.mem_filter]
  refine ⟨(RefinedTupleCertificate.mem_classIoc_iff
    (s.certificate S hsecond hmediumX)).mpr ⟨hnIoc,
      (refinement_progression_dvd_iff_modEq S).mp hnRefined, ?_⟩,
    hnRough⟩
  apply (s.certificate S hsecond hmediumX).val.ambient_modEq_crtResidue
    hkn.le hvalueLeN
  intro a
  change primePairFactor i j q r a ∣ n - a.val
  unfold primePairFactor
  split_ifs with hai haj
  · subst a
    have hij : i = j := by simpa using haj
    have hrShiftI : r ∣ n - i.val := by simpa [hij] using hrShift
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hq hr).2 (by omega)) hqShift hrShiftI
  · subst a
    simpa using hqShift
  · subst a
    simpa using hrShift
  · simp

/-- Finite quantitative form of the comparable-prime reduction.  Each
source contributes the standard refined Brun main term divided by the two
prime moduli, together with the uniform endpoint error. -/
theorem refinedComparablePrimeErrors_card_le_primePairBrunSum
    {B K X z secondMin gap medium L : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin)
    (hmediumHalf : medium * medium ≤ X / 2)
    (hzSecond : z ≤ secondMin)
    (hX : S.k ≤ X / 2) (hk : 0 < S.k) (hz : 1 ≤ z)
    (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum
        (brunUpperWeight L)) :
    ((RefinedComparablePrimeErrors S X z secondMin gap medium).card : ℝ) ≤
      ∑ s : ComparablePrimeSource S.k secondMin gap medium,
        ((((X - X / 2 : ℕ) : ℝ) /
              (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
            (refinedBinomialBoundingSieve S X z).mainSum
              (brunUpperWeight L) +
          (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L) := by
  classical
  let T := (Finset.univ : Finset
    (ComparablePrimeSource S.k secondMin gap medium))
  let hmediumX : medium * medium ≤ X :=
    hmediumHalf.trans (Nat.div_le_self X 2)
  have hsubset : RefinedComparablePrimeErrors S X z secondMin gap medium ⊆
      T.biUnion (fun s => SiftedSwitchedClassCandidates
        (s.certificate S hsecond hmediumX) z) := by
    simpa [T, hmediumX] using
      refinedComparablePrimeErrors_subset_primePairClasses
        S hsecond hmediumHalf
  have hcardNat := Finset.card_le_card hsubset
  have hunionNat :
      (T.biUnion fun s => SiftedSwitchedClassCandidates
        (s.certificate S hsecond hmediumX) z).card ≤
        ∑ s ∈ T, (SiftedSwitchedClassCandidates
          (s.certificate S hsecond hmediumX) z).card :=
    Finset.card_biUnion_le
  have hleft :
      ((RefinedComparablePrimeErrors S X z secondMin gap medium).card : ℝ) ≤
        ∑ s ∈ T, ((SiftedSwitchedClassCandidates
          (s.certificate S hsecond hmediumX) z).card : ℝ) := by
    exact_mod_cast hcardNat.trans hunionNat
  change _ ≤ ∑ s ∈ T,
    ((((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
        (refinedBinomialBoundingSieve S X z).mainSum
          (brunUpperWeight L) +
      (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L)
  refine hleft.trans (Finset.sum_le_sum fun s _hs => ?_)
  have hs := siftedSwitchedClassCandidates_card_le_brun_of_rough
    (s.certificate S hsecond hmediumX)
    (s.certificate_rough S hsecond hmediumX hzSecond)
    hX hk hz hL hmainNonneg
  rw [s.certificate_value S hsecond hmediumX] at hs
  exact hs

end CoverBPZ

end Erdos387
