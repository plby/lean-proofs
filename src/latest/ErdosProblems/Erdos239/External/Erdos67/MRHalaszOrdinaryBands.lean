import ErdosProblems.Erdos239.External.Erdos67.MRHalaszBands

/-!
# Prime-band convolution for ordinary multiplicative coefficients

The cheap Halász decomposition does not require complete
multiplicativity: factors supported on complementary prime bands are
coprime.  This module upgrades the existing canonical band algebra to the
exact coefficient class occurring in the complex MR theorem.
-/

open scoped BigOperators LSeries.notation
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

theorem coprime_of_complementary_primeSupported
    (P : ℕ → Prop) {d e : ℕ}
    (hd : PrimeSupported P d)
    (he : PrimeSupported (fun p ↦ ¬ P p) e) :
    d.Coprime e := by
  rw [← Nat.disjoint_primeFactors hd.1 he.1]
  rw [Finset.disjoint_left]
  intro p hpd hpe
  exact (he.2 p hpe) (hd.2 p hpd)

theorem primeSupported_one (P : ℕ → Prop) :
    PrimeSupported P 1 := by
  constructor
  · norm_num
  · intro p hp
    simp at hp

theorem primeSupported_mul_iff
    (P : ℕ → Prop) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    PrimeSupported P (m * n) ↔
      PrimeSupported P m ∧ PrimeSupported P n := by
  unfold PrimeSupported
  rw [Nat.primeFactors_mul hm hn]
  constructor
  · intro h
    constructor
    · refine ⟨hm, ?_⟩
      intro p hp
      exact h.2 p (Finset.mem_union_left _ hp)
    · refine ⟨hn, ?_⟩
      intro p hp
      exact h.2 p (Finset.mem_union_right _ hp)
  · rintro ⟨hmP, hnP⟩
    refine ⟨mul_ne_zero hm hn, ?_⟩
    intro p hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact hmP.2 p hp
    · exact hnP.2 p hp

/-- Restricting an ordinary multiplicative coefficient to a prime band
preserves multiplicativity on the positive naturals. -/
theorem primeBandCoefficient_isMultiplicativeOnPositiveNat
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P] :
    IsMultiplicativeOnPositiveNat (primeBandCoefficient f P) := by
  constructor
  · simp [primeBandCoefficient, primeSupported_one P, hmul.1]
  · intro m n hm hn hcop
    have hiff := primeSupported_mul_iff P hm.ne' hn.ne'
    by_cases hmP : PrimeSupported P m
    · by_cases hnP : PrimeSupported P n
      · rw [primeBandCoefficient_eq_of_supported f P (hiff.mpr ⟨hmP, hnP⟩),
          primeBandCoefficient_eq_of_supported f P hmP,
          primeBandCoefficient_eq_of_supported f P hnP]
        exact hmul.2 m n hm hn hcop
      · have hmnP : ¬ PrimeSupported P (m * n) :=
          fun h ↦ hnP (hiff.mp h).2
        simp [primeBandCoefficient, hmP, hnP, hmnP]
    · have hmnP : ¬ PrimeSupported P (m * n) :=
          fun h ↦ hmP (hiff.mp h).1
      simp [primeBandCoefficient, hmP, hmnP]

theorem norm_primeBandCoefficient_le_one
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {n : ℕ} (hn : 0 < n) :
    ‖primeBandCoefficient a P n‖ ≤ 1 := by
  unfold primeBandCoefficient
  split_ifs
  · exact ha n hn
  · simp

/-- Successive prime-band restrictions intersect their predicates. -/
theorem primeBandCoefficient_nested
    (a : ℕ → ℂ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    primeBandCoefficient (primeBandCoefficient a P) Q =
      primeBandCoefficient a (fun p ↦ P p ∧ Q p) := by
  funext n
  by_cases hP : PrimeSupported P n
  · by_cases hQ : PrimeSupported Q n
    · have hPQ : PrimeSupported (fun p ↦ P p ∧ Q p) n := by
        exact ⟨hP.1, fun p hp ↦ ⟨hP.2 p hp, hQ.2 p hp⟩⟩
      simp [primeBandCoefficient, hP, hQ, hPQ]
    · have hPQ : ¬ PrimeSupported (fun p ↦ P p ∧ Q p) n := by
        intro h
        apply hQ
        exact ⟨h.1, fun p hp ↦ (h.2 p hp).2⟩
      simp [primeBandCoefficient, hQ, hPQ]
  · have hPQ : ¬ PrimeSupported (fun p ↦ P p ∧ Q p) n := by
      intro h
      apply hP
      exact ⟨h.1, fun p hp ↦ (h.2 p hp).1⟩
    simp [primeBandCoefficient, hP, hPQ]

/-- Exact complementary-band convolution for an ordinary multiplicative
function on the positive naturals. -/
theorem primeBandCoefficient_convolution_compl_of_multiplicative
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (hn : 0 < n) :
    LSeries.convolution (primeBandCoefficient f P)
        (primeBandCoefficient f (fun p ↦ ¬ P p)) n = f n := by
    rw [LSeries.convolution_def]
    change (∑ q ∈ n.divisorsAntidiagonal,
      primeBandCoefficient f P q.1 *
        primeBandCoefficient f (fun p ↦ ¬ P p) q.2) = f n
    let d := primeBandPart P n
    let e := primeBandPart (fun p ↦ ¬ P p) n
    have hne : n ≠ 0 := Nat.ne_of_gt hn
    have hde : d * e = n := primeBandPart_mul_compl P hne
    have hd : PrimeSupported P d := primeSupported_primeBandPart P n
    have he : PrimeSupported (fun p ↦ ¬ P p) e :=
      primeSupported_primeBandPart (fun p ↦ ¬ P p) n
    have hcop : d.Coprime e :=
      coprime_of_complementary_primeSupported P hd he
    have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hne⟩
    rw [Finset.sum_eq_single (d, e)]
    · simp only [primeBandCoefficient_eq_of_supported f P hd,
        primeBandCoefficient_eq_of_supported f (fun p ↦ ¬ P p) he]
      rw [← hmul.2 d e (Nat.pos_of_ne_zero hd.1)
        (Nat.pos_of_ne_zero he.1) hcop, hde]
    · intro q hq hqne
      by_cases hqP : PrimeSupported P q.1
      · by_cases hqC : PrimeSupported (fun p ↦ ¬ P p) q.2
        · have hqmul := (Nat.mem_divisorsAntidiagonal.mp hq).1
          have hu := eq_primeBandParts_of_mul_eq P hqmul hqP hqC
          exact (hqne (Prod.ext hu.1 hu.2)).elim
        · simp [primeBandCoefficient, hqC]
      · simp [primeBandCoefficient, hqP]
    · intro hnot
      exact (hnot hmem).elim

end

end Erdos67.MRHalaszBands
