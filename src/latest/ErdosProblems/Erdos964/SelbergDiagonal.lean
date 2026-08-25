import ErdosProblems.Erdos964.Basic
import BoundedGaps.Maynard.MaynardYMobiusInterval

/-!
# The scalar Selberg transform used by GGPY

This is the finite inversion and diagonalization behind equations (3.7)--
(3.14) of Goldston--Graham--Pintz--Yıldırım, arXiv:math/0609615.
The coefficients are indexed by a single divisor. This algebra is exact
and does not assume any distribution or asymptotic statement.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.Moebius
open BoundedGaps.Maynard

theorem sum_moebius_divisors_between (P r t : ℕ) (hP : Squarefree P)
    (hr : r ∣ P) (ht : t ∣ P) :
    (∑ d ∈ P.divisors, if r ∣ d ∧ d ∣ t then (μ d : ℝ) else 0) =
      if r = t then (μ r : ℝ) else 0 := by
  classical
  by_cases hrt : r ∣ t
  · have hfilter : P.divisors.filter (fun d => r ∣ d ∧ d ∣ t) = upperDivisorInterval r t := by
      ext d
      simp only [Finset.mem_filter, upperDivisorInterval, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hrd, hdt⟩
        exact ⟨⟨hdt, (hP.squarefree_of_dvd ht).ne_zero⟩, hrd⟩
      · rintro ⟨⟨hdt, _⟩, hrd⟩
        exact ⟨⟨hdt.trans ht, hP.ne_zero⟩, hrd, hdt⟩
    rw [← Finset.sum_filter, hfilter]
    exact_mod_cast sum_moebius_upperDivisorInterval (hP.squarefree_of_dvd ht)
      (Nat.pos_of_ne_zero (hP.squarefree_of_dvd hr).ne_zero) hrt
  · have hne : r ≠ t := fun heq => hrt (heq ▸ dvd_refl r)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro d _
    exact if_neg (fun h => hrt (h.1.trans h.2))

theorem upper_divisor_moebius_inversion (P r : ℕ) (Y : ℕ → ℝ)
    (hP : Squarefree P) (hr : r ∣ P) :
    (∑ d ∈ P.divisors, if r ∣ d then (μ d : ℝ) *
      (∑ t ∈ P.divisors, if d ∣ t then Y t else 0) else 0) = (μ r : ℝ) * Y r := by
  classical
  have hterm (d : ℕ) :
      (if r ∣ d then (μ d : ℝ) *
        (∑ t ∈ P.divisors, if d ∣ t then Y t else 0) else 0) =
      ∑ t ∈ P.divisors, (if r ∣ d ∧ d ∣ t then (μ d : ℝ) else 0) * Y t := by
    by_cases hrd : r ∣ d
    · simp only [if_pos hrd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hdt : d ∣ t <;> simp [hrd, hdt]
    · simp [hrd]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner (t : ℕ) (ht : t ∈ P.divisors) :
      (∑ d ∈ P.divisors, (if r ∣ d ∧ d ∣ t then (μ d : ℝ) else 0) * Y t) =
      (if r = t then (μ r : ℝ) else 0) * Y t := by
    rw [← Finset.sum_mul, sum_moebius_divisors_between P r t hP hr (Nat.dvd_of_mem_divisors ht)]
  rw [Finset.sum_congr rfl hinner]
  simp only [ite_mul, zero_mul]
  exact Finset.sum_ite_eq_of_mem _ _ _ (Nat.mem_divisors.mpr ⟨hr, hP.ne_zero⟩)

noncomputable def scalarSelbergCoefficient (s : BoundingSieve) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  (μ d : ℝ) / s.nu d *
    ∑ r ∈ s.prodPrimes.divisors, if d ∣ r then s.selbergTerms r * y r else 0

theorem scalarSelbergCoefficient_eq_zero_of_not_dvd (s : BoundingSieve) (y : ℕ → ℝ)
    (d : ℕ) (hd : ¬ d ∣ s.prodPrimes) : scalarSelbergCoefficient s y d = 0 := by
  unfold scalarSelbergCoefficient
  have hsum : (∑ r ∈ s.prodPrimes.divisors,
      if d ∣ r then s.selbergTerms r * y r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact if_neg (fun hdr => hd (hdr.trans (Nat.dvd_of_mem_divisors hr)))
  rw [hsum, mul_zero]

theorem scalarSelbergCoefficient_eq_zero_of_radius (s : BoundingSieve) (y : ℕ → ℝ)
    (R d : ℕ) (hy : ∀ r, R ≤ r → y r = 0) (hRd : R ≤ d) :
    scalarSelbergCoefficient s y d = 0 := by
  unfold scalarSelbergCoefficient
  have hsum : (∑ r ∈ s.prodPrimes.divisors,
      if d ∣ r then s.selbergTerms r * y r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hdr : d ∣ r
    · have hrpos := Nat.pos_of_ne_zero
        (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hr)).ne_zero
      rw [if_pos hdr, hy r (hRd.trans (Nat.le_of_dvd hrpos hdr)), mul_zero]
    · exact if_neg hdr
  rw [hsum, mul_zero]

theorem scalarSelbergCoefficient_forward (s : BoundingSieve) (y : ℕ → ℝ)
    (r : ℕ) (hr : r ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if r ∣ d then s.nu d * scalarSelbergCoefficient s y d else 0) =
      (μ r : ℝ) * s.selbergTerms r * y r := by
  classical
  have hterm (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) :
      s.nu d * scalarSelbergCoefficient s y d =
        (μ d : ℝ) * ∑ t ∈ s.prodPrimes.divisors,
          if d ∣ t then s.selbergTerms t * y t else 0 := by
    have hnu := BoundingSieve.nu_ne_zero (s := s) (Nat.dvd_of_mem_divisors hd)
    unfold scalarSelbergCoefficient
    field_simp
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, if r ∣ d then (μ d : ℝ) *
        (∑ t ∈ s.prodPrimes.divisors, if d ∣ t then s.selbergTerms t * y t else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hterm d hd]
    _ = (μ r : ℝ) * (s.selbergTerms r * y r) :=
      upper_divisor_moebius_inversion s.prodPrimes r (fun t => s.selbergTerms t * y t)
        s.prodPrimes_squarefree hr
    _ = _ := by ring

theorem scalarSelbergCoefficient_diagonal (s : BoundingSieve) (y : ℕ → ℝ) :
    s.mainSum (BoundingSieve.lambdaSquared (scalarSelbergCoefficient s y)) =
      ∑ r ∈ s.prodPrimes.divisors, s.selbergTerms r * (y r) ^ 2 := by
  classical
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  apply Finset.sum_congr rfl
  intro r hr
  have hrP := Nat.dvd_of_mem_divisors hr
  have hsq := s.prodPrimes_squarefree.squarefree_of_dvd hrP
  have hmu : (μ r : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one r).mp hsq
  have hg : s.selbergTerms r ≠ 0 := (BoundingSieve.selbergTerms_pos hrP).ne'
  rw [scalarSelbergCoefficient_forward s y r hrP, mul_pow, mul_pow, hmu]
  field_simp

end Erdos964
