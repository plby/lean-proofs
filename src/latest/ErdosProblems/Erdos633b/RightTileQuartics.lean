import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Ideal.Int
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! Explicit Eisenstein quartics and polynomial root transfer for the
remaining right-tile metric exclusions. -/

namespace Erdos633b
open Polynomial

noncomputable def evenQuartic {R : Type*} [CommRing R] (u v : R) : R[X] :=
  X ^ 4 - C u * X ^ 2 + C v

theorem evenQuartic_monic {R : Type*} [CommRing R] [Nontrivial R] (u v : R) :
    (evenQuartic u v).Monic := by
  unfold evenQuartic
  monicity <;> norm_num

theorem evenQuartic_natDegree {R : Type*} [CommRing R] [Nontrivial R] (u v : R) :
    (evenQuartic u v).natDegree = 4 := by
  unfold evenQuartic
  compute_degree <;> norm_num

theorem evenQuartic_irreducible_int (u p : ℤ) (hp : Prime p) (hu : p ∣ u)
    (hpsq : ¬ p ^ 2 ∣ p) : Irreducible (evenQuartic u p) := by
  let I : Ideal ℤ := Ideal.span {p}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  have hm := evenQuartic_monic u p
  have he : (evenQuartic u p).IsEisensteinAt I := by
    apply hm.isEisensteinAt_of_mem_of_notMem hI.ne_top
    · intro n hn
      rw [evenQuartic_natDegree] at hn
      change (evenQuartic u p).coeff n ∈ Ideal.span {p}
      rw [Ideal.mem_span_singleton]
      simp only [evenQuartic, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_X_pow, coeff_C]
      interval_cases n <;> norm_num [hu]
    · change (evenQuartic u p).coeff 0 ∉ Ideal.span {p} ^ 2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simpa [evenQuartic] using hpsq
  exact he.irreducible hI hm.isPrimitive (by rw [evenQuartic_natDegree]; norm_num)

theorem evenQuartic_irreducible_rat (u p : ℤ) (hp : Prime p) (hu : p ∣ u)
    (hpsq : ¬ p ^ 2 ∣ p) : Irreducible (evenQuartic (u : ℚ) (p : ℚ)) := by
  have hi := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (evenQuartic_monic u p).isPrimitive).mp
      (evenQuartic_irreducible_int u p hp hu hpsq)
  simpa [evenQuartic] using hi

theorem rightQuarticEight_irreducible : Irreducible (evenQuartic (4 : ℚ) 2) := by
  exact evenQuartic_irreducible_rat 4 2 (by norm_num) (by norm_num) (by norm_num)

theorem rightQuarticTen_irreducible : Irreducible (evenQuartic (5 : ℚ) 5) := by
  exact evenQuartic_irreducible_rat 5 5 (by norm_num) (by norm_num) (by norm_num)

theorem rational_polynomial_root_transfer (f g : ℚ[X]) (t t' : ℝ)
    (hf : Irreducible f) (hm : f.Monic)
    (ht : aeval t f = 0) (ht' : aeval t' f = 0) (hg : aeval t g = 0) :
    aeval t' g = 0 := by
  have hmin : f = minpoly ℚ t := minpoly.eq_of_irreducible_of_monic hf ht hm
  have hd : f ∣ g := by rw [hmin]; exact minpoly.dvd ℚ t hg
  obtain ⟨q, hq⟩ := hd
  rw [hq, map_mul, ht', zero_mul]

end Erdos633b
