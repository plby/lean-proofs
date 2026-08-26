import Mathlib

/-!
# Primitive integral representatives of rational matrices

Clearing denominators and removing a common gcd gives a primitive integral
representative. If its determinant divides all squared entries, primitivity
forces that determinant to be a unit.
-/

namespace Erdos1148.DukeArithmetic

lemma exists_primitive_int_multiple {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℚ) (hf : f ≠ 0) :
    ∃ (c : ℚ) (v : ι → ℤ), c ≠ 0 ∧ (∀ i, (v i : ℚ) = c * f i) ∧ Finset.univ.gcd v = 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hbQ : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hN : ∀ i, ∃ n : ℤ, (n : ℚ) = ((b : ℤ) : ℚ) * f i := by
    intro i
    obtain ⟨n, hn⟩ := hb i
    exact ⟨n, by simpa [Algebra.smul_def] using hn⟩
  choose N hN using hN
  let D := Finset.univ.gcd N
  have hD : D ≠ 0 := by
    intro hD
    apply hf
    funext i
    have hNi : N i = 0 := Finset.gcd_eq_zero_iff.mp hD i (Finset.mem_univ i)
    have hmul : ((b : ℤ) : ℚ) * f i = 0 := by rw [← hN i, hNi, Int.cast_zero]
    exact (mul_eq_zero.mp hmul).resolve_left hbQ
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  obtain ⟨v, hv, hvgcd⟩ := Finset.extract_gcd (s := Finset.univ) N Finset.univ_nonempty
  refine ⟨((b : ℤ) : ℚ) / D, v, div_ne_zero hbQ hDQ, ?_, hvgcd⟩
  intro i
  have hNi : (N i : ℚ) = (D : ℚ) * v i := by
    exact_mod_cast hv i (Finset.mem_univ i)
  have heq := hNi.symm.trans (hN i)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hDQ).mpr
  convert heq using 1
  ring

lemma exists_primitive_integer_matrix (M : Matrix (Fin 2) (Fin 2) ℚ) (hM : M.det ≠ 0) :
    ∃ (c : ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ), c ≠ 0 ∧
      A.map (Int.castRingHom ℚ) = c • M ∧
      Finset.univ.gcd (fun ij : Fin 2 × Fin 2 => A ij.1 ij.2) = 1 := by
  have hf : (fun ij : Fin 2 × Fin 2 => M ij.1 ij.2) ≠ 0 := by
    intro hf
    have hzero : M = 0 := by ext i j; exact congrFun hf (i, j)
    exact hM (by simp [hzero])
  obtain ⟨c, v, hc, hv, hgcd⟩ := exists_primitive_int_multiple
    (fun ij : Fin 2 × Fin 2 => M ij.1 ij.2) hf
  refine ⟨c, (fun i j => v (i, j)), hc, ?_, hgcd⟩
  ext i j
  exact hv (i, j)

lemma isUnit_of_dvd_squares_primitive {ι : Type*} [Fintype ι] (v : ι → ℤ) (D : ℤ)
    (hprim : Finset.univ.gcd v = 1) (hdiv : ∀ i, D ∣ v i ^ 2) : IsUnit D := by
  classical
  apply Int.isUnit_iff_natAbs_eq.mpr
  by_contra hD
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD
  have hpDZ : (p : ℤ) ∣ D := Int.natCast_dvd.mpr hpD
  have hpi (i : ι) : (p : ℤ) ∣ v i := by
    have hpow : p ∣ (v i ^ 2).natAbs := Int.natCast_dvd.mp (hpDZ.trans (hdiv i))
    rw [Int.natAbs_pow] at hpow
    exact Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow hpow)
  have hgcd : (p : ℤ) ∣ Finset.univ.gcd v := Finset.dvd_gcd fun i _ => hpi i
  rw [hprim] at hgcd
  exact hp.not_dvd_one (by exact_mod_cast hgcd)

end Erdos1148.DukeArithmetic
