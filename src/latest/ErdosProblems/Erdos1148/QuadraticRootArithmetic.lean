import ErdosProblems.Erdos1148.OrderIndexConductor
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.KummerPolynomial

/-! # An integral square root and the good-prime Kummer--Dedekind condition -/

namespace Erdos1148.DukeArithmetic

open NumberField Polynomial

def quadraticRadicandRoot (d : ℤ) : QuadraticDiscrAlgebra d := ⟨0, 1⟩

lemma quadraticRadicandRoot_sq (d : ℤ) :
    quadraticRadicandRoot d ^ 2 = (d : QuadraticDiscrAlgebra d) := by
  ext <;> simp [quadraticRadicandRoot, pow_two]

lemma quadraticRadicandRoot_isIntegral (d : ℤ) : IsIntegral ℤ (quadraticRadicandRoot d) := by
  refine ⟨X ^ 2 - C d, monic_X_pow_sub_C d (by norm_num), ?_⟩
  change aeval (quadraticRadicandRoot d) (X ^ 2 - C d) = 0
  simp only [map_sub, map_pow, aeval_X, aeval_C, eq_intCast, map_intCast,
    quadraticRadicandRoot_sq, sub_self]

def quadraticIntegerRoot (d : ℤ) [Fact (¬IsSquare d)] : 𝓞 (QuadraticDiscrAlgebra d) :=
  ⟨quadraticRadicandRoot d, quadraticRadicandRoot_isIntegral d⟩

theorem quadraticIntegerRoot_minpoly (d : ℤ) [hns : Fact (¬IsSquare d)] :
    minpoly ℤ (quadraticIntegerRoot d) = X ^ 2 - C d := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ (QuadraticDiscrAlgebra d)
    (quadraticIntegerRoot d).isIntegral]
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro r hr
    apply hns.out
    apply Rat.isSquare_intCast_iff.mp
    exact ⟨r, by simpa only [pow_two, eq_intCast] using hr.symm⟩
  · change aeval (quadraticRadicandRoot d) (X ^ 2 - C (algebraMap ℤ ℚ d)) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C, eq_intCast, map_intCast,
      quadraticRadicandRoot_sq, sub_self]
  · exact monic_X_pow_sub_C _ (by norm_num)

theorem twice_orderIndex_mem_root_conductor {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (2 * quadraticOrderIndex ht : 𝓞 (QuadraticDiscrAlgebra d)) ∈
      conductor ℤ (quadraticIntegerRoot d) := by
  intro b
  obtain ⟨x, y, hxy⟩ := (mem_quadraticOrder_iff_coordinates
    ((discr_monicCompanionForm t).trans ht) (primitive_monicCompanionForm t) _).mp
    (orderIndex_mul_integer_mem_order ht b)
  have heq : (2 * quadraticOrderIndex ht : 𝓞 (QuadraticDiscrAlgebra d)) * b =
      ((2 * x + y * d : ℤ) : 𝓞 (QuadraticDiscrAlgebra d)) +
        (y : 𝓞 (QuadraticDiscrAlgebra d)) * quadraticIntegerRoot d := by
    apply Subtype.ext
    change (2 * (quadraticOrderIndex ht : QuadraticDiscrAlgebra d)) * (b : QuadraticDiscrAlgebra d) =
      ((2 * x + y * d : ℤ) : QuadraticDiscrAlgebra d) +
        (y : QuadraticDiscrAlgebra d) * quadraticRadicandRoot d
    rw [mul_assoc, hxy]
    have htwo : (2 : QuadraticDiscrAlgebra d) = ⟨2, 0⟩ := rfl
    ext <;> simp [quadraticOrderGenerator, quadraticRadicandRoot, htwo] <;> ring
  rw [heq]
  exact (Algebra.adjoin ℤ {quadraticIntegerRoot d}).add_mem
    (Subalgebra.intCast_mem _ _) ((Algebra.adjoin ℤ {quadraticIntegerRoot d}).mul_mem
      (Subalgebra.intCast_mem _ _) (Algebra.subset_adjoin (Set.mem_singleton _)))

theorem quadraticIntegerRoot_exponent_dvd_twice_index {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    RingOfIntegers.exponent (quadraticIntegerRoot d) ∣ 2 * quadraticOrderIndex ht := by
  have h := twice_orderIndex_mem_root_conductor ht
  rw [show (2 * quadraticOrderIndex ht : 𝓞 (QuadraticDiscrAlgebra d)) =
    ((2 * quadraticOrderIndex ht : ℕ) : 𝓞 (QuadraticDiscrAlgebra d)) by push_cast; rfl] at h
  have hi := (Int.cast_mem_ideal_iff (I := conductor ℤ (quadraticIntegerRoot d))
    (d := (2 * quadraticOrderIndex ht : ℕ))).mp
    (by simpa only [Int.cast_natCast] using h)
  exact_mod_cast hi

theorem quadraticIntegerRoot_prime_not_dvd_exponent {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) {p : ℕ} (hp : ¬(p : ℤ) ∣ 2 * d) :
    ¬p ∣ RingOfIntegers.exponent (quadraticIntegerRoot d) := by
  intro h
  have hf : (quadraticOrderIndex ht : ℤ) ∣ d :=
    ⟨(quadraticOrderIndex ht : ℤ) * NumberField.discr (QuadraticDiscrAlgebra d), by
      calc
        d = (quadraticOrderIndex ht : ℤ) ^ 2 *
            NumberField.discr (QuadraticDiscrAlgebra d) :=
          (quadraticOrderIndex_sq_mul_field_discr ht).symm
        _ = _ := by ring⟩
  apply hp
  apply dvd_trans _ (mul_dvd_mul_left 2 hf)
  exact_mod_cast h.trans (quadraticIntegerRoot_exponent_dvd_twice_index ht)

end Erdos1148.DukeArithmetic
