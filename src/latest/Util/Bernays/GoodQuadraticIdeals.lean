import Util.Bernays.QuadraticMaximalIdeals
import Util.Bernays.IdealFactorization

/-!
# Factorization of ideals coprime to the quadratic discriminant
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticBadIdeal (d b : ℤ) : Ideal (QuadraticAlgebra ℤ d b) :=
  Ideal.span ({((discriminantLevel (b ^ 2 + 4 * d) : ℕ) : QuadraticAlgebra ℤ d b)} : Set _)

theorem prime_not_dvd_level_of_coprime {d b : ℤ} {q : ℕ}
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P)
    (hcop : IsCoprime P (quadraticBadIdeal d b)) :
    ¬ q ∣ discriminantLevel (b ^ 2 + 4 * d) := by
  rintro ⟨k, hk⟩
  have hmem : ((discriminantLevel (b ^ 2 + 4 * d) : ℕ) : QuadraticAlgebra ℤ d b) ∈ P := by
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right (k : QuadraticAlgebra ℤ d b) hqP
  have hle : quadraticBadIdeal d b ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  apply hP.ne_top
  apply top_unique
  rw [← hcop.sup_eq]
  exact sup_le le_rfl hle

theorem quadraticMaximal_coprime_isUnit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hcop : IsCoprime P (quadraticBadIdeal d b)) :
    letI := quadraticOrderIsDomain hD
    IsUnit (P : FractionalIdeal (QuadraticAlgebra ℤ d b)⁰
      (FractionRing (QuadraticAlgebra ℤ d b))) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨q, hq, hunder⟩ := exists_natPrime_under_quadraticMaximal hD P hP
  letI : Fact q.Prime := ⟨hq⟩
  have hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P := by
    change (q : ℤ) ∈ P.under ℤ
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime P hP hqP hcop
  have hqD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro hdvd
    have hn : q ∣ (b ^ 2 + 4 * d).natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    exact hnot (hn.trans (dvd_mul_left _ _))
  rcases quadraticMaximal_split_or_inert d b q P hP hqP hqD with h | ⟨r, hr, h⟩
  · rw [h]
    have hz : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
      intro hz
      have hc := congrArg QuadraticAlgebra.re hz
      have : (q : ℤ) = 0 := by simpa using hc
      exact hq.ne_zero (by exact_mod_cast this)
    exact (InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hz).2
  · rw [h]
    apply rootIdeal_isUnit hD q r hr
    intro hz
    apply hqD
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hz

theorem goodQuadraticIdeal_factorization {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ l : List (InvertibleIdeal (QuadraticAlgebra ℤ d b)), l.prod = I ∧
        ∀ P ∈ l, (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
          IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) := by
  letI := quadraticOrderIsDomain hD
  exact InvertibleIdeal.exists_list_maximal_factors (quadraticBadIdeal d b)
    (quadraticMaximal_coprime_isUnit hD)

end Bernays
