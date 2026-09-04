import Util.Bernays.QuadraticSplitting

/-!
# Maximal ideals and split-prime classes in arbitrary quadratic orders
-/

open scoped nonZeroDivisors

namespace Bernays

theorem quadraticMaximal_ne_bot (d b : ℤ) (P : Ideal (QuadraticAlgebra ℤ d b))
    (hP : P.IsMaximal) : P ≠ ⊥ := by
  have htwo : Ideal.span ({(2 : QuadraticAlgebra ℤ d b)} : Set _) ≠ ⊤ := by
    intro ht
    have h : (1 : QuadraticAlgebra ℤ d b) ∈ Ideal.span ({2} : Set _) := by rw [ht]; trivial
    rw [Ideal.mem_span_singleton] at h
    have h' := (BinQuadForm.quadratic_intCast_dvd 2 (1 : QuadraticAlgebra ℤ d b)).mp h
    norm_num [QuadraticAlgebra.re_one] at h'
  intro hz
  have heq := hP.eq_of_le htwo (show P ≤ Ideal.span ({2} : Set _) by rw [hz]; exact bot_le)
  have hmem : (2 : QuadraticAlgebra ℤ d b) ∈ (⊥ : Ideal _) := by
    rw [← hz, heq]
    exact Ideal.mem_span_singleton_self 2
  have hre := congrArg QuadraticAlgebra.re (show (2 : QuadraticAlgebra ℤ d b) = 0 from hmem)
  change (2 : ℤ) = 0 at hre
  norm_num at hre

theorem exists_natPrime_under_quadraticMaximal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ P.under ℤ = Ideal.span ({(q : ℤ)} : Set ℤ) := by
  let := quadraticOrderIsDomain hD
  let : P.IsMaximal := hP
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have ha₀ : a ≠ 0 := by
    intro hz
    have hpos := Ring.HasFiniteQuotients.cardQuot_pos P (quadraticMaximal_ne_bot d b P hP)
    have hmem : ((P.cardQuot : ℕ) : QuadraticAlgebra ℤ d b) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact Ideal.Quotient.index_eq_zero P
    have hmem' : (P.cardQuot : ℤ) ∈ P.under ℤ := hmem
    rw [ha, hz] at hmem'
    have hzero : (P.cardQuot : ℤ) = 0 := by simpa using hmem'
    have : P.cardQuot = 0 := by exact_mod_cast hzero
    omega
  have hprime : Prime a := by
    apply (Ideal.span_singleton_prime ha₀).mp
    simpa only [← Ideal.submodule_span_eq, ← ha] using hP.isPrime.under ℤ
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  rw [ha]
  rcases abs_choice a with h | h <;> simp [h, Ideal.span_singleton_neg]

theorem quadraticMaximal_split_or_inert (d b : ℤ) (q : ℕ) [Fact q.Prime]
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P)
    (hD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d) :
    P = Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) ∨
      ∃ r : ZMod q, ∃ hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r,
        P = rootIdeal d b q r hr := by
  have hspan := (Ideal.span_singleton_le_iff_mem P).mpr hqP
  by_cases hroot : ∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r
  · obtain ⟨r, hr⟩ := hroot
    have hmod : (b : ZMod q) ^ 2 + 4 * (d : ZMod q) ≠ 0 := by
      intro hz
      apply hD
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hz
    have hs := quadratic_conjugate_root (d : ZMod q) (b : ZMod q) r hr
    have hrs := quadratic_roots_distinct (d : ZMod q) (b : ZMod q) r hr hmod
    have hprod : rootIdeal d b q r hr * rootIdeal d b q ((b : ZMod q) - r) hs ≤ P := by
      rw [rootIdeal_mul d b q hr hs hrs]
      exact hspan
    rcases hP.isPrime.mul_le.mp hprod with h | h
    · exact Or.inr ⟨r, hr, ((rootIdeal_isMaximal d b q r hr).eq_of_le hP.ne_top h).symm⟩
    · exact Or.inr ⟨(b : ZMod q) - r, hs,
        ((rootIdeal_isMaximal d b q _ hs).eq_of_le hP.ne_top h).symm⟩
  · left
    have hirr : ∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r := by
      simpa only [not_exists] using hroot
    exact ((inertIdeal_isMaximal d b q hirr).eq_of_le hP.ne_top hspan).symm

theorem rootIdeal_isUnit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hmod : (b : ZMod q) ^ 2 + 4 * (d : ZMod q) ≠ 0) :
    letI := quadraticOrderIsDomain hD
    IsUnit ((rootIdeal d b q r hr : Ideal (QuadraticAlgebra ℤ d b)) :
      FractionalIdeal (QuadraticAlgebra ℤ d b)⁰ (FractionRing (QuadraticAlgebra ℤ d b))) := by
  let := quadraticOrderIsDomain hD
  have hs := quadratic_conjugate_root (d : ZMod q) (b : ZMod q) r hr
  have hrs := quadratic_roots_distinct (d : ZMod q) (b : ZMod q) r hr hmod
  have hq₀ : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
    intro hz
    have h := congrArg QuadraticAlgebra.re hz
    have : (q : ℤ) = 0 := by simpa using h
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast this)
  have hu := (InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hq₀).2
  change IsUnit (((Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) :
    Ideal (QuadraticAlgebra ℤ d b)) : FractionalIdeal (QuadraticAlgebra ℤ d b)⁰
      (FractionRing (QuadraticAlgebra ℤ d b)))) at hu
  rw [← rootIdeal_mul d b q hr hs hrs, FractionalIdeal.coeIdeal_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Bernays
