import ErdosProblems.Erdos980.ElliottTail.LocalNormEuler
import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# The prime-local root bound for an integral norm form

This file isolates the finite local estimate used by the odd-prime norm
sieve.  A coordinate presentation of the quotient `ᵒ K / pᵒ K` turns
the zero set of the norm form into the nonunits of that quotient.  The
nonunit density is at most `[K : ℚ] / p`: factor the rational prime ideal,
use the union bound `1 - ∏ (1 - aᵢ) ≤ ∑ aᵢ`, and use that there are at
most `[K : ℚ]` prime ideals above `p`, each of norm at least `p`.

The final theorem is deliberately stated for an arbitrary CRT-compatible
norm residue system together with its genuine quotient presentation.  The
good-prime coordinate bridge for a fixed correction ideal can therefore
instantiate it without duplicating any analytic or cardinal arithmetic.
-/

noncomputable section

open scoped NumberField BigOperators nonZeroDivisors

namespace Erdos980.ElliottTail.LocalNormRootBound

open NumberField
open NumberField.mixedEmbedding
open RayNormPrimeSieve
open LocalNormEuler

private theorem one_sub_prod_one_sub_le_sum
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
      have hai1 : a i ≤ 1 := ha1 i (Finset.mem_insert_self i s)
      have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj ↦
        ha0 j (Finset.mem_insert_of_mem hj)
      have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj ↦
        ha1 j (Finset.mem_insert_of_mem hj)
      have hprod0 : 0 ≤ ∏ j ∈ s, (1 - a j) := by
        exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (hs1 j hj)
      have hprod1 : ∏ j ∈ s, (1 - a j) ≤ 1 := by
        exact Finset.prod_le_one
          (fun j hj ↦ sub_nonneg.mpr (hs1 j hj))
          (fun j hj ↦ by linarith [hs0 j hj])
      rw [Finset.prod_insert hi]
      calc
        1 - (1 - a i) * ∏ j ∈ s, (1 - a j) =
            a i + (1 - a i) * (1 - ∏ j ∈ s, (1 - a j)) := by ring
        _ ≤ a i + (1 - ∏ j ∈ s, (1 - a j)) := by
          nlinarith [mul_nonneg hai0 (sub_nonneg.mpr hprod1)]
        _ ≤ a i + ∑ j ∈ s, a j := by linarith [ih hs0 hs1]
        _ = ∑ j ∈ insert i s, a j := (Finset.sum_insert hi).symm

private theorem rationalPrimeIdealFactor_absNorm_ge
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime)
    {P : Ideal (RingOfIntegers K)}
    (hP : P ∈ rationalPrimeIdealFactors K p) :
    p ≤ Ideal.absNorm P := by
  let pI : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hPfac : P ∈ UniqueFactorizationMonoid.factors
      (rationalModulusIdeal K p) := Multiset.mem_toFinset.mp hP
  have hPprime : Prime P :=
    UniqueFactorizationMonoid.prime_of_factor _ hPfac
  have hPprime' : P.IsPrime := Ideal.isPrime_of_prime hPprime
  letI : P.IsPrime := hPprime'
  letI : Fact p.Prime := ⟨hp⟩
  letI : pI.IsMaximal := by
    simpa only [pI] using Int.ideal_span_isMaximal_of_prime p
  letI : P.LiesOver pI := by
    apply (Ideal.liesOver_iff_dvd_map hPprime'.ne_top).mpr
    simpa only [pI, rationalModulusIdeal, Ideal.map_span,
      Set.image_singleton, map_natCast] using
      (UniqueFactorizationMonoid.dvd_of_mem_factors hPfac)
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp]
  exact Nat.le_pow (Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero pI P))

private theorem rationalPrimeIdealFactors_card_le_degree
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    (rationalPrimeIdealFactors K p).card ≤ Nat.card (index K) := by
  classical
  letI := Fintype.ofFinite (index K)
  let pI : Ideal ℤ := Ideal.span {(p : ℤ)}
  letI : Fact p.Prime := ⟨hp⟩
  letI : pI.IsMaximal := by
    simpa only [pI] using Int.ideal_span_isMaximal_of_prime p
  have hpI0 : pI ≠ ⊥ := by
    intro hbot
    have hmem : (p : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [← hbot]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact hp.ne_zero (by exact_mod_cast (show (p : ℤ) = 0 by simpa using hmem))
  have hcard := Ideal.card_primesOverFinset_le_finrank
    (S := RingOfIntegers K) ℚ K hpI0
  have hdegree : Module.finrank ℚ K = Nat.card (index K) := by
    rw [Nat.card_eq_fintype_card,
      ← Module.finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank]
  rw [← hdegree]
  have hsubset : rationalPrimeIdealFactors K p ⊆
      IsDedekindDomain.primesOverFinset pI (RingOfIntegers K) := by
    intro P hP
    have hPfac : P ∈ UniqueFactorizationMonoid.factors
        (rationalModulusIdeal K p) := Multiset.mem_toFinset.mp hP
    have hPprime : Prime P :=
      UniqueFactorizationMonoid.prime_of_factor _ hPfac
    apply (IsDedekindDomain.mem_primesOverFinset_iff hpI0 _).mpr
    refine ⟨Ideal.isPrime_of_prime hPprime, ?_⟩
    apply (Ideal.liesOver_iff_dvd_map
      (Ideal.isPrime_of_prime hPprime).ne_top).mpr
    simpa only [pI, rationalModulusIdeal, Ideal.map_span,
      Set.image_singleton, map_natCast] using
      (UniqueFactorizationMonoid.dvd_of_mem_factors hPfac)
  exact (Finset.card_le_card hsubset).trans hcard

/-- The unit density modulo a rational prime is at least `1 - [K:ℚ]/p`.
This is the local union bound in precisely the normalization needed for the
root-count estimate. -/
theorem rationalPrime_unitRatio_ge_one_sub_degree_div
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    1 - (Nat.card (index K) : ℝ) / p ≤
      (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  classical
  let F := rationalPrimeIdealFactors K p
  let a : Ideal (RingOfIntegers K) → ℝ := fun P ↦
    (Ideal.absNorm P : ℝ)⁻¹
  have hfactor0 : ∀ P ∈ F, 0 ≤ a P := by
    intro P hP
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hfactor1 : ∀ P ∈ F, a P ≤ 1 := by
    intro P hP
    have hnorm : (0 : ℝ) < Ideal.absNorm P := by
      exact_mod_cast hp.pos.trans_le
        (rationalPrimeIdealFactor_absNorm_ge K p hp hP)
    exact (inv_le_one₀ hnorm).mpr (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (ne_of_gt (hp.pos.trans_le
          (rationalPrimeIdealFactor_absNorm_ge K p hp hP)))))
  have hlocal : 1 - ∏ P ∈ F, (1 - a P) ≤ ∑ P ∈ F, a P :=
    one_sub_prod_one_sub_le_sum F a hfactor0 hfactor1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsum : ∑ P ∈ F, a P ≤ (Nat.card (index K) : ℝ) / p := by
    calc
      ∑ P ∈ F, a P ≤ ∑ _P ∈ F, (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro P hP
        have hnorm : (0 : ℝ) < Ideal.absNorm P := by
          exact_mod_cast hp.pos.trans_le
            (rationalPrimeIdealFactor_absNorm_ge K p hp hP)
        exact (inv_le_inv₀ hnorm hpR).mpr (by
          exact_mod_cast rationalPrimeIdealFactor_absNorm_ge K p hp hP)
      _ = (F.card : ℝ) / p := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ (Nat.card (index K) : ℝ) / p := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hpR.le)
        exact_mod_cast rationalPrimeIdealFactors_card_le_degree K p hp
  rw [rationalPrime_unitRatio_eq_prod_factors p hp]
  change 1 - (Nat.card (index K) : ℝ) / p ≤ ∏ P ∈ F, (1 - a P)
  linarith

/-- A genuine quotient presentation of a prime-local norm residue system
implies the sharp elementary root bound `D p^(D-1)`, where
`D = [K : ℚ]`. -/
theorem rootCount_le_degree_mul_prime_pow_sub_one_of_quotient
    (K : Type*) [Field K] [NumberField K]
    (M : CRTNormResidueSystem K)
    (p : ℕ) (hp : p.Prime)
    (e : (index K → ZMod p) ≃
      (RingOfIntegers K ⧸ rationalModulusIdeal K p))
    (hzero : ∀ x, M.normMod p x = 0 ↔ ¬ IsUnit (e x)) :
    M.rootCount K p ≤
      Nat.card (index K) * p ^ (Nat.card (index K) - 1) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype (index K) := Fintype.ofFinite _
  letI : Finite (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
    (Ideal.absNorm_ne_zero_iff (rationalModulusIdeal K p)).mp (by
      rw [rationalModulusIdeal, Ideal.absNorm_span_natCast]
      exact pow_ne_zero _ hp.ne_zero)
  let D := Nat.card (index K)
  let Z := Nat.card {x : index K → ZMod p // M.normMod p x = 0}
  have hdensity := LocalNormEuler.one_sub_coordinateNormResidueDensity_eq_unitRatio
    K e (M.normMod p) hzero
  have hunit := rationalPrime_unitRatio_ge_one_sub_degree_div K p hp
  have hdiv : (Z : ℝ) / (p : ℝ) ^ D ≤ (D : ℝ) / p := by
    dsimp only [Z, D]
    linarith
  have hDpos : 0 < D := by
    dsimp only [D]
    rw [Nat.card_eq_fintype_card,
      ← Module.finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank]
    exact Module.finrank_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hreal : (Z : ℝ) ≤ (D * p ^ (D - 1) : ℕ) := by
    have hmul := (div_le_iff₀ (pow_pos hpR D)).mp hdiv
    push_cast
    calc
      (Z : ℝ) ≤ (D : ℝ) / p * (p : ℝ) ^ D := hmul
      _ = (D : ℝ) * (p : ℝ) ^ (D - 1) := by
        have hpow : (p : ℝ) ^ D =
            (p : ℝ) ^ (D - 1) * (p : ℝ) := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hDpos.ne')]
        rw [hpow]
        field_simp
  have hnat : Z ≤ D * p ^ (D - 1) := by exact_mod_cast hreal
  have hcard : Z = (normDivisibleResidues K p (M.normMod p)).card := by
    exact Nat.subtype_card _ (by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_normDivisibleResidues])
  rw [M.rootCount_eq K p, ← hcard]
  exact hnat

/-- The actual signed algebraic norm form on the fixed ideal lattice has at
most `D p^(D-1)` zero coordinate cells at every rational prime coprime to the
ideal norm.  This is the concrete local leaf consumed by the odd-prime
squarefree CRT sieve. -/
theorem coordinateAlgebraNormResidueSystem_rootCount_le
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    (coordinateAlgebraNormResidueSystem K J).rootCount K p ≤
      Nat.card (index K) * p ^ (Nat.card (index K) - 1) := by
  apply rootCount_le_degree_mul_prime_pow_sub_one_of_quotient K
    (coordinateAlgebraNormResidueSystem K J) p hp
    (LocalNormEuler.fixedIdealCoordinateQuotientEquiv K J p hp hcop)
  intro k
  exact LocalNormEuler.fixedIdeal_coordinateAlgebraNormMod_eq_zero_iff_nonunit
    K J p hp hcop k

/-- Squarefree CRT form of the concrete local bound.  All dependence on the
sieve modulus is now explicit through `D^omega(d) d^(D-1)`. -/
theorem coordinateAlgebraNormResidueSystem_card_normDivisibleResidues_le
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    {d : ℕ} [NeZero d] (hd : Squarefree d)
    (hcop : ∀ p ∈ d.primeFactors,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    (normDivisibleResidues K d
        ((coordinateAlgebraNormResidueSystem K J).normMod d)).card ≤
      Nat.card (index K) ^ d.primeFactors.card *
        d ^ (Nat.card (index K) - 1) := by
  apply CRTNormResidueSystem.card_normDivisibleResidues_le_of_primeFactors
    K (coordinateAlgebraNormResidueSystem K J) hd
  intro p hpMem
  exact coordinateAlgebraNormResidueSystem_rootCount_le K J p
    (Nat.prime_of_mem_primeFactors hpMem) (hcop p hpMem)

end Erdos980.ElliottTail.LocalNormRootBound
