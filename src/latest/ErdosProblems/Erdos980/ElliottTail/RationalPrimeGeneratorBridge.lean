/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.Basic
import ErdosProblems.Erdos980.ElliottTail.IdealGeneratorCongruenceCount
import ErdosProblems.Erdos980.ElliottTail.RayPrincipalizationHeight

/-!
# Eligible rational primes as bounded cyclotomic ray generators

This file is the concrete algebraic bridge between the rational-prime
candidates in Erdos problem 980 and the fixed-lattice generator sieves.
For a prime `q = 1 (mod ell)` we choose a prime ideal `P` of the
`ell`-cyclotomic field above `(q)`.  Its residue degree is one and hence
`N(P) = q`.  Finite ray principalization then supplies a correction ideal
`J_i` and a strong-primary generator of `P * J_i`.

For the geometric count we retain the unit-balanced generator in the
fundamental cone.  Multiplication by one of the finitely many chosen unit
residue representatives recovers the strong-primary generator used by
Eisenstein reciprocity.  Thus both generators have the same principal ideal,
and the finite pair consisting of a correction index and a unit-residue
index contains every loss in passing between the geometric and reciprocity
normalizations.
-/

open scoped NumberField nonZeroDivisors Pointwise

namespace Erdos980.ElliottTail.RationalPrimeGeneratorBridge

noncomputable section

open NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open BernoulliRegular
open BernoulliRegular.Furtwaengler
open Erdos980.ElliottTail.IdealGeneratorCongruenceCount
open Erdos980.ElliottTail.RayPrincipalization
open Erdos980.ElliottTail.RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
  (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

local notation "lambdaIdeal" =>
  Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K))

/-! ## The degree-one prime over an eligible rational prime -/

/-- The rational prime ideal `(q)` in `ℤ`. -/
def integerPrimeIdeal (q : ℕ) : Ideal ℤ :=
  Ideal.span ({(q : ℤ)} : Set ℤ)

theorem integerPrimeIdeal_isPrime {q : ℕ} (hq : q.Prime) :
    (integerPrimeIdeal q).IsPrime := by
  rw [integerPrimeIdeal]
  exact (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hq.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hq)

/-- A fixed prime ideal of `𝓞 K` above the eligible rational prime `q`. -/
noncomputable def primeIdealAbove (q : ℕ) (hq : q.Prime) : Ideal (𝓞 K) := by
  letI : (integerPrimeIdeal q).IsPrime := integerPrimeIdeal_isPrime hq
  exact (Classical.choice (integerPrimeIdeal q).nonempty_primesOver).1

theorem primeIdealAbove_isPrime (q : ℕ) (hq : q.Prime) :
    (primeIdealAbove K q hq).IsPrime := by
  letI : (integerPrimeIdeal q).IsPrime := integerPrimeIdeal_isPrime hq
  exact (Classical.choice (integerPrimeIdeal q).nonempty_primesOver).2.1

theorem primeIdealAbove_liesOver (q : ℕ) (hq : q.Prime) :
    (primeIdealAbove K q hq).LiesOver (integerPrimeIdeal q) := by
  letI : (integerPrimeIdeal q).IsPrime := integerPrimeIdeal_isPrime hq
  exact (Classical.choice (integerPrimeIdeal q).nonempty_primesOver).2.2

theorem primeIdealAbove_isMaximal (q : ℕ) (hq : q.Prime) :
    (primeIdealAbove K q hq).IsMaximal :=
  (primeIdealAbove_isPrime K q hq).isMaximal
    (by
      intro hbot
      letI : (primeIdealAbove K q hq).LiesOver
          (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
        simpa [integerPrimeIdeal] using primeIdealAbove_liesOver K q hq
      have hq_mem_base : (q : ℤ) ∈ Ideal.span ({(q : ℤ)} : Set ℤ) :=
        Ideal.subset_span (by simp)
      have hq_mem : (q : 𝓞 K) ∈ primeIdealAbove K q hq := by
        simpa using ((Ideal.mem_of_liesOver
          (P := primeIdealAbove K q hq)
          (p := Ideal.span ({(q : ℤ)} : Set ℤ)) (q : ℤ)).mp hq_mem_base)
      have hq_zero : (q : 𝓞 K) = 0 := by
        simpa [hbot] using hq_mem
      exact hq.ne_zero (by exact_mod_cast hq_zero))

theorem eligible_natCast_eq_one {q : ℕ} (hq : Eligible ell q) :
    (q : ZMod ell) = 1 := by
  simpa only [Nat.cast_one] using
    (ZMod.natCast_eq_natCast_iff q 1 ell).mpr hq.2

theorem eligible_ne_exponent {q : ℕ} (hq : Eligible ell q) : q ≠ ell := by
  intro hqe
  subst q
  have hcast := eligible_natCast_eq_one ell hq
  simpa using hcast

theorem eligible_not_dvd_exponent {q : ℕ} (hq : Eligible ell q) : ¬ q ∣ ell := by
  intro hdvd
  have hqe : q = ell :=
    (Nat.prime_dvd_prime_iff_eq hq.1 (Fact.out : ell.Prime)).mp hdvd
  exact eligible_ne_exponent ell hq hqe

theorem primeIdealAbove_inertiaDeg_eq_one {q : ℕ}
    (hq : Eligible ell q) :
    (primeIdealAbove K q hq.1).inertiaDeg ℤ = 1 := by
  let P := primeIdealAbove K q hq.1
  letI : P.IsPrime := primeIdealAbove_isPrime K q hq.1
  letI : Fact q.Prime := ⟨hq.1⟩
  letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using primeIdealAbove_liesOver K q hq.1
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (p := q) (K := K) P (eligible_not_dvd_exponent ell hq),
    eligible_natCast_eq_one ell hq, orderOf_one]

/-- Exact conductor norm: the selected degree-one prime ideal has norm `q`. -/
theorem absNorm_primeIdealAbove {q : ℕ} (hq : Eligible ell q) :
    Ideal.absNorm (primeIdealAbove K q hq.1) = q := by
  let P := primeIdealAbove K q hq.1
  letI : P.IsPrime := primeIdealAbove_isPrime K q hq.1
  letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using primeIdealAbove_liesOver K q hq.1
  rw [← Ideal.pow_inertiaDeg q
    (primeIdealAbove K q hq.1),
    primeIdealAbove_inertiaDeg_eq_one ell K hq, pow_one]

theorem primeIdealAbove_ne_bot {q : ℕ} (hq : Eligible ell q) :
    primeIdealAbove K q hq.1 ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_primeIdealAbove ell K hq
  rw [hbot, Ideal.absNorm_bot] at hnorm
  exact hq.1.ne_zero hnorm.symm

/-- The chosen degree-one prime packaged as a nonzero ideal. -/
noncomputable def nonzeroPrimeIdealAbove {q : ℕ} (hq : Eligible ell q) :
    (Ideal (𝓞 K))⁰ :=
  ⟨primeIdealAbove K q hq.1, by
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (primeIdealAbove_ne_bot ell K hq)⟩

/-- The selected prime over an eligible `q` is distinct from the unique
cyclotomic prime above `ell`. -/
theorem primeIdealAbove_ne_lambda {q : ℕ} (hq : Eligible ell q) :
    primeIdealAbove K q hq.1 ≠ lambdaIdeal := by
  intro h
  have hnorm := congrArg Ideal.absNorm h
  have hnormL : Ideal.absNorm lambdaIdeal = ell := by
    letI : IsCyclotomicExtension {ell ^ (0 + 1)} ℚ K := by
      simpa using (inferInstance : IsCyclotomicExtension {ell} ℚ K)
    have hz : IsPrimitiveRoot (IsCyclotomicExtension.zeta ell ℚ K)
        (ell ^ (0 + 1)) := by
      simpa using (IsCyclotomicExtension.zeta_spec ell ℚ K)
    simpa [FLT37.zetaSubOne_def] using
      (IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one ell 0
        hz)
  rw [absNorm_primeIdealAbove ell K hq, hnormL] at hnorm
  exact eligible_ne_exponent ell hq hnorm

/-- The selected eligible prime is coprime to the distinguished cyclotomic
prime, which is precisely the hypothesis needed for ray principalization. -/
theorem lambda_coprime_primeIdealAbove {q : ℕ} (hq : Eligible ell q) :
    lambdaIdeal ⊔ primeIdealAbove K q hq.1 = ⊤ := by
  have hLprime : Ideal.IsPrime lambdaIdeal :=
    Ideal.isPrime_of_prime
      (Ideal.prime_span_singleton_iff.mpr
        (FLT37.zetaSubOne_prime ell K))
  have hL0 : lambdaIdeal ≠ ⊥ := by
    intro h
    exact FLT37.zetaSubOne_ne_zero ell K
      (Ideal.span_singleton_eq_bot.mp h)
  have hLmax : Ideal.IsMaximal lambdaIdeal := hLprime.isMaximal hL0
  have hPmax : Ideal.IsMaximal (primeIdealAbove K q hq.1) :=
    (primeIdealAbove_isPrime K q hq.1).isMaximal
      (primeIdealAbove_ne_bot ell K hq)
  letI : Ideal.IsMaximal lambdaIdeal := hLmax
  letI : Ideal.IsMaximal (primeIdealAbove K q hq.1) := hPmax
  exact Ideal.isCoprime_iff_sup_eq.mp
    (Ideal.isCoprime_of_isMaximal
      (primeIdealAbove_ne_lambda ell K hq).symm)

/-! ## The degree-one residue field -/

/-- The canonical map from `ZMod q` to the residue field of the selected
degree-one prime is an equivalence.  This is the bridge used when a
cyclotomic generator congruence is encoded by rational residue coordinates. -/
noncomputable def primeIdealAboveResidueEquiv {q : ℕ} (hq : Eligible ell q) :
    ZMod q ≃+* (𝓞 K ⧸ primeIdealAbove K q hq.1) := by
  let P := primeIdealAbove K q hq.1
  letI : Fact q.Prime := ⟨hq.1⟩
  letI : P.IsMaximal := primeIdealAbove_isMaximal K q hq.1
  letI : P.IsPrime := primeIdealAbove_isPrime K q hq.1
  letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using primeIdealAbove_liesOver K q hq.1
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (primeIdealAbove_ne_bot ell K hq)
  have hq_mem_base : (q : ℤ) ∈ Ideal.span ({(q : ℤ)} : Set ℤ) :=
    Ideal.subset_span (by simp)
  have hq_mem : (q : 𝓞 K) ∈ P := by
    simpa using ((Ideal.mem_of_liesOver (P := P)
      (p := Ideal.span ({(q : ℤ)} : Set ℤ)) (q : ℤ)).mp hq_mem_base)
  have hq_zero : (q : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hq_mem
  letI : CharP (𝓞 K ⧸ P) q :=
    (CharP.charP_iff_prime_eq_zero hq.1).2 hq_zero
  let residueMap : ZMod q →+* (𝓞 K ⧸ P) := ZMod.castHom dvd_rfl _
  have hcard : Nat.card (𝓞 K ⧸ P) = q := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact absNorm_primeIdealAbove ell K hq
  have hbijective : Function.Bijective residueMap :=
    (Nat.bijective_iff_injective_and_card residueMap).2
      ⟨residueMap.injective, by rw [Nat.card_zmod, hcard]⟩
  exact RingEquiv.ofBijective residueMap hbijective

theorem primeIdealAboveResidueEquiv_intCast {q : ℕ} (hq : Eligible ell q)
    (n : ℤ) :
    primeIdealAboveResidueEquiv ell K hq (n : ZMod q) =
      Ideal.Quotient.mk (primeIdealAbove K q hq.1) (n : 𝓞 K) := by
  simp [primeIdealAboveResidueEquiv]

/-! ## A cone generator and its finite-unit primary normalization -/

/-- An eligible rational prime gives a degree-one prime ideal and, after one
of finitely many ray corrections, a pair of generators with complementary
normalizations.  The generator `b` lies in the fundamental cone and is the
one counted geometrically.  The generator `a` is strong-primary and is the
one used by power reciprocity.  They differ by the inverse of a representative
from the finite unit-residue image.

The displayed scale is the `d`-th root of the integral norm
`q * N(correction)`, where `d = [K : ℚ]`.  Consequently its `d`-th power is
exactly linear in the rational conductor, as required by the fixed-lattice
upper-bound sieve. -/
theorem exists_balanced_primary_generator {q : ℕ} (hq : Eligible ell q) :
    ∃ (P : (Ideal (𝓞 K))⁰)
      (i : CyclotomicRayCorrectionIndex ell K)
      (r : UnitResidueImage ell K)
      (a b : 𝓞 K),
      (P : Ideal (𝓞 K)).IsPrime ∧
      Ideal.absNorm (P : Ideal (𝓞 K)) = q ∧
      FLT37.IsPrimary ell (K := K) a ∧
      IsPrimeToP (p := ell) (K := K) a ∧
      Ideal.span ({a} : Set (𝓞 K)) =
        (P : Ideal (𝓞 K)) * cyclotomicRayCorrection ell K i ∧
      Ideal.span ({b} : Set (𝓞 K)) =
        (P : Ideal (𝓞 K)) * cyclotomicRayCorrection ell K i ∧
      a = (((unitResidueRepresentative ell K r)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * b ∧
      mixedEmbedding K (b : K) ∈ fundamentalCone K ∧
      (mixedEmbedding.stdBasis K).equivFunL (mixedEmbedding K (b : K)) ∈
        (((q * Ideal.absNorm (cyclotomicRayCorrection ell K i) : ℕ) : ℝ) ^
            ((Module.finrank ℚ K : ℝ)⁻¹)) • generatorNormRegion K ∧
      Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) =
        q * Ideal.absNorm (cyclotomicRayCorrection ell K i) := by
  classical
  let P : (Ideal (𝓞 K))⁰ := nonzeroPrimeIdealAbove ell K hq
  have hPprime : (P : Ideal (𝓞 K)).IsPrime :=
    primeIdealAbove_isPrime K q hq.1
  have hPL : lambdaIdeal ⊔ (P : Ideal (𝓞 K)) = ⊤ := by
    exact lambda_coprime_primeIdealAbove ell K hq
  obtain ⟨i, a₀, ha₀primary, ha₀prime, ha₀span⟩ :=
    exists_primary_generator_mul_cyclotomicRayCorrection ell K P hPL
  let x : mixedSpace K := mixedEmbedding K (a₀ : K)
  have hx0 : x ≠ 0 := by
    intro hx
    have haK : (a₀ : K) = 0 := by
      apply mixedEmbedding_injective K
      simpa [x] using hx
    exact ha₀prime.1 (RingOfIntegers.coe_injective haK)
  have hxnorm : mixedEmbedding.norm x ≠ 0 :=
    (mixedEmbedding.norm_eq_zero_iff' ⟨(a₀ : K), rfl⟩).not.mpr hx0
  obtain ⟨u, hucone⟩ := exists_unit_smul_mem hxnorm
  let r : UnitResidueImage ell K := unitResidueClass ell K u
  let v : (𝓞 K)ˣ := unitResidueRepresentative ell K r
  let w : (𝓞 K)ˣ := primaryBalancingUnit ell K u
  let b : 𝓞 K := (u : 𝓞 K) * a₀
  let a : 𝓞 K := (w : 𝓞 K) * a₀
  have haprimary : FLT37.IsPrimary ell (K := K) a := by
    dsimp [a]
    exact (primaryBalancingUnit_isPrimary ell K u).mul ha₀primary
  have haprime : IsPrimeToP (p := ell) (K := K) a := by
    refine ⟨mul_ne_zero (Units.ne_zero w) ha₀prime.1, ?_⟩
    have ha₀cop := ha₀prime.2
    rw [Ideal.span_insert] at ha₀cop ⊢
    dsimp [a]
    rw [Ideal.span_singleton_mul_left_unit (Units.isUnit w)]
    exact ha₀cop
  have haspan : Ideal.span ({a} : Set (𝓞 K)) =
      (P : Ideal (𝓞 K)) * cyclotomicRayCorrection ell K i := by
    calc
      Ideal.span ({a} : Set (𝓞 K)) = Ideal.span ({a₀} : Set (𝓞 K)) := by
        dsimp [a]
        exact Ideal.span_singleton_mul_left_unit (Units.isUnit w) a₀
      _ = _ := ha₀span
  have hbspan : Ideal.span ({b} : Set (𝓞 K)) =
      (P : Ideal (𝓞 K)) * cyclotomicRayCorrection ell K i := by
    calc
      Ideal.span ({b} : Set (𝓞 K)) = Ideal.span ({a₀} : Set (𝓞 K)) := by
        dsimp [b]
        exact Ideal.span_singleton_mul_left_unit (Units.isUnit u) a₀
      _ = _ := ha₀span
  have hab : a = (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) * b := by
    dsimp [a, w, b, v, r, primaryBalancingUnit]
    ring
  have hbcone : mixedEmbedding K (b : K) ∈ fundamentalCone K := by
    simpa [x, b, unitSMul_smul] using hucone
  let N : ℕ := q * Ideal.absNorm (cyclotomicRayCorrection ell K i)
  have hCorr0 : Ideal.absNorm (cyclotomicRayCorrection ell K i) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr
      (cyclotomicRayCorrection_ne_bot ell K i)
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.mul_pos hq.1.pos (Nat.pos_of_ne_zero hCorr0)
  have hPnorm : Ideal.absNorm (P : Ideal (𝓞 K)) = q := by
    simpa [P, nonzeroPrimeIdealAbove] using
      (absNorm_primeIdealAbove ell K hq)
  have hnormb : mixedEmbedding.norm (mixedEmbedding K (b : K)) = (N : ℝ) := by
    rw [mixedEmbedding_norm_ringOfIntegers K b, hbspan, map_mul,
      hPnorm, Nat.cast_mul]
  let d : ℕ := Module.finrank ℚ K
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Module.finrank_pos.ne'
  let T : ℝ := (N : ℝ) ^ ((d : ℝ)⁻¹)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos hNreal _
  have hTpow : T ^ d = (N : ℝ) := by
    dsimp [T]
    exact Real.rpow_inv_natCast_pow hNreal.le hd
  have hregion :
      (mixedEmbedding.stdBasis K).equivFunL (mixedEmbedding K (b : K)) ∈
        T • generatorNormRegion K := by
    let z : mixedSpace K := T⁻¹ • mixedEmbedding K (b : K)
    have hzcone : z ∈ fundamentalCone K := by
      exact smul_mem_of_mem hbcone (inv_ne_zero hT.ne')
    have hznorm : mixedEmbedding.norm z = 1 := by
      dsimp only [z]
      rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hT, inv_pow,
        hnormb, hTpow]
      exact inv_mul_cancel₀ hNreal.ne'
    have hz : z ∈ normLeOne K := mem_normLeOne.mpr ⟨hzcone, hznorm.le⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hT.ne']
    refine ⟨z, hz, ?_⟩
    dsimp only [z]
    exact (mixedEmbedding.stdBasis K).equivFunL.map_smul
      T⁻¹ (mixedEmbedding K (b : K))
  have hnormspan : Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) = N := by
    rw [hbspan, map_mul, hPnorm]
  refine ⟨P, i, r, a, b, hPprime, absNorm_primeIdealAbove ell K hq,
    haprimary, haprime, haspan, hbspan, hab, hbcone, ?_, ?_⟩
  · simpa [T, d, N] using hregion
  · simpa [N] using hnormspan

/-! ## A finite injective conductor encoding -/

/-- All arithmetic and geometric data selected from the existence theorem
for one eligible rational conductor. -/
structure BoundedGeneratorEncodingData (q : ℕ) where
  primeIdeal : (Ideal (𝓞 K))⁰
  correctionIndex : CyclotomicRayCorrectionIndex ell K
  unitResidueIndex : UnitResidueImage ell K
  primaryGenerator : 𝓞 K
  balancedGenerator : 𝓞 K
  primeIdeal_isPrime : (primeIdeal : Ideal (𝓞 K)).IsPrime
  primeIdeal_absNorm : Ideal.absNorm (primeIdeal : Ideal (𝓞 K)) = q
  primaryGenerator_isPrimary :
    FLT37.IsPrimary ell (K := K) primaryGenerator
  primaryGenerator_isPrimeTo :
    IsPrimeToP (p := ell) (K := K) primaryGenerator
  primaryGenerator_span :
    Ideal.span ({primaryGenerator} : Set (𝓞 K)) =
      (primeIdeal : Ideal (𝓞 K)) *
        cyclotomicRayCorrection ell K correctionIndex
  balancedGenerator_span :
    Ideal.span ({balancedGenerator} : Set (𝓞 K)) =
      (primeIdeal : Ideal (𝓞 K)) *
        cyclotomicRayCorrection ell K correctionIndex
  primaryGenerator_eq :
    primaryGenerator =
      (((unitResidueRepresentative ell K unitResidueIndex)⁻¹ : (𝓞 K)ˣ) :
        𝓞 K) * balancedGenerator
  balancedGenerator_mem_cone :
    mixedEmbedding K (balancedGenerator : K) ∈ fundamentalCone K
  balancedGenerator_mem_region :
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (balancedGenerator : K)) ∈
      (((q * Ideal.absNorm
          (cyclotomicRayCorrection ell K correctionIndex) : ℕ) : ℝ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹)) • generatorNormRegion K
  balancedGenerator_absNorm :
    Ideal.absNorm (Ideal.span ({balancedGenerator} : Set (𝓞 K))) =
      q * Ideal.absNorm (cyclotomicRayCorrection ell K correctionIndex)

/-- The bounded corrected generator data is inhabited for every eligible
rational conductor. -/
theorem nonempty_boundedGeneratorEncodingData {q : ℕ} (hq : Eligible ell q) :
    Nonempty (BoundedGeneratorEncodingData ell K q) := by
  obtain ⟨P, i, r, a, b, hPprime, hPnorm, haprimary, haprime,
      haspan, hbspan, hab, hbcone, hbregion, hbnorm⟩ :=
    exists_balanced_primary_generator ell K hq
  exact ⟨
    { primeIdeal := P
      correctionIndex := i
      unitResidueIndex := r
      primaryGenerator := a
      balancedGenerator := b
      primeIdeal_isPrime := hPprime
      primeIdeal_absNorm := hPnorm
      primaryGenerator_isPrimary := haprimary
      primaryGenerator_isPrimeTo := haprime
      primaryGenerator_span := haspan
      balancedGenerator_span := hbspan
      primaryGenerator_eq := hab
      balancedGenerator_mem_cone := hbcone
      balancedGenerator_mem_region := hbregion
      balancedGenerator_absNorm := hbnorm }⟩

/-- A fixed choice of the bounded corrected generator data. -/
noncomputable def boundedGeneratorEncodingData {q : ℕ} (hq : Eligible ell q) :
    BoundedGeneratorEncodingData ell K q :=
  Classical.choice (nonempty_boundedGeneratorEncodingData ell K hq)

/-- For a finite set `S` of eligible rational primes, retain the correction
index and unit-residue index together with the balanced generator. -/
noncomputable def encodeEligibleFinset (S : Finset ℕ)
    (hS : ∀ q ∈ S, Eligible ell q) (q : ↑S) :
    CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K × 𝓞 K :=
  let data := boundedGeneratorEncodingData ell K (hS q.1 q.2)
  (data.correctionIndex, data.unitResidueIndex, data.balancedGenerator)

/-- The correction-tagged bounded generator remembers its rational
conductor.  Equality of the correction tag and generator makes the two
principal norms equal, and the nonzero correction norm can be cancelled. -/
theorem encodeEligibleFinset_injective (S : Finset ℕ)
    (hS : ∀ q ∈ S, Eligible ell q) :
    Function.Injective (encodeEligibleFinset ell K S hS) := by
  classical
  intro p q hpq
  let dp := boundedGeneratorEncodingData ell K (hS p.1 p.2)
  let dq := boundedGeneratorEncodingData ell K (hS q.1 q.2)
  have hpq' :
      (dp.correctionIndex, dp.unitResidueIndex, dp.balancedGenerator) =
        (dq.correctionIndex, dq.unitResidueIndex, dq.balancedGenerator) := by
    simpa only [encodeEligibleFinset, dp, dq] using hpq
  have hi : dp.correctionIndex = dq.correctionIndex :=
    congrArg Prod.fst hpq'
  have hb : dp.balancedGenerator = dq.balancedGenerator :=
    congrArg (fun z ↦ z.2.2) hpq'
  have hmul :
      p.1 * Ideal.absNorm
          (cyclotomicRayCorrection ell K dp.correctionIndex) =
        q.1 * Ideal.absNorm
          (cyclotomicRayCorrection ell K dp.correctionIndex) := by
    calc
      p.1 * Ideal.absNorm
          (cyclotomicRayCorrection ell K dp.correctionIndex) =
          Ideal.absNorm
            (Ideal.span ({dp.balancedGenerator} : Set (𝓞 K))) :=
        dp.balancedGenerator_absNorm.symm
      _ = Ideal.absNorm
            (Ideal.span ({dq.balancedGenerator} : Set (𝓞 K))) := by
        rw [hb]
      _ = q.1 * Ideal.absNorm
          (cyclotomicRayCorrection ell K dq.correctionIndex) :=
        dq.balancedGenerator_absNorm
      _ = q.1 * Ideal.absNorm
          (cyclotomicRayCorrection ell K dp.correctionIndex) := by
        rw [hi]
  have hcorrectionPos :
      0 < Ideal.absNorm
        (cyclotomicRayCorrection ell K dp.correctionIndex) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (cyclotomicRayCorrection_ne_bot ell K dp.correctionIndex))
  apply Subtype.ext
  exact Nat.mul_right_cancel hcorrectionPos hmul

/-- The finite image of the bounded correction/residue/generator encoding. -/
noncomputable def encodedEligibleFinset (S : Finset ℕ)
    (hS : ∀ q ∈ S, Eligible ell q) :
    Finset
      (CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K × 𝓞 K) := by
  classical
  exact S.attach.image (encodeEligibleFinset ell K S hS)

/-- Passing from eligible rational conductors to the finite tagged generator
image loses no cardinality. -/
theorem card_encodedEligibleFinset (S : Finset ℕ)
    (hS : ∀ q ∈ S, Eligible ell q) :
    (encodedEligibleFinset ell K S hS).card = S.card := by
  classical
  rw [encodedEligibleFinset,
    Finset.card_image_of_injective _
      (encodeEligibleFinset_injective ell K S hS), Finset.card_attach]

end

end Erdos980.ElliottTail.RationalPrimeGeneratorBridge
