/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.KummerPatterns
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The quadratic constant in Erdős problem 980

This file proves the multiquadratic degree calculation needed to identify
Elliott's general constant with Erdős's dyadic constant when `k = 2`.
-/

namespace Erdos980

open Polynomial NumberField Chebotarev Filter Topology
open NaturalChebotarev.SplitTransfer

noncomputable section

/-- The relative algebra structure supplied by the canonical embedding from
one quadratic Kummer level to the next. -/
noncomputable def quadraticStepAlgebra (r : ℕ) :
    Algebra (KummerField 2 r) (KummerField 2 (r + 1)) :=
  (kummerFieldEmbedding (by norm_num) r).toRingHom.toAlgebra

local instance (r : ℕ) : Algebra (KummerField 2 r) (KummerField 2 (r + 1)) :=
  quadraticStepAlgebra r

local instance (r : ℕ) : IsScalarTower ℚ (KummerField 2 r) (KummerField 2 (r + 1)) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((kummerFieldEmbedding (by norm_num) r).commutes x).symm

/-- The one new quadratic factor at step `r`. -/
def quadraticStepPolynomial (r : ℕ) : Polynomial (KummerField 2 r) :=
  (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ)).map
    (algebraMap ℚ (KummerField 2 r))

private theorem kummerFieldPolynomial_two_succ (r : ℕ) :
    kummerFieldPolynomial 2 (r + 1) =
      kummerFieldPolynomial 2 r *
        (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ)) := by
  rw [kummerFieldPolynomial, kummerFieldPolynomial,
    Finset.prod_range_succ, mul_assoc]

private theorem old_roots_mem_step_algebraMap (r : ℕ) :
    ∀ x ∈ (kummerFieldPolynomial 2 r).rootSet (KummerField 2 (r + 1)),
      x ∈ (algebraMap (KummerField 2 r)
        (KummerField 2 (r + 1))).range := by
  letI : Polynomial.IsSplittingField ℚ (KummerField 2 r)
      (kummerFieldPolynomial 2 r) :=
    Polynomial.IsSplittingField.splittingField _
  have h := Polynomial.IsSplittingField.adjoin_rootSet_eq_range
    (KummerField 2 r) (kummerFieldPolynomial 2 r)
    (kummerFieldEmbedding (by norm_num) r)
  intro x hx
  change x ∈ (kummerFieldEmbedding (by norm_num) r).range
  rw [← h]
  exact Algebra.subset_adjoin hx

private theorem quadraticStepPolynomial_splits (r : ℕ) :
    ((quadraticStepPolynomial r).map
      (algebraMap (KummerField 2 r) (KummerField 2 (r + 1)))).Splits := by
  letI : Polynomial.IsSplittingField ℚ (KummerField 2 (r + 1))
      (kummerFieldPolynomial 2 (r + 1)) :=
    Polynomial.IsSplittingField.splittingField _
  have htot := Polynomial.IsSplittingField.splits
    (KummerField 2 (r + 1)) (kummerFieldPolynomial 2 (r + 1))
  have hprod : ((kummerFieldPolynomial 2 r *
      (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ))).map
        (algebraMap ℚ (KummerField 2 (r + 1)))).Splits := by
    simpa only [← kummerFieldPolynomial_two_succ] using htot
  rw [Polynomial.map_mul] at hprod
  have hnew := (Polynomial.splits_mul
    (Polynomial.map_ne_zero (kummerFieldPolynomial_ne_zero (by norm_num) r))
    (Polynomial.map_ne_zero (Polynomial.monic_X_pow_sub_C
      (rationalPrime r : ℚ) (by norm_num)).ne_zero)).mp hprod |>.2
  simpa only [quadraticStepPolynomial, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq ℚ (KummerField 2 r)
      (KummerField 2 (r + 1))] using hnew

private theorem quadraticStep_adjoin_rootSet (r : ℕ) :
    Algebra.adjoin (KummerField 2 r)
      ((quadraticStepPolynomial r).rootSet (KummerField 2 (r + 1)) :
        Set (KummerField 2 (r + 1))) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  have htop := Polynomial.SplittingField.adjoin_rootSet
    (kummerFieldPolynomial 2 (r + 1))
  change Algebra.adjoin ℚ
      ((kummerFieldPolynomial 2 (r + 1)).rootSet
        (KummerField 2 (r + 1))) = ⊤ at htop
  have hle : Algebra.adjoin ℚ
      ((kummerFieldPolynomial 2 (r + 1)).rootSet
        (KummerField 2 (r + 1)) : Set (KummerField 2 (r + 1))) ≤
      (Algebra.adjoin (KummerField 2 r)
        ((quadraticStepPolynomial r).rootSet (KummerField 2 (r + 1)) :
          Set (KummerField 2 (r + 1)))).restrictScalars ℚ := by
    apply Algebra.adjoin_le
    intro y hy
    change y ∈ Algebra.adjoin (KummerField 2 r)
      ((quadraticStepPolynomial r).rootSet (KummerField 2 (r + 1)) :
        Set (KummerField 2 (r + 1)))
    have hy' : y ∈ (kummerFieldPolynomial 2 r *
        (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ))).rootSet
          (KummerField 2 (r + 1)) := by
      simpa only [← kummerFieldPolynomial_two_succ] using hy
    rw [rootSet_def,
      aroots_mul (mul_ne_zero
        (kummerFieldPolynomial_ne_zero (by norm_num) r)
        (Polynomial.monic_X_pow_sub_C
          (rationalPrime r : ℚ) (by norm_num)).ne_zero),
      Multiset.toFinset_add, Finset.coe_union] at hy'
    rcases hy' with hyold | hynew
    · obtain ⟨z, rfl⟩ := old_roots_mem_step_algebraMap r y hyold
      exact (Algebra.adjoin (KummerField 2 r)
        ((quadraticStepPolynomial r).rootSet (KummerField 2 (r + 1)) :
          Set (KummerField 2 (r + 1)))).algebraMap_mem z
    ·
      have hynewRoot : y ∈
          (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ)).rootSet
            (KummerField 2 (r + 1)) := by
        rw [rootSet_def]
        exact hynew
      have hrootEq :
          (quadraticStepPolynomial r).rootSet (KummerField 2 (r + 1)) =
            (Polynomial.X ^ 2 - Polynomial.C (rationalPrime r : ℚ)).rootSet
              (KummerField 2 (r + 1)) := by
        ext z
        change z ∈ ((Polynomial.X ^ 2 -
            Polynomial.C (rationalPrime r : ℚ)).map
              (algebraMap ℚ (KummerField 2 r))).rootSet
                (KummerField 2 (r + 1)) ↔ _
        rw [((Polynomial.monic_X_pow_sub_C
            (n := 2) (rationalPrime r : ℚ) (by norm_num)).map
              (algebraMap ℚ (KummerField 2 r))).mem_rootSet,
          (Polynomial.monic_X_pow_sub_C
            (n := 2) (rationalPrime r : ℚ) (by norm_num)).mem_rootSet]
        rw [aeval_def, aeval_def, Polynomial.eval₂_map,
          ← IsScalarTower.algebraMap_eq ℚ (KummerField 2 r)
            (KummerField 2 (r + 1))]
      rw [hrootEq]
      exact Algebra.subset_adjoin hynewRoot
  have : x ∈ Algebra.adjoin ℚ
      ((kummerFieldPolynomial 2 (r + 1)).rootSet
        (KummerField 2 (r + 1)) : Set (KummerField 2 (r + 1))) := by
    rw [htop]
    trivial
  exact hle this

private instance quadraticStep_isSplittingField (r : ℕ) :
    Polynomial.IsSplittingField (KummerField 2 r)
      (KummerField 2 (r + 1)) (quadraticStepPolynomial r) where
  splits' := quadraticStepPolynomial_splits r
  adjoin_rootSet' := quadraticStep_adjoin_rootSet r

private theorem quadraticStepPolynomial_eq (r : ℕ) :
    quadraticStepPolynomial r = Polynomial.X ^ 2 -
      Polynomial.C (algebraMap ℚ (KummerField 2 r) (rationalPrime r : ℚ)) := by
  simp [quadraticStepPolynomial]

private instance quadraticStep_isSplittingField_explicit (r : ℕ) :
    Polynomial.IsSplittingField (KummerField 2 r) (KummerField 2 (r + 1))
      (Polynomial.X ^ 2 -
        Polynomial.C (algebraMap ℚ (KummerField 2 r) (rationalPrime r : ℚ))) := by
  rw [← quadraticStepPolynomial_eq]
  infer_instance

/-- Each relative quadratic Kummer step has degree either one or two. -/
theorem quadraticStep_finrank_eq_one_or_two (r : ℕ) :
    Module.finrank (KummerField 2 r) (KummerField 2 (r + 1)) = 1 ∨
      Module.finrank (KummerField 2 r) (KummerField 2 (r + 1)) = 2 := by
  let q : KummerField 2 r :=
    algebraMap ℚ (KummerField 2 r) (rationalPrime r : ℚ)
  let f : Polynomial (KummerField 2 r) := Polynomial.X ^ 2 - Polynomial.C q
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C q (by norm_num)
  have hfdeg : f.natDegree = 2 := by simp [f]
  haveI : Polynomial.IsSplittingField (KummerField 2 r)
      (KummerField 2 (r + 1)) f := by
    dsimp only [f, q]
    infer_instance
  by_cases hirr : Irreducible f
  · right
    have hprim : IsPrimitiveRoot (-1 : KummerField 2 r) 2 :=
      IsPrimitiveRoot.neg_one 0 (by norm_num)
    have hroots : (primitiveRoots 2 (KummerField 2 r)).Nonempty := by
      refine ⟨-1, ?_⟩
      exact (mem_primitiveRoots (by norm_num)).mpr hprim
    exact finrank_of_isSplittingField_X_pow_sub_C hroots hirr
      (KummerField 2 (r + 1))
  · left
    have hrootsne : f.roots ≠ 0 := by
      intro hzero
      apply hirr
      exact (hfmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (by omega) (by omega)).mpr hzero
    obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hrootsne
    have hzeval : f.eval z = 0 := by
      exact (Polynomial.mem_roots hfmonic.ne_zero).mp hz
    have hsplit : f.Splits := Polynomial.Splits.of_natDegree_eq_two hfdeg hzeval
    have htopbot : (⊤ : Subalgebra (KummerField 2 r)
        (KummerField 2 (r + 1))) = ⊥ :=
      (Polynomial.IsSplittingField.splits_iff (KummerField 2 (r + 1)) f).mp hsplit
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      (Algebra.bijective_algebraMap_iff.mpr htopbot)

/-- If a quadratic step had relative degree one, complete splitting at the
lower level would ascend across every prime unramified at the upper level. -/
private theorem isCompletelySplit_succ_of_finrank_one
    (r : ℕ)
    (hdegree : Module.finrank (KummerField 2 r) (KummerField 2 (r + 1)) = 1)
    {p : ℕ} (hbase : IsCompletelySplit (KummerField 2 r) p)
    (hunr : UnramifiedIn ℚ (KummerField 2 (r + 1)) (rationalIdeal p)) :
    IsCompletelySplit (KummerField 2 (r + 1)) p := by
  letI : (rationalIdeal p).IsPrime := rationalIdeal_isPrime hbase.1
  have hp0 : rationalIdeal p ≠ ⊥ := hunr.ne_bot
  letI : (rationalIdeal p).IsMaximal :=
    (rationalIdeal_isPrime hbase.1).isMaximal hp0
  obtain ⟨P, hPprime, hlo, hP0⟩ :=
    exists_prime_liesOver ℚ (KummerField 2 (r + 1))
      (rationalIdeal p) hunr.ne_bot
  letI : P.IsPrime := hPprime
  let Q : Ideal (𝓞 (KummerField 2 r)) := P.under (𝓞 (KummerField 2 r))
  have hQprime : Q.IsPrime := Ideal.IsPrime.under (𝓞 (KummerField 2 r)) P
  letI : Q.IsPrime := hQprime
  have hQ0 : Q ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 (KummerField 2 r)) hP0
  letI : Q.IsMaximal := hQprime.isMaximal hQ0
  have hPQ : P.LiesOver Q :=
    Ideal.over_under (A := 𝓞 (KummerField 2 r)) (P := P)
  letI : P.LiesOver Q := hPQ
  have hQlo : Q.LiesOver (rationalIdeal p) := by
    refine ⟨?_⟩
    rw [show Q.under (𝓞 ℚ) = P.under (𝓞 ℚ) by
      simp only [Q, Ideal.under_under], hlo.over]
  letI : Q.LiesOver (rationalIdeal p) := hQlo
  have hbaseDeg : (rationalIdeal p).inertiaDeg' Q = 1 := by
    have h := residueDegree_eq_one_of_isCompletelySplit
      (KummerField 2 r) hbase hQprime hQ0 hQlo
    simpa only [residueDegree, hQlo.over.symm] using h
  have hrel_le : Q.inertiaDeg' P ≤
      Module.finrank (KummerField 2 r) (KummerField 2 (r + 1)) := by
    letI : NoZeroSMulDivisors (𝓞 (KummerField 2 r))
        (𝓞 (KummerField 2 (r + 1))) := {
      eq_zero_or_eq_zero_of_smul_eq_zero {c} {x} hcx := by
        by_cases hc : c = 0
        · exact Or.inl hc
        · exact Or.inr ((smul_eq_zero_iff_right hc).mp hcx) }
    exact Ideal.inertiaDeg_le_finrank
      (R := 𝓞 (KummerField 2 r)) (S := 𝓞 (KummerField 2 (r + 1)))
      (K := KummerField 2 r) (L := KummerField 2 (r + 1)) P hQ0
  have hrel : Q.inertiaDeg' P = 1 := by
    have hpos : 0 < Q.inertiaDeg' P := Ideal.inertiaDeg'_pos' Q P
    omega
  have htower := Ideal.inertiaDeg'_algebra_tower (rationalIdeal p) Q P
  have hglobal : (rationalIdeal p).inertiaDeg' P = 1 := by
    rw [hbaseDeg, hrel] at htower
    simpa using htower
  have hpbelow : primeBelow (KummerField 2 (r + 1)) P = p := by
    rw [primeBelow, hlo.over.symm, absNorm_rationalIdeal]
  have hresidue : residueDegree (KummerField 2 (r + 1)) P = 1 := by
    simpa only [residueDegree, hlo.over.symm] using hglobal
  have hsplit := isCompletelySplit_primeBelow_of_residueDegree_eq_one
    (KummerField 2 (r + 1)) hPprime hP0 (hlo.over.symm ▸ hunr) hresidue
  rwa [hpbelow] at hsplit

end

end Erdos980
