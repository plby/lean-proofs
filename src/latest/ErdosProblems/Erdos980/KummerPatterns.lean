/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib
import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Transfer

/-!
# The Kummer pattern constants for Erdős problem 980

This file isolates the exact algebraic and real-series objects that occur in
the Chebotarev part of Elliott's proof.  Indices of rational primes are
zero-based: `rationalPrime 0 = 2`.  Thus `kummerFieldPolynomial k r` adjoins
the `k`-th roots of the first `r` rational primes, together with all `k`-th
roots of unity, and `patternWeight k j` is the difference between the
complete-splitting densities at levels `j` and `j + 1`.
-/

namespace Erdos980

open scoped BigOperators
open Polynomial

noncomputable section

/-- The zero-indexed sequence `2, 3, 5, ...` of rational primes. -/
def rationalPrime (j : ℕ) : ℕ := Nat.nth Nat.Prime j

theorem rationalPrime_prime (j : ℕ) : Nat.Prime (rationalPrime j) := by
  exact Nat.prime_nth_prime j

theorem rationalPrime_pos (j : ℕ) : 0 < rationalPrime j :=
  (rationalPrime_prime j).pos

theorem rationalPrime_strictMono : StrictMono rationalPrime := by
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime

/-- The polynomial whose splitting field is
`ℚ(ζ_k, q_0^(1/k), ..., q_(r-1)^(1/k))`.

Using a single product polynomial makes this a canonical Lean type, rather
than choosing an algebraic closure and a family of roots in it. -/
def kummerFieldPolynomial (k r : ℕ) : Polynomial ℚ :=
  Polynomial.cyclotomic k ℚ *
    ∏ j ∈ Finset.range r,
      (Polynomial.X ^ k - Polynomial.C (rationalPrime j : ℚ))

/-- The integral model whose reductions modulo rational primes encode the
same finite radical pattern. -/
def kummerIntegralPolynomial (k r : ℕ) : Polynomial ℤ :=
  Polynomial.cyclotomic k ℤ *
    ∏ j ∈ Finset.range r,
      (Polynomial.X ^ k - Polynomial.C (rationalPrime j : ℤ))

theorem kummerIntegralPolynomial_map_rat (k r : ℕ) :
    (kummerIntegralPolynomial k r).map (Int.castRingHom ℚ) =
      kummerFieldPolynomial k r := by
  simp only [kummerIntegralPolynomial, kummerFieldPolynomial,
    Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Int.coe_castRingHom, Int.cast_natCast,
    Polynomial.map_cyclotomic_int]

/-- A canonical model of the finite Kummer splitting field at level `r`. -/
abbrev KummerField (k r : ℕ) : Type :=
  (kummerFieldPolynomial k r).SplittingField

instance kummerField_numberField (k r : ℕ) :
    NumberField (KummerField k r) := by
  change NumberField ((kummerFieldPolynomial k r).SplittingField)
  exact NumberField.of_module_finite ℚ
    ((kummerFieldPolynomial k r).SplittingField)

instance kummerField_isGalois (k r : ℕ) :
    IsGalois ℚ (KummerField k r) := by
  rw [isGalois_iff]
  change Algebra.IsSeparable ℚ
      ((kummerFieldPolynomial k r).SplittingField) ∧
    Normal ℚ ((kummerFieldPolynomial k r).SplittingField)
  exact ⟨inferInstance,
    Polynomial.SplittingField.instNormal (kummerFieldPolynomial k r)⟩

theorem kummerFieldPolynomial_monic {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    (kummerFieldPolynomial k r).Monic := by
  apply (Polynomial.cyclotomic.monic k ℚ).mul
  exact Polynomial.monic_prod_of_monic _ _ fun j _ =>
    Polynomial.monic_X_pow_sub_C _ hk

theorem kummerFieldPolynomial_ne_zero {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    kummerFieldPolynomial k r ≠ 0 :=
  (kummerFieldPolynomial_monic hk r).ne_zero

theorem kummerFieldPolynomial_dvd_succ (k r : ℕ) :
    kummerFieldPolynomial k r ∣ kummerFieldPolynomial k (r + 1) := by
  rw [kummerFieldPolynomial, kummerFieldPolynomial, Finset.prod_range_succ]
  refine ⟨Polynomial.X ^ k - Polynomial.C (rationalPrime r : ℚ), ?_⟩
  rw [mul_assoc]

/-- The canonical embedding obtained because every root present at level `r`
is still present at level `r + 1`. -/
def kummerFieldEmbedding {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    KummerField k r →ₐ[ℚ] KummerField k (r + 1) := by
  apply Polynomial.SplittingField.lift (kummerFieldPolynomial k r)
  apply (Polynomial.SplittingField.splits
    (kummerFieldPolynomial k (r + 1))).of_dvd
  · exact Polynomial.map_ne_zero
      (kummerFieldPolynomial_ne_zero hk (r + 1))
  · exact (Polynomial.map_dvd_map'
      (algebraMap ℚ (KummerField k (r + 1)))).mpr
      (kummerFieldPolynomial_dvd_succ k r)

/-! ## Complete splitting descends in the Kummer tower -/

open NumberField Chebotarev
open NaturalChebotarev.SplitTransfer

/-- Unramifiedness descends in a tower of Galois number fields. -/
theorem unramifiedIn_tower_descend
    (L M : Type*) [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra ℚ L] [Algebra ℚ M] [Algebra L M] [IsScalarTower ℚ L M]
    [IsGalois ℚ L] [IsGalois ℚ M]
    (p : Ideal (𝓞 ℚ)) (hunr : UnramifiedIn ℚ M p) :
    UnramifiedIn ℚ L p := by
  have : IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 M) := inferInstance
  refine ⟨hunr.1, fun Q hQmax hQlo => ?_⟩
  have := hQmax
  have := hQlo
  have hQp : Q.IsPrime := hQmax.isPrime
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 Q
  obtain ⟨P, _, hPp, hPcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 M) Q ⊥ (by simp)
  have := hPp
  have hPloQ : P.LiesOver Q := ⟨hPcomap.symm⟩
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQbot P
  have hPmax : P.IsMaximal := hPp.isMaximal hPbot
  have hQunder : Ideal.under (𝓞 L) P = Q := hPloQ.over.symm
  have hpunder : Ideal.under (𝓞 ℚ) Q = p := hQlo.over.symm
  have hPlop : P.LiesOver p :=
    ⟨by rw [← hpunder, ← hQunder, Ideal.under_under]⟩
  have hunderP : Ideal.under (𝓞 ℚ) P = p := hPlop.over.symm
  have hP1 : (Ideal.under (𝓞 ℚ) P).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ P
      (hunderP ▸ hunr.1)]
    exact Ideal.ramificationIdx_eq_one_iff.mpr
      (hunr.2 P hPmax hPlop)
  rw [hunderP] at hP1
  have htower := Ideal.ramificationIdx'_algebra_tower
    (R := 𝓞 ℚ) (S := 𝓞 L) (T := 𝓞 M)
    (p := p) (P := Q) (Q := P) (Ideal.map_ne_bot_of_ne_bot hQbot)
    (Ideal.map_ne_bot_of_ne_bot hunr.1)
    (by rw [Ideal.map_le_iff_le_comap, hPcomap])
  rw [hP1] at htower
  have heQ : p.ramificationIdx' Q = 1 :=
    Nat.eq_one_of_mul_eq_one_right htower.symm
  rw [← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p Q hunr.1]
  exact heQ

/-- Complete splitting descends through a tower of Galois number fields.
The proof avoids any functoriality assumption on Frobenius classes: it uses
descent of unramifiedness and multiplicativity of residue degrees. -/
theorem isCompletelySplit_tower_descend
    (L M : Type*) [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra ℚ L] [Algebra ℚ M] [Algebra L M] [IsScalarTower ℚ L M]
    [IsGalois ℚ L] [IsGalois ℚ M]
    {p : ℕ} (hsplit : IsCompletelySplit M p) :
    IsCompletelySplit L p := by
  have hpprime : (rationalIdeal p).IsPrime :=
    rationalIdeal_isPrime hsplit.1
  have hpbot : rationalIdeal p ≠ ⊥ :=
    UnramifiedIn.ne_bot ℚ M hsplit.2.1
  have hpmax : (rationalIdeal p).IsMaximal := hpprime.isMaximal hpbot
  have hunrL : UnramifiedIn ℚ L (rationalIdeal p) :=
    unramifiedIn_tower_descend L M (rationalIdeal p) hsplit.2.1
  obtain ⟨Q, hQprime, hQlo, hQbot⟩ :=
    exists_prime_liesOver ℚ L (rationalIdeal p)
      (UnramifiedIn.ne_bot ℚ L hunrL)
  have hqprime : Q.IsPrime := hQprime
  have hQlies : Q.LiesOver (rationalIdeal p) := hQlo
  have hqmax : Q.IsMaximal := hQprime.isMaximal hQbot
  have hqmaxI : Q.IsMaximal := hqmax
  obtain ⟨P, hPprime, hPlo, hPbot⟩ :=
    exists_prime_liesOver L M Q hQbot
  have hpprime : P.IsPrime := hPprime
  have hPliesQ : P.LiesOver Q := hPlo
  have hPliesp : P.LiesOver (rationalIdeal p) :=
    Ideal.LiesOver.trans P Q (rationalIdeal p)
  have htop : residueDegree M P = 1 :=
    residueDegree_eq_one_of_isCompletelySplit M hsplit
      hPprime hPbot hPliesp
  have hpunder : P.under (𝓞 ℚ) = rationalIdeal p := hPliesp.over.symm
  have hqunder : Q.under (𝓞 ℚ) = rationalIdeal p := hQlo.over.symm
  have htop' : (rationalIdeal p).inertiaDeg' P = 1 := by
    simpa only [residueDegree, hpunder] using htop
  have htower := Ideal.inertiaDeg'_algebra_tower
    (rationalIdeal p) Q P
  rw [htop'] at htower
  have hbottom' : (rationalIdeal p).inertiaDeg' Q = 1 :=
    Nat.eq_one_of_mul_eq_one_right htower.symm
  have hbottom : residueDegree L Q = 1 := by
    simpa only [residueDegree, hqunder] using hbottom'
  have hsplitQ := isCompletelySplit_primeBelow_of_residueDegree_eq_one L
    hQprime hQbot (hqunder ▸ hunrL) hbottom
  have hbelow : primeBelow L Q = p := by
    rw [primeBelow, hqunder, absNorm_rationalIdeal]
  rwa [hbelow] at hsplitQ

/-- Complete splitting descends from one canonical Kummer level to the
preceding level. -/
theorem isCompletelySplit_kummer_succ_descend
    {k : ℕ} (hk : k ≠ 0) (j p : ℕ)
    (hsplit : IsCompletelySplit (KummerField k (j + 1)) p) :
    IsCompletelySplit (KummerField k j) p := by
  let e := kummerFieldEmbedding hk j
  let : Algebra (KummerField k j) (KummerField k (j + 1)) :=
    e.toRingHom.toAlgebra
  let : IsScalarTower ℚ (KummerField k j) (KummerField k (j + 1)) :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  exact isCompletelySplit_tower_descend
    (KummerField k j) (KummerField k (j + 1)) hsplit

/-- The exact degree `D_{k,r} = [K_{k,r}:ℚ]`. -/
def kummerDegree (k r : ℕ) : ℕ :=
  Module.finrank ℚ (KummerField k r)

theorem kummerDegree_pos (k r : ℕ) : 0 < kummerDegree k r := by
  exact Module.finrank_pos

theorem kummerDegree_le_succ {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    kummerDegree k r ≤ kummerDegree k (r + 1) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := (kummerFieldEmbedding hk r).toLinearMap)
  exact
    (RingHom.injective (kummerFieldEmbedding hk r).toRingHom)

theorem kummerDegree_monotone {k : ℕ} (hk : k ≠ 0) :
    Monotone (kummerDegree k) := by
  exact monotone_nat_of_le_succ (kummerDegree_le_succ hk)

/-- At level zero only the roots of unity have been adjoined. -/
theorem kummerDegree_zero {k : ℕ} (hk : 0 < k) :
    kummerDegree k 0 = Nat.totient k := by
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero (k : ℚ) := ⟨by exact_mod_cast hk.ne'⟩
  change Module.finrank ℚ ((kummerFieldPolynomial k 0).SplittingField) =
    Nat.totient k
  have hp : kummerFieldPolynomial k 0 = Polynomial.cyclotomic k ℚ := by
    simp [kummerFieldPolynomial]
  rw [hp]
  change Module.finrank ℚ (CyclotomicField k ℚ) = Nat.totient k
  have : IsCyclotomicExtension {k} ℚ (CyclotomicField k ℚ) :=
    CyclotomicField.isCyclotomicExtension k ℚ
  exact IsCyclotomicExtension.finrank _
    (Polynomial.cyclotomic.irreducible_rat hk)

/-- Reciprocal complete-splitting density predicted by Chebotarev. -/
def splittingDensity (k r : ℕ) : ℝ :=
  (kummerDegree k r : ℝ)⁻¹

/-- The density of primes for which the first `j` rational primes are
`k`-th power residues and the next one is not. -/
def patternWeight (k j : ℕ) : ℝ :=
  splittingDensity k j - splittingDensity k (j + 1)

/-- The `j`-th summand in Elliott's constant. -/
def constantTerm (k j : ℕ) : ℝ :=
  rationalPrime j * patternWeight k j

/-- Elliott's constant, with Mathlib's total `tsum`; convergence is a
separate theorem/obligation. -/
def elliottConstant (k : ℕ) : ℝ :=
  ∑' j : ℕ, constantTerm k j

theorem sum_patternWeight_range (k N : ℕ) :
    (∑ j ∈ Finset.range N, patternWeight k j) =
      splittingDensity k 0 - splittingDensity k N := by
  simp only [patternWeight]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem patternWeight_nonneg_of_degree_mono (k j : ℕ)
    (h : kummerDegree k j ≤ kummerDegree k (j + 1)) :
    0 ≤ patternWeight k j := by
  rw [patternWeight, splittingDensity]
  exact sub_nonneg.mpr <| inv_anti₀
    (by exact_mod_cast kummerDegree_pos k j) (by exact_mod_cast h)

theorem patternWeight_nonneg {k : ℕ} (hk : k ≠ 0) (j : ℕ) :
    0 ≤ patternWeight k j :=
  patternWeight_nonneg_of_degree_mono k j
    (kummerDegree_le_succ hk j)

theorem patternWeight_pos_of_degree_strictMono (k j : ℕ)
    (h : kummerDegree k j < kummerDegree k (j + 1)) :
    0 < patternWeight k j := by
  change (kummerDegree k j : ℝ)⁻¹ -
    (kummerDegree k (j + 1) : ℝ)⁻¹ > 0
  have hjpos : (0 : ℝ) < kummerDegree k j := by
    exact_mod_cast kummerDegree_pos k j
  have hreal : (kummerDegree k j : ℝ) < kummerDegree k (j + 1) := by
    exact_mod_cast h
  exact sub_pos.mpr <| by
    simpa [one_div] using one_div_lt_one_div_of_lt hjpos hreal

theorem constantTerm_nonneg_of_degree_mono (k j : ℕ)
    (h : kummerDegree k j ≤ kummerDegree k (j + 1)) :
    0 ≤ constantTerm k j := by
  exact mul_nonneg (by exact_mod_cast (rationalPrime_pos j).le)
    (patternWeight_nonneg_of_degree_mono k j h)

theorem constantTerm_nonneg {k : ℕ} (hk : k ≠ 0) (j : ℕ) :
    0 ≤ constantTerm k j :=
  constantTerm_nonneg_of_degree_mono k j
    (kummerDegree_le_succ hk j)

theorem constantTerm_pos_of_degree_strictMono (k j : ℕ)
    (h : kummerDegree k j < kummerDegree k (j + 1)) :
    0 < constantTerm k j := by
  exact mul_pos (by exact_mod_cast rationalPrime_pos j)
    (patternWeight_pos_of_degree_strictMono k j h)

theorem elliottConstant_nonneg
    (k : ℕ) (hmono : Monotone (kummerDegree k)) :
    0 ≤ elliottConstant k := by
  exact tsum_nonneg fun j => constantTerm_nonneg_of_degree_mono k j
    (hmono (Nat.le_succ j))

theorem elliottConstant_nonneg_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    0 ≤ elliottConstant k :=
  elliottConstant_nonneg k (kummerDegree_monotone hk)

theorem elliottConstant_pos
    (k j : ℕ) (hsum : Summable (constantTerm k))
    (hmono : Monotone (kummerDegree k))
    (hstrict : kummerDegree k j < kummerDegree k (j + 1)) :
    0 < elliottConstant k := by
  rw [elliottConstant]
  exact (constantTerm_pos_of_degree_strictMono k j hstrict).trans_le
    (by
      simpa using hsum.sum_le_tsum {j}
        (fun i _ => constantTerm_nonneg_of_degree_mono k i
          (hmono (Nat.le_succ i))))

/-! ## Exact multiquadratic degree computation -/

/-- The positive square root of the `j`-th rational prime. -/
def quadraticGenerator (j : ℕ) : ℝ := Real.sqrt (rationalPrime j : ℝ)

theorem quadraticGenerator_sq (j : ℕ) :
    quadraticGenerator j ^ 2 = (rationalPrime j : ℝ) := by
  exact Real.sq_sqrt (by positivity)

/-- A rational is represented by a square times a squarefree product of the
first `r` rational primes. -/
def SupportRep (r : ℕ) (a : ℚ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ Finset.range r ∧
    ∃ u : ℚ, a = u ^ 2 * ∏ i ∈ s, (rationalPrime i : ℚ)

lemma rationalPrime_prod_squarefree (s : Finset ℕ) :
    Squarefree (∏ i ∈ s, rationalPrime i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (rationalPrime_prime i)
        (rationalPrime_prime j)).mpr
        (fun h => hij (rationalPrime_strictMono.injective h))
  · intro i hi
    exact (rationalPrime_prime i).prime.squarefree

lemma not_isSquare_prod_rationalPrime_of_nonempty
    {s : Finset ℕ} (hs : s.Nonempty) :
    ¬ IsSquare (((∏ i ∈ s, rationalPrime i) : ℕ) : ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨m, hm⟩
  have hsq := rationalPrime_prod_squarefree s
  have hmunit : IsUnit m := hsq m ⟨1, by simpa [hm]⟩
  have hm1 : m = 1 := Nat.isUnit_iff.mp hmunit
  subst m
  have hprod1 : ∏ i ∈ s, rationalPrime i = 1 := by simpa using hm
  obtain ⟨i, hi⟩ := hs
  have hdiv : rationalPrime i ∣ ∏ j ∈ s, rationalPrime j := by
    exact Finset.dvd_prod_of_mem (fun j => rationalPrime j) hi
  rw [hprod1] at hdiv
  exact (rationalPrime_prime i).not_dvd_one hdiv

lemma not_isSquare_nth_prime_mul_prod_earlier_rat
    {r : ℕ} {s : Finset ℕ} (hs : ∀ i ∈ s, i < r) :
    ¬ IsSquare
      ((rationalPrime r : ℚ) * ∏ i ∈ s, (rationalPrime i : ℚ)) := by
  have hrs : r ∉ s := by
    intro hr
    exact (Nat.lt_irrefl r) (hs r hr)
  have hnonempty : (insert r s).Nonempty := ⟨r, Finset.mem_insert_self r s⟩
  have h := not_isSquare_prod_rationalPrime_of_nonempty hnonempty
  rw [Finset.prod_insert hrs] at h
  exact_mod_cast h

lemma supportRep_zero_iff (a : ℚ) : SupportRep 0 a ↔ IsSquare a := by
  constructor
  · rintro ⟨s, hs, u, hu⟩
    have : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
    subst s
    refine ⟨u, ?_⟩
    simpa [pow_two] using hu
  · rintro ⟨u, hu⟩
    refine ⟨∅, by simp, u, ?_⟩
    simpa [pow_two] using hu

lemma supportRep_succ_iff (r : ℕ) (a : ℚ) :
    SupportRep (r + 1) a ↔
      SupportRep r a ∨ SupportRep r (a / rationalPrime r) := by
  constructor
  · rintro ⟨s, hs, u, hu⟩
    by_cases hr : r ∈ s
    · right
      refine ⟨s.erase r, ?_, u, ?_⟩
      · intro i hi
        have his : i ∈ s := (Finset.mem_erase.mp hi).2
        have hir1 : i < r + 1 := Finset.mem_range.mp (hs his)
        have hir : i ≠ r := (Finset.mem_erase.mp hi).1
        exact Finset.mem_range.mpr (by omega)
      · have hq : (rationalPrime r : ℚ) ≠ 0 := by
          exact_mod_cast (rationalPrime_pos r).ne'
        have hprod := Finset.mul_prod_erase s
          (fun i => (rationalPrime i : ℚ)) hr
        rw [← hprod] at hu
        rw [hu]
        field_simp
    · left
      refine ⟨s, ?_, u, hu⟩
      intro i hi
      have hir1 : i < r + 1 := Finset.mem_range.mp (hs hi)
      have hir : i ≠ r := fun h => hr (h ▸ hi)
      exact Finset.mem_range.mpr (by omega)
  · rintro (h | h)
    · rcases h with ⟨s, hs, u, hu⟩
      exact ⟨s, fun i hi => Finset.mem_range.mpr
        (Nat.lt.step (Finset.mem_range.mp (hs hi))), u, hu⟩
    · rcases h with ⟨s, hs, u, hu⟩
      have hrs : r ∉ s := by
        intro hr
        exact (Nat.lt_irrefl r) (Finset.mem_range.mp (hs hr))
      refine ⟨insert r s, ?_, u, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simp
        · exact Finset.mem_range.mpr
            (Nat.lt.step (Finset.mem_range.mp (hs hi)))
      · rw [Finset.prod_insert hrs]
        have hq : (rationalPrime r : ℚ) ≠ 0 := by
          exact_mod_cast (rationalPrime_pos r).ne'
        apply (div_eq_iff hq).mp at hu
        rw [hu]
        ring

lemma not_supportRep_rationalPrime (r : ℕ) :
    ¬ SupportRep r (rationalPrime r : ℚ) := by
  rintro ⟨s, hs, u, hu⟩
  apply not_isSquare_nth_prime_mul_prod_earlier_rat
    (fun i hi => Finset.mem_range.mp (hs hi))
  refine ⟨u * (∏ i ∈ s, (rationalPrime i : ℚ)), ?_⟩
  rw [hu]
  ring

private abbrev quadraticAdjoinPolynomial
    {K : Type*} [Field K] (d : K) : Polynomial K := X ^ 2 - C d

private lemma quadraticAdjoinRoot_sq {K : Type*} [Field K] (d : K) :
    AdjoinRoot.root (quadraticAdjoinPolynomial d) ^ 2 =
      algebraMap K _ d := by
  exact root_X_pow_sub_C_pow 2 d

private lemma quadraticAdjoinRoot_exists_eq_pair
    {K : Type*} [Field K] (d : K)
    (x : AdjoinRoot (quadraticAdjoinPolynomial d)) :
    ∃ u v : K, x = algebraMap K _ u +
      algebraMap K _ v * AdjoinRoot.root (quadraticAdjoinPolynomial d) := by
  let : Nontrivial (AdjoinRoot (quadraticAdjoinPolynomial d)) :=
    AdjoinRoot.nontrivial _
      (by simp [quadraticAdjoinPolynomial, Polynomial.degree_X_pow_sub_C])
  let pb : PowerBasis K (AdjoinRoot (quadraticAdjoinPolynomial d)) :=
    AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (by norm_num) d)
  obtain ⟨f, hf, hxf⟩ := pb.exists_eq_aeval x
  have hf1 : f.natDegree ≤ 1 := by
    have hpbdim : pb.dim = 2 := by
      simp [pb, AdjoinRoot.powerBasis_dim, quadraticAdjoinPolynomial]
    rw [hpbdim] at hf
    omega
  obtain ⟨v, u, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf1
  refine ⟨u, v, ?_⟩
  rw [hxf]
  simp [pb, AdjoinRoot.powerBasis_gen, add_comm]

private lemma quadraticAdjoinRoot_pair_sq
    {K : Type*} [Field K] (d u v : K) :
    (algebraMap K (AdjoinRoot (quadraticAdjoinPolynomial d)) u +
      algebraMap K _ v * AdjoinRoot.root (quadraticAdjoinPolynomial d)) ^ 2 =
      algebraMap K _ (u ^ 2 + v ^ 2 * d) +
        algebraMap K _ (2 * u * v) *
          AdjoinRoot.root (quadraticAdjoinPolynomial d) := by
  rw [add_sq, mul_pow, quadraticAdjoinRoot_sq]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

private lemma quadraticAdjoinRoot_coeff_eq_zero
    {K : Type*} [Field K] (d a b c : K)
    (h : algebraMap K (AdjoinRoot (quadraticAdjoinPolynomial d)) a +
      algebraMap K _ b * AdjoinRoot.root (quadraticAdjoinPolynomial d) =
        algebraMap K _ c) : b = 0 := by
  have hm : (X ^ 2 - C d).Monic := monic_X_pow_sub_C _ (by norm_num)
  let : Nontrivial (AdjoinRoot (quadraticAdjoinPolynomial d)) :=
    AdjoinRoot.nontrivial _
      (by simp [quadraticAdjoinPolynomial, Polynomial.degree_X_pow_sub_C])
  let ar := AdjoinRoot.isAdjoinRootMonic (X ^ 2 - C d) hm
  have hc := congrArg (fun z => ar.coeff z 1) h
  rw [show algebraMap K (AdjoinRoot (quadraticAdjoinPolynomial d)) b *
      AdjoinRoot.root (quadraticAdjoinPolynomial d) =
      b • AdjoinRoot.root (quadraticAdjoinPolynomial d) by
        rw [Algebra.smul_def]] at hc
  simp only [map_add, LinearMap.add_apply, LinearMap.smul_apply] at hc
  rw [IsAdjoinRootMonic.coeff_algebraMap ar a,
    IsAdjoinRootMonic.coeff_algebraMap ar c] at hc
  simp only [map_smul] at hc
  have hroot : ar.root =
      AdjoinRoot.root (quadraticAdjoinPolynomial d) := rfl
  rw [← hroot] at hc
  rw [IsAdjoinRootMonic.coeff_root ar (by simp)] at hc
  simpa using hc

/-- In a quadratic `AdjoinRoot`, a scalar becomes a square exactly when it
was already a square or differs from the radicand by a square. -/
theorem isSquare_quadraticAdjoinRoot_iff
    {K : Type*} [Field K] [NeZero (2 : K)] (d a : K) (_hd : d ≠ 0) :
    IsSquare (algebraMap K (AdjoinRoot (quadraticAdjoinPolynomial d)) a) ↔
      IsSquare a ∨ ∃ v : K, a = v ^ 2 * d := by
  let : Nontrivial (AdjoinRoot (quadraticAdjoinPolynomial d)) :=
    AdjoinRoot.nontrivial _
      (by simp [quadraticAdjoinPolynomial, Polynomial.degree_X_pow_sub_C])
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, hxuv⟩ := quadraticAdjoinRoot_exists_eq_pair d x
    rw [hxuv, ← pow_two, quadraticAdjoinRoot_pair_sq] at hx
    have huv : 2 * u * v = 0 :=
      quadraticAdjoinRoot_coeff_eq_zero d _ _ _ hx.symm
    rcases mul_eq_zero.mp huv with h2u | hv
    · rcases mul_eq_zero.mp h2u with h2 | hu
      · exact (NeZero.ne (2 : K) h2).elim
      right
      subst u
      refine ⟨v, ?_⟩
      apply RingHom.injective (algebraMap K
        (AdjoinRoot (quadraticAdjoinPolynomial d)))
      simpa using hx
    · left
      subst v
      refine ⟨u, ?_⟩
      apply RingHom.injective (algebraMap K
        (AdjoinRoot (quadraticAdjoinPolynomial d)))
      simpa [pow_two] using hx
  · rintro (ha | ⟨v, rfl⟩)
    · rcases ha with ⟨u, rfl⟩
      refine ⟨algebraMap K _ u, ?_⟩
      simp only [map_mul]
    · refine ⟨algebraMap K _ v *
        AdjoinRoot.root (quadraticAdjoinPolynomial d), ?_⟩
      rw [mul_mul_mul_comm,
        ← pow_two (AdjoinRoot.root (quadraticAdjoinPolynomial d)),
        quadraticAdjoinRoot_sq]
      simp only [map_mul, map_pow]
      ring

/-- The first `r` positive prime square roots in the common ambient field
`ℝ`. -/
def quadraticGeneratorSet (r : ℕ) : Set ℝ :=
  Set.range (fun i : Fin r => quadraticGenerator i)

lemma quadraticGeneratorSet_succ (r : ℕ) :
    quadraticGeneratorSet r ∪ {quadraticGenerator r} =
      quadraticGeneratorSet (r + 1) := by
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨⟨i, Nat.lt.step i.isLt⟩, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨⟨r, Nat.lt_succ_self r⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    by_cases hi : (i : ℕ) < r
    · left
      exact ⟨⟨i, hi⟩, rfl⟩
    · right
      rw [Set.mem_singleton_iff]
      apply congrArg quadraticGenerator
      omega

/-- A concrete common-ambient model of the multiquadratic field. -/
def QuadraticRangeTower (r : ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (quadraticGeneratorSet r)

lemma quadraticRangeTower_succ_eq (r : ℕ) :
    IntermediateField.restrictScalars ℚ
        (IntermediateField.adjoin (QuadraticRangeTower r) {quadraticGenerator r}) =
      QuadraticRangeTower (r + 1) := by
  change IntermediateField.restrictScalars ℚ
      (IntermediateField.adjoin
        (IntermediateField.adjoin ℚ (quadraticGeneratorSet r))
        {quadraticGenerator r}) =
    IntermediateField.adjoin ℚ (quadraticGeneratorSet (r + 1))
  rw [← quadraticGeneratorSet_succ,
    ← IntermediateField.adjoin_adjoin_left]
  rfl

def RangeSquare (r : ℕ) (a : ℚ) : Prop :=
  IsSquare (algebraMap ℚ (QuadraticRangeTower r) a)

lemma rangeSquare_zero_iff (a : ℚ) : RangeSquare 0 a ↔ IsSquare a := by
  unfold RangeSquare
  have hzero : QuadraticRangeTower 0 = (⊥ : IntermediateField ℚ ℝ) := by
    simp [QuadraticRangeTower, quadraticGeneratorSet]
  let e : QuadraticRangeTower 0 ≃ₐ[ℚ] ℚ :=
    (IntermediateField.equivOfEq hzero).trans
      (IntermediateField.botEquiv ℚ ℝ)
  constructor
  · intro h
    have hm := h.map e
    simpa using hm
  · intro h
    have hm := h.map e.symm
    simpa using hm

private lemma rangeGenerator_integral (r : ℕ) :
    IsIntegral (QuadraticRangeTower r) (quadraticGenerator r) := by
  let d : QuadraticRangeTower r :=
    algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ)
  refine ⟨X ^ 2 - C d, monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp [d, quadraticGenerator_sq]

private lemma rangeStep_irreducible
    (r : ℕ) (hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ)) :
    Irreducible (X ^ 2 - C
      (algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ))) := by
  rw [X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  intro b hb
  apply hnonsquare
  refine ⟨b, ?_⟩
  simpa [RangeSquare, pow_two] using hb.symm

private lemma rangeStep_minpoly
    (r : ℕ) (hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ)) :
    X ^ 2 - C
        (algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ)) =
      minpoly (QuadraticRangeTower r) (quadraticGenerator r) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact rangeStep_irreducible r hnonsquare
  · simp [quadraticGenerator_sq]
  · exact monic_X_pow_sub_C _ (by norm_num)

private noncomputable def rangeStepEquiv
    (r : ℕ) (hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ)) :
    AdjoinRoot (X ^ 2 - C
      (algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ))) ≃ₐ[QuadraticRangeTower r]
      IntermediateField.adjoin (QuadraticRangeTower r) {quadraticGenerator r} := by
  let e := IntermediateField.adjoinRootEquivAdjoin
    (QuadraticRangeTower r) (rangeGenerator_integral r)
  rw [← rangeStep_minpoly r hnonsquare] at e
  exact e

private noncomputable def rangeStepEquivTotal
    (r : ℕ) (hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ)) :
    AdjoinRoot (X ^ 2 - C
      (algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ))) ≃ₐ[ℚ]
      QuadraticRangeTower (r + 1) :=
  (rangeStepEquiv r hnonsquare).restrictScalars ℚ |>.trans
    (IntermediateField.equivOfEq (quadraticRangeTower_succ_eq r))

private lemma isSquare_map_rangeStepEquivTotal_iff
    (r : ℕ) (hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ))
    (a : ℚ) :
    IsSquare (algebraMap ℚ (QuadraticRangeTower (r + 1)) a) ↔
      IsSquare (algebraMap ℚ
        (AdjoinRoot (X ^ 2 - C
          (algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ)))) a) := by
  let e := rangeStepEquivTotal r hnonsquare
  constructor
  · intro h
    have hm := h.map e.symm
    rw [e.symm.commutes] at hm
    exact hm
  · intro h
    have hm := h.map e
    rw [e.commutes] at hm
    exact hm

lemma rangeSquare_succ_iff
    (r : ℕ) (ih : ∀ a : ℚ, RangeSquare r a ↔ SupportRep r a)
    (a : ℚ) :
    RangeSquare (r + 1) a ↔
      RangeSquare r a ∨ RangeSquare r (a / rationalPrime r) := by
  have hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ) :=
    (ih _).not.mpr (not_supportRep_rationalPrime r)
  rw [RangeSquare, isSquare_map_rangeStepEquivTotal_iff r hnonsquare a]
  let da : QuadraticRangeTower r :=
    algebraMap ℚ (QuadraticRangeTower r) a
  let dq : QuadraticRangeTower r :=
    algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ)
  have hdq : dq ≠ 0 := by
    intro h
    have hmap : algebraMap ℚ (QuadraticRangeTower r) (rationalPrime r : ℚ) =
        algebraMap ℚ (QuadraticRangeTower r) 0 := by
      simpa [dq] using h
    have hq : (rationalPrime r : ℚ) = 0 :=
      (algebraMap ℚ (QuadraticRangeTower r)).injective hmap
    have hq' : (rationalPrime r : ℚ) ≠ 0 := by
      exact_mod_cast (rationalPrime_pos r).ne'
    exact hq' hq
  have hbase : algebraMap ℚ
      (AdjoinRoot (X ^ 2 - C dq)) a =
      algebraMap (QuadraticRangeTower r)
        (AdjoinRoot (X ^ 2 - C dq)) da :=
    IsScalarTower.algebraMap_apply ℚ (QuadraticRangeTower r) _ a
  have hcriterion :
      IsSquare (algebraMap ℚ (AdjoinRoot (X ^ 2 - C dq)) a) ↔
        IsSquare da ∨ ∃ v : QuadraticRangeTower r, da = v ^ 2 * dq := by
    rw [hbase]
    exact isSquare_quadraticAdjoinRoot_iff dq da hdq
  rw [hcriterion]
  change (IsSquare da ∨ ∃ v : QuadraticRangeTower r, da = v ^ 2 * dq) ↔ _
  constructor
  · rintro (ha | ⟨v, hv⟩)
    · exact Or.inl ha
    · right
      refine ⟨v, ?_⟩
      rw [map_div₀ (algebraMap ℚ (QuadraticRangeTower r))]
      change da / dq = v * v
      apply (div_eq_iff hdq).mpr
      simpa [da, dq, pow_two] using hv
  · rintro (ha | hv)
    · exact Or.inl ha
    · right
      rcases hv with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      change da = v ^ 2 * dq
      rw [map_div₀ (algebraMap ℚ (QuadraticRangeTower r))] at hv
      change da / dq = v * v at hv
      have hmul := (div_eq_iff hdq).mp hv
      simpa [da, dq, pow_two] using hmul

theorem rangeSquare_iff_supportRep (r : ℕ) (a : ℚ) :
    RangeSquare r a ↔ SupportRep r a := by
  induction r generalizing a with
  | zero =>
      exact (rangeSquare_zero_iff a).trans (supportRep_zero_iff a).symm
  | succ r ih =>
      rw [rangeSquare_succ_iff r ih a, ih, ih, ← supportRep_succ_iff]

lemma quadraticRangeTower_finrank_succ (r : ℕ) :
    Module.finrank ℚ (QuadraticRangeTower (r + 1)) =
      2 * Module.finrank ℚ (QuadraticRangeTower r) := by
  have hnonsquare : ¬ RangeSquare r (rationalPrime r : ℚ) :=
    (rangeSquare_iff_supportRep r _).not.mpr
      (not_supportRep_rationalPrime r)
  let R := IntermediateField.adjoin
    (QuadraticRangeTower r) {quadraticGenerator r}
  have hrel : Module.finrank (QuadraticRangeTower r) R = 2 := by
    rw [IntermediateField.adjoin.finrank (rangeGenerator_integral r),
      ← rangeStep_minpoly r hnonsquare]
    exact Polynomial.natDegree_X_pow_sub_C
  have hmul := Module.finrank_mul_finrank ℚ (QuadraticRangeTower r) R
  let e : R ≃ₐ[ℚ] QuadraticRangeTower (r + 1) :=
    IntermediateField.equivOfEq (quadraticRangeTower_succ_eq r)
  rw [← e.toLinearEquiv.finrank_eq, ← hmul, hrel]
  omega

theorem quadraticRangeTower_finrank (r : ℕ) :
    Module.finrank ℚ (QuadraticRangeTower r) = 2 ^ r := by
  induction r with
  | zero =>
      let e : QuadraticRangeTower 0 ≃ₐ[ℚ] ℚ :=
        (IntermediateField.equivOfEq (by
          simp [QuadraticRangeTower, quadraticGeneratorSet])).trans
          (IntermediateField.botEquiv ℚ ℝ)
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_self, pow_zero]
  | succ r ih =>
      rw [quadraticRangeTower_finrank_succ, ih, pow_succ]
      omega

lemma kummerFieldPolynomial_two_map_splits_real (r : ℕ) :
    ((kummerFieldPolynomial 2 r).map (algebraMap ℚ ℝ)).Splits := by
  simp only [kummerFieldPolynomial, Polynomial.map_mul,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_cyclotomic]
  apply (Polynomial.splits_mul
    (Polynomial.cyclotomic.monic 2 ℝ).ne_zero
    (Finset.prod_ne_zero_iff.mpr fun j _ =>
      X_pow_sub_C_ne_zero (by norm_num) (rationalPrime j : ℝ))).2
  constructor
  · rw [Polynomial.cyclotomic_two]
    apply Polynomial.Splits.of_natDegree_le_one
    simpa using (Polynomial.natDegree_X_add_C (1 : ℝ)).le
  · rw [Polynomial.splits_prod_iff]
    · intro j hj
      exact X_pow_sub_C_splits_of_isPrimitiveRoot
        (IsPrimitiveRoot.neg_one 0 (by norm_num))
        (quadraticGenerator_sq j)
    · intro j hj
      exact X_pow_sub_C_ne_zero (by norm_num) (rationalPrime j : ℝ)

lemma quadraticGenerator_mem_kummerRootSet {r : ℕ} (i : Fin r) :
    quadraticGenerator i ∈ (kummerFieldPolynomial 2 r).rootSet ℝ := by
  rw [Polynomial.mem_rootSet']
  constructor
  · exact Polynomial.map_ne_zero (kummerFieldPolynomial_ne_zero (by norm_num) r)
  · simp only [kummerFieldPolynomial, Polynomial.aeval_def,
      Polynomial.eval₂_mul]
    apply mul_eq_zero_of_right
    rw [show Polynomial.eval₂ (algebraMap ℚ ℝ) (quadraticGenerator i)
        (∏ j ∈ Finset.range r,
          (X ^ 2 - C (rationalPrime j : ℚ))) =
        (Polynomial.eval₂RingHom (algebraMap ℚ ℝ) (quadraticGenerator i))
        (∏ j ∈ Finset.range r,
          (X ^ 2 - C (rationalPrime j : ℚ))) by rfl,
      map_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr i.isLt)
    simp [quadraticGenerator_sq]

def QuadraticRootField (r : ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ((kummerFieldPolynomial 2 r).rootSet ℝ)

lemma quadraticRangeTower_eq_rootField (r : ℕ) :
    QuadraticRangeTower r = QuadraticRootField r := by
  apply le_antisymm
  · rw [QuadraticRangeTower, IntermediateField.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _
      (quadraticGenerator_mem_kummerRootSet i)
  · rw [QuadraticRootField, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Polynomial.mem_rootSet'] at hx
    rcases hx with ⟨hn, heval⟩
    simp only [kummerFieldPolynomial, Polynomial.aeval_def,
      Polynomial.eval₂_mul, Polynomial.cyclotomic_two] at heval
    rw [show Polynomial.eval₂ (algebraMap ℚ ℝ) x
        (∏ j ∈ Finset.range r, (X ^ 2 - C (rationalPrime j : ℚ))) =
        (Polynomial.eval₂RingHom (algebraMap ℚ ℝ) x)
        (∏ j ∈ Finset.range r, (X ^ 2 - C (rationalPrime j : ℚ))) by rfl,
      map_prod] at heval
    change Polynomial.eval₂ (algebraMap ℚ ℝ) x (X + 1) *
      (∏ j ∈ Finset.range r,
        Polynomial.eval₂ (algebraMap ℚ ℝ) x
          (X ^ 2 - C (rationalPrime j : ℚ))) = 0 at heval
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_one, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Polynomial.eval₂_natCast] at heval
    rcases mul_eq_zero.mp heval with hlinear | hprod
    · have hxneg : x = -1 := by linarith
      rw [hxneg]
      exact (QuadraticRangeTower r).neg_mem
        ((QuadraticRangeTower r).one_mem)
    · obtain ⟨j, hj, hjzero⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hjlt : j < r := Finset.mem_range.mp hj
      have hsq : x ^ 2 = quadraticGenerator j ^ 2 := by
        rw [quadraticGenerator_sq]
        exact sub_eq_zero.mp hjzero
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
      · rw [hpos]
        exact IntermediateField.subset_adjoin ℚ _
          ⟨⟨j, hjlt⟩, rfl⟩
      · rw [hneg]
        exact (QuadraticRangeTower r).neg_mem <|
          IntermediateField.subset_adjoin ℚ _ ⟨⟨j, hjlt⟩, rfl⟩

instance quadraticRangeTower_isSplittingField (r : ℕ) :
    Polynomial.IsSplittingField ℚ (QuadraticRangeTower r)
      (kummerFieldPolynomial 2 r) := by
  let : Polynomial.IsSplittingField ℚ (QuadraticRootField r)
      (kummerFieldPolynomial 2 r) :=
    IntermediateField.adjoin_rootSet_isSplittingField
      (kummerFieldPolynomial_two_map_splits_real r)
  let e : QuadraticRootField r ≃ₐ[ℚ] QuadraticRangeTower r :=
    IntermediateField.equivOfEq (quadraticRangeTower_eq_rootField r).symm
  exact Polynomial.IsSplittingField.of_algEquiv
    (QuadraticRangeTower r) (kummerFieldPolynomial 2 r) e

/-- The concrete real multiquadratic field and the canonical splitting field
are equivalent over `ℚ`. -/
noncomputable def quadraticRangeTowerEquivKummerField (r : ℕ) :
    QuadraticRangeTower r ≃ₐ[ℚ] KummerField 2 r :=
  Polynomial.IsSplittingField.algEquiv
    (QuadraticRangeTower r) (kummerFieldPolynomial 2 r)

/-- The exact multiquadratic degree formula. -/
theorem kummerDegree_two (r : ℕ) : kummerDegree 2 r = 2 ^ r := by
  rw [kummerDegree]
  exact (quadraticRangeTowerEquivKummerField r).toLinearEquiv.finrank_eq.symm.trans
    (quadraticRangeTower_finrank r)

/-! ## The exact quadratic specialization -/

theorem dyadic_reciprocal_difference (j : ℕ) :
    (1 / (2 ^ j : ℝ) - 1 / (2 ^ (j + 1) : ℝ)) =
      1 / (2 ^ (j + 1) : ℝ) := by
  rw [pow_succ]
  field_simp
  ring

theorem patternWeight_two_eq_dyadic_of_degree
    (hdegree : ∀ r, kummerDegree 2 r = 2 ^ r) (j : ℕ) :
    patternWeight 2 j = 1 / (2 ^ (j + 1) : ℝ) := by
  change (kummerDegree 2 j : ℝ)⁻¹ -
    (kummerDegree 2 (j + 1) : ℝ)⁻¹ = _
  rw [hdegree j, hdegree (j + 1)]
  push_cast
  simpa [one_div] using dyadic_reciprocal_difference j

theorem patternWeight_two_eq_dyadic (j : ℕ) :
    patternWeight 2 j = 1 / (2 ^ (j + 1) : ℝ) :=
  patternWeight_two_eq_dyadic_of_degree kummerDegree_two j

theorem constantTerm_two_eq_dyadic_of_degree
    (hdegree : ∀ r, kummerDegree 2 r = 2 ^ r) (j : ℕ) :
    constantTerm 2 j =
      (rationalPrime j : ℝ) / (2 ^ (j + 1) : ℝ) := by
  rw [constantTerm, patternWeight_two_eq_dyadic_of_degree hdegree]
  exact mul_one_div _ _

theorem constantTerm_two_eq_dyadic (j : ℕ) :
    constantTerm 2 j =
      (rationalPrime j : ℝ) / (2 ^ (j + 1) : ℝ) :=
  constantTerm_two_eq_dyadic_of_degree kummerDegree_two j

theorem elliottConstant_two_eq_dyadic_of_degree
    (hdegree : ∀ r, kummerDegree 2 r = 2 ^ r) :
    elliottConstant 2 =
      ∑' j : ℕ, (rationalPrime j : ℝ) / (2 ^ (j + 1) : ℝ) := by
  apply tsum_congr
  exact constantTerm_two_eq_dyadic_of_degree hdegree

/-- Elliott's degree formula specializes exactly to Erdős's constant
`∑ q_j / 2^(j+1)` (zero-based indexing). -/
theorem elliottConstant_two_eq_dyadic :
    elliottConstant 2 =
      ∑' j : ℕ, (rationalPrime j : ℝ) / (2 ^ (j + 1) : ℝ) :=
  elliottConstant_two_eq_dyadic_of_degree kummerDegree_two

/-! ## Complete-splitting patterns and their exact density difference -/

open Asymptotics Filter Topology
open NaturalChebotarev.SplitTransfer

/-- Subtract two asymptotics on the same scale.  The nonzero condition is
exactly what is needed for the difference of the main terms to remain a
valid asymptotic comparison function. -/
theorem isEquivalent_sub_const_mul
    {α : Type*} {l : Filter α} {A B F : α → ℝ} {a b : ℝ}
    (hA : A ~[l] (fun x => a * F x))
    (hB : B ~[l] (fun x => b * F x)) (hab : a - b ≠ 0) :
    (fun x => A x - B x) ~[l] (fun x => (a - b) * F x) := by
  apply IsLittleO.isEquivalent
  have hAo : (fun x => A x - a * F x) =o[l] F :=
    hA.isLittleO.of_const_mul_right
  have hBo : (fun x => B x - b * F x) =o[l] F :=
    hB.isLittleO.of_const_mul_right
  have hsub :
      (fun x => (A x - a * F x) - (B x - b * F x)) =o[l] F :=
    hAo.sub hBo
  have htarget := hsub.const_mul_right hab
  apply htarget.congr'
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      ring
  · exact Eventually.of_forall fun _ => rfl

/-- Convert a nonzero constant-multiple asymptotic into its ratio limit. -/
theorem ratio_tendsto_of_isEquivalent_const_mul
    {α : Type*} {l : Filter α} {A scale : α → ℝ} {δ : ℝ}
    (hδ : δ ≠ 0) (hscale : ∀ᶠ x in l, scale x ≠ 0)
    (h : A ~[l] (fun x => δ * scale x)) :
    Tendsto (fun x => A x / scale x) l (𝓝 δ) := by
  have htarget : ∀ᶠ x in l, δ * scale x ≠ 0 :=
    hscale.mono fun x hx => mul_ne_zero hδ hx
  have hratio : Tendsto
      (A / (fun x => δ * scale x)) l (𝓝 1) :=
    (isEquivalent_iff_tendsto_one htarget).mp h
  have hmul : Tendsto
      (fun x => δ * (A / (fun y => δ * scale y)) x) l (𝓝 (δ * 1)) :=
    (tendsto_const_nhds (x := δ)).mul hratio
  simpa only [mul_one] using Tendsto.congr' (by
    filter_upwards [hscale] with x hx
    simp only [Pi.div_apply]
    field_simp [hδ, hx]) hmul

/-- The bounded set of rational primes that split completely at Kummer level
`j`, but not at level `j + 1`. -/
def KummerSplitPatternUpTo (k j x : ℕ) :=
  {p : ℕ // IsCompletelySplit (KummerField k j) p ∧
    ¬ IsCompletelySplit (KummerField k (j + 1)) p ∧ p ≤ x}

instance finite_kummerSplitPatternUpTo (k j x : ℕ) :
    Finite (KummerSplitPatternUpTo k j x) :=
  Finite.of_injective
    (fun p : KummerSplitPatternUpTo k j x =>
      (⟨p.1, Nat.lt_succ_of_le p.2.2.2⟩ : Fin (x + 1)))
    (fun _ _ h => Subtype.ext (by simpa using congrArg Fin.val h))

/-- The number of rational primes at most `x` with the exact complete-splitting
pattern `K_{k,j}` split and `K_{k,j+1}` nonsplit. -/
def kummerSplitPatternCount (k j x : ℕ) : ℕ :=
  Nat.card (KummerSplitPatternUpTo k j x)

private def splitPatternPartition (k j x : ℕ)
    (_hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p) :
    SplitPrimesUpTo (KummerField k j) x →
      KummerSplitPatternUpTo k j x ⊕
        SplitPrimesUpTo (KummerField k (j + 1)) x := fun p => by
  by_cases hnext : IsCompletelySplit (KummerField k (j + 1)) p.1
  · exact Sum.inr ⟨p.1, hnext, p.2.2⟩
  · exact Sum.inl ⟨p.1, p.2.1, hnext, p.2.2⟩

private def splitPatternValue (k j x : ℕ) :
    KummerSplitPatternUpTo k j x ⊕
        SplitPrimesUpTo (KummerField k (j + 1)) x → ℕ
  | Sum.inl p => p.1
  | Sum.inr p => p.1

private theorem splitPatternValue_partition (k j x : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p)
    (p : SplitPrimesUpTo (KummerField k j) x) :
    splitPatternValue k j x (splitPatternPartition k j x hnested p) = p.1 := by
  simp only [splitPatternPartition]
  split <;> rfl

private theorem splitPatternPartition_bijective (k j x : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p) :
    Function.Bijective (splitPatternPartition k j x hnested) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    have h := congrArg (splitPatternValue k j x) hpq
    simpa only [splitPatternValue_partition] using h
  · intro z
    rcases z with a | b
    · refine ⟨⟨a.1, a.2.1, a.2.2.2⟩, ?_⟩
      simp only [splitPatternPartition]
      rw [dif_neg a.2.2.1]
      rfl
    · refine ⟨⟨b.1, hnested b.1 b.2.1, b.2.2⟩, ?_⟩
      simp only [splitPatternPartition]
      rw [dif_pos b.2.1]
      rfl

private def splitPatternEquiv (k j x : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p) :
    SplitPrimesUpTo (KummerField k j) x ≃
      KummerSplitPatternUpTo k j x ⊕
        SplitPrimesUpTo (KummerField k (j + 1)) x :=
  Equiv.ofBijective (splitPatternPartition k j x hnested)
    (splitPatternPartition_bijective k j x hnested)

/-- Exact decomposition of level-`j` split primes into the exact pattern and
level-`j+1` split primes, whenever complete splitting descends in the tower. -/
theorem splitPrimeCount_eq_kummerSplitPatternCount_add (k j x : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p) :
    splitPrimeCount (KummerField k j) x =
      kummerSplitPatternCount k j x +
        splitPrimeCount (KummerField k (j + 1)) x := by
  change Nat.card (SplitPrimesUpTo (KummerField k j) x) =
    Nat.card (KummerSplitPatternUpTo k j x) +
      Nat.card (SplitPrimesUpTo (KummerField k (j + 1)) x)
  rw [Nat.card_congr (splitPatternEquiv k j x hnested), Nat.card_sum]

theorem kummerSplitPatternCount_eq_sub (k j x : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p) :
    kummerSplitPatternCount k j x =
      splitPrimeCount (KummerField k j) x -
        splitPrimeCount (KummerField k (j + 1)) x := by
  have h := splitPrimeCount_eq_kummerSplitPatternCount_add k j x hnested
  omega

theorem kummerSplitPatternCount_eq_sub_of_ne_zero
    {k : ℕ} (hk : k ≠ 0) (j x : ℕ) :
    kummerSplitPatternCount k j x =
      splitPrimeCount (KummerField k j) x -
        splitPrimeCount (KummerField k (j + 1)) x :=
  kummerSplitPatternCount_eq_sub k j x
    (fun p => isCompletelySplit_kummer_succ_descend hk j p)

/-- The exact nested complete-splitting formulation of the fixed-pattern
density.  It reduces the pattern theorem to the two adjacent completely-split
prime asymptotics and the strict degree increase. -/
theorem kummerSplitPatternCount_isEquivalent
    (k j : ℕ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p)
    (hlevel : (fun x : ℕ =>
        (splitPrimeCount (KummerField k j) x : ℝ))
      ~[atTop] (fun x : ℕ => splittingDensity k j *
        ((x : ℝ) / Real.log (x : ℝ))))
    (hsucc : (fun x : ℕ =>
        (splitPrimeCount (KummerField k (j + 1)) x : ℝ))
      ~[atTop] (fun x : ℕ => splittingDensity k (j + 1) *
        ((x : ℝ) / Real.log (x : ℝ))))
    (hstrict : kummerDegree k j < kummerDegree k (j + 1)) :
    (fun x : ℕ => (kummerSplitPatternCount k j x : ℝ))
      ~[atTop] (fun x : ℕ => patternWeight k j *
        ((x : ℝ) / Real.log (x : ℝ))) := by
  have hdiff := isEquivalent_sub_const_mul hlevel hsucc
    (ne_of_gt (patternWeight_pos_of_degree_strictMono k j hstrict))
  apply hdiff.congr_left
  exact Eventually.of_forall fun x => by
    simp only
    have hle : splitPrimeCount (KummerField k (j + 1)) x ≤
        splitPrimeCount (KummerField k j) x := by
      have h := splitPrimeCount_eq_kummerSplitPatternCount_add k j x hnested
      omega
    rw [← Nat.cast_sub hle,
      ← kummerSplitPatternCount_eq_sub k j x hnested]

/-- Ratio-limit form of the fixed-pattern theorem.  Unlike asymptotic
equivalence, this statement also covers a zero pattern weight (equal adjacent
degrees), which is needed when summing all fixed patterns. -/
theorem kummerSplitPatternCount_ratio_tendsto
    (k j : ℕ) (scale : ℕ → ℝ)
    (hnested : ∀ p, IsCompletelySplit (KummerField k (j + 1)) p →
      IsCompletelySplit (KummerField k j) p)
    (hlevel : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k j) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k j)))
    (hsucc : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k (j + 1)) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k (j + 1)))) :
    Tendsto
      (fun x : ℕ => (kummerSplitPatternCount k j x : ℝ) / scale x)
      atTop (𝓝 (patternWeight k j)) := by
  rw [patternWeight]
  apply Tendsto.congr' ?_ (hlevel.sub hsucc)
  exact Eventually.of_forall fun x => by
    simp only
    have hle : splitPrimeCount (KummerField k (j + 1)) x ≤
        splitPrimeCount (KummerField k j) x := by
      have h := splitPrimeCount_eq_kummerSplitPatternCount_add k j x hnested
      omega
    rw [← sub_div, ← Nat.cast_sub hle,
      ← kummerSplitPatternCount_eq_sub k j x hnested]

theorem kummerSplitPatternCount_ratio_tendsto_of_ne_zero
    {k : ℕ} (hk : k ≠ 0) (j : ℕ) (scale : ℕ → ℝ)
    (hlevel : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k j) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k j)))
    (hsucc : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k (j + 1)) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k (j + 1)))) :
    Tendsto
      (fun x : ℕ => (kummerSplitPatternCount k j x : ℝ) / scale x)
      atTop (𝓝 (patternWeight k j)) :=
  kummerSplitPatternCount_ratio_tendsto k j scale
    (fun p => isCompletelySplit_kummer_succ_descend hk j p) hlevel hsucc

theorem eventually_pntMain_ne_zero :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) / Real.log (x : ℝ) ≠ 0 := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  apply div_ne_zero
  · exact_mod_cast (show x ≠ 0 by omega)
  · exact Real.log_ne_zero_of_pos_of_ne_one
      (by positivity) (by exact_mod_cast (show x ≠ 1 by omega))

/-- Unconditional fixed-pattern natural-density theorem on the PNT scale.
No strict degree increase is needed: if two adjacent Kummer fields have the
same degree, the conclusion correctly says that the normalized exact-pattern
count tends to zero. -/
theorem kummerSplitPatternCount_ratio_tendsto_pntMain
    {k : ℕ} (hk : k ≠ 0) (j : ℕ) :
    Tendsto
      (fun x : ℕ =>
        (kummerSplitPatternCount k j x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 (patternWeight k j)) := by
  let scale : ℕ → ℝ := fun x => (x : ℝ) / Real.log (x : ℝ)
  have hscale : ∀ᶠ x : ℕ in atTop, scale x ≠ 0 :=
    eventually_pntMain_ne_zero
  have hlevelEquiv := splitPrimeCount_isEquivalent (KummerField k j)
  have hlevel : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k j) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k j)) := by
    apply ratio_tendsto_of_isEquivalent_const_mul
    · rw [splittingDensity]
      exact inv_ne_zero (by
        exact_mod_cast (kummerDegree_pos k j).ne')
    · exact hscale
    · simpa only [splittingDensity, kummerDegree] using hlevelEquiv
  have hsuccEquiv := splitPrimeCount_isEquivalent (KummerField k (j + 1))
  have hsucc : Tendsto
      (fun x : ℕ =>
        (splitPrimeCount (KummerField k (j + 1)) x : ℝ) / scale x)
      atTop (𝓝 (splittingDensity k (j + 1))) := by
    apply ratio_tendsto_of_isEquivalent_const_mul
    · rw [splittingDensity]
      exact inv_ne_zero (by
        exact_mod_cast (kummerDegree_pos k (j + 1)).ne')
    · exact hscale
    · simpa only [splittingDensity, kummerDegree] using hsuccEquiv
  exact kummerSplitPatternCount_ratio_tendsto_of_ne_zero
    hk j scale hlevel hsucc

/-! ## Finite cyclic groups and `k`-th powers -/

/-- An element of a multiplicative monoid is a `k`-th power. -/
def IsKthPower {M : Type*} [Monoid M] (k : ℕ) (a : M) : Prop :=
  ∃ b : M, b ^ k = a

/-- The polynomial over a field encoding a finite residue pattern.  It
contains the roots-of-unity factor and the first `r` radical factors. -/
def residuePatternPolynomial
    {F : Type*} [Field F] (k r : ℕ) (q : ℕ → F) : Polynomial F :=
  Polynomial.cyclotomic k F *
    ∏ j ∈ Finset.range r,
      (Polynomial.X ^ k - Polynomial.C (q j))

theorem isKthPower_iff_mem_powMonoidHom_range
    {G : Type*} [CommGroup G] (k : ℕ) (a : G) :
    IsKthPower k a ↔ a ∈ (powMonoidHom k : G →* G).range := by
  rfl

theorem X_pow_sub_C_splits_iff_isKthPower
    {F : Type*} [Field F] {k : ℕ} (hk : 0 < k) {ζ a : F}
    (hζ : IsPrimitiveRoot ζ k) :
    (Polynomial.X ^ k - Polynomial.C a).Splits ↔ IsKthPower k a := by
  constructor
  · intro hsplit
    obtain ⟨b, hb⟩ := hsplit.exists_eval_eq_zero (by
      rw [Polynomial.degree_X_pow_sub_C hk a]
      exact_mod_cast hk.ne')
    refine ⟨b, ?_⟩
    have hb' : b ^ k - a = 0 := by simpa using hb
    exact sub_eq_zero.mp hb'
  · rintro ⟨b, hb⟩
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ hb

theorem residuePatternPolynomial_splits_iff
    {F : Type*} [Field F] {k : ℕ} (hk : 0 < k) {ζ : F}
    (hζ : IsPrimitiveRoot ζ k) (r : ℕ) (q : ℕ → F) :
    (residuePatternPolynomial k r q).Splits ↔
      ∀ j ∈ Finset.range r, IsKthPower k (q j) := by
  have hcyclo : (Polynomial.cyclotomic k F).Splits := by
    exact (Polynomial.X_pow_sub_one_splits hζ).of_dvd
      (Polynomial.X_pow_sub_C_ne_zero hk (1 : F))
      (Polynomial.cyclotomic.dvd_X_pow_sub_one k F)
  have hcyclo0 : Polynomial.cyclotomic k F ≠ 0 :=
    (Polynomial.cyclotomic.monic k F).ne_zero
  have hfactor0 : ∀ j ∈ Finset.range r,
      Polynomial.X ^ k - Polynomial.C (q j) ≠ 0 :=
    fun j _ => Polynomial.X_pow_sub_C_ne_zero hk (q j)
  have hprod0 : (∏ j ∈ Finset.range r,
      (Polynomial.X ^ k - Polynomial.C (q j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor0
  rw [residuePatternPolynomial,
    Polynomial.splits_mul hcyclo0 hprod0,
    Polynomial.splits_prod_iff hfactor0,
    and_iff_right hcyclo]
  exact forall_congr' fun j => forall_congr' fun _ =>
    X_pow_sub_C_splits_iff_isKthPower hk hζ

/-- The local polynomial over `ZMod p` obtained from the rational-prime
pattern. -/
def finiteFieldPatternPolynomial (p k r : ℕ) : Polynomial (ZMod p) :=
  Polynomial.cyclotomic k (ZMod p) *
    ∏ j ∈ Finset.range r,
      (Polynomial.X ^ k - Polynomial.C (rationalPrime j : ZMod p))

theorem kummerIntegralPolynomial_map_zmod (p k r : ℕ) :
    (kummerIntegralPolynomial k r).map (Int.castRingHom (ZMod p)) =
      finiteFieldPatternPolynomial p k r := by
  simp only [kummerIntegralPolynomial, finiteFieldPatternPolynomial,
    Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Int.coe_castRingHom, Int.cast_natCast,
    Polynomial.map_cyclotomic_int]

theorem finiteFieldPatternPolynomial_splits_iff
    {p k : ℕ} [Fact p.Prime] (hk : 0 < k) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ k) (r : ℕ) :
    (finiteFieldPatternPolynomial p k r).Splits ↔
      ∀ j < r, ∃ b : ZMod p, b ^ k = rationalPrime j := by
  change (residuePatternPolynomial k r
    (fun j => (rationalPrime j : ZMod p))).Splits ↔ _
  rw [residuePatternPolynomial_splits_iff hk hζ]
  simp only [Finset.mem_range, IsKthPower]

theorem card_kthPowers
    {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    Nat.card {a : G // IsKthPower k a} =
      Nat.card G / (Nat.card G).gcd k := by
  change Nat.card (powMonoidHom k : G →* G).range = _
  exact IsCyclic.card_powMonoidHom_range G k

theorem index_kthPowers
    {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    (powMonoidHom k : G →* G).range.index = (Nat.card G).gcd k :=
  IsCyclic.index_powMonoidHom_range G k

theorem all_isKthPower_iff_coprime_card
    {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    (∀ a : G, IsKthPower k a) ↔ (Nat.card G).Coprime k := by
  rw [Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro h
    have hrange : (powMonoidHom k : G →* G).range = ⊤ := by
      ext a
      simp only [Subgroup.mem_top, iff_true]
      exact (isKthPower_iff_mem_powMonoidHom_range k a).mp (h a)
    have hindex : (powMonoidHom k : G →* G).range.index = 1 := by
      rw [hrange, Subgroup.index_top]
    simpa [IsCyclic.index_powMonoidHom_range G k] using hindex
  · intro hcop a
    apply (isKthPower_iff_mem_powMonoidHom_range k a).mpr
    have hindex : (powMonoidHom k : G →* G).range.index = 1 := by
      rw [IsCyclic.index_powMonoidHom_range G k, hcop]
    have hrange : (powMonoidHom k : G →* G).range = ⊤ :=
      Subgroup.index_eq_one.mp hindex
    rw [hrange]
    exact Subgroup.mem_top a

theorem pow_surjective_iff_coprime_card
    (G : Type*) [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    Function.Surjective (fun a : G => a ^ k) ↔ (Nat.card G).Coprime k := by
  simpa [Function.Surjective, IsKthPower, eq_comm] using
    (all_isKthPower_iff_coprime_card (G := G) k)

theorem exists_not_isKthPower_iff_not_coprime_card
    (G : Type*) [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    (∃ a : G, ¬ IsKthPower k a) ↔ ¬(Nat.card G).Coprime k := by
  rw [← not_iff_not]
  push Not
  exact all_isKthPower_iff_coprime_card (G := G) k

theorem finiteField_card_kthPowers
    (F : Type*) [Field F] [Finite F] (k : ℕ) :
    Nat.card {a : Fˣ // IsKthPower k a} =
      (Nat.card F - 1) / (Nat.card F - 1).gcd k := by
  rw [card_kthPowers]
  simp only [Nat.card_units]

theorem zmod_card_kthPowers (p k : ℕ) [Fact p.Prime] :
    Nat.card {a : (ZMod p)ˣ // IsKthPower k a} =
      (p - 1) / (p - 1).gcd k := by
  rw [card_kthPowers, Nat.card_eq_fintype_card, ZMod.card_units]

theorem zmod_all_isKthPower_iff (p k : ℕ) [Fact p.Prime] :
    (∀ a : (ZMod p)ˣ, IsKthPower k a) ↔ (p - 1).Coprime k := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using
    (all_isKthPower_iff_coprime_card (G := (ZMod p)ˣ) k)

theorem zmod_exists_not_isKthPower_iff (p k : ℕ) [Fact p.Prime] :
    (∃ a : (ZMod p)ˣ, ¬ IsKthPower k a) ↔ ¬(p - 1).Coprime k := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using
    (exists_not_isKthPower_iff_not_coprime_card (ZMod p)ˣ k)

theorem zmod_exists_not_isKthPower_of_dvd {p k : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hkp : k ∣ p - 1) :
    ∃ a : (ZMod p)ˣ, ¬ IsKthPower k a := by
  rw [zmod_exists_not_isKthPower_iff, Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_eq_right_iff_dvd.mpr hkp]
  omega

theorem zmod_unit_isKthPower_iff {p k : ℕ} [Fact p.Prime]
    (hk : k ≠ 0) {a : ZMod p} (ha : a ≠ 0) :
    IsKthPower k (Units.mk0 a ha) ↔ ∃ b : ZMod p, b ^ k = a := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(b : ZMod p), congr_arg Units.val hb⟩
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro h
      subst b
      simp [hk] at hb
      exact ha hb.symm
    exact ⟨Units.mk0 b hb0, Units.ext hb⟩

end

end Erdos980
