/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.KummerPatterns
import ErdosProblems.Erdos980.Model
import ErdosProblems.Erdos980.NaturalChebotarev.FiniteException
import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Algebra
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Good-prime bridge for the Kummer patterns

This file supplies the integral model of `kummerFieldPolynomial` and the
finite-exception algebraic bridge between complete splitting of a rational
prime in its splitting field and splitting of the reduced polynomial.
-/

namespace Erdos980

noncomputable section

open Polynomial NumberField Chebotarev Filter Topology

namespace GoodPrimeBridge

variable {k r : ℕ}

/-- The finite set of roots that generates the Kummer splitting field. -/
abbrev KummerRoot (k r : ℕ) :=
  {x : KummerField k r // x ∈ (kummerFieldPolynomial k r).rootSet (KummerField k r)}

private theorem kummerIntegralPolynomial_monic (hk : k ≠ 0) :
    (kummerIntegralPolynomial k r).Monic := by
  apply (Polynomial.cyclotomic.monic k ℤ).mul
  exact Polynomial.monic_prod_of_monic _ _ fun j _ =>
    Polynomial.monic_X_pow_sub_C _ hk

private theorem kummerIntegralPolynomial_map_field :
    (kummerIntegralPolynomial k r).map
        (algebraMap ℤ (KummerField k r)) =
      (kummerFieldPolynomial k r).map
        (algebraMap ℚ (KummerField k r)) := by
  ext n
  simp only [Polynomial.coeff_map]
  have hcoeff :
      ((kummerIntegralPolynomial k r).map (Int.castRingHom ℚ)).coeff n =
        (kummerFieldPolynomial k r).coeff n :=
    congrArg (fun f : Polynomial ℚ ↦ f.coeff n)
      (kummerIntegralPolynomial_map_rat k r)
  calc
    algebraMap ℤ (KummerField k r)
        ((kummerIntegralPolynomial k r).coeff n) =
        algebraMap ℚ (KummerField k r)
          (((kummerIntegralPolynomial k r).coeff n : ℤ) : ℚ) :=
      IsScalarTower.algebraMap_apply ℤ ℚ (KummerField k r) _
    _ = algebraMap ℚ (KummerField k r)
        (((kummerIntegralPolynomial k r).map
          (Int.castRingHom ℚ)).coeff n) := by
      rw [Polynomial.coeff_map]
      rfl
    _ = algebraMap ℚ (KummerField k r)
        ((kummerFieldPolynomial k r).coeff n) := congrArg _ hcoeff

/-- Every defining root is an algebraic integer. -/
theorem root_isIntegral (hk : k ≠ 0) (x : KummerRoot k r) :
    IsIntegral ℤ (x.1 : KummerField k r) := by
  refine ⟨kummerIntegralPolynomial k r,
    kummerIntegralPolynomial_monic hk, ?_⟩
  have hx := (Polynomial.mem_rootSet.mp x.2).2
  rw [eval₂_eq_eval_map, kummerIntegralPolynomial_map_field]
  rw [aeval_def, eval₂_eq_eval_map] at hx
  exact hx

/-- A defining root regarded as an element of the full ring of integers. -/
def rootInteger (hk : k ≠ 0) (x : KummerRoot k r) : 𝓞 (KummerField k r) :=
  ⟨x.1, root_isIntegral hk x⟩

@[simp]
theorem rootInteger_coe (hk : k ≠ 0) (x : KummerRoot k r) :
    (rootInteger hk x : KummerField k r) = x.1 := rfl

theorem aeval_rootInteger_eq_zero (hk : k ≠ 0) (x : KummerRoot k r) :
    (aeval (rootInteger hk x) (kummerIntegralPolynomial k r) :
      𝓞 (KummerField k r)) = 0 := by
  apply RingOfIntegers.coe_injective
  have hx := (Polynomial.mem_rootSet.mp x.2).2
  rw [aeval_def, Polynomial.hom_eval₂, map_zero]
  change eval₂ (algebraMap ℤ (KummerField k r)) x.1
    (kummerIntegralPolynomial k r) = 0
  rw [eval₂_eq_eval_map, kummerIntegralPolynomial_map_field]
  rw [aeval_def, eval₂_eq_eval_map] at hx
  exact hx

/-- The integral defining polynomial already splits over the full ring of
integers of its splitting field. -/
theorem kummerIntegralPolynomial_splits_ringOfIntegers (hk : k ≠ 0) :
    ((kummerIntegralPolynomial k r).map
      (algebraMap ℤ (𝓞 (KummerField k r)))).Splits := by
  classical
  let g := (kummerIntegralPolynomial k r).map
    (algebraMap ℤ (𝓞 (KummerField k r)))
  have hmap : g.map (algebraMap (𝓞 (KummerField k r))
      (KummerField k r)) =
      (kummerFieldPolynomial k r).map
        (algebraMap ℚ (KummerField k r)) := by
    calc
      g.map (algebraMap (𝓞 (KummerField k r))
          (KummerField k r)) =
          (kummerIntegralPolynomial k r).map
            (algebraMap ℤ (KummerField k r)) := by
        dsimp only [g]
        rw [Polynomial.map_map]
        congr 1
      _ = _ := kummerIntegralPolynomial_map_field
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := algebraMap (𝓞 (KummerField k r)) (KummerField k r))
    RingOfIntegers.coe_injective
  · rw [hmap]
    exact Polynomial.SplittingField.splits (kummerFieldPolynomial k r)
  · intro a ha
    rw [hmap] at ha
    let x : KummerRoot k r := ⟨a, Multiset.mem_toFinset.mpr ha⟩
    exact ⟨⟨a, root_isIntegral hk x⟩, rfl⟩

/-- A nonidentity automorphism moves at least one defining root. -/
theorem exists_root_moved (σ : Gal(KummerField k r / ℚ)) (hσ : σ ≠ 1) :
    ∃ x : KummerRoot k r, σ x.1 ≠ x.1 := by
  by_contra! hfix
  apply hσ
  have heq : σ.toAlgHom = AlgHom.id ℚ (KummerField k r) :=
    AlgHom.ext_of_adjoin_eq_top
    (Polynomial.SplittingField.adjoin_rootSet (kummerFieldPolynomial k r))
    (fun x hx ↦ hfix ⟨x, hx⟩)
  apply AlgEquiv.ext
  exact fun x ↦ DFunLike.congr_fun heq x

/-- The integral difference between a root and one of its Galois conjugates. -/
def rootDifference (hk : k ≠ 0) (σ : Gal(KummerField k r / ℚ))
    (x : KummerRoot k r) : 𝓞 (KummerField k r) :=
  RingOfIntegers.mapRingEquiv σ.toRingEquiv (rootInteger hk x) - rootInteger hk x

theorem rootDifference_ne_zero_iff (hk : k ≠ 0)
    (σ : Gal(KummerField k r / ℚ)) (x : KummerRoot k r) :
    rootDifference hk σ x ≠ 0 ↔ σ x.1 ≠ x.1 := by
  have heq : rootDifference hk σ x = 0 ↔ σ x.1 = x.1 := by
    rw [rootDifference, sub_eq_zero, RingOfIntegers.ext_iff]
    rfl
  exact not_congr heq

/-- Prime ideals which identify a root with a genuinely different Galois
conjugate after reduction. -/
def CollisionIdeals (hk : k ≠ 0) (σ : Gal(KummerField k r / ℚ))
    (x : KummerRoot k r) : Set (Ideal (𝓞 (KummerField k r))) :=
  {P | P.IsPrime ∧ P ≠ ⊥ ∧ rootDifference hk σ x ∈ P}

theorem collisionIdeals_finite (hk : k ≠ 0)
    (σ : Gal(KummerField k r / ℚ)) (x : KummerRoot k r)
    (hmove : σ x.1 ≠ x.1) : (CollisionIdeals hk σ x).Finite := by
  let d := rootDifference hk σ x
  have hd : d ≠ 0 := (rootDifference_ne_zero_iff hk σ x).2 hmove
  have hspan : Ideal.span ({d} : Set (𝓞 (KummerField k r))) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  let T : Set (IsDedekindDomain.HeightOneSpectrum
      (𝓞 (KummerField k r))) :=
    {v | v.asIdeal ∣ Ideal.span ({d} : Set (𝓞 (KummerField k r)))}
  have hT : T.Finite := Ideal.finite_factors hspan
  apply Set.Finite.subset (hT.image fun v ↦ v.asIdeal)
  intro P hP
  have hPle : Ideal.span ({d} : Set (𝓞 (KummerField k r))) ≤ P := by
    rw [Ideal.span_le]
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hP.2.2
  let v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (KummerField k r)) :=
    ⟨P, hP.1, hP.2.1⟩
  refine ⟨v, ?_, rfl⟩
  exact (Ideal.dvd_iff_le).2 hPle

private instance finite_kummerRoot : Finite (KummerRoot k r) := by
  exact (Polynomial.rootSet_finite (kummerFieldPolynomial k r)
    (KummerField k r)).to_subtype

/-- The rational primes at which two distinct conjugates of a defining root
can collide. -/
def collisionPrimes (hk : k ≠ 0) : Set ℕ :=
  {p | ∃ (σ : Gal(KummerField k r / ℚ)) (x : KummerRoot k r),
    σ x.1 ≠ x.1 ∧ ∃ P ∈ CollisionIdeals hk σ x,
      NaturalChebotarev.SplitTransfer.primeBelow (KummerField k r) P = p}

theorem collisionPrimes_finite (hk : k ≠ 0) :
    (collisionPrimes (k := k) (r := r) hk).Finite := by
  classical
  let S : Set ℕ := ⋃ (σ : Gal(KummerField k r / ℚ)),
    ⋃ (x : KummerRoot k r),
      if h : σ x.1 ≠ x.1 then
        NaturalChebotarev.SplitTransfer.primeBelow (KummerField k r) ''
          CollisionIdeals hk σ x
      else ∅
  have hS : S.Finite := by
    dsimp only [S]
    refine Set.Finite.iUnion Set.finite_univ ?_ ?_
    · intro σ _
      refine Set.Finite.iUnion Set.finite_univ ?_ ?_
      · intro x _
        split_ifs with h
        · exact (collisionIdeals_finite hk σ x h).image _
        · exact Set.finite_empty
      · intro x hx
        exact (hx (Set.mem_univ x)).elim
    · intro σ hσ
      exact (hσ (Set.mem_univ σ)).elim
  apply hS.subset
  rintro p ⟨σ, x, hmove, P, hP, rfl⟩
  simp only [S, Set.mem_iUnion]
  refine ⟨σ, x, ?_⟩
  rw [dif_pos hmove]
  exact ⟨P, hP, rfl⟩

/-- Rational primes ramified in the Kummer splitting field. -/
def ramifiedPrimes : Set ℕ :=
  {p | p.Prime ∧ ¬ UnramifiedIn ℚ (KummerField k r)
    (NaturalChebotarev.SplitTransfer.rationalIdeal p)}

theorem ramifiedPrimes_finite :
    (ramifiedPrimes (k := k) (r := r)).Finite := by
  let T : Set (Ideal (𝓞 ℚ)) :=
    {P | P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn ℚ (KummerField k r) P}
  have hT : T.Finite := finite_ramifiedIn ℚ (KummerField k r)
  apply (hT.image Ideal.absNorm).subset
  rintro p ⟨hp, hram⟩
  let P := NaturalChebotarev.SplitTransfer.rationalIdeal p
  have hPprime : P.IsPrime :=
    NaturalChebotarev.SplitTransfer.rationalIdeal_isPrime hp
  have hP0 : P ≠ ⊥ := by
    intro h
    have hn := congrArg Ideal.absNorm h
    rw [NaturalChebotarev.SplitTransfer.absNorm_rationalIdeal,
      Ideal.absNorm_bot] at hn
    exact hp.ne_zero hn
  refine ⟨P, ⟨hPprime, hP0, hram⟩, ?_⟩
  exact NaturalChebotarev.SplitTransfer.absNorm_rationalIdeal p

/-- The complete finite exceptional set used by the local/global splitting
bridge. -/
def badPrimes (hk : k ≠ 0) : Set ℕ :=
  collisionPrimes (k := k) (r := r) hk ∪ ramifiedPrimes (k := k) (r := r)

theorem badPrimes_finite (hk : k ≠ 0) :
    (badPrimes (k := k) (r := r) hk).Finite :=
  (collisionPrimes_finite (k := k) (r := r) hk).union
    (ramifiedPrimes_finite (k := k) (r := r))

/-- If the reduced defining polynomial splits, every defining root is fixed
modulo a prime above `p` by an arithmetic Frobenius at that prime. -/
theorem rootDifference_mem_of_splits {p : ℕ} (hp : p.Prime)
    (hk : k ≠ 0)
    (P : Ideal (𝓞 (KummerField k r))) [hPprime : P.IsPrime]
    (hP0 : P ≠ ⊥)
    (hlo : P.LiesOver
      (NaturalChebotarev.SplitTransfer.rationalIdeal p))
    (σ : Gal(KummerField k r / ℚ))
    (hσ : IsArithFrobAt (𝓞 ℚ) σ P)
    (hsplit : (finiteFieldPatternPolynomial p k r).Splits)
    (x : KummerRoot k r) : rootDifference hk σ x ∈ P := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : P.IsMaximal := hPprime.isMaximal hP0
  let : Field (𝓞 (KummerField k r) ⧸ P) := Ideal.Quotient.field P
  let : P.LiesOver
      (NaturalChebotarev.SplitTransfer.rationalIdeal p) := hlo
  have hp_mem_base :
      (p : 𝓞 ℚ) ∈ NaturalChebotarev.SplitTransfer.rationalIdeal p := by
    exact Ideal.subset_span (by simp)
  have hp_mem : (p : 𝓞 (KummerField k r)) ∈ P := by
    exact (Ideal.mem_of_liesOver (P := P)
      (p := NaturalChebotarev.SplitTransfer.rationalIdeal p) (p : 𝓞 ℚ)).mp
      hp_mem_base
  have hp_zero : (p : 𝓞 (KummerField k r) ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hp_mem
  let : CharP (𝓞 (KummerField k r) ⧸ P) p :=
    (CharP.charP_iff_prime_eq_zero hp).2 hp_zero
  let i : ZMod p →+* (𝓞 (KummerField k r) ⧸ P) :=
    ZMod.castHom dvd_rfl _
  have hi : Function.Injective i := i.injective
  let z := rootInteger hk x
  let y : 𝓞 (KummerField k r) ⧸ P := Ideal.Quotient.mk P z
  have hpoly :
      (finiteFieldPatternPolynomial p k r).map i =
        (kummerIntegralPolynomial k r).map
          ((Ideal.Quotient.mk P).comp
            (algebraMap ℤ (𝓞 (KummerField k r)))) := by
    rw [← kummerIntegralPolynomial_map_zmod p k r,
      Polynomial.map_map]
    congr 1
    apply RingHom.ext_int
  have hyroot :
      y ∈ ((finiteFieldPatternPolynomial p k r).map i).roots := by
    have hz := congrArg (Ideal.Quotient.mk P)
      (aeval_rootInteger_eq_zero hk x)
    have heval :
        ((kummerIntegralPolynomial k r).map
          ((Ideal.Quotient.mk P).comp
            (algebraMap ℤ (𝓞 (KummerField k r))))).eval y = 0 := by
      rw [aeval_def, Polynomial.hom_eval₂, map_zero] at hz
      change eval₂ ((Ideal.Quotient.mk P).comp
        (algebraMap ℤ (𝓞 (KummerField k r)))) y
        (kummerIntegralPolynomial k r) = 0 at hz
      rw [eval₂_eq_eval_map] at hz
      exact hz
    rw [hpoly]
    rw [Polynomial.mem_roots]
    · exact heval
    · exact ((kummerIntegralPolynomial_monic (k := k) (r := r) hk).map _).ne_zero
  have hyrange : y ∈ Set.range i := by
    rw [hsplit.roots_map i] at hyroot
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hyroot
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hyrange
  have hypow : y ^ p = y := by
    rw [← ha, ← map_pow, ZMod.pow_card]
  have hcard :
      Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hlo.over.symm,
      NaturalChebotarev.SplitTransfer.absNorm_rationalIdeal]
  rw [← Ideal.Quotient.eq_zero_iff_mem, rootDifference, map_sub,
    sub_eq_zero]
  rw [show Ideal.Quotient.mk P
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv z) =
      y ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) by
        exact hσ.mk_apply z]
  rw [hcard, hypow]

/-- Away from the finite bad set, splitting of the reduced defining
polynomial forces complete splitting of the rational prime in the Kummer
field. -/
theorem isCompletelySplit_of_splits_of_not_mem_bad {p : ℕ}
    (hp : p.Prime) (hk : k ≠ 0)
    (hgood : p ∉ badPrimes (k := k) (r := r) hk)
    (hsplit : (finiteFieldPatternPolynomial p k r).Splits) :
    NaturalChebotarev.SplitTransfer.IsCompletelySplit
      (KummerField k r) p := by
  have hnotram : p ∉ ramifiedPrimes (k := k) (r := r) :=
    fun h ↦ hgood (Or.inr h)
  have hunr : UnramifiedIn ℚ (KummerField k r)
      (NaturalChebotarev.SplitTransfer.rationalIdeal p) := by
    by_contra h
    exact hnotram ⟨hp, h⟩
  let : (NaturalChebotarev.SplitTransfer.rationalIdeal p).IsPrime :=
    NaturalChebotarev.SplitTransfer.rationalIdeal_isPrime hp
  obtain ⟨P, hPprime, hlo, hP0⟩ :=
    exists_prime_liesOver ℚ (KummerField k r)
      (NaturalChebotarev.SplitTransfer.rationalIdeal p) hunr.ne_bot
  let : P.IsPrime := hPprime
  let : Finite (𝓞 (KummerField k r) ⧸ P) :=
    hunr.finite_quotient ℚ (KummerField k r) P hlo
  let σ : Gal(KummerField k r / ℚ) :=
    arithFrobAt (𝓞 ℚ) Gal(KummerField k r / ℚ) P
  have hσfrob : IsArithFrobAt (𝓞 ℚ) σ P :=
    IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(KummerField k r / ℚ) P
  have hσone : σ = 1 := by
    by_contra hσ
    obtain ⟨x, hmove⟩ := exists_root_moved σ hσ
    have hmem : rootDifference hk σ x ∈ P :=
      rootDifference_mem_of_splits hp hk P hP0 hlo σ hσfrob hsplit x
    have hPcoll : P ∈ CollisionIdeals hk σ x :=
      ⟨hPprime, hP0, hmem⟩
    have hpbelow :
        NaturalChebotarev.SplitTransfer.primeBelow
          (KummerField k r) P = p := by
      rw [NaturalChebotarev.SplitTransfer.primeBelow, hlo.over.symm,
        NaturalChebotarev.SplitTransfer.absNorm_rationalIdeal]
    apply hgood
    apply Or.inl
    exact ⟨σ, x, hmove, P, hPcoll, hpbelow⟩
  refine ⟨hp, hunr, ?_⟩
  rw [frobeniusClass_eq_mk_of_isArithFrobAt ℚ (KummerField k r)
    (NaturalChebotarev.SplitTransfer.rationalIdeal p) hunr σ P hσfrob hlo,
    hσone]

/-- At a completely split rational prime, the reduction of the integral
defining polynomial splits over the prime field.  This direction has no
extra exceptional primes: residue degree one identifies every residue field
above `p` with `ZMod p`. -/
theorem finiteFieldPatternPolynomial_splits_of_isCompletelySplit {p : ℕ}
    (hk : k ≠ 0)
    (hsplit : NaturalChebotarev.SplitTransfer.IsCompletelySplit
      (KummerField k r) p) :
    (finiteFieldPatternPolynomial p k r).Splits := by
  classical
  let : Fact p.Prime := ⟨hsplit.1⟩
  let : (NaturalChebotarev.SplitTransfer.rationalIdeal p).IsPrime :=
    NaturalChebotarev.SplitTransfer.rationalIdeal_isPrime hsplit.1
  obtain ⟨P, hPprime, hlo, hP0⟩ :=
    exists_prime_liesOver ℚ (KummerField k r)
      (NaturalChebotarev.SplitTransfer.rationalIdeal p)
      hsplit.2.1.ne_bot
  let : P.IsPrime := hPprime
  let : P.IsMaximal := hPprime.isMaximal hP0
  let : Field (𝓞 (KummerField k r) ⧸ P) := Ideal.Quotient.field P
  let : Finite (𝓞 (KummerField k r) ⧸ P) :=
    hsplit.2.1.finite_quotient ℚ (KummerField k r) P hlo
  let : P.LiesOver
      (NaturalChebotarev.SplitTransfer.rationalIdeal p) := hlo
  have hp_mem_base :
      (p : 𝓞 ℚ) ∈ NaturalChebotarev.SplitTransfer.rationalIdeal p := by
    exact Ideal.subset_span (by simp)
  have hp_mem : (p : 𝓞 (KummerField k r)) ∈ P := by
    exact (Ideal.mem_of_liesOver (P := P)
      (p := NaturalChebotarev.SplitTransfer.rationalIdeal p)
      (p : 𝓞 ℚ)).mp hp_mem_base
  have hp_zero : (p : 𝓞 (KummerField k r) ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hp_mem
  let : CharP (𝓞 (KummerField k r) ⧸ P) p :=
    (CharP.charP_iff_prime_eq_zero hsplit.1).2 hp_zero
  let i : ZMod p →+* (𝓞 (KummerField k r) ⧸ P) :=
    ZMod.castHom dvd_rfl _
  have hdeg : NaturalChebotarev.SplitTransfer.residueDegree
      (KummerField k r) P = 1 :=
    NaturalChebotarev.SplitTransfer.residueDegree_eq_one_of_isCompletelySplit
      (KummerField k r) hsplit hPprime hP0 hlo
  have hpbelow : NaturalChebotarev.SplitTransfer.primeBelow
      (KummerField k r) P = p := by
    rw [NaturalChebotarev.SplitTransfer.primeBelow, hlo.over.symm,
      NaturalChebotarev.SplitTransfer.absNorm_rationalIdeal]
  have hcard : Nat.card (𝓞 (KummerField k r) ⧸ P) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      NaturalChebotarev.SplitTransfer.absNorm_eq_primeBelow_pow_residueDegree
        (KummerField k r) hPprime hP0,
      hpbelow, hdeg, pow_one]
  have hi_bij : Function.Bijective i :=
    (Nat.bijective_iff_injective_and_card i).2
      ⟨i.injective, by rw [Nat.card_zmod, hcard]⟩
  have hpoly :
      (finiteFieldPatternPolynomial p k r).map i =
        (kummerIntegralPolynomial k r).map
          ((Ideal.Quotient.mk P).comp
            (algebraMap ℤ (𝓞 (KummerField k r)))) := by
    rw [← kummerIntegralPolynomial_map_zmod p k r,
      Polynomial.map_map]
    congr 1
    apply RingHom.ext_int
  have hmapped : ((finiteFieldPatternPolynomial p k r).map i).Splits := by
    rw [hpoly]
    have h := (kummerIntegralPolynomial_splits_ringOfIntegers
      (k := k) (r := r) hk).map (Ideal.Quotient.mk P)
    simpa only [Polynomial.map_map] using h
  exact Polynomial.Splits.of_splits_map_of_injective i.injective hmapped
    (fun a _ ↦ hi_bij.surjective a)

/-- The exact good-prime local/global bridge for one Kummer level. -/
theorem isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
    {p : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hgood : p ∉ badPrimes (k := k) (r := r) hk) :
    NaturalChebotarev.SplitTransfer.IsCompletelySplit
        (KummerField k r) p ↔
      (finiteFieldPatternPolynomial p k r).Splits := by
  constructor
  · exact finiteFieldPatternPolynomial_splits_of_isCompletelySplit hk
  · exact isCompletelySplit_of_splits_of_not_mem_bad hp hk hgood

/-- Set-finite packaging of the good-prime bridge, convenient for removing
the exceptional primes from counting functions. -/
theorem exists_finite_badPrimes_split_iff (hk : k ≠ 0) :
    ∃ S : Set ℕ, S.Finite ∧
      ∀ {p : ℕ}, p.Prime → p ∉ S →
        (NaturalChebotarev.SplitTransfer.IsCompletelySplit
            (KummerField k r) p ↔
          (finiteFieldPatternPolynomial p k r).Splits) := by
  exact ⟨badPrimes (k := k) (r := r) hk, badPrimes_finite hk,
    fun hp hgood ↦
      isCompletelySplit_iff_finiteFieldPatternPolynomial_splits hp hk hgood⟩

/-! ## From complete splitting to the exact least-nonresidue pattern -/

/-- The finite set of rational prime divisors of the Kummer exponent.  They
are excluded so that roots of the reduced cyclotomic polynomial are genuine
primitive roots. -/
def exponentDivisorPrimes (k : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ∣ k}

theorem exponentDivisorPrimes_finite (hk : k ≠ 0) :
    (exponentDivisorPrimes k).Finite := by
  apply Set.Finite.subset (Set.finite_Iic k)
  intro p hp
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hp.2

/-- The exceptional set for an exact level-`j` pattern: exceptions at both
adjacent Kummer levels, together with prime divisors of the exponent. -/
def patternBadPrimes (hk : k ≠ 0) (j : ℕ) : Set ℕ :=
  badPrimes (k := k) (r := j) hk ∪
    badPrimes (k := k) (r := j + 1) hk ∪ exponentDivisorPrimes k

theorem patternBadPrimes_finite (hk : k ≠ 0) (j : ℕ) :
    (patternBadPrimes hk j).Finite :=
  ((badPrimes_finite (k := k) (r := j) hk).union
    (badPrimes_finite (k := k) (r := j + 1) hk)).union
      (exponentDivisorPrimes_finite hk)

/-- An eligible prime contains a primitive `k`-th root of unity. -/
theorem exists_isPrimitiveRoot_zmod_of_eligible
    {p : ℕ} (hk : 2 ≤ k) (helig : Eligible k p) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ k := by
  let : Fact p.Prime := ⟨helig.1⟩
  let : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime helig.1
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdiv : k ∣ orderOf u := by
    rw [hu, hcard]
    exact dvd_prime_sub_one_of_eligible helig
  let v : (ZMod p)ˣ := u ^ (orderOf u / k)
  have hu0 : orderOf u ≠ 0 := by
    rw [hu, hcard]
    have hp2 := helig.1.two_le
    omega
  have hvorder : orderOf v = k := by
    exact orderOf_pow_orderOf_div hu0 hdiv
  have hvprim : IsPrimitiveRoot v k :=
    IsPrimitiveRoot.iff_orderOf.mpr hvorder
  exact ⟨(v : ZMod p), IsPrimitiveRoot.coe_units_iff.mpr hvprim⟩

/-- Away from prime divisors of `k`, splitting of the reduced polynomial
forces the congruence condition `p ≡ 1 (mod k)`. -/
theorem eligible_of_finiteFieldPatternPolynomial_splits
    {p : ℕ} (hp : p.Prime) (hk : 0 < k) (hpk : ¬ p ∣ k)
    (hsplit : (finiteFieldPatternPolynomial p k r).Splits) :
    Eligible k p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (k : ZMod p) := ⟨by
    intro hkzero
    exact hpk ((ZMod.natCast_eq_zero_iff k p).mp hkzero)⟩
  have hcyclo0 : Polynomial.cyclotomic k (ZMod p) ≠ 0 :=
    (Polynomial.cyclotomic.monic k (ZMod p)).ne_zero
  have hprod0 : (∏ i ∈ Finset.range r,
      (Polynomial.X ^ k -
        Polynomial.C (rationalPrime i : ZMod p))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact Polynomial.X_pow_sub_C_ne_zero hk (rationalPrime i : ZMod p)
  have hcyclo : (Polynomial.cyclotomic k (ZMod p)).Splits := by
    exact (Polynomial.splits_mul hcyclo0 hprod0).mp hsplit |>.1
  obtain ⟨ζ, hζ⟩ := hcyclo.exists_eval_eq_zero
    (ne_of_gt (Polynomial.degree_cyclotomic_pos k (ZMod p) hk))
  have hprim : IsPrimitiveRoot ζ k := by
    rw [← Polynomial.isRoot_cyclotomic_iff]
    exact hζ
  have hunit : IsUnit ζ := hprim.isUnit hk.ne'
  let u : (ZMod p)ˣ := hunit.unit
  have huprim : IsPrimitiveRoot u k := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [u, IsUnit.unit_spec] using hprim
  have hdiv : k ∣ p - 1 := by
    have hord : orderOf u ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard u
    rw [Nat.card_eq_fintype_card, ZMod.card_units] at hord
    simpa only [← huprim.eq_orderOf] using hord
  exact ⟨hp, (Nat.modEq_of_dvd' hp.pos hdiv).symm⟩

/-- The exact local pattern: the first `j` rational primes are `k`-th
powers modulo `p`, and the next rational prime is not. -/
def KthPowerResiduePattern (k j p : ℕ) : Prop :=
  (∀ i < j, ∃ b : ZMod p, b ^ k = rationalPrime i) ∧
    ¬ ∃ b : ZMod p, b ^ k = rationalPrime j

/-- At an eligible prime the elementary residue pattern is exactly the event
that the least `k`-th-power nonresidue is the `j`-th rational prime. -/
theorem kthPowerResiduePattern_iff_leastKthPowerNonresidue
    {p j : ℕ} (hk : 2 ≤ k) (helig : Eligible k p) :
    KthPowerResiduePattern k j p ↔
      leastKthPowerNonresidue k p = rationalPrime j := by
  classical
  let : Fact p.Prime := ⟨helig.1⟩
  constructor
  · rintro ⟨hfirst, hjnon⟩
    have hjzero : (rationalPrime j : ZMod p) ≠ 0 := by
      intro hz
      apply hjnon
      exact ⟨0, by simp [show k ≠ 0 by omega, hz]⟩
    have hjisnon : IsKthPowerNonresidue k p (rationalPrime j) :=
      ⟨isUnit_iff_ne_zero.mpr hjzero, hjnon⟩
    apply Nat.le_antisymm
    · exact leastKthPowerNonresidue_minimal hk helig hjisnon
    · by_contra hnot
      have hlt : leastKthPowerNonresidue k p < rationalPrime j :=
        Nat.lt_of_not_ge hnot
      let n := leastKthPowerNonresidue k p
      have hnprime : n.Prime := leastKthPowerNonresidue_prime hk helig
      let i := Nat.count Nat.Prime n
      have hi : i < j := by
        have hc := Nat.count_strict_mono hnprime hlt
        simpa only [i, rationalPrime,
          Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] using hc
      obtain ⟨b, hb⟩ := hfirst i hi
      have hni : rationalPrime i = n := by
        exact Nat.nth_count hnprime
      have hspec := leastKthPowerNonresidue_spec hk helig
      apply hspec.2
      refine ⟨b, ?_⟩
      change b ^ k = (n : ZMod p)
      rw [← hni]
      exact hb
  · intro hleast
    have hltp : rationalPrime j < p := by
      rw [← hleast]
      exact leastKthPowerNonresidue_lt hk helig
    have hjnon := (leastKthPowerNonresidue_spec hk helig).2
    rw [hleast] at hjnon
    refine ⟨?_, hjnon⟩
    intro i hi
    have hqi : rationalPrime i < rationalPrime j :=
      rationalPrime_strictMono hi
    have hqip : rationalPrime i < p := hqi.trans hltp
    have hqizero : (rationalPrime i : ZMod p) ≠ 0 := by
      intro hzero
      exact Nat.not_dvd_of_pos_of_lt (rationalPrime_pos i) hqip
        ((ZMod.natCast_eq_zero_iff (rationalPrime i) p).mp hzero)
    have hnotnon : ¬ IsKthPowerNonresidue k p (rationalPrime i) := by
      apply not_kthPowerNonresidue_of_lt_least hk helig
      rwa [hleast]
    exact Classical.byContradiction fun hpow ↦
      hnotnon ⟨isUnit_iff_ne_zero.mpr hqizero, hpow⟩

/-- Adjacent splitting of the two reduced polynomials is precisely the exact
elementary residue pattern. -/
theorem finiteFieldPatternPolynomial_exact_splits_iff
    {p j : ℕ} (hk : 2 ≤ k) (helig : Eligible k p) :
    ((finiteFieldPatternPolynomial p k j).Splits ∧
        ¬ (finiteFieldPatternPolynomial p k (j + 1)).Splits) ↔
      KthPowerResiduePattern k j p := by
  classical
  let : Fact p.Prime := ⟨helig.1⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_zmod_of_eligible hk helig
  have hj := finiteFieldPatternPolynomial_splits_iff
    (p := p) (by omega) hζ j
  have hsucc := finiteFieldPatternPolynomial_splits_iff
    (p := p) (by omega) hζ (j + 1)
  rw [hj, hsucc]
  constructor
  · rintro ⟨hfirst, hnotall⟩
    refine ⟨hfirst, ?_⟩
    intro hjpow
    apply hnotall
    intro i hi
    by_cases hij : i < j
    · exact hfirst i hij
    · have hieq : i = j := by omega
      simpa only [hieq] using hjpow
  · rintro ⟨hfirst, hjnon⟩
    refine ⟨hfirst, ?_⟩
    intro hall
    exact hjnon (hall j (by omega))

/-- Outside the explicit finite exceptional set, the complete-splitting
pattern at two adjacent Kummer levels is exactly the least-nonresidue event.
No eligibility hypothesis is needed: it follows on the splitting side from
the cyclotomic factor, and on the least-nonresidue side from nonvanishing. -/
theorem kummerSplitPattern_iff_leastKthPowerNonresidue
    {p j : ℕ} (hk : 2 ≤ k)
    (hgood : p ∉ patternBadPrimes
      (Nat.ne_of_gt (Nat.zero_lt_two.trans_le hk)) j) :
    (NaturalChebotarev.SplitTransfer.IsCompletelySplit
        (KummerField k j) p ∧
      ¬ NaturalChebotarev.SplitTransfer.IsCompletelySplit
        (KummerField k (j + 1)) p) ↔
      leastKthPowerNonresidue k p = rationalPrime j := by
  classical
  have hgoodj : p ∉ badPrimes (k := k) (r := j) (by omega) := by
    intro hp
    exact hgood (Or.inl (Or.inl hp))
  have hgoodsucc : p ∉ badPrimes (k := k) (r := j + 1) (by omega) := by
    intro hp
    exact hgood (Or.inl (Or.inr hp))
  have hpk (hpprime : p.Prime) : ¬ p ∣ k := by
    intro hdiv
    apply hgood
    exact Or.inr ⟨hpprime, hdiv⟩
  constructor
  · rintro ⟨hsplit, hnotsucc⟩
    have hp : p.Prime := hsplit.1
    have hjlocal :=
      (isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
        hp (by omega) hgoodj).mp hsplit
    have helig : Eligible k p :=
      eligible_of_finiteFieldPatternPolynomial_splits hp (by omega) (hpk hp) hjlocal
    have hsuccLocal :
        ¬ (finiteFieldPatternPolynomial p k (j + 1)).Splits := by
      intro hlocal
      exact hnotsucc
        ((isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
          hp (by omega) hgoodsucc).mpr hlocal)
    apply (kthPowerResiduePattern_iff_leastKthPowerNonresidue hk helig).mp
    exact (finiteFieldPatternPolynomial_exact_splits_iff hk helig).mp
      ⟨hjlocal, hsuccLocal⟩
  · intro hleast
    have hnzero : leastKthPowerNonresidue k p ≠ 0 := by
      rw [hleast]
      exact (rationalPrime_pos j).ne'
    have helig : Eligible k p := by
      have h := (leastKthPowerNonresidue_eq_zero_iff k p).not.mp hnzero
      exact (not_not.mp h).2
    have hlocal := (finiteFieldPatternPolynomial_exact_splits_iff hk helig).mpr
      ((kthPowerResiduePattern_iff_leastKthPowerNonresidue hk helig).mpr hleast)
    exact ⟨
      (isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
        helig.1 (by omega) hgoodj).mpr hlocal.1,
      fun hsucc ↦ hlocal.2
        ((isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
          helig.1 (by omega) hgoodsucc).mp hsucc)⟩

/-- The Kummer exact-pattern predicate and the exact least-nonresidue
predicate differ at only finitely many natural numbers. -/
theorem finite_kummerSplitPattern_symmDiff_leastKthPowerNonresidue
    (hk : 2 ≤ k) (j : ℕ) :
    {p : ℕ | ¬
      ((NaturalChebotarev.SplitTransfer.IsCompletelySplit
          (KummerField k j) p ∧
        ¬ NaturalChebotarev.SplitTransfer.IsCompletelySplit
          (KummerField k (j + 1)) p) ↔
        leastKthPowerNonresidue k p = rationalPrime j)}.Finite := by
  apply (patternBadPrimes_finite
    (Nat.ne_of_gt (Nat.zero_lt_two.trans_le hk)) j).subset
  intro p hp
  by_contra hgood
  exact hp (kummerSplitPattern_iff_leastKthPowerNonresidue hk hgood)

/-! ## Transfer of the fixed-pattern ratio limit -/

/-- Strict-cutoff count of the exact adjacent Kummer splitting pattern. -/
noncomputable def kummerPatternPrimeCount (k j x : ℕ) : ℕ := by
  classical
  exact NaturalChebotarev.primeCount
    (fun p ↦
      NaturalChebotarev.SplitTransfer.IsCompletelySplit
          (KummerField k j) p ∧
        ¬ NaturalChebotarev.SplitTransfer.IsCompletelySplit
          (KummerField k (j + 1)) p) x

/-- Strict-cutoff prime counting is the same as the repository's inclusive
Kummer pattern count at the preceding endpoint. -/
theorem primeCount_kummerSplitPattern_eq_sub_one
    (k j x : ℕ) (hx : 0 < x) :
    kummerPatternPrimeCount k j x =
      kummerSplitPatternCount k j (x - 1) := by
  classical
  rw [kummerPatternPrimeCount, NaturalChebotarev.primeCount,
    kummerSplitPatternCount,
    KummerSplitPatternUpTo]
  symm
  apply Nat.subtype_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, _, hsplit, hnotsplit⟩
    exact ⟨hsplit, hnotsplit, (Nat.lt_iff_le_pred hx).mp hlt⟩
  · rintro ⟨hsplit, hnotsplit, hle⟩
    exact ⟨(Nat.lt_iff_le_pred hx).mpr hle, hsplit.1, hsplit, hnotsplit⟩

/-- The PNT scale is unchanged asymptotically by replacing `x` with `x-1`. -/
theorem erdos980Scale_sub_one_ratio_tendsto_one :
    Tendsto (fun x : ℕ ↦ erdos980Scale (x - 1) / erdos980Scale x)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℕ ↦ ((x : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hxratio : Tendsto (fun x : ℕ ↦ ((x - 1 : ℕ) : ℝ) / (x : ℝ))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun x : ℕ ↦ (1 : ℝ) - ((x : ℝ))⁻¹)
        atTop (nhds 1) := by simpa using tendsto_const_nhds.sub hinv
    refine hbase.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Nat.cast_sub hx]
    have hx0 : (x : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hdelta0 := Real.tendsto_log_nat_add_one_sub_log
  have hdelta : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    have hcomp := hdelta0.comp (tendsto_sub_atTop_nat 1)
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Function.comp_apply]
    rw [show ((x - 1 : ℕ) : ℝ) + 1 = (x : ℝ) by
      exact_mod_cast Nat.sub_add_cancel hx]
  have hlogTop : Tendsto
      (fun x : ℕ ↦ Real.log ((x - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) /
        Real.log ((x - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    have hbase : Tendsto (fun x : ℕ ↦ (1 : ℝ) +
        (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
          Real.log ((x - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add (hdelta.div_atTop hlogTop)
    refine hbase.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with x hx
    have hlog0 : Real.log ((x - 1 : ℕ) : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (show 0 < x - 1 by omega)
      · exact_mod_cast (show x - 1 ≠ 1 by omega)
    field_simp
    ring
  have hbase : Tendsto (fun x : ℕ ↦
      (((x - 1 : ℕ) : ℝ) / (x : ℝ)) *
        (Real.log (x : ℝ) / Real.log ((x - 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by simpa using hxratio.mul hlogratio
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [erdos980Scale, erdos980Scale, Nat.cast_sub (by omega : 1 ≤ x)]
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx0 : (x : ℝ) ≠ 0 := by linarith
  have hxm0 : ((x : ℝ) - 1) ≠ 0 := by linarith
  have hlogx0 : Real.log (x : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
  have hlogxm0 : Real.log ((x : ℝ) - 1) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
  field_simp

/-- The unconditional Kummer fixed-pattern density, written with the strict
cutoff convention used by `primePatternCount`. -/
theorem kummerPatternPrimeCount_ratio_tendsto
    {k : ℕ} (hk : k ≠ 0) (j : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (kummerPatternPrimeCount k j x : ℝ) / erdos980Scale x)
      atTop (nhds (patternWeight k j)) := by
  have hshift : Tendsto
      (fun x : ℕ ↦
        (kummerSplitPatternCount k j (x - 1) : ℝ) /
          erdos980Scale (x - 1))
      atTop (nhds (patternWeight k j)) := by
    have h := (kummerSplitPatternCount_ratio_tendsto_pntMain hk j).comp
      (tendsto_sub_atTop_nat 1)
    change Tendsto
      (fun x : ℕ ↦
        (kummerSplitPatternCount k j (x - 1) : ℝ) /
          (((x - 1 : ℕ) : ℝ) / Real.log ((x - 1 : ℕ) : ℝ)))
      atTop (nhds (patternWeight k j)) at h
    simpa only [erdos980Scale] using h
  have hprod := hshift.mul erdos980Scale_sub_one_ratio_tendsto_one
  have hscaleSub : ∀ᶠ x : ℕ in atTop, erdos980Scale (x - 1) ≠ 0 :=
    (tendsto_sub_atTop_nat 1).eventually erdos980Scale_eventually_ne_zero
  simpa only [mul_one] using hprod.congr' (by
    filter_upwards [eventually_ge_atTop 1, hscaleSub] with x hx hscale
    rw [primeCount_kummerSplitPattern_eq_sub_one k j x (by omega)]
    field_simp)

/-- Strict-cutoff prime count of one exact least-nonresidue value. -/
noncomputable def leastNonresiduePatternPrimeCount
    (k j x : ℕ) : ℕ := by
  classical
  exact NaturalChebotarev.primeCount
    (fun p ↦ leastKthPowerNonresidue k p = rationalPrime j) x

/-- The elementary strict-cutoff count is the model's fixed-pattern count. -/
theorem leastNonresiduePatternPrimeCount_eq_primePatternCount
    {k : ℕ} (hk : 2 ≤ k) (j x : ℕ) :
    (leastNonresiduePatternPrimeCount k j x : ℝ) =
      primePatternCount (leastKthPowerNonresidueModel k) j x := by
  classical
  rw [primePatternCount_leastKthPowerNonresidueModel hk,
    leastNonresiduePatternPrimeCount, NaturalChebotarev.primeCount]

/-- The finite exceptional primes contribute little-oh of the PNT scale to
the difference between the Kummer and elementary fixed-pattern counts. -/
theorem kummerPatternPrimeCount_sub_leastNonresiduePatternPrimeCount_isLittleO
    {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    (fun x : ℕ ↦
      (kummerPatternPrimeCount k j x : ℝ) -
        leastNonresiduePatternPrimeCount k j x) =o[atTop]
      erdos980Scale := by
  classical
  change (fun x : ℕ ↦
      (kummerPatternPrimeCount k j x : ℝ) -
        leastNonresiduePatternPrimeCount k j x) =o[atTop]
    (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ))
  simpa only [kummerPatternPrimeCount, leastNonresiduePatternPrimeCount] using
      NaturalChebotarev.primeCount_sub_primeCount_isLittleO_of_finite
        (fun p ↦
          NaturalChebotarev.SplitTransfer.IsCompletelySplit
              (KummerField k j) p ∧
            ¬ NaturalChebotarev.SplitTransfer.IsCompletelySplit
              (KummerField k (j + 1)) p)
        (fun p ↦ leastKthPowerNonresidue k p = rationalPrime j)
        (finite_kummerSplitPattern_symmDiff_leastKthPowerNonresidue hk j)

/-- Unconditional density of every fixed least-nonresidue pattern.  This is
the exact strict-cutoff statement required by the abstract model assembly. -/
theorem primePatternCount_leastKthPowerNonresidueModel_ratio_tendsto
    {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        primePatternCount (leastKthPowerNonresidueModel k) j x /
          erdos980Scale x)
      atTop (nhds (patternWeight k j)) := by
  have hK := kummerPatternPrimeCount_ratio_tendsto
    (Nat.ne_of_gt (Nat.zero_lt_two.trans_le hk)) j
  have hdiff :=
    (kummerPatternPrimeCount_sub_leastNonresiduePatternPrimeCount_isLittleO
      hk j).tendsto_div_nhds_zero
  have hsub := hK.sub hdiff
  have hsub' : Tendsto
      (fun x : ℕ ↦
        (kummerPatternPrimeCount k j x : ℝ) / erdos980Scale x -
          ((kummerPatternPrimeCount k j x : ℝ) -
            leastNonresiduePatternPrimeCount k j x) / erdos980Scale x)
      atTop (nhds (patternWeight k j)) := by
    simpa only [sub_zero] using hsub
  refine hsub'.congr' ?_
  exact Eventually.of_forall fun x ↦ by
    simp only
    rw [← leastNonresiduePatternPrimeCount_eq_primePatternCount hk]
    ring

/-! ## Positive density of eligible primes -/

/-- The finite exceptional set for identifying level-zero Kummer splitting
with the congruence condition defining eligible primes. -/
def eligibleBadPrimes (hk : k ≠ 0) : Set ℕ :=
  badPrimes (k := k) (r := 0) hk ∪ exponentDivisorPrimes k

theorem eligibleBadPrimes_finite (hk : k ≠ 0) :
    (eligibleBadPrimes hk).Finite :=
  (badPrimes_finite (k := k) (r := 0) hk).union
    (exponentDivisorPrimes_finite hk)

/-- Outside finitely many primes, splitting in the roots-of-unity (level
zero) Kummer field is exactly eligibility. -/
theorem isCompletelySplit_kummer_zero_iff_eligible
    {p : ℕ} (hk : 2 ≤ k)
    (hgood : p ∉ eligibleBadPrimes
      (Nat.ne_of_gt (Nat.zero_lt_two.trans_le hk))) :
    NaturalChebotarev.SplitTransfer.IsCompletelySplit
        (KummerField k 0) p ↔ Eligible k p := by
  classical
  have hfield : p ∉ badPrimes (k := k) (r := 0) (by omega) := by
    intro hp
    exact hgood (Or.inl hp)
  have hpk (hp : p.Prime) : ¬ p ∣ k := by
    intro hpdiv
    exact hgood (Or.inr ⟨hp, hpdiv⟩)
  constructor
  · intro hsplit
    have hlocal :=
      (isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
        hsplit.1 (by omega) hfield).mp hsplit
    exact eligible_of_finiteFieldPatternPolynomial_splits
      hsplit.1 (by omega) (hpk hsplit.1) hlocal
  · intro helig
    let : Fact p.Prime := ⟨helig.1⟩
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_zmod_of_eligible hk helig
    have hlocal : (finiteFieldPatternPolynomial p k 0).Splits :=
      (finiteFieldPatternPolynomial_splits_iff
        (p := p) (by omega) hζ 0).mpr (by
          intro i hi
          omega)
    exact (isCompletelySplit_iff_finiteFieldPatternPolynomial_splits
      helig.1 (by omega) hfield).mpr hlocal

/-- Level-zero Kummer splitting and eligibility differ only finitely. -/
theorem finite_kummerZeroSplit_symmDiff_eligible (hk : 2 ≤ k) :
    {p : ℕ | ¬
      (NaturalChebotarev.SplitTransfer.IsCompletelySplit
          (KummerField k 0) p ↔ Eligible k p)}.Finite := by
  apply (eligibleBadPrimes_finite
    (Nat.ne_of_gt (Nat.zero_lt_two.trans_le hk))).subset
  intro p hp
  by_contra hgood
  exact hp (isCompletelySplit_kummer_zero_iff_eligible hk hgood)

/-- Strict-cutoff count of completely split primes at one Kummer level. -/
noncomputable def kummerLevelPrimeCount (k r x : ℕ) : ℕ := by
  classical
  exact NaturalChebotarev.primeCount
    (NaturalChebotarev.SplitTransfer.IsCompletelySplit
      (KummerField k r)) x

theorem kummerLevelPrimeCount_eq_sub_one
    (k r x : ℕ) (hx : 0 < x) :
    kummerLevelPrimeCount k r x =
      NaturalChebotarev.SplitTransfer.splitPrimeCount
        (KummerField k r) (x - 1) := by
  classical
  rw [kummerLevelPrimeCount, NaturalChebotarev.primeCount,
    NaturalChebotarev.SplitTransfer.splitPrimeCount]
  symm
  apply Nat.subtype_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, _, hsplit⟩
    exact ⟨hsplit, (Nat.lt_iff_le_pred hx).mp hlt⟩
  · rintro ⟨hsplit, hle⟩
    exact ⟨(Nat.lt_iff_le_pred hx).mpr hle, hsplit.1, hsplit⟩

/-- Natural density of strict-cutoff complete splitting at one Kummer level. -/
theorem kummerLevelPrimeCount_ratio_tendsto (k r : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (kummerLevelPrimeCount k r x : ℝ) / erdos980Scale x)
      atTop (nhds (splittingDensity k r)) := by
  let scale : ℕ → ℝ := fun x ↦ (x : ℝ) / Real.log (x : ℝ)
  have hinclusive : Tendsto
      (fun x : ℕ ↦
        (NaturalChebotarev.SplitTransfer.splitPrimeCount
          (KummerField k r) x : ℝ) / scale x)
      atTop (nhds (splittingDensity k r)) := by
    apply ratio_tendsto_of_isEquivalent_const_mul
    · rw [splittingDensity]
      exact inv_ne_zero (by
        exact_mod_cast (kummerDegree_pos k r).ne')
    · exact eventually_pntMain_ne_zero
    · simpa only [splittingDensity, kummerDegree] using
        (NaturalChebotarev.SplitTransfer.splitPrimeCount_isEquivalent
          (KummerField k r))
  have hshift := hinclusive.comp (tendsto_sub_atTop_nat 1)
  have hprod := hshift.mul erdos980Scale_sub_one_ratio_tendsto_one
  have hscaleSub : ∀ᶠ x : ℕ in atTop, erdos980Scale (x - 1) ≠ 0 :=
    (tendsto_sub_atTop_nat 1).eventually erdos980Scale_eventually_ne_zero
  have hprod' : Tendsto
      (fun x : ℕ ↦
        ((NaturalChebotarev.SplitTransfer.splitPrimeCount
            (KummerField k r) (x - 1) : ℝ) / erdos980Scale (x - 1)) *
          (erdos980Scale (x - 1) / erdos980Scale x))
      atTop (nhds (splittingDensity k r)) := by
    simpa only [Function.comp_apply, scale, erdos980Scale, mul_one] using hprod
  refine hprod'.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hscaleSub] with x hx hscale
  rw [kummerLevelPrimeCount_eq_sub_one k r x (by omega)]
  field_simp

/-- Strict-cutoff number of eligible primes, in the same real-valued form as
the final analytic assembly. -/
noncomputable def eligiblePrimeCountBridge (k x : ℕ) : ℝ := by
  classical
  exact (((Finset.range x).filter (Eligible k)).card : ℝ)

noncomputable def eligiblePrimeCountNat (k x : ℕ) : ℕ := by
  classical
  exact NaturalChebotarev.primeCount (Eligible k) x

theorem eligiblePrimeCountBridge_eq_nat (k x : ℕ) :
    eligiblePrimeCountBridge k x =
      (eligiblePrimeCountNat k x : ℝ) := by
  classical
  rw [eligiblePrimeCountBridge, eligiblePrimeCountNat,
    NaturalChebotarev.primeCount]
  congr 2
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, helig⟩
    exact ⟨hlt, helig.1, helig⟩
  · rintro ⟨hlt, _, helig⟩
    exact ⟨hlt, helig⟩

/-- Eligible primes have the positive level-zero Kummer density. -/
theorem eligiblePrimeCountBridge_ratio_tendsto
    {k : ℕ} (hk : 2 ≤ k) :
    Tendsto
      (fun x : ℕ ↦ eligiblePrimeCountBridge k x / erdos980Scale x)
      atTop (nhds (splittingDensity k 0)) := by
  classical
  have hlevel := kummerLevelPrimeCount_ratio_tendsto k 0
  have hdiff :=
    (NaturalChebotarev.primeCount_sub_primeCount_isLittleO_of_finite
      (NaturalChebotarev.SplitTransfer.IsCompletelySplit (KummerField k 0))
      (Eligible k) (finite_kummerZeroSplit_symmDiff_eligible hk)).tendsto_div_nhds_zero
  have hsub := hlevel.sub hdiff
  have hsub' : Tendsto
      (fun x : ℕ ↦
        (kummerLevelPrimeCount k 0 x : ℝ) / erdos980Scale x -
          ((kummerLevelPrimeCount k 0 x : ℝ) -
            eligiblePrimeCountNat k x) / erdos980Scale x)
      atTop (nhds (splittingDensity k 0)) := by
    simpa only [kummerLevelPrimeCount, eligiblePrimeCountNat,
      erdos980Scale, sub_zero] using hsub
  refine hsub'.congr' ?_
  exact Eventually.of_forall fun x ↦ by
    simp only
    rw [eligiblePrimeCountBridge_eq_nat]
    ring

theorem splittingDensity_zero_pos (k : ℕ) :
    0 < splittingDensity k 0 := by
  rw [splittingDensity]
  apply inv_pos.mpr
  exact_mod_cast kummerDegree_pos k 0

#print axioms primePatternCount_leastKthPowerNonresidueModel_ratio_tendsto
#print axioms eligiblePrimeCountBridge_ratio_tendsto
#print axioms kummerSplitPattern_iff_leastKthPowerNonresidue

end GoodPrimeBridge

end

end Erdos980
