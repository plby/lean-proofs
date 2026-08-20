/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve

/-!
# Combined ray-tensor and conductor-norm remainder

For one fixed correction ideal, this file combines two independent finite
conditions on generator coordinates:

* a ray/tensor pattern modulo the fixed conductor `f`, occupying exactly an
  `ell ^ (-j)` fraction of a specified family of unit residues;
* divisibility of the natural conductor norm by `d`, represented by the
  zero set of its integral norm form modulo `d`.

Coordinatewise CRT turns the conjunction into a literal product of finite
residue sets modulo `f*d`.  The growing-modulus lattice estimate therefore
has main term `ell^(-j)` times the unit-residue density times the norm-form
local density, and an endpoint error multiplied by the exact product of the
two residue cardinalities.
-/

open scoped BigOperators NumberField NNReal nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.RayNormRemainder

open NumberField Set Submodule Ideal
open NumberField.mixedEmbedding
open Erdos980.ElliottTail.IdealGeneratorCongruenceCount
open Erdos980.ElliottTail.RayNormPrimeSieve

/-- The exact ray-tensor fraction times norm-form local density, expressed
as a real number. -/
def combinedRayNormDensity
    (K : Type*) [Field K] [NumberField K]
    (ell j d : ℕ) [NeZero d]
    (normMod : (index K → ZMod d) → ZMod d) : ℝ :=
  (ell : ℝ) ^ (- (j : ℤ)) * normResidueDensity K d normMod

/-- The exact density when the ray tensor occupies an `ell ^ (-j)`
fraction of a specified family of unit residue tuples rather than of all
coordinate tuples.  The extra middle factor is the unit density modulo the
fixed ray modulus. -/
def combinedRayUnitNormDensity
    (K : Type*) [Field K] [NumberField K]
    (ell j f d unitResidueCount : ℕ) [NeZero d]
    (normMod : (index K → ZMod d) → ZMod d) : ℝ :=
  (ell : ℝ) ^ (- (j : ℤ)) *
    ((unitResidueCount : ℝ) /
      (f : ℝ) ^ Nat.card (index K)) *
    normResidueDensity K d normMod

theorem combinedRayNormDensity_nonneg
    (K : Type*) [Field K] [NumberField K]
    (ell j d : ℕ) [NeZero d]
    (normMod : (index K → ZMod d) → ZMod d) :
    0 ≤ combinedRayNormDensity K ell j d normMod := by
  unfold combinedRayNormDensity
  exact mul_nonneg (zpow_nonneg (Nat.cast_nonneg ell) _)
    (normResidueDensity_nonneg K d normMod)

theorem combinedRayUnitNormDensity_nonneg
    (K : Type*) [Field K] [NumberField K]
    (ell j f d unitResidueCount : ℕ) [NeZero d]
    (normMod : (index K → ZMod d) → ZMod d) :
    0 ≤ combinedRayUnitNormDensity K ell j f d unitResidueCount normMod := by
  unfold combinedRayUnitNormDensity
  exact mul_nonneg
    (mul_nonneg (zpow_nonneg (Nat.cast_nonneg ell) _)
      (div_nonneg (Nat.cast_nonneg unitResidueCount)
        (pow_nonneg (Nat.cast_nonneg f) _)))
    (normResidueDensity_nonneg K d normMod)

open Classical in
/-- Uniform simultaneous ray/norm count with the correct normalization for
ray conditions imposed only on unit residue tuples.  The hypothesis says
that `rayAllowed` is exactly an `ell ^ (-j)` fraction of the chosen unit
tuples. -/
theorem exists_uniform_combinedRayUnitNormCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, ∀ {ell j f d unitResidueCount : ℕ}, ell ≠ 0 →
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → (f * d : ℕ) ≤ t →
      ell ^ j * rayAllowed.card = unitResidueCount →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayUnitNormDensity K ell j f d unitResidueCount normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        (rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) * C *
          (t / (f * d : ℕ)) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C, hC⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨C, ?_⟩
  intro ell j f d unitResidueCount hell0 hfd _ _ rayAllowed normMod t hmod hray
  have h := hC (f * d)
    (combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d normMod)) t hmod
  rw [card_combinedCoordinateResidues] at h
  have hmain :
      ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          (generatorCellMainConstant K J *
            (t / (f * d : ℕ)) ^ Nat.card (index K)) =
        combinedRayUnitNormDensity K ell j f d unitResidueCount normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K)) := by
    have hellR : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell0
    have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
    have hd0 : d ≠ 0 := NeZero.ne d
    have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have hrayR : (ell : ℝ) ^ j * (rayAllowed.card : ℝ) =
        (unitResidueCount : ℝ) := by
      exact_mod_cast hray
    rw [combinedRayUnitNormDensity, normResidueDensity, zpow_neg,
      zpow_natCast, div_pow]
    push_cast
    rw [mul_pow]
    field_simp
    rw [← hrayR]
    ring
  simp only [generatorCellMainConstant, Nat.card_eq_fintype_card] at hmain h
  rw [hmain] at h
  simpa only [generatorCellMainConstant, Nat.card_eq_fintype_card] using h

/-- The completely general finite-cell density.  This version does not
assume that the chosen ray residues occupy an exact `ell⁻ʲ` fraction of
all coordinate residues.  It is the honest interface for an embedding of a
smaller finite local-unit space into the coordinate residue space. -/
def combinedRayNormCardinalDensity
    (K : Type*) [Field K] [NumberField K]
    (f d : ℕ) [NeZero d]
    (rayAllowed : Finset (index K → ZMod f))
    (normMod : (index K → ZMod d) → ZMod d) : ℝ :=
  (rayAllowed.card : ℝ) / (f : ℝ) ^ Nat.card (index K) *
    normResidueDensity K d normMod

theorem combinedRayNormCardinalDensity_nonneg
    (K : Type*) [Field K] [NumberField K]
    (f d : ℕ) [NeZero d]
    (rayAllowed : Finset (index K → ZMod f))
    (normMod : (index K → ZMod d) → ZMod d) :
    0 ≤ combinedRayNormCardinalDensity K f d rayAllowed normMod := by
  unfold combinedRayNormCardinalDensity
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg rayAllowed.card)
      (pow_nonneg (Nat.cast_nonneg f) _))
    (normResidueDensity_nonneg K d normMod)

theorem rayAllowed_card_le_fullCoordinateResidues
    (K : Type*) [Field K] [NumberField K]
    (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) :
    rayAllowed.card ≤ f ^ Nat.card (index K) := by
  classical
  calc
    rayAllowed.card ≤ Fintype.card (index K → ZMod f) :=
      Finset.card_le_univ rayAllowed
    _ = f ^ Nat.card (index K) := by
      simp only [Fintype.card_fun, ZMod.card, Nat.card_eq_fintype_card]

/-- A finite ray subset has density at most one in the full coordinate
residue space. -/
theorem combinedRayNormCardinalDensity_le_normResidueDensity
    (K : Type*) [Field K] [NumberField K]
    (f d : ℕ) [NeZero f] [NeZero d]
    (rayAllowed : Finset (index K → ZMod f))
    (normMod : (index K → ZMod d) → ZMod d) :
    combinedRayNormCardinalDensity K f d rayAllowed normMod ≤
      normResidueDensity K d normMod := by
  have hfpos : (0 : ℝ) < f := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne f)
  have hdenpos : (0 : ℝ) < (f : ℝ) ^ Nat.card (index K) := by
    positivity
  have hcardR : (rayAllowed.card : ℝ) ≤
      (f : ℝ) ^ Nat.card (index K) := by
    exact_mod_cast rayAllowed_card_le_fullCoordinateResidues K f rayAllowed
  unfold combinedRayNormCardinalDensity
  calc
    (rayAllowed.card : ℝ) / (f : ℝ) ^ Nat.card (index K) *
          normResidueDensity K d normMod ≤
        1 * normResidueDensity K d normMod := by
      exact mul_le_mul_of_nonneg_right ((div_le_one hdenpos).mpr hcardR)
        (normResidueDensity_nonneg K d normMod)
    _ = normResidueDensity K d normMod := one_mul _

/-- Rewriting an `ell⁻ʲ` fraction of a specified unit family as the
literal cardinality density of the selected coordinate residues. -/
theorem combinedRayUnitNormDensity_eq_cardinalDensity
    (K : Type*) [Field K] [NumberField K]
    {ell j f d unitResidueCount : ℕ} [NeZero d]
    (rayAllowed : Finset (index K → ZMod f))
    (normMod : (index K → ZMod d) → ZMod d)
    (hell0 : ell ≠ 0) (hf0 : f ≠ 0)
    (hray : ell ^ j * rayAllowed.card = unitResidueCount) :
    combinedRayUnitNormDensity K ell j f d unitResidueCount normMod =
      combinedRayNormCardinalDensity K f d rayAllowed normMod := by
  have hellR : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell0
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
  have hrayR : (ell : ℝ) ^ j * (rayAllowed.card : ℝ) =
      (unitResidueCount : ℝ) := by
    exact_mod_cast hray
  rw [combinedRayUnitNormDensity, combinedRayNormCardinalDensity,
    zpow_neg, zpow_natCast]
  field_simp
  rw [← hrayR]
  ring

theorem combinedRayUnitNormDensity_le_normResidueDensity
    (K : Type*) [Field K] [NumberField K]
    {ell j f d unitResidueCount : ℕ} [NeZero d]
    (rayAllowed : Finset (index K → ZMod f))
    (normMod : (index K → ZMod d) → ZMod d)
    (hell0 : ell ≠ 0) (hf0 : f ≠ 0)
    (hray : ell ^ j * rayAllowed.card = unitResidueCount) :
    combinedRayUnitNormDensity K ell j f d unitResidueCount normMod ≤
      normResidueDensity K d normMod := by
  letI : NeZero f := ⟨hf0⟩
  rw [combinedRayUnitNormDensity_eq_cardinalDensity K rayAllowed normMod
    hell0 hf0 hray]
  exact combinedRayNormCardinalDensity_le_normResidueDensity
    K f d rayAllowed normMod

open Classical in
/-- Uniform CRT count with the exact finite ray-cardinality density.  No
surjectivity of a supplied local-unit-to-coordinate embedding is hidden in
this statement. -/
theorem exists_uniform_combinedRayNormCellCount_cardinalDensity
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, ∀ {f d : ℕ},
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → ((f * d : ℕ) : ℝ) ≤ t →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayNormCardinalDensity K f d rayAllowed normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        (rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) * C *
          (t / (f * d : ℕ)) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C, hC⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨C, ?_⟩
  intro f d hfd _ _ rayAllowed normMod t hmod
  have h := hC (f * d)
    (combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d normMod)) t hmod
  rw [card_combinedCoordinateResidues] at h
  have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
  have hd0 : d ≠ 0 := NeZero.ne d
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hmain :
      ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          (generatorCellMainConstant K J *
            (t / (f * d : ℕ)) ^ Nat.card (index K)) =
        combinedRayNormCardinalDensity K f d rayAllowed normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K)) := by
    rw [combinedRayNormCardinalDensity, normResidueDensity, div_pow]
    push_cast
    rw [mul_pow]
    field_simp
  simp only [generatorCellMainConstant, Nat.card_eq_fintype_card] at hmain h
  rw [hmain] at h
  simpa only [generatorCellMainConstant, Nat.card_eq_fintype_card] using h

open Classical in
/-- Uniform count for the simultaneous ray/tensor and natural-norm
conditions.  The denominator-free hypothesis on `rayAllowed` is exactly the
finite tensor equidistribution certificate. -/
theorem exists_uniform_combinedRayNormCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, ∀ {ell j f d : ℕ}, ell ≠ 0 →
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → (f * d : ℕ) ≤ t →
      ell ^ j * rayAllowed.card = f ^ Nat.card (index K) →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayNormDensity K ell j d normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        (rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) * C *
          (t / (f * d : ℕ)) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C, hC⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨C, ?_⟩
  intro ell j f d hell0 hfd _ _ rayAllowed normMod t hmod hray
  have h := hC (f * d)
    (combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d normMod)) t hmod
  rw [card_combinedCoordinateResidues] at h
  have hmain :
      ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          (generatorCellMainConstant K J *
            (t / (f * d : ℕ)) ^ Nat.card (index K)) =
        combinedRayNormDensity K ell j d normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K)) := by
    have hellR : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell0
    have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
    have hd0 : d ≠ 0 := NeZero.ne d
    have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have hrayR : (ell : ℝ) ^ j * (rayAllowed.card : ℝ) =
        (f : ℝ) ^ Nat.card (index K) := by
      exact_mod_cast hray
    rw [combinedRayNormDensity, normResidueDensity, zpow_neg,
      zpow_natCast, div_pow]
    push_cast
    rw [mul_pow]
    field_simp
    rw [← hrayR]
    ring
  simp only [generatorCellMainConstant, Nat.card_eq_fintype_card] at hmain h
  rw [hmain] at h
  simpa only [generatorCellMainConstant, Nat.card_eq_fintype_card] using h

open Classical in
/-- The fully general squarefree root-bound endpoint.  Its main density is
the literal cardinality ratio of the supplied ray residues, so it applies
without any tensor-cardinality certificate. -/
theorem exists_uniform_combinedRayNormCellCount_cardinalDensity_of_rootBound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f d k : ℕ},
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → ((f * d : ℕ) : ℝ) ≤ t →
      (normDivisibleResidues K d normMod).card ≤
        k ^ d.primeFactors.card *
          d ^ (Nat.card (index K) - 1) →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayNormCardinalDensity K f d rayAllowed normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        C * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C₀, hgeom⟩ :=
    exists_uniform_combinedRayNormCellCount_cardinalDensity K J
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  intro f d k hfd _ _ rayAllowed normMod t hmod hroot
  have h := hgeom hfd rayAllowed normMod t hmod
  refine h.trans ?_
  have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
  have hd0 : d ≠ 0 := NeZero.ne d
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg (f * d)) hmod
  have hratio : 0 ≤ t / ((f * d : ℕ) : ℝ) :=
    div_nonneg ht (Nat.cast_nonneg (f * d))
  calc
    ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          C₀ * (t / ((f * d : ℕ) : ℝ)) ^ (Nat.card (index K) - 1) ≤
        ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
      exact le_abs_self C₀
    _ ≤ ((rayAllowed.card *
          (k ^ d.primeFactors.card *
            d ^ (Nat.card (index K) - 1)) : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
    _ = |C₀| * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
      push_cast
      rw [div_pow, div_pow]
      field_simp
      ring

open Classical in
/-- After the standard root bound for the integral norm form, the endpoint
error has the squarefree-divisor growth required by the Rosser sieve.  The
factor depending on the fixed ray cell family is left explicit; in each
fixed correction family it is absorbed into the uniform constant. -/
theorem exists_uniform_combinedRayNormCellCount_of_rootBound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ell j f d k : ℕ}, ell ≠ 0 →
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → ((f * d : ℕ) : ℝ) ≤ t →
      ell ^ j * rayAllowed.card = f ^ Nat.card (index K) →
      (normDivisibleResidues K d normMod).card ≤
        k ^ d.primeFactors.card *
          d ^ (Nat.card (index K) - 1) →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayNormDensity K ell j d normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        C * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C₀, hgeom⟩ := exists_uniform_combinedRayNormCellCount K J
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  intro ell j f d k hell0 hfd _ _ rayAllowed normMod t hmod hray hroot
  have h := hgeom hell0 hfd rayAllowed normMod t hmod hray
  refine h.trans ?_
  have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
  have hd0 : d ≠ 0 := NeZero.ne d
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg (f * d)) hmod
  have hratio : 0 ≤ t / ((f * d : ℕ) : ℝ) :=
    div_nonneg ht (Nat.cast_nonneg (f * d))
  calc
    ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          C₀ * (t / ((f * d : ℕ) : ℝ)) ^ (Nat.card (index K) - 1) ≤
        ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
      exact le_abs_self C₀
    _ ≤ ((rayAllowed.card *
          (k ^ d.primeFactors.card *
            d ^ (Nat.card (index K) - 1)) : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
    _ = |C₀| * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
      push_cast
      rw [div_pow, div_pow]
      field_simp
      ring

open Classical in
/-- Root-bound version with the correct unit-residue normalization.  This is
the endpoint used when a tensor cell is an `ell⁻ʲ` fraction of a finite
unit-residue family whose cardinality need not be `f^[K:ℚ]`. -/
theorem exists_uniform_combinedRayUnitNormCellCount_of_rootBound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ell j f d k unitResidueCount : ℕ}, ell ≠ 0 →
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (normMod : (index K → ZMod d) → ZMod d) →
      (t : ℝ) → ((f * d : ℕ) : ℝ) ≤ t →
      ell ^ j * rayAllowed.card = unitResidueCount →
      (normDivisibleResidues K d normMod).card ≤
        k ^ d.primeFactors.card *
          d ^ (Nat.card (index K) - 1) →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d normMod)) t : ℝ) -
        combinedRayUnitNormDensity K ell j f d unitResidueCount normMod *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        C * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C₀, hgeom⟩ := exists_uniform_combinedRayUnitNormCellCount K J
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  intro ell j f d k unitResidueCount hell0 hfd _ _ rayAllowed normMod
    t hmod hray hroot
  have h := hgeom hell0 hfd rayAllowed normMod t hmod hray
  refine h.trans ?_
  have hf0 : f ≠ 0 := fun hf ↦ NeZero.ne (f * d) (by simp [hf])
  have hd0 : d ≠ 0 := NeZero.ne d
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf0
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg (f * d)) hmod
  have hratio : 0 ≤ t / ((f * d : ℕ) : ℝ) :=
    div_nonneg ht (Nat.cast_nonneg (f * d))
  calc
    ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          C₀ * (t / ((f * d : ℕ) : ℝ)) ^ (Nat.card (index K) - 1) ≤
        ((rayAllowed.card * (normDivisibleResidues K d normMod).card : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
      exact le_abs_self C₀
    _ ≤ ((rayAllowed.card *
          (k ^ d.primeFactors.card *
            d ^ (Nat.card (index K) - 1)) : ℕ) : ℝ) *
          |C₀| * (t / ((f * d : ℕ) : ℝ)) ^
            (Nat.card (index K) - 1) := by
      gcongr
    _ = |C₀| * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
      push_cast
      rw [div_pow, div_pow]
      field_simp
      ring

open Classical in
/-- Prime-local root bounds for a CRT-compatible norm form automatically
supply the honest unit-normalized squarefree remainder estimate.  This is
the direct finite input expected by the Rosser sieve. -/
theorem exists_uniform_combinedRayUnitNormCellCount_of_primeBounds
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : CRTNormResidueSystem K)
        {ell j f d k unitResidueCount : ℕ}, ell ≠ 0 →
      (hfd : f.Coprime d) → [NeZero d] → [NeZero (f * d)] →
      (rayAllowed : Finset (index K → ZMod f)) →
      (t : ℝ) → ((f * d : ℕ) : ℝ) ≤ t →
      ell ^ j * rayAllowed.card = unitResidueCount →
      Squarefree d →
      (∀ p ∈ d.primeFactors,
        M.rootCount K p ≤
          k * p ^ (Nat.card (index K) - 1)) →
      |(allowedGeneratorResidueCellCount J (f * d)
          (combinedCoordinateResidues K hfd rayAllowed
            (normDivisibleResidues K d (M.normMod d))) t : ℝ) -
        combinedRayUnitNormDensity K ell j f d unitResidueCount (M.normMod d) *
          (generatorCellMainConstant K J *
            t ^ Nat.card (index K))| ≤
        C * rayAllowed.card * (k : ℝ) ^ d.primeFactors.card *
          (t / f) ^ (Nat.card (index K) - 1) := by
  obtain ⟨C, hC, hgeom⟩ :=
    exists_uniform_combinedRayUnitNormCellCount_of_rootBound K J
  refine ⟨C, hC, ?_⟩
  intro M ell j f d k unitResidueCount hell0 hfd _ _ rayAllowed t
    hmod hray hd hlocal
  apply hgeom hell0 hfd rayAllowed (M.normMod d) t hmod hray
  exact M.card_normDivisibleResidues_le_of_primeFactors K hd hlocal

end Erdos980.ElliottTail.RayNormRemainder
