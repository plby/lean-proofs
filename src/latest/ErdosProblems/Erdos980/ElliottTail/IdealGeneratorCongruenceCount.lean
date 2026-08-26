/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CebotarevDensity.ForMathlib.IdealCongruenceCount

/-!
# Uniform congruence-cell counts for canonical number-field generators

This file exposes the lattice statement needed to count canonical cone
generators in prescribed congruence cells.  The analytic input is the
translate-uniform Lipschitz-boundary lattice estimate proved in
`IdealCongruenceCount`.  For a nonzero integral ideal `J`, we choose a real
linear chart identifying its Minkowski lattice with `ℤ^[K:ℚ]`.  A coordinate
pattern `k : index K → ZMod m` then determines a coset of the sublattice
`m Λ_J`.

The main theorem below counts that coset in a dilation of the standard
fundamental-cone norm region, uniformly in `k`.  Its leading term is the
expected covolume quotient and its error is of order `t ^ (d - 1)`.

This is the geometric generator-congruence input to Elliott's tensor sieve.
It deliberately does not assert that the generated ideal is prime: obtaining
an `x / log x` estimate from this `x + O(x^(1-1/d))` lattice count still
requires a separate upper-bound sieve for the corresponding norm form (or a
prime-ideal theorem uniform in the growing ray modulus).
-/

open NumberField Set Submodule Ideal
open scoped NNReal nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.IdealGeneratorCongruenceCount

open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone

/-- Transport of an integral span along a real-linear equivalence. -/
private theorem map_span_int_linearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E ≃ₗ[ℝ] F) (S : Set E) :
    f '' (span ℤ S : Set E) = (span ℤ (f '' S) : Set F) := by
  simpa using congrArg SetLike.coe (Submodule.map_span (f.restrictScalars ℤ).toLinearMap S)

/-- The Minkowski lattice of a nonzero integral ideal admits a full real
coordinate chart whose image of `ℤ^[K:ℚ]` is exactly that ideal lattice. -/
theorem exists_idealLatticeChart {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ),
      T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
        ((mixedEmbedding.stdBasis K).equivFunL ''
          (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
            Set (index K → ℝ)) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) :=
    (mixedEmbedding.stdBasis K).equivFunL
  set I := FractionalIdeal.mk0 K J
  have e : Module.Free.ChooseBasisIndex ℤ I ≃ index K := by
    apply Fintype.equivOfCardEq
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      NumberField.fractionalIdeal_rank, RingOfIntegers.rank,
      ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
  set c : Module.Basis (index K) ℝ (index K → ℝ) :=
    ((mixedEmbedding.fractionalIdealLatticeBasis K I).map Φ.toLinearEquiv).reindex e with hc
  refine ⟨(Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)), ?_⟩
  have hcrange : Set.range c =
      Φ '' (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
    rw [hc, Module.Basis.range_reindex, ← Set.range_comp]
    rfl
  rw [map_span_int_linearEquiv]
  have hrange : ((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K))) ''
      (Set.range (Pi.basisFun ℝ (index K))) = Set.range c := by
    rw [← Set.range_comp]
    congr 1
    ext i
    simp only [Function.comp_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [hrange, hcrange, ← mixedEmbedding.span_idealLatticeBasis K I]
  exact (map_span_int_linearEquiv Φ.toLinearEquiv _).symm

/-- A fixed choice of full-lattice chart for the ideal `J`. -/
def idealLatticeChart {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ) :=
  (exists_idealLatticeChart J).choose

/-- The chosen chart identifies the standard integral lattice with the
Minkowski lattice of `J`. -/
theorem idealLatticeChart_image {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    idealLatticeChart J ''
        (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
      ((mixedEmbedding.stdBasis K).equivFunL ''
        (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
          Set (index K → ℝ)) :=
  (exists_idealLatticeChart J).choose_spec

/-- The standard-coordinate image of the norm-at-most-one slice of the
fundamental cone. -/
def generatorNormRegion (K : Type*) [Field K] [NumberField K] :
    Set (index K → ℝ) :=
  (mixedEmbedding.stdBasis K).equivFunL '' normLeOne K

/-- The `m`-scaled coordinate chart of the ideal lattice. -/
def scaledIdealLatticeChart {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] :
    (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ)
    (Nat.cast_ne_zero.mpr (NeZero.ne m))).trans (idealLatticeChart J)

open Classical in
/-- Scaling the ideal lattice by the rational integer `m` multiplies its
covolume determinant by `m ^ [K:ℚ]`. -/
theorem det_scaledIdealLatticeChart {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] :
    LinearMap.det (scaledIdealLatticeChart J m :
      (index K → ℝ) →ₗ[ℝ] (index K → ℝ)) =
      (m : ℝ) ^ Fintype.card (index K) *
        LinearMap.det (idealLatticeChart J :
          (index K → ℝ) →ₗ[ℝ] (index K → ℝ)) := by
  change LinearMap.det ((idealLatticeChart J :
      (index K → ℝ) →ₗ[ℝ] (index K → ℝ)).comp
      (LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ)
        (Nat.cast_ne_zero.mpr (NeZero.ne m)) :
          (index K → ℝ) →ₗ[ℝ] (index K → ℝ))) = _
  rw [LinearMap.det_comp]
  have hsmul : (LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ)
      (Nat.cast_ne_zero.mpr (NeZero.ne m)) :
        (index K → ℝ) →ₗ[ℝ] (index K → ℝ)) =
      (m : ℝ) • LinearMap.id := by
    ext x i
    simp
  rw [hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [← Module.finrank_eq_card_basis (Pi.basisFun ℝ (index K))]
  ring

open Classical in
/-- Absolute-value form of `det_scaledIdealLatticeChart`, used in the
explicit main term of a congruence-cell count. -/
theorem abs_det_scaledIdealLatticeChart {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] :
    |LinearMap.det (scaledIdealLatticeChart J m :
      (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| =
      (m : ℝ) ^ Fintype.card (index K) *
        |LinearMap.det (idealLatticeChart J :
          (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| := by
  rw [det_scaledIdealLatticeChart, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg m)]

/-- The translate representing the coordinate residue pattern `k` modulo
`m` in the chosen ideal-lattice chart. -/
def generatorCongruenceTranslate {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) {m : ℕ} (k : index K → ZMod m) : index K → ℝ :=
  idealLatticeChart J (fun i ↦ ((k i).val : ℝ))

/-- The complete coordinate congruence cell attached to `k : index K → ZMod m`. -/
def generatorCongruenceCell {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] (k : index K → ZMod m) :
    Set (index K → ℝ) :=
  generatorCongruenceTranslate J k +ᵥ
    (scaledIdealLatticeChart J m ''
      (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))

open Classical in
/-- Uniform effective count of canonical-generator congruence cells.

For every coordinate residue pattern `k modulo m`, the corresponding coset
of `m Λ_J` has the same explicit main term in the dilated fundamental-cone
norm region, with a constant in the boundary error independent of `k` and
`t`. -/
theorem exists_uniform_generatorCongruenceCell_count
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] :
    ∃ C : ℝ, ∀ (k : index K → ZMod m) (t : ℝ), 1 ≤ t →
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) -
        MeasureTheory.volume.real (generatorNormRegion K) /
            |LinearMap.det (scaledIdealLatticeChart J m :
              (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
          t ^ Fintype.card (index K)|
        ≤ C * t ^ (Fintype.card (index K) - 1) := by
  classical
  have hbdd : Bornology.IsBounded (generatorNormRegion K) :=
    (mixedEmbedding.stdBasis K).equivFunL.lipschitz.isBounded_image
      (isBounded_normLeOne K)
  have hmeas : MeasurableSet (generatorNormRegion K) :=
    ((mixedEmbedding.stdBasis K).equivFunL.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr
      (measurableSet_normLeOne K)
  obtain ⟨C, hC⟩ :=
    Chebotarev.exists_card_coset_inter_smul_sub_volume_mul_rpow_le
      (scaledIdealLatticeChart J m) (generatorNormRegion K) hbdd hmeas
        (Chebotarev.normLeOne_frontier_lipschitz_cover_index K)
  refine ⟨C, fun k t ht ↦ ?_⟩
  simpa only [generatorCongruenceCell, generatorCongruenceTranslate] using
    hC (idealLatticeChart J (fun i ↦ ((k i).val : ℝ))) t ht

open Classical in
/-- The same uniform congruence-cell count with the determinant expanded.
This displays the exact factor `m ^ (-[K:ℚ])` in every cell's main term. -/
theorem exists_uniform_generatorCongruenceCell_count_explicit_modulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m] :
    ∃ C : ℝ, ∀ (k : index K → ZMod m) (t : ℝ), 1 ≤ t →
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) -
        MeasureTheory.volume.real (generatorNormRegion K) /
            ((m : ℝ) ^ Fintype.card (index K) *
              |LinearMap.det (idealLatticeChart J :
                (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|) *
          t ^ Fintype.card (index K)|
        ≤ C * t ^ (Fintype.card (index K) - 1) := by
  obtain ⟨C, hC⟩ := exists_uniform_generatorCongruenceCell_count K J m
  refine ⟨C, fun k t ht ↦ ?_⟩
  simpa only [abs_det_scaledIdealLatticeChart] using hC k t ht

open Classical in
/-- A congruence cell for `m Λ_J` is the scalar dilation by `m` of a
translate of the fixed lattice `Λ_J`.  This elementary identity is what
makes the boundary constant uniform even when the modulus grows. -/
theorem generatorCongruenceCell_eq_smul {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) :
    generatorCongruenceCell J m k =
      (m : ℝ) • (((m : ℝ)⁻¹ • generatorCongruenceTranslate J k) +ᵥ
        (idealLatticeChart J ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  ext x
  constructor
  · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(m : ℝ)⁻¹ • generatorCongruenceTranslate J k + idealLatticeChart J z,
      ?_, ?_⟩
    · refine ⟨idealLatticeChart J z, ⟨z, hz, rfl⟩, rfl⟩
    · simp only [scaledIdealLatticeChart, LinearEquiv.trans_apply,
        LinearEquiv.smulOfNeZero_apply, vadd_eq_add]
      rw [smul_add, smul_inv_smul₀ hm, map_smul]
  · rintro ⟨y, ⟨w, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    refine ⟨scaledIdealLatticeChart J m z, ⟨z, hz, rfl⟩, ?_⟩
    simp only [vadd_eq_add, smul_add]
    rw [smul_inv_smul₀ hm]
    simp only [scaledIdealLatticeChart, LinearEquiv.trans_apply,
      LinearEquiv.smulOfNeZero_apply, map_smul]

open Classical in
/-- Cardinality form of `generatorCongruenceCell_eq_smul`: a cell at
modulus `m` and scale `t` is counted by the fixed ideal lattice at scale
`t / m`. -/
theorem card_generatorCongruenceCell_eq_rescaled
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) (t : ℝ) :
    Nat.card ↑(generatorCongruenceCell J m k ∩ t • generatorNormRegion K) =
      Nat.card ↑((((m : ℝ)⁻¹ • generatorCongruenceTranslate J k) +ᵥ
          (idealLatticeChart J ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
        (t / m) • generatorNormRegion K) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  let S : Set (index K → ℝ) :=
    (((m : ℝ)⁻¹ • generatorCongruenceTranslate J k) +ᵥ
        (idealLatticeChart J ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
      (t / m) • generatorNormRegion K
  have himage : (m : ℝ) • S =
      generatorCongruenceCell J m k ∩ t • generatorNormRegion K := by
    dsimp only [S]
    rw [Set.smul_set_inter₀ hm, ← generatorCongruenceCell_eq_smul]
    congr 1
    rw [smul_smul]
    congr 1
    field_simp
  rw [← himage]
  exact Nat.card_image_of_injective (smul_right_injective _ hm) S

open Classical in
/-- Uniform effective congruence-cell count for a growing rational modulus.

Unlike `exists_uniform_generatorCongruenceCell_count`, the constant here is
chosen *before* `m`.  In the natural range `m ≤ t`, rescaling turns the
problem into the fixed lattice `Λ_J` at scale `t / m ≥ 1`.  Thus both the
main term and the boundary error acquire their expected powers of `t / m`,
uniformly in the modulus and the residue vector. -/
theorem exists_uniform_generatorCongruenceCell_count_growing_modulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ C : ℝ, ∀ (m : ℕ) [NeZero m]
      (k : index K → ZMod m) (t : ℝ), (m : ℝ) ≤ t →
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) -
        MeasureTheory.volume.real (generatorNormRegion K) /
            |LinearMap.det (idealLatticeChart J :
              (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
          (t / m) ^ Fintype.card (index K)|
        ≤ C * (t / m) ^ (Fintype.card (index K) - 1) := by
  have hbdd : Bornology.IsBounded (generatorNormRegion K) :=
    (mixedEmbedding.stdBasis K).equivFunL.lipschitz.isBounded_image
      (isBounded_normLeOne K)
  have hmeas : MeasurableSet (generatorNormRegion K) :=
    ((mixedEmbedding.stdBasis K).equivFunL.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr
      (measurableSet_normLeOne K)
  obtain ⟨C, hC⟩ :=
    Chebotarev.exists_card_coset_inter_smul_sub_volume_mul_rpow_le
      (idealLatticeChart J) (generatorNormRegion K) hbdd hmeas
        (Chebotarev.normLeOne_frontier_lipschitz_cover_index K)
  refine ⟨C, fun m _ k t hmt ↦ ?_⟩
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hs : 1 ≤ t / m := (le_div_iff₀ hm0).mpr (by simpa using hmt)
  rw [card_generatorCongruenceCell_eq_rescaled]
  exact hC ((m : ℝ)⁻¹ • generatorCongruenceTranslate J k) (t / m) hs

/-- Sum of the lattice-point counts over a finite set of allowed coordinate
residues.  This is the literal strict-ray-class union count before the
finite correction classes are summed. -/
noncomputable def allowedGeneratorResidueCellCount
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m]
    (allowed : Finset (index K → ZMod m)) (t : ℝ) : ℕ :=
  ∑ k ∈ allowed,
    Nat.card ↑(generatorCongruenceCell J m k ∩ t • generatorNormRegion K)

open Classical in
/-- Finite allowed-cell summation, uniform in a growing scalar modulus.

Every allowed residue has the same main term.  Summing the translate-uniform
estimate therefore multiplies both that term and its boundary error by the
literal number of allowed residues, with no loss from the ray-class
packaging. -/
theorem exists_uniform_allowedGeneratorResidueCellCount
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ C : ℝ, ∀ (m : ℕ) [NeZero m]
      (allowed : Finset (index K → ZMod m)) (t : ℝ), (m : ℝ) ≤ t →
      |(allowedGeneratorResidueCellCount J m allowed t : ℝ) -
        allowed.card *
          (MeasureTheory.volume.real (generatorNormRegion K) /
              |LinearMap.det (idealLatticeChart J :
                (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
            (t / m) ^ Fintype.card (index K))| ≤
        allowed.card * C * (t / m) ^ (Fintype.card (index K) - 1) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_generatorCongruenceCell_count_growing_modulus K J
  refine ⟨C, fun m _ allowed t hmt ↦ ?_⟩
  let main : ℝ := MeasureTheory.volume.real (generatorNormRegion K) /
      |LinearMap.det (idealLatticeChart J :
        (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
      (t / m) ^ Fintype.card (index K)
  let error : ℝ := C * (t / m) ^ (Fintype.card (index K) - 1)
  have hcell : ∀ k : index K → ZMod m,
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main| ≤ error := by
    intro k
    exact hC m k t hmt
  rw [allowedGeneratorResidueCellCount]
  change |((∑ k ∈ allowed,
      Nat.card ↑(generatorCongruenceCell J m k ∩
        t • generatorNormRegion K) : ℕ) : ℝ) - allowed.card * main| ≤
      allowed.card * C * (t / m) ^ (Fintype.card (index K) - 1)
  push_cast only [Nat.cast_sum, Nat.cast_id]
  calc
    |(∑ k ∈ allowed,
        (Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ)) - allowed.card * main| =
        |∑ k ∈ allowed,
          ((Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ) - main)| := by
          rw [Finset.sum_sub_distrib]
          simp
    _ ≤ ∑ k ∈ allowed,
        |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ allowed, error := by
      exact Finset.sum_le_sum fun k _ ↦ hcell k
    _ = allowed.card * error := by simp
    _ = allowed.card * C *
        (t / m) ^ (Fintype.card (index K) - 1) := by
      simp only [error]
      ring

open Classical in
/-- Exact `ell⁻ʲ` normalization of the finite allowed-cell sum in the
special case where the tensor pattern partitions the *entire coordinate
residue space*.

The cardinality hypothesis is the denominator-free statement that the
allowed tensor pattern occupies exactly one of `ell ^ j` equal parts of the
full coordinate residue space, whose cardinality is `m ^ [K:ℚ]`.

This theorem must **not** be used when the tensor pattern ranges only over
unit residue tuples.  In that situation one has
`ell ^ j * allowed.card = fullUnits.card`, not
`ell ^ j * allowed.card = m ^ [K:ℚ]`; use
`exists_uniform_allowedGeneratorResidueCellCount` and retain the local-unit
density `fullUnits.card / m ^ [K:ℚ]`. -/
theorem exists_uniform_allowedGeneratorResidueCellCount_ellFraction
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ C : ℝ, ∀ {ell j : ℕ}, ell ≠ 0 →
      ∀ (m : ℕ) [NeZero m]
      (allowed : Finset (index K → ZMod m)) (t : ℝ), (m : ℝ) ≤ t →
      ell ^ j * allowed.card = m ^ Fintype.card (index K) →
      |(allowedGeneratorResidueCellCount J m allowed t : ℝ) -
        ((m : ℝ) ^ Fintype.card (index K) / (ell : ℝ) ^ j) *
          (MeasureTheory.volume.real (generatorNormRegion K) /
              |LinearMap.det (idealLatticeChart J :
                (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| *
            (t / m) ^ Fintype.card (index K))| ≤
        ((m : ℝ) ^ Fintype.card (index K) / (ell : ℝ) ^ j) * C *
          (t / m) ^ (Fintype.card (index K) - 1) := by
  obtain ⟨C, hC⟩ := exists_uniform_allowedGeneratorResidueCellCount K J
  refine ⟨C, fun {ell j} hell0 m _ allowed t hmt hcard ↦ ?_⟩
  have hellpow : (ell : ℝ) ^ j ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hell0)
  have hcast : (ell : ℝ) ^ j * (allowed.card : ℝ) =
      (m : ℝ) ^ Fintype.card (index K) := by
    exact_mod_cast hcard
  have hallowed : (allowed.card : ℝ) =
      (m : ℝ) ^ Fintype.card (index K) / (ell : ℝ) ^ j := by
    rw [eq_div_iff hellpow]
    simpa [mul_comm] using hcast
  simpa only [hallowed] using hC m allowed t hmt

/-! ## Combining ray and norm-sieve residue conditions by CRT -/

/-- Coordinatewise Chinese remainder equivalence for the chosen ideal
lattice coordinates. -/
def coordinateChineseRemainder
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hcop : f.Coprime d) :
    (index K → ZMod (f * d)) ≃
      (index K → ZMod f) × (index K → ZMod d) where
  toFun k :=
    (fun i ↦ (ZMod.chineseRemainder hcop (k i)).1,
      fun i ↦ (ZMod.chineseRemainder hcop (k i)).2)
  invFun k i := ZMod.chineseRemainder hcop |>.symm (k.1 i, k.2 i)
  left_inv k := by
    funext i
    exact (ZMod.chineseRemainder hcop).left_inv (k i)
  right_inv k := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst
        ((ZMod.chineseRemainder hcop).right_inv (k.1 i, k.2 i))
    · funext i
      exact congrArg Prod.snd
        ((ZMod.chineseRemainder hcop).right_inv (k.1 i, k.2 i))

/-- The residue vectors satisfying a selected ray condition modulo `f` and
a selected norm-zero (or other sieve) condition modulo `d`. -/
noncomputable def combinedCoordinateResidues
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hcop : f.Coprime d)
    (rayAllowed : Finset (index K → ZMod f))
    (normAllowed : Finset (index K → ZMod d)) :
    Finset (index K → ZMod (f * d)) :=
  (rayAllowed ×ˢ normAllowed).map
    (coordinateChineseRemainder K hcop).symm.toEmbedding

/-- CRT makes the combined ray × norm-sieve residue count a literal
product, so the tensor fraction and the norm local density remain separate. -/
theorem card_combinedCoordinateResidues
    (K : Type*) [Field K] [NumberField K]
    {f d : ℕ} (hcop : f.Coprime d)
    (rayAllowed : Finset (index K → ZMod f))
    (normAllowed : Finset (index K → ZMod d)) :
    (combinedCoordinateResidues K hcop rayAllowed normAllowed).card =
      rayAllowed.card * normAllowed.card := by
  rw [combinedCoordinateResidues, Finset.card_map, Finset.card_product]

@[simp] theorem mem_combinedCoordinateResidues
    {K : Type*} [Field K] [NumberField K]
    {f d : ℕ} {hcop : f.Coprime d}
    {rayAllowed : Finset (index K → ZMod f)}
    {normAllowed : Finset (index K → ZMod d)}
    {k : index K → ZMod (f * d)} :
    k ∈ combinedCoordinateResidues K hcop rayAllowed normAllowed ↔
      (coordinateChineseRemainder K hcop k).1 ∈ rayAllowed ∧
        (coordinateChineseRemainder K hcop k).2 ∈ normAllowed := by
  classical
  simp [combinedCoordinateResidues]

end Erdos980.ElliottTail.IdealGeneratorCongruenceCount
