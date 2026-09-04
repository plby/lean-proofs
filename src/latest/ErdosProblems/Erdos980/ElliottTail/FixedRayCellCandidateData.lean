/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.OddMediumCoordinateBridge
import ErdosProblems.Erdos980.ElliottTail.RayNormRemainder

/-!
# Finite fixed-ray cell candidates for the conductor-norm sieve

This file is the finite, algebraic adapter between the literal lattice cells
counted by `allowedGeneratorResidueCellCount` and
`RayNormPrimeSieve.Data`.  It deliberately contains no exceptional-prime or
prime-ideal input.

The candidate type is the dependent disjoint union of all lattice points in
the allowed cells modulo the fixed ray modulus.  A `GeneratorRealization`
records the (unique in applications) integral generator represented by each
point.  Its conductor norm is defined honestly as

`N((a)) / N(J)`.

There is one non-definitional arithmetic bridge.  For every sieve divisor
`d`, coordinate CRT and cancellation of `N(J)` must identify the candidates
whose conductor norm is divisible by `d` with the points in the corresponding
allowed cells modulo `f*d`.  `DivisorCellRefinement` packages exactly this
finite equivalence, rather than hiding it as a cardinality assumption.  Once
that equivalence is supplied, both identities consumed by
`OddRayNormRosser` are proved below.
-/

open scoped BigOperators NumberField nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.FixedRayCellCandidateData

open NumberField
open NumberField.mixedEmbedding
open IdealGeneratorCongruenceCount
open OddMediumCoordinateBridge
open RayNormPrimeSieve
open RayNormRemainder

variable (K : Type*) [Field K] [NumberField K]

/-- The actual points in one congruence cell, cut out by the fixed height
region. -/
def CellPoint
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) (height : ℝ) :=
  {x : index K → ℝ //
    x ∈ generatorCongruenceCell J m k ∩
      height • generatorNormRegion K}

/-- The dependent finite union of the allowed fixed-ray cells.  The ray
label is retained, so its cardinal is definitionally the sum of the cell
cardinals and no disjointness proof is needed. -/
def Candidate
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ) :=
  Σ k : {k : index K → ZMod f // k ∈ rayAllowed},
    CellPoint K J f k.1 height

noncomputable instance candidateDecidableEq
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ) :
    DecidableEq (Candidate K J f rayAllowed height) := Classical.decEq _

variable {K}

/-- A geometric candidate carries an integral generator in `J` whose
standard Minkowski coordinates are the recorded lattice point and whose
integral-coordinate residue is the recorded ray label. -/
structure GeneratorRealization
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ) where
  generator : Candidate K J f rayAllowed height → RingOfIntegers K
  generator_mem : ∀ a, generator a ∈ (J : Ideal (RingOfIntegers K))
  embedding_eq_point : ∀ a,
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (generator a : K)) = a.2.1
  coordinateResidue_eq : ∀ a,
    coordinateResidue K J f ⟨generator a, generator_mem a⟩ = a.1.1

/-- Every literal point of a generator congruence cell comes from an
element of the fixed ideal with precisely the indicated integral-coordinate
residue. -/
theorem exists_idealGenerator_of_mem_generatorCongruenceCell
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) (x : index K → ℝ)
    (hx : x ∈ generatorCongruenceCell J m k) :
    ∃ b : (J : Ideal (RingOfIntegers K)),
      (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K (b.1 : K)) = x ∧
      coordinateResidue K J m b = k := by
  classical
  rw [generatorCongruenceCell] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, hxy⟩ := hx
  have hzcoords : ∀ i, ∃ w : ℤ, (w : ℝ) = z i := by
    let := Fintype.ofFinite (index K)
    change z ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (index K))) at hz
    simpa only [
      (Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ z,
      Pi.basisFun_repr, Set.mem_range, eq_intCast] using hz
  choose w hw using hzcoords
  let coords : index K → ℤ :=
    fun i ↦ ((k i).val : ℤ) + (m : ℤ) * w i
  obtain ⟨b, hb⟩ := integralCoordinates_surjective K J coords
  refine ⟨b, ?_, ?_⟩
  · rw [← idealLatticeChart_integralCoordinates K J b, hb]
    rw [← hxy]
    simp only [vadd_eq_add, scaledIdealLatticeChart,
      LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
      generatorCongruenceTranslate, ← map_add]
    congr 1
    funext i
    dsimp only [coords]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hw i]
    norm_cast
  · funext i
    rw [coordinateResidue, hb]
    dsimp only [coords]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_mul,
      ZMod.natCast_self, zero_mul, add_zero]
    exact ZMod.natCast_zmod_val (k i)

/-- Canonical ideal element represented by a tagged point of the finite
cell union. -/
def candidateIdealGenerator
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (a : Candidate K J f rayAllowed height) :
    (J : Ideal (RingOfIntegers K)) :=
  Classical.choose (exists_idealGenerator_of_mem_generatorCongruenceCell
    J f a.1.1 a.2.1 a.2.2.1)

theorem candidateIdealGenerator_embedding
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (a : Candidate K J f rayAllowed height) :
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K ((candidateIdealGenerator J f rayAllowed height a).1 : K)) =
      a.2.1 :=
  (Classical.choose_spec (exists_idealGenerator_of_mem_generatorCongruenceCell
    J f a.1.1 a.2.1 a.2.2.1)).1

theorem candidateIdealGenerator_coordinateResidue
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (a : Candidate K J f rayAllowed height) :
    coordinateResidue K J f
        (candidateIdealGenerator J f rayAllowed height a) = a.1.1 :=
  (Classical.choose_spec (exists_idealGenerator_of_mem_generatorCongruenceCell
    J f a.1.1 a.2.1 a.2.2.1)).2

/-- The literal fixed-ray cell union has a canonical, assumption-free
generator realization. -/
def canonicalGeneratorRealization
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ) :
    GeneratorRealization J f rayAllowed height where
  generator a := (candidateIdealGenerator J f rayAllowed height a).1
  generator_mem a := (candidateIdealGenerator J f rayAllowed height a).2
  embedding_eq_point := candidateIdealGenerator_embedding
    J f rayAllowed height
  coordinateResidue_eq := candidateIdealGenerator_coordinateResidue
    J f rayAllowed height

/-- Conversely, an ideal element lies in the congruence cell labelled by
its own integral-coordinate residue. -/
theorem embedding_mem_generatorCongruenceCell_coordinateResidue
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (b : (J : Ideal (RingOfIntegers K))) :
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (b.1 : K)) ∈
      generatorCongruenceCell J m (coordinateResidue K J m b) := by
  classical
  let k := coordinateResidue K J m b
  have hdvd : ∀ i, (m : ℤ) ∣
      integralCoordinates K J b i - ((k i).val : ℤ) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_natCast, k, coordinateResidue]
    rw [ZMod.natCast_zmod_val, sub_self]
  choose z hz using hdvd
  let zr : index K → ℝ := fun i ↦ (z i : ℝ)
  have hzr : zr ∈
      (Submodule.span ℤ (Set.range
        (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
    let := Fintype.ofFinite (index K)
    change zr ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (index K)))
    simpa only [
      (Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ zr,
      Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm] using
      (fun i ↦ ⟨z i, rfl⟩)
  rw [generatorCongruenceCell]
  refine ⟨scaledIdealLatticeChart J m zr, ⟨zr, hzr, rfl⟩, ?_⟩
  simp only [vadd_eq_add, scaledIdealLatticeChart,
    LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
    generatorCongruenceTranslate]
  rw [← map_add, ← idealLatticeChart_integralCoordinates K J b]
  congr 1
  funext i
  have hint : ((k i).val : ℤ) + (m : ℤ) * z i =
      integralCoordinates K J b i := by
    have := hz i
    omega
  change ((k i).val : ℝ) + (m : ℝ) * (z i : ℝ) =
    (integralCoordinates K J b i : ℝ)
  exact_mod_cast hint

/-- Reducing integral coordinates modulo a product and then applying CRT
is the same as reducing separately modulo the two factors. -/
theorem coordinateChineseRemainder_coordinateResidue
    (J : (Ideal (RingOfIntegers K))⁰) {f d : ℕ}
    [NeZero f] [NeZero d] [NeZero (f * d)] (hfd : f.Coprime d)
    (b : (J : Ideal (RingOfIntegers K))) :
    IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd
        (coordinateResidue K J (f * d) b) =
      (coordinateResidue K J f b, coordinateResidue K J d b) := by
  apply Prod.ext <;> funext i
  · change (ZMod.chineseRemainder hfd
        ((integralCoordinates K J b i : ℤ) : ZMod (f * d))).1 =
      ((integralCoordinates K J b i : ℤ) : ZMod f)
    change (ZMod.castHom (show f.lcm d ∣ f * d by simp [Nat.lcm_dvd_iff])
        (ZMod f × ZMod d)
        (((integralCoordinates K J b i : ℤ) : ZMod (f * d)))).1 = _
    rw [ZMod.castHom_apply, Prod.fst_zmod_cast]
    rw [ZMod.cast_intCast (by simp)]
  · change (ZMod.chineseRemainder hfd
        ((integralCoordinates K J b i : ℤ) : ZMod (f * d))).2 =
      ((integralCoordinates K J b i : ℤ) : ZMod d)
    change (ZMod.castHom (show f.lcm d ∣ f * d by simp [Nat.lcm_dvd_iff])
        (ZMod f × ZMod d)
        (((integralCoordinates K J b i : ℤ) : ZMod (f * d)))).2 = _
    rw [ZMod.castHom_apply, Prod.snd_zmod_cast]
    rw [ZMod.cast_intCast (by simp)]

/-- The coordinate norm form evaluated on an ideal element's own residue
is its signed algebraic norm modulo the same modulus. -/
theorem coordinateAlgebraNormMod_coordinateResidue
    (J : (Ideal (RingOfIntegers K))⁰) (d : ℕ) [NeZero d]
    (b : (J : Ideal (RingOfIntegers K))) :
    coordinateAlgebraNormMod K J d (coordinateResidue K J d b) =
      ((Algebra.norm ℤ b.1 : ℤ) : ZMod d) := by
  let rep : (J : Ideal (RingOfIntegers K)) :=
    coordinateRepresentative K J (coordinateResidue K J d b)
  have hres : coordinateResidue K J d b =
      coordinateResidue K J d rep := by
    simp only [rep, coordinateResidue_coordinateRepresentative]
  obtain ⟨c, hc⟩ :=
    (coordinateResidue_eq_iff_exists_sub_eq_nsmul K J).mp hres
  have hb : b.1 = rep.1 + (d : RingOfIntegers K) * c.1 := by
    have hc' : b.1 - rep.1 = (d : RingOfIntegers K) * c.1 := by
      have hcval := congrArg Subtype.val hc
      change b.1 - rep.1 = (d : ℕ) • c.1 at hcval
      simpa only [nsmul_eq_mul] using hcval
    linear_combination hc'
  rw [hb, algebraNorm_add_nat_mul_mod]
  rfl

/-- Under coprimality with `N(J)`, vanishing of the coordinate norm form
is exactly divisibility of the natural conductor norm. -/
theorem coordinateNorm_zero_iff_dvd_conductorNorm
    (J : (Ideal (RingOfIntegers K))⁰) (d : ℕ) [NeZero d]
    (b : (J : Ideal (RingOfIntegers K)))
    (hdJ : d.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    coordinateAlgebraNormMod K J d (coordinateResidue K J d b) = 0 ↔
      d ∣ Ideal.absNorm (Ideal.span ({b.1} : Set (RingOfIntegers K))) /
        Ideal.absNorm (J : Ideal (RingOfIntegers K)) := by
  rw [coordinateAlgebraNormMod_coordinateResidue]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← Int.dvd_natAbs]
  rw [Int.natCast_dvd_natCast]
  rw [← Ideal.absNorm_span_singleton]
  have hJdvd : Ideal.absNorm (J : Ideal (RingOfIntegers K)) ∣
      Ideal.absNorm (Ideal.span ({b.1} : Set (RingOfIntegers K))) := by
    apply Ideal.absNorm_dvd_absNorm_of_le
    rw [Ideal.span_le]
    exact Set.singleton_subset_iff.mpr b.2
  conv_lhs => rw [← Nat.div_mul_cancel hJdvd]
  exact hdJ.dvd_mul_right

/-- A tagged candidate is determined by its geometric point.  Its ray
label is recovered as the integral-coordinate residue of the unique ideal
element mapping to that point. -/
theorem candidate_eq_of_point_eq
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (allowed : Finset (index K → ZMod m)) (height : ℝ)
    {a b : Candidate K J m allowed height} (hpoint : a.2.1 = b.2.1) :
    a = b := by
  have hgen : candidateIdealGenerator J m allowed height a =
      candidateIdealGenerator J m allowed height b := by
    apply Subtype.ext
    apply RingOfIntegers.coe_injective (K := K)
    apply mixedEmbedding_injective K
    apply (mixedEmbedding.stdBasis K).equivFunL.injective
    rw [candidateIdealGenerator_embedding, candidateIdealGenerator_embedding,
      hpoint]
  have hk : a.1.1 = b.1.1 := by
    rw [← candidateIdealGenerator_coordinateResidue J m allowed height a,
      ← candidateIdealGenerator_coordinateResidue J m allowed height b,
      hgen]
  cases a with
  | mk ka xa =>
      cases b with
      | mk kb xb =>
          dsimp only at hk hpoint ⊢
          have hkab : ka = kb := Subtype.ext hk
          subst kb
          congr 1
          exact Subtype.ext hpoint

/-- The natural conductor norm represented by a fixed-ideal generator. -/
def conductorNorm
    {J : (Ideal (RingOfIntegers K))⁰} {f : ℕ} [NeZero f]
    {rayAllowed : Finset (index K → ZMod f)} {height : ℝ}
    (R : GeneratorRealization J f rayAllowed height)
    (a : Candidate K J f rayAllowed height) : ℕ :=
  Ideal.absNorm (Ideal.span ({R.generator a} : Set (RingOfIntegers K))) /
    Ideal.absNorm (J : Ideal (RingOfIntegers K))

/-- The ideal norm of `J` divides the principal ideal norm of every realized
candidate. -/
theorem correctionNorm_dvd_principalNorm
    {J : (Ideal (RingOfIntegers K))⁰} {f : ℕ} [NeZero f]
    {rayAllowed : Finset (index K → ZMod f)} {height : ℝ}
    (R : GeneratorRealization J f rayAllowed height)
    (a : Candidate K J f rayAllowed height) :
    Ideal.absNorm (J : Ideal (RingOfIntegers K)) ∣
      Ideal.absNorm
        (Ideal.span ({R.generator a} : Set (RingOfIntegers K))) := by
  apply Ideal.absNorm_dvd_absNorm_of_le
  rw [Ideal.span_le]
  exact Set.singleton_subset_iff.mpr (R.generator_mem a)

/-- Consequently the quotient defining the conductor norm has the exact
principal-norm factorization required by `RayNormPrimeSieve.Data`. -/
theorem principalNorm_eq_conductorNorm_mul
    {J : (Ideal (RingOfIntegers K))⁰} {f : ℕ} [NeZero f]
    {rayAllowed : Finset (index K → ZMod f)} {height : ℝ}
    (R : GeneratorRealization J f rayAllowed height)
    (a : Candidate K J f rayAllowed height) :
    Ideal.absNorm
        (Ideal.span ({R.generator a} : Set (RingOfIntegers K))) =
      conductorNorm R a *
        Ideal.absNorm (J : Ideal (RingOfIntegers K)) := by
  exact (Nat.div_mul_cancel (correctionNorm_dvd_principalNorm R a)).symm

/-- The exact normalized root-count arithmetic function.  Its value at
`d` is `#\{x mod d : N(x)=0\} / d^[K:ℚ]`; defining it also at zero makes
it a genuine `ArithmeticFunction`. -/
def normResidueDensityFunction (M : CRTNormResidueSystem K) :
    ArithmeticFunction ℝ where
  toFun d := (M.rootCount K d : ℝ) /
    (d : ℝ) ^ Nat.card (index K)
  map_zero' := by simp [CRTNormResidueSystem.rootCount]

@[simp] theorem normResidueDensityFunction_apply
    (M : CRTNormResidueSystem K) (d : ℕ) :
    normResidueDensityFunction M d =
      (M.rootCount K d : ℝ) /
        (d : ℝ) ^ Nat.card (index K) := rfl

/-- CRT multiplicativity of the numerator and complete multiplicativity of
the denominator make the normalized root density multiplicative. -/
theorem normResidueDensityFunction_mult (M : CRTNormResidueSystem K) :
    (normResidueDensityFunction M).IsMultiplicative := by
  constructor
  · rw [normResidueDensityFunction_apply, M.rootCount_one K]
    simp
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := by simpa using hmn
      subst n
      simp [normResidueDensityFunction, CRTNormResidueSystem.rootCount]
    by_cases hn : n = 0
    · subst n
      have hm1 : m = 1 := by simpa using hmn
      subst m
      simp [normResidueDensityFunction, CRTNormResidueSystem.rootCount]
    let : NeZero m := ⟨hm⟩
    let : NeZero n := ⟨hn⟩
    let : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
    rw [normResidueDensityFunction_apply,
      normResidueDensityFunction_apply, normResidueDensityFunction_apply,
      M.rootCount_mul K m n hmn]
    push_cast
    rw [mul_pow]
    field_simp
    <;> ring

/-- Away from zero, the arithmetic function is literally the geometric
norm-residue density used by the ray/norm remainder theorem. -/
theorem normResidueDensityFunction_eq
    (M : CRTNormResidueSystem K) (d : ℕ) [NeZero d] :
    normResidueDensityFunction M d =
      normResidueDensity K d (M.normMod d) := by
  rw [normResidueDensityFunction_apply, normResidueDensity,
    ← M.rootCount_eq K d]

/-- The exact ray-unit main mass, before multiplying by the norm density.
This is chosen so that `nu d * totalMass` is definitionally the combined
ray/unit/norm main term. -/
def rayCellTotalMass
    (J : (Ideal (RingOfIntegers K))⁰)
    (ell j f unitResidueCount : ℕ) (height : ℝ) : ℝ :=
  (ell : ℝ) ^ (- (j : ℤ)) *
    ((unitResidueCount : ℝ) /
      (f : ℝ) ^ Nat.card (index K)) *
    (generatorCellMainConstant K J *
      height ^ Nat.card (index K))

/-! ## Finite union and the only required refinement equivalence -/

/-- A congruence cell meets every dilate of the bounded generator region
in a finite set.  This is the generic geometric fact needed to form the
candidate `Finset`; it has no exceptional-prime dependencies. -/
theorem generatorCongruenceCell_inter_generatorNormRegion_finite
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) (height : ℝ) :
    Set.Finite (generatorCongruenceCell J m k ∩
      height • generatorNormRegion K) := by
  classical
  let L : Set (index K → ℝ) :=
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K))) :
      Set (index K → ℝ))
  let e : (index K → ℝ) ≃ₜ (index K → ℝ) :=
    (scaledIdealLatticeChart J m).toContinuousLinearEquiv.toHomeomorph |>.trans
      (Homeomorph.addLeft (generatorCongruenceTranslate J k))
  have hcell : generatorCongruenceCell J m k = e '' L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨scaledIdealLatticeChart J m z, ⟨z, hz, rfl⟩, rfl⟩
  let : DiscreteTopology
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K)))) :=
    inferInstance
  have hLdiscrete : IsDiscrete L := by
    dsimp only [L]
    exact DiscreteTopology.isDiscrete
  have hLclosed : IsClosed L := by
    change IsClosed
      ((Submodule.span ℤ (Set.range
        (Pi.basisFun ℝ (index K)))).toAddSubgroup : Set (index K → ℝ))
    exact AddSubgroup.isClosed_of_discrete
  have hcellDiscrete : IsDiscrete (generatorCongruenceCell J m k) := by
    rw [hcell]
    exact hLdiscrete.image e.isInducing
  have hcellClosed : IsClosed (generatorCongruenceCell J m k) := by
    rw [hcell]
    exact e.isClosed_image.mpr hLclosed
  have hregion : Bornology.IsBounded (generatorNormRegion K) :=
    (mixedEmbedding.stdBasis K).equivFunL.lipschitz.isBounded_image
      (mixedEmbedding.fundamentalCone.isBounded_normLeOne K)
  have hscaled : Bornology.IsBounded (height • generatorNormRegion K) :=
    Bornology.IsBounded.smul₀ hregion height
  simpa only [Set.inter_comm] using
    Metric.finite_isBounded_inter_isClosed hcellDiscrete hscaled hcellClosed

/-- Turn the dependent cell union into the literal finite candidate set.
Finiteness is intentionally a geometric input here: the existing lattice
count is stated using `Nat.card`, while this adapter needs an actual
`Finset`. -/
def candidateFinset
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K)) :
    Finset (Candidate K J f rayAllowed height) := by
  classical
  letI : ∀ k : {k : index K → ZMod f // k ∈ rayAllowed},
      Fintype (CellPoint K J f k.1 height) :=
    fun k ↦ (hfinite k.1 k.2).fintype
  letI : Fintype (Candidate K J f rayAllowed height) := by
    unfold Candidate
    infer_instance
  exact Finset.univ

@[simp] theorem mem_candidateFinset
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (a : Candidate K J f rayAllowed height) :
    a ∈ candidateFinset (K := K) J f rayAllowed height hfinite := by
  classical
  simp [candidateFinset]

/-- The dependent union has exactly the cardinal used by the geometric
allowed-cell count. -/
theorem candidate_natCard_eq_allowedGeneratorResidueCellCount
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K)) :
    Nat.card (Candidate K J f rayAllowed height) =
      allowedGeneratorResidueCellCount J f rayAllowed height := by
  classical
  let : ∀ k : {k : index K → ZMod f // k ∈ rayAllowed},
      Fintype (CellPoint K J f k.1 height) :=
    fun k ↦ (hfinite k.1 k.2).fintype
  rw [Candidate, Nat.card_sigma, allowedGeneratorResidueCellCount]
  simpa only [CellPoint] using
    (Finset.sum_subtype rayAllowed (fun _ ↦ Iff.rfl) (fun k ↦
    Nat.card ↑(generatorCongruenceCell J f k ∩
      height • generatorNormRegion K))).symm

/-- The combined `(f*d)`-cell union occurring in the divisor mass. -/
abbrev CombinedCandidate
    (J : (Ideal (RingOfIntegers K))⁰) (f d : ℕ)
    [NeZero d] [NeZero (f * d)] (hfd : f.Coprime d)
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (M : CRTNormResidueSystem K) :=
  Candidate K J (f * d)
    (combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d (M.normMod d))) height

/-- The precise arithmetic refinement needed to pass from a ray cell
modulo `f` to simultaneous ray/norm cells modulo `f*d`.

This is an equivalence of the actual finite objects, not an assumed
cardinality equation.  In the cyclotomic application it is supplied by:
coordinate CRT, the equality between the coordinate norm form and the
algebraic norm, and cancellation of `N(J)` using `d.Coprime (N J)`. -/
structure DivisorCellRefinement
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ) (M : CRTNormResidueSystem K)
    (hfprod : f.Coprime (sievePrimes.prod id)) where
  combined_finite : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
      (hd : d ∣ sievePrimes.prod id)
      (k : index K → ZMod (f * d)),
      k ∈ combinedCoordinateResidues K
          (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
          (normDivisibleResidues K d (M.normMod d)) →
      Set.Finite (generatorCongruenceCell J (f * d) k ∩
        height • generatorNormRegion K)
  equiv : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
      (hd : d ∣ sievePrimes.prod id),
      {a : Candidate K J f rayAllowed height //
        d ∣ conductorNorm R a} ≃
      CombinedCandidate (K := K) J f d
        (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed height M

/-! ## Unconditional coordinate-CRT refinement -/

/-- Refine a fixed-ray candidate to its simultaneous ray/norm residue cell
at a sieve divisor. -/
def refineCandidate
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ)
    (hfprod : f.Coprime (sievePrimes.prod id))
    (hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))))
    (d : ℕ) [NeZero d] [NeZero (f * d)]
    (hd : d ∣ sievePrimes.prod id)
    (a : {a : Candidate K J f rayAllowed height //
      d ∣ conductorNorm R a}) :
    CombinedCandidate (K := K) J f d
      (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed height
      (coordinateAlgebraNormResidueSystem K J) := by
  classical
  let hfd : f.Coprime d := Nat.Coprime.of_dvd_right hd hfprod
  let b : (J : Ideal (RingOfIntegers K)) :=
    ⟨R.generator a.1, R.generator_mem a.1⟩
  let r : index K → ZMod (f * d) := coordinateResidue K J (f * d) b
  have hcrt : IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd r =
      (coordinateResidue K J f b, coordinateResidue K J d b) :=
    coordinateChineseRemainder_coordinateResidue J hfd b
  have hray :
      (IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd r).1 ∈
        rayAllowed := by
    rw [hcrt]
    change coordinateResidue K J f b ∈ rayAllowed
    rw [show coordinateResidue K J f b = a.1.1.1 from R.coordinateResidue_eq a.1]
    exact a.1.1.2
  have hprodJ : (sievePrimes.prod id).Coprime
      (Ideal.absNorm (J : Ideal (RingOfIntegers K))) := by
    rw [Nat.coprime_prod_left_iff]
    exact hgood
  have hdJ : d.Coprime
      (Ideal.absNorm (J : Ideal (RingOfIntegers K))) :=
    Nat.Coprime.of_dvd_left hd hprodJ
  have hnorm :
      (IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd r).2 ∈
        normDivisibleResidues K d
          ((coordinateAlgebraNormResidueSystem K J).normMod d) := by
    rw [hcrt, mem_normDivisibleResidues]
    change coordinateAlgebraNormMod K J d (coordinateResidue K J d b) = 0
    rw [coordinateNorm_zero_iff_dvd_conductorNorm J d b hdJ]
    exact a.2
  have hr : r ∈ combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d
        ((coordinateAlgebraNormResidueSystem K J).normMod d)) :=
    mem_combinedCoordinateResidues.mpr ⟨hray, hnorm⟩
  refine ⟨⟨r, hr⟩, ⟨a.1.2.1, ?_, a.1.2.2.2⟩⟩
  rw [← R.embedding_eq_point a.1]
  exact embedding_mem_generatorCongruenceCell_coordinateResidue J (f * d) b

/-- Forget the norm-residue component of a combined cell.  The resulting
fixed-ray label is recovered from the same point's ideal generator. -/
def coarsenCandidate
    (J : (Ideal (RingOfIntegers K))⁰) (f d : ℕ)
    [NeZero f] [NeZero d] [NeZero (f * d)] (hfd : f.Coprime d)
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (c : CombinedCandidate (K := K) J f d hfd rayAllowed height
      (coordinateAlgebraNormResidueSystem K J)) :
    Candidate K J f rayAllowed height := by
  classical
  let combined := combinedCoordinateResidues K hfd rayAllowed
    (normDivisibleResidues K d
      ((coordinateAlgebraNormResidueSystem K J).normMod d))
  let b : (J : Ideal (RingOfIntegers K)) :=
    candidateIdealGenerator J (f * d) combined height c
  let k : index K → ZMod f := coordinateResidue K J f b
  have hcrt : IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd
      (coordinateResidue K J (f * d) b) =
        (k, coordinateResidue K J d b) :=
    coordinateChineseRemainder_coordinateResidue J hfd b
  have hlabel : coordinateResidue K J (f * d) b = c.1.1 :=
    candidateIdealGenerator_coordinateResidue J (f * d) combined height c
  have hpair : IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd
      c.1.1 = (k, coordinateResidue K J d b) := by
    rw [← hlabel]
    exact hcrt
  have hmem := mem_combinedCoordinateResidues.mp c.1.2
  have hk : k ∈ rayAllowed := by
    rw [hpair] at hmem
    exact hmem.1
  refine ⟨⟨k, hk⟩, ⟨c.2.1, ?_, c.2.2.2⟩⟩
  rw [← candidateIdealGenerator_embedding J (f * d) combined height c]
  exact embedding_mem_generatorCongruenceCell_coordinateResidue J f b

/-- The coarsened candidate has conductor norm divisible by `d` whenever
the original combined label belongs to the norm-zero residue set. -/
theorem coarsenCandidate_dvd
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ)
    (hfprod : f.Coprime (sievePrimes.prod id))
    (hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))))
    (d : ℕ) [NeZero d] [NeZero (f * d)]
    (hd : d ∣ sievePrimes.prod id)
    (c : CombinedCandidate (K := K) J f d
      (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed height
      (coordinateAlgebraNormResidueSystem K J)) :
    d ∣ conductorNorm R
      (coarsenCandidate J f d (Nat.Coprime.of_dvd_right hd hfprod)
        rayAllowed height c) := by
  classical
  let hfd : f.Coprime d := Nat.Coprime.of_dvd_right hd hfprod
  let combined := combinedCoordinateResidues K hfd rayAllowed
    (normDivisibleResidues K d
      ((coordinateAlgebraNormResidueSystem K J).normMod d))
  let b : (J : Ideal (RingOfIntegers K)) :=
    candidateIdealGenerator J (f * d) combined height c
  let a := coarsenCandidate J f d hfd rayAllowed height c
  have hgen : R.generator a = b.1 := by
    apply RingOfIntegers.coe_injective (K := K)
    apply mixedEmbedding_injective K
    apply (mixedEmbedding.stdBasis K).equivFunL.injective
    rw [R.embedding_eq_point a,
      candidateIdealGenerator_embedding J (f * d) combined height c]
    rfl
  have hprodJ : (sievePrimes.prod id).Coprime
      (Ideal.absNorm (J : Ideal (RingOfIntegers K))) := by
    rw [Nat.coprime_prod_left_iff]
    exact hgood
  have hdJ : d.Coprime
      (Ideal.absNorm (J : Ideal (RingOfIntegers K))) :=
    Nat.Coprime.of_dvd_left hd hprodJ
  have hcrt : IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd
      (coordinateResidue K J (f * d) b) =
        (coordinateResidue K J f b, coordinateResidue K J d b) :=
    coordinateChineseRemainder_coordinateResidue J hfd b
  have hlabel : coordinateResidue K J (f * d) b = c.1.1 :=
    candidateIdealGenerator_coordinateResidue J (f * d) combined height c
  have hmem := mem_combinedCoordinateResidues.mp c.1.2
  have hzero : coordinateAlgebraNormMod K J d
      (coordinateResidue K J d b) = 0 := by
    have hz := (mem_normDivisibleResidues K).mp hmem.2
    have hsnd :
        (IdealGeneratorCongruenceCount.coordinateChineseRemainder K hfd
          c.1.1).2 = coordinateResidue K J d b := by
      rw [← hlabel]
      exact congrArg Prod.snd hcrt
    rw [← hsnd]
    exact hz
  have hdcond :=
    (coordinateNorm_zero_iff_dvd_conductorNorm J d b hdJ).mp hzero
  change d ∣ Ideal.absNorm
      (Ideal.span ({R.generator a} : Set (RingOfIntegers K))) /
        Ideal.absNorm (J : Ideal (RingOfIntegers K))
  rw [hgen]
  exact hdcond

/-- Coordinate CRT gives the actual divisor-cell equivalence; no cardinality
or realization identity is assumed. -/
def divisorCellEquiv
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ)
    (hfprod : f.Coprime (sievePrimes.prod id))
    (hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))))
    (d : ℕ) [NeZero d] [NeZero (f * d)]
    (hd : d ∣ sievePrimes.prod id) :
    {a : Candidate K J f rayAllowed height // d ∣ conductorNorm R a} ≃
      CombinedCandidate (K := K) J f d
        (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed height
        (coordinateAlgebraNormResidueSystem K J) where
  toFun := refineCandidate J f rayAllowed height R sievePrimes hfprod
    hgood d hd
  invFun c := ⟨coarsenCandidate J f d
      (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed height c,
    coarsenCandidate_dvd J f rayAllowed height R sievePrimes hfprod
      hgood d hd c⟩
  left_inv a := by
    apply Subtype.ext
    apply candidate_eq_of_point_eq J f rayAllowed height
    rfl
  right_inv c := by
    apply candidate_eq_of_point_eq J (f * d)
      (combinedCoordinateResidues K
        (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
        (normDivisibleResidues K d
          ((coordinateAlgebraNormResidueSystem K J).normMod d))) height
    rfl

/-- Build the complete divisor refinement from the canonical coordinate
maps and the elementary coprimality of the selected sieve primes with
`N(J)`.  Finiteness of the combined cells is transported from the original
finite ray-cell union through the equivalence. -/
def divisorCellRefinement
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ)
    (hfprod : f.Coprime (sievePrimes.prod id))
    (hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    DivisorCellRefinement J f rayAllowed height R sievePrimes
      (coordinateAlgebraNormResidueSystem K J) hfprod where
  equiv d _ _ hd := divisorCellEquiv J f rayAllowed height R sievePrimes
    hfprod hgood d hd
  combined_finite d _ _ hd k hk := by
    classical
    let : ∀ r : {r : index K → ZMod f // r ∈ rayAllowed},
        Fintype (CellPoint K J f r.1 height) :=
      fun r ↦ (hfinite r.1 r.2).fintype
    let : Fintype (Candidate K J f rayAllowed height) := by
      unfold Candidate
      infer_instance
    let hfd : f.Coprime d := Nat.Coprime.of_dvd_right hd hfprod
    let combined := combinedCoordinateResidues K hfd rayAllowed
      (normDivisibleResidues K d
        ((coordinateAlgebraNormResidueSystem K J).normMod d))
    let e := divisorCellEquiv J f rayAllowed height R sievePrimes
      hfprod hgood d hd
    let : Finite (CombinedCandidate (K := K) J f d hfd rayAllowed height
        (coordinateAlgebraNormResidueSystem K J)) :=
      Finite.of_injective e.symm e.symm.injective
    let includeCell : CellPoint K J (f * d) k height →
        CombinedCandidate (K := K) J f d hfd rayAllowed height
          (coordinateAlgebraNormResidueSystem K J) :=
      fun x ↦ ⟨⟨k, hk⟩, x⟩
    let : Finite (CellPoint K J (f * d) k height) :=
      Finite.of_injective includeCell (by
        intro x y hxy
        exact Subtype.ext (congrArg (fun c ↦ c.2.1) hxy))
    change Set.Finite (generatorCongruenceCell J (f * d) k ∩
      height • generatorNormRegion K)
    rw [← Set.finite_coe_iff]
    change Finite (CellPoint K J (f * d) k height)
    infer_instance

/-- Assumption-free finite refinement for the literal cell union. -/
def canonicalDivisorCellRefinement
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (R : GeneratorRealization J f rayAllowed height)
    (sievePrimes : Finset ℕ)
    (hfprod : f.Coprime (sievePrimes.prod id))
    (hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    DivisorCellRefinement J f rayAllowed height R sievePrimes
      (coordinateAlgebraNormResidueSystem K J) hfprod :=
  divisorCellRefinement J f rayAllowed height
    (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
      J f k height) R sievePrimes hfprod hgood

/-! ## The concrete `RayNormPrimeSieve.Data` -/

/-- Build the complete conductor-norm sieve data from the literal fixed-ray
cell union.  The only numerical local inputs are positivity and strict
density below one at the selected sieve primes. -/
def data
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (normBound : ℕ)
    (hnormBound : ∀ a, conductorNorm R a ≤ normBound)
    (sievePrimes : Finset ℕ)
    (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K)) :
    Data K (Candidate K J f rayAllowed height) where
  correctionIdeal := J
  candidates := candidateFinset (K := K) J f rayAllowed height hfinite
  generator := R.generator
  generator_mem_correction := fun a _ ↦ R.generator_mem a
  conductorNorm := conductorNorm R
  normBound := normBound
  conductorNorm_le := fun a _ ↦ hnormBound a
  principalNorm_eq := fun a _ ↦ principalNorm_eq_conductorNorm_mul R a
  weight := fun _ ↦ 1
  weight_nonneg := by simp
  sievePrimes := sievePrimes
  sievePrimes_prime := hsievePrime
  totalMass := rayCellTotalMass (K := K) J ell j f unitResidueCount height
  nu := normResidueDensityFunction (coordinateAlgebraNormResidueSystem K J)
  nu_mult := normResidueDensityFunction_mult
    (coordinateAlgebraNormResidueSystem K J)
  nu_pos_of_prime := by
    intro p hp hpdvd
    rw [normResidueDensityFunction_apply]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos (by exact_mod_cast hrootPos p hp hpdvd)
      (pow_pos hp0 _)
  nu_lt_one_of_prime := by
    intro p hp hpdvd
    rw [normResidueDensityFunction_apply, div_lt_one]
    · exact_mod_cast hrootLt p hp hpdvd
    · exact pow_pos (by exact_mod_cast hp.pos) _

/-- The canonical fixed-ray-cell `Data`: its candidates are the literal
finite union of geometric cells and its generators are recovered
canonically from those points. -/
def canonicalData
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (normBound : ℕ)
    (hnormBound : ∀ a,
      conductorNorm (canonicalGeneratorRealization J f rayAllowed height) a ≤
        normBound)
    (sievePrimes : Finset ℕ)
    (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K)) :
    Data K (Candidate K J f rayAllowed height) :=
  data J f rayAllowed height
    (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
      J f k height)
    (canonicalGeneratorRealization J f rayAllowed height)
    normBound hnormBound sievePrimes hsievePrime ell j unitResidueCount
    hrootPos hrootLt

@[simp] theorem data_candidates
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (normBound : ℕ) (hnormBound : ∀ a, conductorNorm R a ≤ normBound)
    (sievePrimes : Finset ℕ) (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K)) :
    (data (K := K) J f rayAllowed height hfinite R normBound hnormBound
      sievePrimes hsievePrime ell j unitResidueCount hrootPos hrootLt).candidates =
      candidateFinset (K := K) J f rayAllowed height hfinite := rfl

/-- Unit weights turn a divisor mass into the literal cardinality of the
corresponding subtype of the fixed-ray cell union. -/
theorem data_normDivisorMass_eq_natCard
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (normBound : ℕ) (hnormBound : ∀ a, conductorNorm R a ≤ normBound)
    (sievePrimes : Finset ℕ) (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K)) (d : ℕ) :
    normDivisorMass
        (data (K := K) J f rayAllowed height hfinite R normBound hnormBound
          sievePrimes hsievePrime ell j unitResidueCount hrootPos hrootLt) d =
      (Nat.card {a : Candidate K J f rayAllowed height //
        d ∣ conductorNorm R a} : ℝ) := by
  classical
  let : ∀ k : {k : index K → ZMod f // k ∈ rayAllowed},
      Fintype (CellPoint K J f k.1 height) :=
    fun k ↦ (hfinite k.1 k.2).fintype
  let : Fintype (Candidate K J f rayAllowed height) := by
    unfold Candidate
    infer_instance
  change (∑ a ∈ candidateFinset (K := K) J f rayAllowed height hfinite,
      if d ∣ conductorNorm R a then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  norm_cast
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_ofFinset _ (fun a ↦ by
    change a ∈ Finset.filter (fun a ↦ d ∣ conductorNorm R a)
        (candidateFinset (K := K) J f rayAllowed height hfinite) ↔
      d ∣ conductorNorm R a
    simp only [Finset.mem_filter, mem_candidateFinset, true_and])).symm

/-- The chosen normalized arithmetic function and total mass give exactly
the combined ray/unit/norm main term required by `OddRayNormRosser`. -/
theorem data_nu_mul_totalMass
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (normBound : ℕ) (hnormBound : ∀ a, conductorNorm R a ≤ normBound)
    (sievePrimes : Finset ℕ) (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K))
    (d : ℕ) [NeZero d] :
    let D := data (K := K) J f rayAllowed height hfinite R normBound
      hnormBound sievePrimes hsievePrime ell j unitResidueCount
      hrootPos hrootLt
    D.nu d * D.totalMass =
      combinedRayUnitNormDensity K ell j f d unitResidueCount
          ((coordinateAlgebraNormResidueSystem K J).normMod d) *
        (generatorCellMainConstant K J *
          height ^ Nat.card (index K)) := by
  dsimp only [data]
  rw [normResidueDensityFunction_eq]
  unfold rayCellTotalMass combinedRayUnitNormDensity
  ring

/-- The refinement equivalence turns the unit-weight divisor mass into the
literal combined `(f*d)` lattice-cell count. -/
theorem data_normDivisorMass_eq_allowedGeneratorResidueCellCount
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f)) (height : ℝ)
    (hfinite : ∀ k ∈ rayAllowed,
      Set.Finite (generatorCongruenceCell J f k ∩
        height • generatorNormRegion K))
    (R : GeneratorRealization J f rayAllowed height)
    (normBound : ℕ) (hnormBound : ∀ a, conductorNorm R a ≤ normBound)
    (sievePrimes : Finset ℕ) (hsievePrime : ∀ p ∈ sievePrimes, p.Prime)
    (ell j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K J).rootCount K p <
        p ^ Nat.card (index K))
    (hfprod : f.Coprime (sievePrimes.prod id))
    (Ref : DivisorCellRefinement J f rayAllowed height R sievePrimes
      (coordinateAlgebraNormResidueSystem K J) hfprod)
    (d : ℕ) [NeZero d] [NeZero (f * d)]
    (hd : d ∣ sievePrimes.prod id) :
    normDivisorMass
        (data (K := K) J f rayAllowed height hfinite R normBound hnormBound
          sievePrimes hsievePrime ell j unitResidueCount hrootPos hrootLt) d =
      (allowedGeneratorResidueCellCount J (f * d)
        (combinedCoordinateResidues K
          (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
          (normDivisibleResidues K d
            ((coordinateAlgebraNormResidueSystem K J).normMod d))) height : ℕ) := by
  rw [data_normDivisorMass_eq_natCard]
  norm_cast
  rw [Nat.card_congr (Ref.equiv d hd)]
  exact candidate_natCard_eq_allowedGeneratorResidueCellCount
    J (f * d)
    (combinedCoordinateResidues K
      (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
      (normDivisibleResidues K d
        ((coordinateAlgebraNormResidueSystem K J).normMod d))) height
    (Ref.combined_finite d hd)


end Erdos980.ElliottTail.FixedRayCellCandidateData
