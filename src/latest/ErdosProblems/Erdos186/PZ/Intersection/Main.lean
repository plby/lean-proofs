/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.PZ.Intersection.CommonWitness
import ErdosProblems.Erdos186.PZ.Intersection.ConvexPools
import ErdosProblems.Erdos186.PZ.Intersection.Equation15
import ErdosProblems.Erdos186.PZ.Intersection.Irreducibility
import ErdosProblems.Erdos186.PZ.Intersection.Lattice
import ErdosProblems.Erdos186.ConvexCombination
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext
import ErdosProblems.Erdos186.PZ.Reduction.Replacement
import ErdosProblems.Erdos186.Zonotope

/-!
# The post-CFP intersection theorem

This file composes the exact finite ingredients of Pham--Zakharov Theorem 4.
Each side contains an actual enhanced CFP witness, a disjoint rounding core,
the residual-error assertion produced by zonotope rounding, and the concrete
lattice region contained in the target.  A common covering-radius estimate
then supplies the nonzero lattice point; equation (15) turns it into subset
sums, and the deviation criterion turns those subset sums into the forbidden
average.

The side data do not contain a common point, a subset-sum inclusion, or an
averaging witness.  Those are all conclusions below.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

/-- Concrete CFP and finite-set data for one side, before the two geometric
source lemmas are applied.  This record contains neither residual absorption
nor a target-region inclusion. -/
structure IntersectionSideInput {d : ℕ} (pool : Finset (LatticePoint d))
    (a : LatticePoint d) (orientation : Orientation) where
  reserveBound : ℕ
  rankBound : ℕ
  dilation : ℕ
  loss : ℕ
  witness : CFP.EnhancedCFPWitness (orientedTranslate orientation a pool)
    reserveBound rankBound dilation loss
  target : Finset (LatticePoint d)
  roundingCore : Finset (LatticePoint d)
  roundingCore_subset : roundingCore ⊆ orientedTranslate orientation a pool
  reserved_disjoint_roundingCore : Disjoint witness.reserved roundingCore
  lattice : Set (LatticePoint d)

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}

/-- The exact missing Lemma 12/13 output for a particular CFP side: rounding
the target by the retained core leaves an error absorbed by the translated
dilated progression. -/
def Lemma13ResidualAbsorption
    (I : IntersectionSideInput pool a orientation) : Prop :=
  RoundingErrorsAbsorbedBy I.target I.roundingCore
    (CFP.translate I.witness.translatePoint
      (I.witness.progression.dilate I.dilation).carrier)

/-- The exact target-thickness output of Lemma 14, after the center-error
estimates have converted the centered zonotope inclusion into a cube. -/
def Lemma14TargetThickness (I : IntersectionSideInput pool a orientation)
    (center : Fin d → ℝ) (radius : ℝ) : Prop :=
  ∀ z, z ∈ I.lattice → MemCube center radius z → z ∈ I.target

end IntersectionSideInput

/-- The exact post-CFP data on one side of equation (15). -/
structure IntersectionSide {d : ℕ} (pool : Finset (LatticePoint d))
    (a : LatticePoint d) (orientation : Orientation)
    (center : Fin d → ℝ) (radius : ℝ) where
  reserveBound : ℕ
  rankBound : ℕ
  dilation : ℕ
  loss : ℕ
  /-- The genuine, nondegenerate CFP conclusion for this deviation pool. -/
  witness : CFP.EnhancedCFPWitness (orientedTranslate orientation a pool)
    reserveBound rankBound dilation loss
  /-- The lattice points in the rounded zonotope-plus-progression region. -/
  target : Finset (LatticePoint d)
  /-- The part of the pool left after reserving the CFP absorber. -/
  roundingCore : Finset (LatticePoint d)
  roundingCore_subset : roundingCore ⊆ orientedTranslate orientation a pool
  reserved_disjoint_roundingCore : Disjoint witness.reserved roundingCore
  /-- Lemma 13 plus the scale comparison locate the rounding residual in the
  translated dilated progression. -/
  roundingErrors : RoundingErrorsAbsorbedBy target roundingCore
    (CFP.translate witness.translatePoint
      (witness.progression.dilate dilation).carrier)
  /-- The full-rank lattice associated with the side progression. -/
  lattice : Set (LatticePoint d)
  /-- Lemma 14 and the center-error estimates put the indicated lattice
  cube in the target region. -/
  cube_subset_target : ∀ z, z ∈ lattice → MemCube center radius z → z ∈ target

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}
    {center : Fin d → ℝ} {radius : ℝ}

/-- Assemble one side from its finite CFP input and the two separate source
lemmas.  Keeping this constructor explicit prevents either missing geometric
statement from being hidden in the final intersection theorem. -/
def toIntersectionSide (I : IntersectionSideInput pool a orientation)
    (hround : I.Lemma13ResidualAbsorption)
    (hthick : I.Lemma14TargetThickness center radius) :
    IntersectionSide pool a orientation center radius where
  reserveBound := I.reserveBound
  rankBound := I.rankBound
  dilation := I.dilation
  loss := I.loss
  witness := I.witness
  target := I.target
  roundingCore := I.roundingCore
  roundingCore_subset := I.roundingCore_subset
  reserved_disjoint_roundingCore := I.reserved_disjoint_roundingCore
  roundingErrors := hround
  lattice := I.lattice
  cube_subset_target := hthick

end IntersectionSideInput

namespace IntersectionSide

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}
    {center : Fin d → ℝ} {radius : ℝ}

/-- Equation (15) applied to an enhanced witness: every target point is a
subset sum of the corresponding deviation pool. -/
theorem target_subset_subsetSums
    (S : IntersectionSide pool a orientation center radius) :
    S.target ⊆ GAP.subsetSums (orientedTranslate orientation a pool) := by
  exact equation15_subsetSums_of_cfpWitness S.witness.basic
    S.roundingCore_subset S.reserved_disjoint_roundingCore S.roundingErrors

end IntersectionSide

/-- Readable alias for the already formalized probabilistic-rounding result,
which is Lemma 13 in Pham--Zakharov. -/
theorem lemma13_zonotope_rounding {d : ℕ} (A : Finset (Fin d → ℤ))
    (x : Fin d → ℝ) (width : ℝ) (hx : Zonotope.IsZonotopePoint A x)
    (hwidth : 0 ≤ width)
    (hA : ∀ a ∈ A, ∀ i, |(a i : ℝ)| ≤ width) :
    ∃ B : Finset (Fin d → ℤ), B ⊆ A ∧ ∀ i,
      |x i - ∑ a ∈ B, (a i : ℝ)| ≤
        Real.sqrt (((d * A.card : ℕ) : ℝ)) * width :=
  Zonotope.zonotope_rounding A x width hx hwidth hA

/-- **Pham--Zakharov intersection theorem, exact post-CFP form.**

The two independently rounded CFP regions share a nonzero lattice point.
The conclusion is the literal pair of nonempty disjoint subsets with equal
deviation sums (equation (11) of the paper).
-/
theorem theorem4_intersection_of_postCFP {d R : ℕ} (hd : 0 < d)
    {A₁ A₂ : Finset (LatticePoint d)} {a : LatticePoint d}
    {center : Fin d → ℝ}
    (hdisjoint : Disjoint A₁ A₂)
    (S₁ : IntersectionSide A₁ a .forward center (3 * R + 2))
    (S₂ : IntersectionSide A₂ a .reverse center (3 * R + 2))
    (hcover : HasCommonCoveringRadius S₁.lattice S₂.lattice R) :
    ∃ z : LatticePoint d, ∃ T₁ T₂ : Finset (LatticePoint d),
      z ≠ 0 ∧ T₁.Nonempty ∧ T₂.Nonempty ∧
      T₁ ⊆ A₁ ∧ T₂ ⊆ A₂ ∧ Disjoint T₁ T₂ ∧
      (∑ x ∈ T₁, (x - a)) = z ∧
      (∑ x ∈ T₂, (a - x)) = z := by
  obtain ⟨z, hzL₁, hzL₂, hzne, hzcube⟩ :=
    exists_nonzero_common_point_memCube hd hcover center
  have hzTarget₁ : z ∈ S₁.target := S₁.cube_subset_target z hzL₁ hzcube
  have hzTarget₂ : z ∈ S₂.target := S₂.cube_subset_target z hzL₂ hzcube
  have hzSum₁ := S₁.target_subset_subsetSums hzTarget₁
  have hzSum₂ := S₂.target_subset_subsetSums hzTarget₂
  change z ∈ GAP.subsetSums (A₁.image fun x ↦ x - a) at hzSum₁
  change z ∈ GAP.subsetSums (A₂.image fun x ↦ a - x) at hzSum₂
  obtain ⟨T₁, T₂, hT₁ne, hT₂ne, hT₁, hT₂, hTdisjoint,
    hsum₁, hsum₂⟩ :=
    PZ.common_subsetSums_deviations_gives_witness hdisjoint hzne hzSum₁ hzSum₂
  exact ⟨z, T₁, T₂, hzne, hT₁ne, hT₂ne, hT₁, hT₂,
    hTdisjoint, hsum₁, hsum₂⟩

/-- A direct contradiction form of `theorem4_intersection_of_postCFP`.
Thus, once irreducibility, Lemma 14 and the lattice-covolume bound construct
the two side records, failure of convex position is incompatible with
nonaveraging. -/
theorem not_nonaveraging_of_postCFP {d R : ℕ} (hd : 0 < d)
    {A A₁ A₂ : Finset (LatticePoint d)} {a : LatticePoint d}
    {center : Fin d → ℝ}
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (S₁ : IntersectionSide A₁ a .forward center (3 * R + 2))
    (S₂ : IntersectionSide A₂ a .reverse center (3 * R + 2))
    (hcover : HasCommonCoveringRadius S₁.lattice S₂.lattice R) :
    ¬ IsBoxNonaveraging A := by
  obtain ⟨z, T₁, T₂, hz, _hT₁ne, _hT₂ne, hT₁, hT₂,
    hTdisjoint, hsum₁, hsum₂⟩ :=
    theorem4_intersection_of_postCFP hd hdisjoint S₁ S₂ hcover
  apply PZ.averaging_witness_of_common_deviation_sum ha
    (hT₁.trans hA₁) (hT₂.trans hA₂) hTdisjoint hz hsum₁ hsum₂

/-! ## Composition with failure of `mu`-convex position -/

/-- All concrete objects which the post-CFP part of Theorem 4 constructs
from the capped convex combination.  No common point or subset-sum witness
is a field of this record. -/
structure Theorem4PostCFPData {d : ℕ} (A : Finset (LatticePoint d)) where
  dimension_pos : 0 < d
  a : LatticePoint d
  a_mem : a ∈ A
  A₁ : Finset (LatticePoint d)
  A₂ : Finset (LatticePoint d)
  A₁_subset : A₁ ⊆ A.erase a
  A₂_subset : A₂ ⊆ A.erase a
  disjoint : Disjoint A₁ A₂
  coveringRadius : ℕ
  center : Fin d → ℝ
  side₁ : IntersectionSide A₁ a .forward center (3 * coveringRadius + 2)
  side₂ : IntersectionSide A₂ a .reverse center (3 * coveringRadius + 2)
  commonCoveringRadius :
    HasCommonCoveringRadius side₁.lattice side₂.lattice coveringRadius

/-- The exact remaining output of the full-rank lattice/covolume estimate:
the intersection of the two progression lattices has the asserted integral
covering radius.  `Lattice.lean` proves that this output gives a nonzero
common point; the determinant-to-covering-radius implication itself is the
source lemma still absent from the repository. -/
def FullRankLatticeCovolumeConclusion {d : ℕ}
    {A₁ A₂ : Finset (LatticePoint d)} {a : LatticePoint d}
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse) (R : ℕ) : Prop :=
  HasCommonCoveringRadius I₁.lattice I₂.lattice R

namespace Theorem4PostCFPData

variable {d : ℕ} {A : Finset (LatticePoint d)}

/-- Assemble the post-CFP data from the three separately named source
outputs: residual absorption on each side, target thickness on each side,
and the common covering-radius consequence of the full-rank covolume bound.
No intersection point or averaging witness is an input. -/
def ofSourceLemmas {R : ℕ} {a : LatticePoint d}
    {A₁ A₂ : Finset (LatticePoint d)} {center : Fin d → ℝ}
    (hd : 0 < d) (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (hround₁ : I₁.Lemma13ResidualAbsorption)
    (hround₂ : I₂.Lemma13ResidualAbsorption)
    (hthick₁ : I₁.Lemma14TargetThickness center (3 * R + 2))
    (hthick₂ : I₂.Lemma14TargetThickness center (3 * R + 2))
    (hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R) :
    Theorem4PostCFPData A where
  dimension_pos := hd
  a := a
  a_mem := ha
  A₁ := A₁
  A₂ := A₂
  A₁_subset := hA₁
  A₂_subset := hA₂
  disjoint := hdisjoint
  coveringRadius := R
  center := center
  side₁ := I₁.toIntersectionSide hround₁ hthick₁
  side₂ := I₂.toIntersectionSide hround₂ hthick₂
  commonCoveringRadius := hcovolume

/-- The data record constructs the literal intersection witness. -/
theorem exists_intersection_witness (D : Theorem4PostCFPData A) :
    ∃ z : LatticePoint d, ∃ T₁ T₂ : Finset (LatticePoint d),
      z ≠ 0 ∧ T₁.Nonempty ∧ T₂.Nonempty ∧
      T₁ ⊆ D.A₁ ∧ T₂ ⊆ D.A₂ ∧ Disjoint T₁ T₂ ∧
      (∑ x ∈ T₁, (x - D.a)) = z ∧
      (∑ x ∈ T₂, (D.a - x)) = z := by
  exact theorem4_intersection_of_postCFP D.dimension_pos D.disjoint
    D.side₁ D.side₂ D.commonCoveringRadius

/-- Hence the ambient set is not nonaveraging. -/
theorem not_nonaveraging (D : Theorem4PostCFPData A) :
    ¬ IsBoxNonaveraging A := by
  exact not_nonaveraging_of_postCFP D.dimension_pos D.a_mem
    D.A₁_subset D.A₂_subset D.disjoint D.side₁ D.side₂
    D.commonCoveringRadius

/-- **Theorem 4 from the explicit remaining source lemmas.**  The hypotheses
are exactly the two residual-absorption statements, the two target-thickness
statements, and the common-lattice covering conclusion.  The common nonzero
subset sum and the forbidden average are derived conclusions. -/
theorem not_nonaveraging_of_source_lemmas {R : ℕ} {a : LatticePoint d}
    {A₁ A₂ : Finset (LatticePoint d)} {center : Fin d → ℝ}
    (hd : 0 < d) (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (hround₁ : I₁.Lemma13ResidualAbsorption)
    (hround₂ : I₂.Lemma13ResidualAbsorption)
    (hthick₁ : I₁.Lemma14TargetThickness center (3 * R + 2))
    (hthick₂ : I₂.Lemma14TargetThickness center (3 * R + 2))
    (hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R) :
    ¬ IsBoxNonaveraging A := by
  exact (ofSourceLemmas hd ha hA₁ hA₂ hdisjoint I₁ I₂ hround₁ hround₂
    hthick₁ hthick₂ hcovolume).not_nonaveraging

end Theorem4PostCFPData

/-- Explicit finite parameter regime in the statement of Pham--Zakharov
Theorem 4.  The constants `C`, `C'` depend on the fixed ambient dimension
and `beta`; the cardinality threshold `M` may additionally depend on the
chosen uniform CFP context. -/
structure Theorem4Parameters {d : ℕ} (A : Finset (LatticePoint d))
    (beta C C' : ℝ) (M : ℕ) (delta gamma mu : ℝ) where
  beta_gt_one : 1 < beta
  C_pos : 0 < C
  C'_pos : 0 < C'
  delta_pos : 0 < delta
  gamma_pos : 0 < gamma
  mu_pos : 0 < mu
  delta_lt_one : delta < 1
  gamma_lt_one : gamma < 1
  mu_lt_one : mu < 1
  gamma_le_delta : gamma ≤ delta ^ C
  delta_le_mu : delta ≤ mu ^ C
  gamma_log_lower :
    (Real.log (A.card : ℝ)) ^ (-(1 / C')) ≤ gamma
  card_large : M ≤ A.card

/-- The precise remaining construction statement between irreducibility
and the already formalized post-CFP argument.  The intersection is carried
out on the selected core in its canonical coefficient lattice, whose ambient
dimension is the selected subset-sum dimension.  The original `A` remains
the population used by the density threshold.  Candidate-domain closure is
explicit, so bounded irreducibility cannot hold merely because all shifted
inputs were declared ineligible.  The explicit core-retention inequality is
the terminal reduction estimate that makes both balanced pools dense enough
for Definition 9. -/
def ProducesTheorem4PostCFPData
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (_hd : 0 < d) (rankCeiling : ℕ)
    (_hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
    {C C' : ℝ} {M : ℕ}
    (delta gamma mu : ℝ)
    (_hparams : Theorem4Parameters A beta C C' M delta gamma mu)
    (_hclosed : selector.CandidateClosedAt A hA delta)
    (_hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) :
    Prop :=
  let S := selector.chosen A hA
  Reduction.IsBoundedCoordinateIrreducible selector A hA delta gamma →
    ∀ (a₀ : realImage S.identifiedCore)
      (c : realImage S.identifiedCore → ℝ),
      (∀ x, 0 ≤ c x ∧
        c x ≤ (mu * S.identifiedCore.card)⁻¹) →
      (∑ x, c x) = 1 →
      (∑ x, c x •
        ((x : EuclideanSpace ℝ (Fin S.dimension)) - a₀)) = 0 →
      ∃ D : Theorem4PostCFPData S.identifiedCore,
        latticeEuclidean D.a =
          (a₀ : EuclideanSpace ℝ (Fin S.dimension))

/-- Stable all-input boundary for the source-dependent post-CFP construction
in Theorem 4.  The exponents `C`, `C'` are chosen from the ambient dimension
and `beta`.  The population threshold is chosen only after the concrete CFP
context, since it must dominate that context's scale denominators and loss
constants.  A local `CandidateClosedAt` proof accompanies irreducibility,
exactly as in the terminal output of the bounded reduction. -/
def Theorem4PostCFPStatement : Prop :=
  ∀ d rankCeiling : ℕ, (hd : 0 < d) →
    ∀ beta eta : ℝ, 1 < beta → 0 < eta → eta < 1 →
    ∃ C C' : ℝ,
      0 < C ∧ 0 < C' ∧
      ∀ (context : Reduction.HigherDimensionalContext beta eta),
      ∃ M : ℕ,
      ∀
        (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint d)) (hA : selector.Eligible A)
        (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
        (delta gamma mu : ℝ)
        (hparams : Theorem4Parameters A beta C C' M delta gamma mu),
        (hclosed : selector.CandidateClosedAt A hA delta) →
        (hcoreRetention : delta * (A.card : ℝ) ≤
          ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) →
        ProducesTheorem4PostCFPData selector A hA hd rankCeiling hrank
          delta gamma mu hparams hclosed hcoreRetention

/-- **Theorem 4, composed form.**  Failure of `mu`-convex position gives the
capped combination, and a source-faithful post-CFP construction from the
irreducibility hypothesis gives the two side records.  The proved finite
intersection pipeline then contradicts nonaveraging. -/
theorem theorem4_of_irreducible_of_not_isDeltaConvexPosition
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d rankCeiling : ℕ}
    {A : Finset (LatticePoint d)} (hA : selector.Eligible A)
    (hd : 0 < d)
    (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
    {C C' : ℝ} {M : ℕ} {delta gamma mu : ℝ}
    (hparams : Theorem4Parameters A beta C C' M delta gamma mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
    (hpost : ProducesTheorem4PostCFPData selector A hA hd rankCeiling hrank
      delta gamma mu hparams hclosed hcoreRetention)
    (hfail : ¬ ConvexGeometry.IsDeltaConvexPosition mu
      (realImage (selector.chosen A hA).identifiedCore)) :
    ¬ IsBoxNonaveraging A := by
  obtain ⟨a₀, c, hc, hsum, hcenter⟩ :=
    ConvexCombination.exists_capped_centered_combination_of_not_isDeltaConvexPosition
      hparams.mu_pos hfail
  have hc' : ∀ x, 0 ≤ c x ∧
      c x ≤ (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ := by
    simpa only [card_realImage] using hc
  obtain ⟨D, _hDa⟩ := hpost hirr a₀ c hc' hsum hcenter
  intro hNA
  exact D.not_nonaveraging
    ((selector.chosen A hA).identifiedCore_nonaveraging hNA)

end

end Erdos186.PZ.Intersection
