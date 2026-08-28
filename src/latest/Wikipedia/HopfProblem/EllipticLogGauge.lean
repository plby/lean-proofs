import Wikipedia.HopfProblem.EllipticLogGaugeSource
import Wikipedia.HopfProblem.EllipticLogGaugeQuotients
import Wikipedia.HopfProblem.EllipticEquivariantConcrete

/-!
# The logarithmic filling agrees with the tautological family off the centre

The logarithmic period section gives a genuine biholomorphism from the
complement of the central fibre to the untwisted punctured quotient.  The
quotient and open-subspace atlases are the original analytic atlases, and
the identification preserves the powered base coordinate.

The construction applies to every supplied covariant holomorphic period
map.  Its specialization to the two explicit families uses the checked
equality of the generic and original filling atlases.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

variable {j : Kind} (D : Equivariant.Data j)

/-- The untwisted action used in the tautological quotient is exactly
the source's linear monodromy on the complex covering coordinates. -/
theorem untwisted_complexLift (z : Disc) (u : ComplexPlane₂) :
    D.complexLift 0 (z, u) =
      (familyRotation j z, linearMatrix j (D.periods.point z) *ᵥ u) := by
  rw [complexLift_formula, periodVector_zero, smul_zero, add_zero]

/-- The logarithmic translation is an actual holomorphic conjugacy,
not a prescribed equivalence of the underlying sets. -/
theorem holomorphic_gauge_conjugacy (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.periods.totalChartedSpace
    ∃ h : Diffeomorph IF IF (FamilyStar D.periods) (FamilyStar D.periods) ω,
      h.toEquiv * starPermutation D v * h.toEquiv⁻¹ = starPermutation D 0 :=
  ⟨gaugeBiholomorph D.periods v, gaugeEquiv_conjugates D v hv⟩

/-- Theorem 5.4(iv), for any covariant admissible period family: the
literal complement of the central fibre is biholomorphic over the
powered punctured base to the actual untwisted punctured quotient. -/
theorem punctured_filling_identification (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    ∃ e : Diffeomorph IF IF (FillingStar D v hv) (TautologicalStar D) ω,
      ∀ x, starProjection D 0 (Matrix.mulVec_zero j.matrix) (e x) =
        fillingStarProjection D v hv x :=
  ⟨fillingToTautologicalBiholomorph D v hv,
    fillingToTautologicalBiholomorph_base D v hv⟩

/-- The source's specified twists satisfy all the required arithmetic
conditions, so no freeness or admissibility hypothesis remains. -/
def mainFillingToTautologicalBiholomorph :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph IF IF (FillingStar D j.twist (mainTwist_admissible j))
      (TautologicalStar D) ω :=
  fillingToTautologicalBiholomorph D j.twist (mainTwist_admissible j)

theorem mainFillingToTautologicalBiholomorph_base
    (x : FillingStar D j.twist (mainTwist_admissible j)) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (mainFillingToTautologicalBiholomorph D x) =
      fillingStarProjection D j.twist (mainTwist_admissible j) x :=
  fillingToTautologicalBiholomorph_base D j.twist (mainTwist_admissible j) x

/-- The literal open complement of the central fibre in the original
concrete filling. -/
def concreteFillingOpen (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    TopologicalSpace.Opens (Filling j v hv) :=
  ⟨{x | (fillingProjection j v hv x : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp (fillingProjection_proper j v hv).continuous)
      continuous_const⟩

abbrev ConcreteFillingStar (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :=
  concreteFillingOpen j v hv

/-- Specialization to the original elliptic filling.  The source has
its inherited original atlas; the agreement with the generic atlas is
definitional and has also been checked explicitly in
`Equivariant.concrete_chartedSpace_eq`. -/
def concreteFillingToTautologicalBiholomorph (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := starChartedSpace (Equivariant.concrete j) 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph IF IF (ConcreteFillingStar j v hv)
      (TautologicalStar (Equivariant.concrete j)) ω :=
  fillingToTautologicalBiholomorph (Equivariant.concrete j) v hv

theorem concreteFillingToTautologicalBiholomorph_base (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : ConcreteFillingStar j v hv) :
    (starProjection (Equivariant.concrete j) 0 (Matrix.mulVec_zero j.matrix)
      (concreteFillingToTautologicalBiholomorph j v hv x) : Disc) =
        fillingProjection j v hv x :=
  fillingToTautologicalBiholomorph_base_coe (Equivariant.concrete j) v hv x

/-- An unconditional punctured-filling biholomorphism for each of the
two specified local constructions. -/
def concreteMainFillingToTautologicalBiholomorph (j : Kind) :
    letI := starChartedSpace (Equivariant.concrete j) 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph IF IF (ConcreteFillingStar j j.twist (mainTwist_admissible j))
      (TautologicalStar (Equivariant.concrete j)) ω :=
  concreteFillingToTautologicalBiholomorph j j.twist (mainTwist_admissible j)

end Wikipedia.HopfProblem.Elliptic.LogGauge
