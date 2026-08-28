import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusInjective
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusReduction
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverBoundary
import Wikipedia.HopfProblem.CuspCentralHomologySuspension

/-!
# The actual central double locus is the suspension of three circles

The map is the original quotient projection of compact phases over the
three chosen compatible boundary arcs. Its exact fibres collapse the two
end slices separately and nothing else. The opposite-edge translations
prove that its range is the literal central boundary. Compactness and the
Hausdorff topology of the actual cusp quotient then give a homeomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem doubleCylinder_mem_centralBoundary (p : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p ∈ centralBoundary C ε hε := by
  rcases p with ⟨t, a | (a | a)⟩
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 0 (t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 1 (unitInterval.symm t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 2 (t, a)

/-- The three actual edge cylinders cover exactly the original central boundary. -/
theorem range_doubleCylinder_eq_centralBoundary :
    Set.range (doubleCylinder C ε hε) = centralBoundary C ε hε := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact doubleCylinder_mem_centralBoundary C ε hε p
  · intro hq
    obtain ⟨k, t, u, hu⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [← hu]
    exact centralCollapseMap_edgeArc_mem_range_doubleCylinder C ε hε k t u

theorem range_doubleSuspensionMap_eq_centralBoundary :
    Set.range (doubleSuspensionMap C ε hε) = centralBoundary C ε hε := by
  rw [range_doubleSuspensionMap, range_doubleCylinder_eq_centralBoundary]

theorem doubleSuspensionMap_mem_centralBoundary (p : ThreeCircleSuspension) :
    doubleSuspensionMap C ε hε p ∈ centralBoundary C ε hε := by
  rw [← range_doubleSuspensionMap_eq_centralBoundary]
  exact mem_range_self p

/-- The suspension map with its codomain restricted to its actual geometric image. -/
def doubleSuspensionBoundaryMap (p : ThreeCircleSuspension) : centralBoundary C ε hε :=
  ⟨doubleSuspensionMap C ε hε p, doubleSuspensionMap_mem_centralBoundary C ε hε p⟩

@[simp] theorem doubleSuspensionBoundaryMap_coe (p : ThreeCircleSuspension) :
    (doubleSuspensionBoundaryMap C ε hε p : QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε p := rfl

theorem doubleSuspensionBoundaryMap_continuous :
    Continuous (doubleSuspensionBoundaryMap C ε hε) :=
  (doubleSuspensionMap_continuous C ε hε).subtype_mk _

theorem doubleSuspensionBoundaryMap_bijective :
    Function.Bijective (doubleSuspensionBoundaryMap C ε hε) := by
  constructor
  · intro p q h
    exact doubleSuspensionMap_injective C ε hε (congrArg Subtype.val h)
  · rintro ⟨q, hq⟩
    rw [← range_doubleSuspensionMap_eq_centralBoundary] at hq
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

def doubleSuspensionBoundaryEquiv : ThreeCircleSuspension ≃ centralBoundary C ε hε :=
  Equiv.ofBijective (doubleSuspensionBoundaryMap C ε hε)
    (doubleSuspensionBoundaryMap_bijective C ε hε)

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- A homeomorphism onto the literal double locus in the actual cusp quotient. -/
def doubleSuspensionBoundaryHomeomorph : ThreeCircleSuspension ≃ₜ centralBoundary C ε hε := by
  letI := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (doubleSuspensionBoundaryEquiv C ε hε).toHomeomorphOfContinuousClosed
    (doubleSuspensionBoundaryMap_continuous C ε hε)
    (doubleSuspensionBoundaryMap_continuous C ε hε).isClosedMap

@[simp] theorem doubleSuspensionBoundaryHomeomorph_coe (p : ThreeCircleSuspension) :
    (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε p := rfl

/-- The same actual identification, oriented from the geometric double locus. -/
def centralBoundarySuspensionHomeomorph : centralBoundary C ε hε ≃ₜ ThreeCircleSuspension :=
  (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR).symm

@[simp] theorem centralBoundarySuspensionHomeomorph_symm_coe (p : ThreeCircleSuspension) :
    ((centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm p :
      QuotientCentralFibre C ε) = doubleSuspensionMap C ε hε p := rfl

/-- The two suspension poles are the two genuine toric-origin orbits. -/
@[simp] theorem doubleSuspensionBoundaryHomeomorph_north_coe :
    (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR Suspension.north :
      QuotientCentralFibre C ε) = oddPole C ε hε :=
  doubleSuspensionMap_north C ε hε

@[simp] theorem doubleSuspensionBoundaryHomeomorph_south_coe :
    (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR Suspension.south :
      QuotientCentralFibre C ε) = evenPole C ε hε :=
  doubleSuspensionMap_south C ε hε

end Wikipedia.HopfProblem.CuspCentralHomology
