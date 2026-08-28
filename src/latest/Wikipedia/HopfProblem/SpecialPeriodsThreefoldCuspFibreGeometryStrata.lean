import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometry
import Wikipedia.HopfProblem.CuspDoubleCurves
import Wikipedia.HopfProblem.CuspStrata

/-!
# The double curves and triple points in the actual glued cusp fibre

The three double curves and two triple points are the literal images of
the native cusp strata under its proved open embedding into the constructed
threefold. Compactness, distinctness, all pairwise intersections, and the
branch-count descriptions follow from the corresponding native results.
No projective-line parametrization or singular analytic-space structure
is asserted here.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

attribute [local instance] Threefold.space_t2Space

/-- The three actual double-curve subsets in the glued threefold. -/
def doubleCurve (i : Fin 3) : Set Threefold.Space :=
  inclusion '' CuspQuotient.doubleCurve data.correction data.radius data.radius_pos i

/-- The lower native triple point, as an actual point of the glued space. -/
def lowerTriplePoint : Threefold.Space :=
  inclusion (CuspQuotient.lowerTriplePoint data.correction data.radius data.radius_pos)

/-- The upper native triple point, as an actual point of the glued space. -/
def upperTriplePoint : Threefold.Space :=
  inclusion (CuspQuotient.upperTriplePoint data.correction data.radius data.radius_pos)

/-- The actual image of the three-branch stratum. -/
def tripleStratum : Set Threefold.Space :=
  inclusion '' {x : LocalSpace | CuspQuotient.branchCount data.correction data.radius x = 3}

/-- The actual image of the locus having at least two branches. -/
def doubleStratum : Set Threefold.Space :=
  inclusion '' {x : LocalSpace | 2 ≤ CuspQuotient.branchCount data.correction data.radius x}

theorem lowerTriplePoint_mem_doubleCurve (i : Fin 3) : lowerTriplePoint ∈ doubleCurve i :=
  ⟨_, CuspQuotient.lowerTriplePoint_mem_doubleCurve
    data.correction data.radius data.radius_pos i, rfl⟩

theorem upperTriplePoint_mem_doubleCurve (i : Fin 3) : upperTriplePoint ∈ doubleCurve i :=
  ⟨_, CuspQuotient.upperTriplePoint_mem_doubleCurve
    data.correction data.radius data.radius_pos i, rfl⟩

/-- Each imaged curve lies in the literal sphere fibre at infinity. -/
theorem doubleCurve_subset_sphereCuspFibre (i : Fin 3) :
    doubleCurve i ⊆ sphereCuspFibre := by
  rw [doubleCurve, sphereCuspFibre_eq_image]
  exact Set.image_mono
    (CuspQuotient.doubleCurve_subset_central data.correction data.radius data.radius_pos i)

theorem lowerTriplePoint_mem_sphereCuspFibre : lowerTriplePoint ∈ sphereCuspFibre :=
  doubleCurve_subset_sphereCuspFibre 0 (lowerTriplePoint_mem_doubleCurve 0)

theorem upperTriplePoint_mem_sphereCuspFibre : upperTriplePoint ∈ sphereCuspFibre :=
  doubleCurve_subset_sphereCuspFibre 0 (upperTriplePoint_mem_doubleCurve 0)

/-- The curves remain compact in the ambient glued threefold. -/
theorem doubleCurve_compact (i : Fin 3) : IsCompact (doubleCurve i) :=
  (CuspQuotient.doubleCurve_compact data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift i).image inclusion_continuous

theorem doubleCurve_isClosed (i : Fin 3) : IsClosed (doubleCurve i) :=
  (doubleCurve_compact i).isClosed

/-- None of the three native curve loci becomes identified under gluing. -/
theorem doubleCurves_injective : Function.Injective doubleCurve :=
  inclusion_injective.image_injective.comp
    (CuspQuotient.doubleCurves_injective data.correction data.radius data.radius_pos)

/-- There are exactly three distinct curve subsets in the ambient space. -/
theorem doubleCurves_card : (Set.range doubleCurve).ncard = 3 := by
  rw [Set.ncard_range_of_injective doubleCurves_injective]
  simp

theorem triplePoints_distinct : lowerTriplePoint ≠ upperTriplePoint :=
  fun h => CuspQuotient.triplePoints_distinct data.correction data.radius data.radius_pos
    (inclusion_injective h)

/-- The entire actual three-branch stratum is the displayed pair. -/
theorem tripleStratum_eq_pair : tripleStratum = {lowerTriplePoint, upperTriplePoint} := by
  let e : CuspQuotient.QuotientSpace data.correction data.radius → Threefold.Space := inclusion
  exact (congrArg (Set.image e)
    (CuspQuotient.tripleStratum_eq data.correction data.radius data.radius_pos)).trans
      (Set.image_pair e _ _)

theorem tripleStratum_card : tripleStratum.ncard = 2 := by
  rw [tripleStratum_eq_pair]
  exact Set.ncard_pair triplePoints_distinct

theorem tripleStratum_compact : IsCompact tripleStratum := by
  rw [tripleStratum_eq_pair]
  exact (isCompact_singleton : IsCompact ({upperTriplePoint} : Set Threefold.Space)).insert _

theorem tripleStratum_isClosed : IsClosed tripleStratum := tripleStratum_compact.isClosed

/-- Every two distinct double curves meet at exactly the two triple points. -/
theorem doubleCurve_inter_eq_pair (i j : Fin 3) (hij : i ≠ j) :
    doubleCurve i ∩ doubleCurve j = {lowerTriplePoint, upperTriplePoint} := by
  let e : CuspQuotient.QuotientSpace data.correction data.radius → Threefold.Space := inclusion
  have he : Function.Injective e := inclusion_injective
  exact (Set.image_inter he).symm.trans ((congrArg (Set.image e)
    (CuspQuotient.doubleCurve_inter_eq_pair data.correction data.radius data.radius_pos
      i j hij)).trans (Set.image_pair e _ _))

theorem doubleCurve_inter_eq_tripleStratum (i j : Fin 3) (hij : i ≠ j) :
    doubleCurve i ∩ doubleCurve j = tripleStratum := by
  rw [doubleCurve_inter_eq_pair i j hij, tripleStratum_eq_pair]

theorem doubleCurve_inter_card (i j : Fin 3) (hij : i ≠ j) :
    (doubleCurve i ∩ doubleCurve j).ncard = 2 := by
  rw [doubleCurve_inter_eq_tripleStratum i j hij]
  exact tripleStratum_card

/-- The entire multiple-branch locus is the union of the three actual curves. -/
theorem doubleStratum_eq_union : doubleStratum = ⋃ i : Fin 3, doubleCurve i := by
  let e : CuspQuotient.QuotientSpace data.correction data.radius → Threefold.Space := inclusion
  exact (congrArg (Set.image e)
    (CuspQuotient.double_locus_eq_union data.correction data.radius data.radius_pos)).trans
      Set.image_iUnion

theorem doubleStratum_compact : IsCompact doubleStratum := by
  rw [doubleStratum_eq_union]
  exact isCompact_iUnion doubleCurve_compact

theorem doubleStratum_isClosed : IsClosed doubleStratum := doubleStratum_compact.isClosed

theorem doubleStratum_subset_sphereCuspFibre : doubleStratum ⊆ sphereCuspFibre := by
  rw [doubleStratum_eq_union]
  exact iUnion_subset doubleCurve_subset_sphereCuspFibre

theorem tripleStratum_subset_doubleCurve (i : Fin 3) : tripleStratum ⊆ doubleCurve i := by
  rw [tripleStratum_eq_pair]
  rintro x (rfl | rfl)
  · exact lowerTriplePoint_mem_doubleCurve i
  · exact upperTriplePoint_mem_doubleCurve i

theorem tripleStratum_subset_sphereCuspFibre : tripleStratum ⊆ sphereCuspFibre :=
  (tripleStratum_subset_doubleCurve 0).trans (doubleCurve_subset_sphereCuspFibre 0)

/-- Intrinsic fibre branch count detects the actual global triple stratum. -/
theorem mem_tripleStratum_iff (x : sphereCuspFibre) :
    (x : Threefold.Space) ∈ tripleStratum ↔ fibreBranchCount x = 3 :=
  mem_image_branchCount_iff (fun n => n = 3) x

/-- Intrinsic fibre branch count detects the actual global double stratum. -/
theorem mem_doubleStratum_iff (x : sphereCuspFibre) :
    (x : Threefold.Space) ∈ doubleStratum ↔ 2 ≤ fibreBranchCount x :=
  mem_image_branchCount_iff (fun n => 2 ≤ n) x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
