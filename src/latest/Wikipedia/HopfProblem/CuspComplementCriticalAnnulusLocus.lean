import Wikipedia.HopfProblem.CuspComplementCap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspCritical
import Wikipedia.HopfProblem.ThreefoldCircleActionSemifree

/-!
# The genuine critical locus left in the actual cusp complement

The original central fibre lies inside the chosen cap.  Removing the
interior of the already fixed normal neighborhood removes the fixed
double curve and both triple points.  The remaining ambient critical
locus is exactly the disjoint union of the other two carved double
curves; every remaining critical point has two branches.  The unchanged
global circle action is free on the entire complement.

No annulus parametrization, boundary tangency condition, or criticality
statement for a map restricted to the boundary is assumed or asserted.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold Homology

/-- The entire literal fibre at the original sphere infinity lies in
the strict cusp cap, by its unchanged zero parameter. -/
theorem sphereCuspFibre_subset_openCap :
    CuspGeometry.sphereCuspFibre ⊆ (openCap : Set Threefold.Space) := by
  rw [CuspGeometry.sphereCuspFibre_eq_image]
  rintro x ⟨q, hq, rfl⟩
  refine ⟨q, ?_, rfl⟩
  change ‖CuspGeometry.parameter q‖ < capRadius
  rw [(CuspGeometry.mem_localCentralFibre q).mp hq, norm_zero]
  exact capRadius_pos

theorem doubleCurve_subset_openCap (i : Fin 3) :
    CuspGeometry.doubleCurve i ⊆ (openCap : Set Threefold.Space) :=
  (CuspGeometry.doubleCurve_subset_sphereCuspFibre i).trans sphereCuspFibre_subset_openCap

theorem doubleCurve_subset_cap (i : Fin 3) : CuspGeometry.doubleCurve i ⊆ cap :=
  (doubleCurve_subset_openCap i).trans openCap_subset_cap

/-- Neither native triple point survives anywhere in the actual complement. -/
theorem capComplement_not_mem_tripleStratum {x : Threefold.Space}
    (hx : x ∈ capComplement) : x ∉ CuspGeometry.tripleStratum :=
  fun ht => capComplement_not_mem_doubleCurve hx
    (CuspGeometry.tripleStratum_subset_doubleCurve 1 ht)

/-- This is the restriction of the original ambient critical locus,
not the critical locus of a boundary-restricted map. -/
theorem cuspCriticalLocus_inter_capComplement :
    CuspGeometry.cuspCriticalLocus ∩ capComplement =
      (CuspGeometry.doubleCurve 0 \ interior closedDiskNeighborhood) ∪
        (CuspGeometry.doubleCurve 2 \ interior closedDiskNeighborhood) := by
  rw [CuspGeometry.cuspCriticalLocus_eq_doubleCurves]
  ext x
  constructor
  · rintro ⟨hc, hcomp⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    fin_cases i
    · exact Or.inl ⟨hi, hcomp.2⟩
    · exact (capComplement_not_mem_doubleCurve hcomp hi).elim
    · exact Or.inr ⟨hi, hcomp.2⟩
  · rintro (⟨h0, hN⟩ | ⟨h2, hN⟩)
    · exact ⟨mem_iUnion.mpr ⟨0, h0⟩, doubleCurve_subset_cap 0 h0, hN⟩
    · exact ⟨mem_iUnion.mpr ⟨2, h2⟩, doubleCurve_subset_cap 2 h2, hN⟩

/-- The two surviving critical pieces are disjoint because their
original intersection lies in the removed neighborhood's interior. -/
theorem remainingCriticalPieces_disjoint :
    Disjoint (CuspGeometry.doubleCurve 0 \ interior closedDiskNeighborhood)
      (CuspGeometry.doubleCurve 2 \ interior closedDiskNeighborhood) := by
  apply Set.disjoint_left.mpr
  rintro x h0 h2
  have ht : x ∈ CuspGeometry.tripleStratum := by
    rw [← CuspGeometry.doubleCurve_inter_eq_tripleStratum 0 2 (by decide)]
    exact ⟨h0.1, h2.1⟩
  exact h0.2 (doubleCurve_subset_interior_closedDiskNeighborhood
    (CuspGeometry.tripleStratum_subset_doubleCurve 1 ht))

/-- Every remaining actual critical point has exactly two native
branches, using the intrinsic branch count on the original cusp fibre. -/
theorem remainingCritical_fibreBranchCount_eq_two (x : CuspGeometry.sphereCuspFibre)
    (hx : (x : Threefold.Space) ∈ CuspGeometry.cuspCriticalLocus ∩ capComplement) :
    CuspGeometry.fibreBranchCount x = 2 := by
  have hd : (x : Threefold.Space) ∈ CuspGeometry.doubleStratum := by
    rw [← CuspGeometry.cuspCriticalLocus_eq_doubleStratum]
    exact hx.1
  have htwo := (CuspGeometry.mem_doubleStratum_iff x).mp hd
  have hthree := CuspGeometry.fibreBranchCount_le_three x
  have hn : CuspGeometry.fibreBranchCount x ≠ 3 := fun h =>
    capComplement_not_mem_tripleStratum hx.2 ((CuspGeometry.mem_tripleStratum_iff x).mpr h)
  omega

/-- Every point of the actual complement, in particular each remaining
critical point, has trivial stabilizer for the original period-one circle. -/
theorem capComplement_actionMap_eq_self_iff {x : Threefold.Space}
    (hx : x ∈ capComplement) (t : AddCircle (1 : ℝ)) :
    DeltaSweep.actionMap (t, x) = x ↔ t = 0 :=
  CircleActionSemifree.actionMap_eq_self_iff x (capComplement_not_mem_doubleCurve hx) t

end Wikipedia.HopfProblem.CuspComplement
