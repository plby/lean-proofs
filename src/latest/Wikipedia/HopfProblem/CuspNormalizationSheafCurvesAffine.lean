import Wikipedia.HopfProblem.CuspNormalizationBranches
import Wikipedia.HopfProblem.CuspRationalCurves

/-!
# The two affine lifts of a double-curve axis

An axis in a toric chart lies on the two components at the endpoints of its
edge. Translating either endpoint to the zero ray gives an actual holomorphic
map to the normalization component, with image in the corresponding signed
boundary curve. These formulas will identify the inverse boundary projections.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- Lift an axis to the selected coordinate-plane branch. -/
def affineLift (s : Triangle) (i j : Fin 3) (z : ℂ) : rayDivisor 0 :=
  branchAffine C s j (removeCoordinate j (axisPoint s i z))

theorem affineLift_holomorphic (s : Triangle) (i j : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineLift C s i j) :=
  (branchAffine_holomorphic C s j).comp
    ((removeCoordinate_holomorphic j).comp (axisPoint_holomorphic s i)).contMDiff

theorem affineLift_coe (s : Triangle) (i j : Fin 3) (hj : j ≠ s.axisIndex i) (z : ℂ) :
    (affineLift C s i j z : Space) =
      twistedTranslate C (cuspVector (s.vertex j)) (inclusion s (axisPoint s i z)) := by
  rw [affineLift, branchAffine_coe, insertZero_removeCoordinate j _
    (axisPoint_apply_of_ne s i j z hj)]

theorem componentProjection_affineLift (ε : ℝ) (hε : 0 < ε)
    (s : Triangle) (i j : Fin 3) (hj : j ≠ s.axisIndex i) (z : ℂ) :
    componentProjection C ε hε (affineLift C s i j z) = axisMap C ε hε s i z := by
  rw [affineLift, componentProjection_branchAffine, axisMap_eq_centralChartMap]
  congr 1
  apply Subtype.ext
  exact insertZero_removeCoordinate j _ (axisPoint_apply_of_ne s i j z hj)

theorem edgeStart_ne_axisIndex (s : Triangle) (i : Fin 3) :
    s.edgeStart i ≠ s.axisIndex i :=
  (axis_complement s i _).mpr (Or.inl rfl)

theorem edgeEnd_ne_axisIndex (s : Triangle) (i : Fin 3) :
    s.edgeEnd i ≠ s.axisIndex i :=
  (axis_complement s i _).mpr (Or.inr rfl)

theorem affineLift_start_mem_boundary (s : Triangle) (i : Fin 3) (z : ℂ) :
    affineLift C s i (s.edgeStart i) z ∈ componentBoundary (edgeDirection i) := by
  change (affineLift C s i (s.edgeStart i) z : Space) ∈ rayDivisor (edgeDirection i)
  rw [affineLift_coe C s i _ (edgeStart_ne_axisIndex s i),
    twistedTranslate_mem_rayDivisor, cuspVector_cuspVector]
  have he := (vertices_edge_iff s i (s.edgeStart i) (s.edgeEnd i)).mpr ⟨rfl, rfl⟩
  have hv : edgeDirection i - -s.vertex (s.edgeStart i) = s.vertex (s.edgeEnd i) := by
    rw [sub_neg_eq_add, add_comm, ← he]
  rw [hv, mem_rayDivisor_vertex]
  exact axisPoint_apply_of_ne s i _ z (edgeEnd_ne_axisIndex s i)

theorem affineLift_end_mem_boundary (s : Triangle) (i : Fin 3) (z : ℂ) :
    affineLift C s i (s.edgeEnd i) z ∈ componentBoundary (-edgeDirection i) := by
  change (affineLift C s i (s.edgeEnd i) z : Space) ∈ rayDivisor (-edgeDirection i)
  rw [affineLift_coe C s i _ (edgeEnd_ne_axisIndex s i),
    twistedTranslate_mem_rayDivisor, cuspVector_cuspVector]
  have he := (vertices_edge_iff s i (s.edgeStart i) (s.edgeEnd i)).mpr ⟨rfl, rfl⟩
  have hv : -edgeDirection i - -s.vertex (s.edgeEnd i) = s.vertex (s.edgeStart i) := by
    rw [sub_neg_eq_add, he]
    abel
  rw [hv, mem_rayDivisor_vertex]
  exact axisPoint_apply_of_ne s i _ z (edgeStart_ne_axisIndex s i)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
