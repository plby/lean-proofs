import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateCompactification
import Wikipedia.SmoothSixDPoincare.SeparatedDegreeMaps
import Wikipedia.SmoothSixDPoincare.OnePointCollapseCover

/-! # The constructed separated cover of the actual twelve-point fiber -/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open Wikipedia.SmoothSixDPoincare

local notation "Coordinates" => EuclideanSpace ℝ (Fin 7)
local notation "Parameters" => ParameterSpace rotatedInput

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def candidateNeighborhoods : LocalDegree.SeparatedNeighborhoods Coordinates
    sphereCandidateTargetPreimage normalizedCandidateCoordinates candidateTargetDomain :=
  Classical.choice (LocalDegree.nonempty_separatedNeighborhoods Coordinates
    sphereCandidateTargetPreimage_finite contMDiffAt_normalizedCandidateCoordinates_target
    normalizedCandidateCoordinates_target_zero isInvertible_normalizedCandidateCoordinates_target
    (fun x hx ↦ isOpen_candidateTargetDomain.mem_nhds (target_mem_candidateTargetDomain x hx)))

theorem candidateNeighborhoods_open_cover :
    sphereCandidateTargetPreimageᶜ ∪
      (⋃ x : sphereCandidateTargetPreimage, candidateNeighborhoods.neighborhood x) = univ :=
  candidateNeighborhoods.open_cover

theorem compactifiedCandidate_maps_old :
    MapsTo compactifiedCandidate sphereCandidateTargetPreimageᶜ (OnePointCover.oldPatch) := by
  intro x hx
  change compactifiedCandidate x ≠ ((0 : Parameters) : OnePoint Parameters)
  exact fun h ↦ hx ((compactifiedCandidate_zero_iff x).mp h)

theorem compactifiedCandidate_maps_domain :
    MapsTo compactifiedCandidate candidateTargetDomain OnePointCover.finitePatch := by
  intro x hx
  change compactifiedCandidate x ≠ OnePoint.infty
  rw [compactifiedCandidate_eq_coe x hx]
  exact OnePoint.coe_ne_infty _

theorem compactifiedCandidate_maps_neighborhood (x : sphereCandidateTargetPreimage) :
    MapsTo compactifiedCandidate (candidateNeighborhoods.neighborhood x)
      OnePointCover.finitePatch :=
  fun _ hy ↦ compactifiedCandidate_maps_domain (candidateNeighborhoods.neighborhood_subset x hy)

theorem normalizedCandidateCoordinates_zero_iff_on_domain (x : Sphere 7)
    (hx : x ∈ candidateTargetDomain) :
    normalizedCandidateCoordinates x = 0 ↔ x ∈ sphereCandidateTargetPreimage := by
  rw [← compactifiedCandidate_zero_iff, compactifiedCandidate_eq_coe x hx]
  exact OnePoint.coe_injective.eq_iff.symm

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
