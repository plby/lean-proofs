/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos989.GlobalSelection

/-!
# Fixed-radius upper construction for Erdős problem 989

Beck's upper theorem has fixed-scale quantifiers: for each sufficiently large radius one may
choose a new infinite discrete set, while the implied constant is independent of the radius.
This file gives the exact bridge from a finite-family jittered-discrepancy theorem at one radius
to an admissible planar point set with the required bound at that radius.

The finite-family hypothesis below is the substantive probabilistic-discrepancy input.  It is
kept visible rather than being replaced by an unproved global selection principle.
-/

open Set

namespace Erdos989
namespace FixedRadiusUpper

open GlobalSelection

/-- The exact finite-family statement needed at one fixed radius.  The finite alphabet and its
offset grid may depend on the radius. -/
def HasFiniteJitteredCertificateAtRadius (radius allowance : ℝ) : Prop :=
  ∃ n : ℕ, ∃ offset : Fin n → ℝ × ℝ,
    ∃ support : Plane → Finset PlaneCell,
    OffsetsInHalfOpenUnitSquare offset ∧
    (∀ center, CoversClosedBall (latticeLocation offset) center radius (support center)) ∧
    ∀ s : Finset Plane, ∃ x : JitteredSelection (Fin n),
      ∀ center ∈ s,
        |(localDiskCount
              (support center)
              (latticeLocation offset) center radius (fun i ↦ x i) : ℝ) -
            Real.pi * radius ^ 2| ≤ allowance

/-- The range of a parametrized point selection intersects a set in the image of its preimage. -/
theorem range_inter_eq_image_preimage {Cell : Type*} (z : Cell → Plane) (K : Set Plane) :
    range z ∩ K = z '' {cell | z cell ∈ K} := by
  ext p
  constructor
  · rintro ⟨⟨cell, rfl⟩, hK⟩
    exact ⟨cell, hK, rfl⟩
  · rintro ⟨cell, hK, rfl⟩
    exact ⟨⟨cell, rfl⟩, hK⟩

/-- A finite jittered certificate at one radius produces an actual admissible point set whose
disk discrepancy is bounded uniformly over all centers at that radius. -/
theorem exists_admissible_fixedRadius_of_finiteJitteredCertificate
    {radius allowance : ℝ}
    (hcert : HasFiniteJitteredCertificateAtRadius radius allowance) :
    ∃ A : Set Plane, IsAdmissible A ∧ ∀ center : Plane,
      diskError A center radius ≤ allowance := by
  rcases hcert with ⟨n, offset, support, hoffset, hcover, hfinite⟩
  obtain ⟨x, hinj, hbound⟩ :=
    exists_injective_point_selection_with_all_disk_bounds
      (latticeLocation offset) (latticeLocation_cell_separated hoffset)
      (fun center : Plane ↦ center) (fun _ ↦ radius) (fun _ ↦ allowance)
      support hcover hfinite
  have htable : CandidateTableLocallyFinite (latticeLocation offset) :=
    latticeLocation_candidateTableLocallyFinite fun q ↦
      ⟨(hoffset q).1, (hoffset q).2.1.le,
        (hoffset q).2.2.1, (hoffset q).2.2.2.le⟩
  let z : PlaneCell → Plane := selectedPoint (latticeLocation offset) x
  have hzinf : (range z).Infinite := Set.infinite_range_of_injective hinj
  have hzloc : ∀ K : Set Plane, IsCompact K → (range z ∩ K).Finite := by
    intro K hK
    rw [range_inter_eq_image_preimage]
    exact (selectedPoint_compact_preimage_finite htable x K hK).image z
  refine ⟨range z, ⟨hzinf, hzloc⟩, ?_⟩
  intro center
  simpa [diskError, diskCount, z] using hbound center

/-- Radius-by-radius finite jittered certificates imply Beck's exact fixed-radius upper
construction in the core formulation. -/
theorem finiteJitteredCertificates_imply_sqrtLogUpper
    {C R : ℝ} (hC : 0 < C)
    (hcert : ∀ r ≥ R,
      HasFiniteJitteredCertificateAtRadius r
        (C * Real.sqrt (r * Real.log r))) :
    HasSqrtLogUpperConstruction := by
  refine ⟨C, hC, R, ?_⟩
  intro r hr
  exact exists_admissible_fixedRadius_of_finiteJitteredCertificate (hcert r hr)

end FixedRadiusUpper
end Erdos989
