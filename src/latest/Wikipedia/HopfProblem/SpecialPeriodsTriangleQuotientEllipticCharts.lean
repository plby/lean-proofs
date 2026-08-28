import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticNeighborhoods
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientPower
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBranchLocal

/-!
# Actual elliptic charts of the full triangle orbit space

The precisely invariant Cayley neighbourhoods have their genuine stabilizer
quotients identified with the disc by the third and fourth power maps.
Composing with the proved local-to-global orbit homeomorphism produces actual
open partial homeomorphisms on the full quotient.  Their coordinate pullbacks
are holomorphic on their entire saturated sources and locally biholomorphic
away from the corresponding central orbit.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous triangleGeometricAction_continuous

/-- The actual stabilizer quotient has the power coordinate as a disc
homeomorphism, including the ramification point. -/
def ellipticLocalDiscHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ Disc := by
  letI := ellipticNeighborhoodAction j
  exact TriangleQuotientPower.orbitDiscHomeomorph j
    (ellipticNeighborhoodChart j).toHomeomorph (ellipticStabilizerGenerator j)
    (ellipticStabilizer_eq_generator_pow j) (ellipticNeighborhoodChart_generator j)

@[simp] theorem ellipticLocalDiscHomeomorph_mk (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticLocalDiscHomeomorph j
      (LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
        (ellipticNeighborhood_mapsTo j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := rfl

/-- The disc coordinate on the actual open image in the full quotient. -/
def ellipticImageDiscHomeomorph (j : Elliptic.Kind) :
    ellipticNeighborhoodImage j ≃ₜ Disc :=
  (ellipticNeighborhoodQuotientHomeomorph j).symm.trans (ellipticLocalDiscHomeomorph j)

theorem ellipticImageDiscHomeomorph_projection (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticImageDiscHomeomorph j
      (LocalOrbitQuotient.imageProjection (G := TriangleGroup) (ellipticNeighborhood j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
  let q := LocalOrbitQuotient.localProjection (ellipticStabilizer j)
    (ellipticNeighborhood j) (ellipticNeighborhood_mapsTo j) z
  have he : ellipticNeighborhoodQuotientHomeomorph j q =
      LocalOrbitQuotient.imageProjection (G := TriangleGroup) (ellipticNeighborhood j) z := rfl
  change ellipticLocalDiscHomeomorph j
    ((ellipticNeighborhoodQuotientHomeomorph j).symm _) = _
  rw [← he, Homeomorph.symm_apply_apply]
  exact ellipticLocalDiscHomeomorph_mk j z

/-- A full-source disc parametrization of the actual elliptic quotient image. -/
def ellipticOrbitParametrization (j : Elliptic.Kind) :
    OpenPartialHomeomorph Disc TriangleOrbitSpace :=
  (ellipticImageDiscHomeomorph j).symm.toOpenPartialHomeomorph.trans
    ((ellipticNeighborhoodImage j).openPartialHomeomorphSubtypeCoe
      ⟨⟨ellipticOrbitCenter j, ellipticOrbitCenter_mem_neighborhoodImage j⟩⟩)

@[simp] theorem ellipticOrbitParametrization_source (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).source = univ := by
  simp [ellipticOrbitParametrization]

@[simp] theorem ellipticOrbitParametrization_target (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).target = ellipticNeighborhoodImage j := by
  simp [ellipticOrbitParametrization]

theorem ellipticOrbitParametrization_power (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticOrbitParametrization j
      (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) =
      triangleOrbitProjection z := by
  change ((ellipticImageDiscHomeomorph j).symm
    (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) :
      TriangleOrbitSpace) = triangleOrbitProjection z
  rw [← ellipticImageDiscHomeomorph_projection j z]
  exact congrArg (fun q : ellipticNeighborhoodImage j => (q : TriangleOrbitSpace))
    ((ellipticImageDiscHomeomorph j).symm_apply_apply
      (show ellipticNeighborhoodImage j from
        LocalOrbitQuotient.imageProjection (G := TriangleGroup) (ellipticNeighborhood j) z))

/-- The actual complex-valued elliptic chart on the full orbit space. -/
def ellipticFullChart (j : Elliptic.Kind) : OpenPartialHomeomorph TriangleOrbitSpace ℂ :=
  (ellipticOrbitParametrization j).symm.trans
    (unitDisc.openPartialHomeomorphSubtypeCoe ⟨discZero⟩)

@[simp] theorem ellipticFullChart_source (j : Elliptic.Kind) :
    (ellipticFullChart j).source = ellipticNeighborhoodImage j := by
  simp [ellipticFullChart]

@[simp] theorem ellipticFullChart_target (j : Elliptic.Kind) :
    (ellipticFullChart j).target = unitDisc := by
  simp [ellipticFullChart]

/-- The exact local equation of the quotient projection is the normalized
centered Cayley coordinate to the indicated third or fourth power. -/
theorem ellipticFullChart_projection (j : Elliptic.Kind) (z : ellipticNeighborhood j) :
    ellipticFullChart j (triangleOrbitProjection z) =
      normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order z := by
  have he : (ellipticOrbitParametrization j).symm (triangleOrbitProjection z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
    rw [← ellipticOrbitParametrization_power j z]
    exact (ellipticOrbitParametrization j).left_inv (by simp)
  change ((ellipticOrbitParametrization j).symm (triangleOrbitProjection z) : ℂ) = _
  rw [he, Elliptic.discPower_coe, ellipticNeighborhoodChart_val]
  rfl

theorem ellipticFullChart_center_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOrbitCenter_mem_neighborhoodImage j

@[simp] theorem ellipticFullChart_center (j : Elliptic.Kind) :
    ellipticFullChart j (ellipticOrbitCenter j) = 0 := by
  have he := ellipticFullChart_projection j (ellipticNeighborhoodCenter j)
  simpa only [ellipticOrbitCenter, ellipticNeighborhoodCenter, normalizedCayleyBranch,
    normalizedCayley, cayleyCoordinate, sub_self, zero_div, zero_pow j.order_pos.ne'] using he

theorem ellipticFullChart_eq_zero_iff (j : Elliptic.Kind) {q : TriangleOrbitSpace}
    (hq : q ∈ (ellipticFullChart j).source) :
    ellipticFullChart j q = 0 ↔ q = ellipticOrbitCenter j := by
  constructor
  · intro h
    apply (ellipticFullChart j).injOn hq (ellipticFullChart_center_mem_source j)
    rw [h, ellipticFullChart_center]
  · rintro rfl
    exact ellipticFullChart_center j

theorem ellipticFullChart_other_not_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOtherOrbitCenter_not_mem_neighborhoodImage j

/-- Any local translate landing in the chosen neighbourhood gives the same
quotient coordinate on an actual neighbourhood of its source point. -/
theorem ellipticFullChart_pullback_eventuallyEq (j : Elliptic.Kind)
    (g : TriangleGroup) {z : ℍ}
    (hz : triangleGeometricRepresentation g z ∈ ellipticNeighborhood j) :
    (ellipticFullChart j ∘ triangleOrbitProjection) =ᶠ[𝓝 z]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        triangleGeometricRepresentation g) := by
  have hU : ∀ᶠ w in 𝓝 z, triangleGeometricRepresentation g w ∈ ellipticNeighborhood j :=
    (triangleGeometricRepresentation_holomorphic g).continuous.continuousAt
      ((ellipticNeighborhood j).isOpen.mem_nhds hz)
  filter_upwards [hU] with w hw
  change ellipticFullChart j (triangleOrbitProjection w) = _
  rw [← triangleOrbitProjection_smul g w]
  exact ellipticFullChart_projection j ⟨triangleGeometricRepresentation g w, hw⟩

/-- Every point above the chart source has a translate in its genuine local
uniformizing neighbourhood. -/
theorem ellipticFullChart_exists_lift (j : Elliptic.Kind) {z : ℍ}
    (hz : triangleOrbitProjection z ∈ (ellipticFullChart j).source) :
    ∃ g : TriangleGroup, triangleGeometricRepresentation g z ∈ ellipticNeighborhood j := by
  rw [ellipticFullChart_source] at hz
  obtain ⟨w, hw, he⟩ := hz
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff w z).mp he
  exact ⟨g, hg ▸ hw⟩

/-- Holomorphicity holds on the entire saturated chart source, not only on
the one chosen local representative neighbourhood. -/
theorem ellipticFullChart_pullback_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFullChart j ∘ triangleOrbitProjection)
      (triangleOrbitProjection ⁻¹' (ellipticFullChart j).source) := by
  intro z hz
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hf := (normalizedCayleyBranch_holomorphic (ellipticCenter j)
    (ellipticNeighborhoodRadius j) (ellipticNeighborhoodRadius_pos j).ne' j.order).comp
      (triangleGeometricRepresentation_holomorphic g)
  exact (hf.contMDiffAt.congr_of_eventuallyEq
    (ellipticFullChart_pullback_eventuallyEq j g hg)).contMDiffWithinAt

/-- Away from its own elliptic orbit the pulled-back chart is a local
biholomorphism, on every sheet of its full inverse image. -/
theorem ellipticFullChart_pullback_isLocalDiffeomorphAt (j : Elliptic.Kind) {z : ℍ}
    (hz : triangleOrbitProjection z ∈ (ellipticFullChart j).source)
    (hcenter : triangleOrbitProjection z ≠ ellipticOrbitCenter j) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFullChart j ∘ triangleOrbitProjection) z := by
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hgc : triangleGeometricRepresentation g z ≠ ellipticCenter j := by
    intro h
    apply hcenter
    rw [← triangleOrbitProjection_smul g z, h]
    rfl
  have hf := ((triangleGeometricBiholomorph g).isLocalDiffeomorph z).comp
    (K := 𝓘(ℂ)) (P := ℂ)
    (normalizedCayleyBranch_isLocalDiffeomorphAt (ellipticCenter j)
      (triangleGeometricRepresentation g z) (ellipticNeighborhoodRadius j)
      (ellipticNeighborhoodRadius_pos j).ne' j.order j.order_pos hgc)
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq hf
    (ellipticFullChart_pullback_eventuallyEq j g hg)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
