import Wikipedia.HopfProblem.ThreefoldStandardNormalPiece
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeSmooth
import Wikipedia.HopfProblem.StandardSixSphereCircleModelIsometries

/-!
# Native smoothness and circle equivariance of the actual normal-piece comparison

The open comparison uses the original threefold and stereographic sphere
atlases. The already constructed closed comparison is its literal restriction.
Both maps intertwine the original global circle action with the actual two-block
orthogonal action on the last four Euclidean coordinates of the sphere.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece

open CuspCircleNormalTrivialization StandardSixSphereCircleModel

attribute [local instance] SpecialPeriods.Threefold.chartedSpace

local notation "Circle" => AddCircle (1 : ℝ)
local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

/-- A diffeomorphism of genuine open subsets for their unchanged original smooth atlases. -/
def openDiffeomorph : fixedCurveNeighborhood ≃ₘ⟮IX, 𝓡 6⟯ ↥(Tube.openTube 1) where
  toEquiv := openHomeomorph.toEquiv
  contMDiff_toFun := (Tube.openDiffeomorph 1 le_rfl).contMDiff.comp
    (standardNeighborhoodDiffeomorph.symm.contMDiff.of_le le_top)
  contMDiff_invFun := (standardNeighborhoodDiffeomorph.contMDiff.of_le le_top).comp
    (Tube.openDiffeomorph 1 le_rfl).symm.contMDiff

@[simp] theorem openDiffeomorph_toHomeomorph :
    openDiffeomorph.toHomeomorph = openHomeomorph := rfl

/-- The genuine compact comparison extends to this actual smooth neighbourhood map. -/
theorem openDiffeomorph_closedIntoOpen (x : closedDiskNeighborhood) :
    (openDiffeomorph (closedIntoOpen x)).val = (closedHomeomorph x).val :=
  openHomeomorph_closedIntoOpen x

/-- The original global circle action becomes the specified standard sphere isometry. -/
theorem openHomeomorph_circleAction (t : Circle) (x : fixedCurveNeighborhood) :
    (openHomeomorph (neighborhoodCircleAction t x)).val =
      Isometries.sphereMap (RealFour.circleRotation t) (openHomeomorph x).val := by
  obtain ⟨p, rfl⟩ := standardNeighborhoodDiffeomorph.surjective x
  change (openHomeomorph (neighborhoodCircleAction t (standardNeighborhoodDiffeomorph p))).val =
    Isometries.sphereMap (RealFour.circleRotation t)
      (openHomeomorph (standardNeighborhoodDiffeomorph p)).val
  rw [standardNeighborhoodDiffeomorph_circleAction]
  apply Subtype.ext
  rw [openHomeomorph_parametrization, Isometries.sphereMap_val,
    openHomeomorph_parametrization]
  change Tube.ambient p.1 (RealFour.circleRotation t (p.2 : RealFour.Space)) =
    Isometries.ambientIsometry (RealFour.circleRotation t)
      (Tube.ambient p.1 (p.2 : RealFour.Space))
  simp only [Tube.ambient, Tube.baseFactor, LinearIsometryEquiv.norm_map,
    Isometries.ambientIsometry_join]

/-- The original action preserves the actual compact piece, including its entire interior. -/
theorem actionMap_mem_closed (t : Circle) (x : closedDiskNeighborhood) :
    Homology.DeltaSweep.actionMap (t, x.val) ∈ closedDiskNeighborhood := by
  obtain ⟨p, rfl⟩ := standardClosedDiskNeighborhoodHomeomorph.surjective x
  change Homology.DeltaSweep.actionMap (t, standardClosedDiskMap p) ∈ _
  rw [standardClosedDiskMap_circleAction]
  exact (standardClosedDiskNeighborhoodHomeomorph (standardClosedCircleAction t p)).property

/-- Restriction of the unchanged global action to the original compact piece. -/
def closedCircleAction (t : Circle) (x : closedDiskNeighborhood) : closedDiskNeighborhood :=
  ⟨Homology.DeltaSweep.actionMap (t, x.val), actionMap_mem_closed t x⟩

@[simp] theorem closedCircleAction_coe (t : Circle) (x : closedDiskNeighborhood) :
    (closedCircleAction t x : Space) = Homology.DeltaSweep.actionMap (t, x.val) := rfl

theorem closedIntoOpen_circleAction (t : Circle) (x : closedDiskNeighborhood) :
    closedIntoOpen (closedCircleAction t x) =
      neighborhoodCircleAction t (closedIntoOpen x) := rfl

/-- The same original circle marking is retained by the compact-piece comparison. -/
theorem closedHomeomorph_circleAction (t : Circle) (x : closedDiskNeighborhood) :
    (closedHomeomorph (closedCircleAction t x)).val =
      Isometries.sphereMap (RealFour.circleRotation t) (closedHomeomorph x).val := by
  rw [← openHomeomorph_closedIntoOpen, closedIntoOpen_circleAction,
    openHomeomorph_circleAction, openHomeomorph_closedIntoOpen]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece
