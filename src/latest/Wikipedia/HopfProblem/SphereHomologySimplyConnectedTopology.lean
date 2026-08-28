import Wikipedia.HopfProblem.SphereHomologySimplyConnectedCover
import Wikipedia.HopfProblem.SphereHomologySuspension
import Wikipedia.HopfProblem.SphereHomologySuspensionOneTopology

/-!
# Simple connectedness of the genuine suspension and Euclidean spheres

The two actual open cones have constructed contractions, and their
actual overlap is path connected when the original space is. Applying
van Kampen proves simple connectedness of the original suspension.
The explicit latitude homeomorphism then transfers the result to the
literal Euclidean unit spheres of dimension at least two.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open CuspCentralHomology FundamentalGroupVanKampen

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]

/-- The genuine two-cone cover based at a specified equatorial point. -/
def suspensionConeCover (x : X) : TwoOpenCover (Suspension X) where
  U := ⟨Suspension.northOpen, Suspension.northOpen_isOpen⟩
  V := ⟨Suspension.southOpen, Suspension.southOpen_isOpen⟩
  cover := Suspension.open_cover
  pathConnectedU := by
    change IsPathConnected (Suspension.northOpen : Set (Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedV := by
    change IsPathConnected (Suspension.southOpen : Set (Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := by
    change IsPathConnected (Suspension.middleBand X)
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  base := Suspension.mk ⟨1 / 2, by norm_num⟩ x
  baseU := by norm_num [Suspension.mem_northOpen]
  baseV := by norm_num [Suspension.mem_southOpen]

/-- The suspension of every path-connected space is genuinely simply connected. -/
instance suspension_simplyConnectedSpace : SimplyConnectedSpace (Suspension X) := by
  let D := suspensionConeCover X (Classical.choice (inferInstance : Nonempty X))
  let : SimplyConnectedSpace D.U := by
    change SimplyConnectedSpace (Suspension.northOpen : Set (Suspension X))
    infer_instance
  let : SimplyConnectedSpace D.V := by
    change SimplyConnectedSpace (Suspension.southOpen : Set (Suspension X))
    infer_instance
  exact twoOpenCover_simplyConnectedSpace D

/-- Every actual loop in the suspension is null-homotopic. -/
theorem suspension_loop_nullhomotopic (x : Suspension X) (p : Path x x) :
    Path.Homotopic p (Path.refl x) :=
  SimplyConnectedSpace.paths_homotopic p (Path.refl x)

/-- Every literal Euclidean unit sphere of dimension at least two is simply connected. -/
instance unitSphere_simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (UnitSphere (n + 2)) :=
  (suspensionSphereHomeomorph (n + 1)).symm.toHomotopyEquiv.simplyConnectedSpace

/-- The actual based fundamental group is trivial at every point of these spheres. -/
theorem unitSphere_fundamentalGroup_subsingleton (n : ℕ) (x : UnitSphere (n + 2)) :
    Subsingleton (FundamentalGroup (UnitSphere (n + 2)) x) := inferInstance

/-- The resulting null-homotopies concern the original paths on the original sphere. -/
theorem unitSphere_loop_nullhomotopic (n : ℕ) (x : UnitSphere (n + 2))
    (p : Path x x) : Path.Homotopic p (Path.refl x) :=
  SimplyConnectedSpace.paths_homotopic p (Path.refl x)

end Wikipedia.HopfProblem.SphereHomology
