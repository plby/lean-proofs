import Wikipedia.HopfProblem.DegreeCollapseCylinderFilling
import Wikipedia.HopfProblem.DegreeCollapseCellLifting
import Wikipedia.HopfProblem.ThreefoldSphereHomologyEquivalence

/-!
# Exact relative lifting through dimension five

Extend the source boundary into the actual standard sphere. The full
comparison-cylinder boundary then fills in the five-connected target.
This discharges exact relative disk lifting through dimension five for the
original sphere map; the six-dimensional obstruction is not discarded.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCellLifting

open SixSphereCube

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]

/-- Any map to a five-connected target admits exact relative lifts on cells below dimension six. -/
theorem relativeDiskLifting_five (F : C(StandardSphere, Y))
    (hpi : ∀ n, 0 < n → n < 6 → ∀ y : Y, Subsingleton (π_ n Y y)) :
    FiniteCells.RelativeDiskLifting F 5 := by
  intro V _ _ _ hd a u H h0 h1
  obtain ⟨v, hv, _⟩ := Sphere.exists_boundary_extension (hd.trans (by decide)) a sphereBasePoint
  have h0' : ∀ s, H (0, s) = (F.comp v) (DiskCylinder.boundaryToDisk s) := by
    intro s
    exact (h0 s).trans (congrArg F (hv s).symm)
  obtain ⟨G, hG0, hG1, hGside⟩ := CylinderFilling.exists_filling hpi
    (by omega : Module.finrank ℝ V + 1 ≤ 6) (F.comp v) u H h0' h1 (F sphereBasePoint)
  exact ⟨v, G, hv, hG0, hG1, hGside⟩

open SpecialPeriods.Threefold

attribute [local instance] space_simplyConnected

theorem threefold_pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6) (x : Space) :
    Subsingleton (π_ n Space x) := by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact HomotopyTwo.piTwo_subsingleton x
  · exact HomotopyThree.piThree_subsingleton x
  · exact HomotopyFour.piFour_subsingleton x
  · exact HomotopyFive.piFive_subsingleton x

/-- The genuine original sphere map satisfies exact relative disk lifting through degree five. -/
theorem sphereMap_relativeDiskLifting_five (x : Space) :
    FiniteCells.RelativeDiskLifting (SphereHomologyEquivalence.sphereMap x) 5 :=
  relativeDiskLifting_five _ (fun _ hn hn6 => threefold_pi_subsingleton hn hn6)

end Wikipedia.HopfProblem.DegreeCollapse.LowCellLifting
