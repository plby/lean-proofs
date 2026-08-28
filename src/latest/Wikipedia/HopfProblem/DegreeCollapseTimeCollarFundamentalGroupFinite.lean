import Wikipedia.HopfProblem.DegreeCollapseCompactFundamentalGroupFinite
import Wikipedia.HopfProblem.DegreeCollapseOpenCoverConnectedPart
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap
import Wikipedia.HopfProblem.DegreeCollapseTrivialPatchVanKampen

/-!

# Finite generation for the actual collared half

The original open halves have simply connected overlap when the boundary
is simply connected. The identity on one patch group and the trivial map
on the other extend to a retraction from the ambient fundamental group.
Thus ambient finite generation passes to the patch and, through the
actual collar homotopy equivalence, to the original closed half.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse

open FundamentalGroupVanKampen Wikipedia.SmoothSixDPoincare

namespace AttachmentConnectivity

variable {X : Type*} [TopologicalSpace X] (D : TwoOpenCover X)

theorem old_fundamentalGroup_finite [Subsingleton D.OverlapGroup]
    [Group.FG (FundamentalGroup X D.base)] (x : D.U) :
    Group.FG (FundamentalGroup D.U x) := by
  have hComp : (oldGroupRetraction D).comp D.inclusionHomU = MonoidHom.id D.UGroup :=
    D.lift_comp_inclusionU (MonoidHom.id D.UGroup) 1 _
  have hSurj : Surjective (oldGroupRetraction D) := by
    intro g
    exact ⟨D.inclusionHomU g, DFunLike.congr_fun hComp g⟩
  let : Group.FG D.UGroup := Group.fg_of_surjective hSurj
  let : PathConnectedSpace D.U :=
    isPathConnected_iff_pathConnectedSpace.mp D.pathConnectedU
  exact FundamentalGroupFiniteness.of_pathConnected D.baseUPoint x

end AttachmentConnectivity

namespace TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [PreconnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem positiveOpen_pathConnected : PathConnectedSpace C.positiveOpen := by
  let : SimplyConnectedSpace C.overlap := C.overlapHomotopyEquiv.simplyConnectedSpace
  apply OpenCoverConnectivity.right_pathConnected
    C.reverse.positiveOpen.isOpen C.positiveOpen.isOpen
  · rw [union_comm]
    exact C.open_halves_cover
  · rw [inter_comm]
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (inferInstanceAs (PathConnectedSpace C.overlap))

include C in
theorem half_pathConnected : PathConnectedSpace (NonnegativeHalf t) := by
  let : PathConnectedSpace C.positiveOpen := C.positiveOpen_pathConnected
  exact FundamentalGroupTools.pathConnected_of_homotopyEquiv
    C.positiveHalfHomotopyEquiv.symm

def connectedHalfCover : TwoOpenCover M := by
  let : SimplyConnectedSpace C.overlap := C.overlapHomotopyEquiv.simplyConnectedSpace
  let o : C.overlap := Classical.arbitrary _
  exact {
    U := C.positiveOpen
    V := C.reverse.positiveOpen
    cover := C.open_halves_cover
    pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr C.positiveOpen_pathConnected
    pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr
      C.reverse.positiveOpen_pathConnected
    pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr
      (inferInstanceAs (PathConnectedSpace C.overlap))
    base := o.val
    baseU := o.property.1
    baseV := o.property.2 }

theorem positiveOpen_fundamentalGroup_finite
    (hM : ∀ x : M, Group.FG (FundamentalGroup M x)) (x : C.positiveOpen) :
    Group.FG (FundamentalGroup C.positiveOpen x) := by
  let : SimplyConnectedSpace C.overlap := C.overlapHomotopyEquiv.simplyConnectedSpace
  let D := C.connectedHalfCover
  let : SimplyConnectedSpace D.overlap := inferInstanceAs (SimplyConnectedSpace C.overlap)
  let : Group.FG (FundamentalGroup M D.base) := hM _
  exact AttachmentConnectivity.old_fundamentalGroup_finite D x

include C in
theorem half_fundamentalGroup_finite
    (hM : ∀ x : M, Group.FG (FundamentalGroup M x)) (x : NonnegativeHalf t) :
    Group.FG (FundamentalGroup (NonnegativeHalf t) x) :=
  FundamentalGroupFiniteness.of_homotopyEquiv C.positiveHalfHomotopyEquiv
    (C.positiveOpen_fundamentalGroup_finite hM) x

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [PathConnectedSpace M]

include C E in
theorem compact_half_fundamentalGroup_finite (x : NonnegativeHalf t) :
    Group.FG (FundamentalGroup (NonnegativeHalf t) x) :=
  C.half_fundamentalGroup_finite (MorseFiniteness.compactManifold_fundamentalGroup_finite E M) x

end TimeCollar

end Wikipedia.HopfProblem.DegreeCollapse
