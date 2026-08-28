import Wikipedia.HopfProblem.DegreeCollapsePatchLoopGeneration
import Wikipedia.HopfProblem.DegreeCollapseFundamentalGroupFiniteTransport
import Wikipedia.HopfProblem.DegreeCollapseFiniteZeroSphere
import Wikipedia.SmoothSixDPoincare.CellFundamentalGroupCover
import Mathlib.Analysis.Normed.Module.Connected

/-!

# Finite generation through an actual embedded cell

For a finite attaching sphere, its actual annular homotopy equivalence
supplies finitely many overlap-component representatives. The patch
generation theorem then applies to the original open cell cover. For a
connected attaching sphere, the already proved old-inclusion surjection
gives finite generation directly. Both conclusions concern every actual
basepoint of the attached space.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachmentFiniteness

open Wikipedia.SmoothSixDPoincare

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X) [PathConnectedSpace D.old]

def cellPatchCover (u : sphere (0 : N) 1) : PatchLoopGeneration.Cover X := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  exact {
    U := ⟨D.oldNeighborhood, D.isOpen_oldNeighborhood⟩
    V := ⟨D.diskPatch, D.isOpen_diskPatch⟩
    cover := D.open_cover
    pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr D.oldNeighborhood_pathConnected
    simplyV := inferInstanceAs (SimplyConnectedSpace D.diskPatch)
    base := (D.overlapSphereEquiv u).val
    baseU := (D.overlapSphereEquiv u).property.1
    baseV := (D.overlapSphereEquiv u).property.2 }

theorem cell_fg_of_finite_sphere [Finite (sphere (0 : N) 1)] (u : sphere (0 : N) 1)
    (hOld : ∀ x : D.old, Group.FG (FundamentalGroup D.old x)) (x : X) :
    Group.FG (FundamentalGroup X x) := by
  let C := cellPatchCover D u
  let : Group.FG (FundamentalGroup C.U (⟨C.base, C.baseU⟩ : C.U)) :=
    FundamentalGroupFiniteness.of_homotopyEquiv D.oldHomotopyEquiv hOld _
  let r : sphere (0 : N) 1 → X := fun v ↦ (D.overlapSphereEquiv v).val
  have hU : ∀ v, r v ∈ C.U := fun v ↦ (D.overlapSphereEquiv v).property.1
  have hV : ∀ v, r v ∈ C.V := fun v ↦ (D.overlapSphereEquiv v).property.2
  have hcomponent : ∀ y, y ∈ C.U → y ∈ C.V →
      ∃ v, JoinedIn ((C.U : Set X) ∩ C.V) (r v) y := by
    intro y hyU hyV
    let q : ↥(D.oldNeighborhood ∩ D.diskPatch) := ⟨y, hyU, hyV⟩
    let v := D.overlapSphereEquiv.invFun q
    let p := D.overlapSphereEquiv.right_inv.some.evalAt q
    refine ⟨v, ⟨p.map continuous_subtype_val, ?_⟩⟩
    intro t
    exact (p t).property
  let : Group.FG (FundamentalGroup X C.base) := C.fg_of_finite_overlap r hU hV hcomponent
  let : Nonempty (sphere (0 : N) 1) := ⟨u⟩
  let : PathConnectedSpace X := D.total_pathConnected_of_sphere_nonempty
  exact FundamentalGroupFiniteness.of_pathConnected C.base x

theorem cell_fg_of_connected_sphere [PathConnectedSpace (sphere (0 : N) 1)]
    (hOld : ∀ x : D.old, Group.FG (FundamentalGroup D.old x)) (x : X) :
    Group.FG (FundamentalGroup X x) := by
  let y : D.old := Classical.arbitrary _
  let : Group.FG (FundamentalGroup D.old y) := hOld y
  let : Group.FG (FundamentalGroup X y.val) :=
    Group.fg_of_surjective (D.old_inclusion_fundamentalGroup_surjective y)
  let : PathConnectedSpace X := D.total_pathConnected
  exact FundamentalGroupFiniteness.of_pathConnected y.val x

include D in
theorem cell_pathConnected_of_positive_finrank (hN : 0 < Module.finrank ℝ N) :
    PathConnectedSpace X := by
  let : Nontrivial N := Module.nontrivial_of_finrank_pos hN
  let : Nonempty (sphere (0 : N) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  exact D.total_pathConnected_of_sphere_nonempty

theorem cell_fg_of_positive_finrank (hN : 0 < Module.finrank ℝ N)
    (hOld : ∀ x : D.old, Group.FG (FundamentalGroup D.old x)) (x : X) :
    Group.FG (FundamentalGroup X x) := by
  by_cases hOne : Module.finrank ℝ N = 1
  · let : Finite (sphere (0 : N) 1) := finite_unit_sphere_of_finrank_one hOne
    let : Nontrivial N := Module.nontrivial_of_finrank_pos hN
    obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : N))).mpr zero_le_one
    exact cell_fg_of_finite_sphere D ⟨u, hu⟩ hOld x
  · have hTwo : 1 < Module.finrank ℝ N := by omega
    let : PathConnectedSpace (sphere (0 : N) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank hTwo) _ zero_le_one)
    exact cell_fg_of_connected_sphere D hOld x

end Wikipedia.HopfProblem.DegreeCollapse.AttachmentFiniteness
