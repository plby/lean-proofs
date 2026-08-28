import Wikipedia.SmoothSixDPoincare.HandleCoreFundamentalGroup
import Wikipedia.SmoothSixDPoincare.CellFundamentalGroupRelations
import Wikipedia.SmoothSixDPoincare.NormalClosureKernelTransport

/-!
# The exact nonabelian relations of the original whole-handle inclusion

The embedded core-cell theorem is transferred through the actual old-space
coordinates and the whole-handle deformation. Its relations are induced
by the original core boundary, not by unrelated abstract generators.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCoreAttachment

open MorseHandle

variable {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (r : R → X) (h : C(UnitDisk N × UnitDisk P, X))
  (hr : IsClosedEmbedding r) (hh : IsClosedEmbedding h)
  (hcover : range r ∪ range h = univ)
  (hface : ∀ z, h z ∈ range r ↔ ‖(z.1 : N)‖ = 1)
  [PathConnectedSpace R] [PathConnectedSpace (sphere (0 : N) 1)]

include hcover in
theorem old_fundamentalGroup_kernel (u : sphere (0 : N) 1) :
    (FundamentalGroup.map ⟨r, hr.continuous⟩ (coreBoundaryMap r h hr hh hface u)).ker =
      Subgroup.normalClosure
        (range (FundamentalGroup.map (coreBoundaryMap r h hr hh hface) u)) := by
  let D := cellPresentation r h hr hh hface
  let e := cellOldHomeomorph r h hr hh hface
  let q := homotopyEquiv r h hr hh hcover hface
  let i : C(D.old, coreSpace r h) := ⟨Subtype.val, continuous_subtype_val⟩
  let rmap : C(R, X) := ⟨r, hr.continuous⟩
  let a := D.attachingSphere u
  let ρ := FundamentalGroup.map e.symm.toHomotopyEquiv.toFun a
  let _ : PathConnectedSpace D.old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv e.symm.toHomotopyEquiv
  have hρ : Surjective ρ :=
    (FundamentalGroupTools.map_bijective_of_homotopyEquiv e.symm.toHomotopyEquiv a).2
  have he : rmap.comp e.symm.toHomotopyEquiv.toFun = q.toFun.comp i := by
    apply ContinuousMap.ext
    intro y
    exact congrArg (fun z : D.old => z.val.val) (e.apply_symm_apply y)
  have hnull (γ : FundamentalGroup D.old a) :
      FundamentalGroup.map i a γ = 1 ↔
        FundamentalGroup.map rmap (e.symm a) (ρ γ) = 1 := by
    have hm := (congrArg (fun f : C(D.old, X) => FundamentalGroup.map f a γ = 1) he).to_iff
    have hl := DFunLike.congr_fun
      (FundamentalGroupTools.map_comp e.symm.toHomotopyEquiv.toFun rmap a) γ
    have hr' := DFunLike.congr_fun (FundamentalGroupTools.map_comp i q.toFun a) γ
    have hq := (FundamentalGroupTools.map_bijective_of_homotopyEquiv q (i a)).1
    have hleft := (congrArg (fun z : FundamentalGroup X _ => z = 1) hl).to_iff
    have hright := (congrArg (fun z : FundamentalGroup X _ => z = 1) hr').to_iff
    exact (map_eq_one_iff (FundamentalGroup.map q.toFun (i a)) hq).symm.trans
      (hright.symm.trans (hm.symm.trans hleft))
  have hk := NormalClosureKernel.kernel_normalClosure (FundamentalGroup.map i a)
    (FundamentalGroup.map rmap (e.symm a)) ρ (FundamentalGroup.map D.attachingSphere u)
    hρ hnull (D.old_inclusion_fundamentalGroup_kernel u)
  have hs := FundamentalGroupTools.map_comp D.attachingSphere e.symm.toHomotopyEquiv.toFun u
  exact hk.trans (congrArg (fun f : FundamentalGroup (sphere (0 : N) 1) u →*
    FundamentalGroup R (e.symm a) => Subgroup.normalClosure (range f)) hs.symm)

end Wikipedia.SmoothSixDPoincare.HandleCoreAttachment
