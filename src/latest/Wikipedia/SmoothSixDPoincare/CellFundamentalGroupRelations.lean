import Wikipedia.SmoothSixDPoincare.CellFundamentalGroupCover

/-!
# The actual nonabelian attaching relations of an embedded cell

The kernel of the old-space inclusion is the normal closure of the map
induced by the original attaching sphere. The proof transports the actual
van Kampen kernel through the old-neighborhood deformation and the annular
sphere equivalence; no presentation or choice of generators is assumed.
-/

noncomputable section

open Set Metric Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X) [PathConnectedSpace D.old]
  [PathConnectedSpace (sphere (0 : N) 1)]

theorem old_inclusion_fundamentalGroup_kernel_overlap (u : sphere (0 : N) 1) :
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(D.old, X))
      (D.overlapOldMap (D.overlapSphereEquiv u))).ker =
        Subgroup.normalClosure (range
          (FundamentalGroup.map D.overlapOldMap (D.overlapSphereEquiv u))) := by
  let C := D.fundamentalGroupCover u
  let i : C(D.old, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let ρ := FundamentalGroup.map D.oldRetraction C.baseUPoint
  have hρ : Surjective ρ :=
    (FundamentalGroupTools.map_bijective_of_homotopyEquiv
      D.oldHomotopyEquiv.symm C.baseUPoint).2
  have H : C.inclusionU.Homotopy (i.comp D.oldRetraction) :=
    (ContinuousMap.Homotopy.refl C.inclusionU).comp D.oldDeformation.toHomotopy
  have hnull (γ : C.UGroup) :
      C.inclusionHomU γ = 1 ↔
        FundamentalGroup.map i (D.oldRetraction C.baseUPoint) (ρ γ) = 1 := by
    have he := FundamentalGroupTools.map_eq_one_iff_of_homotopy H C.baseUPoint γ
    have hm := DFunLike.congr_fun
      (FundamentalGroupTools.map_comp D.oldRetraction i C.baseUPoint) γ
    exact he.trans (congrArg (fun a : FundamentalGroup X _ => a = 1) hm).to_iff
  have hker : (FundamentalGroup.map i (D.oldRetraction C.baseUPoint)).ker =
      C.inclusionHomU.ker.map ρ := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨δ, rfl⟩ := hρ γ
      exact ⟨δ, (hnull δ).mpr hγ, rfl⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact (hnull δ).mp hδ
  have hmaps : ρ.comp C.overlapHomU =
      FundamentalGroup.map D.overlapOldMap (D.overlapSphereEquiv u) :=
    (FundamentalGroupTools.map_comp C.overlapToU D.oldRetraction C.baseOverlapPoint).symm
  change (FundamentalGroup.map i (D.oldRetraction C.baseUPoint)).ker = _
  calc
    _ = C.inclusionHomU.ker.map ρ := hker
    _ = (Subgroup.normalClosure (range C.overlapHomU)).map ρ :=
      congrArg (fun K : Subgroup C.UGroup => K.map ρ)
        (D.fundamentalGroupCover_inclusion_kernel u)
    _ = Subgroup.normalClosure (ρ '' range C.overlapHomU) :=
      Subgroup.map_normalClosure (range C.overlapHomU) ρ hρ
    _ = _ := congrArg Subgroup.normalClosure
      ((Set.range_comp ρ C.overlapHomU).symm.trans
        (congrArg (fun f : C.OverlapGroup →* FundamentalGroup D.old
          (D.oldRetraction C.baseUPoint) => range f) hmaps))

/-- Exact relations at the original attaching-sphere basepoint. -/
theorem old_inclusion_fundamentalGroup_kernel (u : sphere (0 : N) 1) :
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(D.old, X))
      (D.attachingSphere u)).ker =
        Subgroup.normalClosure (range (FundamentalGroup.map D.attachingSphere u)) := by
  have h := D.old_inclusion_fundamentalGroup_kernel_overlap u
  have hs := FundamentalGroupTools.map_bijective_of_homotopyEquiv D.overlapSphereEquiv u
  have hr := hs.2.range_comp
    (FundamentalGroup.map D.overlapOldMap (D.overlapSphereEquiv u))
  have hm := FundamentalGroupTools.map_comp D.overlapSphereEquiv.toFun D.overlapOldMap u
  have he : range (FundamentalGroup.map
      (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) u) =
        range (FundamentalGroup.map D.overlapOldMap (D.overlapSphereEquiv u)) := by
    rw [hm]
    exact hr
  rw [← he] at h
  let statement (f : C(sphere (0 : N) 1, D.old)) : Prop :=
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(D.old, X)) (f u)).ker =
      Subgroup.normalClosure (range (FundamentalGroup.map f u))
  exact (congrArg statement D.overlapOldMap_comp_sphere).mp h

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
