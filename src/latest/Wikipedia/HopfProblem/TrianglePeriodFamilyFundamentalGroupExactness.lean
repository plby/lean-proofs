import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupExactnessCovering
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupExactnessProduct

/-!
# Fundamental-group exactness for the actual diagonal quotient

The homomorphism induced by a fibre inclusion is injective, and its range
is exactly the kernel of the homomorphism induced by the projection.
These statements use the actual quotient covering of the product.  They
do not require the base or the fibre to be connected or simply connected,
nor do they require a fixed point of the fibre action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)

include hq

/-- The actual fibre inclusion induces an injective homomorphism on
fundamental groups. -/
theorem fibreFundamentalGroupHom_injective (b : B) (c : F) :
    Function.Injective (fibreFundamentalGroupHom (G := G) b c) := by
  intro α β h
  apply product_vertical_loop_map_injective b c
  apply (quotient_isCoveringMap (F := F) hq).injective_path_homotopic_map (b, c) (b, c)
  change (Path.Homotopic.Quotient.map α
    ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
      ⟨quotient G B F, quotient_continuous G B F⟩ =
    (Path.Homotopic.Quotient.map β
      ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨quotient G B F, quotient_continuous G B F⟩
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
  exact h

/-- A loop in the total space has trivial projected class exactly when
its class comes from the actual fibre inclusion. -/
theorem fibreFundamentalGroupHom_range_eq_ker (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range =
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  apply le_antisymm (fibreFundamentalGroupHom_range_le_ker b c)
  intro γ hγ
  change Path.Homotopic.Quotient.map γ
      ⟨projection G B F, projection_continuous G B F⟩ =
    Path.Homotopic.Quotient.refl (baseQuotient G B b) at hγ
  obtain ⟨α, hα⟩ := quotient_loop_lift_of_projection_eq_refl hq b c γ hγ
  have hfst : α.map ⟨Prod.fst, continuous_fst⟩ =
      Path.Homotopic.Quotient.refl b := by
    apply hq.isCoveringMap.injective_path_homotopic_map b b
    change (α.map ⟨Prod.fst, continuous_fst⟩).map
      ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        Path.Homotopic.Quotient.refl (baseQuotient G B b)
    have hs : (α.map ⟨Prod.fst, continuous_fst⟩).map
        ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        (α.map ⟨quotient G B F, quotient_continuous G B F⟩).map
          ⟨projection G B F, projection_continuous G B F⟩ := by
      rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
      rfl
    exact hs.trans ((congrArg (fun η : Path.Homotopic.Quotient
      (fibreInclusion G B F b c) (fibreInclusion G B F b c) =>
        η.map ⟨projection G B F, projection_continuous G B F⟩) hα).trans hγ)
  refine ⟨α.map ⟨Prod.snd, continuous_snd⟩, ?_⟩
  have hv := congrArg (fun η : Path.Homotopic.Quotient (b, c) (b, c) =>
    η.map ⟨quotient G B F, quotient_continuous G B F⟩)
      (product_loop_eq_vertical_of_fst_eq_refl b c α hfst)
  rw [← Path.Homotopic.Quotient.map_comp] at hv
  exact hv.symm.trans hα

/-- Kernel-first form of exactness for the actual projection. -/
theorem projectionFundamentalGroupHom_ker (b : B) (c : F) :
    (projectionFundamentalGroupHom (G := G) b c).ker =
      (fibreFundamentalGroupHom (G := G) b c).range :=
  (fibreFundamentalGroupHom_range_eq_ker hq b c).symm

end Wikipedia.HopfProblem.DiagonalQuotient
