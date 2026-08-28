import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairHomology
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleFundamentalGroup
import Wikipedia.HopfProblem.FundamentalGroupBasepointNaturality

/-!

# The actual fundamental-group quotient across a surgery pair

The two original ends include into the same whole-handle body. When the
opposite attaching sphere is simply connected, the new inclusion induces
an isomorphism. At a retained exterior point its basepoint is literally
the old inclusion's basepoint, so their comparison is a specified
surjection, with no change of endpoint topology. Its kernel is precisely
the normal closure of the original attaching-sphere map, transported
along an actual path in the old end.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap FundamentalGroup

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle

variable {E F R X Y : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] (d : SurgeryBoundaryPair E F R X Y)

include d in
theorem pathConnected_iff [PathConnectedSpace (UnitSphere E)]
    [PathConnectedSpace (UnitSphere F)] :
    PathConnectedSpace Y ↔ PathConnectedSpace X :=
  (newHandleData d).pathConnected_iff.symm.trans (oldHandleData d).pathConnected_iff

section Connected

variable [PathConnectedSpace X] [PathConnectedSpace (UnitSphere E)]
  [SimplyConnectedSpace (UnitSphere F)]

omit [CompactSpace Y] [SimplyConnectedSpace (UnitSphere F)] in
theorem homotopic_attaching_map_eq_one {f : C(UnitSphere E, X)}
    (H : f.Homotopy d.attachingSphere) (u : UnitSphere E)
    (g : FundamentalGroup (UnitSphere E) u) :
    FundamentalGroup.map ((oldMap d).comp f) u g = 1 := by
  have hatt : FundamentalGroup.map ((oldMap d).comp d.attachingSphere) u g = 1 := by
    rw [FundamentalGroupTools.map_comp]
    change FundamentalGroup.map d.attachingSphere u g ∈
      (FundamentalGroup.map (oldMap d) (d.attachingSphere u)).ker
    have hker : (FundamentalGroup.map (oldMap d) (d.attachingSphere u)).ker =
        Subgroup.normalClosure (range (FundamentalGroup.map d.attachingSphere u)) :=
      (oldHandleData d).old_fundamentalGroup_kernel u
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨g, rfl⟩
  exact (FundamentalGroupTools.map_eq_one_iff_of_homotopy
    ((ContinuousMap.Homotopy.refl (oldMap d)).comp H) u g).mpr hatt

theorem new_fundamentalGroup_bijective (y : Y) :
    Bijective (FundamentalGroup.map (newMap d) y) := by
  let : PathConnectedSpace Y := (pathConnected_iff d).mpr inferInstance
  exact (newHandleData d).old_fundamentalGroup_bijective y

/-- The new inclusion, with the actual equality of retained exterior points. -/
def newGroupExteriorEquiv (r : R) :
    FundamentalGroup Y (d.newExterior r) ≃* FundamentalGroup (Space d) (exteriorMap d r) :=
  MulEquiv.ofBijective (FundamentalGroup.mapOfEq (newMap d) (newMap_exterior d r)) (by
    unfold FundamentalGroup.mapOfEq
    let q : CategoryTheory.Iso (FundamentalGroupoid.mk (newMap d (d.newExterior r)))
        (FundamentalGroupoid.mk (exteriorMap d r)) :=
      CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk (newMap_exterior d r))
    exact q.conj.bijective.comp (new_fundamentalGroup_bijective d (d.newExterior r)))

/-- The surgery map compares the literal endpoint inclusions into the common body. -/
def fundamentalGroupMap (r : R) :
    FundamentalGroup X (d.oldExterior r) →* FundamentalGroup Y (d.newExterior r) :=
  (newGroupExteriorEquiv d r).symm.toMonoidHom.comp
    (FundamentalGroup.map (oldMap d) (d.oldExterior r))

theorem fundamentalGroupMap_inclusions (r : R)
    (g : FundamentalGroup X (d.oldExterior r)) :
    FundamentalGroup.mapOfEq (newMap d) (newMap_exterior d r) (fundamentalGroupMap d r g) =
      FundamentalGroup.map (oldMap d) (d.oldExterior r) g :=
  (newGroupExteriorEquiv d r).apply_symm_apply _

theorem fundamentalGroupMap_surjective (r : R) : Surjective (fundamentalGroupMap d r) :=
  (newGroupExteriorEquiv d r).symm.surjective.comp
    ((oldHandleData d).old_fundamentalGroup_surjective (d.oldExterior r))

theorem fundamentalGroupMap_ker (r : R) :
    (fundamentalGroupMap d r).ker =
      (FundamentalGroup.map (oldMap d) (d.oldExterior r)).ker := by
  ext g
  change fundamentalGroupMap d r g = 1 ↔
    FundamentalGroup.map (oldMap d) (d.oldExterior r) g = 1
  constructor
  · intro hg
    have h := fundamentalGroupMap_inclusions d r g
    rw [hg, map_one] at h
    exact h.symm
  · intro hg
    apply (newGroupExteriorEquiv d r).injective
    exact (fundamentalGroupMap_inclusions d r g).trans
      (hg.trans (map_one (newGroupExteriorEquiv d r)).symm)

/-- The exact relations are marked by the original attaching sphere and an old-end path. -/
theorem fundamentalGroupMap_kernel_normalClosure (r : R) (u : UnitSphere E)
    (p : Path (d.attachingSphere u) (d.oldExterior r)) :
    (fundamentalGroupMap d r).ker = Subgroup.normalClosure (range
      ((fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
        (FundamentalGroup.map d.attachingSphere u))) := by
  rw [fundamentalGroupMap_ker]
  apply NormalClosureKernel.kernel_normalClosure
    (FundamentalGroup.map (oldMap d) (d.attachingSphere u))
    (FundamentalGroup.map (oldMap d) (d.oldExterior r))
    (fundamentalGroupMulEquivOfPath p).toMonoidHom
    (FundamentalGroup.map d.attachingSphere u)
    (fundamentalGroupMulEquivOfPath p).surjective
  · intro g
    have hn := fundamentalGroup_basepoint_naturality_apply (oldMap d) p g
    exact (fundamentalGroup_basepoint_change_eq_one_iff (p.map (oldMap d).continuous)
      (FundamentalGroup.map (oldMap d) (d.attachingSphere u) g)).symm.trans
        (congrArg (fun z : FundamentalGroup (Space d) (oldMap d (d.oldExterior r)) =>
          z = 1) hn).to_iff
  · exact (oldHandleData d).old_fundamentalGroup_kernel u

def fundamentalGroupQuotient (r : R) (u : UnitSphere E)
    (p : Path (d.attachingSphere u) (d.oldExterior r)) :
    FundamentalGroup X (d.oldExterior r) ⧸ Subgroup.normalClosure (range
      ((fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
        (FundamentalGroup.map d.attachingSphere u))) ≃*
          FundamentalGroup Y (d.newExterior r) :=
  QuotientGroup.liftEquiv _ (fundamentalGroupMap_surjective d r)
    (fundamentalGroupMap_kernel_normalClosure d r u p).symm

@[simp] theorem fundamentalGroupQuotient_mk (r : R) (u : UnitSphere E)
    (p : Path (d.attachingSphere u) (d.oldExterior r))
    (g : FundamentalGroup X (d.oldExterior r)) :
    fundamentalGroupQuotient d r u p (QuotientGroup.mk' _ g) =
      fundamentalGroupMap d r g := rfl

end Connected

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
