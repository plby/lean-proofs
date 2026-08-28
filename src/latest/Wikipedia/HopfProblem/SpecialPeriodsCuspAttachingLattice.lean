import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeLoops
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupBaseChange
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupMarkedInclusion

/-!
# The actual cusp-toric lattice vanishes in the threefold

The cusp calculation is transported along a genuine path in the regular
upper-half-plane locus.  The flat-coordinate product homotopy preserves
the original integral column.  Thus the source kernel of `M₀ - 1` dies
under the actual regular inclusion at the canonical joint marking.
No meridian relation or abstract presentation is assumed.
-/

noncomputable section

open Set Topology
open scoped Matrix unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open TrianglePeriodFamily CuspFamily CuspUniformization

/-- The literal zero-section trajectory, included into the constructed space. -/
def globalZeroSectionPath {b₀ b₁ : TriangleRegularPoint} (p : Path b₀ b₁) :
    Path (inclusion none (regularData.fundamentalGroupBasepoint b₀))
      (inclusion none (regularData.fundamentalGroupBasepoint b₁)) :=
  (regularData.zeroSectionPath p).map regularFamilyInclusionMap.continuous

@[simp] theorem globalZeroSectionPath_apply {b₀ b₁ : TriangleRegularPoint}
    (p : Path b₀ b₁) (t : I) :
    globalZeroSectionPath p t = inclusion none (regularData.quotient (p t, 0)) := rfl

/-- Actual basepoint change preserves the same source column after inclusion. -/
theorem globalLatticeHom_baseChange {b₀ b₁ : TriangleRegularPoint} (p : Path b₀ b₁)
    (v : Multiplicative Lattice) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p)
        (globalLatticeHom b₀ v) = globalLatticeHom b₁ v := by
  exact (fundamentalGroup_basepoint_naturality_apply regularFamilyInclusionMap
      (regularData.zeroSectionPath p) (regularData.latticeFundamentalGroupHom b₀ v)).trans
    (congrArg (FundamentalGroup.map regularFamilyInclusionMap
      (regularData.fundamentalGroupBasepoint b₁))
        (regularData.latticeFundamentalGroupHom_baseChange p v))

/-- At every regular upper-half-plane lift, the exact rank-two cusp-toric
kernel vanishes under the actual inclusion into the constructed threefold. -/
theorem globalLatticeHom_eq_one_of_projection_zero (b : TriangleRegularPoint)
    (v : Lattice) (hv : cuspLatticeProjection v = 0) :
    globalLatticeHom b (Multiplicative.ofAdd v) = 1 := by
  obtain ⟨s, hs⟩ := exists_small_exponential
  let s' : LogBase radius := ⟨s, (mem_logBase radius s).mpr hs⟩
  let p : Path (cuspLift s') b := PathConnectedSpace.somePath _ _
  calc
    globalLatticeHom b (Multiplicative.ofAdd v) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p)
          (globalLatticeHom (cuspLift s') (Multiplicative.ofAdd v)) :=
      (globalLatticeHom_baseChange p (Multiplicative.ofAdd v)).symm
    _ = FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p) 1 :=
      congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p))
        (globalLatticeHom_eq_one_at_cusp s' v hv)
    _ = 1 := map_one _

theorem globalLatticeHom_eq_one_of_monodromy_kernel (b : TriangleRegularPoint)
    (v : Lattice) (hv : (M₀ - 1) *ᵥ v = 0) :
    globalLatticeHom b (Multiplicative.ofAdd v) = 1 :=
  globalLatticeHom_eq_one_of_projection_zero b v
    ((cuspLatticeProjection_eq_zero_iff v).mpr hv)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

open TrianglePeriodFamily Meridians CuspUniformization

/-- The actual canonical marked inclusion kills the displayed rank-two
cusp-toric source subgroup; this assertion does not assume a presentation. -/
theorem latticeHom_eq_one_of_cusp_projection_zero (v : Lattice)
    (hv : cuspLatticeProjection v = 0) :
    latticeHom (Multiplicative.ofAdd v) = 1 :=
  CuspAttaching.globalLatticeHom_eq_one_of_projection_zero
    normalizedRegularMeridianBasepoint v hv

/-- In the original source coordinates, `ker (M₀ - 1)` is killed globally. -/
theorem latticeHom_eq_one_of_cusp_monodromy_kernel (v : Lattice)
    (hv : (M₀ - 1) *ᵥ v = 0) :
    latticeHom (Multiplicative.ofAdd v) = 1 :=
  latticeHom_eq_one_of_cusp_projection_zero v ((cuspLatticeProjection_eq_zero_iff v).mpr hv)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
