import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingGlobalPaths
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingGlobalTransport
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttaching

/-!
# The actual elliptic attaching relation at the global marked basepoint

A genuine path upstairs joins the canonical regular base lift to the
local logarithmic base lift.  Its zero-section image transports the
actual attaching loops into the native fundamental group of the glued
threefold.  The positive fibre loop retains exactly the original integral
column, so the local power relation becomes the corresponding global
marked-lattice relation.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge TrianglePeriodFamily CuspUniformization
open FundamentalGroup

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "bsp" => Meridians.normalizedRegularMeridianBasepoint

/-- The included positive fibre loop is the same source-column loop in the regular family. -/
theorem includedAttachingFibreLoop_eq_column (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    includedAttachingFibreLoop j s₀ hs₀ hr w =
      globalColumnLoop (attachingUpstairsPoint j s₀ hs₀ 0) w := by
  ext t
  rw [globalColumnLoop_apply]
  exact (inclusion_eq_regular_overlap j (attachingFibreLoop j s₀ hs₀ hr w t)
    (attachingFibreLoop_mem_overlap j s₀ hs₀ hr w t)).trans
      (congrArg regularFamilyInclusionMap
        (specialEllipticOverlap_attachingFibreLoop j s₀ hs₀ hr w t))

/-- A genuine upstairs path fixes a single unchanged source-column marking. -/
def attachingUpstairsTail (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path bsp (attachingUpstairsPoint j s₀ hs₀ 0) :=
  PathConnectedSpace.somePath _ _

/-- The projected actual base tail, independent of the lattice column. -/
def attachingBaseTail (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (triangleRegularProject bsp)
      (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)) :=
  (attachingUpstairsTail j s₀ hs₀).map triangleRegularProject_covering.continuous

/-- The global tail is literally the zero-section image of that upstairs path. -/
def attachingGlobalTail (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path PiOne.basepoint
      (regularFamilyInclusionMap
        ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  upstairsPathGlobalTail (attachingUpstairsTail j s₀ hs₀)

theorem attachingGlobalTail_eq_zeroSection (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingGlobalTail j s₀ hs₀ =
      ((attachingBaseTail j s₀ hs₀).map (Dsp).zeroSection_continuous).map
        regularFamilyInclusionMap.continuous := by
  ext t
  rfl

/-- Include a local loop, cast by the actual gluing equality, and transport
it along the one displayed global zero-section tail. -/
def attachingTransportHom (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    FundamentalGroup (LocalSpace j) (attachingBasepoint j s₀ hs₀ hr) →* PiOne.GlobalGroup :=
  (fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm).toMonoidHom.comp
    ((MulEquiv.cast (M := FundamentalGroup Threefold.Space)
      (attachingGlobalBasepoint_eq j s₀ hs₀ hr)).toMonoidHom.comp
        (FundamentalGroup.map (attachingPieceInclusionMap j) (attachingBasepoint j s₀ hs₀ hr)))

theorem attachingTransportHom_fromPath (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (γ : Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr)) :
    attachingTransportHom j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦γ⟧) =
      fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
        (FundamentalGroup.fromPath
          ⟦(γ.map (inclusion_continuous j)).cast (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm
            (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm⟧) := by
  change fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
    (MulEquiv.cast (M := FundamentalGroup Threefold.Space)
      (attachingGlobalBasepoint_eq j s₀ hs₀ hr)
      (FundamentalGroup.fromPath ⟦γ.map (inclusion_continuous j)⟧)) = _
  rw [fundamentalGroup_cast_loop]

/-- Transport of the included fibre loop keeps exactly the same integral column. -/
theorem attachingTransportHom_fibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    attachingTransportHom j s₀ hs₀ hr
      (FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr w⟧) =
        PiOne.latticeHom (Multiplicative.ofAdd w) := by
  rw [attachingTransportHom_fromPath]
  change fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
    (FundamentalGroup.fromPath ⟦includedAttachingFibreLoop j s₀ hs₀ hr w⟧) = _
  rw [includedAttachingFibreLoop_eq_column]
  exact transport_globalColumnLoop (attachingUpstairsTail j s₀ hs₀) w

/-- The actual globally based logarithmic meridian path. -/
def transportedAttachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path PiOne.basepoint PiOne.basepoint :=
  (attachingGlobalTail j s₀ hs₀).trans
    ((includedAttachingLoop j s₀ hs₀ hr).trans (attachingGlobalTail j s₀ hs₀).symm)

/-- The same loop class expressed through the actual induced homomorphism. -/
def transportedAttachingClass (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) : PiOne.GlobalGroup :=
  attachingTransportHom j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧)

theorem transportedAttachingClass_fromPath (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    transportedAttachingClass j s₀ hs₀ hr =
      FundamentalGroup.fromPath ⟦transportedAttachingLoop j s₀ hs₀ hr⟧ := by
  rw [transportedAttachingClass, attachingTransportHom_fromPath]
  change fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
    (Path.Homotopic.Quotient.mk (includedAttachingLoop j s₀ hs₀ hr)) = _
  rw [fundamentalGroup_basepoint_change_mk, Path.symm_symm]
  rfl

/-- The underlying globally based regular-base loop uses precisely the same tail. -/
def transportedAttachingBaseLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path (triangleRegularProject bsp) (triangleRegularProject bsp) :=
  (attachingBaseTail j s₀ hs₀).trans
    ((attachingRegularBaseLoop j s₀ hs₀ hr).trans (attachingBaseTail j s₀ hs₀).symm)

/-- The global attaching path is exactly the zero-section image of its displayed base loop. -/
private theorem map_twice_tail {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {a b : X} (p : Path a b) (q : Path b b)
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    ((p.trans (q.trans p.symm)).map hf).map hg =
      ((p.map hf).map hg).trans
        (((q.map hf).map hg).trans ((p.map hf).map hg).symm) := by
  simp only [Path.map_trans, Path.map_symm]

/-- The global attaching path is exactly the zero-section image of its displayed base loop. -/
theorem transportedAttachingLoop_eq_zeroSection (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    transportedAttachingLoop j s₀ hs₀ hr =
      ((transportedAttachingBaseLoop j s₀ hs₀ hr).map (Dsp).zeroSection_continuous).map
        regularFamilyInclusionMap.continuous := by
  simp only [transportedAttachingLoop, transportedAttachingBaseLoop]
  rw [attachingGlobalTail_eq_zeroSection, includedAttachingLoop_eq_regular,
    attachingRegularLoop_eq_zeroSection]
  exact (map_twice_tail (attachingBaseTail j s₀ hs₀)
    (attachingRegularBaseLoop j s₀ hs₀ hr) (Dsp).zeroSection_continuous
    regularFamilyInclusionMap.continuous).symm

/-- The actual zero-section homomorphism followed by inclusion into the glued space. -/
def attachingBaseSectionHom :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject bsp) →*
      PiOne.GlobalGroup :=
  PiOne.regularHom.comp ((Dsp).sectionFundamentalGroupHom bsp)

theorem attachingBaseSectionHom_fromPath
    (γ : Path (triangleRegularProject bsp) (triangleRegularProject bsp)) :
    attachingBaseSectionHom (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath
        ⟦(γ.map (Dsp).zeroSection_continuous).map regularFamilyInclusionMap.continuous⟧ := rfl

/-- The transported class is the actual section image of the displayed based loop. -/
theorem transportedAttachingClass_eq_baseImage (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    transportedAttachingClass j s₀ hs₀ hr =
      attachingBaseSectionHom
        (FundamentalGroup.fromPath ⟦transportedAttachingBaseLoop j s₀ hs₀ hr⟧) := by
  rw [transportedAttachingClass_fromPath, transportedAttachingLoop_eq_zeroSection]
  rfl

/-- The local geometric power relation becomes the actual global marked-column relation. -/
theorem transportedAttachingClass_pow_order (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    transportedAttachingClass j s₀ hs₀ hr ^ j.order =
      PiOne.latticeHom (Multiplicative.ofAdd j.twist) := by
  change (attachingTransportHom j s₀ hs₀ hr
    (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧)) ^ j.order = _
  rw [← map_pow, attachingLoop_pow_order, attachingTransportHom_fibreLoop]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
