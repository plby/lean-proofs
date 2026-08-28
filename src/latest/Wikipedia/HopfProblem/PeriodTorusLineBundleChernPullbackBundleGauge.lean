import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundleQuotient
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundleCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundlePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# The actual cross-cover gauge for a pulled-back factor

The source factor bundle and the pullback of the target transition data
use independent covers and independently chosen lifts.  Their difference
is the actual target-lattice translation.  Evaluating the original factor
at that translation gives the holomorphic cross-cover gauge, whose native
bundle isomorphism realizes the map `(z,c) ↦ (L z,c)` on orbit quotients.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open CanonicalGlobalLineBundle

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (F : FactorOfAutomorphy q)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The existing target transition data pulled back along the genuine descended map. -/
abbrev pullbackTransitionData : HolomorphicCharacterBundle.TransitionData p.Torus q.Torus :=
  CanonicalGlobalLineBundle.pullback (Core.data F)
    (L.torusMap : p.Torus → q.Torus) L.torusMap.contMDiff.continuous

instance pullbackTransitionData_isHolomorphic : (pullbackTransitionData L F).IsHolomorphic IC :=
  CanonicalGlobalLineBundle.pullback_isHolomorphic (Core.data F)
    (L.torusMap : p.Torus → q.Torus) L.torusMap.contMDiff.continuous IC IC L.torusMap.contMDiff

/-- The factor at the actual difference between the two chosen lifts. -/
def pullbackGaugeValue (i : p.Torus × q.Torus) (x : p.Torus) : ℂˣ :=
  F.factor (pullbackCrossDeck L i x) (L.linear (Core.lift p i.1 x))

theorem pullbackGaugeValue_holomorphic (i : p.Torus × q.Torus) :
    ContMDiffOn IC I₁ ω (fun x => (pullbackGaugeValue L F i x : ℂ))
      (pullbackCrossBaseSet L i) := by
  intro x hx
  have hlift := (Core.lift_holomorphic p i.1).contMDiffAt
    ((Core.isOpen_baseSet p i.1).mem_nhds hx.1)
  have hlin : ContMDiffAt IC IC ω (fun y => L.linear (Core.lift p i.1 y)) x :=
    L.linear.contDiff.contMDiff.contMDiffAt.comp x hlift
  have hnear : (fun y => (pullbackGaugeValue L F i y : ℂ)) =ᶠ[𝓝 x]
      (fun y => (F.factor (pullbackCrossDeck L i x)
        (L.linear (Core.lift p i.1 y)) : ℂ)) := by
    filter_upwards [pullbackCrossDeck_locally_constant L i hx] with y hy
    change (F.factor (pullbackCrossDeck L i y) (L.linear (Core.lift p i.1 y)) : ℂ) = _
    rw [hy]
  exact (((F.holomorphic_factor (pullbackCrossDeck L i x)).contMDiff.contMDiffAt.comp
    x hlin).congr_of_eventuallyEq hnear).contMDiffWithinAt

/-- The actual cross-cover comparison, derived from the original factor cocycle law. -/
def pullbackCrossGauge : CrossGauge IC (Core.data (pullbackFactor L F))
    (pullbackTransitionData L F) where
  value := pullbackGaugeValue L F
  compatible i j x hx := by
    change x ∈ pullbackCrossBaseSet L i ∩ pullbackCrossBaseSet L j at hx
    have hp : x ∈ Core.baseSet p i.1 ∩ Core.baseSet p j.1 := ⟨hx.1.1, hx.2.1⟩
    have hsource : L.linear (Core.lift p i.1 x) +
        (L.latticeMap (Core.deck p i.1 j.1 x) : ComplexPlane₂) =
          L.linear (Core.lift p j.1 x) := by
      rw [← L.linear_add_lattice, Core.deck_spec p i.1 j.1 hp]
    change F.factor (Core.deck q i.2 j.2 (L.torusMap x)) (Core.lift q i.2 (L.torusMap x)) *
        F.factor (pullbackCrossDeck L i x) (L.linear (Core.lift p i.1 x)) =
      F.factor (pullbackCrossDeck L j x) (L.linear (Core.lift p j.1 x)) *
        F.factor (L.latticeMap (Core.deck p i.1 j.1 x)) (L.linear (Core.lift p i.1 x))
    calc
      _ = F.factor (Core.deck q i.2 j.2 (L.torusMap x) + pullbackCrossDeck L i x)
          (L.linear (Core.lift p i.1 x)) := by
        rw [F.factor_add, pullbackCrossDeck_spec L i hx.1]
      _ = F.factor (pullbackCrossDeck L j x + L.latticeMap (Core.deck p i.1 j.1 x))
          (L.linear (Core.lift p i.1 x)) := by
        rw [pullbackCrossDeck_compatible L i j hx]
      _ = _ := by rw [F.factor_add, hsource]
  holomorphicOn := pullbackGaugeValue_holomorphic L F

/-- The actual native source bundle is analytically the pulled-back transition core. -/
def pullbackCoreIso : AnalyticBundleIso IC (Core.data (pullbackFactor L F)).core.Fiber
    (pullbackTransitionData L F).core.Fiber where
  diffeomorph := (pullbackCrossGauge L F).diffeomorph
  fiberEquiv x := ((pullbackCrossGauge L F).fiberEquiv x).toLinearEquiv
  map_fiber x v := (pullbackCrossGauge L F).diffeomorph_mk x v

/-- The native cross-gauge realizes exactly the independently constructed orbit-quotient map. -/
theorem pullbackCoreIso_toAssociated (u : (Core.data (pullbackFactor L F)).core.TotalSpace) :
    Core.toAssociated F
        (CanonicalGlobalLineBundle.pullbackTotalMap (Core.data F)
          (L.torusMap : p.Torus → q.Torus) L.torusMap.contMDiff.continuous
          ((pullbackCoreIso L F).diffeomorph u)) =
      pullbackAssociatedMap L F (Core.toAssociated (pullbackFactor L F) u) := by
  rcases u with ⟨x, c⟩
  rw [(pullbackCoreIso L F).map_fiber]
  change associatedMap F (Core.lift q (L.torusMap x) (L.torusMap x),
      (pullbackCrossGauge L F).fiberEquiv x c) =
    associatedMap F (L.linear (Core.lift p x x), id (α := ℂ) c)
  rw [CrossGauge.fiberEquiv_apply]
  change associatedMap F (Core.lift q (L.torusMap x) (L.torusMap x),
      (F.factor (pullbackCrossDeck L (x, L.torusMap x) x)
        (L.linear (Core.lift p x x)) : ℂ) * id (α := ℂ) c) = _
  have hx : x ∈ pullbackCrossBaseSet L (x, L.torusMap x) :=
    ⟨Core.mem_baseSet p x, Core.mem_baseSet q (L.torusMap x)⟩
  rw [← pullbackCrossDeck_spec L (x, L.torusMap x) hx]
  exact associatedMap_diagonal F (pullbackCrossDeck L (x, L.torusMap x) x)
    (L.linear (Core.lift p x x), id (α := ℂ) c)

/-- Forgetting the source base point gives the literal native map induced by `(z,c) ↦ (Lz,c)`. -/
theorem pullbackCoreIso_totalMap (u : (Core.data (pullbackFactor L F)).core.TotalSpace) :
    CanonicalGlobalLineBundle.pullbackTotalMap (Core.data F)
        (L.torusMap : p.Torus → q.Torus) L.torusMap.contMDiff.continuous
        ((pullbackCoreIso L F).diffeomorph u) =
      Core.fromAssociated F
        (pullbackAssociatedMap L F (Core.toAssociated (pullbackFactor L F) u)) := by
  apply Core.toAssociated_injective F
  rw [pullbackCoreIso_toAssociated, Core.toAssociated_fromAssociated]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
