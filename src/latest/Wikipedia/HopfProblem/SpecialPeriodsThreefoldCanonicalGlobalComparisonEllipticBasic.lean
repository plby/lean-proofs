import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorIdentificationBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonicalSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonPatches
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# The actual prescribed-to-canonical map on the elliptic patch

On the full order-four patch the pulled-back base line uses its finite
frame.  Thus the prescribed tensor line has exactly the effective-divisor
line's coefficients in the corresponding original charts.  Its map to
the native canonical presentation is the already constructed divisor
comparison multiplied by the actual descended elliptic comparison unit.
The preferred multiplier is extended by one outside this patch; no
holomorphicity of that preferred scalar extension is asserted.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic

open TrianglePeriodFamily.Canonical
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace

local instance ellipticComparisonBasicManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

abbrev sourceData := GlobalPrescribedDivisor.cartier.transitions
abbrev targetData := NativePresentation.transitionData
abbrev sourceBundle := GlobalPrescribedDivisor.bundle
abbrev targetBundle := NativePresentation.transitionBundle
abbrev patch := GlobalEllipticDivisor.patch

/-- The actual descended nonvanishing elliptic coefficient, as a unit. -/
def patchRatioUnit (x : patch) : ℂˣ :=
  Units.mk0 (GlobalEllipticComparison.patchRatio .four x)
    (GlobalEllipticComparison.patchRatio_ne_zero .four x)

@[simp] theorem patchRatioUnit_val (x : patch) :
    (patchRatioUnit x : ℂ) = GlobalEllipticComparison.patchRatio .four x := rfl

/-- A scalar extension used only on the actual elliptic patch. -/
def ratioExtension (x : Threefold.Space) : ℂ := by
  classical
  exact if hx : x ∈ patch then GlobalEllipticComparison.patchRatio .four ⟨x, hx⟩ else 1

theorem ratioExtension_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    ratioExtension x = GlobalEllipticComparison.patchRatio .four ⟨x, hx⟩ := by
  simp only [ratioExtension, dif_pos hx]

theorem ratioExtension_ne_zero (x : Threefold.Space) : ratioExtension x ≠ 0 := by
  classical
  by_cases hx : x ∈ patch
  · rw [ratioExtension_of_mem hx]
    exact GlobalEllipticComparison.patchRatio_ne_zero .four ⟨x, hx⟩
  · simp only [ratioExtension, dif_neg hx]
    exact one_ne_zero

/-- The genuine preferred-fibre multiplier on the entire elliptic patch.
Its value off the patch is irrelevant to the local comparison. -/
def preferredUnit (x : Threefold.Space) : ℂˣ := by
  classical
  exact if hx : x ∈ patch then patchRatioUnit ⟨x, hx⟩ * GlobalEllipticDivisor.patchWeight x
    else 1

theorem preferredUnit_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    preferredUnit x = patchRatioUnit ⟨x, hx⟩ * GlobalEllipticDivisor.patchWeight x := by
  simp only [preferredUnit, dif_pos hx]

theorem preferredUnit_val_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    (preferredUnit x : ℂ) = ratioExtension x * (GlobalEllipticDivisor.patchWeight x : ℂ) := by
  rw [preferredUnit_of_mem hx, Units.val_mul, patchRatioUnit_val, ratioExtension_of_mem hx]
  rfl

theorem preferredUnit_of_not_mem {x : Threefold.Space} (hx : x ∉ patch) :
    preferredUnit x = 1 := by
  simp only [preferredUnit, dif_neg hx]

/-- The original prescribed bundle's preferred base frame is the finite
one at every point of the full elliptic patch. -/
theorem source_indexAt_of_finite {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    sourceData.indexAt x = (false, GlobalEllipticDivisor.transitions.indexAt x) := by
  change (CanonicalGlobal.BaseTwist.indexAt (Threefold.projectionSphere x),
    GlobalEllipticDivisor.indexAt x) = (false, GlobalEllipticDivisor.indexAt x)
  simp only [CanonicalGlobal.BaseTwist.indexAt, if_neg hx]

theorem source_indexAt_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    sourceData.indexAt x = (false, GlobalEllipticDivisor.transitions.indexAt x) :=
  source_indexAt_of_finite (GlobalPrescribedDivisor.fourPatch_projection_ne_infty hx)

/-- Every finite-frame source coefficient is literally a coefficient of
the independently constructed effective-divisor bundle. -/
theorem source_localTriv_finite (i : GlobalEllipticDivisor.Index)
    (p : sourceBundle.TotalSpace)
    (hp : Threefold.projectionSphere p.proj ≠ (∞ : RiemannSphere)) :
    (sourceBundle.localTriv (false, i) p).2 =
      (GlobalEllipticDivisor.divisorBundle.localTriv i
        ⟨p.proj, id (α := ℂ) p.2⟩).2 := by
  change (sourceData.transition (sourceData.indexAt p.proj) (false, i) p.proj : ℂ) *
    id (α := ℂ) p.2 =
      (GlobalEllipticDivisor.transition (GlobalEllipticDivisor.indexAt p.proj) i p.proj : ℂ) *
        id (α := ℂ) p.2
  rw [source_indexAt_of_finite hp]
  change ((CanonicalGlobal.BaseTwist.transition false false (Threefold.projectionSphere p.proj) *
    GlobalEllipticDivisor.transition (GlobalEllipticDivisor.indexAt p.proj) i p.proj : ℂˣ) : ℂ) *
      id (α := ℂ) p.2 = _
  rw [CanonicalGlobal.BaseTwist.transition_self, one_mul]

theorem source_chart_mem (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : x ∈ patch) (hi : x ∈ i.val.source) :
    x ∈ sourceData.baseSet (false, some i) := by
  change Threefold.projectionSphere x ∈ finiteChart ∧
    x ∈ (patch : Set Threefold.Space) ∩ i.val.source
  exact ⟨(mem_finiteChart _).mpr (GlobalPrescribedDivisor.fourPatch_projection_ne_infty hx), hx, hi⟩

/-- The actual total-space map between the two independently constructed
original holomorphic line bundles. -/
def totalMap : sourceBundle.TotalSpace → targetBundle.TotalSpace :=
  CanonicalGlobalLineBundle.OpenMaps.preferredMap sourceData targetData preferredUnit

/-- Its map on every literal fibre is a continuous complex-linear equivalence. -/
def fiberEquiv (x : Threefold.Space) : sourceBundle.Fiber x ≃L[ℂ] targetBundle.Fiber x :=
  CanonicalGlobalLineBundle.OpenMaps.fiberEquiv sourceData targetData preferredUnit x

@[simp] theorem totalMap_proj (p : sourceBundle.TotalSpace) : (totalMap p).proj = p.proj := rfl

@[simp] theorem totalMap_mk (x : Threefold.Space) (v : sourceBundle.Fiber x) :
    totalMap ⟨x, v⟩ = ⟨x, fiberEquiv x v⟩ := rfl

@[simp] theorem fiberEquiv_apply (x : Threefold.Space) (v : sourceBundle.Fiber x) :
    fiberEquiv x v = (preferredUnit x : ℂ) * id (α := ℂ) v := rfl

/-- In the original matched charts the map is exactly multiplication by
the actual holomorphic elliptic ratio, including over the central zeros. -/
theorem totalMap_localTriv (i : atlas Model Threefold.Space) (p : sourceBundle.TotalSpace)
    (hp : p.proj ∈ patch) (hi : p.proj ∈ i.val.source) :
    (targetBundle.localTriv i (totalMap p)).2 =
      ratioExtension p.proj * (sourceBundle.localTriv (false, some i) p).2 := by
  rw [source_localTriv_finite (some i) p
    (GlobalPrescribedDivisor.fourPatch_projection_ne_infty hp)]
  change (NativeTransitions.transition Threefold.Space (achart Model p.proj) i p.proj : ℂ) *
    ((preferredUnit p.proj : ℂ) * id (α := ℂ) p.2) =
      ratioExtension p.proj *
        ((GlobalEllipticDivisor.transition (GlobalEllipticDivisor.indexAt p.proj)
          (some i) p.proj : ℂ) * id (α := ℂ) p.2)
  rw [preferredUnit_val_of_mem hp, ← GlobalEllipticDivisor.patchWeight_change i hp hi]
  ring

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic
