import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatchCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback

/-!
# Full-patch comparisons of the native canonical bundles

The global canonical fibre over a point of any actual piece pulls back
isomorphically to that piece's native canonical fibre.  These comparisons
are defined through the actual manifold derivative.  Their inverses give
injective maps of bundle total spaces whose ranges are precisely the full
inverse-image patches in the global canonical bundle.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace localPieceChartedSpace
  localPiece_nonempty localPiece_isManifold

local instance patchesGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The native canonical bundle of the actual piece in the common model. -/
abbrev localBundle (i : Index) := Atlas.core (localPiece i)

theorem localBundle_holomorphic (i : Index) :
    ContMDiffVectorBundle ω ℂ (localBundle i).Fiber IF :=
  Atlas.holomorphicVectorBundle (localPiece i)

def localIntrinsicEquiv (i : Index) (x : localPiece i) :
    (localBundle i).Fiber x ≃L[ℂ] (TangentSpace IF x) [⋀^(Fin 3)]→L[ℂ] ℂ :=
  Atlas.intrinsicEquiv (localPiece i) x

/-- Pullback along the actual full piece inclusion, on genuine fibres. -/
def patchPullback (i : Index) (x : localPiece i) :
    bundle.Fiber (Threefold.inclusion i x) ≃L[ℂ] (localBundle i).Fiber x :=
  Pullback.pullbackEquiv (inclusion_isLocalDiffeomorph i) x

theorem patchPullback_intrinsic (i : Index) (x : localPiece i)
    (v : bundle.Fiber (Threefold.inclusion i x)) :
    localIntrinsicEquiv i x (patchPullback i x v) =
      (intrinsicEquiv (Threefold.inclusion i x) v).compContinuousLinearMap
        (mfderiv IF IF (Threefold.inclusion i) x) :=
  Pullback.intrinsic_pullbackEquiv (inclusion_isLocalDiffeomorph i) x v

theorem patchPullback_preferred_coefficient (i : Index) (x : localPiece i)
    (v : bundle.Fiber (Threefold.inclusion i x)) :
    id (α := ℂ) (patchPullback i x v) =
      LinearMap.det (mfderiv IF IF (Threefold.inclusion i) x).toLinearMap * id (α := ℂ) v :=
  Pullback.pullbackLinear_preferred_coefficient (Threefold.inclusion i) x v

/-- The inverse comparison is inverse pullback of actual tangent covectors. -/
theorem patchPullback_symm_intrinsic (i : Index) (x : localPiece i)
    (v : (localBundle i).Fiber x) :
    intrinsicEquiv (Threefold.inclusion i x) ((patchPullback i x).symm v) =
      (localIntrinsicEquiv i x v).compContinuousLinearMap
        ((inclusion_isLocalDiffeomorph i x).mfderivToContinuousLinearEquiv
          (by simp)).symm.toContinuousLinearMap :=
  Pullback.intrinsic_pullbackEquivAt_symm (inclusion_isLocalDiffeomorph i x) v

/-- The map over the actual inclusion is fibrewise the inverse of genuine
canonical pullback, not a scalar chosen independently of the derivative. -/
def patchPushforward (i : Index) (p : (localBundle i).TotalSpace) : bundle.TotalSpace :=
  ⟨Threefold.inclusion i p.proj, (patchPullback i p.proj).symm p.2⟩

@[simp] theorem patchPushforward_proj (i : Index) (p : (localBundle i).TotalSpace) :
    (patchPushforward i p).proj = Threefold.inclusion i p.proj := rfl

theorem patchPushforward_add (i : Index) (x : localPiece i)
    (v w : (localBundle i).Fiber x) :
    id (α := ℂ) (patchPushforward i ⟨x, v + w⟩).2 =
      id (α := ℂ) (patchPushforward i ⟨x, v⟩).2 +
        id (α := ℂ) (patchPushforward i ⟨x, w⟩).2 :=
  (patchPullback i x).symm.map_add v w

theorem patchPushforward_smul (i : Index) (x : localPiece i)
    (c : ℂ) (v : (localBundle i).Fiber x) :
    id (α := ℂ) (patchPushforward i ⟨x, c • v⟩).2 =
      c • id (α := ℂ) (patchPushforward i ⟨x, v⟩).2 :=
  (patchPullback i x).symm.map_smul c v

theorem patchPushforward_injective (i : Index) : Function.Injective (patchPushforward i) := by
  intro p q h
  obtain ⟨x, v⟩ := p
  obtain ⟨y, w⟩ := q
  have hb : Threefold.inclusion i x = Threefold.inclusion i y :=
    congrArg Bundle.TotalSpace.proj h
  have hxy := (Threefold.inclusion_openEmbedding i).injective hb
  subst y
  have hv : (patchPullback i x).symm v = (patchPullback i x).symm w :=
    congrArg (fun q : bundle.TotalSpace => id (α := ℂ) q.2) h
  have hvw := (patchPullback i x).symm.injective hv
  subst w
  rfl

theorem patchPushforward_range (i : Index) :
    range (patchPushforward i) =
      (Bundle.TotalSpace.proj : bundle.TotalSpace → Threefold.Space) ⁻¹'
        (Threefold.liftedPatch i : Set Threefold.Space) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (Threefold.patchBiholomorph i q.proj).property
  · intro hp
    obtain ⟨y, v⟩ := p
    have hy : y ∈ range (Threefold.inclusion i) := by
      rw [Threefold.inclusion_range]
      exact hp
    obtain ⟨x, hx⟩ := hy
    subst y
    refine ⟨⟨x, patchPullback i x v⟩, ?_⟩
    simp only [patchPushforward, ContinuousLinearEquiv.symm_apply_apply]

/-- Equality of global base points gives the usual transport of their
actual canonical fibres. -/
def fibreTransport {x y : Threefold.Space} (h : x = y) : bundle.Fiber x ≃L[ℂ] bundle.Fiber y := by
  subst y
  exact ContinuousLinearEquiv.refl ℂ (bundle.Fiber x)

theorem intrinsicEquiv_fibreTransport {x y : Threefold.Space} (h : x = y)
    (v : bundle.Fiber x) :
    (intrinsicEquiv y (fibreTransport h v) : TopCovector) = intrinsicEquiv x v := by
  subst y
  rfl

/-- The covector gluing rule is the bundle comparison's native
contravariant composition on the actual full overlap. -/
theorem patchPullback_gluing (i j : Index) (x : localPiece i)
    (hx : x ∈ (gluingData.transition i j).source)
    (v : bundle.Fiber (Threefold.inclusion i x)) :
    patchPullback i x v = Pullback.pullbackLinear (gluingData.transition i j) x
      (patchPullback j (gluingData.transition i j x)
        (fibreTransport (inclusion_transition i j x hx).symm v)) := by
  apply (localIntrinsicEquiv i x).injective
  rw [patchPullback_intrinsic]
  change _ = Atlas.intrinsicEquiv (localPiece i) x
    (Pullback.pullbackLinear (gluingData.transition i j) x
      (patchPullback j (gluingData.transition i j x)
        (fibreTransport (inclusion_transition i j x hx).symm v)))
  rw [Pullback.intrinsic_pullbackLinear]
  change _ = (localIntrinsicEquiv j (gluingData.transition i j x)
    (patchPullback j (gluingData.transition i j x)
      (fibreTransport (inclusion_transition i j x hx).symm v))).compContinuousLinearMap _
  rw [patchPullback_intrinsic, intrinsicEquiv_fibreTransport]
  exact topCovector_gluing i j x hx (intrinsicEquiv (Threefold.inclusion i x) v)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
