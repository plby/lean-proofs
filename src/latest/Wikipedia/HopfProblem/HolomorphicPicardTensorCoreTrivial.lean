import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# The actual zero-cocycle bundle is the analytic product bundle

Every original transition of the zero unit cocycle is one.  Hence the
original core's local coordinates are literally the preferred fibre
coordinates.  Checking the two coordinate maps in that original atlas
gives an analytic diffeomorphism with the product and a fibre-linear
analytic isomorphism with mathlib's genuine trivial bundle.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorCore

open HolomorphicExponentialSheaf HolomorphicPicardNative
open HolomorphicFunctionSheaf.SphereH1
open PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Z" => cocycleCore I M U hcover (0 : CechOneCocycle (unitsSheaf I M) U)

/-- Each original zero-cocycle chart is the identity on fibre coordinates,
including the chosen extension away from its base set. -/
@[simp] theorem zero_localTriv_apply (i : ι) (p : (Z).TotalSpace) :
    (Z).localTriv i p = (p.proj, id (α := ℂ) p.2) := by
  change (p.proj,
    ((cocycleTransitionData I M U hcover 0).transition _ i p.proj : ℂ) *
      id (α := ℂ) p.2) = _
  simp only [data_zero_transition, Units.val_one, one_mul]

/-- The original preferred chart also has literal identity coordinates. -/
@[simp] theorem zero_trivializationAt_apply (x : M) (p : (Z).TotalSpace) :
    trivializationAt ℂ (Z).Fiber x p = (p.proj, id (α := ℂ) p.2) := by
  change (Z).localTriv ((Z).indexAt x) p = _
  exact zero_localTriv_apply I M U hcover _ p

/-- Analyticity of the preferred fibre coordinate is proved using the
original core atlas, not a transported product topology. -/
theorem zero_fiberCoordinate_holomorphic :
    ContMDiff (I.prod I₁) I₁ ω (fun p : (Z).TotalSpace => id (α := ℂ) p.2) := by
  intro p
  have h := (Bundle.contMDiffAt_totalSpace.mp
    (contMDiffAt_id : ContMDiffAt (I.prod I₁) (I.prod I₁) ω
      (id : (Z).TotalSpace → (Z).TotalSpace) p)).2
  simpa only [id_eq, zero_trivializationAt_apply] using h

/-- The literal coordinate map from the original core to the product. -/
def zeroToProduct (p : (Z).TotalSpace) : M × ℂ :=
  (p.proj, id (α := ℂ) p.2)

/-- The inverse literal coordinate map into the original glued topology. -/
def zeroFromProduct (p : M × ℂ) : (Z).TotalSpace := ⟨p.1, p.2⟩

theorem zeroToProduct_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (zeroToProduct I M U hcover) :=
  (Bundle.contMDiff_proj (Z).Fiber).prodMk
    (zero_fiberCoordinate_holomorphic I M U hcover)

theorem zeroFromProduct_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (zeroFromProduct I M U hcover) := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  simpa only [zero_trivializationAt_apply, zeroFromProduct, id_eq] using
    (contMDiffAt_snd : ContMDiffAt (I.prod I₁) I₁ ω (Prod.snd : M × ℂ → ℂ) p)

/-- An actual analytic diffeomorphism between the zero-cocycle core's
original total space and the ordinary Cartesian product. -/
def zeroProductDiffeomorph :
    Diffeomorph (I.prod I₁) (I.prod I₁) (Z).TotalSpace (M × ℂ) ω where
  toFun := zeroToProduct I M U hcover
  invFun := zeroFromProduct I M U hcover
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  contMDiff_toFun := zeroToProduct_holomorphic I M U hcover
  contMDiff_invFun := zeroFromProduct_holomorphic I M U hcover

@[simp] theorem zeroProductDiffeomorph_apply (p : (Z).TotalSpace) :
    zeroProductDiffeomorph I M U hcover p = (p.proj, id (α := ℂ) p.2) := rfl

@[simp] theorem zeroProductDiffeomorph_symm_apply (p : M × ℂ) :
    (zeroProductDiffeomorph I M U hcover).symm p = ⟨p.1, p.2⟩ := rfl

/-- The fibre equivalence to the genuine trivial bundle is literally the
identity complex-linear map. -/
def zeroTrivialFiberEquiv (x : M) : (Z).Fiber x ≃ₗ[ℂ] Bundle.Trivial M ℂ x :=
  LinearEquiv.refl ℂ ℂ

theorem zeroToTrivial_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω
      (fun p : (Z).TotalSpace =>
        (⟨p.proj, zeroTrivialFiberEquiv I M U hcover p.proj p.2⟩ :
          TotalSpace ℂ (Bundle.Trivial M ℂ))) := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨Bundle.contMDiffAt_proj (Z).Fiber, ?_⟩
  exact (zero_fiberCoordinate_holomorphic I M U hcover).contMDiffAt

theorem zeroFromTrivial_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω
      (fun p : TotalSpace ℂ (Bundle.Trivial M ℂ) =>
        (⟨p.proj, (zeroTrivialFiberEquiv I M U hcover p.proj).symm p.2⟩ :
          (Z).TotalSpace)) := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨Bundle.contMDiffAt_proj (Bundle.Trivial M ℂ), ?_⟩
  have h := (Bundle.contMDiffAt_totalSpace.mp
    (contMDiffAt_id : ContMDiffAt (I.prod I₁) (I.prod I₁) ω
      (id : TotalSpace ℂ (Bundle.Trivial M ℂ) →
        TotalSpace ℂ (Bundle.Trivial M ℂ)) p)).2
  change ContMDiffAt (I.prod I₁) I₁ ω
    (fun q : TotalSpace ℂ (Bundle.Trivial M ℂ) => id (α := ℂ) q.2) p at h
  simp only [zero_trivializationAt_apply]
  change ContMDiffAt (I.prod I₁) I₁ ω
    (fun q : TotalSpace ℂ (Bundle.Trivial M ℂ) => id (α := ℂ) q.2) p
  exact h

/-- The zero actual unit cocycle glues to the genuine trivial line bundle
by an analytic fibre-linear isomorphism on the original native topologies. -/
def zeroTrivialIso : AnalyticBundleIso I (Z).Fiber (Bundle.Trivial M ℂ) :=
  AnalyticBundleIso.ofFiberEquiv (zeroTrivialFiberEquiv I M U hcover)
    (zeroToTrivial_holomorphic I M U hcover)
    (zeroFromTrivial_holomorphic I M U hcover)

@[simp] theorem zeroTrivialIso_apply (p : (Z).TotalSpace) :
    (zeroTrivialIso I M U hcover).diffeomorph p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem zeroTrivialIso_symm_apply (p : TotalSpace ℂ (Bundle.Trivial M ℂ)) :
    (zeroTrivialIso I M U hcover).diffeomorph.symm p = ⟨p.proj, p.2⟩ := rfl

@[simp] theorem zeroTrivialIso_fiberEquiv_apply (x : M) (v : (Z).Fiber x) :
    (zeroTrivialIso I M U hcover).fiberEquiv x v = id (α := ℂ) v := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.TensorCore
