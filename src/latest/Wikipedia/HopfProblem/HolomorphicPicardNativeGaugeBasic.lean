import Wikipedia.HopfProblem.HolomorphicPicardNativeCocycle
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# Fibrewise gluing of an actual holomorphic gauge on a common refinement

A nowhere-zero holomorphic scalar gauge between the original native
transition functions gives compatible local complex-linear equivalences.
Their actual compatibility makes the fibre equivalence independent of the
chosen member of the covering family.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative

variable {M : Type*} [TopologicalSpace M] (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- The actual native coordinate-change identity, applied to a vector in
the original fibre. -/
theorem native_coordinates (i j x : M)
    (hi : x ∈ (nativeTriv V i).baseSet) (hj : x ∈ (nativeTriv V j).baseSet) (v : V x) :
    (nativeTriv V j ⟨x, v⟩).2 =
      (scalarTransition V i j x : ℂ) * (nativeTriv V i ⟨x, v⟩).2 := by
  calc
    _ = (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x
        ((nativeTriv V i).linearEquivAt ℂ x hi v) := by
      rw [Trivialization.coe_coordChangeL _ _ ⟨hi, hj⟩]
      change (nativeTriv V j).linearEquivAt ℂ x hj v =
        (nativeTriv V j).linearEquivAt ℂ x hj
          (((nativeTriv V i).linearEquivAt ℂ x hi).symm
            ((nativeTriv V i).linearEquivAt ℂ x hi v))
      rw [LinearEquiv.symm_apply_apply]
    _ = _ := coordChange_apply V i j x _

end Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge

namespace Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    {ι : Type} (U : ι → Opens M) (r s : ι → M)
    (hV : ∀ i, U i ≤ nativeCover M V (r i))
    (hW : ∀ i, U i ≤ nativeCover M W (s i))
    (b : ∀ i, UnitSection I M (U i))

/-- The local map in the original native fibres, with the given gauge as
its literal scalar coordinate. -/
def localFiberEquiv (i : ι) (x : U i) : V x ≃ₗ[ℂ] W x :=
  ((nativeTriv V (r i)).linearEquivAt ℂ x (hV i x.property)).trans
    ((LinearEquiv.smulOfNeZero ℂ ℂ (unitSectionEval (b i) x)
      (unitSectionEval_ne_zero (b i) x)).trans
      ((nativeTriv W (s i)).linearEquivAt ℂ x (hW i x.property)).symm)

theorem localFiberEquiv_coordinate (i : ι) (x : U i) (v : V x) :
    (nativeTriv W (s i) ⟨x, localFiberEquiv I M V W U r s hV hW b i x v⟩).2 =
      unitSectionEval (b i) x * (nativeTriv V (r i) ⟨x, v⟩).2 := by
  change (nativeTriv W (s i)).linearEquivAt ℂ x (hW i x.property)
    (localFiberEquiv I M V W U r s hV hW b i x v) = _
  simp only [localFiberEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  rfl

variable (hpoint : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j),
    unitSectionEval (b j) ⟨x, hj⟩ * (scalarTransition V (r i) (r j) x : ℂ) =
      (scalarTransition W (s i) (s j) x : ℂ) * unitSectionEval (b i) ⟨x, hi⟩)

include hpoint in
/-- Equality of the actual fibre maps on overlaps follows from the actual
scalar gauge equation. -/
theorem localFiberEquiv_independent (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j)
    (v : V x) :
    localFiberEquiv I M V W U r s hV hW b i ⟨x, hi⟩ v =
      localFiberEquiv I M V W U r s hV hW b j ⟨x, hj⟩ v := by
  apply ((nativeTriv W (s j)).linearEquivAt ℂ x (hW j hj)).injective
  change (nativeTriv W (s j) ⟨x, localFiberEquiv I M V W U r s hV hW b i ⟨x, hi⟩ v⟩).2 =
    (nativeTriv W (s j) ⟨x, localFiberEquiv I M V W U r s hV hW b j ⟨x, hj⟩ v⟩).2
  rw [native_coordinates W (s i) (s j) x (hW i hi) (hW j hj),
    localFiberEquiv_coordinate I M V W U r s hV hW b i ⟨x, hi⟩ v,
    localFiberEquiv_coordinate I M V W U r s hV hW b j ⟨x, hj⟩ v,
    native_coordinates V (r i) (r j) x (hV i hi) (hV j hj)]
  rw [← mul_assoc, ← hpoint i j x hi hj, mul_assoc]

variable (hcover : ∀ x : M, ∃ i, x ∈ U i)

/-- The global fibre equivalence obtained from the actual compatible local
maps. The chosen chart has no effect on its original-chart expressions. -/
def fiberEquiv (x : M) : V x ≃ₗ[ℂ] W x :=
  localFiberEquiv I M V W U r s hV hW b (Classical.choose (hcover x))
    ⟨x, Classical.choose_spec (hcover x)⟩

include hpoint in
theorem fiberEquiv_coordinate (i : ι) (x : M) (hx : x ∈ U i) (v : V x) :
    (nativeTriv W (s i) ⟨x, fiberEquiv I M V W U r s hV hW b hcover x v⟩).2 =
      unitSectionEval (b i) ⟨x, hx⟩ * (nativeTriv V (r i) ⟨x, v⟩).2 := by
  rw [fiberEquiv, localFiberEquiv_independent I M V W U r s hV hW b hpoint
    (Classical.choose (hcover x)) i x (Classical.choose_spec (hcover x)) hx]
  exact localFiberEquiv_coordinate I M V W U r s hV hW b i ⟨x, hx⟩ v

include hpoint in
theorem fiberEquiv_symm_coordinate (i : ι) (x : M) (hx : x ∈ U i) (w : W x) :
    (nativeTriv V (r i) ⟨x, (fiberEquiv I M V W U r s hV hW b hcover x).symm w⟩).2 =
      unitSectionEval (-b i) ⟨x, hx⟩ * (nativeTriv W (s i) ⟨x, w⟩).2 := by
  have h := fiberEquiv_coordinate I M V W U r s hV hW b hpoint hcover i x hx
    ((fiberEquiv I M V W U r s hV hW b hcover x).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [unitSectionEval_neg, h, ← mul_assoc,
    inv_mul_cancel₀ (unitSectionEval_ne_zero (b i) ⟨x, hx⟩), one_mul]

def toBundle (v : TotalSpace ℂ V) : TotalSpace ℂ W :=
  ⟨v.proj, fiberEquiv I M V W U r s hV hW b hcover v.proj v.2⟩

def fromBundle (w : TotalSpace ℂ W) : TotalSpace ℂ V :=
  ⟨w.proj, (fiberEquiv I M V W U r s hV hW b hcover w.proj).symm w.2⟩

@[simp] theorem toBundle_proj (v : TotalSpace ℂ V) :
    (toBundle I M V W U r s hV hW b hcover v).proj = v.proj := rfl

@[simp] theorem fromBundle_proj (w : TotalSpace ℂ W) :
    (fromBundle I M V W U r s hV hW b hcover w).proj = w.proj := rfl

end Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge
