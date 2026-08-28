import Wikipedia.HopfProblem.HolomorphicLineBundleCore
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# An actual holomorphic trivialization from compatible local frames

The scalar bundle constructed from constant frame coefficients is globally
trivial. The maps below are inverse analytic maps of the total spaces and
are complex-linear in every fibre. The proof uses the bundle topology and
its analytic trivializations; it does not identify the total space with a
product by changing its topology.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicLineBundle.ConstantTransitionData

variable {M ι : Type*} [TopologicalSpace M]
    (A : ConstantTransitionData M ι)

def toProduct (p : A.core.TotalSpace) : M × ℂ :=
  (p.1, (A.coefficient (A.indexAt p.1))⁻¹ * id (α := ℂ) p.2)

def fromProduct (p : M × ℂ) : A.core.TotalSpace :=
  ⟨p.1, A.coefficient (A.indexAt p.1) * p.2⟩

@[simp] theorem toProduct_fromProduct (p : M × ℂ) :
    A.toProduct (A.fromProduct p) = p := by
  apply Prod.ext
  · rfl
  · change (A.coefficient (A.indexAt p.1))⁻¹ *
      (A.coefficient (A.indexAt p.1) * p.2) = p.2
    rw [← mul_assoc, inv_mul_cancel₀ (A.coefficient_ne_zero _), one_mul]

@[simp] theorem fromProduct_toProduct (p : A.core.TotalSpace) :
    A.fromProduct (A.toProduct p) = p := by
  cases p with
  | mk b v =>
    change (⟨b, A.coefficient (A.indexAt b) *
      ((A.coefficient (A.indexAt b))⁻¹ * id (α := ℂ) v)⟩ : A.core.TotalSpace) = ⟨b, v⟩
    rw [← mul_assoc, mul_inv_cancel₀ (A.coefficient_ne_zero _), one_mul]
    rfl

theorem fromProduct_localTriv (i : ι) (p : M × ℂ) :
    A.core.localTriv i (A.fromProduct p) = (p.1, A.coefficient i * p.2) := by
  rw [A.core_localTriv_apply]
  apply Prod.ext
  · rfl
  · change (A.coefficient i / A.coefficient (A.indexAt p.1)) *
      (A.coefficient (A.indexAt p.1) * p.2) = A.coefficient i * p.2
    field_simp [A.coefficient_ne_zero]

theorem toProduct_localTriv (i : ι) (p : A.core.TotalSpace) :
    A.toProduct p =
      ((A.core.localTriv i p).1, (A.coefficient i)⁻¹ * (A.core.localTriv i p).2) := by
  rw [A.core_localTriv_apply]
  apply Prod.ext
  · rfl
  · change (A.coefficient (A.indexAt p.1))⁻¹ * id (α := ℂ) p.2 =
      (A.coefficient i)⁻¹ *
        ((A.coefficient i / A.coefficient (A.indexAt p.1)) * id (α := ℂ) p.2)
    field_simp [A.coefficient_ne_zero]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem fromProduct_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω A.fromProduct := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  have he : (fun q : M × ℂ =>
      (trivializationAt ℂ A.core.Fiber (A.fromProduct p).proj (A.fromProduct q)).2) =
      (fun q => A.coefficient (A.indexAt p.1) * q.2) := by
    funext q
    change (A.core.localTriv (A.indexAt p.1) (A.fromProduct q)).2 = _
    rw [fromProduct_localTriv]
  rw [he]
  exact ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd).contMDiffAt

theorem toProduct_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω A.toProduct := by
  intro p
  let e := trivializationAt ℂ A.core.Fiber p.proj
  have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp)
  have hm : ContMDiff (I.prod I₁) (I.prod I₁) ω
      (fun q : M × ℂ => (q.1, (A.coefficient (A.indexAt p.1))⁻¹ * q.2)) :=
    contMDiff_fst.prodMk ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)
  apply (hm.contMDiffAt.comp p he).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q => A.toProduct_localTriv (A.indexAt p.1) q

/-- A base-preserving analytic diffeomorphism of the actual bundle total
space with the product. Its linearity on each fibre is recorded below. -/
def globalTrivialization : Diffeomorph (I.prod I₁) (I.prod I₁) A.core.TotalSpace (M × ℂ) ω where
  toFun := A.toProduct
  invFun := A.fromProduct
  left_inv := A.fromProduct_toProduct
  right_inv := A.toProduct_fromProduct
  contMDiff_toFun := A.toProduct_holomorphic I
  contMDiff_invFun := A.fromProduct_holomorphic I

@[simp] theorem globalTrivialization_fst (p : A.core.TotalSpace) :
    (A.globalTrivialization I p).1 = p.1 := rfl

@[simp] theorem globalTrivialization_symm_proj (p : M × ℂ) :
    ((A.globalTrivialization I).symm p).proj = p.1 := rfl

theorem globalTrivialization_add (x : M) (v w : A.core.Fiber x) :
    (A.globalTrivialization I ⟨x, v + w⟩).2 =
      (A.globalTrivialization I ⟨x, v⟩).2 + (A.globalTrivialization I ⟨x, w⟩).2 :=
  mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)

theorem globalTrivialization_smul (x : M) (a : ℂ) (v : A.core.Fiber x) :
    (A.globalTrivialization I ⟨x, a • v⟩).2 =
      a • (A.globalTrivialization I ⟨x, v⟩).2 := by
  change _ * (a * id (α := ℂ) v) = a * (_ * id (α := ℂ) v)
  ring

/-- The same global equivalence bundled as a genuine vector-bundle
trivialization over all of the base. -/
def bundleTrivialization : Trivialization ℂ
    (Bundle.TotalSpace.proj : A.core.TotalSpace → M) where
  toOpenPartialHomeomorph := (A.globalTrivialization I).toHomeomorph.toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

@[simp] theorem bundleTrivialization_baseSet : (A.bundleTrivialization I).baseSet = univ := rfl

instance bundleTrivialization_isLinear : (A.bundleTrivialization I).IsLinear ℂ where
  linear x _ :=
    { map_add := fun v w => A.globalTrivialization_add I x v w
      map_smul := fun c v => A.globalTrivialization_smul I x c v }

theorem bundleTrivialization_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (A.bundleTrivialization I) :=
  (A.globalTrivialization I).contMDiff

theorem bundleTrivialization_symm_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω
      (A.bundleTrivialization I).toOpenPartialHomeomorph.symm :=
  (A.globalTrivialization I).symm.contMDiff

/-- The compatible nonzero local coefficients define an actual global section. -/
def frame (x : M) : A.core.Fiber x := A.coefficient (A.indexAt x)

theorem frame_ne_zero (x : M) : A.frame x ≠ 0 := A.coefficient_ne_zero _

theorem frame_localTriv (i : ι) (x : M) :
    (A.core.localTriv i ⟨x, A.frame x⟩).2 = A.coefficient i := by
  change (A.coefficient i / A.coefficient (A.indexAt x)) *
    A.coefficient (A.indexAt x) = A.coefficient i
  exact div_mul_cancel₀ _ (A.coefficient_ne_zero _)

theorem frame_holomorphic :
    ContMDiff I (I.prod I₁) ω (fun x => (⟨x, A.frame x⟩ : A.core.TotalSpace)) := by
  have h : ContMDiff I (I.prod I₁) ω (fun x : M => (x, (1 : ℂ))) :=
    contMDiff_id.prodMk contMDiff_const
  simpa [fromProduct, frame, Function.comp_def] using (A.fromProduct_holomorphic I).comp h

@[simp] theorem globalTrivialization_frame (x : M) :
    A.globalTrivialization I ⟨x, A.frame x⟩ = (x, 1) := by
  apply Prod.ext
  · rfl
  · exact inv_mul_cancel₀ (A.coefficient_ne_zero _)

end Wikipedia.HopfProblem.HolomorphicLineBundle.ConstantTransitionData
