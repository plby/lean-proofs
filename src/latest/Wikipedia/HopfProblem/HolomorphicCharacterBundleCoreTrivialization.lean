import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Trivializing a holomorphic line bundle by a nowhere-zero section

The bundle in this file is the actual `VectorBundleCore` bundle attached to
an arbitrary multiplicative transition cocycle. A nowhere-zero holomorphic
section gives inverse analytic, fibrewise complex-linear maps between its
total space and the product. Their analyticity is checked in the original
bundle charts; no replacement of the topology or atlas is made.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)
    (s : ∀ x, A.core.Fiber x)

/-- The fibre coefficient relative to a given section. -/
def sectionToProduct (p : A.core.TotalSpace) : M × ℂ :=
  (p.1, (id (α := ℂ) (s p.1))⁻¹ * id (α := ℂ) p.2)

/-- Multiplying the section by a scalar in the product fibre. -/
def sectionFromProduct (p : M × ℂ) : A.core.TotalSpace :=
  ⟨p.1, id (α := ℂ) (s p.1) * p.2⟩

@[simp] theorem sectionToProduct_sectionFromProduct
    (hne : ∀ x, s x ≠ 0) (p : M × ℂ) :
    A.sectionToProduct s (A.sectionFromProduct s p) = p := by
  apply Prod.ext
  · rfl
  · change (id (α := ℂ) (s p.1))⁻¹ * (id (α := ℂ) (s p.1) * p.2) = p.2
    rw [← mul_assoc, inv_mul_cancel₀ (hne p.1), one_mul]

@[simp] theorem sectionFromProduct_sectionToProduct
    (hne : ∀ x, s x ≠ 0) (p : A.core.TotalSpace) :
    A.sectionFromProduct s (A.sectionToProduct s p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, id (α := ℂ) (s x) *
      ((id (α := ℂ) (s x))⁻¹ * id (α := ℂ) v)⟩ : A.core.TotalSpace) = ⟨x, v⟩
    rw [← mul_assoc, mul_inv_cancel₀ (hne x), one_mul]
    rfl

theorem sectionFromProduct_localTriv (i : ι) (p : M × ℂ) :
    A.core.localTriv i (A.sectionFromProduct s p) =
      (p.1, (A.core.localTriv i ⟨p.1, s p.1⟩).2 * p.2) := by
  apply Prod.ext
  · rfl
  · exact (mul_assoc _ _ _).symm

theorem section_localTriv_ne_zero (hne : ∀ x, s x ≠ 0) (i : ι) (x : M) :
    (A.core.localTriv i ⟨x, s x⟩).2 ≠ 0 :=
  mul_ne_zero (A.transition_ne_zero _ _ _) (hne x)

theorem sectionToProduct_localTriv (i : ι) (p : A.core.TotalSpace) :
    A.sectionToProduct s p =
      ((A.core.localTriv i p).1,
        ((A.core.localTriv i ⟨p.1, s p.1⟩).2)⁻¹ * (A.core.localTriv i p).2) := by
  apply Prod.ext
  · rfl
  · change (id (α := ℂ) (s p.1))⁻¹ * id (α := ℂ) p.2 =
      ((A.transition (A.indexAt p.1) i p.1 : ℂ) * id (α := ℂ) (s p.1))⁻¹ *
        ((A.transition (A.indexAt p.1) i p.1 : ℂ) * id (α := ℂ) p.2)
    rw [mul_inv_rev, mul_assoc, ← mul_assoc (A.transition _ _ _ : ℂ)⁻¹,
      inv_mul_cancel₀ (A.transition_ne_zero _ _ _), one_mul]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem sectionFromProduct_holomorphic
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace))) :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (A.sectionFromProduct s) := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  have he : (fun q : M × ℂ =>
      (trivializationAt ℂ A.core.Fiber (A.sectionFromProduct s p).proj
        (A.sectionFromProduct s q)).2) =
      (fun q => (A.core.localTriv (A.indexAt p.1) ⟨q.1, s q.1⟩).2 * q.2) := by
    funext q
    change (A.core.localTriv (A.indexAt p.1) (A.sectionFromProduct s q)).2 = _
    rw [sectionFromProduct_localTriv]
  rw [he]
  have hc := ((trivializationAt ℂ A.core.Fiber p.1).contMDiffAt_section_iff
    (A.mem_baseSet_at p.1)).mp (hs p.1)
  exact (hc.comp p contMDiffAt_fst).mul contMDiffAt_snd

theorem sectionToProduct_holomorphic
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace)))
    (hne : ∀ x, s x ≠ 0) :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (A.sectionToProduct s) := by
  intro p
  let e := trivializationAt ℂ A.core.Fiber p.1
  have hp : p ∈ e.source := A.mem_baseSet_at p.1
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp)
  have hc := (e.contMDiffAt_section_iff (A.mem_baseSet_at p.1)).mp (hs p.1)
  have hci := hc.inv₀ (A.section_localTriv_ne_zero s hne (A.indexAt p.1) p.1)
  have hm : ContMDiffAt (I.prod I₁) (I.prod I₁) ω
      (fun q : M × ℂ => (q.1, ((e ⟨q.1, s q.1⟩).2)⁻¹ * q.2)) (e p) :=
    contMDiffAt_fst.prodMk ((hci.comp (e p) contMDiffAt_fst).mul contMDiffAt_snd)
  apply (hm.comp p he).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q => A.sectionToProduct_localTriv s (A.indexAt p.1) q

/-- The genuine analytic product trivialization determined by a nowhere-zero
holomorphic section of the original line bundle. -/
def sectionTrivialization
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace)))
    (hne : ∀ x, s x ≠ 0) :
    Diffeomorph (I.prod I₁) (I.prod I₁) A.core.TotalSpace (M × ℂ) ω where
  toFun := A.sectionToProduct s
  invFun := A.sectionFromProduct s
  left_inv := A.sectionFromProduct_sectionToProduct s hne
  right_inv := A.sectionToProduct_sectionFromProduct s hne
  contMDiff_toFun := A.sectionToProduct_holomorphic s I hs hne
  contMDiff_invFun := A.sectionFromProduct_holomorphic s I hs

variable
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace)))
    (hne : ∀ x, s x ≠ 0)

@[simp] theorem sectionTrivialization_fst (p : A.core.TotalSpace) :
    (A.sectionTrivialization s I hs hne p).1 = p.1 := rfl

@[simp] theorem sectionTrivialization_symm_proj (p : M × ℂ) :
    ((A.sectionTrivialization s I hs hne).symm p).proj = p.1 := rfl

theorem sectionTrivialization_add (x : M) (v w : A.core.Fiber x) :
    (A.sectionTrivialization s I hs hne ⟨x, v + w⟩).2 =
      (A.sectionTrivialization s I hs hne ⟨x, v⟩).2 +
        (A.sectionTrivialization s I hs hne ⟨x, w⟩).2 :=
  mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)

theorem sectionTrivialization_smul (x : M) (a : ℂ) (v : A.core.Fiber x) :
    (A.sectionTrivialization s I hs hne ⟨x, a • v⟩).2 =
      a • (A.sectionTrivialization s I hs hne ⟨x, v⟩).2 := by
  change _ * (a * id (α := ℂ) v) = a * (_ * id (α := ℂ) v)
  exact mul_left_comm _ _ _

/-- The analytic trivialization, viewed as a vector-bundle trivialization
whose base set is the entire base. -/
def sectionBundleTrivialization : Trivialization ℂ
    (Bundle.TotalSpace.proj : A.core.TotalSpace → M) where
  toOpenPartialHomeomorph :=
    (A.sectionTrivialization s I hs hne).toHomeomorph.toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

@[simp] theorem sectionBundleTrivialization_baseSet :
    (A.sectionBundleTrivialization s I hs hne).baseSet = univ := rfl

instance sectionBundleTrivialization_isLinear :
    (A.sectionBundleTrivialization s I hs hne).IsLinear ℂ where
  linear x _ :=
    { map_add := fun v w => A.sectionTrivialization_add s I hs hne x v w
      map_smul := fun a v => A.sectionTrivialization_smul s I hs hne x a v }

theorem sectionBundleTrivialization_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (A.sectionBundleTrivialization s I hs hne) :=
  (A.sectionTrivialization s I hs hne).contMDiff

theorem sectionBundleTrivialization_symm_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω
      (A.sectionBundleTrivialization s I hs hne).toOpenPartialHomeomorph.symm :=
  (A.sectionTrivialization s I hs hne).symm.contMDiff

@[simp] theorem sectionTrivialization_section (x : M) :
    A.sectionTrivialization s I hs hne ⟨x, s x⟩ = (x, 1) := by
  apply Prod.ext
  · rfl
  · exact inv_mul_cancel₀ (hne x)

/-- A holomorphic trivialization means an actual analytic diffeomorphism of
total spaces over the base, linear on each fibre. This definition makes no
reference to sections or to a coboundary expression for the cocycle. -/
structure AnalyticTrivialization where
  diffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁) A.core.TotalSpace (M × ℂ) ω
  preserves_base : ∀ p, (diffeomorph p).1 = p.1
  map_add : ∀ (x : M) (v w : A.core.Fiber x),
    (diffeomorph ⟨x, v + w⟩).2 = (diffeomorph ⟨x, v⟩).2 + (diffeomorph ⟨x, w⟩).2
  map_smul : ∀ (x : M) (a : ℂ) (v : A.core.Fiber x),
    (diffeomorph ⟨x, a • v⟩).2 = a • (diffeomorph ⟨x, v⟩).2

/-- The trivialization constructed from a nowhere-zero section has all the
properties in the geometric definition of analytic triviality. -/
def analyticTrivializationOfSection : A.AnalyticTrivialization I where
  diffeomorph := A.sectionTrivialization s I hs hne
  preserves_base := A.sectionTrivialization_fst s I hs hne
  map_add := A.sectionTrivialization_add s I hs hne
  map_smul := A.sectionTrivialization_smul s I hs hne

namespace AnalyticTrivialization

variable {A I} (e : A.AnalyticTrivialization I)

omit [A.IsHolomorphic I]

theorem symm_preserves_base (p : M × ℂ) :
    (e.diffeomorph.symm p).proj = p.1 := by
  calc
    (e.diffeomorph.symm p).proj = (e.diffeomorph (e.diffeomorph.symm p)).1 :=
      (e.preserves_base _).symm
    _ = p.1 := congrArg Prod.fst (e.diffeomorph.apply_symm_apply p)

/-- The section obtained from the constant vector `1` in a product
trivialization. The equality of its base with `x` is verified below. -/
def frame (x : M) : A.core.Fiber x :=
  id (α := ℂ) (e.diffeomorph.symm (x, 1)).2

theorem frame_totalSpace (x : M) :
    (⟨x, e.frame x⟩ : A.core.TotalSpace) = e.diffeomorph.symm (x, 1) := by
  apply Bundle.TotalSpace.ext (e.symm_preserves_base (x, 1)).symm
  rfl

theorem frame_holomorphic :
    ContMDiff I (I.prod I₁) ω (fun x => (⟨x, e.frame x⟩ : A.core.TotalSpace)) := by
  have he : (fun x => (⟨x, e.frame x⟩ : A.core.TotalSpace)) =
      (fun x => e.diffeomorph.symm (x, 1)) := funext e.frame_totalSpace
  rw [he]
  exact e.diffeomorph.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

@[simp] theorem map_zero (x : M) : (e.diffeomorph ⟨x, 0⟩).2 = 0 := by
  simpa using e.map_smul x 0 0

@[simp] theorem frame_image (x : M) : e.diffeomorph ⟨x, e.frame x⟩ = (x, 1) := by
  rw [e.frame_totalSpace]
  exact e.diffeomorph.apply_symm_apply _

theorem frame_ne_zero (x : M) : e.frame x ≠ 0 := by
  intro hz
  have h := congrArg Prod.snd (e.frame_image x)
  rw [hz, e.map_zero] at h
  exact zero_ne_one h

end AnalyticTrivialization

/-- A holomorphic line bundle is analytically trivial exactly when it admits
a holomorphic nowhere-zero section. Both directions concern the original
bundle total space and atlas. -/
theorem exists_holomorphic_nonzero_section_iff_analyticTrivialization :
    (∃ s : ∀ x, A.core.Fiber x,
      ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) ∧
        ∀ x, s x ≠ 0) ↔ Nonempty (A.AnalyticTrivialization I) := by
  constructor
  · rintro ⟨s, hs, hne⟩
    exact ⟨A.analyticTrivializationOfSection s I hs hne⟩
  · rintro ⟨e⟩
    exact ⟨e.frame, e.frame_holomorphic, e.frame_ne_zero⟩

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData
