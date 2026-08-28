import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# A genuine canonical-bundle trivialization from a holomorphic frame

A nowhere-zero holomorphic section of the actual canonical bundle gives
an analytic, fibrewise complex-linear diffeomorphism with the product line
bundle. Both directions use the original bundle topology and manifold
atlas. In any actual chart the forward coefficient is the ratio of the
vector coefficient to the frame coefficient, so no determinant-one
condition on the atlas is required.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsFrameTrivialization

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber)

/-- The scalar coordinate relative to the given canonical section. -/
def toProduct (p : (Atlas.core M).TotalSpace) : M × ℂ :=
  (p.proj, (id (α := ℂ) (s p.proj))⁻¹ * id (α := ℂ) p.2)

/-- The product coordinate `c` represents the actual canonical vector `c • s x`. -/
def fromProduct (p : M × ℂ) : (Atlas.core M).TotalSpace :=
  ⟨p.1, p.2 • s p.1⟩

@[simp] theorem toProduct_fst (p : (Atlas.core M).TotalSpace) :
    (toProduct s p).1 = p.proj := rfl

@[simp] theorem fromProduct_proj (p : M × ℂ) :
    (fromProduct s p).proj = p.1 := rfl

@[simp] theorem fromProduct_mk (x : M) (c : ℂ) :
    fromProduct s (x, c) = ⟨x, c • s x⟩ := rfl

@[simp] theorem toProduct_fromProduct (hne : ∀ x, s x ≠ 0) (p : M × ℂ) :
    toProduct s (fromProduct s p) = p := by
  apply Prod.ext
  · rfl
  · change (id (α := ℂ) (s p.1))⁻¹ * (p.2 * id (α := ℂ) (s p.1)) = p.2
    rw [mul_left_comm, inv_mul_cancel₀ (hne p.1), mul_one]

@[simp] theorem fromProduct_toProduct (hne : ∀ x, s x ≠ 0)
    (p : (Atlas.core M).TotalSpace) : fromProduct s (toProduct s p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, ((id (α := ℂ) (s x))⁻¹ * id (α := ℂ) v) *
      id (α := ℂ) (s x)⟩ : (Atlas.core M).TotalSpace) = ⟨x, v⟩
    rw [mul_right_comm, inv_mul_cancel₀ (hne x), one_mul]
    rfl

/-- The frame coefficient in an actual canonical-bundle chart. -/
def localCoefficient (i : atlas Model M) (x : M) : ℂ :=
  ((Atlas.core M).localTriv i ⟨x, s x⟩).2

theorem localCoefficient_ne_zero (hne : ∀ x, s x ≠ 0) (i : atlas Model M)
    {x : M} (hx : x ∈ i.val.source) : localCoefficient s i x ≠ 0 := by
  change Atlas.jacobian M i (achart Model x) x * id (α := ℂ) (s x) ≠ 0
  exact mul_ne_zero (Atlas.jacobian_ne_zero M i (achart Model x)
    hx (mem_chart_source Model x)) (hne x)

theorem fromProduct_localTriv (i : atlas Model M) (p : M × ℂ) :
    (Atlas.core M).localTriv i (fromProduct s p) =
      (p.1, p.2 * localCoefficient s i p.1) := by
  apply Prod.ext
  · rfl
  · change Atlas.jacobian M i (achart Model p.1) p.1 *
      (p.2 * id (α := ℂ) (s p.1)) =
        p.2 * (Atlas.jacobian M i (achart Model p.1) p.1 * id (α := ℂ) (s p.1))
    exact mul_left_comm _ _ _

/-- In every valid actual chart, the forward coordinate is the ratio of
the vector coefficient to the frame coefficient. -/
theorem toProduct_localTriv (i : atlas Model M) (p : (Atlas.core M).TotalSpace)
    (hp : p.proj ∈ i.val.source) :
    toProduct s p =
      (((Atlas.core M).localTriv i p).1,
        (localCoefficient s i p.proj)⁻¹ * ((Atlas.core M).localTriv i p).2) := by
  apply Prod.ext
  · rfl
  · change (id (α := ℂ) (s p.proj))⁻¹ * id (α := ℂ) p.2 =
      (Atlas.jacobian M i (achart Model p.proj) p.proj *
        id (α := ℂ) (s p.proj))⁻¹ *
      (Atlas.jacobian M i (achart Model p.proj) p.proj * id (α := ℂ) p.2)
    rw [mul_inv_rev, mul_assoc,
      ← mul_assoc (Atlas.jacobian M i (achart Model p.proj) p.proj)⁻¹,
      inv_mul_cancel₀ (Atlas.jacobian_ne_zero M i (achart Model p.proj)
        hp (mem_chart_source Model p.proj)), one_mul]

theorem localCoefficient_holomorphicAt (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) : ContMDiffAt I I₁ ω (localCoefficient s i) x :=
  (((Atlas.core M).localTriv i).contMDiffAt_section_iff hx).mp (s.contMDiff x)

/-- Multiplication of the holomorphic section by the product coordinate is
holomorphic into the original canonical-bundle total space. -/
theorem fromProduct_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (fromProduct s) := by
  intro p
  let i := achart Model p.1
  have hp : fromProduct s p ∈ ((Atlas.core M).localTriv i).source :=
    mem_chart_source Model p.1
  apply (((Atlas.core M).localTriv i).contMDiffAt_iff hp).mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  have he : (fun q : M × ℂ => ((Atlas.core M).localTriv i (fromProduct s q)).2) =
      (fun q => q.2 * localCoefficient s i q.1) := by
    funext q
    exact congrArg Prod.snd (fromProduct_localTriv s i q)
  rw [he]
  exact contMDiffAt_snd.mul
    ((localCoefficient_holomorphicAt s i (mem_chart_source Model p.1)).comp
      p contMDiffAt_fst)

/-- The locally computed ratio is holomorphic since its frame denominator
never vanishes on the chart domain. -/
theorem toProduct_holomorphic (hne : ∀ x, s x ≠ 0) :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (toProduct s) := by
  intro p
  let i := achart Model p.proj
  let e := (Atlas.core M).localTriv i
  have hp : p ∈ e.source := mem_chart_source Model p.proj
  have he : ContMDiffAt ((I).prod I₁) ((I).prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp)
  have hproj : ContMDiffAt ((I).prod I₁) I ω
      (Bundle.TotalSpace.proj : (Atlas.core M).TotalSpace → M) p :=
    Bundle.contMDiffAt_proj (Atlas.core M).Fiber
  have hc := (localCoefficient_holomorphicAt s i (mem_chart_source Model p.proj)).inv₀
    (localCoefficient_ne_zero s hne i (mem_chart_source Model p.proj))
  have hratio : ContMDiffAt ((I).prod I₁) ((I).prod I₁) ω
      (fun q : (Atlas.core M).TotalSpace =>
        (q.proj, (localCoefficient s i q.proj)⁻¹ * (e q).2)) p :=
    hproj.prodMk ((hc.comp p hproj).mul he.snd)
  apply hratio.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact toProduct_localTriv s i q hq

/-- A nowhere-zero holomorphic canonical section gives a genuine analytic
product trivialization of the native canonical bundle. -/
def bundleBiholomorph (hne : ∀ x, s x ≠ 0) :
    Diffeomorph ((I).prod I₁) ((I).prod I₁) (Atlas.core M).TotalSpace (M × ℂ) ω where
  toFun := toProduct s
  invFun := fromProduct s
  left_inv := fromProduct_toProduct s hne
  right_inv := toProduct_fromProduct s hne
  contMDiff_toFun := toProduct_holomorphic s hne
  contMDiff_invFun := fromProduct_holomorphic s

variable (hne : ∀ x, s x ≠ 0)

@[simp] theorem bundleBiholomorph_apply (p : (Atlas.core M).TotalSpace) :
    bundleBiholomorph s hne p = toProduct s p := rfl

@[simp] theorem bundleBiholomorph_fst (p : (Atlas.core M).TotalSpace) :
    (bundleBiholomorph s hne p).1 = p.proj := rfl

@[simp] theorem bundleBiholomorph_symm_apply (x : M) (c : ℂ) :
    (bundleBiholomorph s hne).symm (x, c) = ⟨x, c • s x⟩ := rfl

@[simp] theorem bundleBiholomorph_symm_proj (p : M × ℂ) :
    ((bundleBiholomorph s hne).symm p).proj = p.1 := rfl

theorem bundleBiholomorph_add (x : M) (v w : (Atlas.core M).Fiber x) :
    (bundleBiholomorph s hne ⟨x, v + w⟩).2 =
      (bundleBiholomorph s hne ⟨x, v⟩).2 + (bundleBiholomorph s hne ⟨x, w⟩).2 :=
  mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)

theorem bundleBiholomorph_smul (x : M) (c : ℂ) (v : (Atlas.core M).Fiber x) :
    (bundleBiholomorph s hne ⟨x, c • v⟩).2 =
      c • (bundleBiholomorph s hne ⟨x, v⟩).2 := by
  change _ * (c * id (α := ℂ) v) = c * (_ * id (α := ℂ) v)
  exact mul_left_comm _ _ _

@[simp] theorem bundleBiholomorph_section (x : M) :
    bundleBiholomorph s hne ⟨x, s x⟩ = (x, 1) := by
  apply Prod.ext
  · rfl
  · exact inv_mul_cancel₀ (hne x)

@[simp] theorem bundleBiholomorph_symm_one (x : M) :
    (bundleBiholomorph s hne).symm (x, 1) = ⟨x, s x⟩ := by
  rw [bundleBiholomorph_symm_apply, one_smul]

/-- The same native analytic diffeomorphism as a global vector-bundle
trivialization with base set the whole manifold. -/
def bundleTrivialization : Trivialization ℂ
    (Bundle.TotalSpace.proj : (Atlas.core M).TotalSpace → M) where
  toOpenPartialHomeomorph := (bundleBiholomorph s hne).toHomeomorph.toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

@[simp] theorem bundleTrivialization_baseSet :
    (bundleTrivialization s hne).baseSet = univ := rfl

instance bundleTrivialization_isLinear : (bundleTrivialization s hne).IsLinear ℂ where
  linear x _ :=
    { map_add := fun v w => bundleBiholomorph_add s hne x v w
      map_smul := fun c v => bundleBiholomorph_smul s hne x c v }

theorem bundleTrivialization_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (bundleTrivialization s hne) :=
  (bundleBiholomorph s hne).contMDiff

theorem bundleTrivialization_symm_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω
      (bundleTrivialization s hne).toOpenPartialHomeomorph.symm :=
  (bundleBiholomorph s hne).symm.contMDiff

/-- The induced continuous complex-linear equivalence on each actual
canonical fibre. -/
def fiberEquiv (x : M) : (Atlas.core M).Fiber x ≃L[ℂ] ℂ :=
  (bundleTrivialization s hne).continuousLinearEquivAt ℂ x (Set.mem_univ x)

@[simp] theorem fiberEquiv_apply (x : M) (v : (Atlas.core M).Fiber x) :
    fiberEquiv s hne x v = (bundleBiholomorph s hne ⟨x, v⟩).2 := rfl

@[simp] theorem fiberEquiv_symm_apply (x : M) (c : ℂ) :
    (fiberEquiv s hne x).symm c = c • s x := by
  apply (fiberEquiv s hne x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, fiberEquiv_apply]
  exact (congrArg Prod.snd (toProduct_fromProduct s hne (x, c))).symm

theorem eq_coefficient_smul (x : M) (v : (Atlas.core M).Fiber x) :
    v = fiberEquiv s hne x v • s x := by
  calc
    v = (fiberEquiv s hne x).symm (fiberEquiv s hne x v) :=
      ((fiberEquiv s hne x).symm_apply_apply v).symm
    _ = _ := fiberEquiv_symm_apply s hne x _

/-- The inverse fibre coordinate is scalar multiplication of the genuine
intrinsic alternating top covector represented by the frame. -/
theorem intrinsic_fiberEquiv_symm_apply (x : M) (c : ℂ) :
    Atlas.intrinsicEquiv M x ((fiberEquiv s hne x).symm c) =
      c • Atlas.intrinsicEquiv M x (s x) := by
  rw [fiberEquiv_symm_apply, map_smul]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsFrameTrivialization
