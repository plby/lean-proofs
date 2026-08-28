import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAlternating
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The canonical line bundle from the actual tangent atlas

For any analytic complex manifold with the period-family product model,
the tangent bundle's actual chart derivatives give a canonical line bundle.
Its transition functions are the determinants of the reversed tangent
coordinate changes.  Its chart representations are the full continuous
alternating three-covectors, transforming by genuine derivative pullback.
No transition cocycle or Jacobian identity is an additional hypothesis.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Atlas

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The determinant on continuous endomorphisms is analytic: in the
actual product basis it is the ordinary finite determinant polynomial. -/
theorem determinant_contDiff :
    ContDiff ℂ ω (fun A : Model →L[ℂ] Model => LinearMap.det A.toLinearMap) := by
  have heval (j : Fin 3) : ContDiff ℂ ω (fun A : Model →L[ℂ] Model => A (basis j)) :=
    contDiff_id.clm_apply contDiff_const
  have hentry (i j : Fin 3) :
      ContDiff ℂ ω (fun A : Model →L[ℂ] Model => coordinateEquiv (A (basis j)) i) :=
    (contDiff_pi.mp (coordinateEquiv.toContinuousLinearMap.contDiff.comp (heval j))) i
  simp_rw [← LinearMap.det_toMatrix basis, Matrix.det_fin_three,
    LinearMap.toMatrix_apply, basis_repr]
  exact (((((hentry 0 0).mul (hentry 1 1)).mul (hentry 2 2)).sub
    (((hentry 0 0).mul (hentry 1 2)).mul (hentry 2 1))).sub
    (((hentry 0 1).mul (hentry 1 0)).mul (hentry 2 2))).add
    (((hentry 0 1).mul (hentry 1 2)).mul (hentry 2 0)) |>.add
    (((hentry 0 2).mul (hentry 1 0)).mul (hentry 2 1)) |>.sub
    (((hentry 0 2).mul (hentry 1 1)).mul (hentry 2 0))

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- Mathlib's tangent core, indexed by the actual manifold atlas. -/
abbrev tangentCore : VectorBundleCore ℂ M Model (atlas Model M) := tangentBundleCore I M

/-- The determinant of an actual tangent coordinate change. -/
def jacobian (i j : atlas Model M) (x : M) : ℂ :=
  LinearMap.det ((tangentCore M).coordChange i j x).toLinearMap

theorem tangentCore_coordChange (i j : atlas Model M) (x : M) :
    (tangentCore M).coordChange i j x =
      fderiv ℂ (j.val ∘ i.val.symm) (i.val x) := by
  simp [tangentCore, tangentBundleCore_coordChange, mfld_simps]

theorem jacobian_eq_fderiv (i j : atlas Model M) (x : M) :
    jacobian M i j x = LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap := by
  rw [jacobian, tangentCore_coordChange]

theorem jacobian_self (i : atlas Model M) {x : M} (hx : x ∈ i.val.source) :
    jacobian M i i x = 1 := by
  have h : (tangentCore M).coordChange i i x = ContinuousLinearMap.id ℂ Model := by
    apply ContinuousLinearMap.ext
    intro v
    exact (tangentCore M).coordChange_self i x hx v
  rw [jacobian, h]
  exact LinearMap.det_id

theorem jacobian_comp (i j k : atlas Model M) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source ∩ k.val.source) :
    jacobian M j k x * jacobian M i j x = jacobian M i k x := by
  have h := congrArg (fun A : Model →L[ℂ] Model => LinearMap.det A.toLinearMap)
    ((tangentCore M).coordChange_linear_comp i j k x hx)
  change LinearMap.det (((tangentCore M).coordChange j k x).toLinearMap.comp
    ((tangentCore M).coordChange i j x).toLinearMap) = _ at h
  rw [LinearMap.det_comp] at h
  exact h

theorem jacobian_reverse_mul (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) :
    jacobian M j i x * jacobian M i j x = 1 :=
  (jacobian_comp M i j i ⟨⟨hi, hj⟩, hi⟩).trans (jacobian_self M i hi)

theorem jacobian_ne_zero (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) : jacobian M i j x ≠ 0 := by
  intro hz
  have h := jacobian_reverse_mul M i j hi hj
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem jacobian_reverse (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) :
    jacobian M j i x = (jacobian M i j x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (jacobian_reverse_mul M i j hi hj)

theorem jacobian_continuousOn (i j : atlas Model M) :
    ContinuousOn (jacobian M i j) (i.val.source ∩ j.val.source) :=
  determinant_contDiff.continuous.comp_continuousOn
    ((tangentCore M).continuousOn_coordChange i j)

/-- The genuine canonical line bundle core: its transition from `i` to
`j` is the determinant of the reverse tangent derivative. -/
def core : VectorBundleCore ℂ M ℂ (atlas Model M) where
  baseSet := (tangentCore M).baseSet
  isOpen_baseSet := (tangentCore M).isOpen_baseSet
  indexAt := (tangentCore M).indexAt
  mem_baseSet_at := (tangentCore M).mem_baseSet_at
  coordChange i j x := jacobian M j i x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    simp [jacobian_self M i hx]
  continuousOn_coordChange i j := by
    have h : ContinuousOn (jacobian M j i) (i.val.source ∩ j.val.source) := by
      simpa only [inter_comm] using jacobian_continuousOn M j i
    exact h.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm (jacobian M k j x) (jacobian M j i x),
      jacobian_comp M k j i ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩]

@[simp] theorem core_baseSet (i : atlas Model M) : (core M).baseSet i = i.val.source := rfl

@[simp] theorem core_indexAt (x : M) : (core M).indexAt x = achart Model x := rfl

@[simp] theorem core_coordChange (i j : atlas Model M) (x : M) :
    (core M).coordChange i j x = jacobian M j i x • ContinuousLinearMap.id ℂ ℂ := rfl

@[simp] theorem core_coordChange_apply (i j : atlas Model M) (x : M) (c : ℂ) :
    (core M).coordChange i j x c = jacobian M j i x * c := rfl

/-- The scalar transition is precisely the inverse forward Jacobian. -/
theorem coordChange_eq_inverse_jacobian (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) :
    (core M).coordChange i j x =
      (LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ •
        ContinuousLinearMap.id ℂ ℂ := by
  rw [core_coordChange, jacobian_reverse M i j hi hj, jacobian_eq_fderiv]

theorem jacobian_holomorphicOn (i j : atlas Model M) :
    ContMDiffOn I I₁ ω (jacobian M i j) (i.val.source ∩ j.val.source) := by
  let : (tangentCore M).IsContMDiff I ω := tangentBundleCore.isContMDiff
  exact determinant_contDiff.contMDiff.comp_contMDiffOn
    ((tangentCore M).contMDiffOn_coordChange I i j)

instance core_isContMDiff : (core M).IsContMDiff I ω where
  contMDiffOn_coordChange i j := by
    have h : ContMDiffOn I I₁ ω (jacobian M j i) (i.val.source ∩ j.val.source) := by
      simpa only [inter_comm] using jacobian_holomorphicOn M j i
    exact ((ContinuousLinearMap.id ℂ ℂ).smulRight
      (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn h

theorem holomorphicVectorBundle : ContMDiffVectorBundle ω ℂ (core M).Fiber I := inferInstance

theorem fibre_rank_one (x : M) : Module.finrank ℂ ((core M).Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

/-- Scalar coordinate changes are exactly pullback of genuine continuous
alternating three-covectors by the reversed chart derivative. -/
theorem coordChange_topCovector (i j : atlas Model M) (x : M) (c : ℂ) :
    coefficientEquiv ((core M).coordChange i j x c) =
      (coefficientEquiv c).compContinuousLinearMap
        (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) := by
  rw [coefficientEquiv_pullback, ← jacobian_eq_fderiv, core_coordChange_apply]

/-- The full top covector representing a canonical-bundle vector in a
particular actual chart. -/
def inCoordinates (i : atlas Model M) (x : M) (v : (core M).Fiber x) : TopCovector :=
  coefficientEquiv ((core M).localTriv i ⟨x, v⟩).2

/-- A valid chart identifies each bundle fibre with the entire space of
continuous alternating three-covectors on its model. -/
def coordinateEquiv (i : atlas Model M) {x : M} (hx : x ∈ i.val.source) :
    (core M).Fiber x ≃L[ℂ] TopCovector :=
  (((core M).localTriv i).continuousLinearEquivAt ℂ x hx).trans coefficientEquiv

@[simp] theorem coordinateEquiv_apply (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) (v : (core M).Fiber x) :
    coordinateEquiv M i hx v = inCoordinates M i x v := rfl

theorem inCoordinates_change (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) (v : (core M).Fiber x) :
    inCoordinates M j x v = (inCoordinates M i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) := by
  rw [inCoordinates, inCoordinates, coefficientEquiv_pullback, ← jacobian_eq_fderiv]
  apply congrArg coefficientEquiv
  change (core M).coordChange ((core M).indexAt x) j x v =
    jacobian M j i x * (core M).coordChange ((core M).indexAt x) i x v
  exact ((core M).coordChange_comp ((core M).indexAt x) i j x
    ⟨⟨(core M).mem_baseSet_at x, hi⟩, hj⟩ v).symm

theorem coordinateEquiv_change (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) (v : (core M).Fiber x) :
    coordinateEquiv M j hj v = (coordinateEquiv M i hi v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) :=
  inCoordinates_change M i j hi hj v

theorem inCoordinates_indexAt (x : M) (v : (core M).Fiber x) :
    inCoordinates M ((core M).indexAt x) x v = coefficientEquiv v := by
  unfold inCoordinates
  rw [VectorBundleCore.localTriv_apply,
    (core M).coordChange_self ((core M).indexAt x) x ((core M).mem_baseSet_at x) v]

/-- The intrinsic fibre is the full continuous alternating top-covector
space on Mathlib's actual tangent space at the base point. -/
abbrev IntrinsicTopCovector (x : M) := (TangentSpace I x) [⋀^(Fin 3)]→L[ℂ] ℂ

/-- Identification with intrinsic top covectors, expressed in the preferred
tangent chart used by `tangentBundleCore`. -/
def intrinsicEquiv (x : M) : (core M).Fiber x ≃L[ℂ] IntrinsicTopCovector M x :=
  coefficientEquiv

theorem inCoordinates_eq_intrinsic_pullback (i : atlas Model M) (x : M)
    (v : (core M).Fiber x) :
    inCoordinates M i x v = (intrinsicEquiv M x v).compContinuousLinearMap
      ((tangentCore M).coordChange i (achart Model x) x) := by
  exact (coefficientEquiv_pullback (id (α := ℂ) v)
    ((tangentCore M).coordChange i (achart Model x) x)).symm

theorem inCoordinates_preferred (x : M) (v : (core M).Fiber x) :
    inCoordinates M (achart Model x) x v = intrinsicEquiv M x v :=
  inCoordinates_indexAt M x v

theorem totalSpace_isManifold :
    IsManifold ((I).prod I₁) ω (core M).TotalSpace := inferInstance

/-- The unit top covector in the preferred tangent coordinates. It is a
holomorphic global frame when the actual overlap Jacobians are one. -/
def unitFrame (x : M) : (core M).Fiber x := (1 : ℂ)

theorem unitFrame_ne_zero (x : M) : unitFrame M x ≠ 0 := by
  change (1 : ℂ) ≠ 0
  exact one_ne_zero

@[simp] theorem intrinsicEquiv_unitFrame (x : M) :
    intrinsicEquiv M x (unitFrame M x) = volume := by
  change coefficientEquiv (1 : ℂ) = volume
  simp

section UnitJacobian

variable (hdet : ∀ (i j : atlas Model M) (x : M),
  x ∈ i.val.source → x ∈ j.val.source → jacobian M i j x = 1)

include hdet

theorem unitFrame_localCoefficient (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) :
    ((core M).localTriv i ⟨x, unitFrame M x⟩).2 = 1 := by
  change jacobian M i (achart Model x) x * 1 = 1
  rw [hdet i (achart Model x) x hx (mem_chart_source Model x), mul_one]

/-- The actual chart representation is the base-first volume form
`dz ∧ dζ₀ ∧ dζ₁`, not merely a nonzero scalar. -/
theorem unitFrame_inCoordinates (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) : inCoordinates M i x (unitFrame M x) = volume := by
  rw [inCoordinates, unitFrame_localCoefficient M hdet i hx]
  change (1 : ℂ) • volume = volume
  exact one_smul ℂ volume

theorem unitFrame_holomorphic :
    ContMDiff I ((I).prod I₁) ω
      (fun x => (⟨x, unitFrame M x⟩ : (core M).TotalSpace)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  have hnhds : (achart Model x).val.source ∈ 𝓝 x :=
    (achart Model x).val.open_source.mem_nhds (mem_chart_source Model x)
  apply (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
  filter_upwards [hnhds] with y hy
  exact unitFrame_localCoefficient M hdet (achart Model x) hy

/-- The genuine global section of the canonical bundle, bundled with its
holomorphicity proof under the proved-overlap criterion. -/
def unitHolomorphicFrame : ContMDiffSection I ℂ ω (core M).Fiber where
  toFun := unitFrame M
  contMDiff_toFun := unitFrame_holomorphic M hdet

@[simp] theorem unitHolomorphicFrame_apply (x : M) :
    unitHolomorphicFrame M hdet x = unitFrame M x := rfl

theorem localTriv_eq_of_jacobian_one (i : atlas Model M) (p : (core M).TotalSpace)
    (hp : p.proj ∈ i.val.source) :
    (core M).localTriv i p = (p.proj, id (α := ℂ) p.2) := by
  apply Prod.ext
  · rfl
  · change jacobian M i (achart Model p.proj) p.proj * id (α := ℂ) p.2 = _
    rw [hdet i (achart Model p.proj) p.proj hp (mem_chart_source Model p.proj), one_mul]

def toProduct (p : (core M).TotalSpace) : M × ℂ := (p.proj, p.2)

def fromProduct (p : M × ℂ) : (core M).TotalSpace := ⟨p.1, p.2⟩

theorem toProduct_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (toProduct M) := by
  intro p
  let e := trivializationAt ℂ (core M).Fiber p.proj
  have hp : p ∈ e.source := mem_chart_source Model p.proj
  have he : ContMDiffAt ((I).prod I₁) ((I).prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp)
  apply he.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (localTriv_eq_of_jacobian_one M hdet (achart Model p.proj) q hq).symm

theorem fromProduct_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (fromProduct M) := by
  intro p
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  have hnhds : Prod.fst ⁻¹' (achart Model p.1).val.source ∈ 𝓝 p :=
    continuous_fst.continuousAt.preimage_mem_nhds
      ((achart Model p.1).val.open_source.mem_nhds (mem_chart_source Model p.1))
  apply contMDiffAt_snd.congr_of_eventuallyEq
  filter_upwards [hnhds] with q hq
  exact congrArg Prod.snd (localTriv_eq_of_jacobian_one M hdet (achart Model p.1)
    (fromProduct M q) hq)

/-- A fibrewise-linear analytic trivialization, verified in the original
bundle atlas using determinant one only on genuine chart overlaps. -/
def globalTrivialization :
    Diffeomorph ((I).prod I₁) ((I).prod I₁) (core M).TotalSpace (M × ℂ) ω where
  toFun := toProduct M
  invFun := fromProduct M
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  contMDiff_toFun := toProduct_holomorphic M hdet
  contMDiff_invFun := fromProduct_holomorphic M hdet

@[simp] theorem globalTrivialization_fst (p : (core M).TotalSpace) :
    (globalTrivialization M hdet p).1 = p.proj := rfl

@[simp] theorem globalTrivialization_symm_proj (p : M × ℂ) :
    ((globalTrivialization M hdet).symm p).proj = p.1 := rfl

theorem globalTrivialization_add (x : M) (v w : (core M).Fiber x) :
    (globalTrivialization M hdet ⟨x, v + w⟩).2 =
      (globalTrivialization M hdet ⟨x, v⟩).2 +
        (globalTrivialization M hdet ⟨x, w⟩).2 := rfl

theorem globalTrivialization_smul (x : M) (a : ℂ) (v : (core M).Fiber x) :
    (globalTrivialization M hdet ⟨x, a • v⟩).2 =
      a • (globalTrivialization M hdet ⟨x, v⟩).2 := rfl

@[simp] theorem globalTrivialization_frame (x : M) :
    globalTrivialization M hdet ⟨x, unitFrame M x⟩ = (x, 1) := rfl

/-- The same map as a vector-bundle trivialization over all of the base. -/
def bundleTrivialization : Trivialization ℂ
    (Bundle.TotalSpace.proj : (core M).TotalSpace → M) where
  toOpenPartialHomeomorph := (globalTrivialization M hdet).toHomeomorph.toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

@[simp] theorem bundleTrivialization_baseSet :
    (bundleTrivialization M hdet).baseSet = univ := rfl

instance bundleTrivialization_isLinear : (bundleTrivialization M hdet).IsLinear ℂ where
  linear x _ :=
    { map_add := fun v w => globalTrivialization_add M hdet x v w
      map_smul := fun c v => globalTrivialization_smul M hdet x c v }

theorem bundleTrivialization_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (bundleTrivialization M hdet) :=
  (globalTrivialization M hdet).contMDiff

theorem bundleTrivialization_symm_holomorphic :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω
      (bundleTrivialization M hdet).toOpenPartialHomeomorph.symm :=
  (globalTrivialization M hdet).symm.contMDiff

end UnitJacobian

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Atlas
