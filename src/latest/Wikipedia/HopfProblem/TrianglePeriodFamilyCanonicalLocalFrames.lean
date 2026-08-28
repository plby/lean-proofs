import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAtlas

/-!
# Holomorphic local frames of the actual canonical bundle

Inverting the canonical bundle's actual chart trivialization at coefficient
`1` gives the local form `dz ∧ dζ₀ ∧ dζ₁`.  These frames are holomorphic and
nowhere zero on the natural open chart domains.  Their overlap coefficients
are the inverse determinants of the actual forward chart derivatives.
No determinant-one condition or additional transition data is assumed.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Atlas

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

instance core_localTriv_memTrivializationAtlas (i : atlas Model M) :
    MemTrivializationAtlas ((core M).localTriv i) where
  out := ⟨i, rfl⟩

/-- The source of an actual chart, with its natural open-submanifold structure. -/
abbrev chartSource (i : atlas Model M) : Opens M := ⟨i.val.source, i.val.open_source⟩

omit [IsManifold I ω M] in
@[simp] theorem mem_chartSource (i : atlas Model M) (x : M) :
    x ∈ chartSource M i ↔ x ∈ i.val.source := Iff.rfl

/-- The local canonical frame obtained from coefficient `1` in the actual
bundle trivialization associated to the chart. -/
def localFrame (i : atlas Model M) (x : chartSource M i) : (core M).Fiber (x : M) :=
  ((core M).localTriv i).symm (x : M) 1

/-- This is literally the inverse local trivialization, not a choice of a
nonzero scalar in the preferred model fibre. -/
theorem localFrame_localTriv (i : atlas Model M) (x : chartSource M i) :
    (core M).localTriv i ⟨(x : M), localFrame M i x⟩ = ((x : M), 1) :=
  ((core M).localTriv i).apply_mk_symm x.property 1

@[simp] theorem localFrame_localCoefficient (i : atlas Model M) (x : chartSource M i) :
    ((core M).localTriv i ⟨(x : M), localFrame M i x⟩).2 = 1 :=
  congrArg Prod.snd (localFrame_localTriv M i x)

/-- The frame's actual chart representation is the standard top covector. -/
@[simp] theorem localFrame_inCoordinates (i : atlas Model M) (x : chartSource M i) :
    inCoordinates M i (x : M) (localFrame M i x) = volume := by
  rw [inCoordinates, localFrame_localCoefficient]
  change (1 : ℂ) • volume = volume
  exact one_smul ℂ volume

theorem localFrame_ne_zero (i : atlas Model M) (x : chartSource M i) :
    localFrame M i x ≠ 0 := by
  intro h
  apply volume_ne_zero
  calc
    volume = coordinateEquiv M i x.property (localFrame M i x) :=
      (localFrame_inCoordinates M i x).symm
    _ = 0 := by rw [h, map_zero]

/-- The frame as a map into the original canonical bundle total space. -/
def localFrameSection (i : atlas Model M) (x : chartSource M i) : (core M).TotalSpace :=
  ⟨(x : M), localFrame M i x⟩

@[simp] theorem localFrameSection_proj (i : atlas Model M) (x : chartSource M i) :
    (localFrameSection M i x).proj = (x : M) := rfl

/-- Holomorphicity is verified in the bundle's original local trivialization
and the open subtype's inherited manifold atlas. -/
theorem localFrameSection_holomorphic (i : atlas Model M) :
    ContMDiff I ((I).prod I₁) ω (localFrameSection M i) := by
  apply ((core M).localTriv i).contMDiff_iff (fun x => x.property) |>.mpr
  refine ⟨contMDiff_subtype_val, ?_⟩
  have h : (fun x : chartSource M i =>
      ((core M).localTriv i (localFrameSection M i x)).2) = fun _ => (1 : ℂ) := by
    funext x
    exact localFrame_localCoefficient M i x
  rw [h]
  exact contMDiff_const

/-- In another chart, the same frame is the reverse-Jacobian multiple of
the standard volume. -/
theorem localFrame_inCoordinates_change (i j : atlas Model M) (x : chartSource M i)
    (hj : (x : M) ∈ j.val.source) :
    inCoordinates M j (x : M) (localFrame M i x) =
      jacobian M j i x • volume := by
  rw [inCoordinates_change M i j x.property hj, localFrame_inCoordinates,
    volume_pullback, ← jacobian_eq_fderiv]

theorem localFrame_localCoefficient_change (i j : atlas Model M) (x : chartSource M i)
    (hj : (x : M) ∈ j.val.source) :
    ((core M).localTriv j ⟨(x : M), localFrame M i x⟩).2 = jacobian M j i x := by
  apply coefficientEquiv.injective
  exact localFrame_inCoordinates_change M i j x hj

/-- The overlap coefficient is the inverse forward chart Jacobian. -/
theorem localFrame_localCoefficient_inverse_jacobian
    (i j : atlas Model M) (x : chartSource M i) (hj : (x : M) ∈ j.val.source) :
    ((core M).localTriv j ⟨(x : M), localFrame M i x⟩).2 =
      (LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ := by
  rw [localFrame_localCoefficient_change M i j x hj,
    jacobian_reverse M i j x.property hj, jacobian_eq_fderiv]

/-- Equality of the two actual fibre vectors on a chart overlap. -/
theorem localFrame_change (i j : atlas Model M) (x : chartSource M i)
    (hj : (x : M) ∈ j.val.source) :
    localFrame M i x = jacobian M j i x • localFrame M j ⟨(x : M), hj⟩ := by
  apply (coordinateEquiv M j hj).injective
  rw [map_smul, coordinateEquiv_apply, coordinateEquiv_apply,
    localFrame_inCoordinates_change M i j x hj]
  exact congrArg (fun α : TopCovector => jacobian M j i (x : M) • α)
    (localFrame_inCoordinates M j ⟨(x : M), hj⟩).symm

/-- The chart trivialization supplies the full scalar-to-fibre equivalence
whose unit vector is this frame. -/
def localFrameEquiv (i : atlas Model M) (x : chartSource M i) :
    ℂ ≃L[ℂ] (core M).Fiber (x : M) :=
  (((core M).localTriv i).continuousLinearEquivAt ℂ (x : M) x.property).symm

@[simp] theorem localFrameEquiv_one (i : atlas Model M) (x : chartSource M i) :
    localFrameEquiv M i x 1 = localFrame M i x := rfl

theorem localFrameEquiv_apply (i : atlas Model M) (x : chartSource M i) (c : ℂ) :
    localFrameEquiv M i x c = c • localFrame M i x := by
  calc
    localFrameEquiv M i x c = localFrameEquiv M i x (c • (1 : ℂ)) := by simp
    _ = c • localFrame M i x := by rw [map_smul, localFrameEquiv_one]

/-- The natural open intersection of two chart domains. -/
abbrev chartOverlap (i j : atlas Model M) : Opens M :=
  chartSource M i ⊓ chartSource M j

/-- The coefficient of the first chart's local frame in the second chart's
actual bundle trivialization. -/
def localOverlapCoefficient (i j : atlas Model M) (x : chartOverlap M i j) : ℂ :=
  ((core M).localTriv j
    ⟨(x : M), localFrame M i ⟨(x : M), x.property.1⟩⟩).2

@[simp] theorem localOverlapCoefficient_eq_jacobian (i j : atlas Model M)
    (x : chartOverlap M i j) :
    localOverlapCoefficient M i j x = jacobian M j i x :=
  localFrame_localCoefficient_change M i j ⟨(x : M), x.property.1⟩ x.property.2

theorem localOverlapCoefficient_eq_inverse_jacobian (i j : atlas Model M)
    (x : chartOverlap M i j) :
    localOverlapCoefficient M i j x =
      (LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ :=
  localFrame_localCoefficient_inverse_jacobian M i j
    ⟨(x : M), x.property.1⟩ x.property.2

theorem localOverlapCoefficient_ne_zero (i j : atlas Model M)
    (x : chartOverlap M i j) : localOverlapCoefficient M i j x ≠ 0 := by
  rw [localOverlapCoefficient_eq_jacobian]
  exact jacobian_ne_zero M j i x.property.2 x.property.1

theorem localOverlapCoefficient_holomorphic (i j : atlas Model M) :
    ContMDiff I I₁ ω (localOverlapCoefficient M i j) := by
  have hfun : localOverlapCoefficient M i j =
      (fun x : chartOverlap M i j => jacobian M j i x) :=
    funext (localOverlapCoefficient_eq_jacobian M i j)
  rw [hfun]
  intro x
  have hjac : ContMDiffAt I I₁ ω (jacobian M j i) (x : M) :=
    (jacobian_holomorphicOn M j i).contMDiffAt
      ((j.val.open_source.inter i.val.open_source).mem_nhds
        ⟨x.property.2, x.property.1⟩)
  exact hjac.comp x contMDiff_subtype_val.contMDiffAt

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Atlas
