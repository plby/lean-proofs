import Wikipedia.HopfProblem.HolomorphicVectorFields
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDescentHolomorphic

/-!
# Actual descent of the projected holomorphic vector field

The derivative of the constructed sphere projection sends a genuine
holomorphic tangent section to an analytic map into the sphere tangent
bundle. Its scalar coordinates descend by the proved holomorphic
function descent theorem. The resulting section is a holomorphic field
on the original sphere, not a prescribed family of chart coefficients.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

open Wikipedia.HopfProblem.HolomorphicVectorFields

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- A genuine global holomorphic field on the actual compact threefold. -/
abbrev Field := Wikipedia.HopfProblem.HolomorphicVectorFields.Field
  (ℂ × ComplexPlane₂) Threefold.Space

/-- The actual projection differential applied to a native tangent field. -/
def differential (v : Field) (x : Threefold.Space) :
    TangentSpace 𝓘(ℂ) (Threefold.projectionSphere x) :=
  mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x (v x)

/-- The full domain of a native sphere chart. -/
def baseChartOpen (b : RiemannSphere) : Opens RiemannSphere :=
  ⟨(chartAt ℂ b).source, (chartAt ℂ b).open_source⟩

/-- The literal coefficient of the projected field in a target chart. -/
def localDifferential (v : Field) (b : RiemannSphere) :
    Threefold.basePreimage (baseChartOpen b) → ℂ :=
  fun x => alongMapCoordinates (ℂ × ComplexPlane₂) Threefold.Space (F := ℂ)
    v Threefold.projectionSphere b x.val

theorem localDifferential_holomorphic (v : Field) (b : RiemannSphere) :
    ContMDiff IF 𝓘(ℂ) ω (localDifferential v b) := by
  intro x
  exact (alongMapCoordinates_holomorphicAt (ℂ × ComplexPlane₂) Threefold.Space
    (F := ℂ) v Threefold.projectionSphere_holomorphic b x.property).comp x
      (contMDiff_subtype_val x)

def localSection (v : Field) (b : RiemannSphere) :
    Threefold.PreimageSection (baseChartOpen b) :=
  ⟨localDifferential v b, localDifferential_holomorphic v b⟩

/-- Actual scalar holomorphic descent, already proved for every base open set. -/
def localDescended (v : Field) (b : RiemannSphere) :
    Threefold.BaseSection (baseChartOpen b) :=
  Threefold.descendedSection (baseChartOpen b) (localSection v b)

@[simp] theorem localDescended_projection (v : Field) (b : RiemannSphere)
    (x : Threefold.basePreimage (baseChartOpen b)) :
    localDescended v b (Threefold.baseProjection (baseChartOpen b) x) =
      localDifferential v b x :=
  Threefold.descendedFunction_projection (baseChartOpen b) (localDifferential v b)
    (localDifferential_holomorphic v b) x

/-- Equality of projected values on a literal fibre follows from scalar
holomorphic descent in the native chart centered at that fibre's value. -/
theorem differential_fibre_eq (v : Field) {x y : Threefold.Space}
    (hxy : Threefold.projectionSphere x = Threefold.projectionSphere y) :
    differential v x = differential v y := by
  let b := Threefold.projectionSphere x
  have hx : x ∈ Threefold.basePreimage (baseChartOpen b) := mem_chart_source ℂ b
  have hy : y ∈ Threefold.basePreimage (baseChartOpen b) := by
    change Threefold.projectionSphere y ∈ (chartAt ℂ b).source
    rw [← hxy]
    exact mem_chart_source ℂ b
  have h := Threefold.holomorphic_fibre_apply_eq (baseChartOpen b)
    (localDifferential v b) (localDifferential_holomorphic v b) ⟨x, hx⟩ ⟨y, hy⟩ hxy
  change (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b
      ⟨Threefold.projectionSphere x, differential v x⟩).2 =
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b
      ⟨Threefold.projectionSphere y, differential v y⟩).2 at h
  rw [← hxy] at h
  exact (tangentCoordinates_self ℂ RiemannSphere b (differential v x)).symm.trans
    (h.trans (tangentCoordinates_self ℂ RiemannSphere b (differential v y)))

/-- A chosen lift is used only to define the value; fibrewise equality
proves that the result is independent of that lift. -/
def sphereLift (b : RiemannSphere) : Threefold.Space :=
  (Threefold.baseLift ⊤ ⟨b, Set.mem_univ b⟩).val

@[simp] theorem sphereLift_projection (b : RiemannSphere) :
    Threefold.projectionSphere (sphereLift b) = b :=
  Threefold.projectionSphere_baseLift ⊤ ⟨b, Set.mem_univ b⟩

def descendedValue (v : Field) (b : RiemannSphere) : TangentSpace 𝓘(ℂ) b :=
  differential v (sphereLift b)

@[simp] theorem descendedValue_projection (v : Field) (x : Threefold.Space) :
    descendedValue v (Threefold.projectionSphere x) = differential v x :=
  differential_fibre_eq v (sphereLift_projection (Threefold.projectionSphere x))

/-- In every actual sphere tangent chart, the descended tangent value
has precisely the holomorphic coefficient constructed by scalar descent. -/
theorem descendedValue_coordinate (v : Field) (b : RiemannSphere)
    (p : baseChartOpen b) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b ⟨p.val, descendedValue v p.val⟩).2 =
      localDescended v b p := by
  obtain ⟨x, rfl⟩ := Threefold.baseProjection_surjective (baseChartOpen b) p
  rw [localDescended_projection]
  change (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b
      ⟨Threefold.projectionSphere x.val,
        descendedValue v (Threefold.projectionSphere x.val)⟩).2 = _
  rw [descendedValue_projection]
  rfl

/-- The descended values are a genuine holomorphic tangent section. -/
theorem descendedValue_holomorphic (v : Field) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (fun b => (⟨b, descendedValue v b⟩ : TangentBundle 𝓘(ℂ) RiemannSphere)) := by
  intro b
  apply (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt _ _ b) |>.mpr
  have hlocal : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun p : baseChartOpen b =>
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b
          ⟨p.val, descendedValue v p.val⟩).2) := by
    have heq : (fun p : baseChartOpen b =>
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b
          ⟨p.val, descendedValue v p.val⟩).2) = localDescended v b :=
      funext (descendedValue_coordinate v b)
    rw [heq]
    exact (localDescended v b).contMDiff
  exact (contMDiffAt_subtype_iff (U := baseChartOpen b)
    (x := ⟨b, mem_chart_source ℂ b⟩)).mp (hlocal ⟨b, mem_chart_source ℂ b⟩)

/-- The actual holomorphic vector field on the sphere obtained from df(v). -/
def descendedField (v : Field) : Wikipedia.HopfProblem.HolomorphicVectorFields.Field
    ℂ RiemannSphere :=
  ⟨descendedValue v, descendedValue_holomorphic v⟩

@[simp] theorem descendedField_projection (v : Field) (x : Threefold.Space) :
    descendedField v (Threefold.projectionSphere x) =
      mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x (v x) :=
  descendedValue_projection v x

theorem descendedField_unique (v : Field)
    (w : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere)
    (hw : ∀ x, w (Threefold.projectionSphere x) =
      mfderiv IF 𝓘(ℂ) Threefold.projectionSphere x (v x)) : w = descendedField v := by
  apply ContMDiffSection.ext
  intro b
  obtain ⟨x, rfl⟩ := Threefold.projectionSphere_surjective b
  exact (hw x).trans (descendedField_projection v x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields
