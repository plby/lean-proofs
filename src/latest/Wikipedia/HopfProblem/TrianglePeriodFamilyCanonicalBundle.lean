import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAtlas
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalCoordinates

/-!
# The genuine canonical bundle of a varying-period family

The bundle below is built from the actual tangent atlas of the lattice
quotient, with fibres identified with the full alternating top-covector
spaces of its tangent spaces.  The determinant-one assertion for its
atlas is proved from the actual lattice shears, not supplied as a new
geometric hypothesis.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B]

/-- The canonical line bundle of the actual varying-period lattice quotient. -/
abbrev familyCanonicalBundle (P : HolomorphicPeriodMap ℂ B) :=
  letI := P.totalChartedSpace
  letI := P.totalSpace_isManifold
  Atlas.core P.TotalSpace

theorem familyCanonicalBundle_holomorphic (P : HolomorphicPeriodMap ℂ B) :
    letI := P.totalChartedSpace
    ContMDiffVectorBundle ω ℂ (familyCanonicalBundle P).Fiber I₃ := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  exact Atlas.holomorphicVectorBundle P.TotalSpace

/-- A fibre of this bundle is the actual full space of alternating
three-covectors on the corresponding tangent space. -/
def familyCanonicalIntrinsicEquiv (P : HolomorphicPeriodMap ℂ B) (x : P.TotalSpace) :
    letI := P.totalChartedSpace
    (familyCanonicalBundle P).Fiber x ≃L[ℂ]
      (TangentSpace I₃ x) [⋀^(Fin 3)]→L[ℂ] ℂ := by
  letI := P.totalChartedSpace
  letI := P.totalSpace_isManifold
  exact Atlas.intrinsicEquiv P.TotalSpace x

/-- A preferred chart is an index of the actual family atlas. -/
def familyChartIndex (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    letI := P.totalChartedSpace
    atlas Model P.TotalSpace :=
  letI := P.totalChartedSpace
  achart Model i

omit [IsManifold I₁ ω B] in
@[simp] theorem familyChartIndex_val (P : HolomorphicPeriodMap ℂ B) (i : P.TotalSpace) :
    (familyChartIndex P i).val = familyChart P i := rfl

/-- Representation of an actual canonical-bundle vector in an actual
preferred quotient chart. -/
def familyCanonicalInCoordinates (P : HolomorphicPeriodMap ℂ B) (i x : P.TotalSpace)
    (v : (familyCanonicalBundle P).Fiber x) : TopCovector :=
  letI := P.totalChartedSpace
  letI := P.totalSpace_isManifold
  Atlas.inCoordinates P.TotalSpace (familyChartIndex P i) x v

omit [IsManifold I₁ ω B] in
/-- The base point recovered by a valid family chart is its actual base
projection, independently of the selected local lattice lift. -/
theorem familyChart_inverse_base (P : HolomorphicPeriodMap ℂ B)
    (i x : P.TotalSpace) (hx : x ∈ (familyChart P i).source) :
    (chartAt ℂ (familyRepresentative P i).1).symm (familyChart P i x).1 = x.1 := by
  have h := familyChart_symm_apply P i (familyChart P i x)
  rw [(familyChart P i).left_inv hx] at h
  exact (congrArg Prod.fst h).symm

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

omit [IsManifold I₁ ω B] in
include hcoordinate in
/-- The first coordinate of every valid family chart is literally the
given common coordinate of its actual base projection. -/
theorem familyChart_first_coordinate (P : HolomorphicPeriodMap ℂ B)
    (i x : P.TotalSpace) (hx : x ∈ (familyChart P i).source) :
    (familyChart P i x).1 = coordinate x.1 := by
  have hz := (familyChart_target_subset P i ((familyChart P i).map_source hx)).1
  have h := base_chart_inverse_coordinate coordinate hcoordinate
    (familyRepresentative P i).1 hz
  rw [familyChart_inverse_base P i x hx] at h
  exact h.symm

include hcoordinate in
/-- Every pair of actual family atlas charts has Jacobian one at every
point where both charts are valid. -/
theorem family_atlas_jacobian (P : HolomorphicPeriodMap ℂ B) :
    letI := P.totalChartedSpace
    letI := P.totalSpace_isManifold
    ∀ (i j : atlas Model P.TotalSpace) (x : P.TotalSpace),
      x ∈ i.val.source → x ∈ j.val.source → Atlas.jacobian P.TotalSpace i j x = 1 := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  intro i j x hi hj
  have hir : i.val ∈ range (familyChart P) := i.property
  have hjr : j.val ∈ range (familyChart P) := j.property
  obtain ⟨a, ha⟩ := hir
  obtain ⟨b, hb⟩ := hjr
  rw [Atlas.jacobian_eq_fderiv, ← ha, ← hb]
  rw [← ha] at hi
  rw [← hb] at hj
  exact family_chart_transition_det_at coordinate hcoordinate P a b x hi hj

/-- The actual canonical-bundle vector represented by `dz ∧ dζ₀ ∧ dζ₁`
in the preferred tangent coordinates. -/
def familyCanonicalVolume (P : HolomorphicPeriodMap ℂ B) (x : P.TotalSpace) :
    (familyCanonicalBundle P).Fiber x :=
  letI := P.totalChartedSpace
  letI := P.totalSpace_isManifold
  Atlas.unitFrame P.TotalSpace x

theorem familyCanonicalVolume_ne_zero (P : HolomorphicPeriodMap ℂ B) (x : P.TotalSpace) :
    familyCanonicalVolume P x ≠ 0 := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  exact Atlas.unitFrame_ne_zero P.TotalSpace x

@[simp] theorem familyCanonicalIntrinsicEquiv_volume (P : HolomorphicPeriodMap ℂ B)
    (x : P.TotalSpace) :
    familyCanonicalIntrinsicEquiv P x (familyCanonicalVolume P x) = volume := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  exact Atlas.intrinsicEquiv_unitFrame P.TotalSpace x

include hcoordinate in
/-- Holomorphicity is a theorem about the original bundle topology and
atlas, proved using the actual lattice-transition Jacobians. -/
theorem familyCanonicalVolume_holomorphic (P : HolomorphicPeriodMap ℂ B) :
    letI := P.totalChartedSpace
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x => (⟨x, familyCanonicalVolume P x⟩ : (familyCanonicalBundle P).TotalSpace)) := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  exact Atlas.unitFrame_holomorphic P.TotalSpace
    (family_atlas_jacobian coordinate hcoordinate P)

include hcoordinate in
/-- Every valid quotient chart represents this genuine global form by
the literal base-first product volume. -/
theorem familyCanonicalVolume_inCoordinates (P : HolomorphicPeriodMap ℂ B)
    (i x : P.TotalSpace) (hx : x ∈ (familyChart P i).source) :
    familyCanonicalInCoordinates P i x (familyCanonicalVolume P x) = volume := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  exact Atlas.unitFrame_inCoordinates P.TotalSpace
    (family_atlas_jacobian coordinate hcoordinate P) (familyChartIndex P i) hx

/-- The actual canonical bundle is analytically and fibrewise-linearly
trivial over any of the common-coordinate bases considered here. -/
def familyCanonicalTrivialization (P : HolomorphicPeriodMap ℂ B) :
    letI := P.totalChartedSpace
    Diffeomorph ((I₃).prod I₁) ((I₃).prod I₁)
      (familyCanonicalBundle P).TotalSpace (P.TotalSpace × ℂ) ω :=
  letI := P.totalChartedSpace
  letI := P.totalSpace_isManifold
  Atlas.globalTrivialization P.TotalSpace (family_atlas_jacobian coordinate hcoordinate P)

@[simp] theorem familyCanonicalTrivialization_fst (P : HolomorphicPeriodMap ℂ B)
    (p : (familyCanonicalBundle P).TotalSpace) :
    (familyCanonicalTrivialization coordinate hcoordinate P p).1 = p.proj := rfl

theorem familyCanonicalTrivialization_add (P : HolomorphicPeriodMap ℂ B)
    (x : P.TotalSpace) (v w : (familyCanonicalBundle P).Fiber x) :
    (familyCanonicalTrivialization coordinate hcoordinate P ⟨x, v + w⟩).2 =
      (familyCanonicalTrivialization coordinate hcoordinate P ⟨x, v⟩).2 +
        (familyCanonicalTrivialization coordinate hcoordinate P ⟨x, w⟩).2 := rfl

theorem familyCanonicalTrivialization_smul (P : HolomorphicPeriodMap ℂ B)
    (x : P.TotalSpace) (c : ℂ) (v : (familyCanonicalBundle P).Fiber x) :
    (familyCanonicalTrivialization coordinate hcoordinate P ⟨x, c • v⟩).2 =
      c • (familyCanonicalTrivialization coordinate hcoordinate P ⟨x, v⟩).2 := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
