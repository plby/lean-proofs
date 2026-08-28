import Mathlib.Topology.Gluing
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Gluing local spaces over a covered base

This constructs an actual topological gluing over an open cover of a base.
Transition maps are defined on full inverse images of base intersections,
preserve the base, and satisfy a cocycle. The resulting local identifications
are proved, not supplied as properties of an assumed global space.
-/

noncomputable section

open Set Topology TopologicalSpace

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing

/-- Actual local gluing data over an open cover of the base. -/
structure Data (B : Type u) [TopologicalSpace B] where
  J : Type u
  patch : J → Opens B
  cover : IsOpenCover patch
  piece : J → TopCat.{u}
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  transition : ∀ i j, OpenPartialHomeomorph (piece i) (piece j)
  source_eq : ∀ i j, (transition i j).source = toBase i ⁻¹' (patch j : Set B)
  self_eq : ∀ i, transition i i = OpenPartialHomeomorph.refl (piece i)
  symm_eq : ∀ i j, (transition i j).symm = transition j i
  preserves_base : ∀ i j x, x ∈ (transition i j).source →
    toBase j (transition i j x) = toBase i x
  cocycle : ∀ i j k x, x ∈ (transition i j).source →
    transition i j x ∈ (transition j k).source →
    transition j k (transition i j x) = transition i k x

namespace Data

variable {B : Type u} [TopologicalSpace B] (D : Data B)

theorem transition_map_source (i j : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) :
    D.transition i j x ∈ (D.transition j i).source := by
  rw [← D.symm_eq i j]
  exact (D.transition i j).map_source hx

theorem transition_inter (i j k : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) (hk : x ∈ (D.transition i k).source) :
    D.transition i j x ∈ (D.transition j k).source := by
  rw [D.source_eq] at hk ⊢
  change D.toBase j (D.transition i j x) ∈ D.patch k
  rw [D.preserves_base i j x hx]
  exact hk

/-- The topological gluing core uses the given full base overlaps. -/
abbrev gluingCore : TopCat.GlueData.MkCore where
  J := D.J
  U := D.piece
  V i j := ⟨(D.transition i j).source, (D.transition i j).open_source⟩
  t i j := TopCat.ofHom {
    toFun := fun x => ⟨D.transition i j x, D.transition_map_source i j x.property⟩
    continuous_toFun := (D.transition i j).continuousOn.domRestrict.subtype_mk _ }
  V_id i := by apply Opens.ext; simp [D.self_eq]
  t_id i := by
    funext x
    exact Subtype.ext (congrArg
      (fun e : OpenPartialHomeomorph (D.piece i) (D.piece i) => e x.val) (D.self_eq i))
  t_inter := by
    intro i j k x hx
    exact D.transition_inter i j k x.property hx
  cocycle i j k x hx := D.cocycle i j k x x.property
    (D.transition_inter i j k x.property hx)

abbrev gluing : TopCat.GlueData := TopCat.GlueData.mk' D.gluingCore

/-- The actual categorical/topological gluing of the local pieces. -/
abbrev Space := D.gluing.toGlueData.glued

def inclusion (i : D.J) : D.piece i → D.Space := D.gluing.toGlueData.ι i

theorem inclusion_openEmbedding (i : D.J) : IsOpenEmbedding (D.inclusion i) :=
  D.gluing.ι_isOpenEmbedding i

theorem inclusion_jointly_surjective (x : D.Space) :
    ∃ i z, D.inclusion i z = x := D.gluing.ι_jointly_surjective x

theorem inclusion_eq_iff (i j : D.J) (x : D.piece i) (y : D.piece j) :
    D.inclusion i x = D.inclusion j y ↔
      x ∈ (D.transition i j).source ∧ D.transition i j x = y := by
  refine (D.gluing.ι_eq_iff_rel i j x y).trans ?_
  constructor
  · rintro ⟨⟨z, hz⟩, hzx, hzy⟩
    change z = x at hzx
    change D.transition i j z = y at hzy
    subst z
    exact ⟨hz, hzy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨x, hx⟩, rfl, hxy⟩

/-- A representative used to define the descended base map. -/
def representative (x : D.Space) : Σ i, D.piece i :=
  ⟨(D.inclusion_jointly_surjective x).choose,
    (D.inclusion_jointly_surjective x).choose_spec.choose⟩

theorem inclusion_representative (x : D.Space) :
    D.inclusion (D.representative x).1 (D.representative x).2 = x :=
  (D.inclusion_jointly_surjective x).choose_spec.choose_spec

/-- The actual base projection on the glued space. -/
def projection (x : D.Space) : B :=
  D.toBase (D.representative x).1 (D.representative x).2

@[simp] theorem projection_inclusion (i : D.J) (x : D.piece i) :
    D.projection (D.inclusion i x) = D.toBase i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change D.toBase r.1 r.2 = D.toBase i x
  rw [← h.2]
  exact (D.preserves_base r.1 i r.2 h.1).symm

theorem projection_continuous : Continuous D.projection := by
  rw [continuous_def]
  intro U hU
  rw [D.gluing.isOpen_iff]
  change ∀ i : D.J, IsOpen (D.inclusion i ⁻¹' (D.projection ⁻¹' U))
  intro i
  convert hU.preimage (D.toBase i).continuous using 1
  ext x
  change D.projection (D.inclusion i x) ∈ U ↔ D.toBase i x ∈ U
  rw [D.projection_inclusion]

/-- Each piece is the entire inverse image of its base patch. -/
theorem inclusion_range (i : D.J) :
    range (D.inclusion i) = D.projection ⁻¹' (D.patch i : Set B) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change D.projection (D.inclusion i z) ∈ D.patch i
    rw [D.projection_inclusion]
    exact D.toBase_mem i z
  · intro hx
    obtain ⟨j, z, rfl⟩ := D.inclusion_jointly_surjective x
    have hz : z ∈ (D.transition j i).source := by
      rw [D.source_eq]
      simpa only [mem_preimage, projection_inclusion] using hx
    exact ⟨D.transition j i z, ((D.inclusion_eq_iff j i z _).mpr ⟨hz, rfl⟩).symm⟩

/-- The local map with its correct open-patch codomain. -/
def localProjection (i : D.J) : C(D.piece i, D.patch i) where
  toFun x := ⟨D.toBase i x, D.toBase_mem i x⟩
  continuous_toFun := (D.toBase i).continuous.subtype_mk _

/-- Each piece is homeomorphic to the full inverse image of its base patch. -/
def patchHomeomorph (i : D.J) :
    D.piece i ≃ₜ (D.projection ⁻¹' (D.patch i : Set B)) :=
  (D.inclusion_openEmbedding i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (D.inclusion_range i))

@[simp] theorem patchHomeomorph_val (i : D.J) (x : D.piece i) :
    (D.patchHomeomorph i x).val = D.inclusion i x := rfl

theorem patchHomeomorph_projection (i : D.J) (x : D.piece i) :
    (D.patch i : Set B).restrictPreimage D.projection (D.patchHomeomorph i x) =
      D.localProjection i x := by
  apply Subtype.ext
  exact D.projection_inclusion i x

/-- Hausdorff local pieces over a Hausdorff base glue to a Hausdorff space.
Full inverse-image overlaps rule out doubled points over a base patch. -/
instance spaceT2 [T2Space B] [∀ i, T2Space (D.piece i)] : T2Space D.Space := by
  constructor
  intro x y hxy
  by_cases hb : D.projection x = D.projection y
  · obtain ⟨i, hi⟩ := D.cover.exists_mem (D.projection x)
    have hx : x ∈ range (D.inclusion i) := by rw [D.inclusion_range]; exact hi
    have hy : y ∈ range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection y ∈ D.patch i
      rw [← hb]
      exact hi
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (congrArg (D.inclusion i) h)
    obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation hab
    refine ⟨D.inclusion i '' U, D.inclusion i '' V,
      (D.inclusion_openEmbedding i).isOpenMap _ hU,
      (D.inclusion_openEmbedding i).isOpenMap _ hV,
      mem_image_of_mem _ ha, mem_image_of_mem _ hb, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb', hzb⟩
    have hab' := (D.inclusion_openEmbedding i).injective (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hUV) ha' (hab'.symm ▸ hb')
  · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hb
    exact ⟨D.projection ⁻¹' U, D.projection ⁻¹' V,
      hU.preimage D.projection_continuous, hV.preimage D.projection_continuous,
      hx, hy, hUV.preimage D.projection⟩

section Parametrizations

variable [∀ i, Nonempty (D.piece i)]

/-- The canonical partial parametrization by any nonempty local piece. -/
def parametrization (i : D.J) : OpenPartialHomeomorph (D.piece i) D.Space :=
  (D.inclusion_openEmbedding i).toOpenPartialHomeomorph (D.inclusion i)

@[simp] theorem parametrization_apply (i : D.J) (x : D.piece i) :
    D.parametrization i x = D.inclusion i x := rfl

@[simp] theorem parametrization_source (i : D.J) :
    (D.parametrization i).source = univ := rfl

@[simp] theorem parametrization_target (i : D.J) :
    (D.parametrization i).target = range (D.inclusion i) := by
  simp [parametrization]

theorem parametrization_transition (i j : D.J) {x : D.piece i}
    (hx : D.inclusion i x ∈ range (D.inclusion j)) :
    x ∈ (D.transition i j).source ∧
      (D.parametrization j).symm (D.inclusion i x) = D.transition i j x := by
  obtain ⟨y, hy⟩ := hx
  have he := (D.inclusion_eq_iff i j x y).mp hy.symm
  refine ⟨he.1, ?_⟩
  rw [← hy]
  exact ((D.inclusion_openEmbedding j).toOpenPartialHomeomorph_left_inv).trans he.2.symm

end Parametrizations

end Data

end Wikipedia.HopfProblem.ThreefoldGluing
