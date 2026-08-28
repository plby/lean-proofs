import Wikipedia.SmoothSixDPoincare.OpenGluing
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The actual charts of an open gluing

Both original atlases are lifted through the proved open embeddings. Their
cross-patch transition is exactly the prescribed gluing map, between the
original charts, on exactly its source.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

section Transition

variable {X Y Z H : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace H] [Nonempty H]

theorem lift_transition (e : OpenPartialHomeomorph X Y)
    {i : X → Z} {j : Y → Z} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
    (hij : ∀ x y, i x = j y ↔ x ∈ e.source ∧ e x = y)
    (c : OpenPartialHomeomorph X H) (d : OpenPartialHomeomorph Y H) :
    (c.lift_openEmbedding hi).symm.trans (d.lift_openEmbedding hj) ≈
      (c.symm.trans e).trans d := by
  constructor
  · ext z
    change (z ∈ c.target ∧ i (c.symm z) ∈ j '' d.source) ↔
      (z ∈ c.target ∧ c.symm z ∈ e.source) ∧ e (c.symm z) ∈ d.source
    constructor
    · rintro ⟨hz, y, hy, hyz⟩
      obtain ⟨hs, he⟩ := (hij _ _).mp hyz.symm
      exact ⟨⟨hz, hs⟩, he.symm ▸ hy⟩
    · rintro ⟨⟨hz, hs⟩, hd⟩
      exact ⟨hz, e (c.symm z), hd, ((hij _ _).mpr ⟨hs, rfl⟩).symm⟩
  · intro z hz
    change z ∈ c.target ∧ i (c.symm z) ∈ j '' d.source at hz
    obtain ⟨y, hy, hyz⟩ := hz.2
    obtain ⟨hs, he⟩ := (hij _ _).mp hyz.symm
    change (d.lift_openEmbedding hj) (i (c.symm z)) = d (e (c.symm z))
    rw [← hyz, OpenPartialHomeomorph.lift_openEmbedding_apply, he]

end Transition

variable {X Y H : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace H] [Nonempty H] [ChartedSpace H X] [ChartedSpace H Y]
  (e : OpenPartialHomeomorph X Y)

def gluedAtlas : Set (OpenPartialHomeomorph (Space e) H) :=
  ((fun c => c.lift_openEmbedding (left_isOpenEmbedding e)) '' atlas H X) ∪
    ((fun d => d.lift_openEmbedding (right_isOpenEmbedding e)) '' atlas H Y)

theorem exists_chart (z : Space e) :
    ∃ c ∈ gluedAtlas (H := H) e, z ∈ c.source := by
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := cover e z
  · refine ⟨(chartAt H x).lift_openEmbedding (left_isOpenEmbedding e),
      Or.inl ⟨chartAt H x, chart_mem_atlas H x, rfl⟩, ?_⟩
    exact ⟨x, mem_chart_source H x, rfl⟩
  · refine ⟨(chartAt H y).lift_openEmbedding (right_isOpenEmbedding e),
      Or.inr ⟨chartAt H y, chart_mem_atlas H y, rfl⟩, ?_⟩
    exact ⟨y, mem_chart_source H y, rfl⟩

/-- The quotient topology with the two original atlases, not a substitute space. -/
@[instance_reducible]
def chartedSpace : ChartedSpace H (Space e) where
  atlas := gluedAtlas e
  chartAt z := (exists_chart (H := H) e z).choose
  mem_chart_source z := (exists_chart (H := H) e z).choose_spec.2
  chart_mem_atlas z := (exists_chart (H := H) e z).choose_spec.1

theorem left_chart_mem_atlas (c : OpenPartialHomeomorph X H) (hc : c ∈ atlas H X) :
    letI := chartedSpace (H := H) e
    c.lift_openEmbedding (left_isOpenEmbedding e) ∈ atlas H (Space e) :=
  Or.inl ⟨c, hc, rfl⟩

theorem right_chart_mem_atlas (d : OpenPartialHomeomorph Y H) (hd : d ∈ atlas H Y) :
    letI := chartedSpace (H := H) e
    d.lift_openEmbedding (right_isOpenEmbedding e) ∈ atlas H (Space e) :=
  Or.inr ⟨d, hd, rfl⟩

omit [ChartedSpace H X] [ChartedSpace H Y] in
theorem left_right_transition (c : OpenPartialHomeomorph X H)
    (d : OpenPartialHomeomorph Y H) :
    (c.lift_openEmbedding (left_isOpenEmbedding e)).symm.trans
        (d.lift_openEmbedding (right_isOpenEmbedding e)) ≈ (c.symm.trans e).trans d :=
  lift_transition e (left_isOpenEmbedding e) (right_isOpenEmbedding e) (left_eq_right e) c d

omit [ChartedSpace H X] [ChartedSpace H Y] in
theorem right_left_transition (d : OpenPartialHomeomorph Y H)
    (c : OpenPartialHomeomorph X H) :
    (d.lift_openEmbedding (right_isOpenEmbedding e)).symm.trans
        (c.lift_openEmbedding (left_isOpenEmbedding e)) ≈ (d.symm.trans e.symm).trans c :=
  lift_transition e.symm (right_isOpenEmbedding e) (left_isOpenEmbedding e)
    (right_eq_left e) d c

end Wikipedia.SmoothSixDPoincare.OpenGluing
