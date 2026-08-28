import Wikipedia.HopfProblem.HolomorphicVectorFields

/-!
# Gluing local holomorphic sections of the native tangent bundle

Compatible tangent sections on an open cover glue to an actual
`ContMDiffSection` of the original tangent bundle. Holomorphicity is local:
near every point the glued section equals one of the given sections.
-/

noncomputable section

open Bundle Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing

variable {ι E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  {U : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
  (s : ι → (x : M) → TangentSpace 𝓘(ℂ, E) x)
  (hs : ∀ i, ContMDiffOn 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω
    (fun x => (⟨x, s i x⟩ : TangentBundle 𝓘(ℂ, E) M)) (U i))
  (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → s i x = s j x)

/-- The global holomorphic tangent section obtained from compatible local sections. -/
def glueLocalSections : HolomorphicVectorFields.Field E M where
  toFun x := s (hcover x).choose x
  contMDiff_toFun := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    apply ((hs i).contMDiffAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq
    filter_upwards [(hU i).mem_nhds hi] with y hy
    exact congrArg (fun a : TangentSpace 𝓘(ℂ, E) y =>
      (⟨y, a⟩ : TangentBundle 𝓘(ℂ, E) M))
      (hcompat (hcover y).choose i y (hcover y).choose_spec hy)

/-- On each member of the cover, the glued native section is the supplied section. -/
@[simp] theorem glueLocalSections_apply (i : ι) {x : M} (hx : x ∈ U i) :
    glueLocalSections hU hcover s hs hcompat x = s i x :=
  hcompat (hcover x).choose i x (hcover x).choose_spec hx

/-- A global native holomorphic tangent section with these local values is unique. -/
theorem glueLocalSections_unique (v : HolomorphicVectorFields.Field E M)
    (hv : ∀ i x, x ∈ U i → v x = s i x) :
    v = glueLocalSections hU hcover s hs hcompat := by
  apply ContMDiffSection.ext
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact (hv i x hi).trans (glueLocalSections_apply hU hcover s hs hcompat i hi).symm

/-- The global section vanishes exactly when all of its local sections vanish
on the members of the cover. -/
theorem glueLocalSections_eq_zero_iff :
    glueLocalSections hU hcover s hs hcompat = 0 ↔
      ∀ i x, x ∈ U i → s i x = 0 := by
  rw [HolomorphicVectorFields.eq_zero_iff E M]
  constructor
  · intro h i x hx
    rw [← glueLocalSections_apply hU hcover s hs hcompat i hx]
    exact h x
  · intro h x
    obtain ⟨i, hi⟩ := hcover x
    rw [glueLocalSections_apply hU hcover s hs hcompat i hi]
    exact h i x hi

/-- Nonvanishing of the global section is detected by a nonzero value of one
of the local sections inside its own open set. -/
theorem glueLocalSections_ne_zero_iff :
    glueLocalSections hU hcover s hs hcompat ≠ 0 ↔
      ∃ i x, x ∈ U i ∧ s i x ≠ 0 := by
  classical
  simp only [ne_eq, glueLocalSections_eq_zero_iff, not_forall, exists_prop]

/-- A nonzero local value gives a nonzero global holomorphic vector field. -/
theorem glueLocalSections_ne_zero (i : ι) {x : M} (hx : x ∈ U i) (h : s i x ≠ 0) :
    glueLocalSections hU hcover s hs hcompat ≠ 0 :=
  (glueLocalSections_ne_zero_iff hU hcover s hs hcompat).mpr ⟨i, x, hx, h⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing
