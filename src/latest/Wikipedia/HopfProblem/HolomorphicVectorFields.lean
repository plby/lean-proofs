import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Holomorphic sections of the native tangent bundle

A holomorphic vector field is an analytic section of Mathlib's actual
tangent bundle. Its image under a holomorphic map is an analytic map to
the target tangent bundle, with the genuine manifold differential.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicVectorFields

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- All analytic sections of the original tangent bundle. -/
abbrev Field := ContMDiffSection 𝓘(ℂ, E) E ω (TangentSpace 𝓘(ℂ, E) : M → Type _)

/-- Actual tangent-trivialization coordinates of a holomorphic field. -/
def inCoordinates (v : Field E M) (x₀ x : M) : E :=
  (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀ ⟨x, v x⟩).2

/-- The chosen tangent chart acts as the identity at its own center. -/
theorem tangentCoordinates_self (x : M) (w : TangentSpace 𝓘(ℂ, E) x) :
    (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x ⟨x, w⟩).2 = w := by
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℂ _
    (mem_baseSet_trivializationAt _ _ x),
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source E x)]
  exact (tangentBundleCore 𝓘(ℂ, E) M).coordChange_self
    (achart E x) x (mem_chart_source E x) w

theorem inCoordinates_self (v : Field E M) (x : M) :
    inCoordinates E M v x x = v x := tangentCoordinates_self E M x (v x)

theorem inCoordinates_holomorphicOn (v : Field E M) (x₀ : M) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (inCoordinates E M v x₀)
      (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).baseSet :=
  (Trivialization.contMDiffOn_section_baseSet_iff
    (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀)).mp v.contMDiff.contMDiffOn

theorem inCoordinates_holomorphicAt (v : Field E M) (x₀ : M) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (inCoordinates E M v x₀) x₀ :=
  (inCoordinates_holomorphicOn E M v x₀).contMDiffAt
    ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀))

theorem eq_zero_iff (v : Field E M) : v = 0 ↔ ∀ x, v x = 0 := by
  constructor
  · rintro rfl x
    rfl
  · intro h
    exact ContMDiffSection.ext h

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]

/-- The genuine differential of a map, evaluated on a native field. -/
def alongMap (v : Field E M) (f : M → N) (x : M) : TangentBundle 𝓘(ℂ, F) N :=
  ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x (v x)⟩

omit [IsManifold 𝓘(ℂ, F) ω N] in
@[simp] theorem alongMap_proj (v : Field E M) (f : M → N) (x : M) :
    (alongMap E M (F := F) v f x).proj = f x := rfl

omit [IsManifold 𝓘(ℂ, F) ω N] in
@[simp] theorem alongMap_snd (v : Field E M) (f : M → N) (x : M) :
    (alongMap E M (F := F) v f x).2 = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x (v x) := rfl

/-- This is holomorphic as a map to the original target tangent bundle,
not merely as a family of separately chosen scalar coefficients. -/
theorem alongMap_holomorphic (v : Field E M) {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) :
    ContMDiff 𝓘(ℂ, E) (𝓘(ℂ, F).prod 𝓘(ℂ, F)) ω (alongMap E M (F := F) v f) := by
  exact (hf.contMDiff_tangentMap (m := ω) (by simp)).comp v.contMDiff

/-- The actual coefficient of the differential in a fixed target chart. -/
def alongMapCoordinates (v : Field E M) (f : M → N) (b : N) (x : M) : F :=
  (trivializationAt F (TangentSpace 𝓘(ℂ, F)) b (alongMap E M (F := F) v f x)).2

theorem alongMapCoordinates_holomorphicAt (v : Field E M) {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) (b : N) {x : M}
    (hx : f x ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) b).baseSet) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω (alongMapCoordinates E M (F := F) v f b) x :=
  ((trivializationAt F (TangentSpace 𝓘(ℂ, F)) b).contMDiffAt_iff hx).mp
    (alongMap_holomorphic E M (F := F) v hf x) |>.2

theorem alongMapCoordinates_holomorphicOn (v : Field E M) {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) (b : N) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ω (alongMapCoordinates E M (F := F) v f b)
      (f ⁻¹' (trivializationAt F (TangentSpace 𝓘(ℂ, F)) b).baseSet) :=
  fun _ hx => (alongMapCoordinates_holomorphicAt E M (F := F) v hf b hx).contMDiffWithinAt

end Wikipedia.HopfProblem.HolomorphicVectorFields
