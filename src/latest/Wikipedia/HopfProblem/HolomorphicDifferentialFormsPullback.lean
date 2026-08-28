import Wikipedia.HopfProblem.HolomorphicDifferentialForms
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Actual derivative pullback of holomorphic forms

Pullback is composition of the genuine alternating tangent covector with
the actual manifold derivative. Analyticity follows in the native tangent
trivializations, not from a separately supplied coefficient formula.
-/

noncomputable section

open Bundle Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]
  {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, F) ω N] {p : ℕ}

/-- Literal pullback on the full actual tangent covectors. -/
def pullbackCovector (f : M → N) (θ : Form F N p) (x : M) : Covector E M p x :=
  (θ (f x)).compContinuousLinearMap (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Its coordinate formula uses the actual derivative written in the
original source and target tangent trivializations. -/
theorem pullbackCovector_coordinates (f : M → N) (θ : Form F N p) (x₀ x : M)
    (hx : f x ∈ (chartAt F (f x₀)).source) :
    (trivializationAt (E [⋀^Fin p]→L[ℂ] ℂ) (Covector E M p) x₀
      ⟨x, pullbackCovector f θ x⟩).2 =
      (inCoordinates F N θ (f x₀) (f x)).compContinuousLinearMap
        (inTangentCoordinates 𝓘(ℂ, E) 𝓘(ℂ, F) id f
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f) x₀ x) := by
  have hx' : f x ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) (f x₀)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  ext v
  have hv := congrArg (θ (f x)) (funext fun i : Fin p =>
    ((trivializationAt F (TangentSpace 𝓘(ℂ, F)) (f x₀)).symmL_continuousLinearMapAt
      (R := ℂ) hx' (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x
        ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).symmL ℂ x (v i)))).symm)
  simpa [FiberBundle.trivializationAt_continuousAlternatingMap_apply,
    pullbackCovector, inCoordinates_eq, ContinuousAlternatingMap.inCoordinates,
    inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.comp_def] using hv

/-- Pullback by an actual holomorphic map is a holomorphic section of
the original alternating cotangent bundle. -/
theorem pullbackCovector_holomorphic (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) (θ : Form F N p) :
    ContMDiff 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E [⋀^Fin p]→L[ℂ] ℂ)) ω
      (fun x => (⟨x, pullbackCovector f θ x⟩ : TotalSpace E M p)) := by
  intro x₀
  apply (contMDiffAt_section _).mpr
  have hθ := (inCoordinates_holomorphicAt F N θ (f x₀)).comp x₀ (hf x₀)
  have hdf := (hf x₀).mfderiv_const (m := ω) (by simp)
  have hc := ((HolomorphicAlternatingMaps.pullback_apply_contDiff E ℂ p F).contMDiff
    (inCoordinates F N θ (f x₀) (f x₀),
      inTangentCoordinates 𝓘(ℂ, E) 𝓘(ℂ, F) id f
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f) x₀ x₀)).comp x₀ (hθ.prodMk_space hdf)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf x₀).continuousAt.preimage_mem_nhds
    ((chartAt F (f x₀)).open_source.mem_nhds (mem_chart_source F (f x₀)))] with x hx
  exact pullbackCovector_coordinates (E := E) (F := F) f θ x₀ x hx

/-- The complex-linear pullback on all genuine holomorphic forms. -/
def pullback (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) :
    Form F N p →ₗ[ℂ] Form E M p where
  toFun θ := ⟨pullbackCovector f θ, pullbackCovector_holomorphic f hf θ⟩
  map_add' θ η := by
    apply ContMDiffSection.ext
    intro x
    ext v
    rfl
  map_smul' a θ := by
    apply ContMDiffSection.ext
    intro x
    ext v
    rfl

@[simp] theorem pullback_apply (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (θ : Form F N p) (x : M) :
    pullback f hf θ x =
      (θ (f x)).compContinuousLinearMap (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) :=
  rfl

end Wikipedia.HopfProblem.HolomorphicDifferentialForms
