module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-!
## Manifold definitions, allowing minimal public imports
-/

open scoped ContDiff Manifold Topology
noncomputable section

/-!
## General manifolds
-/

variable {𝕜 E A F B M N : Type} [NontriviallyNormedField 𝕜]

/-- Analyticity in a neighborhood of a set (the manifold analogue of `AnalyticOnNhd`) -/
@[expose] public def ContMDiffOnNhd {𝕜 E A F B M N : Type} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace A M] [ChartedSpace B N] (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    (f : M → N) (s : Set M) : Prop := ∀ x ∈ s, ContMDiffAt I J ω f x

/-- A typeclass for trivial manifolds where `extChartAt` is the identity.
    In this case, `extChartAt I : E → E`, but the intermediate space `H` might be different.
    This is necessary to handle product spaces, where the intermediate space may be `ModelProd`. -/
public class ExtChartEqRefl [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] : Prop where
  eq_refl : ∀ x, extChartAt I x = PartialEquiv.refl E

/-- `extChartAt I x = refl` given [ExtChartEqRefl] -/
public theorem extChartAt_eq_refl [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    [ChartedSpace A E] {I : ModelWithCorners 𝕜 E A} [e : ExtChartEqRefl I] (x : E) :
    extChartAt I x = PartialEquiv.refl E :=
  e.eq_refl x

/-- `extChartAt = refl` for `I = modelWithCornersSelf 𝕜 E` -/
public instance extChartEqReflSelf [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    ExtChartEqRefl (modelWithCornersSelf 𝕜 E) := ⟨by
  simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, forall_const]⟩

/-- `extChartAt = refl` extends to products -/
public instance extChartEqReflProd [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [ChartedSpace A E]
    [ChartedSpace B F] {I : ModelWithCorners 𝕜 E A} [ExtChartEqRefl I] {J : ModelWithCorners 𝕜 F B}
    [ExtChartEqRefl J] : ExtChartEqRefl (I.prod J) :=
  ⟨fun x ↦ by simp_rw [extChartAt_prod, extChartAt_eq_refl, PartialEquiv.refl_prod_refl]⟩

/-!
## One dimension
-/

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

/-- Abbreviation for `𝓘(ℂ,ℂ) = modelWithCornersSelf ℂ ℂ` -/
public abbrev OneDimension.I := modelWithCornersSelf ℂ ℂ

/-- Abbreviation for `𝓘(ℂ,ℂ).prod 𝓘(ℂ,ℂ)` -/
public abbrev OneDimension.II := I.prod I

open OneDimension

/-- A critical point is where the derivative of `f` vanishes -/
@[expose] public def Critical (f : S → T) (z : S) :=
  mfderiv I I f z = 0

/-- A precritical point is an iterated preimage of a critical point -/
@[expose] public def Precritical (f : S → S) (z : S) :=
  ∃ n, Critical f (f^[n] z)

/-!
## Nontrivial analyticity
-/

/-- A nontrivial analytic function is one which is not locally constant -/
public structure NontrivialAnalyticOn (f : ℂ → ℂ) (s : Set ℂ) : Prop where
  analyticOn : AnalyticOnNhd ℂ f s
  nonconst : ∀ x, x ∈ s → ∃ᶠ y in 𝓝 x, f y ≠ f x

/-- A analytic function that is nonconstant near a point -/
public structure NontrivialMAnalyticAt (f : S → T) (z : S) : Prop where
  mAnalyticAt : ContMDiffAt I I ω f z
  nonconst : ∃ᶠ w in 𝓝 z, f w ≠ f z

/-- `f` is nontrivial analytic everyone in `s` -/
@[expose] public def NontrivialMAnalyticOn (f : S → T) (s : Set S) : Prop :=
  ∀ z, z ∈ s → NontrivialMAnalyticAt f z
