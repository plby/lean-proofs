module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import ErdosProblems.Erdos515.External.Ray.Manifold.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import ErdosProblems.Erdos515.External.Ray.Manifold.Manifold

/-!
## Facts about analytic manifolds

This file used to define `AnalyticManifold`, but now `IsManifold I ω M` handles that natively!
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped ContDiff Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

variable {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G C : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H D : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable {M : Type} {I : ModelWithCorners 𝕜 E A} [TopologicalSpace M]
variable {N : Type} {J : ModelWithCorners 𝕜 F B} [TopologicalSpace N]
variable {O : Type} {K : ModelWithCorners 𝕜 G C} [TopologicalSpace O]
variable {P : Type} {L : ModelWithCorners 𝕜 H D} [TopologicalSpace P]
variable [ChartedSpace A M] [ChartedSpace B N] [ChartedSpace C O] [ChartedSpace D P]

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff {f : M → N} {x : M} [CompleteSpace F] :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
      (extChartAt I x x) := by
  rw [contMDiffAt_iff, contDiffWithinAt_omega_iff_analyticWithinAt]

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
public theorem mAnalyticAt_iff_of_boundaryless [I.Boundaryless] [CompleteSpace F] {f : M → N}
    {x : M} :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simp only [mAnalyticAt_iff, I.range_eq_univ, analyticWithinAt_univ]

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
public theorem mAnalytic_iff {f : M → N} [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (range I) (extChartAt I x x) := by
  simp only [ContMDiff, contMDiffAt_iff, continuous_iff_continuousAt,
    contDiffWithinAt_omega_iff_analyticWithinAt]
  aesop

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
public theorem mAnalytic_iff_of_boundaryless [I.Boundaryless] [IsManifold I ω M] [IsManifold J ω N]
    [CompleteSpace F] {f : M → N} :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
  simp only [mAnalytic_iff, I.range_eq_univ, analyticWithinAt_univ]

section Iff

variable (I J)

/-- Analytic functions are analytic, and vice versa -/
public theorem analyticAt_iff_mAnalyticAt [I.Boundaryless] [ChartedSpace A E] [IsManifold I ω E]
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl I] [ExtChartEqRefl J] [CompleteSpace F]
    {f : E → F} {x : E} : AnalyticAt 𝕜 f x ↔ ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff_of_boundaryless, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq, iff_and_self]
  exact AnalyticAt.continuousAt

end Iff

/-- Analytic functions are analytic -/
public theorem AnalyticAt.mAnalyticAt {f : E → F} {x : E} (fa : AnalyticAt 𝕜 f x) [CompleteSpace F]
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] :
    ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff, fa.continuousAt, true_and, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq]
  exact fa.analyticWithinAt

/-- ContMDiff functions are analytic -/
public theorem ContMDiffAt.analyticAt [CompleteSpace F] (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I] (J : ModelWithCorners 𝕜 F B)
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] {f : E → F} {x : E} :
    ContMDiffAt I J ω f x → AnalyticAt 𝕜 f x :=
  (analyticAt_iff_mAnalyticAt _ _).mpr

/-- Complex powers `f x ^ g x` are analytic if `f x` avoids the negative real axis  -/
public theorem ContMDiffAt.cpow [NormedSpace ℂ E] [CompleteSpace E] {I : ModelWithCorners ℂ E A}
    [IsManifold I ω M] {f g : M → ℂ} {x : M} (fa : ContMDiffAt I (𝓘(ℂ, ℂ)) ω f x)
    (ga : ContMDiffAt I (𝓘(ℂ, ℂ)) ω g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0) :
    ContMDiffAt I (𝓘(ℂ, ℂ)) ω (fun x ↦ f x ^ g x) x := by
  have e : (fun x ↦ f x ^ g x) = (fun p : ℂ × ℂ ↦ p.1 ^ p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  refine ((analyticAt_fst.cpow analyticAt_snd ?_).mAnalyticAt _ _).comp _ (fa.prodMk ga)
  exact a

/-- If we're analytic at a point, we're locally analytic.
This is true even with boundary, but for now we prove only the `Boundaryless` case. -/
public theorem ContMDiffAt.eventually [I.Boundaryless] [J.Boundaryless] [CompleteSpace E]
    [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] {f : M → N} {x : M}
    (fa : ContMDiffAt I J ω f x) : ∀ᶠ y in 𝓝 x, ContMDiffAt I J ω f y := by
  have ea := (mAnalyticAt_iff_of_boundaryless.mp fa).2.eventually_analyticAt
  simp only [← map_extChartAt_nhds_of_boundaryless, Filter.eventually_map] at ea
  filter_upwards [ea, (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f x)).mem_nhds
    (mem_extChartAt_source (I := J) (f x)))).eventually_nhds,
    (isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := I) x)]
  intro y a fm m
  have h := a.mAnalyticAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F)
  clear a
  have h' := ((contMDiffOn_extChartAt_symm _).contMDiffAt
    (extChartAt_target_mem_nhds' (PartialEquiv.map_source _ fm.self_of_nhds))).comp_of_eq
      (h.comp _ (contMDiffAt_extChartAt' (extChartAt_source I x ▸ m))) ?_
  · apply h'.congr_of_eventuallyEq
    clear h h'
    apply ((isOpen_extChartAt_source x).eventually_mem m).mp
    refine fm.mp (.of_forall fun z mf m ↦ ?_)
    simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ mf, Function.comp_def]
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- The domain of analyticity is open -/
public theorem isOpen_mAnalyticAt [I.Boundaryless] [J.Boundaryless] [CompleteSpace E]
    [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] {f : M → N} :
    IsOpen {x | ContMDiffAt I J ω f x} := by
  rw [isOpen_iff_eventually]; intro x fa; exact fa.eventually

/-- `ContMDiffOnNhd` restricts to subsets -/
public lemma ContMDiffOnNhd.mono {f : M → N} {s t : Set M} (fa : ContMDiffOnNhd I J f s) (st : t ⊆ s) :
    ContMDiffOnNhd I J f t := fun x m ↦ fa x (st m)

/-- `ContMDiffOnNhd` extends `ContMDiffOn` -/
public lemma ContMDiffOnNhd.contMDiffOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContMDiffOn I J ω f s := fun x m ↦ (fa x m).contMDiffWithinAt

/-- `ContMDiffOnNhd` implies analyticity -/
public lemma ContMDiffOnNhd.contMDiffAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s)
    {x : M} (xs : x ∈ s) : ContMDiffAt I J ω f x := fa x xs

/-- `ContMDiffOnNhd` implies continuity -/
public lemma ContMDiffOnNhd.continuousAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s)
    {x : M} (xs : x ∈ s) : ContinuousAt f x := (fa x xs).continuousAt

/-- `ContMDiffOnNhd` implies continuity on the domain -/
public lemma ContMDiffOnNhd.continuousOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContinuousOn f s := fun x m ↦ (fa x m).continuousAt.continuousWithinAt
