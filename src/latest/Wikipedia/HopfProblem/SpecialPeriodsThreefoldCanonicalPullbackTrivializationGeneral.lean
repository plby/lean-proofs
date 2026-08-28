import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Complex.Basic

/-!
# Local biholomorphisms from arbitrary complex line-bundle trivializations

Every trivialization in the actual atlas of a holomorphic complex line bundle
is a local biholomorphism onto its natural product target.  The construction
retains the bundle's original topology, total-space atlas, open source, and
inverse function.  The base model is arbitrary, so the result applies both
to the native cusp model and to the global period-family product model.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  [TopologicalSpace B] [ChartedSpace H B] {V : B → Type*}
  [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The given atlas trivialization as an actual partial biholomorphism,
with its original forward map, inverse, and open source and target. -/
def trivializationPartialDiffeomorph
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] :
    PartialDiffeomorph (I.prod I₁) (I.prod I₁) (TotalSpace ℂ V) (B × ℂ) ω where
  __ := e.toOpenPartialHomeomorph
  contMDiffOn_toFun := e.contMDiffOn
  contMDiffOn_invFun := e.contMDiffOn_symm

@[simp] theorem trivializationPartialDiffeomorph_source
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] :
    (trivializationPartialDiffeomorph (I := I) e).source = e.source := rfl

@[simp] theorem trivializationPartialDiffeomorph_target
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] :
    (trivializationPartialDiffeomorph (I := I) e).target = e.target := rfl

@[simp] theorem trivializationPartialDiffeomorph_apply
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] (p : TotalSpace ℂ V) :
    trivializationPartialDiffeomorph (I := I) e p = e p := rfl

@[simp] theorem trivializationPartialDiffeomorph_symm_apply
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] (p : B × ℂ) :
    (trivializationPartialDiffeomorph (I := I) e).symm p =
      e.toOpenPartialHomeomorph.symm p := rfl

/-- Atlas trivializations are local biholomorphisms throughout their
original total-space source. -/
theorem trivialization_isLocalDiffeomorphAt
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] {p : TotalSpace ℂ V} (hp : p ∈ e.source) :
    IsLocalDiffeomorphAt (I.prod I₁) (I.prod I₁) ω e p :=
  (trivializationPartialDiffeomorph (I := I) e).isLocalDiffeomorphAt _ _ _ hp

/-- Inverse atlas trivializations are local biholomorphisms throughout
their original product target. -/
theorem trivialization_symm_isLocalDiffeomorphAt
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] {p : B × ℂ} (hp : p ∈ e.target) :
    IsLocalDiffeomorphAt (I.prod I₁) (I.prod I₁) ω
      e.toOpenPartialHomeomorph.symm p :=
  (trivializationPartialDiffeomorph (I := I) e).symm.isLocalDiffeomorphAt _ _ _ hp

/-- The forward local-biholomorphism criterion in terms of the base point. -/
theorem trivialization_isLocalDiffeomorphAt_of_mem_baseSet
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] {p : TotalSpace ℂ V} (hp : p.proj ∈ e.baseSet) :
    IsLocalDiffeomorphAt (I.prod I₁) (I.prod I₁) ω e p :=
  trivialization_isLocalDiffeomorphAt (I := I) e (e.mem_source.mpr hp)

/-- The inverse local-biholomorphism criterion in terms of the base point. -/
theorem trivialization_symm_isLocalDiffeomorphAt_of_mem_baseSet
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → B))
    [MemTrivializationAtlas e] {p : B × ℂ} (hp : p.1 ∈ e.baseSet) :
    IsLocalDiffeomorphAt (I.prod I₁) (I.prod I₁) ω
      e.toOpenPartialHomeomorph.symm p :=
  trivialization_symm_isLocalDiffeomorphAt (I := I) e (e.mem_target.mpr hp)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
