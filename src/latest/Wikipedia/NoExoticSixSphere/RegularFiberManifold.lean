import Wikipedia.NoExoticSixSphere.RegularChartFiberManifold

/-!
# Regular fibers of maps between boundaryless manifolds

Use the existing smooth chart at the target value and restrict the source to
its valid preimage. Regularity constructs the level atlas; no target chart,
fiber atlas, or smooth inclusion is assumed as additional data.
-/

open scoped Manifold ContDiff
open Module

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (f : ContinuousMap M N) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)

noncomputable def regularFiberLevelAtlas :
    RegularLevelAtlas (K := EuclideanSpace ℝ (Fin k)) I
      (ChartFiber.coordinates f (modelChartPartialDiffeomorph (I := J) b) b) :=
  Classical.choice (ChartFiber.nonempty_levelAtlas f
    (modelChartPartialDiffeomorph (I := J) b) hf b (mem_extChartAt_source b) hreg k hd)

@[instance_reducible]
noncomputable def regularFiberAtlas :
    ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : M // f x = b} :=
  ChartFiber.atlas f (modelChartPartialDiffeomorph (I := J) b) b (mem_extChartAt_source b)
    (regularFiberLevelAtlas f hf b hreg k hd)

theorem regularFiber_isManifold : letI := regularFiberAtlas f hf b hreg k hd;
    IsManifold (𝓡 k) ∞ {x : M // f x = b} :=
  ChartFiber.isManifold f (modelChartPartialDiffeomorph (I := J) b) b (mem_extChartAt_source b)
    (regularFiberLevelAtlas f hf b hreg k hd)

theorem regularFiber_contMDiff_subtype_val : letI := regularFiberAtlas f hf b hreg k hd;
    ContMDiff (𝓡 k) I ∞ (Subtype.val : {x : M // f x = b} → M) :=
  ChartFiber.contMDiff_subtype_val f (modelChartPartialDiffeomorph (I := J) b) b
    (mem_extChartAt_source b) (regularFiberLevelAtlas f hf b hreg k hd)

variable {B' H'' P : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H''] {L : ModelWithCorners ℝ B' H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem regularFiber_contMDiffAt_iff_ambient (g : P → {x : M // f x = b}) (x : P) :
    letI := regularFiberAtlas f hf b hreg k hd;
    ContMDiffAt L (𝓡 k) ∞ g x ↔ ContMDiffAt L I ∞ (fun y ↦ (g y).val) x :=
  ChartFiber.contMDiffAt_iff_ambient f (modelChartPartialDiffeomorph (I := J) b) b
    (mem_extChartAt_source b) (regularFiberLevelAtlas f hf b hreg k hd) g x

theorem regularFiber_contMDiff_iff_ambient (g : P → {x : M // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k hd;
    ContMDiff L (𝓡 k) ∞ g ↔ ContMDiff L I ∞ (fun y ↦ (g y).val) :=
  ChartFiber.contMDiff_iff_ambient f (modelChartPartialDiffeomorph (I := J) b) b
    (mem_extChartAt_source b) (regularFiberLevelAtlas f hf b hreg k hd) g

theorem regularFiber_injective_mfderiv_subtype_val (x : {x : M // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k hd;
    Function.Injective (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x) :=
  ChartFiber.injective_mfderiv_subtype_val f (modelChartPartialDiffeomorph (I := J) b) b
    (mem_extChartAt_source b) (regularFiberLevelAtlas f hf b hreg k hd) x

include hf hreg hd in
theorem exists_regularFiberManifold :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : M // f x = b},
      letI := atlas;
      IsManifold (𝓡 k) ∞ {x : M // f x = b} ∧
      ContMDiff (𝓡 k) I ∞ (Subtype.val : {x : M // f x = b} → M) :=
  ⟨regularFiberAtlas f hf b hreg k hd, regularFiber_isManifold f hf b hreg k hd,
    regularFiber_contMDiff_subtype_val f hf b hreg k hd⟩

end NoExoticSixSphere
