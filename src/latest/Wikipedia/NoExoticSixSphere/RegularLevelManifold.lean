import Wikipedia.NoExoticSixSphere.ManifoldLevelNormalForm
import Wikipedia.NoExoticSixSphere.RegularLevelInclusion

/-!
# The regular-level manifold construction

A smooth map with surjective differential along its zero fiber has a smooth
level-set atlas of the expected dimension. The atlas and its smooth inclusion
are constructed on the existing subtype topology, using the proved local
normal forms and their transitions.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {B H M F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem nonempty_regularLevelAtlas {f : M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hzero : {x | f x = 0} ⊆ U)
    (hreg : ∀ x, f x = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x))
    (k : ℕ) (hd : finrank ℝ B = finrank ℝ F + k) :
    Nonempty (RegularLevelAtlas (K := EuclideanSpace ℝ (Fin k)) I f) := by
  classical
  have hlocal (x : {x : M // f x = 0}) :=
    exists_manifoldLevelNormalForm hU (hzero x.property) hf (hreg x x.property) k hd
  choose Φ hΦx hΦU hΦfirst hΦzero using hlocal
  exact ⟨{
    normalForm := Φ
    mem_source := hΦx
    first_eq := hΦfirst
  }⟩

theorem exists_regularLevelManifold {f : M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hzero : {x | f x = 0} ⊆ U)
    (hreg : ∀ x, f x = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x))
    (k : ℕ) (hd : finrank ℝ B = finrank ℝ F + k) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : M // f x = 0},
      letI := c;
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ {x : M // f x = 0} ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) I ∞ ((↑) : {x : M // f x = 0} → M) := by
  obtain ⟨A⟩ := nonempty_regularLevelAtlas hU hf hzero hreg k hd
  exact ⟨A.chartedSpace, A.isManifold, A.contMDiff_subtype_val⟩

end NoExoticSixSphere
