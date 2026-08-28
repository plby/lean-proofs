import Wikipedia.NoExoticSixSphere.JamesSphereExcursions
import Wikipedia.NoExoticSixSphere.JamesCompactFactorization

/-!
# Hausdorff separation and finite-stage quotient topology for James spheres

The actual Moore-loop comparison is injective by unique excursion
factorization. It separates points in the James topology. Each finite
stage is therefore compact Hausdorff, its Cartesian-power presentation
is a quotient map, and its Moore-loop comparison is a closed embedding.

None of these assertions identifies the whole James space with the loop
space or proves the required EHP exactness theorem.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere

namespace JamesSphere

theorem mooreComparison_injective (n : ℕ) : Function.Injective (mooreComparison n) := by
  change Function.Injective (FreeMonoid.lift
    (fun x : {x : Sphere n // x ≠ spherePole n} ↦ mooreGenerator n x.val))
  apply Moore.Loop.freeMonoid_lift_injective_of_excursions
  · intro x y h
    exact Subtype.ext (mooreGenerator_injective n h)
  · intro x
    exact mooreGenerator_isExcursion n x.property

instance (n : ℕ) : T2Space (James.Space (Sphere n) (spherePole n)) :=
  T2Space.of_injective_continuous (mooreComparison_injective n) (mooreComparison n).continuous

instance (n k : ℕ) : CompactSpace (James.stage (spherePole n) k) :=
  isCompact_iff_compactSpace.mp (James.isCompact_stage (spherePole n) k)

theorem isClosed_stage (n k : ℕ) : IsClosed (James.stage (spherePole n) k) :=
  (James.isCompact_stage (spherePole n) k).isClosed

def stagePresentation (n k : ℕ) : C((Fin k → Sphere n), James.stage (spherePole n) k) :=
  ⟨fun v ↦ ⟨James.word (spherePole n) (List.ofFn v), by
      rw [← James.range_word_array]
      exact mem_range_self v⟩,
    (James.continuous_word_array (spherePole n) k).subtype_mk _⟩

theorem stagePresentation_surjective (n k : ℕ) : Function.Surjective (stagePresentation n k) := by
  intro w
  obtain ⟨v, hv⟩ := James.exists_array_of_mem_stage (spherePole n) w.property
  exact ⟨v, Subtype.ext hv⟩

theorem isQuotientMap_stagePresentation (n k : ℕ) : IsQuotientMap (stagePresentation n k) :=
  IsQuotientMap.of_surjective_continuous (stagePresentation_surjective n k)
    (stagePresentation n k).continuous

def stageMooreComparison (n k : ℕ) :
    C(James.stage (spherePole n) k, Moore.Loop (spherePole (n + 1))) :=
  ⟨fun w ↦ mooreComparison n w.val, (mooreComparison n).continuous.comp continuous_subtype_val⟩

theorem isClosedEmbedding_stageMooreComparison (n k : ℕ) :
    IsClosedEmbedding (stageMooreComparison n k) :=
  (stageMooreComparison n k).continuous.isClosedEmbedding
    (fun _ _ h ↦ Subtype.ext (mooreComparison_injective n h))

end JamesSphere

end NoExoticSixSphere
