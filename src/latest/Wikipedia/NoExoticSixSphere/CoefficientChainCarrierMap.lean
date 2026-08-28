import Wikipedia.NoExoticSixSphere.CoefficientChainCompactCarrier

/-!
# Compact carriers under actual continuous maps

Map the compact carrier and its representing chain along the specified
continuous map. In particular, a chain coming from a subspace already
comes from a compact subset of that same subspace.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The image chain has a compact carrier inside the actual image of the map. -/
theorem exists_compactCarrier_map (f : C(Y, X)) (n : ℕ) (c : Chains A Y n) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ range f ∧ ∃ d : Chains A K n,
      ((RelativeCoefficients.inclusion A K).f n).hom d =
        ((RelativeCoefficients.spaceMap A f).f n).hom c := by
  obtain ⟨T, hT, b, hb⟩ := exists_compactCarrier A Y n c
  let K : Set X := f '' T
  let g : C(T, K) := ⟨fun t => ⟨f t, ⟨t, t.property, rfl⟩⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have he : (subtypeInclusion K).comp g = f.comp (subtypeInclusion T) := by
    ext t
    rfl
  have hmap : RelativeCoefficients.spaceMap A g ≫ RelativeCoefficients.inclusion A K =
      RelativeCoefficients.inclusion A T ≫ RelativeCoefficients.spaceMap A f := by
    change RelativeCoefficients.spaceMap A g ≫
      RelativeCoefficients.spaceMap A (subtypeInclusion K) =
        RelativeCoefficients.spaceMap A (subtypeInclusion T) ≫
          RelativeCoefficients.spaceMap A f
    rw [← RelativeCoefficients.spaceMap_comp, ← RelativeCoefficients.spaceMap_comp, he]
  refine ⟨K, hT.image f.continuous, image_subset_range f T,
    ((RelativeCoefficients.spaceMap A g).f n).hom b, ?_⟩
  have hm := congrArg (fun q => (q.f n).hom b) hmap
  change ((RelativeCoefficients.inclusion A K).f n).hom
    (((RelativeCoefficients.spaceMap A g).f n).hom b) =
      ((RelativeCoefficients.spaceMap A f).f n).hom
        (((RelativeCoefficients.inclusion A T).f n).hom b) at hm
  exact hm.trans (congrArg ((RelativeCoefficients.spaceMap A f).f n).hom hb)

/-- A chain supported in `U` has a compact carrier contained in `U`. -/
theorem exists_compactCarrier_subspace (U : Set X) (n : ℕ) (c : Chains A U n) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∃ d : Chains A K n,
      ((RelativeCoefficients.inclusion A K).f n).hom d =
        ((RelativeCoefficients.inclusion A U).f n).hom c := by
  obtain ⟨K, hK, hKU, d, hd⟩ := exists_compactCarrier_map A (subtypeInclusion U) n c
  refine ⟨K, hK, ?_, d, hd⟩
  rintro x hx
  obtain ⟨y, rfl⟩ := hKU hx
  exact y.property

/-- Enlarging the actual subspace enlarges the image of its inclusion on chains. -/
theorem inclusion_range_mono {U V : Set X} (h : U ⊆ V) (n : ℕ) :
    LinearMap.range ((RelativeCoefficients.inclusion A U).f n).hom ≤
      LinearMap.range ((RelativeCoefficients.inclusion A V).f n).hom := by
  rintro c ⟨d, rfl⟩
  let f := RelativeSingularHomology.restrictedMap (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) U V from fun _ hx => h hx)
  have he := RelativeCoefficients.inclusion_pairMap A (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) U V from fun _ hx => h hx)
  rw [RelativeCoefficients.spaceMap_id, Category.comp_id] at he
  refine ⟨((RelativeCoefficients.spaceMap A f).f n).hom d, ?_⟩
  exact (congrArg (fun q => (q.f n).hom d) he).symm

end NoExoticSixSphere.CoefficientChains
