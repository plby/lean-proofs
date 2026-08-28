import Wikipedia.HopfProblem.OrbitPairSubdivisionBarycentreNaturality

/-!
# Restricting geometric simplex weights to an injective support

If all weights outside an injective vertex image vanish, restricting the
weights gives an actual geometric simplex point. Pushing it forward
recovers the original point exactly.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.SimplexSupport

variable {A B : Type*} [Fintype A] [Fintype B]

def restrictWeights (f : A → B) (hf : Function.Injective f) (t : stdSimplex ℝ B)
    (hzero : ∀ b, b ∉ Set.range f → t b = 0) : stdSimplex ℝ A := by
  classical
  refine ⟨fun a ↦ t (f a), fun a ↦ stdSimplex.zero_le t (f a), ?_⟩
  calc
    ∑ a, t (f a) = ∑ b ∈ Finset.univ.image f, t b :=
      (Finset.sum_image (fun a _ a' _ h ↦ hf h)).symm
    _ = ∑ b, t b := Finset.sum_subset (Finset.subset_univ _) (fun b hb hnot ↦
      hzero b (by
        rintro ⟨a, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)))
    _ = 1 := stdSimplex.sum_eq_one t

theorem restrictWeights_apply (f : A → B) (hf : Function.Injective f) (t : stdSimplex ℝ B)
    (hzero : ∀ b, b ∉ Set.range f → t b = 0) (a : A) :
    restrictWeights f hf t hzero a = t (f a) := rfl

theorem map_restrictWeights (f : A → B) (hf : Function.Injective f) (t : stdSimplex ℝ B)
    (hzero : ∀ b, b ∉ Set.range f → t b = 0) :
    stdSimplex.map f (restrictWeights f hf t hzero) = t := by
  apply Subtype.ext
  funext b
  change stdSimplex.map f (restrictWeights f hf t hzero) b = t b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [map_coordinate_injective f hf]
    rfl
  · rw [Subdivision.simplex_map_zero_of_not_mem_range f _ b hb, hzero b hb]

end Wikipedia.HopfProblem.OrbitPair.SimplexSupport
