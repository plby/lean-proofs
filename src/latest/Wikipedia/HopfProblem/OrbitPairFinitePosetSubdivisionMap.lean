import Wikipedia.HopfProblem.OrbitPairFiniteChainDistribution

/-!
# A continuous map between the actual successive face-poset realizations

The positive support of the interpolated chain distributions lies in the
largest face of each nerve simplex, hence is a chain in the original
poset. The exact coordinate-image theorem and the closed embedding supply
a continuous map into the actual preceding realization.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex AffineCoordinates

variable (P : Type u) [PartialOrder P] [Fintype P]

theorem weighted_chainDistribution_zero {k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains P) (hA : Monotone A) (t : Simplex k)
    (p : P) (hp : p ∉ (A (Fin.last k)).finset) :
    weighted (fun j ↦ chainDistribution P (A j)) t p = 0 := by
  have hz (j : Fin (k + 1)) : chainDistribution P (A j) p = 0 := by
    rw [chainDistribution_apply, if_neg]
    exact fun h ↦ hp ((hA (Fin.le_last j) : (A j).finset ⊆ (A (Fin.last k)).finset) h)
  change (∑ j, t j * chainDistribution P (A j) p) = 0
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem subdivisionCoordinates_support_isChain
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    IsChain (· ≤ ·) {p | 0 < subdivisionCoordinates P z p} := by
  obtain ⟨k, x, t, rfl⟩ := exists_characteristic (nerve (NonemptyFiniteChains P)) z
  have hsub : {p | 0 < subdivisionCoordinates P
      (characteristic (nerve (NonemptyFiniteChains P)) k x t) p} ⊆
      ((x.obj (Fin.last k)).finset : Set P) := by
    intro p hp
    by_contra hnot
    have hz := weighted_chainDistribution_zero P x.obj x.monotone t p hnot
    have he := congrArg (fun a : stdSimplex ℝ P ↦ a p)
      (subdivisionCoordinates_characteristic P k x t)
    exact (ne_of_gt hp) (he.trans hz)
  exact IsChain.mono hsub (chain_isChain (x.obj (Fin.last k)))

theorem subdivisionCoordinates_mem_range
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    subdivisionCoordinates P z ∈ Set.range (coordinates P) :=
  (mem_coordinates_range_iff P _).mpr (subdivisionCoordinates_support_isChain P z)

def subdivisionMap :
    C(SSet.toTop.obj (nerve (NonemptyFiniteChains P)), SSet.toTop.obj (nerve P)) := by
  let e := (coordinates_isClosedEmbedding P).isEmbedding.toHomeomorph
  exact ⟨fun z ↦ e.symm ⟨subdivisionCoordinates P z, subdivisionCoordinates_mem_range P z⟩,
    e.symm.continuous.comp ((subdivisionCoordinates P).continuous.subtype_mk _)⟩

theorem coordinates_subdivisionMap
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    coordinates P (subdivisionMap P z) = subdivisionCoordinates P z := by
  let e := (coordinates_isClosedEmbedding P).isEmbedding.toHomeomorph
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨subdivisionCoordinates P z, subdivisionCoordinates_mem_range P z⟩)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
