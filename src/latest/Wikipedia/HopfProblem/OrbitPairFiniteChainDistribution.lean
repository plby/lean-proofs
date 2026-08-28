import Wikipedia.HopfProblem.OrbitPairFinitePosetCoordinateImage

/-!
# Uniform distributions on finite-poset chains

The barycentre of a nonempty chain is its uniform probability vector.
Injective monotone vertex maps preserve this vector exactly. Interpolating
these distributions defines the geometric coordinate map of the next
native face-poset nerve.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial PartialOrder
open scoped Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz SimplexSupport Subdivision AffineCoordinates RealizationSimplex

variable (P : Type u) [PartialOrder P] [Fintype P]

def chainDistribution (A : NonemptyFiniteChains P) : stdSimplex ℝ P := by
  letI : Nonempty A.finset := A.nonempty.to_subtype
  exact stdSimplex.map (Subtype.val : A.finset → P) stdSimplex.barycenter

theorem chainDistribution_apply (A : NonemptyFiniteChains P) (p : P) :
    chainDistribution P A p = if p ∈ A.finset then (A.finset.card : ℝ)⁻¹ else 0 := by
  let : Nonempty A.finset := A.nonempty.to_subtype
  by_cases hp : p ∈ A.finset
  · rw [if_pos hp]
    have h := map_coordinate_injective (Subtype.val : A.finset → P) Subtype.val_injective
      (stdSimplex.barycenter : stdSimplex ℝ A.finset) ⟨p, hp⟩
    change chainDistribution P A p = (Fintype.card A.finset : ℝ)⁻¹ at h
    simpa only [Fintype.card_coe] using h
  · rw [if_neg hp]
    exact simplex_map_zero_of_not_mem_range (Subtype.val : A.finset → P) stdSimplex.barycenter p
      (by rintro ⟨a, rfl⟩; exact hp a.property)

theorem chainDistribution_map {Q : Type v} [PartialOrder Q] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f) (A : NonemptyFiniteChains P) :
    chainDistribution Q (A.map f) = stdSimplex.map f (chainDistribution P A) := by
  have hc := chainMap_card f hf A
  apply Subtype.ext
  funext q
  change chainDistribution Q (A.map f) q = stdSimplex.map f (chainDistribution P A) q
  by_cases hq : q ∈ Set.range f
  · obtain ⟨p, rfl⟩ := hq
    have hm : f p ∈ (A.map f).finset ↔ p ∈ A.finset := by
      rw [NonemptyFiniteChains.mem_map_iff]
      constructor
      · rintro ⟨a, ha, he⟩
        exact hf he ▸ ha
      · intro hp
        exact ⟨p, hp, rfl⟩
    rw [map_coordinate_injective f hf, chainDistribution_apply, chainDistribution_apply]
    simp only [hm, hc]
  · have hm : q ∉ (A.map f).finset := by
      intro hq'
      obtain ⟨p, hp, he⟩ := (NonemptyFiniteChains.mem_map_iff A f q).mp hq'
      exact hq ⟨p, he⟩
    rw [chainDistribution_apply, if_neg hm, simplex_map_zero_of_not_mem_range f _ q hq]

def subdivisionCoordinates :
    C(SSet.toTop.obj (nerve (NonemptyFiniteChains P)), stdSimplex ℝ P) :=
  nerveInterpolation (NonemptyFiniteChains P) (chainDistribution P)

theorem subdivisionCoordinates_characteristic (k : ℕ)
    (x : (nerve (NonemptyFiniteChains P)) _⦋k⦌) (t : Simplex k) :
    subdivisionCoordinates P (characteristic (nerve (NonemptyFiniteChains P)) k x t) =
      weighted (fun j ↦ chainDistribution P (x.obj j)) t :=
  nerveInterpolation_characteristic (NonemptyFiniteChains P) (chainDistribution P) k x t

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
