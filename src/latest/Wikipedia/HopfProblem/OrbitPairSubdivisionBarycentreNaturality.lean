import Wikipedia.HopfProblem.OrbitPairSubdivisionHomeomorphism

/-!
# Barycentres commute with injective simplex maps

An injective simplex map preserves the cardinality of each face, and hence
its uniform barycentric weights. This is the compatibility needed for
gluing along faces; no analogous assertion is made for degeneracies.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz AffineCoordinates

theorem simplex_map_zero_of_not_mem_range {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (t : stdSimplex ℝ A) (b : B) (hb : b ∉ Set.range f) :
    stdSimplex.map f t b = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hpos
    obtain ⟨a, ha, _⟩ := (SimplexSupport.map_pos_iff f t b).mp hpos
    exact hb ⟨a, ha⟩
  · exact stdSimplex.zero_le _ _

theorem chainMap_card {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]
    (f : X →o Y) (hf : Function.Injective f) (A : NonemptyFiniteChains X) :
    (A.map f).finset.card = A.finset.card := by
  classical
  exact Finset.card_image_of_injective A.finset hf

theorem chainBarycentre_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f]
    (A : NonemptyFiniteChains (ULift.{u} (Fin (m + 1)))) :
    chainBarycentre n (A.map (SimplexCategory.toPartOrd.{u}.map f).hom) =
      stdSimplex.map f.toOrderHom (chainBarycentre m A) := by
  classical
  have hf : Function.Injective f.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f)
  let F : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)) :=
    (SimplexCategory.toPartOrd.{u}.map f).hom
  have hF : Function.Injective F := by
    intro a b hab
    apply ULift.ext a b
    exact hf (congrArg ULift.down hab)
  have hc := chainMap_card F hF A
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ Set.range f.toOrderHom
  · obtain ⟨i, rfl⟩ := hj
    have hm : ULift.up (f.toOrderHom i) ∈ (A.map F).finset ↔ ULift.up i ∈ A.finset := by
      rw [NonemptyFiniteChains.mem_map_iff]
      constructor
      · rintro ⟨a, ha, he⟩
        have he' : a = ULift.up i := hF he
        exact he' ▸ ha
      · intro hi
        exact ⟨ULift.up i, hi, rfl⟩
    change chainBarycentre n (A.map F) (f.toOrderHom i) =
      stdSimplex.map f.toOrderHom (chainBarycentre m A) (f.toOrderHom i)
    rw [SimplexSupport.map_coordinate_injective f.toOrderHom hf,
      chainBarycentre_apply, chainBarycentre_apply]
    simp only [hm, hc]
  · have hm : ULift.up j ∉ (A.map F).finset := by
      intro hm
      obtain ⟨a, ha, he⟩ := (NonemptyFiniteChains.mem_map_iff A F (ULift.up j)).mp hm
      exact hj ⟨a.down, congrArg ULift.down he⟩
    change chainBarycentre n (A.map F) j =
      stdSimplex.map f.toOrderHom (chainBarycentre m A) j
    rw [chainBarycentre_apply, if_neg hm, simplex_map_zero_of_not_mem_range _ _ j hj]

theorem simplex_map_weighted {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (f : B → D) (a : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) :
    stdSimplex.map f (weighted a t) = weighted (fun i ↦ stdSimplex.map f (a i)) t := by
  classical
  apply Subtype.ext
  funext d
  change FunOnFinite.linearMap ℝ ℝ f (weighted a t) d =
    ∑ i, t i * FunOnFinite.linearMap ℝ ℝ f (a i) d
  simp only [FunOnFinite.linearMap_apply_apply, weighted_apply, Finset.mul_sum]
  exact Finset.sum_comm

end Wikipedia.HopfProblem.OrbitPair.Subdivision
