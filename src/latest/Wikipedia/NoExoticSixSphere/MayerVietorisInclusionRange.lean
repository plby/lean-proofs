import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Low-degree homology of an original open-piece inclusion

The actual Mayer--Vietoris maps give injectivity when the intersection
homology vanishes, and surjectivity when the other piece and the preceding
intersection homology vanish. Exactness also lifts every class killed by
the ambient inclusion to the actual intersection, without any homology
vanishing hypothesis. No replacement of the inclusion map occurs.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.MayerVietorisInclusionRange

variable {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)

include hU hV hc

theorem exists_intersection_lift_of_inclusion_zero (n : ℕ)
    (a : SingularHomology U n) (ha : singularHomologyMap (subtypeInclusion U) n a = 0) :
    ∃ b : SingularHomology (U ∩ V : Set X) n,
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) n b = a ∧
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) n b = 0 := by
  have hker : (a, 0) ∈ LinearMap.ker (rightHomologyMap U V n) := by
    change rightHomologyMap U V n (a, 0) = 0
    simp only [rightHomologyMap_apply, ha, map_zero, add_zero]
  rw [← exact_at_pair U V hU hV hc n] at hker
  obtain ⟨b, hb⟩ := hker
  rw [leftHomologyMap_apply] at hb
  refine ⟨b, congrArg Prod.fst hb, ?_⟩
  have h := congrArg Prod.snd hb
  simpa only [Prod.snd, neg_eq_zero] using h

theorem injective (d : ℕ) [Subsingleton (SingularHomology (U ∩ V : Set X) d)] :
    Function.Injective (singularHomologyMap (subtypeInclusion U) d) := by
  have hl : leftHomologyMap U V d = 0 := by
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
    rfl
  have hi : Function.Injective (rightHomologyMap U V d) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_pair U V hU hV hc d, hl, LinearMap.range_zero]
  intro a b hab
  have he : rightHomologyMap U V d (a, 0) = rightHomologyMap U V d (b, 0) := by
    simpa only [rightHomologyMap_apply, map_zero, add_zero] using hab
  exact congrArg Prod.fst (hi he)

theorem surjective (d : ℕ) [Subsingleton (SingularHomology V (d + 1))]
    [Subsingleton (SingularHomology (U ∩ V : Set X) d)] :
    Function.Surjective (singularHomologyMap (subtypeInclusion U) (d + 1)) := by
  have hδ : connectingHomomorphism U V hU hV hc d = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  have hs : Function.Surjective (rightHomologyMap U V (d + 1)) := by
    apply LinearMap.range_eq_top.mp
    rw [exact_at_ambient U V hU hV hc d, hδ, LinearMap.ker_zero]
  intro c
  obtain ⟨⟨a, b⟩, hab⟩ := hs c
  have hb : b = 0 := Subsingleton.elim _ _
  refine ⟨a, ?_⟩
  simpa only [rightHomologyMap_apply, hb, map_zero, add_zero] using hab

end NoExoticSixSphere.MayerVietorisInclusionRange
