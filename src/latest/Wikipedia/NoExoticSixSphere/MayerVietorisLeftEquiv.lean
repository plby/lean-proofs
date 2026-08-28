import Wikipedia.NoExoticSixSphere.MayerVietorisVanishingEquiv

/-!
# The actual intersection-inclusion isomorphism for an acyclic ambient space

Vanishing of the two adjacent ambient homology groups makes the signed
Mayer--Vietoris inclusion bijective. If the second open set also has zero
homology, the literal inclusion into the first open set is an isomorphism.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.MayerVietorisVanishing

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (n : ℕ)
  [Subsingleton (SingularHomology X n)] [Subsingleton (SingularHomology X (n + 1))]

include hU hV hc

theorem left_bijective : Bijective (leftHomologyMap U V n) := by
  have hd : connectingHomomorphism U V hU hV hc n = 0 := by
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
    rfl
  have hr : rightHomologyMap U V n = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_intersection U V hU hV hc n, hd, LinearMap.range_zero]
  · apply LinearMap.range_eq_top.mp
    rw [exact_at_pair U V hU hV hc n, hr, LinearMap.ker_zero]

variable [Subsingleton (SingularHomology V n)]

theorem leftInclusion_bijective :
    Bijective (singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) n) := by
  have h := left_bijective U V hU hV hc n
  constructor
  · intro a b hab
    apply h.injective
    rw [leftHomologyMap_apply, leftHomologyMap_apply]
    exact Prod.ext hab (Subsingleton.elim _ _)
  · intro b
    obtain ⟨a, ha⟩ := h.surjective (b, 0)
    rw [leftHomologyMap_apply] at ha
    exact ⟨a, congrArg Prod.fst ha⟩

def leftInclusionEquiv : SingularHomology (U ∩ V : Set X) n ≃ₗ[ℤ] SingularHomology U n :=
  LinearEquiv.ofBijective
    (singularHomologyMap (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) n)
    (leftInclusion_bijective U V hU hV hc n)

theorem leftInclusionEquiv_apply (a : SingularHomology (U ∩ V : Set X) n) :
    leftInclusionEquiv U V hU hV hc n a =
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) n a := rfl

end NoExoticSixSphere.MayerVietorisVanishing
