import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Mathlib.Analysis.Convex.Contractible

/-!
# Homology in a two-point complement is detected by the one-point complements

The two one-point complements form an actual open cover of the contractible
ambient vector space. Mayer--Vietoris and ambient positive-degree vanishing
make their intersection-inclusion maps jointly injective. This will identify
the endpoint-plus-meridian relation without a manifold-with-boundary theorem.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]

def twoPunctureSet (a b : X) : Set X := ({a}ᶜ : Set X) ∩ {b}ᶜ

def firstPunctureInclusion (a b : X) : C(twoPunctureSet a b, ({a}ᶜ : Set X)) :=
  ContinuousMap.inclusion inter_subset_left

def secondPunctureInclusion (a b : X) : C(twoPunctureSet a b, ({b}ᶜ : Set X)) :=
  ContinuousMap.inclusion inter_subset_right

theorem homology_ext_of_ambient_vanishing
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (n : ℕ)
    [Subsingleton (SingularHomology X (n + 1))]
    {a b : SingularHomology (U ∩ V : Set X) n}
    (hfirst : singularHomologyMap (ContinuousMap.inclusion
      (inter_subset_left : U ∩ V ⊆ U)) n a =
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) n b)
    (hsecond : singularHomologyMap (ContinuousMap.inclusion
      (inter_subset_right : U ∩ V ⊆ V)) n a =
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) n b) :
    a = b := by
  have hz : connectingHomomorphism U V hU hV hc n = 0 := by
    apply LinearMap.ext
    intro c
    have hc0 : c = 0 := Subsingleton.elim _ _
    rw [hc0, map_zero]
    rfl
  have hi : Injective (leftHomologyMap U V n) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_intersection U V hU hV hc n, hz, LinearMap.range_zero]
  apply hi
  rw [leftHomologyMap_apply, leftHomologyMap_apply, hfirst, hsecond]

theorem two_puncture_homology_ext [T1Space X] [ContractibleSpace X]
    {p q : X} (hpq : p ≠ q) (n : ℕ) {a b : SingularHomology (twoPunctureSet p q) n}
    (hfirst : singularHomologyMap (firstPunctureInclusion p q) n a =
      singularHomologyMap (firstPunctureInclusion p q) n b)
    (hsecond : singularHomologyMap (secondPunctureInclusion p q) n a =
      singularHomologyMap (secondPunctureInclusion p q) n b) : a = b := by
  have hc : ({p}ᶜ : Set X) ∪ {q}ᶜ = univ := by
    ext z
    simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases hz : z = p
    · exact Or.inr (fun hq => hpq (hz.symm.trans hq))
    · exact Or.inl hz
  let _ := contractible_homology_subsingleton X (n + 1) (Nat.succ_ne_zero n)
  exact homology_ext_of_ambient_vanishing _ _ isOpen_compl_singleton
    isOpen_compl_singleton hc n hfirst hsecond

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
