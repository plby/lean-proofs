import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual connecting isomorphism when the adjacent homology groups vanish

Exactness of the genuine open-cover Mayer–Vietoris sequence supplies both
injectivity and surjectivity. Contractibility of the whole cover pieces is
not required; only the four adjacent actual homology groups must vanish.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.MayerVietorisVanishing

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (n : ℕ)
  [Subsingleton (SingularHomology U n)] [Subsingleton (SingularHomology V n)]
  [Subsingleton (SingularHomology U (n + 1))] [Subsingleton (SingularHomology V (n + 1))]

theorem connecting_bijective : Bijective (connectingHomomorphism U V hU hV hc n) := by
  have hl : leftHomologyMap U V n = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  have hr : rightHomologyMap U V (n + 1) = 0 := by
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
    rfl
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_ambient U V hU hV hc n, hr, LinearMap.range_zero]
  · apply LinearMap.range_eq_top.mp
    rw [exact_at_intersection U V hU hV hc n, hl, LinearMap.ker_zero]

def connectingEquiv : SingularHomology X (n + 1) ≃ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  LinearEquiv.ofBijective (connectingHomomorphism U V hU hV hc n)
    (connecting_bijective U V hU hV hc n)

theorem connectingEquiv_apply (a : SingularHomology X (n + 1)) :
    connectingEquiv U V hU hV hc n a = connectingHomomorphism U V hU hV hc n a := rfl

end NoExoticSixSphere.MayerVietorisVanishing
