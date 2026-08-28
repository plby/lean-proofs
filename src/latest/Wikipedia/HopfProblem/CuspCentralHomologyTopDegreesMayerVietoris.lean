import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Degreewise vanishing in the actual singular Mayer–Vietoris sequence

For an actual open cover by `U` and `V`, vanishing of their homology in
degree `n + 1` makes the actual connecting homomorphism injective. If their
homology also vanishes in degree `n`, that same homomorphism is an
isomorphism. Vanishing of the intersection homology in degree `n` then
implies vanishing of the ambient homology in degree `n + 1`.

These statements use the proved exact singular sequence, not a supplied
connecting-map formula, an assumed exact sequence, or an assumed splitting.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ)

/-- Vanishing in the upper degree makes the actual Mayer–Vietoris
connecting homomorphism injective. -/
theorem coverConnecting_injective_of_vanishing (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))] :
    Function.Injective (connectingHomomorphism U V hU hV hcover n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

/-- Vanishing in the lower degree makes the actual Mayer–Vietoris
connecting homomorphism surjective. -/
theorem coverConnecting_surjective_of_vanishing (n : ℕ)
    [Subsingleton (SingularHomology U n)]
    [Subsingleton (SingularHomology V n)] :
    Function.Surjective (connectingHomomorphism U V hU hV hcover n) := by
  intro a
  have ha : a ∈ LinearMap.ker (leftHomologyMap U V n) := by
    exact Subsingleton.elim _ _
  rw [← exact_at_intersection U V hU hV hcover n] at ha
  exact ha

/-- With vanishing on both sides, the actual connecting homomorphism
identifies ambient homology with the preceding intersection homology. -/
def coverConnectingEquivOfVanishing (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    [Subsingleton (SingularHomology U n)]
    [Subsingleton (SingularHomology V n)] :
    SingularHomology X (n + 1) ≃ₗ[ℤ]
      SingularHomology (U ∩ V : Set X) n :=
  LinearEquiv.ofBijective (connectingHomomorphism U V hU hV hcover n)
    ⟨coverConnecting_injective_of_vanishing U V hU hV hcover n,
      coverConnecting_surjective_of_vanishing U V hU hV hcover n⟩

@[simp] theorem coverConnectingEquivOfVanishing_apply (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    [Subsingleton (SingularHomology U n)]
    [Subsingleton (SingularHomology V n)]
    (a : SingularHomology X (n + 1)) :
    coverConnectingEquivOfVanishing U V hU hV hcover n a =
      connectingHomomorphism U V hU hV hcover n a := rfl

@[simp] theorem coverConnectingEquivOfVanishing_toLinearMap (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    [Subsingleton (SingularHomology U n)]
    [Subsingleton (SingularHomology V n)] :
    (coverConnectingEquivOfVanishing U V hU hV hcover n).toLinearMap =
      connectingHomomorphism U V hU hV hcover n := rfl

include hU hV hcover in
/-- If the upper-degree homology of the two open sets and the
lower-degree homology of their intersection vanish, the ambient homology
vanishes in the upper degree. No lower-degree vanishing of `U` or `V` is needed. -/
theorem coverHomology_subsingleton_of_vanishing (n : ℕ)
    [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    [Subsingleton (SingularHomology (U ∩ V : Set X) n)] :
    Subsingleton (SingularHomology X (n + 1)) :=
  (coverConnecting_injective_of_vanishing U V hU hV hcover n).subsingleton

end Wikipedia.HopfProblem.CuspCentralHomology
