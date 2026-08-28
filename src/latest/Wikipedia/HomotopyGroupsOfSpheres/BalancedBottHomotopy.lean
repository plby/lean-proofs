import Wikipedia.HomotopyGroupsOfSpheres.BalancedBottCubeComparison

/-!
# Bijectivity of the actual balanced Bott homomorphism

Relative representatives and homotopy reflection prove that the original
balanced rotation map, followed by reference congruence and cubical
uncurrying, induces a group isomorphism in the stated dimension range.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere

def homotopyMap (n d : ℕ) :
    HomotopyGroup (Fin d) (Space n) (standard n) →
      HomotopyGroup (Fin d) (Path (specialIdentity : SpecialSpace (Index n)) specialIdentity)
        (Path.refl specialIdentity) :=
  HigherHomotopy.map (loopMap n) (loopMap_reference n)

theorem homotopyMap_surjective (n d : ℕ) (hd : d < n) :
    Function.Surjective (homotopyMap n d) :=
  HigherHomotopy.map_surjective _ _ (loopMap_injective n)
    (exists_cube_loopMap_representative d n hd)

theorem homotopyMap_injective (n d : ℕ) (hd : d + 1 < n) :
    Function.Injective (homotopyMap n d) :=
  HigherHomotopy.map_injective _ _ (fun f g S h ↦
    (cube_loopMap_homotopicRel_iff d n hd f g S).mpr h)

theorem degreeShiftHom_surjective (n d : ℕ) [NeZero d] (hd : d < n) :
    Function.Surjective (degreeShiftHom n d) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d
    (specialIdentity : SpecialSpace (Index n))).surjective.comp
      (homotopyMap_surjective n d hd)

theorem degreeShiftHom_injective (n d : ℕ) [NeZero d] (hd : d + 1 < n) :
    Function.Injective (degreeShiftHom n d) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d
    (specialIdentity : SpecialSpace (Index n))).injective.comp
      (homotopyMap_injective n d hd)

/-- The balanced Bott isomorphism is the original, explicitly defined homomorphism. -/
def bottDegreeShiftMulEquiv (n d : ℕ) [NeZero d] (hd : d + 1 < n) :
    HomotopyGroup (Fin d) (Space n) (standard n) ≃*
      HomotopyGroup (Fin (d + 1)) (SpecialSpace (Index n)) specialIdentity :=
  MulEquiv.ofBijective (degreeShiftHom n d)
    ⟨degreeShiftHom_injective n d hd, degreeShiftHom_surjective n d (by omega)⟩

theorem bottDegreeShiftMulEquiv_apply (n d : ℕ) [NeZero d] (hd : d + 1 < n)
    (x : HomotopyGroup (Fin d) (Space n) (standard n)) :
    bottDegreeShiftMulEquiv n d hd x = degreeShiftHom n d x := rfl

theorem bottDegreeShiftMulEquiv_mk (n d : ℕ) [NeZero d] (hd : d + 1 < n)
    (p : GenLoop (Fin d) (Space n) (standard n)) :
    bottDegreeShiftMulEquiv n d hd (Quotient.mk' p) = Quotient.mk' (inducedCube n p) :=
  degreeShiftHom_mk n d p

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
