import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondBottCubeComparison

/-!
# Bijectivity of the actual second Bott homomorphism

The map is the original conjugated rotation family followed by cubical
uncurrying. Relative representatives give surjectivity, and relative homotopy
reflection gives injectivity in the stated dimension range.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere

variable {n : ℕ} {a : ComplexStructures.Space n}

def homotopyMap (d : ℕ) (J : Space a) :
    HomotopyGroup (Fin d) (Space a) J → HomotopyGroup (Fin d) (Path a a) (Path.refl a) :=
  HigherHomotopy.map (loopMap J) (loopMap_reference J)

theorem homotopyMap_surjective (d : ℕ) (J : Space a) (hd : d < n) :
    Function.Surjective (homotopyMap d J) :=
  HigherHomotopy.map_surjective _ _ (loopMap_injective J)
    (exists_cube_loopMap_representative d J hd)

theorem homotopyMap_injective (d : ℕ) (J : Space a) (hd : d + 1 < n) :
    Function.Injective (homotopyMap d J) :=
  HigherHomotopy.map_injective _ _ (fun f g S h ↦
    (cube_loopMap_homotopicRel_iff d J hd f g S).mpr h)

theorem degreeShiftHom_surjective (d : ℕ) [NeZero d] (J : Space a) (hd : d < n) :
    Function.Surjective (degreeShiftHom d J) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d a).surjective.comp
    (homotopyMap_surjective d J hd)

theorem degreeShiftHom_injective (d : ℕ) [NeZero d] (J : Space a) (hd : d + 1 < n) :
    Function.Injective (degreeShiftHom d J) :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d a).injective.comp
    (homotopyMap_injective d J hd)

/-- The second Bott isomorphism, induced by the original rotation-loop map. -/
def bottDegreeShiftMulEquiv (d : ℕ) [NeZero d] (J : Space a) (hd : d + 1 < n) :
    HomotopyGroup (Fin d) (Space a) J ≃*
      HomotopyGroup (Fin (d + 1)) (ComplexStructures.Space n) a :=
  MulEquiv.ofBijective (degreeShiftHom d J)
    ⟨degreeShiftHom_injective d J hd, degreeShiftHom_surjective d J (by omega)⟩

theorem bottDegreeShiftMulEquiv_apply (d : ℕ) [NeZero d] (J : Space a) (hd : d + 1 < n)
    (x : HomotopyGroup (Fin d) (Space a) J) :
    bottDegreeShiftMulEquiv d J hd x = degreeShiftHom d J x := rfl

theorem bottDegreeShiftMulEquiv_mk (d : ℕ) [NeZero d] (J : Space a) (hd : d + 1 < n)
    (p : GenLoop (Fin d) (Space a) J) :
    bottDegreeShiftMulEquiv d J hd (Quotient.mk' p) = Quotient.mk' (inducedCube J p) :=
  degreeShiftHom_mk J p

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
