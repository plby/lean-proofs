import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondLoopMap
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# The second Bott map on native homotopy groups

The map is induced by the actual conjugated rotation family and ordinary
cubical uncurrying. Its representative formula is explicit. Bijectivity is
proved separately in `QuaternionicSecondBottHomotopy` using the relative
deformation within the complex-structure locus.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere

variable {n d : ℕ} {J₀ : ComplexStructures.Space n}

def inducedCube (J : Space J₀) (p : GenLoop (Fin d) (Space J₀) J) :
    GenLoop (Fin (d + 1)) (ComplexStructures.Space n) J₀ :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (loopMap J) (loopMap_reference J) p)

theorem inducedCube_apply (J : Space J₀) (p : GenLoop (Fin d) (Space J₀) J)
    (t : Fin (d + 1) → I) :
    inducedCube J p t =
      ComplexStructures.conjugate (conjugator J ((t 0 : ℝ) * Real.pi))⁻¹
        (rotation (p (Fin.tail t)) ((t 0 : ℝ) * Real.pi)) := rfl

def degreeShiftHom (d : ℕ) [NeZero d] (J : Space J₀) :
    π_ d (Space J₀) J →* π_ (d + 1) (ComplexStructures.Space n) J₀ :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d J₀).toMonoidHom.comp
    (HigherHomotopy.mapMonoidHom (loopMap J) (loopMap_reference J))

theorem degreeShiftHom_mk [NeZero d] (J : Space J₀)
    (p : GenLoop (Fin d) (Space J₀) J) :
    degreeShiftHom d J (Quotient.mk' p) = Quotient.mk' (inducedCube J p) := rfl

theorem pathMap_homotopicRel_iff_loopMap {X : Type*} [TopologicalSpace X]
    (J : Space J₀) (f g : C(X, Space J₀)) (S : Set X) :
    Nonempty (((pathMap J₀).comp f).HomotopyRel ((pathMap J₀).comp g) S) ↔
      Nonempty (((loopMap J).comp f).HomotopyRel ((loopMap J).comp g) S) :=
  homotopicRel_iff_postcompose_homeomorph (loopHomeomorph J)
    ((pathMap J₀).comp f) ((pathMap J₀).comp g) S

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
