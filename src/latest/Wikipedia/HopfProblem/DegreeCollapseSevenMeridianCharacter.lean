import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionCharacter
import Wikipedia.HopfProblem.DegreeCollapseSevenSelectedTorsionSurgery

/-!
# The actual seven-dimensional exterior's meridian character

The original exterior inclusion is surjective and its kernel is exactly
the original meridian subgroup. Fourth-homology vanishing makes that
meridian infinite, and finite third homology constructs a normalized
rational coordinate and a character on the actual old half's homology.
Its value on the original attaching class is the negative surgery ratio
modulo the integers. A nonzero value constructs the nondivisible relation
needed by the already checked decreasing framed surgery. Symmetry and
nondegeneracy of a linking pairing are not assumed or asserted here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

theorem halfOldInclusion_addKernel (s : Sphere 3) :
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom.ker =
      AddSubgroup.zmultiples (halfMeridianClass A hA T s) := by
  change (LinearMap.ker (singularHomologyMap (halfOldInclusion A hA T) 3)).toAddSubgroup = _
  rw [halfOld_kernel_span, CyclicSurgeryIndex.span_toAddSubgroup]

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

def meridianRationalCoordinate (s : Sphere 3) :
    SingularHomology (HalfExterior A hA T) 3 →+ ℚ :=
  (CyclicExtensionCharacter.rationalCoordinate (halfMeridianClass A hA T s)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_addKernel A hA T s)
    (halfMeridian_coefficient_injective A hA T s)).toAddMonoidHom

def meridianCharacter (s : Sphere 3) :
    SingularHomology (OldPositiveHalf A T) 3 →+ RationalResidue.Value :=
  (CyclicExtensionCharacter.character (halfMeridianClass A hA T s)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_addKernel A hA T s)
    (halfMeridian_coefficient_injective A hA T s)
    (halfOldInclusion_surjective A hA T)).toAddMonoidHom

theorem meridianRationalCoordinate_meridian (s : Sphere 3) :
    meridianRationalCoordinate A hA T s (halfMeridianClass A hA T s) = 1 :=
  CyclicExtensionCharacter.rationalCoordinate_meridian _ _ _ _

theorem meridianCharacter_oldInclusion (s : Sphere 3)
    (c : SingularHomology (HalfExterior A hA T) 3) :
    meridianCharacter A hA T s (singularHomologyMap (halfOldInclusion A hA T) 3 c) =
      RationalResidue.residue (meridianRationalCoordinate A hA T s c) :=
  CyclicExtensionCharacter.character_quotient _ _ _ _ _ _

theorem meridianCharacter_attaching_of_relation (v s : Sphere 3) (l p : ℤ) (hl : l ≠ 0)
    (hrel : l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0) :
    meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) =
        RationalResidue.residue (-(p : ℚ) / (l : ℚ)) := by
  have hq : singularHomologyMap (halfOldInclusion A hA T) 3 (halfSectionClass A hA T v) =
      singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2) :=
    halfOldInclusion_section A hA T v (unitSphereTopClass 2)
  refine (congrArg (meridianCharacter A hA T s) hq).symm.trans ?_
  exact CyclicExtensionCharacter.character_of_relation _ _ _ _ _ _ l p hl hrel

theorem meridianCharacter_nonzero_iff_nondivisible_relation (v s : Sphere 3) :
    meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) ≠ 0 ↔
      ∃ l p : ℤ, 0 < l ∧ ¬ l ∣ p ∧
        l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0 := by
  have hq : singularHomologyMap (halfOldInclusion A hA T) 3 (halfSectionClass A hA T v) =
      singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2) :=
    halfOldInclusion_section A hA T v (unitSphereTopClass 2)
  rw [← hq]
  exact CyclicExtensionCharacter.character_ne_zero_iff_nondivisible_relation _ _ _ _ _ _

theorem exists_strict_shrunk_twist_of_meridianCharacter (v s : Sphere 3)
    (hfamily : ∀ j : ℤ, Nonempty (ShrunkEvenTwist A v j))
    (hn : meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) ≠ 0) :
    ∃ (j : ℤ) (Q : ShrunkEvenTwist A v j),
      Finite (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
        Nat.card (SingularHomology
          (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) <
            Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  obtain ⟨l, p, hl, hp, hrel⟩ :=
    (meridianCharacter_nonzero_iff_nondivisible_relation A hA T v s).mp hn
  exact SevenSurgery.exists_strict_shrunk_twist hA T hfamily s l p hl hp hrel

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
