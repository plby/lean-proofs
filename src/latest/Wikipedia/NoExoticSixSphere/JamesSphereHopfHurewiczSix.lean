import Wikipedia.NoExoticSixSphere.JamesSphereAboveFirstStageHomology
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientHurewiczSix
import Wikipedia.NoExoticSixSphere.SixthHurewiczNativeNaturality
import Wikipedia.NoExoticSixSphere.SphereFiveEighthPresentation

/-!
# The actual S4 Hopf coordinate is the homology class of its James adjoint

The actual quotient map J(S3) -> J(S3)/S3 is a sixth-homology isomorphism.
Transport the quotient's proved integral marking through this map.
Native sixth Hurewicz naturality and the original Hopf factorization
identify this homology coordinate with the original seventh-sphere Hopf
coordinate. In particular, this reduces the attaching relation's integer
coordinate to a specified genuine six-cube homology class. Its numerical
value is not evaluated here.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SphereFourHopfHomology

open JamesSphere

def wordAdjoint (c : π_ 7 (Sphere 4) (spherePole 4)) : π_ 6 (WordHomology.Words 3) 1 :=
  (InclusionRange.orderedComparison 3 (by decide) 6).symm c

theorem comparison_wordAdjoint (c : π_ 7 (Sphere 4) (spherePole 4)) :
    InclusionRange.orderedComparison 3 (by decide) 6 (wordAdjoint c) = c :=
  (InclusionRange.orderedComparison 3 (by decide) 6).apply_symm_apply c

def adjointClassHom : π_ 7 (Sphere 4) (spherePole 4) →*
    Multiplicative (SingularHomology (WordHomology.Words 3) 6) :=
  (SixthHurewicz.hurewiczPi6 (1 : WordHomology.Words 3)).comp
    (InclusionRange.orderedComparison 3 (by decide) 6).symm.toMonoidHom

def adjointClass (c : π_ 7 (Sphere 4) (spherePole 4)) :
    SingularHomology (WordHomology.Words 3) 6 := (adjointClassHom c).toAdd

theorem adjointClass_eq (c : π_ 7 (Sphere 4) (spherePole 4)) :
    adjointClass c = SixthHurewicz.hurewiczFunction 1 (wordAdjoint c) := rfl

theorem adjointClass_one : adjointClass 1 = 0 :=
  congrArg Multiplicative.toAdd (map_one adjointClassHom)

theorem adjointClass_mul (a b : π_ 7 (Sphere 4) (spherePole 4)) :
    adjointClass (a * b) = adjointClass a + adjointClass b :=
  congrArg Multiplicative.toAdd (map_mul adjointClassHom a b)

def wordIntegerEquiv : SingularHomology (WordHomology.Words 3) 6 ≃ₗ[ℤ] ℤ :=
  (FirstStageQuotient.aboveHomologyEquiv 3 5 (by decide) (by decide)).trans
    QuotientHurewiczSix.integerEquiv

theorem wordIntegerEquiv_apply (c : SingularHomology (WordHomology.Words 3) 6) :
    wordIntegerEquiv c = QuotientHurewiczSix.integerEquiv
      (singularHomologyMap (FirstStageQuotient.quotientMap 3) 6 c) := rfl

theorem quotient_native_formula (c : π_ 7 (Sphere 4) (spherePole 4)) :
    FirstStageQuotient.sphereHopfHom 3 (by decide) 6
      (HigherHomotopy.map (N := Fin 6) (FirstStageQuotient.quotientMap 3) rfl
        (wordAdjoint c)) = SphereFourSeventh.hopf c := by
  have h := FirstStageQuotient.sphereHopfHom_quotientMap 3 (by decide) 6 (wordAdjoint c)
  change _ = SphereFourSeventh.hopf
    (InclusionRange.orderedComparison 3 (by decide) 6 (wordAdjoint c)) at h
  rw [comparison_wordAdjoint] at h
  exact h

theorem wordIntegerEquiv_adjoint (c : π_ 7 (Sphere 4) (spherePole 4)) :
    wordIntegerEquiv (adjointClass c) =
      (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
        (SphereFourSeventh.hopf c)).toAdd := by
  rw [adjointClass_eq, wordIntegerEquiv_apply,
    SixthHurewiczNative.natural (FirstStageQuotient.quotientMap 3) 1
      (FirstStageQuotient.basepoint 3) rfl,
    QuotientHurewiczSix.integerEquiv_hurewicz, quotient_native_formula]

theorem coordinate_hurewicz (c : π_ 7 (Sphere 4) (spherePole 4)) :
    (SphereFourSeventh.groupEquiv c).1.toAdd = wordIntegerEquiv (adjointClass c) := by
  rw [SphereFourSeventh.groupEquiv_hopf]
  exact (wordIntegerEquiv_adjoint c).symm

theorem adjointClass_eq_zero_iff_hopf (c : π_ 7 (Sphere 4) (spherePole 4)) :
    adjointClass c = 0 ↔ SphereFourSeventh.hopf c = 1 := by
  constructor
  · intro h
    apply (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)).injective
    have he := wordIntegerEquiv_adjoint c
    rw [h, map_zero] at he
    exact (congrArg Multiplicative.ofAdd he.symm).trans (map_one _).symm
  · intro h
    apply wordIntegerEquiv.injective
    rw [wordIntegerEquiv_adjoint, h, map_one, map_zero]
    rfl

theorem adjointClass_eq_zero_iff_suspension (c : π_ 7 (Sphere 4) (spherePole 4)) :
    adjointClass c = 0 ↔ ∃ a : π_ 6 (Sphere 3) (spherePole 3),
      SphereFourSeventh.suspension a = c :=
  (adjointClass_eq_zero_iff_hopf c).trans (SphereFourSeventh.hopf_kernel c)

theorem attaching_coordinate : SphereFiveEighth.relation.1.toAdd =
    wordIntegerEquiv (adjointClass SphereFourAttaching.attachingClass) :=
  coordinate_hurewicz SphereFourAttaching.attachingClass

theorem coordinate_comparison_cube (p : GenLoop (Fin 6) (WordHomology.Words 3) 1) :
    (SphereFourSeventh.groupEquiv
      (InclusionRange.orderedComparison 3 (by decide) 6 (Quotient.mk' p))).1.toAdd =
        wordIntegerEquiv (SixthHurewicz.cubeHomologyClass p) := by
  let c : π_ 6 (WordHomology.Words 3) 1 := Quotient.mk' p
  have he := congrArg
    (fun a : π_ 6 (WordHomology.Words 3) 1 ↦
      wordIntegerEquiv (SixthHurewicz.hurewiczFunction 1 a))
    ((InclusionRange.orderedComparison 3 (by decide) 6).symm_apply_apply c)
  exact (coordinate_hurewicz _).trans he

end NoExoticSixSphere.SphereFourHopfHomology
