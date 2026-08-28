import Wikipedia.HopfProblem.DegreeCollapseAttachingSmashHomotopy
import Wikipedia.HopfProblem.DegreeCollapseFirstStemGroup

/-!
# The actual five-sphere attaching action on the first-stem generator

The original round boundary, the actual face collapse, and the original
source quotient give a homotopy-group automorphism. In degree ten its
source has order two, so it fixes the unique nonidentity element exactly.
The original EHP attaching action on that element therefore equals its
action by the independently constructed meridian smash map.
The nonidentity of this image remains a separate proof obligation.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FiveSphereAttachingGenerator

open NoExoticSixSphere JamesSphere AttachingSquare AttachingSmashHomotopy
open OrbitPair.HigherHomotopyCoordinates

def boundaryHomeomorph : Sphere 9 ≃ₜ fullBoundary 4 :=
  (RoundCell.boundaryHomeomorph 5 (by decide)).trans (fullBoundaryHomeomorph 4).symm

theorem boundaryHomeomorph_pole : boundaryHomeomorph (spherePole 9) = fullPoint 4 := by
  change (fullBoundaryHomeomorph 4).symm
    (RoundCell.boundaryHomeomorph 5 (by decide) (spherePole 9)) = _
  rw [RoundCell.boundaryHomeomorph_pole, ← fullBoundaryHomeomorph_point 4,
    Homeomorph.symm_apply_apply]

def boundaryPiEquiv (d : ℕ) [NeZero d] :
    π_ d (Sphere 9) (spherePole 9) ≃* π_ d (fullBoundary 4) (fullPoint 4) :=
  (homeomorphMulEquiv (Fin d) boundaryHomeomorph
    (spherePole 9)).trans (NativeHomotopyTargetEquality.equiv d boundaryHomeomorph_pole)

theorem boundaryPiEquiv_apply (d : ℕ) [NeZero d] (c : π_ d (Sphere 9) (spherePole 9)) :
    boundaryPiEquiv d c = HigherHomotopy.map (N := Fin d)
      (boundaryHomeomorph : C(_, _)) boundaryHomeomorph_pole c :=
  NativeHomotopyTargetEquality.equiv_map d
    (boundaryHomeomorph : C(Sphere 9, fullBoundary 4)) boundaryHomeomorph_pole c

def sourceChange (d : ℕ) [NeZero d] :
    π_ d (Sphere 9) (spherePole 9) ≃* π_ d (Sphere 9) (spherePole 9) :=
  (boundaryPiEquiv d).trans (sourceComparison 4 d)

theorem fullAttaching_comp : (fullAttaching 4).comp (boundaryHomeomorph : C(_, _)) =
    EHPCell.attachingMap 5 (by decide) := by
  apply ContinuousMap.ext
  intro x
  change CellBoundary.attaching 5 (fullBoundaryHomeomorph 4
    ((fullBoundaryHomeomorph 4).symm (RoundCell.boundaryHomeomorph 5 (by decide) x))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem attaching_comparison (d : ℕ) [NeZero d] (c : π_ d (Sphere 9) (spherePole 9)) :
    EHPCell.attachingHom 5 (by decide) d c =
      sourceSphereAttachingHom 4 d (sourceChange d c) := by
  have hmap : HigherHomotopy.map (N := Fin d) (fullAttaching 4) (fullAttaching_point 4)
      (boundaryPiEquiv d c) = EHPCell.attachingHom 5 (by decide) d c := by
    rw [boundaryPiEquiv_apply, HigherHomotopy.map_comp]
    simp only [fullAttaching_comp]
    rfl
  exact hmap.symm.trans (sourceAttaching_comparison 4 d (boundaryPiEquiv d c))

theorem sourceChange_generator :
    sourceChange 10 (FirstStemGroup.generator 6) = FirstStemGroup.generator 6 := by
  rcases FirstStemGroup.eq_one_or_generator 6
    (sourceChange 10 (FirstStemGroup.generator 6)) with h | h
  · exact False.elim (FirstStemGroup.generator_ne_one 6
      ((sourceChange 10).injective (h.trans (map_one (sourceChange 10)).symm)))
  · exact h

def meridianImage : π_ 10 (Sphere 5) (spherePole 5) :=
  HigherHomotopy.map meridianFiveMap.val meridianFiveMap.property (FirstStemGroup.generator 6)

theorem generator_comparison :
    EHPCell.attachingHom 5 (by decide) 10 (FirstStemGroup.generator 6) = meridianImage := by
  rw [attaching_comparison, sourceChange_generator, sourceFiveHom_comparison]
  rfl

theorem attaching_ten_injective_iff :
    Function.Injective (EHPCell.attachingHom 5 (by decide) 10) ↔ meridianImage ≠ 1 := by
  constructor
  · intro h hzero
    exact FirstStemGroup.generator_ne_one 6
      (h ((generator_comparison.trans hzero).trans
        (map_one (EHPCell.attachingHom 5 (by decide) 10)).symm))
  · intro h a b hab
    rcases FirstStemGroup.eq_one_or_generator 6 a with ha | ha <;>
      rcases FirstStemGroup.eq_one_or_generator 6 b with hb | hb
    · exact ha.trans hb.symm
    · rw [ha, hb, map_one, generator_comparison] at hab
      exact False.elim (h hab.symm)
    · rw [ha, hb, map_one, generator_comparison] at hab
      exact False.elim (h hab)
    · exact ha.trans hb.symm

theorem connecting_ten_injective_of_meridian_ne_one (h : meridianImage ≠ 1) :
    Function.Injective (EHP.connectingHomMetastable 5 10 (by decide) (by decide)) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := (EHPCell.comparisonHom_bijective 5 10
    (by decide) (by decide)).surjective a
  obtain ⟨d, rfl⟩ := (EHPCell.comparisonHom_bijective 5 10
    (by decide) (by decide)).surjective b
  rw [EHPCell.connecting_comparisonHom, EHPCell.connecting_comparisonHom] at hab
  exact congrArg (EHPCell.comparisonHom 5 (by decide) 10)
    ((attaching_ten_injective_iff.mpr h) hab)

theorem suspension_surjective_of_meridian_ne_one (h : meridianImage ≠ 1) :
    Function.Surjective (CubicalSphereSuspension.hom 11 5) := by
  intro x
  apply (EHP.hopf_eq_one_iff_metastable 5 10 (by decide) (by decide) x).mp
  apply connecting_ten_injective_of_meridian_ne_one h
  exact ((EHP.connecting_eq_one_iff_metastable 5 10 (by decide) (by decide) _).mpr
    ⟨x, rfl⟩).trans
      (map_one (EHP.connectingHomMetastable 5 10 (by decide) (by decide))).symm

end Wikipedia.HopfProblem.DegreeCollapse.FiveSphereAttachingGenerator
