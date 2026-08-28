import Wikipedia.HopfProblem.DegreeCollapseJamesSixInverseNative
import Wikipedia.HopfProblem.DegreeCollapseTwelveSphereTorsion
import Wikipedia.NoExoticSixSphere.JamesSphereEHPMetastable
import Wikipedia.NoExoticSixSphere.CubicalStableSixEquivalence

/-!
# The original suspension pi12(S6) -> pi13(S7) is surjective

The actual second-stage collapse has involutive image in pi12(S12),
whose integral coordinate has no nontrivial involution. Thus this
collapse is zero on the required native group. Every relevant James
class has an original second-stage representative, so the original
James--Hopf map vanishes. Metastable EHP exactness gives surjectivity.
Consequently the literal S6 stage covers the stable sixth stem.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixSphereDesuspension

open NoExoticSixSphere JamesSphere CubicalSphereSuspension

theorem collapse_native_eq_one
    (c : π_ 12 (SecondStage.Space 6) (SecondStage.basepoint 6)) :
    HigherHomotopy.map (N := Fin 12) (SecondStage.collapse 6)
      (SecondStage.collapse_basepoint 6) c = 1 :=
  TwelveSphereTorsion.eq_one_of_eq_inv _ (JamesSixInverseNative.collapse_eq_inv c)

theorem comparison_surjective :
    Function.Surjective (SecondStage.comparisonHom 6 (by decide) 12) :=
  (SuspensionComparison.coordinateEquiv 6 13).surjective.comp
    ((NativeHopf.spherePiEquiv 6 (by decide) 12).surjective.comp
      (SecondStage.wordInclusion_pi_bijective 6 (by decide) 12
        (by decide) (by decide) (SecondStage.basepoint 6)).surjective)

theorem hopf_eq_one (x : π_ 13 (Sphere 7) (spherePole 7)) :
    SuspensionComparison.orderedHopfHom 6 (by decide) 12 x = 1 := by
  obtain ⟨c, rfl⟩ := comparison_surjective x
  rw [SecondStage.orderedHopfHom_comparisonHom, collapse_native_eq_one, map_one]

theorem suspension_surjective : Function.Surjective (hom 12 6) := by
  intro x
  exact (EHP.hopf_eq_one_iff_metastable 6 11 (by decide) (by decide) x).mp (hopf_eq_one x)

theorem stable_surjective : Function.Surjective (CubicalStableSix.ofNative (k := 4)) := by
  intro z
  obtain ⟨x, hx⟩ := CubicalStableSix.ofNative_surjective (by decide : 5 ≤ 5) z
  obtain ⟨a, rfl⟩ := suspension_surjective x
  exact ⟨a, (CubicalStableSix.ofNative_stepHom 4 a).symm.trans hx⟩

end Wikipedia.HopfProblem.DegreeCollapse.SixSphereDesuspension

