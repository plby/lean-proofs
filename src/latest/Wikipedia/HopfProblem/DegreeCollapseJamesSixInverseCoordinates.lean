import Wikipedia.HopfProblem.DegreeCollapseJamesInverseAction
import Wikipedia.NoExoticSixSphere.SpherePairingCubeCoordinates
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageNativeHopf

/-!
# Exact second-stage inverse coordinates for the six-dimensional letter sphere

Reflected word reversal exchanges the two letter blocks and reflects
one coordinate in each. The resulting actual self-map of the smash
sphere S12 has positive permutation sign and two reflections, hence
is based homotopic to the identity. The original second-stage collapse
commutes with these specified maps.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesSixInverseCoordinates

open NoExoticSixSphere SmoothCube JamesSphere

def blockSwap : Equiv.Perm (Fin 12) :=
  (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin (6 + 6)).symm.trans
    ((Equiv.sumComm (Fin 6) (Fin 6)).trans finSumFinEquiv)

theorem blockSwap_sign : ((Equiv.Perm.sign blockSwap : ℤˣ) : ℤ) = 1 := by decide

def targetTwist : C(Sphere 12, Sphere 12) :=
  (reflection 12 (by decide) 0).comp
    ((reflection 12 (by decide) 6).comp (permutation 12 (by decide) blockSwap))

theorem targetTwist_pole : targetTwist (spherePole 12) = spherePole 12 := by
  simp only [targetTwist, ContinuousMap.comp_apply, permutation_pole, reflection_pole]

theorem targetTwist_homotopic_id :
    targetTwist.HomotopicRel (ContinuousMap.id (Sphere 12)) {spherePole 12} := by
  let e : BasedMap 12 (Sphere 12) (spherePole 12) := ⟨ContinuousMap.id _, rfl⟩
  let f := permuted (by decide : 0 < 12) blockSwap
    (reflected (by decide) 6 (reflected (by decide) 0 e))
  apply (sphereClass_eq_iff (by decide : 0 < 12) f e).mp
  rw [permuted_sphereClass, blockSwap_sign, zpow_one,
    reflected_sphereClass, reflected_sphereClass, inv_inv]

theorem pairing_inverse (x y : Sphere 6) :
    pairing 6 (reflection 6 (by decide) 0 y, reflection 6 (by decide) 0 x) =
      targetTwist (pairing 6 (x, y)) := by
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 6) x
  obtain ⟨v, rfl⟩ := quotient_surjective (by decide : 0 < 6) y
  rw [reflection_quotient, reflection_quotient, PairingCoordinates.pairing_cubes,
    PairingCoordinates.pairing_cubes]
  simp only [targetTwist, ContinuousMap.comp_apply]
  rw [permutation_quotient, reflection_quotient, reflection_quotient]
  apply congrArg (quotient 12)
  funext j
  fin_cases j <;> rfl

def stageInverse : C(SecondStage.Space 6, SecondStage.Space 6) :=
  (JamesWordReversal.stageMap (spherePole 6) (spherePole 6)
    (reflection 6 (by decide) 0) (reflection_pole 6 (by decide) 0) 2).comp
      (JamesWordReversal.stageReverse (spherePole 6) 2)

theorem stageInverse_basepoint :
    stageInverse (SecondStage.basepoint 6) = SecondStage.basepoint 6 := by
  apply Subtype.ext
  exact JamesInverseAction.inverseWords_one 6 (by decide) 0

theorem stageInverse_word (w : SecondStage.Space 6) :
    SecondStage.wordInclusion 6 (stageInverse w) =
      JamesInverseAction.inverseWords 6 (by decide) 0 (SecondStage.wordInclusion 6 w) := rfl

theorem stageInverse_presentation (v : Fin 2 → Sphere 6) :
    stageInverse (stagePresentation 6 2 v) =
      stagePresentation 6 2
        ![reflection 6 (by decide) 0 (v 1), reflection 6 (by decide) 0 (v 0)] := by
  apply Subtype.ext
  change JamesWordReversal.mapWords (spherePole 6) (spherePole 6)
    (reflection 6 (by decide) 0)
    (JamesWordReversal.reverse (spherePole 6) (James.word (spherePole 6) (List.ofFn v))) =
      James.word (spherePole 6)
        (List.ofFn ![reflection 6 (by decide) 0 (v 1), reflection 6 (by decide) 0 (v 0)])
  simp only [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil, mul_one]
  rw [JamesWordReversal.reverse_mul, JamesWordReversal.reverse_letter,
    JamesWordReversal.reverse_letter, map_mul,
    JamesWordReversal.mapWords_letter _ _ _ (reflection_pole 6 (by decide) 0),
    JamesWordReversal.mapWords_letter _ _ _ (reflection_pole 6 (by decide) 0)]
  rfl

theorem collapse_inverse (w : SecondStage.Space 6) :
    SecondStage.collapse 6 (stageInverse w) = targetTwist (SecondStage.collapse 6 w) := by
  obtain ⟨v, rfl⟩ := stagePresentation_surjective 6 2 w
  rw [stageInverse_presentation, SecondStage.collapse_presentation,
    SecondStage.collapse_presentation]
  exact pairing_inverse (v 0) (v 1)

end Wikipedia.HopfProblem.DegreeCollapse.JamesSixInverseCoordinates
