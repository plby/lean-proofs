import Wikipedia.HopfProblem.DegreeCollapseMooreBasedNormalization
import Wikipedia.HopfProblem.DegreeCollapseJamesWordReversal
import Wikipedia.HopfProblem.DegreeCollapseJamesHomotopyLift
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyPrecomposition

/-!
# Reflected word reversal acts by inversion on the original James groups

Extend the proved based meridian homotopy to all original James words
and precompose by actual word reversal. Moore reversal reverses products,
and normalization is literal native path reversal. The original James
comparison therefore identifies the resulting word map with inversion
in every positive native homotopy degree.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesInverseAction

open NoExoticSixSphere JamesSphere MeridianCommutator

theorem reversed_pole (n : ℕ) : reversedMeridians n (spherePole n) = 1 := by
  change Moore.Loop.reverse (mooreGenerator n (spherePole n)) = 1
  rw [mooreGenerator_pole, Moore.Loop.reverse_one]

theorem reflected_pole (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ((meridians n).comp (SmoothCube.reflection n hn i)) (spherePole n) = 1 := by
  change mooreGenerator n (SmoothCube.reflection n hn i (spherePole n)) = 1
  rw [SmoothCube.reflection_pole, mooreGenerator_pole]

def inverseWords (n : ℕ) (hn : 0 < n) (i : Fin n) :
    C(WordHomology.Words n, WordHomology.Words n) :=
  (JamesWordReversal.mapWordsContinuous (spherePole n) (spherePole n)
    (SmoothCube.reflection n hn i) (SmoothCube.reflection_pole n hn i)).comp
      (JamesWordReversal.reverseMap (spherePole n))

theorem inverseWords_one (n : ℕ) (hn : 0 < n) (i : Fin n) :
    inverseWords n hn i 1 = 1 := by
  change JamesWordReversal.mapWords (spherePole n) (spherePole n)
    (SmoothCube.reflection n hn i) (JamesWordReversal.reverse (spherePole n) 1) = 1
  rw [JamesWordReversal.reverse_one, map_one]

theorem reversed_lift (n : ℕ) (w : WordHomology.Words n) :
    James.lift (spherePole n) (reversedMeridians n)
      (JamesWordReversal.reverse (spherePole n) w) =
        Moore.Loop.reverse (mooreComparison n w) := by
  obtain ⟨l, rfl⟩ := James.word_surjective (spherePole n) w
  induction l with
  | nil =>
    rw [James.word_nil, JamesWordReversal.reverse_one, map_one,
      mooreComparison_one, Moore.Loop.reverse_one]
  | cons x l ih =>
    rw [James.word_cons, JamesWordReversal.reverse_mul, map_mul,
      JamesWordReversal.reverse_letter, James.lift_letter _ _ (reversed_pole n),
      ih, mooreComparison_mul, Moore.Loop.reverse_mul, mooreComparison_letter]
    rfl

theorem reflected_lift (n : ℕ) (hn : 0 < n) (i : Fin n) (w : WordHomology.Words n) :
    James.lift (spherePole n) ((meridians n).comp (SmoothCube.reflection n hn i)) w =
      mooreComparison n (JamesWordReversal.mapWords (spherePole n) (spherePole n)
        (SmoothCube.reflection n hn i) w) := by
  have he : (James.lift (spherePole n) (mooreGenerator n)).comp
      (JamesWordReversal.mapWords (spherePole n) (spherePole n)
        (SmoothCube.reflection n hn i)) =
      James.lift (spherePole n) ((meridians n).comp (SmoothCube.reflection n hn i)) := by
    apply James.hom_ext (spherePole n)
    intro x
    simp only [MonoidHom.comp_apply,
      JamesWordReversal.mapWords_letter _ _ _ (SmoothCube.reflection_pole n hn i),
      James.lift_letter _ _ (mooreGenerator_pole n),
      James.lift_letter _ _ (reflected_pole n hn i)]
    rfl
  exact (DFunLike.congr_fun he w).symm

theorem moore_comparison_homotopic (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    (Moore.Loop.reverseMap.comp (mooreComparison n)).HomotopicRel
      ((mooreComparison n).comp (inverseWords n hn i)) {1} := by
  obtain ⟨H⟩ := MeridianBasedReversal.reversed_meridians_based n hn i
  let K := JamesHomotopyLift.lifted H (reversed_pole n) (reflected_pole n hn i)
  let L := Wikipedia.HomotopyGroupsOfSpheres.pointedHomotopyPrecomp K
    (JamesWordReversal.reverseMap (spherePole n)) 1
    (JamesWordReversal.reverse_one (spherePole n))
  refine ⟨L.cast ?_ ?_⟩
  · apply ContinuousMap.ext
    intro w
    exact reversed_lift n w
  · apply ContinuousMap.ext
    intro w
    exact reflected_lift n hn i (JamesWordReversal.reverse (spherePole n) w)

theorem loop_comparison_homotopic (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    ((GeneralizedLoopCurrying.reverseMap (spherePole (n + 1))).comp
      (loopComparison n)).HomotopicRel
      ((loopComparison n).comp (inverseWords n hn i)) {1} := by
  obtain ⟨H⟩ := moore_comparison_homotopic n hn i
  refine ⟨(H.compContinuousMap Moore.Loop.normalizationMap).cast ?_ ?_⟩
  · apply ContinuousMap.ext
    intro w
    exact Moore.Loop.toPath_reverse (mooreComparison n w)
  · rfl

theorem inverseWords_native (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (d : ℕ) [NeZero d] (c : π_ d (WordHomology.Words n) 1) :
    HigherHomotopy.map (N := Fin d) (inverseWords n (by omega) i)
      (inverseWords_one n (by omega) i) c = c⁻¹ := by
  let : NeZero n := ⟨by omega⟩
  apply (NativeHopf.basedComparisonPiEquiv n hn d).injective
  rw [map_inv]
  change HigherHomotopy.map (N := Fin d) (loopComparison n) (loopComparison_one n)
    (HigherHomotopy.map (N := Fin d) (inverseWords n (by omega) i)
      (inverseWords_one n (by omega) i) c) =
        (HigherHomotopy.map (N := Fin d) (loopComparison n) (loopComparison_one n) c)⁻¹
  obtain ⟨H⟩ := loop_comparison_homotopic n (by omega) i
  have h := HigherHomotopy.map_eq_of_based_homotopy
    ((GeneralizedLoopCurrying.reverseMap (spherePole (n + 1))).comp (loopComparison n))
    ((loopComparison n).comp (inverseWords n (by omega) i))
    ((congrArg (GeneralizedLoopCurrying.reverseMap (spherePole (n + 1)))
      (loopComparison_one n)).trans (GeneralizedLoopCurrying.reverseMap_refl _))
    ((congrArg (loopComparison n) (inverseWords_one n (by omega) i)).trans
      (loopComparison_one n)) H c
  have h₁ := HigherHomotopy.map_comp (inverseWords n (by omega) i)
    (inverseWords_one n (by omega) i) (loopComparison n) (loopComparison_one n) c
  have h₂ := HigherHomotopy.map_comp (loopComparison n) (loopComparison_one n)
    (GeneralizedLoopCurrying.reverseMap (spherePole (n + 1)))
    (GeneralizedLoopCurrying.reverseMap_refl _) c
  exact h₁.trans (h.symm.trans (h₂.symm.trans (GeneralizedLoopCurrying.reverse_native _)))

end Wikipedia.HopfProblem.DegreeCollapse.JamesInverseAction

