import Wikipedia.NoExoticSixSphere.JamesSphereMeridianReflection
import Wikipedia.NoExoticSixSphere.JamesSphereOrderedLoopComparison
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCommutatorHomology

/-!
# The actual meridian commutator and a four-letter James word

The four letters are x, y, rho(x), rho(y), where rho is an actual
cube-descended sphere reflection. The proved meridian-reversal
homotopy replaces the two reversed Moore factors. Postcomposition
by the original normalization and coordinate reordering therefore
identifies all induced homology maps with the ordered James image
of this explicit finite word.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.MeridianCommutator

def fourLetters (n : ℕ) (hn : 0 < n) (i : Fin n) :
    C((Fin 2 → Sphere n), Fin 4 → Sphere n) :=
  ⟨fun v ↦ ![v 0, v 1, SmoothCube.reflection n hn i (v 0),
      SmoothCube.reflection n hn i (v 1)], by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact (SmoothCube.reflection n hn i).continuous.comp (continuous_apply 0)
    · exact (SmoothCube.reflection n hn i).continuous.comp (continuous_apply 1)⟩

def fourWordMap (n : ℕ) (hn : 0 < n) (i : Fin n) :
    C((Fin 2 → Sphere n), WordHomology.Words n) :=
  ⟨fun v ↦ James.word (spherePole n) (List.ofFn (fourLetters n hn i v)),
    (James.continuous_word_array (spherePole n) 4).comp (fourLetters n hn i).continuous⟩

theorem fourWordMap_apply (n : ℕ) (hn : 0 < n) (i : Fin n) (v : Fin 2 → Sphere n) :
    fourWordMap n hn i v =
      ((inclusion n (v 0) * inclusion n (v 1)) *
        inclusion n (SmoothCube.reflection n hn i (v 0))) *
          inclusion n (SmoothCube.reflection n hn i (v 1)) := by
  simp only [fourWordMap, List.ofFn_succ, List.ofFn_zero, James.word_cons,
    James.word_nil, mul_one]
  change inclusion n (v 0) * (inclusion n (v 1) *
    (inclusion n (SmoothCube.reflection n hn i (v 0)) *
      inclusion n (SmoothCube.reflection n hn i (v 1)))) = _
  simp only [mul_assoc]

theorem fourWordMap_moore (n : ℕ) (hn : 0 < n) (i : Fin n) (v : Fin 2 → Sphere n) :
    mooreComparison n (fourWordMap n hn i v) =
      mooreGenerator n (v 0) * mooreGenerator n (v 1) *
        mooreGenerator n (SmoothCube.reflection n hn i (v 0)) *
          mooreGenerator n (SmoothCube.reflection n hn i (v 1)) := by
  rw [fourWordMap_apply, mooreComparison_mul, mooreComparison_mul, mooreComparison_mul]
  simp only [inclusion, ContinuousMap.coe_mk, mooreComparison_letter]

theorem hopf_fourWordMap (n : ℕ) (hn : 0 < n) (i : Fin n) (v : Fin 2 → Sphere n) :
    hopf n (fourWordMap n hn i v) = James.word (spherePole (n + n))
      [pairing n (v 0, v 1),
        pairing n (v 0, SmoothCube.reflection n hn i (v 0)),
        pairing n (v 1, SmoothCube.reflection n hn i (v 0)),
        pairing n (v 0, SmoothCube.reflection n hn i (v 1)),
        pairing n (v 1, SmoothCube.reflection n hn i (v 1)),
        pairing n (SmoothCube.reflection n hn i (v 0),
          SmoothCube.reflection n hn i (v 1))] := by
  change James.secondHopf (spherePole n) (spherePole (n + n))
    (fun x y ↦ pairing n (x, y))
      (James.word (spherePole n) [v 0, v 1, SmoothCube.reflection n hn i (v 0),
        SmoothCube.reflection n hn i (v 1)]) = _
  rw [James.secondHopf_word (spherePole n) (spherePole (n + n))
    (fun x y ↦ pairing n (x, y)) (pairing_left_pole n) (pairing_right_pole n)]
  rfl

theorem commutator_fourWord_homotopic (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    (SphereMooreCommutator.commutator n (meridians n) (meridians n)).Homotopic
      ((mooreComparison n).comp (fourWordMap n hn i)) := by
  obtain ⟨H⟩ := reversed_meridians n hn i
  refine ⟨{
    toFun := fun u ↦ mooreGenerator n (u.2 0) * mooreGenerator n (u.2 1) *
      H (u.1, u.2 0) * H (u.1, u.2 1)
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · exact (((continuous_mooreGenerator n).comp
      ((continuous_apply 0).comp continuous_snd)).mul
      ((continuous_mooreGenerator n).comp ((continuous_apply 1).comp continuous_snd))).mul
      (H.continuous.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))) |>.mul
      (H.continuous.comp (continuous_fst.prodMk ((continuous_apply 1).comp continuous_snd)))
  · intro v
    rw [H.apply_zero, H.apply_zero]
    rfl
  · intro v
    rw [H.apply_one, H.apply_one]
    exact (fourWordMap_moore n hn i v).symm

end NoExoticSixSphere.JamesSphere.MeridianCommutator

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem commutator_fourWord_homology (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) (d : ℕ) :
    singularHomologyMap (normalizedSphereCommutator n) d =
      singularHomologyMap ((orderedLoopComparison n).comp
        (MeridianCommutator.fourWordMap n hn i)) d := by
  have h := (ContinuousMap.Homotopic.refl
    ((reorderPaths n).comp Moore.Loop.normalizationMap)).comp
      (MeridianCommutator.commutator_fourWord_homotopic n hn i)
  exact homotopy_homologyMap h.some d

end NoExoticSixSphere.JamesSphere.AttachingSquare
