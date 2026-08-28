import Wikipedia.NoExoticSixSphere.JamesSphereHomotopyComparison
import Wikipedia.NoExoticSixSphere.JamesSphereHopf

/-!
# The actual James--Hopf map on native sphere homotopy groups

The proved James comparison at the actual unit word, followed by native
loop currying, identifies the word-space groups with the original sphere
groups. Transporting the constructed second James--Hopf map through these
equivalences gives a homomorphism on the actual sphere groups. It kills
the homomorphism induced by the actual one-letter inclusion.

EHP exactness, and identification of the one-letter homomorphism with the
previously constructed sphere suspension, are not asserted here.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.NativeHopf

def basedComparisonPiEquiv (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (WordHomology.Words n) 1 ≃*
      π_ d (Path (spherePole (n + 1)) (spherePole (n + 1))) (Path.refl (spherePole (n + 1))) :=
  MulEquiv.ofBijective
    (HigherHomotopy.mapMonoidHom (N := Fin d) (loopComparison n) (loopComparison_one n))
    (MappingCylinderNativeHomotopy.map_bijective_of_eq_target d (loopComparison n)
      (loopComparison_one n) (HomotopyComparison.comparison_pi_bijective_of_two_le n d hn 1))

def spherePiEquiv (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (WordHomology.Words n) 1 ≃* π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  (basedComparisonPiEquiv n hn d).trans
    (GeneralizedLoopCurrying.homotopyMulEquiv d (spherePole (n + 1)))

def hopfHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) →*
      π_ (d + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) :=
  (spherePiEquiv (n + n) (by omega) d).toMonoidHom.comp
    ((HigherHomotopy.mapMonoidHom (N := Fin d) (hopf n) (hopf_one n)).comp
      (spherePiEquiv n hn d).symm.toMonoidHom)

theorem hopfHom_comparison (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (WordHomology.Words n) 1) :
    hopfHom n hn d (spherePiEquiv n hn d c) =
      spherePiEquiv (n + n) (by omega) d
        (HigherHomotopy.map (N := Fin d) (hopf n) (hopf_one n) c) := by
  change spherePiEquiv (n + n) (by omega) d
    (HigherHomotopy.map (N := Fin d) (hopf n) (hopf_one n)
      ((spherePiEquiv n hn d).symm (spherePiEquiv n hn d c))) = _
  rw [MulEquiv.symm_apply_apply]

theorem inclusion_pole (n : ℕ) : inclusion n (spherePole n) = 1 :=
  James.letter_basepoint (spherePole n)

def letterHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (Sphere n) (spherePole n) →*
      π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  (spherePiEquiv n hn d).toMonoidHom.comp
    (HigherHomotopy.mapMonoidHom (N := Fin d) (inclusion n) (inclusion_pole n))

theorem nativeHopf_letter (n d : ℕ) [NeZero d] (c : π_ d (Sphere n) (spherePole n)) :
    HigherHomotopy.map (N := Fin d) (hopf n) (hopf_one n)
      (HigherHomotopy.map (N := Fin d) (inclusion n) (inclusion_pole n) c) = 1 := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin d) (WordHomology.Words (n + n)) 1 ↦
    (Quotient.mk' q : π_ d (WordHomology.Words (n + n)) 1))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact hopf_letter n (p t)

theorem hopfHom_letterHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) : hopfHom n hn d (letterHom n hn d c) = 1 := by
  change hopfHom n hn d (spherePiEquiv n hn d
    (HigherHomotopy.map (N := Fin d) (inclusion n) (inclusion_pole n) c)) = 1
  rw [hopfHom_comparison, nativeHopf_letter, map_one]

end NoExoticSixSphere.JamesSphere.NativeHopf
