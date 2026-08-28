import Wikipedia.NoExoticSixSphere.JamesSphereNativeHopf
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionCoordinates

/-!
# The original cubical suspension and the coordinate-corrected James maps

After the explicit target-coordinate reordering, the actual one-letter
homomorphism equals the existing cubical sphere suspension on every
native representative. Conjugating the actual James--Hopf homomorphism
by these same coordinate equivalences gives a zero composite with that
original suspension. No EHP exactness is inferred from this identity.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.SuspensionComparison

open SuspensionCoordinates

def coordinateEquiv (n d : ℕ) [NeZero d] :
    π_ d (Sphere (n + 1)) (spherePole (n + 1)) ≃*
      π_ d (Sphere (n + 1)) (spherePole (n + 1)) := by
  let f : C(Sphere (n + 1), Sphere (n + 1)) := reorder n
  have hb : Function.Bijective
      (HigherHomotopy.map (N := Fin d) f (y := spherePole (n + 1)) rfl) :=
    (HigherHomotopyCoordinates.homeomorphEquiv (Fin d) (reorder n) (spherePole (n + 1))).bijective
  exact MulEquiv.ofBijective
    (HigherHomotopy.mapMonoidHom (N := Fin d) f (reorder_pole n))
    (MappingCylinderNativeHomotopy.map_bijective_of_eq_target d f (reorder_pole n) hb)

def letterLoop {n d : ℕ} (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    GenLoop (Fin (d + 1)) (Sphere (n + 1)) (spherePole (n + 1)) :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (loopComparison n) (loopComparison_one n)
      (HigherHomotopy.genLoopMap (inclusion n) (NativeHopf.inclusion_pole n) p))

theorem letterLoop_apply {n d : ℕ} (p : GenLoop (Fin d) (Sphere n) (spherePole n))
    (u : Fin (d + 1) → unitInterval) :
    letterLoop p u = loopEvaluation n (p (Fin.tail u), u 0) := by
  change (loopComparison n (James.letter (spherePole n) (p (Fin.tail u)))) (u 0) = _
  rw [loopComparison_letter]
  rfl

theorem letterHom_mk (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    NativeHopf.letterHom n hn d (Quotient.mk' p) = Quotient.mk' (letterLoop p) := rfl

theorem reorder_letterLoop {n d : ℕ} (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    HigherHomotopy.genLoopMap (reorder n : C(_, _)) (reorder_pole n) (letterLoop p) =
      CubicalSphereSuspension.loop p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  change reorder n (letterLoop p u) = CubicalSphereSuspension.loop p u
  rw [letterLoop_apply, CubicalSphereSuspension.loop_apply]
  exact reorder_loopEvaluation n (p (Fin.tail u)) (u 0)

theorem coordinateEquiv_letterHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    coordinateEquiv n (d + 1) (NativeHopf.letterHom n hn d c) =
      CubicalSphereSuspension.hom d n c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  exact congrArg (fun q : GenLoop (Fin (d + 1)) (Sphere (n + 1)) (spherePole (n + 1)) ↦
    (Quotient.mk' q : π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)))) (reorder_letterLoop p)

def orderedHopfHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) →*
      π_ (d + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) :=
  (coordinateEquiv (n + n) (d + 1)).toMonoidHom.comp
    ((NativeHopf.hopfHom n hn d).comp (coordinateEquiv n (d + 1)).symm.toMonoidHom)

theorem orderedHopfHom_suspension (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    orderedHopfHom n hn d (CubicalSphereSuspension.hom d n c) = 1 := by
  rw [← coordinateEquiv_letterHom n hn d c]
  change coordinateEquiv (n + n) (d + 1)
    (NativeHopf.hopfHom n hn d ((coordinateEquiv n (d + 1)).symm
      (coordinateEquiv n (d + 1) (NativeHopf.letterHom n hn d c)))) = 1
  rw [MulEquiv.symm_apply_apply, NativeHopf.hopfHom_letterHom, map_one]

end NoExoticSixSphere.JamesSphere.SuspensionComparison
