import Wikipedia.NoExoticSixSphere.JamesSphereLoopMap
import Wikipedia.NoExoticSixSphere.JamesLetterAction
import Wikipedia.NoExoticSixSphere.MooreLoopMultiplication

/-!
# The James comparison intertwines the one-letter actions up to homotopy

On the actual sphere and James word space, the comparison of adjoining a
letter with concatenating its sphere loop is supplied by a continuous
homotopy. The homotopy fixes the pair consisting of the pole and empty word.
This is an input to the James comparison theorem, not that theorem itself.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere

def loopAction (n : ℕ) : C(Sphere n × James.Space (Sphere n) (spherePole n),
    Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨fun p ↦ (unitLoop n p.1).trans (loopComparison n p.2),
    ((continuous_unitLoop n).comp continuous_fst).path_trans
      ((loopComparison n).continuous.comp continuous_snd)⟩

def actionHomotopy (n : ℕ) :
    ((loopComparison n).comp (James.letterAction (spherePole n))).Homotopy (loopAction n) where
  toFun u := Moore.Loop.multiplicationHomotopy
    (u.1, (mooreGenerator n u.2.1, mooreComparison n u.2.2))
  continuous_toFun := by
    have hp : Continuous (fun u : I × (Sphere n × James.Space (Sphere n) (spherePole n)) ↦
        (mooreGenerator n u.2.1, mooreComparison n u.2.2)) :=
      ((continuous_mooreGenerator n).comp (continuous_fst.comp continuous_snd)).prodMk
        ((mooreComparison n).continuous.comp (continuous_snd.comp continuous_snd))
    exact Moore.Loop.multiplicationHomotopy.continuous.comp (continuous_fst.prodMk hp)
  map_zero_left p := by
    refine (Moore.Loop.multiplicationHomotopy.map_zero_left
      (mooreGenerator n p.1, mooreComparison n p.2)).trans ?_
    change Moore.Loop.toPath (mooreGenerator n p.1 * mooreComparison n p.2) =
      Moore.Loop.toPath (mooreComparison n (James.letter (spherePole n) p.1 * p.2))
    rw [mooreComparison_mul, mooreComparison_letter]
  map_one_left p := by
    refine (Moore.Loop.multiplicationHomotopy.map_one_left
      (mooreGenerator n p.1, mooreComparison n p.2)).trans ?_
    change (Moore.Loop.toPath (mooreGenerator n p.1)).trans
      (Moore.Loop.toPath (mooreComparison n p.2)) =
        (unitLoop n p.1).trans (loopComparison n p.2)
    rw [toPath_mooreGenerator]
    rfl

theorem actionHomotopy_basepoint (n : ℕ) (s : I) :
    actionHomotopy n (s, (spherePole n, 1)) = Path.refl (spherePole (n + 1)) := by
  change Moore.Loop.multiplicationHomotopy
    (s, (mooreGenerator n (spherePole n), mooreComparison n 1)) = _
  rw [mooreGenerator_pole, mooreComparison_one, Moore.Loop.multiplicationHomotopy_one]

theorem loopComparison_action_homotopic (n : ℕ) :
    ((loopComparison n).comp (James.letterAction (spherePole n))).Homotopic (loopAction n) :=
  ⟨actionHomotopy n⟩

end NoExoticSixSphere.JamesSphere
