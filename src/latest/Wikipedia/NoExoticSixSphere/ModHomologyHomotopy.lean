import Wikipedia.HopfProblem.SphereHomologyCoefficientsBasic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Homotopy invariance with the original finite coefficient object

The native simplicial prism homotopy is applied with coefficient module
`ZMod p`. This compares the original homology maps, without replacing the
finite-coefficient homology by a quotient of integral homology.
-/

noncomputable section

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem modHomologyMap_homotopy (p : ℕ) {f g : C(X, Y)}
    (H : f.Homotopy g) (n : ℕ) : modHomologyMap p f n = modHomologyMap p g n := by
  exact congrArg ModuleCat.Hom.hom
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ (ZMod p)) n)

theorem modHomologyMap_homotopic (p : ℕ) {f g : C(X, Y)}
    (H : f.Homotopic g) (n : ℕ) : modHomologyMap p f n = modHomologyMap p g n := by
  obtain ⟨H⟩ := H
  exact modHomologyMap_homotopy p H n

end NoExoticSixSphere
