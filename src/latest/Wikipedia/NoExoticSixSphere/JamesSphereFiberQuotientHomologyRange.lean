import Wikipedia.NoExoticSixSphere.JamesSphereQuotientConnectivity

/-!
# The remaining comparison reduced to its actual integral homology map

Both genuine spaces are now proved simply connected. The checked
finite-range Hurewicz theorem therefore reduces native bijectivity of
the actual fiber-to-quotient homomorphism to homology bijectivity of the
original continuous path-composition map. This homology input is explicit;
its metastable proof, the homotopy-excision content, is not supplied here.
-/

noncomputable section

open CategoryTheory
open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

theorem toLoops_basepoint (n : ℕ) :
    toLoops n (basepoint n) = Path.refl (FirstStageQuotient.basepoint n) :=
  FiberQuotientComparison.toLoops_basepoint (inclusion n) (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.basepoint n) (quotient_inclusion n) (spherePole n)

theorem hom_eq_curry (n d : ℕ) [NeZero d] (c : π_ d (Fiber n) (basepoint n)) :
    hom n d c = GeneralizedLoopCurrying.homotopyMulEquiv d (FirstStageQuotient.basepoint n)
      (HigherHomotopy.map (N := Fin d) (toLoops n) (toLoops_basepoint n) c) := rfl

theorem hom_bijective_iff_toLoops (n d : ℕ) [NeZero d] :
    Function.Bijective (hom n d) ↔ Function.Bijective
      (HigherHomotopy.map (N := Fin d) (toLoops n) (toLoops_basepoint n)) := by
  change Function.Bijective
    ((GeneralizedLoopCurrying.homotopyMulEquiv d (FirstStageQuotient.basepoint n)) ∘
      HigherHomotopy.map (N := Fin d) (toLoops n) (toLoops_basepoint n)) ↔ _
  exact Function.Bijective.of_comp_iff'
    (GeneralizedLoopCurrying.homotopyMulEquiv d (FirstStageQuotient.basepoint n)).bijective _

theorem hom_bijective_of_homology (n D : ℕ) (hn : 2 ≤ n) (hD : 0 < D)
    (hH : ∀ k, 2 ≤ k → k ≤ D + 1 →
      Function.Bijective (singularHomologyMap (toLoops n) k))
    (d : ℕ) [NeZero d] (hdD : d ≤ D) : Function.Bijective (hom n d) := by
  let := fiber_simplyConnected n hn
  let := FirstStageQuotient.loops_simplyConnected n hn
  apply (hom_bijective_iff_toLoops n d).mpr
  have hb := HomologyRangeConnectivity.map_pi_bijective (TopCat.ofHom (toLoops n)) D hD hH
    d (Nat.pos_of_ne_zero (NeZero.ne d)) hdD (basepoint n)
  exact MappingCylinderNativeHomotopy.map_bijective_of_eq_target d (toLoops n)
    (toLoops_basepoint n) hb

end NoExoticSixSphere.JamesSphere.FiberQuotient
