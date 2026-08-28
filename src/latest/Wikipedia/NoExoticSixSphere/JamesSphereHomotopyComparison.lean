import Wikipedia.NoExoticSixSphere.JamesPairFiberConnectivity
import Wikipedia.NoExoticSixSphere.MappingCylinderNativeHomotopy
import Wikipedia.NoExoticSixSphere.JamesComparisonFiber

/-!
# The original James comparison induces native homotopy isomorphisms

For sphere dimension at least two, the source-image inclusion is already
proved to induce bijections in every positive native degree. The actual
mapping-cylinder projection and source homeomorphism transport these
bijections to the original continuous comparison map. Degree zero uses
the proved path connectedness. The original comparison fiber's native
groups then vanish by its genuine exact sequence.

No homotopy equivalence of spaces is inferred from these group bijections.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.JamesSphere.HomotopyComparison

open ComparisonCylinder

theorem comparison_piZero_bijective (n : ℕ) (x : WordHomology.Words (n + 2)) :
    Function.Bijective (HigherHomotopy.map (N := Fin 0) (loopComparison (n + 2))
      (y := x) rfl) := by
  let := JamesSphere.simplyConnectedSpace n
  let := loops_simplyConnected n
  let : Subsingleton (ZerothHomotopy (WordHomology.Words (n + 2))) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp
      (inferInstanceAs (PathConnectedSpace (WordHomology.Words (n + 2))))).2
  let : Subsingleton (ZerothHomotopy (CoverMaps.Loops (n + 2))) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp
      (inferInstanceAs (PathConnectedSpace (CoverMaps.Loops (n + 2))))).2
  let : Subsingleton (π_ 0 (WordHomology.Words (n + 2)) x) :=
    HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton
  let : Subsingleton (π_ 0 (CoverMaps.Loops (n + 2)) (loopComparison (n + 2) x)) :=
    HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun c ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ c⟩⟩

theorem comparison_pi_bijective (n d : ℕ) (x : WordHomology.Words (n + 2)) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (loopComparison (n + 2))
      (y := x) rfl) := by
  cases d with
  | zero => exact comparison_piZero_bijective n x
  | succ d =>
    exact MappingCylinderNativeHomotopy.original_pi_bijective (comparison (n + 2)) (d + 1)
      (by omega) (FiberConnectivity.inclusion_pi_bijective n (d + 1) (by omega)) x

def comparisonPiEquiv (n d : ℕ) [NeZero d] (x : WordHomology.Words (n + 2)) :
    π_ d (WordHomology.Words (n + 2)) x ≃*
      π_ d (CoverMaps.Loops (n + 2)) (loopComparison (n + 2) x) :=
  MulEquiv.ofBijective
    (HigherHomotopy.mapMonoidHom (N := Fin d) (loopComparison (n + 2)) (y := x) rfl)
    (comparison_pi_bijective n d x)

theorem comparison_pi_bijective_of_two_le (n d : ℕ) (hn : 2 ≤ n)
    (x : WordHomology.Words n) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (loopComparison n) (y := x) rfl) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact comparison_pi_bijective m d x

theorem comparisonPiEquiv_apply (n d : ℕ) [NeZero d]
    (x : WordHomology.Words (n + 2)) (c : π_ d (WordHomology.Words (n + 2)) x) :
    comparisonPiEquiv n d x c =
      HigherHomotopy.map (N := Fin d) (loopComparison (n + 2)) (y := x) rfl c := rfl

theorem comparison_fiber_pi (n d : ℕ) (hd : 0 < d)
    (x : WordHomology.Words (n + 2)) (p : ComparisonFiber.Space (n + 2) x) :
    Subsingleton (π_ d (ComparisonFiber.Space (n + 2) x) p) := by
  let := ComparisonFiber.simplyConnectedSpace n x
  let : Subsingleton (π_ d (ComparisonFiber.Space (n + 2) x)
      (ComparisonFiber.basepoint (n + 2) x)) :=
    HomotopyFiberConnectivity.homotopy_subsingleton_of_maps d (loopComparison (n + 2)) x
      (comparison_pi_bijective n d x).injective
      (comparison_pi_bijective n (d + 1) x).surjective
  exact NativeHomotopyBasepointVanishing.subsingleton d hd
    (ComparisonFiber.basepoint (n + 2) x) p

end NoExoticSixSphere.JamesSphere.HomotopyComparison
