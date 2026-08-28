import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageQuotient
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionComparison

/-!
# The actual James--Hopf homomorphism on second-stage representatives

For a native class represented in the genuine second James stage, the
coordinate-corrected James--Hopf map is the original cubical suspension
of the quotient collapse class. All maps and basepoints are retained.
This identifies a restriction of the actual map; it does not assert
that arbitrary classes have second-stage representatives or prove EHP.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.SecondStage

def basepoint (n : ℕ) : Space n := ⟨1, Nat.zero_le 2⟩

def wordInclusion (n : ℕ) : C(Space n, WordHomology.Words n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem collapse_basepoint (n : ℕ) : collapse n (basepoint n) = spherePole (n + n) :=
  (collapse_eq_pole_iff n (basepoint n)).mpr (Nat.zero_le 1)

theorem native_hopf_factor (n d : ℕ) [NeZero d] (c : π_ d (Space n) (basepoint n)) :
    HigherHomotopy.map (N := Fin d) (hopf n) (hopf_one n)
      (HigherHomotopy.map (N := Fin d) (wordInclusion n) rfl c) =
    HigherHomotopy.map (N := Fin d) (inclusion (n + n)) (NativeHopf.inclusion_pole (n + n))
      (HigherHomotopy.map (N := Fin d) (collapse n) (collapse_basepoint n) c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin d) (WordHomology.Words (n + n)) 1 ↦
    (Quotient.mk' q : π_ d (WordHomology.Words (n + n)) 1))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact hopf_factor n (p u)

def comparisonHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (Space n) (basepoint n) →*
      π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  (SuspensionComparison.coordinateEquiv n (d + 1)).toMonoidHom.comp
    ((NativeHopf.spherePiEquiv n hn d).toMonoidHom.comp
      (HigherHomotopy.mapMonoidHom (N := Fin d) (wordInclusion n) rfl))

theorem orderedHopfHom_comparisonHom (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Space n) (basepoint n)) :
    SuspensionComparison.orderedHopfHom n hn d (comparisonHom n hn d c) =
      CubicalSphereSuspension.hom d (n + n)
        (HigherHomotopy.map (N := Fin d) (collapse n) (collapse_basepoint n) c) := by
  change SuspensionComparison.coordinateEquiv (n + n) (d + 1)
    (NativeHopf.hopfHom n hn d ((SuspensionComparison.coordinateEquiv n (d + 1)).symm
      (SuspensionComparison.coordinateEquiv n (d + 1) (NativeHopf.spherePiEquiv n hn d
        (HigherHomotopy.map (N := Fin d) (wordInclusion n) rfl c))))) = _
  rw [MulEquiv.symm_apply_apply, NativeHopf.hopfHom_comparison, native_hopf_factor]
  exact SuspensionComparison.coordinateEquiv_letterHom (n + n) (by omega) d
    (HigherHomotopy.map (N := Fin d) (collapse n) (collapse_basepoint n) c)

end NoExoticSixSphere.JamesSphere.SecondStage
