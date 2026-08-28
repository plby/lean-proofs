import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageCone
import Wikipedia.NoExoticSixSphere.JamesSphereBottomHomotopy
import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality

/-!
# The original finite-to-full quotient map on native homotopy

The checked bottom-sphere comparison factors through the actual
second-stage quotient homeomorphism. Both basepoint identities are
literal quotient identities. This transfers the proved range to the
original finite-to-full quotient map itself.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem stageMap_basepoint (n : ℕ) :
    stageMap n (SecondStageCone.quotientBasepoint n) = basepoint n := rfl

theorem secondQuotient_pole (n : ℕ) :
    SecondStage.quotientHomeomorph n (SecondStageCone.quotientBasepoint n) =
      spherePole (n + n) :=
  SecondStage.quotientHomeomorph_lower n ⟨1, Nat.zero_le 2⟩ (Nat.zero_le 1)

theorem bottomSphere_quotientHomeomorph (n : ℕ) :
    (bottomSphere n).comp (SecondStage.quotientHomeomorph n : C(_, _)) = stageMap n := by
  apply ContinuousMap.ext
  intro z
  change stageMap n ((SecondStage.quotientHomeomorph n).symm
    (SecondStage.quotientHomeomorph n z)) = stageMap n z
  rw [Homeomorph.symm_apply_apply]

theorem stageMap_native_factor (n d : ℕ) :
    HigherHomotopy.map (N := Fin d) (bottomSphere n) (bottomSphere_pole n) ∘
      HigherHomotopy.map (N := Fin d) (SecondStage.quotientHomeomorph n : C(_, _))
        (secondQuotient_pole n) =
      HigherHomotopy.map (N := Fin d) (stageMap n) (stageMap_basepoint n) := by
  funext c
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun r : GenLoop (Fin d) (Space n) (basepoint n) ↦
    (Quotient.mk _ r : π_ d (Space n) (basepoint n)))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact ContinuousMap.congr_fun (bottomSphere_quotientHomeomorph n) (p.val z)

theorem stageMap_pi_bijective (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) (hdn : d + 2 ≤ 3 * n) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (stageMap n) (stageMap_basepoint n)) := by
  let e : C(SecondStage.QuotientSpace n, Sphere (n + n)) := SecondStage.quotientHomeomorph n
  have he₀ : Function.Bijective
      (HigherHomotopy.map (N := Fin d) e (y := SecondStageCone.quotientBasepoint n) rfl) :=
    (HigherHomotopyCoordinates.homeomorphEquiv (Fin d) (SecondStage.quotientHomeomorph n)
      (SecondStageCone.quotientBasepoint n)).bijective
  have he : Function.Bijective (HigherHomotopy.map (N := Fin d)
      e (secondQuotient_pole n)) :=
    (NativeHomotopyTargetEquality.map_bijective_iff d e (secondQuotient_pole n)).mpr he₀
  have hb := (bottomSphere_pi_bijective_range n d hn hd hdn).comp he
  dsimp only [e] at hb
  rwa [stageMap_native_factor] at hb

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
