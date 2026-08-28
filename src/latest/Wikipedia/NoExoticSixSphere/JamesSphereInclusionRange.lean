import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionComparison
import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality

/-!
# Connectivity of the original one-letter inclusion

The checked coordinate-corrected James comparison identifies the actual
one-letter native map with cubical suspension. Its stable-range injection
and surjection therefore apply to the original inclusion, including the
literal image basepoint required by the genuine homotopy-fiber sequence.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.InclusionRange

def orderedComparison (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d] :
    π_ d (WordHomology.Words n) 1 ≃*
      π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  (NativeHopf.spherePiEquiv n hn d).trans (SuspensionComparison.coordinateEquiv n (d + 1))

theorem orderedComparison_inclusion (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    orderedComparison n hn d
      (HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n) c) =
        CubicalSphereSuspension.hom d n c :=
  SuspensionComparison.coordinateEquiv_letterHom n hn d c

theorem inclusion_injective (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 2 ≤ 2 * n) :
    Function.Injective
      (HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n)) := by
  intro x y hxy
  apply CubicalSphereSuspension.hom_injective (m := d) (n := n) (by omega)
  rw [← orderedComparison_inclusion n hn d, ← orderedComparison_inclusion n hn d, hxy]

theorem inclusion_surjective (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 1 ≤ 2 * n) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n)) := by
  intro c
  obtain ⟨b, hb⟩ := CubicalSphereSuspension.hom_surjective (m := d) (n := n)
    (by omega) (orderedComparison n hn d c)
  refine ⟨b, (orderedComparison n hn d).injective ?_⟩
  rw [orderedComparison_inclusion]
  exact hb

theorem inclusion_injective_imageBasepoint (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 2 ≤ 2 * n) :
    Function.Injective
      (HigherHomotopy.map (N := Fin d) (inclusion n) (y := spherePole n) rfl) :=
  (NativeHomotopyTargetEquality.map_injective_iff d (inclusion n)
    (NativeHopf.inclusion_pole n)).mp (inclusion_injective n d hn hdn)

theorem inclusion_surjective_imageBasepoint (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 1 ≤ 2 * n) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin d) (inclusion n) (y := spherePole n) rfl) :=
  (NativeHomotopyTargetEquality.map_surjective_iff d (inclusion n)
    (NativeHopf.inclusion_pole n)).mp (inclusion_surjective n d hn hdn)

end NoExoticSixSphere.JamesSphere.InclusionRange
