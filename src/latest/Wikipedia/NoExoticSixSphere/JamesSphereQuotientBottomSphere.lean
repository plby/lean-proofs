import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageQuotient

/-!
# The second-stage sphere inside the full James quotient

The checked second-stage quotient homeomorphism gives a genuine embedded
sphere in the full quotient. The descended original Hopf map restricts
to the actual one-letter inclusion on this sphere. No assertion about
the connectivity of this embedding or homotopy excision is included.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.JamesSphere

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion n) := by
  intro x y h
  have he := congrArg (fun w ↦ loopComparison n w) h
  change loopComparison n (James.letter (spherePole n) x) =
    loopComparison n (James.letter (spherePole n) y) at he
  rw [loopComparison_letter, loopComparison_letter] at he
  exact unitLoop_injective n he

theorem isClosedEmbedding_inclusion (n : ℕ) : IsClosedEmbedding (inclusion n) :=
  (inclusion n).continuous.isClosedEmbedding (inclusion_injective n)

namespace FirstStageQuotient

def bottomSphere (n : ℕ) : C(Sphere (n + n), Space n) :=
  (stageMap n).comp ((SecondStage.quotientHomeomorph n).symm :
    C(Sphere (n + n), SecondStage.QuotientSpace n))

theorem bottomSphere_collapse (n : ℕ) (w : SecondStage.Space n) :
    bottomSphere n (SecondStage.collapse n w) = quotientMap n w.val := by
  change stageMap n ((SecondStage.quotientHomeomorph n).symm
    (SecondStage.collapse n w)) = _
  rw [← SecondStage.quotientHomeomorph_quotientMap n w, Homeomorph.symm_apply_apply]
  exact stageMap_quotientMap n w

theorem bottomSphere_injective (n : ℕ) : Function.Injective (bottomSphere n) :=
  (stageMap_injective n).comp (SecondStage.quotientHomeomorph n).symm.injective

theorem bottomSphere_pole (n : ℕ) : bottomSphere n (spherePole (n + n)) = basepoint n := by
  let w : SecondStage.Space n := ⟨1, Nat.zero_le 2⟩
  have hc : SecondStage.collapse n w = spherePole (n + n) :=
    (SecondStage.collapse_eq_pole_iff n w).mpr (Nat.zero_le 1)
  rw [← hc, bottomSphere_collapse]
  rfl

theorem hopfMap_bottomSphere (n : ℕ) (x : Sphere (n + n)) :
    hopfMap n (bottomSphere n x) = inclusion (n + n) x := by
  obtain ⟨w, rfl⟩ := SecondStage.collapse_surjective n x
  rw [bottomSphere_collapse, hopfMap_quotientMap]
  exact SecondStage.hopf_factor n w

theorem hopfMap_bottomSphere_comp (n : ℕ) :
    (hopfMap n).comp (bottomSphere n) = inclusion (n + n) := by
  apply ContinuousMap.ext
  exact hopfMap_bottomSphere n

theorem isEmbedding_bottomSphere (n : ℕ) : IsEmbedding (bottomSphere n) := by
  have hc : IsEmbedding ((hopfMap n) ∘ (bottomSphere n)) := by
    change IsEmbedding ((hopfMap n).comp (bottomSphere n))
    rw [hopfMap_bottomSphere_comp]
    exact (isClosedEmbedding_inclusion (n + n)).isEmbedding
  exact ⟨IsInducing.of_comp (bottomSphere n).continuous (hopfMap n).continuous hc.isInducing,
    bottomSphere_injective n⟩

end FirstStageQuotient

end NoExoticSixSphere.JamesSphere
