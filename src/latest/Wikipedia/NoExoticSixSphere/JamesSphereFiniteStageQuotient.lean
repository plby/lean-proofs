import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageCofibration
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientSeparation
import Wikipedia.NoExoticSixSphere.JamesSphereSimplyConnected

/-!
# Actual finite-stage quotients inside the full James quotient

Each finite quotient collapses the original first stage and embeds as a
closed subspace of the full quotient. The original cofibration and collapse
pushout prove simple connectivity when the sphere dimension is at least two.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.FiniteStage

open FirstStageCofibration

abbrev Space (n k : ℕ) := CollapsedSubspace.Space (lower n k)

def quotientMap (n k : ℕ) : C(Words n k, Space n k) :=
  CollapsedSubspace.quotientMap (lower n k)

def map (n k : ℕ) : C(Space n k, FirstStageQuotient.Space n) :=
  CollapsedSubspace.lift (lower n k)
    ((FirstStageQuotient.quotientMap n).comp ⟨Subtype.val, continuous_subtype_val⟩)
    (fun w hw z hz ↦ (CollapsedSubspace.quotientMap_eq_iff
      (James.stage (spherePole n) 1) w.val z.val).mpr (Or.inr ⟨hw, hz⟩))

theorem map_quotientMap (n k : ℕ) (w : Words n k) :
    map n k (quotientMap n k w) = FirstStageQuotient.quotientMap n w.val := rfl

theorem map_injective (n k : ℕ) : Function.Injective (map n k) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun w z h ↦ ?_
  change FirstStageQuotient.quotientMap n w.val = FirstStageQuotient.quotientMap n z.val at h
  rcases (CollapsedSubspace.quotientMap_eq_iff (James.stage (spherePole n) 1)
    w.val z.val).mp h with hwz | ⟨hw, hz⟩
  · exact Quotient.sound (Or.inl (Subtype.ext hwz))
  · exact Quotient.sound (Or.inr ⟨hw, hz⟩)

theorem isClosedEmbedding_map (n k : ℕ) : IsClosedEmbedding (map n k) :=
  (map n k).continuous.isClosedEmbedding (map_injective n k)

theorem range_map (n k : ℕ) :
    Set.range (map n k) =
      FirstStageQuotient.quotientMap n '' James.stage (spherePole n) (k + 1) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    refine Quotient.inductionOn a fun w ↦ ?_
    exact ⟨w.val, w.property, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨quotientMap n k ⟨w, hw⟩, rfl⟩

def rangeHomeomorph (n k : ℕ) : Space n k ≃ₜ Set.range (map n k) :=
  (isClosedEmbedding_map n k).isEmbedding.toHomeomorph

theorem simplyConnectedSpace (n k : ℕ) : SimplyConnectedSpace (Space (n + 2) k) := by
  let := JamesSphere.stage_simplyConnected n (k + 1)
  let := JamesSphere.stage_simplyConnected n 1
  let : SimplyConnectedSpace (lower (n + 2) k) :=
    (lowerHomeomorph (n + 2) k).symm.toHomotopyEquiv.simplyConnectedSpace
  let a : lower (n + 2) k := ⟨⟨1, Nat.zero_le (k + 1)⟩, Nat.zero_le 1⟩
  exact CollapsedSubspacePushout.simplyConnectedSpace (lower (n + 2) k) a
    (lower_hasHomotopyExtension (n + 2) k)

theorem range_simplyConnectedSpace (n k : ℕ) :
    SimplyConnectedSpace (Set.range (map (n + 2) k)) := by
  let := simplyConnectedSpace n k
  exact (rangeHomeomorph (n + 2) k).symm.toHomotopyEquiv.simplyConnectedSpace

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.FiniteStage
