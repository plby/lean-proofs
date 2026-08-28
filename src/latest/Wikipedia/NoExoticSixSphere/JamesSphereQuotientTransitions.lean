import Wikipedia.NoExoticSixSphere.JamesSphereFiniteStageQuotient

/-!
# The original transition maps between finite James quotients

Word-stage inclusion descends through the first-stage collapse relation.
The transitions are closed embeddings, compose exactly, and retain the
literal maps into the full quotient. Their image is characterized by
the reduced-word length of any original representative.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.FiniteStage

open FirstStageCofibration

instance (n k : ℕ) : T2Space (Space n k) :=
  T2Space.of_injective_continuous (map_injective n k) (map n k).continuous

def transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) : C(Space n k, Space n l) :=
  CollapsedSubspace.lift (lower n k)
    ((quotientMap n l).comp (ContinuousMap.inclusion
      (James.stage_mono (spherePole n) (Nat.succ_le_succ hkl))))
    (fun w hw z hz ↦ (CollapsedSubspace.quotientMap_eq_iff (lower n l) _ _).mpr
      (Or.inr ⟨hw, hz⟩))

theorem transition_quotientMap (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (w : Words n k) :
    transition n hkl (quotientMap n k w) =
      quotientMap n l ⟨w.val, James.stage_mono (spherePole n) (Nat.succ_le_succ hkl)
        w.property⟩ := rfl

theorem map_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (map n l).comp (transition n hkl) = map n k := by
  apply ContinuousMap.ext
  intro a
  exact Quotient.inductionOn a (fun _ ↦ rfl)

theorem transition_refl (n k : ℕ) : transition n (le_refl k) = ContinuousMap.id (Space n k) := by
  apply ContinuousMap.ext
  intro a
  exact Quotient.inductionOn a (fun _ ↦ rfl)

theorem transition_trans (n : ℕ) {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (transition n hlm).comp (transition n hkl) = transition n (hkl.trans hlm) := by
  apply ContinuousMap.ext
  intro a
  exact Quotient.inductionOn a (fun _ ↦ rfl)

theorem transition_injective (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    Function.Injective (transition n hkl) := by
  intro a b h
  apply map_injective n k
  have he := congrArg (map n l) h
  change ((map n l).comp (transition n hkl)) a =
    ((map n l).comp (transition n hkl)) b at he
  rwa [map_transition] at he

theorem isClosedEmbedding_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    IsClosedEmbedding (transition n hkl) :=
  (transition n hkl).continuous.isClosedEmbedding (transition_injective n hkl)

theorem quotientMap_mem_range_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (w : Words n l) :
    quotientMap n l w ∈ Set.range (transition n hkl) ↔
      w.val ∈ James.stage (spherePole n) (k + 1) := by
  constructor
  · rintro ⟨a, ha⟩
    revert ha
    refine Quotient.inductionOn a fun v hv ↦ ?_
    change transition n hkl (quotientMap n k v) = quotientMap n l w at hv
    rw [transition_quotientMap] at hv
    rcases (CollapsedSubspace.quotientMap_eq_iff (lower n l) _ w).mp hv with he | ⟨_, hw⟩
    · exact (congrArg Subtype.val he) ▸ v.property
    · exact James.stage_mono (spherePole n) (Nat.succ_le_succ (Nat.zero_le k)) hw
  · intro hw
    exact ⟨quotientMap n k ⟨w.val, hw⟩, rfl⟩

theorem range_mono (n : ℕ) : Monotone (fun k ↦ Set.range (map n k)) := by
  intro k l hkl
  change Set.range (map n k) ⊆ Set.range (map n l)
  rw [range_map, range_map]
  exact Set.image_mono (James.stage_mono (spherePole n) (Nat.succ_le_succ hkl))

def transitionRangeHomeomorph (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    Space n k ≃ₜ Set.range (transition n hkl) :=
  (isClosedEmbedding_transition n hkl).isEmbedding.toHomeomorph

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.FiniteStage
