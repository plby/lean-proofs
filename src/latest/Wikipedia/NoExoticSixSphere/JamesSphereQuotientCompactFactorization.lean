import Wikipedia.NoExoticSixSphere.JamesSphereFiniteStageQuotient

/-!
# Compact maps into the full James quotient factor through finite stages

Properness of the actual quotient map makes the preimage of a compact
set compact in the original James space. The proved James finite-stage
factorization then applies. The finite-quotient range homeomorphism
provides a genuine continuous factorization, not merely a set-theoretic lift.
-/

noncomputable section

open Set

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem exists_stage_of_isCompact (n : ℕ) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ k : ℕ, K ⊆ Set.range (FiniteStage.map n k) := by
  obtain ⟨k, hk⟩ := James.exists_stage_of_isCompact (spherePole n)
    ((isProperMap_quotientMap n).isCompact_preimage hK)
  refine ⟨k, ?_⟩
  intro y hy
  obtain ⟨w, rfl⟩ := (CollapsedSubspace.isQuotientMap (James.stage (spherePole n) 1)).surjective y
  rw [FiniteStage.range_map]
  exact ⟨w, James.stage_mono (spherePole n) (Nat.le_succ k) (hk hy), rfl⟩

theorem exists_stage_of_continuous (n : ℕ) {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (f : Y → Space n) (hf : Continuous f) :
    ∃ k : ℕ, ∀ y, f y ∈ Set.range (FiniteStage.map n k) := by
  obtain ⟨k, hk⟩ := exists_stage_of_isCompact n (isCompact_range hf)
  exact ⟨k, fun y ↦ hk (Set.mem_range_self y)⟩

theorem exists_continuous_stage_factorization (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] (f : C(Y, Space n)) :
    ∃ (k : ℕ) (g : C(Y, FiniteStage.Space n k)), ∀ y, FiniteStage.map n k (g y) = f y := by
  obtain ⟨k, hk⟩ := exists_stage_of_continuous n f f.continuous
  let e := FiniteStage.rangeHomeomorph n k
  let g : C(Y, FiniteStage.Space n k) :=
    (e.symm : C(Set.range (FiniteStage.map n k), FiniteStage.Space n k)).comp
      ⟨fun y ↦ ⟨f y, hk y⟩, f.continuous.subtype_mk _⟩
  refine ⟨k, g, ?_⟩
  intro y
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f y, hk y⟩)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
