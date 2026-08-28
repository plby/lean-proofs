import Wikipedia.NoExoticSixSphere.JamesSphereConeStageInclusion

/-!
# The exact inverse image of the preceding auxiliary cone stage

It consists of shorter tails together with the cone point times all
tails. This identifies the actual subspace needed for the relative
compression argument, not just a homotopy-equivalent replacement.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.ConeStage

def preceding (n k : ℕ) : Set (Space n (k + 1)) := Set.range (step n k)

theorem quotient_mem_preceding_iff (n k : ℕ) (c : ReducedCone.Space n)
    (w : James.stage (spherePole n) (k + 1)) :
    quotientMap n (k + 1) (c, w) ∈ preceding n k ↔
      w.val ∈ James.stage (spherePole n) k ∨ c = ReducedCone.base n := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨⟨d, v⟩, rfl⟩ := (quotientMap_isQuotientMap n k).surjective p
    rw [step_quotientMap] at hp
    rcases (quotient_eq_iff n (k + 1) (d, StageAttachment.inclusion n k v) (c, w)).mp hp with
      he | ⟨a, b, ha, hb, hab⟩
    · left
      have hvw : StageAttachment.inclusion n k v = w := congrArg Prod.snd he
      rw [← hvw]
      exact v.property
    · have hat : a.2 = StageAttachment.inclusion n k v := congrArg Prod.snd ha
      have hbt : b.2 = w := congrArg Prod.snd hb
      have hbc : ReducedCone.boundary n b.1 = c := congrArg Prod.fst hb
      have hshort : a.2.val ∈ James.stage (spherePole n) k := by
        rw [hat]
        exact v.property
      have hsa : (stageAction n (k + 1) a).val ∈ James.stage (spherePole n) (k + 1) :=
        (stageAction_mem_lower_iff n k a.1 a.2).mpr (Or.inl hshort)
      have hsb : (stageAction n (k + 1) b).val ∈ James.stage (spherePole n) (k + 1) := by
        rw [← hab]
        exact hsa
      rcases (stageAction_mem_lower_iff n k b.1 b.2).mp hsb with ht | hx
      · exact Or.inl (hbt ▸ ht)
      · right
        exact hbc.symm.trans ((congrArg (ReducedCone.boundary n) hx).trans
          (ReducedCone.boundary_pole n))
  · rintro (hw | hc)
    · let v : James.stage (spherePole n) k := ⟨w.val, hw⟩
      refine ⟨quotientMap n k (c, v), ?_⟩
      rw [step_quotientMap]
      exact congrArg (fun z ↦ quotientMap n (k + 1) (c, z)) (Subtype.ext rfl)
    · refine ⟨words n k w, ?_⟩
      rw [step_words, hc, quotient_base]

theorem stageInclusion_mem_range (n k : ℕ) (w : James.stage (spherePole n) (k + 1)) :
    w ∈ Set.range (StageAttachment.inclusion n k) ↔ w.val ∈ James.stage (spherePole n) k := by
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro hw
    exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩

theorem preimage_preceding (n k : ℕ) : quotientMap n (k + 1) ⁻¹' preceding n k =
    Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct.boundary
      (MetricPointCofibration.inclusion (ReducedCone.base n)) (StageAttachment.inclusion n k) := by
  ext p
  rw [Set.mem_preimage, quotient_mem_preceding_iff]
  change (_ ∨ _) ↔
    p.1 ∈ Set.range (SubspaceCofibration.inclusion
      ({ReducedCone.base n} : Set (ReducedCone.Space n))) ∨
      p.2 ∈ Set.range (StageAttachment.inclusion n k)
  rw [SubspaceCofibration.mem_range, stageInclusion_mem_range]
  exact or_comm

end NoExoticSixSphere.JamesSphere.ConeStage
