import Wikipedia.NoExoticSixSphere.CompactAdjunction

/-!
# Compactness, Hausdorff separation, and the actual adjunction inclusion

The quotient relation is the union of the diagonal and the compact image
of the attaching-map equality relation. This proves that the adjunction
space is Hausdorff. The target inclusion is continuous and, for a compact
target, a closed embedding. These statements refer to the quotient
topology defined on the actual adjunction set.
-/

noncomputable section

universe u

open Set Topology

namespace NoExoticSixSphere.CompactAdjunction

variable {A X Y : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (D : Data A X Y)

theorem relation_eq : {p : X × X | projection D p.1 = projection D p.2} =
    Set.diagonal X ∪ (Prod.map D.embedding D.embedding) ''
      {p : A × A | D.attaching p.1 = D.attaching p.2} := by
  ext p
  constructor
  · intro hp
    rcases (projection_eq_iff D p.1 p.2).mp hp with he | ⟨a, b, ha, hb, hab⟩
    · exact Or.inl he
    · exact Or.inr ⟨(a, b), hab, Prod.ext ha hb⟩
  · rintro (he | ⟨⟨a, b⟩, hab, hp⟩)
    · exact (projection_eq_iff D p.1 p.2).mpr (Or.inl he)
    · exact (projection_eq_iff D p.1 p.2).mpr
        (Or.inr ⟨a, b, congrArg Prod.fst hp, congrArg Prod.snd hp, hab⟩)

theorem relation_isClosed [CompactSpace A] [T2Space X] [T2Space Y] :
    IsClosed {p : X × X | projection D p.1 = projection D p.2} := by
  rw [relation_eq]
  apply isClosed_diagonal.union
  have hc : IsClosed {p : A × A | D.attaching p.1 = D.attaching p.2} :=
    isClosed_eq (D.attaching.continuous.comp continuous_fst)
      (D.attaching.continuous.comp continuous_snd)
  exact (hc.isCompact.image (D.embedding.continuous.prodMap D.embedding.continuous)).isClosed

instance [CompactSpace X] : CompactSpace (Space D) :=
  (projection_surjective D).compactSpace (projection_isQuotientMap D).continuous

instance [CompactSpace A] [CompactSpace X] [T2Space X] [T2Space Y] : T2Space (Space D) :=
  CompactClosedQuotient.t2Space (projection D) (projection_isQuotientMap D) (relation_isClosed D)

def inclusion [CompactSpace A] [T2Space Y] : C(Y, Space D) := by
  refine ⟨Sum.inr, ?_⟩
  have hf : IsQuotientMap D.attaching :=
    IsQuotientMap.of_surjective_continuous D.attaching_surjective D.attaching.continuous
  apply hf.continuous_iff.mpr
  exact ((projection_isQuotientMap D).continuous.comp D.embedding.continuous).congr
    (projection_embedding D)

theorem inclusion_injective [CompactSpace A] [T2Space Y] : Function.Injective (inclusion D) :=
  Sum.inr_injective

theorem inclusion_isClosedEmbedding [CompactSpace A] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] : IsClosedEmbedding (inclusion D) :=
  (inclusion D).continuous.isClosedEmbedding (inclusion_injective D)

theorem quotientMap_embedding [CompactSpace A] [T2Space Y] (a : A) :
    quotientMap D (D.embedding a) = inclusion D (D.attaching a) :=
  projection_embedding D a

theorem preimage_range_inclusion [CompactSpace A] [T2Space Y] :
    quotientMap D ⁻¹' Set.range (inclusion D) = Set.range D.embedding := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, _⟩ := (projection_eq_inr_iff D x y).mp hy.symm
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨D.attaching a, (quotientMap_embedding D a).symm⟩

end NoExoticSixSphere.CompactAdjunction
