import Arxiv.Arxiv2411_18291.ExchangeNearFar

/-!
# The base and independent private pieces of an exchange frame

Near cliques correspond bijectively to the base edges. Their private
vertices form disjoint sets of size `q-r`. Far cliques meet the base in
fewer than `r` vertices, as required when only the base is fixed in the
colour moment argument.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem V q r} {A : Finset (Block V q)}

def IsExchangeFamily.nearRootEquiv (hA : IsExchangeFamily S A) (hr : 0 < r) :
    S.nearCliques ≃ cliqueEdges r S.base :=
  Equiv.ofBijective (fun P => ⟨hA.nearRoot hr P, hA.nearRoot_mem hr P⟩) (by
    constructor
    · intro P Q hPQ
      exact hA.nearRoot_injective hr (congrArg Subtype.val hPQ)
    · rintro ⟨e, he⟩
      obtain ⟨Q, hQ, hQE⟩ := hA.2.2.1 e he
      have hnear : Q ∈ S.nearCliques := mem_filter.mpr
        ⟨mem_union_left _ (hA.1 hQ), by rw [hQE]; exact singleton_nonempty e⟩
      refine ⟨⟨Q, hnear⟩, Subtype.ext ?_⟩
      apply Subtype.ext
      exact vertices_inter_eq_of_cliqueEdges_singleton hr Q S.base e hQE)

theorem IsExchangeFamily.near_card (hA : IsExchangeFamily S A) (hr : 0 < r) :
    S.nearCliques.card = q.choose r := by
  simpa only [Fintype.card_coe, card_cliqueEdges] using Fintype.card_congr (hA.nearRootEquiv hr)

theorem IsExchangeFamily.near_eq (hA : IsExchangeFamily S A) (hr : 0 < r) :
    S.nearCliques = A := by
  apply eq_of_subset_of_card_le (fun Q hQ => (hA.near_root hr hQ).1)
  rw [hA.near_card hr, hA.2.1]

theorem IsExchangeFamily.private_card (hA : IsExchangeFamily S A) (hr : 0 < r)
    {Q : Block V q} (hQ : Q ∈ S.nearCliques) : (Q.val \ S.base.val).card = q - r := by
  rw [card_sdiff, Q.property, inter_comm, hA.near_inter_card hr hQ]

theorem IsExchangeFamily.private_pairwise (hA : IsExchangeFamily S A) (hr : 0 < r) :
    (S.nearCliques : Set (Block V q)).Pairwise
      (fun P Q => Disjoint (P.val \ S.base.val) (Q.val \ S.base.val)) := by
  rw [hA.near_eq hr]
  exact hA.2.2.2.1

def ExchangeSystem.frameVertices (S : ExchangeSystem V q r) : Finset V :=
  S.base.val ∪ S.nearCliques.biUnion Subtype.val

theorem ExchangeSystem.frameVertices_eq_private (S : ExchangeSystem V q r) :
    S.frameVertices = S.base.val ∪ S.nearCliques.biUnion (fun Q => Q.val \ S.base.val) := by
  ext v
  simp only [frameVertices, mem_union, mem_biUnion, mem_sdiff]
  constructor
  · rintro (hb | ⟨Q, hQ, hv⟩)
    · exact Or.inl hb
    · by_cases hb : v ∈ S.base.val
      · exact Or.inl hb
      · exact Or.inr ⟨Q, hQ, hv, hb⟩
  · rintro (hb | ⟨Q, hQ, hv, _⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨Q, hQ, hv⟩

theorem IsExchangeFamily.frame_card (hA : IsExchangeFamily S A) (hr : 0 < r) :
    S.frameVertices.card = q + q.choose r * (q - r) := by
  have hd : Disjoint S.base.val (S.nearCliques.biUnion (fun Q => Q.val \ S.base.val)) := by
    apply disjoint_left.mpr
    intro v hvB hv
    obtain ⟨Q, _, hQ⟩ := mem_biUnion.mp hv
    exact (mem_sdiff.mp hQ).2 hvB
  rw [S.frameVertices_eq_private, card_union_of_disjoint hd, S.base.property,
    card_biUnion (hA.private_pairwise hr)]
  have hs : ∑ Q ∈ S.nearCliques, (Q.val \ S.base.val).card = q.choose r * (q - r) := by
    calc
      _ = ∑ _Q ∈ S.nearCliques, (q - r) := sum_congr rfl (fun Q hQ => hA.private_card hr hQ)
      _ = _ := by rw [sum_const, smul_eq_mul, hA.near_card hr]
  rw [hs]

theorem ExchangeSystem.far_inter_card_lt (S : ExchangeSystem V q r)
    {Q : Block V q} (hQ : Q ∈ S.farCliques) : (Q.val ∩ S.base.val).card < r :=
  clique_inter_card_lt_of_disjoint Q S.base (S.far_disjoint_base hQ)

end Arxiv2411_18291
