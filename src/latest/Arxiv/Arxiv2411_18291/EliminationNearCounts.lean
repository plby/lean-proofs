import Arxiv.Arxiv2411_18291.SharpEliminationCounts

/-! # Only a small part of an elimination exchange touches its roots

At most `2*(choose(q,r)-1)` replacement cliques meet either root. This
bound is independent of the total size of the exchange configuration.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def ExchangeSystem.eliminationNear (S : ExchangeSystem V q r) (N : Block V q) :=
  (S.eliminationCliques N).filter fun Q =>
    (cliqueEdges r Q ∩ (cliqueEdges r S.base ∪ cliqueEdges r N)).Nonempty

theorem ExchangeSystem.eliminationNear_subset (S : ExchangeSystem V q r) (N : Block V q) :
    S.eliminationNear N ⊆ S.eliminationCliques N := filter_subset _ _

theorem ExchangeSystem.eliminationNear_card_le (S : ExchangeSystem V q (r + 1))
    {N : Block V q} {e : Block V (r + 1)} (hpair : IsEliminationPair S N e) :
    (S.eliminationNear N).card ≤ 2 * (q.choose (r + 1) - 1) := by
  let R := cliqueEdges (r + 1) S.base ∪ cliqueEdges (r + 1) N
  have heP : e ∈ cliqueEdges (r + 1) S.base :=
    (mem_cliqueEdges _ _).mpr (by rw [← hpair.vertex_inter]; exact inter_subset_left)
  have heR : e ∈ R := mem_union_left _ heP
  have heN : e ∈ cliqueEdges (r + 1) N :=
    (mem_cliqueEdges _ _).mpr (by rw [← hpair.vertex_inter]; exact inter_subset_right)
  have hchoose (Q : ↥(S.eliminationNear N)) :
      ∃ f ∈ R.erase e, f.val ⊆ Q.val.val := by
    obtain ⟨f, hf⟩ := (mem_filter.mp Q.property).2
    have hfe : f ≠ e := by
      intro h
      subst f
      exact S.elimination_avoids_common hpair.negative_mem heP heN
        (mem_filter.mp Q.property).1 (mem_inter.mp hf).1
    exact ⟨f, mem_erase.mpr ⟨hfe, (mem_inter.mp hf).2⟩,
      (mem_cliqueEdges _ _).mp (mem_inter.mp hf).1⟩
  choose f hf hQf using hchoose
  let g : ↥(S.eliminationNear N) → ↥(R.erase e) := fun Q => ⟨f Q, hf Q⟩
  have hinj : Function.Injective g := by
    intro Q T hQT
    have hft : f Q = f T := congrArg Subtype.val hQT
    have hcount := S.elimination_count_le_one_of_root hpair.negative_mem (f Q)
      (mem_erase.mp (hf Q)).2
    apply Subtype.ext
    apply card_le_one.mp hcount
    · exact mem_filter.mpr ⟨(mem_filter.mp Q.property).1, hQf Q⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp T.property).1, hft ▸ hQf T⟩
  have hcard : (S.eliminationNear N).card ≤ (R.erase e).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hinj
  have hinter : cliqueEdges (r + 1) S.base ∩ cliqueEdges (r + 1) N = {e} :=
    cliqueEdges_inter_singleton_of_vertices _ _ e hpair.vertex_inter
  have hroot := card_union_add_card_inter
    (cliqueEdges (r + 1) S.base) (cliqueEdges (r + 1) N)
  rw [hinter, card_singleton, card_cliqueEdges, card_cliqueEdges] at hroot
  have herase := card_erase_of_mem heR
  change R.card + 1 = q.choose (r + 1) + q.choose (r + 1) at hroot
  omega

theorem ExchangeSystem.eliminationNear_support_card_le (S : ExchangeSystem V q (r + 1))
    {N : Block V q} {e : Block V (r + 1)} (hpair : IsEliminationPair S N e) :
    (cliqueSupport (r + 1) (S.eliminationNear N)).card ≤
      2 * (q.choose (r + 1) - 1) * q.choose (r + 1) := by
  calc
    _ ≤ ∑ Q ∈ S.eliminationNear N, (cliqueEdges (r + 1) Q).card := card_biUnion_le
    _ = (S.eliminationNear N).card * q.choose (r + 1) := by
      simp only [card_cliqueEdges, sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (S.eliminationNear_card_le hpair)

theorem ExchangeSystem.eliminationNear_support_subset (S : ExchangeSystem V q r)
    (N : Block V q) : cliqueSupport r (S.eliminationNear N) ⊆ S.graph := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  exact S.elimination_clique_subset N (S.eliminationNear_subset N hQ) heQ

theorem ExchangeSystem.eliminationNear_newEdges_card_le (S : ExchangeSystem V q (r + 1))
    {N : Block V q} {e : Block V (r + 1)} (hpair : IsEliminationPair S N e) :
    (newEdges (S.base.val ∪ N.val) (cliqueSupport (r + 1) (S.eliminationNear N))).card ≤
      2 * (q.choose (r + 1) - 1) ^ 2 := by
  have hpiece (Q : Block V q) (hQ : Q ∈ S.eliminationNear N) :
      (newEdges (S.base.val ∪ N.val) (cliqueEdges (r + 1) Q)).card ≤
        q.choose (r + 1) - 1 := by
    obtain ⟨f, hf⟩ := (mem_filter.mp hQ).2
    have hfF : f.val ⊆ S.base.val ∪ N.val := by
      rcases mem_union.mp (mem_inter.mp hf).2 with hp | hn
      · exact ((mem_cliqueEdges _ _).mp hp).trans subset_union_left
      · exact ((mem_cliqueEdges _ _).mp hn).trans subset_union_right
    have hsub : newEdges (S.base.val ∪ N.val) (cliqueEdges (r + 1) Q) ⊆
        (cliqueEdges (r + 1) Q).erase f := by
      intro g hg
      refine mem_erase.mpr ⟨?_, (mem_filter.mp hg).1⟩
      intro hgf
      subst g
      exact (mem_filter.mp hg).2 hfF
    calc
      _ ≤ ((cliqueEdges (r + 1) Q).erase f).card := card_le_card hsub
      _ = _ := by rw [card_erase_of_mem (mem_inter.mp hf).1, card_cliqueEdges]
  have hsplit : newEdges (S.base.val ∪ N.val)
      (cliqueSupport (r + 1) (S.eliminationNear N)) =
      (S.eliminationNear N).biUnion fun Q =>
        newEdges (S.base.val ∪ N.val) (cliqueEdges (r + 1) Q) := by
    simp only [cliqueSupport, newEdges, filter_biUnion]
  rw [hsplit]
  calc
    _ ≤ ∑ Q ∈ S.eliminationNear N,
        (newEdges (S.base.val ∪ N.val) (cliqueEdges (r + 1) Q)).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ S.eliminationNear N, (q.choose (r + 1) - 1) := sum_le_sum hpiece
    _ = (S.eliminationNear N).card * (q.choose (r + 1) - 1) := by
      simp only [sum_const, smul_eq_mul]
    _ ≤ (2 * (q.choose (r + 1) - 1)) * (q.choose (r + 1) - 1) :=
      Nat.mul_le_mul_right _ (S.eliminationNear_card_le hpair)
    _ = _ := by ring

end Arxiv2411_18291
