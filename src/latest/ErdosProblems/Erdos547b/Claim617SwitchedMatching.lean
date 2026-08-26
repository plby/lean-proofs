/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617DistinctSwitch

/-! The genuine switched matching and its exact freed-partner set. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable {M : R.Subgraph} {L S W : Finset K} {m : ℕ}
variable (D : DistinctSwitch M L S W m)

def sourceSet : Finset K := Finset.univ.image D.source
def targetSet : Finset K := Finset.univ.image D.target
def partnerSet : Finset K := Finset.univ.image D.partner

theorem partnerSet_card (hM : M.IsMatching) : D.partnerSet.card = m := by
  rw [partnerSet, Finset.card_image_of_injective _ (D.partner_injective hM),
    Finset.card_univ, Fintype.card_coe, D.card_edges]

theorem partnerSet_subset_large (hM : M.IsMatching) (hS : S ⊆ sourceS1 M L) :
    D.partnerSet ⊆ L := by
  rintro x hx
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  exact D.partner_mem_large hM hS e

theorem source_mem_support (e : {e // e ∈ D.edges}) : D.source e ∈ matchingSupport M :=
  (mem_matchingSupport M _).mpr (D.source_partner_adj e).fst_mem

theorem partner_mem_support (e : {e // e ∈ D.edges}) : D.partner e ∈ matchingSupport M :=
  (mem_matchingSupport M _).mpr (D.source_partner_adj e).snd_mem

theorem source_ne_target (hW : Disjoint W (matchingSupport M))
    (e f : {e // e ∈ D.edges}) : D.source e ≠ D.target f := by
  intro h
  exact Finset.disjoint_left.mp hW (D.target_mem f) (h ▸ D.source_mem_support e)

theorem partner_ne_target (hW : Disjoint W (matchingSupport M))
    (e f : {e // e ∈ D.edges}) : D.partner e ≠ D.target f := by
  intro h
  exact Finset.disjoint_left.mp hW (D.target_mem f) (h ▸ D.partner_mem_support e)

def newMatching : R.Subgraph where
  verts := Set.range D.source ∪ Set.range D.target
  Adj x y := ∃ e, (x = D.source e ∧ y = D.target e) ∨
    (x = D.target e ∧ y = D.source e)
  adj_sub := by
    rintro x y ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact D.adjacent e
    · exact (D.adjacent e).symm
  edge_vert := by
    rintro x y ⟨e, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩
    · exact Or.inl ⟨e, rfl⟩
    · exact Or.inr ⟨e, rfl⟩
  symm := ⟨by
    rintro x y ⟨e, ⟨hxs, hyt⟩ | ⟨hxt, hys⟩⟩
    · exact ⟨e, Or.inr ⟨hyt, hxs⟩⟩
    · exact ⟨e, Or.inl ⟨hys, hxt⟩⟩⟩

theorem newMatching_isMatching (hM : M.IsMatching)
    (hW : Disjoint W (matchingSupport M)) : D.newMatching.IsMatching := by
  intro x hx
  rcases hx with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨D.target e, ⟨e, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro y ⟨f, ⟨hs, ht⟩ | ⟨ht, hs⟩⟩
    · have hef := D.source_injective hM hs
      subst f
      exact ht
    · exact False.elim (D.source_ne_target hW e f ht)
  · refine ⟨D.source e, ⟨e, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro y ⟨f, ⟨hs, ht⟩ | ⟨ht, hs⟩⟩
    · exact False.elim (D.source_ne_target hW f e hs.symm)
    · have hef := D.target_injective ht
      subst f
      exact hs

def remainder : R.Subgraph :=
  edgeFinsetSubgraph M L (allMatchingEdges M \ D.edges)

theorem remainder_isMatching (hM : M.IsMatching) : D.remainder.IsMatching :=
  edgeFinsetSubgraph_isMatching M hM L _

theorem remainder_subset_support : matchingSupport D.remainder ⊆ matchingSupport M := by
  intro x hx
  obtain ⟨e, _, h | h⟩ := (mem_matchingSupport _ x).mp hx
  · rw [h]
    exact (mem_matchingSupport M _).mpr (orientedEndpoint_adj M L e).fst_mem
  · rw [h]
    exact (mem_matchingSupport M _).mpr (orientedEndpoint_adj M L e).snd_mem

private theorem edge_eq_of_endpoint_eq (hM : M.IsMatching) (e f : MatchingEdge M)
    (c d : Fin 2) (h : orientedEndpoint M L e c = orientedEndpoint M L f d) : e = f := by
  have hpair : (e, c) = (f, d) := orientedEndpoint_injective M hM L h
  exact congrArg Prod.fst hpair

theorem endpoint_not_mem_remainder (hM : M.IsMatching) (e : {e // e ∈ D.edges}) (c : Fin 2) :
    orientedEndpoint M L e.1 c ∉ matchingSupport D.remainder := by
  intro hx
  obtain ⟨f, hf, h | h⟩ := (mem_matchingSupport _ _).mp hx
  · have he := edge_eq_of_endpoint_eq hM e.1 f c 0 h
    exact (Finset.mem_sdiff.mp hf).2 (he ▸ e.2)
  · have he := edge_eq_of_endpoint_eq hM e.1 f c 1 h
    exact (Finset.mem_sdiff.mp hf).2 (he ▸ e.2)

theorem remainder_disjoint_newMatching (hM : M.IsMatching)
    (hW : Disjoint W (matchingSupport M)) :
    Disjoint D.remainder.verts D.newMatching.verts := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hx' := (mem_matchingSupport D.remainder x).mpr hx
  rcases hy with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact D.endpoint_not_mem_remainder hM e (D.side e) hx'
  · exact Finset.disjoint_left.mp hW (D.target_mem e) (D.remainder_subset_support hx')

def switched : R.Subgraph := D.remainder ⊔ D.newMatching

theorem switched_isMatching (hM : M.IsMatching)
    (hW : Disjoint W (matchingSupport M)) : D.switched.IsMatching := by
  have hr := D.remainder_isMatching hM
  have hn := D.newMatching_isMatching hM hW
  apply hr.sup hn
  rw [hr.support_eq_verts, hn.support_eq_verts]
  exact D.remainder_disjoint_newMatching hM hW

theorem switched_support : matchingSupport D.switched =
    matchingSupport D.remainder ∪ D.sourceSet ∪ D.targetSet := by
  ext x
  simp only [mem_matchingSupport, switched, Subgraph.verts_sup, Set.mem_union,
    newMatching, Set.mem_range, sourceSet, targetSet, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and, or_assoc]

theorem partnerSet_disjoint_switched (hM : M.IsMatching)
    (hW : Disjoint W (matchingSupport M)) :
    Disjoint D.partnerSet (matchingSupport D.switched) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  rw [D.switched_support] at hy
  rcases Finset.mem_union.mp hy with hy | hy
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact D.endpoint_not_mem_remainder hM e _ hy
    · obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hy
      exact D.source_ne_partner hM f e hf
  · obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hy
    exact D.partner_ne_target hW e f hf.symm

theorem endpoint_eq_source_or_partner (e : {e // e ∈ D.edges}) (c : Fin 2) :
    orientedEndpoint M L e.1 c = D.source e ∨ orientedEndpoint M L e.1 c = D.partner e := by
  unfold source partner
  generalize D.side e = d
  fin_cases d <;> fin_cases c <;> simp

/-- Every lost old vertex is one of the literal freed partners. -/
theorem original_support_subset (hM : M.IsMatching) : matchingSupport M ⊆
    matchingSupport D.switched ∪ D.partnerSet := by
  intro x hx
  rw [support_partition M hM L D.edges] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨e, he, h | h⟩ := (mem_matchingSupport _ x).mp hx
    · rcases D.endpoint_eq_source_or_partner ⟨e, he⟩ 0 with hs | hp
      · apply Finset.mem_union_left
        rw [D.switched_support]
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, (h.trans hs).symm⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨e, he⟩, Finset.mem_univ _, (h.trans hp).symm⟩)
    · rcases D.endpoint_eq_source_or_partner ⟨e, he⟩ 1 with hs | hp
      · apply Finset.mem_union_left
        rw [D.switched_support]
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, (h.trans hs).symm⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨e, he⟩, Finset.mem_univ _, (h.trans hp).symm⟩)
  · apply Finset.mem_union_left
    rw [D.switched_support]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem switched_support_subset : matchingSupport D.switched ⊆ matchingSupport M ∪ W := by
  intro x hx
  rw [D.switched_support] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (D.remainder_subset_support hx)
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_union_left _ (D.source_mem_support e)
  · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_union_right _ (D.target_mem e)

theorem switched_disjoint_of_disjoint (B : Finset K)
    (hM : Disjoint (matchingSupport M) B) (hW : Disjoint W B) :
    Disjoint (matchingSupport D.switched) B :=
  Finset.disjoint_of_subset_left D.switched_support_subset (Finset.disjoint_union_left.mpr ⟨hM, hW⟩)

theorem weight_loss (hM : M.IsMatching) (hW : Disjoint W (matchingSupport M))
    (w : K → ℝ) (cap : ℝ) (hw : ∀ x, 0 ≤ w x) (hcap : ∀ x ∈ D.partnerSet, w x ≤ cap) :
    (∑ x ∈ matchingSupport M, w x) ≤
      (∑ x ∈ matchingSupport D.switched, w x) + (m : ℝ) * cap := by
  calc
    ∑ x ∈ matchingSupport M, w x ≤
        ∑ x ∈ matchingSupport D.switched ∪ D.partnerSet, w x :=
      Finset.sum_le_sum_of_subset_of_nonneg (D.original_support_subset hM) (fun x _ _ => hw x)
    _ = (∑ x ∈ matchingSupport D.switched, w x) + ∑ x ∈ D.partnerSet, w x :=
      Finset.sum_union (D.partnerSet_disjoint_switched hM hW).symm
    _ ≤ (∑ x ∈ matchingSupport D.switched, w x) + (m : ℝ) * cap := by
      apply add_le_add le_rfl
      calc
        ∑ x ∈ D.partnerSet, w x ≤ ∑ _x ∈ D.partnerSet, cap := Finset.sum_le_sum hcap
        _ = (m : ℝ) * cap := by simp only [Finset.sum_const, nsmul_eq_mul, D.partnerSet_card hM]

end Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch

#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch.switched_isMatching
#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch.partnerSet_disjoint_switched
#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch.original_support_subset
#print axioms Erdos547b.ZhaoClaim617DistinctSwitch.DistinctSwitch.weight_loss
