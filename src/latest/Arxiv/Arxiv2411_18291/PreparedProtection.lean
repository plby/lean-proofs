import Arxiv.Arxiv2411_18291.PreparedGluing
import Arxiv.Arxiv2411_18291.PreparedInsert

/-!
# Protecting positive cliques through the exchange construction

The prepared regions also control the positive decomposition. Carry this
additional locality invariant through both attachments and insertion, so
a positive clique can meet the prepared frame only inside the base or
one distinguished negative clique. This works also for uniformity one.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291.PreparedFamily

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q r : ℕ} {I : Type*}
variable {G : Hypergraph V r} {D K : Finset (Block V q)} {B : Block V q}
variable {s : Finset I} {edge : I → Block V r}

def Protects (P : PreparedFamily G D B s edge) (K : Finset (Block V q)) : Prop :=
  ∀ i ∈ s, ∀ Q ∈ K, ¬Disjoint Q.val ((P.clique i).val \ B.val) → Q.val ⊆ P.region i

theorem Protects.mono {P : PreparedFamily G D B s edge} (hP : P.Protects K)
    {K' : Finset (Block V q)} (hK : K' ⊆ K) : P.Protects K' :=
  fun i hi Q hQ => hP i hi Q (hK hQ)

theorem empty_protects (G : Hypergraph V r) (D K : Finset (Block V q))
    (B : Block V q) (edge : I → Block V r) : (empty G D B edge).Protects K := by
  intro i hi
  exact (notMem_empty i hi).elim

theorem Protects.map {P : PreparedFamily G D B s edge} (hP : P.Protects K) (f : V ↪ W) :
    (P.map f).Protects (mapGraph f K) := by
  intro i hi Q hQ hcontact
  obtain ⟨R, hR, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
  change ¬Disjoint (R.val.map f) ((P.clique i).val.map f \ B.val.map f) at hcontact
  rw [← map_sdiff, disjoint_map] at hcontact
  exact map_subset_map.mpr (hP i hi R hR hcontact)

theorem Protects.glue {P : PreparedFamily G D B s edge} (hP : P.Protects K) (hqr : r < q)
    (C : Block V q) (Q : Block W q) (σ : Q.val ≃ C.val)
    (H : Hypergraph W r) (N K' : Finset (Block W q))
    (havoid : ∀ i ∈ s, Disjoint C.val ((P.clique i).val \ B.val)) :
    (P.glue hqr C Q σ H N havoid).Protects
      (mapGraph (glueLeft Q.val) K ∪ (mapGraph (glueRight C Q σ) K').erase
        (mapBlock (glueLeft Q.val) C)) := by
  intro i hi R hR hcontact
  rcases mem_union.mp hR with hR | hR
  · exact hP.map (glueLeft Q.val) i hi R hR hcontact
  · obtain ⟨A, _, rfl⟩ := (mem_mapGraph _ _ _).mp (mem_erase.mp hR).2
    apply (hcontact ?_).elim
    change Disjoint (A.val.map (glueRight C Q σ))
      ((P.clique i).val.map (glueLeft Q.val) \ B.val.map (glueLeft Q.val))
    rw [← map_sdiff]
    exact glue_right_disjoint_left C Q σ A.val _ (havoid i hi)

theorem Protects.insert_fresh [DecidableEq I] {P : PreparedFamily G D B s edge}
    (hP : P.Protects K) (j : I) (hj : j ∉ s) (N : Block V q) (R U : Finset V)
    (hN : N ∈ D) (heN : (edge j).val ⊆ N.val) (hNR : N.val ⊆ R)
    (hRB : R ∩ B.val = (edge j).val) (hregions : ∀ i ∈ s, P.region i ⊆ U)
    (hfresh : R ∩ U ⊆ B.val)
    (hlocalE : ∀ e ∈ G, ¬Disjoint e.val (N.val \ B.val) → e.val ⊆ R)
    (hlocalD : ∀ Q ∈ D, ¬Disjoint Q.val (N.val \ B.val) → Q.val ⊆ R)
    (hlocalK : ∀ Q ∈ K, ¬Disjoint Q.val (N.val \ B.val) → Q.val ⊆ R) :
    (P.insert_fresh j hj N R U hN heN hNR hRB hregions hfresh hlocalE hlocalD).Protects K := by
  intro i hi
  change ∀ Q ∈ K, ¬Disjoint Q.val ((Function.update P.clique j N i).val \ B.val) →
    Q.val ⊆ Function.update P.region j R i
  rcases mem_insert.mp hi with rfl | hi
  · simpa only [Function.update_self] using hlocalK
  · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)] using
      hP i hi

theorem Protects.frame_local {P : PreparedFamily G D B s edge} (hP : P.Protects K)
    {Q : Block V q} (hQ : Q ∈ K) :
    Q.val ∩ P.frame ⊆ B.val ∨ ∃ i ∈ s, Q.val ∩ P.frame ⊆ (P.clique i).val := by
  by_cases h : Q.val ∩ P.frame ⊆ B.val
  · exact Or.inl h
  obtain ⟨v, hv, hvB⟩ := not_subset.mp h
  obtain ⟨hvQ, hvF⟩ := mem_inter.mp hv
  obtain ⟨i, hi, hvN⟩ := mem_biUnion.mp ((mem_union.mp hvF).resolve_left hvB)
  have hcontact : ¬Disjoint Q.val ((P.clique i).val \ B.val) := by
    intro hd
    exact disjoint_left.mp hd hvQ (mem_sdiff.mpr ⟨hvN, hvB⟩)
  have hQR := hP i hi Q hQ hcontact
  refine Or.inr ⟨i, hi, ?_⟩
  intro x hx
  exact P.region_inter_frame_subset hi
    (mem_inter.mpr ⟨hQR (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩)

end Arxiv2411_18291.PreparedFamily
