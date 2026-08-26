import Mathlib
import ErdosProblems.Erdos550.Centroid
import ErdosProblems.Erdos550.TauFineAttachments

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Promoting branch vertices of a seed set

Auxiliary tree theory for strengthening a τ-fine separator.  A direction from
`v` is seed-bearing when the branch through the corresponding neighbour
contains an original seed.  Vertices with at least three such directions are
promoted to seeds.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Every other vertex of a finite tree lies in a unique neighbour direction
from a given vertex. -/
lemma existsUnique_mem_branch (T : SimpleGraph α) (hT : T.IsTree)
    (v x : α) (hx : x ≠ v) :
    ∃! u, T.Adj v u ∧ x ∈ branch T v u := by
  obtain ⟨p, hp⟩ : ∃ p : T.Walk v x, p.length = T.dist v x :=
    SimpleGraph.Reachable.exists_walk_length_eq_dist (hT.1 v x)
  have hpath : p.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist p hp
  have hlen : 0 < p.length := by
    rw [hp]
    have hr : T.Reachable v x := hT.1 v x
    have hz : T.dist v x ≠ 0 := by
      intro hz
      rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hz with h | h
      · exact hx h.symm
      · exact h hr
    omega
  let u := p.getVert 1
  have hadj : T.Adj v u := by
    have h := p.adj_getVert_succ (show 0 < p.length by exact hlen)
    simpa [u] using! h
  have hu : x ∈ branch T v u := by
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
    have htail : T.dist x u ≤ p.tail.length := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_le (p.tail.copy (by simp [u]) rfl)
    have htail_len : p.tail.length + 1 = p.length := p.length_tail_add_one (by
      intro hn
      have := SimpleGraph.Walk.nil_iff_length_eq.mp hn
      omega)
    have hlt : T.dist x u < T.dist x v := by
      have hp' : p.length = T.dist x v := by simpa [SimpleGraph.dist_comm] using! hp
      rw [← hp']
      omega
    simpa [SimpleGraph.dist_comm] using! hlt
  refine ⟨u, ⟨hadj, hu⟩, ?_⟩
  intro w hw
  by_contra hwu
  have hsub : branch T v w ⊂ branch T u v :=
    branch_ssubset hT hadj.symm hw.1 hwu
  have hxuv : x ∈ branch T u v := hsub.1 hw.2
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hu hxuv
  omega

/-- Neighbour directions from `v` whose branch contains an original seed. -/
noncomputable def seedDirections (T : SimpleGraph α) (S₀ : Finset α) (v : α) : Finset α :=
  T.neighborFinset v |>.filter fun u => ∃ s ∈ S₀, s ∈ branch T v u

/-- Branch vertices of the subtree spanned by `S₀`, described intrinsically by
having at least three seed-bearing directions. -/
noncomputable def promotedBranchVertices
    (T : SimpleGraph α) (S₀ : Finset α) : Finset α :=
  Finset.univ.filter fun v => 3 ≤ (seedDirections T S₀ v).card

lemma originalSeedNeighbors_subset_seedDirections
    (T : SimpleGraph α) (S₀ : Finset α) (v : α) :
    S₀.filter (T.Adj v) ⊆ seedDirections T S₀ v := by
  intro s hs
  simp only [Finset.mem_filter] at hs
  simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  refine ⟨hs.2, s, hs.1, ?_⟩
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
  have hdist : T.dist s v = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hs.2.symm
  simp [hdist]

lemma three_original_seed_neighbors_promoted
    (T : SimpleGraph α) (S₀ : Finset α) (v : α)
    (hthree : 3 ≤ (S₀.filter (T.Adj v)).card) :
    v ∈ promotedBranchVertices T S₀ := by
  simp only [promotedBranchVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hthree.trans (Finset.card_le_card
    (originalSeedNeighbors_subset_seedDirections T S₀ v))

lemma enlargedSeed_attachment_bears_originalSeed
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    {s v : α} (hs : s ∈ S₀ ∪ promotedBranchVertices T S₀)
    (hsv : T.Adj s v) :
    ∃ t ∈ S₀, t ∈ branch T v s := by
  rcases Finset.mem_union.mp hs with hs₀ | hsB
  · refine ⟨s, hs₀, ?_⟩
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdist : T.dist s v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hsv
    simp [hdist]
  · have hcard : 3 ≤ (seedDirections T S₀ s).card := by
      simpa [promotedBranchVertices] using! hsB
    have hmore : 1 < (seedDirections T S₀ s).card := by omega
    obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne hmore v
    simp only [seedDirections, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset] at hu
    rcases hu with ⟨hsu, t, htS, htbranch⟩
    refine ⟨t, htS, ?_⟩
    exact (branch_ssubset hT hsv.symm hsu huv).1 htbranch

lemma enlargedSeed_mem_seedDirections_of_adj
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    {s v : α} (hs : s ∈ S₀ ∪ promotedBranchVertices T S₀)
    (hsv : T.Adj s v) :
    s ∈ seedDirections T S₀ v := by
  simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  refine ⟨hsv.symm, ?_⟩
  exact enlargedSeed_attachment_bears_originalSeed T hT S₀ hs hsv

lemma enlargedSeedNeighbors_subset_seedDirections
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    (v : α) :
    (S₀ ∪ promotedBranchVertices T S₀).filter (T.Adj v) ⊆
      seedDirections T S₀ v := by
  intro s hs
  simp only [Finset.mem_filter] at hs
  exact enlargedSeed_mem_seedDirections_of_adj T hT S₀ hs.1 hs.2.symm

lemma three_enlarged_seed_neighbors_promoted
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    (v : α)
    (hthree : 3 ≤ ((S₀ ∪ promotedBranchVertices T S₀).filter
      (T.Adj v)).card) :
    v ∈ promotedBranchVertices T S₀ := by
  simp only [promotedBranchVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hthree.trans (Finset.card_le_card
    (enlargedSeedNeighbors_subset_seedDirections T hT S₀ v))

lemma nonpromoted_enlargedSeedNeighbors_card_le_two
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    {v : α} (hv : v ∉ S₀ ∪ promotedBranchVertices T S₀) :
    ((S₀ ∪ promotedBranchVertices T S₀).filter (T.Adj v)).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ ((S₀ ∪ promotedBranchVertices T S₀).filter
      (T.Adj v)).card := by omega
  have hvB := three_enlarged_seed_neighbors_promoted T hT S₀ v hthree
  exact hv (Finset.mem_union_right S₀ hvB)

lemma componentSeeds_card_le_two_of_common_neighbor
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    (c : (seedDeleted T (S₀ ∪ promotedBranchVertices T S₀)).ConnectedComponent)
    {v : α} (hv : v ∉ S₀ ∪ promotedBranchVertices T S₀)
    (hcommon : ∀ s ∈ componentSeeds
      T (S₀ ∪ promotedBranchVertices T S₀) c, T.Adj v s) :
    (componentSeeds T (S₀ ∪ promotedBranchVertices T S₀) c).card ≤ 2 := by
  have hsub : componentSeeds T (S₀ ∪ promotedBranchVertices T S₀) c ⊆
      (S₀ ∪ promotedBranchVertices T S₀).filter (T.Adj v) := by
    intro s hs
    exact Finset.mem_filter.mpr
      ⟨componentSeeds_subset T (S₀ ∪ promotedBranchVertices T S₀) c hs,
        hcommon s hs⟩
  exact (Finset.card_le_card hsub).trans
    (nonpromoted_enlargedSeedNeighbors_card_le_two T hT S₀ hv)

lemma component_attachment_bears_originalSeed
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    (c : (seedDeleted T (S₀ ∪ promotedBranchVertices T S₀)).ConnectedComponent)
    {s v : α} (hs : s ∈ componentSeeds
      T (S₀ ∪ promotedBranchVertices T S₀) c)
    (hsv : T.Adj s v) :
    ∃ t ∈ S₀, t ∈ branch T v s := by
  have hs' : s ∈ S₀ ∪ promotedBranchVertices T S₀ :=
    (mem_componentSeeds_iff T _ c s).mp hs |>.1
  exact enlargedSeed_attachment_bears_originalSeed T hT S₀ hs' hsv

/-- The edge core spanned by `S₀`: an edge is retained exactly when there is
an original seed on both sides of it. -/
noncomputable def seedCore (T : SimpleGraph α) (S₀ : Finset α) : SimpleGraph α where
  Adj a b := T.Adj a b ∧
    (∃ s ∈ S₀, s ∈ branch T a b) ∧ (∃ s ∈ S₀, s ∈ branch T b a)
  symm := by
    constructor
    intro a b h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro a h
    exact h.1.ne rfl

lemma seedCore_le (T : SimpleGraph α) (S₀ : Finset α) : seedCore T S₀ ≤ T := by
  intro a b h
  exact h.1

lemma seedCore_neighbor_subset_seedDirections
    (T : SimpleGraph α) [DecidableRel T.Adj] (S₀ : Finset α) (v : α) :
    (seedCore T S₀).neighborFinset v ⊆ seedDirections T S₀ v := by
  intro u hu
  simp only [SimpleGraph.mem_neighborFinset] at hu
  simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨hu.1, hu.2.1⟩

lemma seedCore_degree_three_promoted
    (T : SimpleGraph α) [DecidableRel T.Adj] (S₀ : Finset α)
    {v : α} (hv : 3 ≤ (seedCore T S₀).degree v) :
    v ∈ promotedBranchVertices T S₀ := by
  simp only [promotedBranchVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hv
  exact hv.trans (Finset.card_le_card
    (seedCore_neighbor_subset_seedDirections T S₀ v))

lemma promoted_degree_seedCore
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    {v : α} (hv : v ∈ promotedBranchVertices T S₀) :
    3 ≤ (seedCore T S₀).degree v := by
  have hthree : 3 ≤ (seedDirections T S₀ v).card := by
    simpa [promotedBranchVertices] using! hv
  have hsub : seedDirections T S₀ v ⊆ (seedCore T S₀).neighborFinset v := by
    intro u hu
    simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
    rcases hu with ⟨hvu, s, hsS, hsbr⟩
    have hex : ∃ w ∈ seedDirections T S₀ v, w ≠ u := by
      by_contra hn
      push_neg at hn
      have : seedDirections T S₀ v ⊆ {u} := fun w hw => by simpa [hn w hw]
      have hc := Finset.card_le_card this
      simp at hc
      omega
    obtain ⟨w, hw, hwu⟩ := hex
    simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
    rcases hw with ⟨hvw, t, htS, htbr⟩
    have htopp : t ∈ branch T u v :=
      (branch_ssubset hT hvu.symm hvw hwu).1 htbr
    simp only [seedCore, SimpleGraph.mem_neighborFinset]
    exact ⟨hvu, ⟨s, hsS, hsbr⟩, ⟨t, htS, htopp⟩⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact hthree.trans (Finset.card_le_card hsub)

/-- Degree-sum counting in a forest-shaped graph: if the number of edges is
strictly smaller than the number of active vertices and all leaves belong to
`S`, then the vertices of degree at least three are no more numerous than `S`.
This deliberately weak form avoids subtraction edge cases. -/
lemma highDegree_card_le_of_edges_lt_active
    (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α)
    (hedges : G.edgeFinset.card < (Finset.univ.filter fun v => 0 < G.degree v).card)
    (hleaf : ∀ v, G.degree v = 1 → v ∈ S) :
    (Finset.univ.filter fun v => 3 ≤ G.degree v).card ≤ S.card := by
  let A := Finset.univ.filter fun v => 0 < G.degree v
  let B := Finset.univ.filter fun v => 3 ≤ G.degree v
  let L := Finset.univ.filter fun v => G.degree v = 1
  have hLsub : L ⊆ S := by
    intro v hv
    exact hleaf v (by simpa [L] using! hv)
  have hsum : (∑ v ∈ A, G.degree v) = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_subset (by simp [A])
    intro v _ hv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    omega
  have hpoint : ∀ v ∈ A, 2 + (if v ∈ B then 1 else 0) ≤ G.degree v + (if v ∈ L then 1 else 0) := by
    intro v hv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [B, L, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  have hsumineq := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole, Finset.filter_mem_eq_inter] at hsumineq
  have hBA : B ⊆ A := by
    intro v hv
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    omega
  have hLA : L ⊆ A := by
    intro v hv
    simp only [L, A, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    omega
  have hiB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
  have hiL : A ∩ L = L := Finset.inter_eq_right.mpr hLA
  rw [hiB, hiL, hsum] at hsumineq
  have hedges' : G.edgeFinset.card < A.card := by simpa [A] using! hedges
  have hAcard : A.card ≥ G.edgeFinset.card + 1 := by omega
  have hineq : 2 * A.card + B.card ≤ 2 * G.edgeFinset.card + L.card := by
    have h := hsumineq
    norm_num [mul_comm] at h ⊢
    exact h
  have hBL : B.card ≤ L.card := by omega
  exact hBL.trans (Finset.card_le_card hLsub)

lemma acyclic_edges_lt_active
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (hne : (Finset.univ.filter fun v => 0 < G.degree v).Nonempty) :
    G.edgeFinset.card < (Finset.univ.filter fun v => 0 < G.degree v).card := by
  let P : α → Prop := fun v => 0 < G.degree v
  letI : DecidablePred P := fun v => inferInstanceAs (Decidable (0 < G.degree v))
  let GA : SimpleGraph {v // P v} := G.induce {v | P v}
  have hsupp : G.support ⊆ {v | P v} := by
    intro v hv
    rcases hv with ⟨w, hvw⟩
    change 0 < G.degree v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨w, by simpa using! hvw⟩
  have hcardE : GA.edgeFinset.card = G.edgeFinset.card :=
    SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
  have hne' : Nonempty {v // P v} := by
    rcases hne with ⟨v, hv⟩
    exact ⟨⟨v, by simpa [P] using! hv⟩⟩
  letI : Nonempty {v // P v} := hne'
  have htop : (⊤ : SimpleGraph {v // P v}).Connected := SimpleGraph.connected_top
  obtain ⟨F, hle, _, hF⟩ :=
    SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic htop
      (by exact le_top) (hG.induce {v | P v})
  have hcardle : GA.edgeFinset.card ≤ F.edgeFinset.card := by
    exact Finset.card_le_card (by
      intro e he
      simp only [SimpleGraph.mem_edgeFinset] at he ⊢
      rcases e with ⟨a, b⟩
      exact hle he)
  have hFcard := hF.card_edgeFinset
  have htypecard : Fintype.card {v // P v} =
      (Finset.univ.filter fun v => 0 < G.degree v).card := by
    simpa [P] using! Fintype.card_subtype P
  rw [htypecard] at hFcard
  omega

/-- A finite tree has no more branch vertices in the subtree spanned by a set
of terminals than it has terminals.  (The sharper `|B| ≤ |S₀| - 2` is not
needed for the separator budget.) -/
lemma promotedBranchVertices_card_le
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α) :
    (promotedBranchVertices T S₀).card ≤ S₀.card := by
  by_cases hB : (promotedBranchVertices T S₀).Nonempty
  · have hcore_nonempty : (Finset.univ.filter fun v => 0 < (seedCore T S₀).degree v).Nonempty := by
      obtain ⟨v, hv⟩ := hB
      have hdeg := promoted_degree_seedCore T hT S₀ hv
      refine ⟨v, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
    have hedges := acyclic_edges_lt_active (seedCore T S₀)
      (hT.2.anti (seedCore_le T S₀)) hcore_nonempty
    have hleaf : ∀ v, (seedCore T S₀).degree v = 1 → v ∈ S₀ := by
      intro v hvdeg
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hvdeg
      obtain ⟨u, hu⟩ := hvdeg
      have hvu : (seedCore T S₀).Adj v u := by
        have : u ∈ (seedCore T S₀).neighborFinset v := by simp [hu]
        simpa using! this
      rcases hvu with ⟨hvuT, ⟨s, hsS, hsbr⟩, ⟨t, htS, htbr⟩⟩
      by_contra hvS
      have htv : t ≠ v := fun h => by
        subst t
        exact hvS htS
      obtain ⟨w, hw, hwuniq⟩ := existsUnique_mem_branch T hT v t htv
      have hwu : w ≠ u := by
        intro h
        subst w
        simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at htbr hw
        omega
      have hsopp : s ∈ branch T w v :=
        (branch_ssubset hT hw.1.symm hvuT hwu.symm).1 hsbr
      have hvwcore : (seedCore T S₀).Adj v w :=
        ⟨hw.1, ⟨t, htS, hw.2⟩, ⟨s, hsS, hsopp⟩⟩
      have hwmem : w ∈ (seedCore T S₀).neighborFinset v := by simpa using! hvwcore
      rw [hu] at hwmem
      exact hwu (by simpa using! hwmem)
    have hhigh := highDegree_card_le_of_edges_lt_active (seedCore T S₀) S₀ hedges hleaf
    apply le_trans (Finset.card_le_card ?_) hhigh
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact promoted_degree_seedCore T hT S₀ hv
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hB]

/-- Deleting edges incident with additional promoted seeds only refines the
nonseed components, so their sizes retain any bound valid for the original
separator. -/
lemma promoted_components_small
    (T : SimpleGraph α) [DecidableRel T.Adj]
    (S₀ : Finset α) (B : Finset α) (K : ℝ)
    (hsmall : ∀ c : (seedDeleted T S₀).ConnectedComponent,
      (Nat.card c.supp : ℝ) ≤ K) :
    ∀ c : (seedDeleted T (S₀ ∪ B)).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S₀ ∪ B) → (Nat.card c.supp : ℝ) ≤ K := by
  intro c ⟨v, hv, hvnot⟩
  -- seedDeleted T (S₀ ∪ B) has fewer edges than seedDeleted T S₀
  have adj_implication : ∀ a b, (seedDeleted T (S₀ ∪ B)).Adj a b → (seedDeleted T S₀).Adj a b := by
    intro a b hadj
    rw [seedDeleted_adj_iff] at hadj ⊢
    exact ⟨hadj.1, fun ha => hadj.2.1 (Finset.mem_union_left B ha), fun hb => hadj.2.2 (Finset.mem_union_left B hb)⟩
  -- All vertices in c.supp are reachable from v in seedDeleted T (S₀ ∪ B), hence in seedDeleted T S₀
  let c' := (seedDeleted T S₀).connectedComponentMk v
  have hsupp_subset : c.supp ⊆ c'.supp := by
    intro x hx
    -- x is reachable from v in seedDeleted T (S₀ ∪ B) since they're in the same component
    have hreach_S₀B : (seedDeleted T (S₀ ∪ B)).Reachable x v := by
      simp +decide [SimpleGraph.ConnectedComponent.supp] at hx ⊢
      -- hx : connectedComponentMk x = c, and v ∈ c.supp means connectedComponentMk v = c
      have hv_eq : (seedDeleted T (S₀ ∪ B)).connectedComponentMk v = c := by
        simp +decide [SimpleGraph.ConnectedComponent.supp] at hv
        exact hv
      have heq : (seedDeleted T (S₀ ∪ B)).connectedComponentMk x =
                 (seedDeleted T (S₀ ∪ B)).connectedComponentMk v := by rw [hx, hv_eq]
      simp only [connectedComponentMk] at heq
      rw [Quot.eq] at heq
      have heqv : Equivalence (seedDeleted T (S₀ ∪ B)).Reachable :=
        ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
      exact heqv.eqvGen_eq.symm ▸ heq
    -- By adj_implication, x is also reachable from v in seedDeleted T S₀
    have hreach_S₀ : (seedDeleted T S₀).Reachable x v := by
      -- Use that reachability can be lifted via edge implication
      rw [SimpleGraph.Reachable] at hreach_S₀B ⊢
      obtain ⟨w⟩ := hreach_S₀B
      let f : (seedDeleted T (S₀ ∪ B)) →g (seedDeleted T S₀) := {
        toFun := (fun a => a)
        map_rel' := @fun a b hab => adj_implication a b hab
      }
      refine ⟨w.map f⟩
    -- Therefore x is in the same component as v in seedDeleted T S₀
    simp +decide [SimpleGraph.ConnectedComponent.supp]
    have heqv : Equivalence (seedDeleted T S₀).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    show Quot.mk (seedDeleted T S₀).Reachable x = Quot.mk (seedDeleted T S₀).Reachable v
    rw [Quot.eq]
    exact heqv.eqvGen_eq.symm ▸ hreach_S₀
  have hcard : Nat.card c.supp ≤ Nat.card c'.supp := by
    apply Set.ncard_le_ncard hsupp_subset
  exact (hsmall c').trans' (Nat.cast_le.mpr hcard)

/-!
## Metric lemmas for the three-attachment median step
-/

omit [DecidableEq α] in
/-- Moving from the centre into the branch containing `x` decreases its
distance from `x` by exactly one. -/
lemma dist_succ_of_mem_branch (T : SimpleGraph α) (hT : T.IsTree)
    {v u x : α} (hadj : T.Adj v u) (hx : x ∈ branch T v u) :
    T.dist x u + 1 = T.dist x v := by
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have huv : T.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
  obtain ⟨p, hp⟩ :=
    SimpleGraph.Reachable.exists_walk_length_eq_dist (hT.1 x u)
  have hp' : (p.concat hadj.symm).length = T.dist x u + 1 := by simp [hp]
  have hle : T.dist x v ≤ T.dist x u + 1 := by
    rw [← hp']
    exact SimpleGraph.dist_le (p.concat hadj.symm)
  omega

/-- Distinct neighbour directions at a vertex of a tree are disjoint. -/
lemma branch_disjoint_of_ne (T : SimpleGraph α) (hT : T.IsTree)
    {v u w x : α} (hu : T.Adj v u) (hw : T.Adj v w) (huw : u ≠ w)
    (hxu : x ∈ branch T v u) (hxw : x ∈ branch T v w) : False := by
  have hxv : x ≠ v := by
    intro h
    subst x
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hxu
    have huv : T.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu
    simp [huv] at hxu
  obtain ⟨d, hd, huniq⟩ := existsUnique_mem_branch T hT v x hxv
  have hud : u = d := huniq u ⟨hu, hxu⟩
  have hwd : w = d := huniq w ⟨hw, hxw⟩
  exact huw (hud.trans hwd.symm)

omit [DecidableEq α] in
/-- If the geodesic from `t` to the branch centre passes through a point
already in a branch, then `t` lies in that same branch. -/
lemma mem_branch_of_through (T : SimpleGraph α) (hT : T.IsTree)
    {m u s t : α} (hadj : T.Adj m u) (hs : s ∈ branch T m u)
    (hdist : T.dist t m = T.dist t s + T.dist s m) :
    t ∈ branch T m u := by
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
  have htri : T.dist t u ≤ T.dist t s + T.dist s u :=
    (hT.1 t s).dist_triangle_left u
  have hstep := dist_succ_of_mem_branch T hT hadj hs
  omega

omit [Fintype α] [DecidableEq α] in
/-- A deleted-edge component containing a nonseed vertex contains no seed. -/
lemma component_supp_disjoint_seeds (T : SimpleGraph α) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) : ∀ x ∈ c.supp, x ∉ S := by
  rintro x hx hxS
  obtain ⟨v, hv, hvS⟩ := hc
  have hreach : (seedDeleted T S).Reachable x v := by
    have hx' : (seedDeleted T S).connectedComponentMk x = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hx
    have hv' : (seedDeleted T S).connectedComponentMk v = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hv
    have heq : (seedDeleted T S).connectedComponentMk x =
        (seedDeleted T S).connectedComponentMk v := hx'.trans hv'.symm
    simp only [connectedComponentMk] at heq
    rw [Quot.eq] at heq
    have heqv : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact heqv.eqvGen_eq.symm ▸ heq
  rcases hreach with ⟨p⟩
  have hlen : p.length = 0 := by
    by_contra hp
    have hpos : 0 < p.length := Nat.pos_of_ne_zero hp
    have hadj := p.adj_getVert_succ hpos
    have hx0 : p.getVert 0 = x := p.getVert_zero
    rw [hx0] at hadj
    exact ((seedDeleted_adj_iff T S x (p.getVert 1)).mp hadj).2.1 hxS
  have hxv : x = v := (SimpleGraph.Walk.nil_iff_length_eq.mpr hlen).eq
  exact hvS (hxv ▸ hxS)

omit [DecidableEq α] in
/-- Points lying in an additive split through `m` must occupy distinct
neighbour directions from `m`. -/
lemma branch_directions_ne_of_dist_add (T : SimpleGraph α) (hT : T.IsTree)
    {m x y ux uy : α}
    (hadd : T.dist x y = T.dist x m + T.dist m y)
    (hux : T.Adj m ux ∧ x ∈ branch T m ux)
    (huy : T.Adj m uy ∧ y ∈ branch T m uy) : ux ≠ uy := by
  intro heq
  subst uy
  have hxstep := dist_succ_of_mem_branch T hT hux.1 hux.2
  have hystep := dist_succ_of_mem_branch T hT huy.1 huy.2
  have htri : T.dist x y ≤ T.dist x ux + T.dist ux y :=
    (hT.1 x ux).dist_triangle_left y
  have hxy : T.dist y x = T.dist x y := SimpleGraph.dist_comm
  have huy : T.dist ux y = T.dist y ux := SimpleGraph.dist_comm
  have hmy : T.dist m y = T.dist y m := SimpleGraph.dist_comm
  omega

/-!
## The three-attachment median step
-/

/-- The first neighbour in the direction from one vertex of a nonseed deleted
component toward another still belongs to that component. -/
lemma component_direction_neighbor_mem
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    {m x u : α} (hm : m ∈ c.supp) (hx : x ∈ c.supp)
    (hmu : T.Adj m u) (hxu : x ∈ branch T m u) :
    u ∈ c.supp := by
  have hreach : (seedDeleted T S).Reachable m x := by
    have hm' : (seedDeleted T S).connectedComponentMk m = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hm
    have hx' : (seedDeleted T S).connectedComponentMk x = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hx
    have heq := hm'.trans hx'.symm
    simp only [connectedComponentMk] at heq
    rw [Quot.eq] at heq
    have heqv : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact heqv.eqvGen_eq.symm ▸ heq
  obtain ⟨p⟩ := hreach
  let f : (seedDeleted T S) →g T := {
    toFun := fun a => a
    map_rel' := fun hab => (seedDeleted_adj_iff T S _ _).mp hab |>.1
  }
  let pT : T.Walk x m := p.reverse.map f
  obtain ⟨q, hq⟩ :=
    SimpleGraph.Reachable.exists_walk_length_eq_dist (hT.1 x u)
  let r : T.Walk x m := q.concat hmu.symm
  have hrlen : r.length = T.dist x m := by
    simp only [r, SimpleGraph.Walk.length_concat, hq]
    exact dist_succ_of_mem_branch T hT hmu hxu
  have hrpath : r.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist r hrlen
  have hpathEq : r = (pT.toPath : T.Walk x m) := by
    exact (hT.existsUnique_path x m).unique hrpath pT.toPath.property
  have humem_r : u ∈ r.support := by simp [r]
  have humem_pTpath : u ∈ (pT.toPath : T.Walk x m).support := hpathEq ▸ humem_r
  have humem_pT : u ∈ pT.support := pT.support_toPath_subset humem_pTpath
  have humem_p : u ∈ p.support := by simpa [pT, f] using! humem_pT
  obtain ⟨a, b, hab⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp humem_p
  have hru : (seedDeleted T S).Reachable m u := by
    subst p
    exact a.reachable
  have hcomp : (seedDeleted T S).connectedComponentMk u = c := by
    have hm' : (seedDeleted T S).connectedComponentMk m = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hm
    rw [← hm']
    simp only [connectedComponentMk]
    rw [Quot.eq]
    have heqv : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact heqv.eqvGen_eq.symm ▸ hru.symm
  simpa [SimpleGraph.ConnectedComponent.supp] using! hcomp


/-- For three marked vertices of a finite tree, there is a vertex minimizing
the sum of the three distances. -/
lemma exists_min_three_distances (T : SimpleGraph α) (a b d : α) :
    ∃ m, ∀ v,
      T.dist m a + T.dist m b + T.dist m d ≤
        T.dist v a + T.dist v b + T.dist v d := by
  let weight : α → ℕ := fun v => T.dist v a + T.dist v b + T.dist v d
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ weight
    (by exact ⟨a, Finset.mem_univ a⟩)
  exact ⟨m, fun v => hm v (Finset.mem_univ v)⟩

/-- At a minimizer of the sum of distances to three marked vertices, no branch
direction contains two of the marked vertices. -/
lemma min_three_distances_branch_exclusive
    (T : SimpleGraph α) (hT : T.IsTree) {a b d m u : α}
    (hmin : ∀ v,
      T.dist m a + T.dist m b + T.dist m d ≤
        T.dist v a + T.dist v b + T.dist v d)
    (hmu : T.Adj m u) (ha : a ∈ branch T m u) (hb : b ∈ branch T m u) :
    False := by
  have haStep := dist_succ_of_mem_branch T hT hmu ha
  have hbStep := dist_succ_of_mem_branch T hT hmu hb
  have hd : T.dist u d ≤ T.dist m d + 1 := by
    have hdu : T.dist d u ≤ T.dist d m + T.dist m u :=
      (hT.1 d m).dist_triangle_left u
    have hmuDist : T.dist m u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hmu
    simpa [SimpleGraph.dist_comm, hmuDist] using! hdu
  have hminimum := hmin u
  have hma : T.dist m a = T.dist a m := SimpleGraph.dist_comm
  have hmb : T.dist m b = T.dist b m := SimpleGraph.dist_comm
  have hua : T.dist u a = T.dist a u := SimpleGraph.dist_comm
  have hub : T.dist u b = T.dist b u := SimpleGraph.dist_comm
  omega

/-- Every vertex on a deleted-edge walk that starts in a component remains in
that component. -/
lemma deleted_walk_support_mem_component
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent) {x y z : α}
    (hx : x ∈ c.supp) (p : (seedDeleted T S).Walk x y)
    (hz : z ∈ p.support) : z ∈ c.supp := by
  obtain ⟨a, b, hab⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hz
  have hr : (seedDeleted T S).Reachable x z := by
    subst p
    exact a.reachable
  have hx' : (seedDeleted T S).connectedComponentMk x = c := by
    simpa [SimpleGraph.ConnectedComponent.supp] using! hx
  have hz' : (seedDeleted T S).connectedComponentMk z = c := by
    rw [← hx']
    simp only [connectedComponentMk]
    rw [Quot.eq]
    have heqv : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact heqv.eqvGen_eq.symm ▸ hr.symm
  simpa [SimpleGraph.ConnectedComponent.supp] using! hz'

/-- The unique tree path between two vertices of a nonseed deleted component
contains no seed. -/
lemma component_tree_path_avoids_seeds
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {x y : α}
    (hx : x ∈ c.supp) (hy : y ∈ c.supp)
    (p : T.Walk x y) (hp : p.IsPath) :
    ∀ z ∈ p.support, z ∉ S := by
  have hreach : (seedDeleted T S).Reachable x y := by
    have hx' : (seedDeleted T S).connectedComponentMk x = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hx
    have hy' : (seedDeleted T S).connectedComponentMk y = c := by
      simpa [SimpleGraph.ConnectedComponent.supp] using! hy
    have heq := hx'.trans hy'.symm
    simp only [connectedComponentMk] at heq
    rw [Quot.eq] at heq
    have heqv : Equivalence (seedDeleted T S).Reachable :=
      ⟨SimpleGraph.Reachable.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    exact heqv.eqvGen_eq.symm ▸ heq
  obtain ⟨q⟩ := hreach
  let f : (seedDeleted T S) →g T := {
    toFun := fun a => a
    map_rel' := fun hab => (seedDeleted_adj_iff T S _ _).mp hab |>.1
  }
  have hpq : p = ((q.map f).toPath : T.Walk x y) :=
    (hT.existsUnique_path x y).unique hp (q.map f).toPath.property
  intro z hz hzS
  have hzmapPath : z ∈ ((q.map f).toPath : T.Walk x y).support := hpq ▸ hz
  have hzmap : z ∈ (q.map f).support :=
    (q.map f).support_toPath_subset hzmapPath
  have hzq : z ∈ q.support := by simpa [f] using! hzmap
  have hzc := deleted_walk_support_mem_component T S c hx q hzq
  exact component_supp_disjoint_seeds T S c hc z hzc hzS

/-- A boundary edge from a seed into a nonseed deleted component is the first
edge of the tree geodesic from that seed to every vertex of the component. -/
lemma boundary_dist_eq_succ
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {s x m : α}
    (hs : s ∈ S) (hx : x ∈ c.supp) (hm : m ∈ c.supp)
    (hsx : T.Adj s x) :
    T.dist s m = T.dist x m + 1 := by
  obtain ⟨q, hq⟩ :=
    SimpleGraph.Reachable.exists_walk_length_eq_dist (hT.1 x m)
  have hqpath : q.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist q hq
  have hsnot : s ∉ q.support := by
    intro hsupp
    exact component_tree_path_avoids_seeds T hT S c hc hx hm q hqpath s hsupp hs
  have hconsPath : (SimpleGraph.Walk.cons hsx q).IsPath := by
    simpa [SimpleGraph.Walk.cons_isPath_iff] using! ⟨hqpath, hsnot⟩
  obtain ⟨p, hp⟩ :=
    SimpleGraph.Reachable.exists_walk_length_eq_dist (hT.1 s m)
  have hppath : p.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist p hp
  have heq : p = SimpleGraph.Walk.cons hsx q :=
    (hT.existsUnique_path s m).unique hppath hconsPath
  rw [← hp, heq]
  simp [hq]

/-- Viewed from another vertex of its nonseed component, an attachment seed
lies in the same direction as its adjacent component witness. -/
lemma attachment_seed_same_direction
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {s x m u : α}
    (hs : s ∈ S) (hx : x ∈ c.supp) (hm : m ∈ c.supp)
    (hsx : T.Adj s x) (hmu : T.Adj m u) (hxu : x ∈ branch T m u) :
    s ∈ branch T m u := by
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
  have hxStep := dist_succ_of_mem_branch T hT hmu hxu
  have hsxDist : T.dist s x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hsx
  have hsm := boundary_dist_eq_succ T hT S c hc hs hx hm hsx
  have hsuTri : T.dist s u ≤ T.dist s x + T.dist x u :=
    (hT.1 s x).dist_triangle_left u
  omega

/-- Three vertices in one deleted-edge component admit a minimizer of their
total distance that remains in that component. -/
lemma exists_component_min_three_distances
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent) {a b d w : α}
    (hw : w ∈ c.supp) :
    ∃ m ∈ c.supp, ∀ v ∈ c.supp,
      T.dist m a + T.dist m b + T.dist m d ≤
        T.dist v a + T.dist v b + T.dist v d := by
  let weight : α → ℕ := fun v => T.dist v a + T.dist v b + T.dist v d
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun v => v ∈ c.supp) weight
    (by exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩)
  refine ⟨m, (Finset.mem_filter.mp hm).2, ?_⟩
  intro v hv
  exact hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-- At a component-restricted three-point median, no component direction can
contain two of the marked vertices. -/
lemma component_min_branch_exclusive
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent) {a b d m u w : α}
    (hm : m ∈ c.supp)
    (hmin : ∀ v ∈ c.supp,
      T.dist m a + T.dist m b + T.dist m d ≤
        T.dist v a + T.dist v b + T.dist v d)
    (hwC : w ∈ c.supp) (hmu : T.Adj m u) (hw : w ∈ branch T m u)
    (ha : a ∈ branch T m u) (hb : b ∈ branch T m u) : False := by
  have huC := component_direction_neighbor_mem T hT S c hm hwC hmu hw
  have haStep := dist_succ_of_mem_branch T hT hmu ha
  have hbStep := dist_succ_of_mem_branch T hT hmu hb
  have hd : T.dist u d ≤ T.dist m d + 1 := by
    have hdu : T.dist d u ≤ T.dist d m + T.dist m u :=
      (hT.1 d m).dist_triangle_left u
    have hmuDist : T.dist m u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hmu
    simpa [SimpleGraph.dist_comm, hmuDist] using! hdu
  have hminimum := hmin u huC
  have hma : T.dist m a = T.dist a m := SimpleGraph.dist_comm
  have hmb : T.dist m b = T.dist b m := SimpleGraph.dist_comm
  have hua : T.dist u a = T.dist a u := SimpleGraph.dist_comm
  have hub : T.dist u b = T.dist b u := SimpleGraph.dist_comm
  omega

/-- Every attachment of a nonseed component has an adjacent witness in the
component, and that witness is outside the enlarged seed set. -/
lemma componentSeed_exists_adjacent_nonseed
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {s : α}
    (hs : s ∈ componentSeeds T S c) :
    ∃ x ∈ c.supp, x ∉ S ∧ T.Adj s x := by
  obtain ⟨hsS, x, hx, hsx⟩ := (mem_componentSeeds_iff T S c s).mp hs
  exact ⟨x, hx, component_supp_disjoint_seeds T S c hc x hx, hsx⟩

/-- If a nonseed component has more than two attachments, one can select three
distinct attachment seeds together with adjacent nonseed witnesses inside the
component. -/
lemma component_three_seeds_with_witnesses
    (T : SimpleGraph α) [DecidableRel T.Adj] (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S)
    (hthree : 3 ≤ (componentSeeds T S c).card) :
    ∃ s₁ s₂ s₃ x₁ x₂ x₃,
      s₁ ∈ componentSeeds T S c ∧ s₂ ∈ componentSeeds T S c ∧
      s₃ ∈ componentSeeds T S c ∧
      s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧
      x₁ ∈ c.supp ∧ x₂ ∈ c.supp ∧ x₃ ∈ c.supp ∧
      x₁ ∉ S ∧ x₂ ∉ S ∧ x₃ ∉ S ∧
      T.Adj s₁ x₁ ∧ T.Adj s₂ x₂ ∧ T.Adj s₃ x₃ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < (componentSeeds T S c).card)
  obtain ⟨x₁, hx₁, hx₁S, hsx₁⟩ :=
    componentSeed_exists_adjacent_nonseed T S c hc hs₁
  obtain ⟨x₂, hx₂, hx₂S, hsx₂⟩ :=
    componentSeed_exists_adjacent_nonseed T S c hc hs₂
  obtain ⟨x₃, hx₃, hx₃S, hsx₃⟩ :=
    componentSeed_exists_adjacent_nonseed T S c hc hs₃
  exact ⟨s₁, s₂, s₃, x₁, x₂, x₃, hs₁, hs₂, hs₃,
    h₁₂, h₁₃, h₂₃, hx₁, hx₂, hx₃, hx₁S, hx₂S, hx₃S,
    hsx₁, hsx₂, hsx₃⟩

/-- From a point in a nonseed component, an attachment seed and its
component witness determine one direction; unless the witness is the point
itself, the witness lies in that direction too. -/
lemma attachment_direction_witness
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {s x m : α}
    (hs : s ∈ S) (hx : x ∈ c.supp) (hm : m ∈ c.supp) (hsx : T.Adj s x) :
    ∃ u, T.Adj m u ∧ s ∈ branch T m u ∧
      ((x = m ∧ u = s) ∨ x ∈ branch T m u) := by
  have hsm : s ≠ m := by
    intro h
    subst s
    exact component_supp_disjoint_seeds T S c hc m hm hs
  obtain ⟨u, hu, huuniq⟩ := existsUnique_mem_branch T hT m s hsm
  refine ⟨u, hu.1, hu.2, ?_⟩
  by_cases hxm : x = m
  · subst x
    have hum : u = s := by
      exact (huuniq s ⟨hsx.symm, by
        simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
        have hdist : T.dist s m = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hsx
        simp [hdist]⟩).symm
    exact Or.inl ⟨rfl, hum⟩
  · obtain ⟨w, hw, hwuniq⟩ := existsUnique_mem_branch T hT m x hxm
    have hsW : s ∈ branch T m w :=
      attachment_seed_same_direction T hT S c hc hs hx hm hsx hw.1 hw.2
    have hwu : w = u := huuniq w ⟨hw.1, hsW⟩
    exact Or.inr (hwu ▸ hw.2)

/-- Branches pointing away from a centre are nested inside the first
neighbour direction from that centre. -/
lemma branch_chain_trans
    (T : SimpleGraph α) (hT : T.IsTree) {t s x m u : α}
    (hmu : T.Adj m u) (hxu : x ∈ branch T m u) (hsx : T.Adj s x)
    (hsu : s ∈ branch T m u)
    (hsm : T.dist s m = T.dist x m + 1) (ht : t ∈ branch T x s) :
    t ∈ branch T m u := by
  generalize hn : T.dist x m = n
  induction n using Nat.strong_induction_on generalizing m u with
  | h n ih =>
      have hxuStep := dist_succ_of_mem_branch T hT hmu hxu
      by_cases hxuEq : x = u
      · subst x
        exact (branch_ssubset hT hmu hsx.symm (by
          intro h
          subst s
          have hzero : T.dist m m = 0 := SimpleGraph.dist_self
          omega)).1 ht
      · obtain ⟨v, hv, hvuniq⟩ := existsUnique_mem_branch T hT u x hxuEq
        have hvne : v ≠ m := by
          intro h
          subst v
          simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hv hxu
          omega
        have hsuStep := dist_succ_of_mem_branch T hT hmu hsu
        have hs_u : T.dist s u = T.dist x u + 1 := by omega
        have hsv : s ∈ branch T u v := by
          simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
          have hxvStep := dist_succ_of_mem_branch T hT hv.1 hv.2
          have hsxDist : T.dist s x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hsx
          have hsvTri : T.dist s v ≤ T.dist s x + T.dist x v :=
            (hT.1 s x).dist_triangle_left v
          omega
        have hlt : T.dist x u < n := by omega
        have htuv : t ∈ branch T u v :=
          ih (T.dist x u) hlt hv.1 hv.2 hsv hs_u rfl
        exact (branch_ssubset hT hmu hv.1 hvne).1 htuv

/-- An original seed lying beyond an attachment edge remains in the same
median direction as that attachment. -/
lemma original_seed_same_attachment_direction
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {t s x m u : α}
    (ht : t ∈ branch T x s) (hs : s ∈ S) (hx : x ∈ c.supp)
    (hm : m ∈ c.supp) (hsx : T.Adj s x) (hmu : T.Adj m u)
    (hsu : s ∈ branch T m u)
    (hxdir : (x = m ∧ u = s) ∨ x ∈ branch T m u) :
    t ∈ branch T m u := by
  rcases hxdir with ⟨rfl, rfl⟩ | hxu
  · exact ht
  · exact branch_chain_trans T hT hmu hxu hsx hsu
      (boundary_dist_eq_succ T hT S c hc hs hx hm hsx) ht

/-- Distinct attachments selected at a component median determine distinct
directions from that median. -/
lemma attachment_directions_ne
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S) {a b d m s₁ s₂ u₁ u₂ : α}
    (hm : m ∈ c.supp) (haC : a ∈ c.supp) (hbC : b ∈ c.supp)
    (hmin : ∀ v ∈ c.supp,
      T.dist m a + T.dist m b + T.dist m d ≤
        T.dist v a + T.dist v b + T.dist v d)
    (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (hne : s₁ ≠ s₂)
    (hu₁ : T.Adj m u₁) (hu₂ : T.Adj m u₂)
    (ha : (a = m ∧ u₁ = s₁) ∨ a ∈ branch T m u₁)
    (hb : (b = m ∧ u₂ = s₂) ∨ b ∈ branch T m u₂) : u₁ ≠ u₂ := by
  intro heq
  rcases ha with ⟨ham, hu₁s⟩ | ha
  · rcases hb with ⟨hbm, hu₂s⟩ | hb
    · exact hne (hu₁s ▸ hu₂s ▸ heq)
    · have hu₂C := component_direction_neighbor_mem T hT S c hm hbC hu₂ hb
      have hu₂not := component_supp_disjoint_seeds T S c hc u₂ hu₂C
      exact hu₂not (by simpa [← heq, hu₁s] using! hs₁)
  · rcases hb with ⟨hbm, hu₂s⟩ | hb
    · have hu₁C := component_direction_neighbor_mem T hT S c hm haC hu₁ ha
      have hu₁not := component_supp_disjoint_seeds T S c hc u₁ hu₁C
      exact hu₁not (by simpa [heq, hu₂s] using! hs₂)
    · exact component_min_branch_exclusive T hT S c hm hmin haC hu₁
        ha ha (heq ▸ hb)

/-- After promoting every vertex with three original-seed-bearing directions,
each remaining nonseed component has at most two attachments to the enlarged
seed set. -/
lemma promoted_components_two_attachments
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S₀ : Finset α)
    (c : (seedDeleted T (S₀ ∪ promotedBranchVertices T S₀)).ConnectedComponent)
    (hc : ∃ v ∈ c.supp, v ∉ S₀ ∪ promotedBranchVertices T S₀) :
    (componentSeeds T (S₀ ∪ promotedBranchVertices T S₀) c).card ≤ 2 := by
  let S := S₀ ∪ promotedBranchVertices T S₀
  by_contra hnot
  have hthree : 3 ≤ (componentSeeds T S c).card := by
    simpa [S] using! (show ¬ (componentSeeds T S c).card ≤ 2 from hnot)
  obtain ⟨s₁, s₂, s₃, x₁, x₂, x₃, hs₁, hs₂, hs₃,
      hs₁₂, hs₁₃, hs₂₃, hx₁, hx₂, hx₃, hx₁S, hx₂S, hx₃S,
      hsx₁, hsx₂, hsx₃⟩ := component_three_seeds_with_witnesses T S c hc hthree
  obtain ⟨m, hm, hmin⟩ := exists_component_min_three_distances
    T S c (a := x₁) (b := x₂) (d := x₃) hx₁
  have hs₁S : s₁ ∈ S := componentSeeds_subset T S c hs₁
  have hs₂S : s₂ ∈ S := componentSeeds_subset T S c hs₂
  have hs₃S : s₃ ∈ S := componentSeeds_subset T S c hs₃
  obtain ⟨u₁, hmu₁, hs₁u, hx₁dir⟩ :=
    attachment_direction_witness T hT S c hc hs₁S hx₁ hm hsx₁
  obtain ⟨u₂, hmu₂, hs₂u, hx₂dir⟩ :=
    attachment_direction_witness T hT S c hc hs₂S hx₂ hm hsx₂
  obtain ⟨u₃, hmu₃, hs₃u, hx₃dir⟩ :=
    attachment_direction_witness T hT S c hc hs₃S hx₃ hm hsx₃
  have hu₁₂ : u₁ ≠ u₂ := attachment_directions_ne T hT S c hc hm hx₁ hx₂
    hmin hs₁S hs₂S hs₁₂ hmu₁ hmu₂ hx₁dir hx₂dir
  have hmin₁₃ : ∀ v ∈ c.supp,
      T.dist m x₁ + T.dist m x₃ + T.dist m x₂ ≤
        T.dist v x₁ + T.dist v x₃ + T.dist v x₂ := by
    intro v hv
    have := hmin v hv
    omega
  have hu₁₃ : u₁ ≠ u₃ := attachment_directions_ne T hT S c hc hm hx₁ hx₃
    hmin₁₃ hs₁S hs₃S hs₁₃ hmu₁ hmu₃ hx₁dir hx₃dir
  have hmin₂₃ : ∀ v ∈ c.supp,
      T.dist m x₂ + T.dist m x₃ + T.dist m x₁ ≤
        T.dist v x₂ + T.dist v x₃ + T.dist v x₁ := by
    intro v hv
    have := hmin v hv
    omega
  have hu₂₃ : u₂ ≠ u₃ := attachment_directions_ne T hT S c hc hm hx₂ hx₃
    hmin₂₃ hs₂S hs₃S hs₂₃ hmu₂ hmu₃ hx₂dir hx₃dir
  have hu₁D : u₁ ∈ seedDirections T S₀ m := by
    simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    obtain ⟨t, htS, ht⟩ := enlargedSeed_attachment_bears_originalSeed T hT S₀ hs₁S hsx₁
    exact ⟨hmu₁, t, htS, original_seed_same_attachment_direction
      T hT S c hc ht hs₁S hx₁ hm hsx₁ hmu₁ hs₁u hx₁dir⟩
  have hu₂D : u₂ ∈ seedDirections T S₀ m := by
    simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    obtain ⟨t, htS, ht⟩ := enlargedSeed_attachment_bears_originalSeed T hT S₀ hs₂S hsx₂
    exact ⟨hmu₂, t, htS, original_seed_same_attachment_direction
      T hT S c hc ht hs₂S hx₂ hm hsx₂ hmu₂ hs₂u hx₂dir⟩
  have hu₃D : u₃ ∈ seedDirections T S₀ m := by
    simp only [seedDirections, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    obtain ⟨t, htS, ht⟩ := enlargedSeed_attachment_bears_originalSeed T hT S₀ hs₃S hsx₃
    exact ⟨hmu₃, t, htS, original_seed_same_attachment_direction
      T hT S c hc ht hs₃S hx₃ hm hsx₃ hmu₃ hs₃u hx₃dir⟩
  have hcard : 3 ≤ (seedDirections T S₀ m).card := by
    have hsub : {u₁, u₂, u₃} ⊆ seedDirections T S₀ m := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact hu₁D
      · exact hu₂D
      · exact hu₃D
    have hc := Finset.card_le_card hsub
    simp [hu₁₂, hu₁₃, hu₂₃] at hc
    exact hc
  have hmB : m ∈ promotedBranchVertices T S₀ := by
    simpa [promotedBranchVertices] using! hcard
  exact component_supp_disjoint_seeds T S c hc m hm
    (by exact Finset.mem_union_right S₀ hmB)

end Erdos550
