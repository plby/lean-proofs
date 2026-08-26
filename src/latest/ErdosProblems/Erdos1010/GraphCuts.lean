import ErdosProblems.Erdos1010.GraphPairs

/-! # Finite cuts and internal edge counts -/

open Finset

namespace Erdos1010

variable {V : Type*} [Fintype V] [DecidableEq V]

def internalPairs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 2).filter fun p ↦ p ⊆ S

def crossingPairs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 2).filter fun p ↦ (p ∩ S).card = 1

def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (crossingPairs G S).card

lemma pair_inter_card (p S : Finset V) (hp : p.card = 2) :
    (p ∩ S).card = (if (p ∩ S).card = 1 then 1 else 0) + 2 * (if p ⊆ S then 1 else 0) := by
  have hle : (p ∩ S).card ≤ 2 := by simpa [hp] using card_le_card (inter_subset_left : p ∩ S ⊆ p)
  by_cases hsub : p ⊆ S
  · rw [inter_eq_left.mpr hsub, hp]
    simp [hsub]
  · have hne : (p ∩ S).card ≠ 2 := by
      intro hcard
      have heq : p ∩ S = p := eq_of_subset_of_card_le inter_subset_left (by omega)
      exact hsub (inter_eq_left.mp heq)
    split_ifs <;> omega

lemma sum_indicator_pair (p S : Finset V) :
    (∑ v ∈ p, if v ∈ S then (1 : ℤ) else 0) = (p ∩ S).card := by
  rw [← sum_filter]
  have heq : p.filter (fun v ↦ v ∈ S) = p ∩ S := by ext v; simp
  rw [heq]
  simp

lemma cut_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (cutSize G S : ℤ) + 2 * (internalPairs G S).card = ∑ v ∈ S, (G.degree v : ℤ) := by
  have hcharge := pairCharge_cliqueFinset_eq G (fun v ↦ if v ∈ S then (1 : ℤ) else 0)
  have hleft : pairCharge (G.cliqueFinset 2) (fun v ↦ if v ∈ S then (1 : ℤ) else 0) =
      (cutSize G S : ℤ) + 2 * (internalPairs G S).card := by
    unfold pairCharge
    simp_rw [sum_indicator_pair]
    have hpoint : ∀ p ∈ G.cliqueFinset 2, ((p ∩ S).card : ℤ) =
        (if (p ∩ S).card = 1 then 1 else 0) + 2 * (if p ⊆ S then 1 else 0) := by
      intro p hp
      exact_mod_cast pair_inter_card p S (G.mem_cliqueFinset_iff.mp hp).card_eq
    rw [sum_congr rfl hpoint, sum_add_distrib, ← mul_sum]
    simp only [← sum_filter]
    simp [cutSize, crossingPairs, internalPairs]
  rw [hleft] at hcharge
  simpa [mul_ite] using hcharge

lemma pair_inter_compl_card (p S : Finset V) :
    (p ∩ S).card + (p ∩ Sᶜ).card = p.card := by
  have hdis : Disjoint (p ∩ S) (p ∩ Sᶜ) := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (mem_compl.mp (mem_inter.mp hw).2) (mem_inter.mp hv).2
  rw [← card_union_of_disjoint hdis]
  congr 1
  ext v
  simp only [mem_union, mem_inter, mem_compl]
  tauto

lemma cutSize_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G Sᶜ = cutSize G S := by
  unfold cutSize crossingPairs
  congr 1
  apply filter_congr
  intro p hp
  have hc := (G.mem_cliqueFinset_iff.mp hp).card_eq
  have hsum := pair_inter_compl_card p S
  omega

lemma cut_partition_edges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (internalPairs G S).card + (internalPairs G Sᶜ).card + cutSize G S = G.edgeFinset.card := by
  have hS := cut_degree_sum G S
  have hSc := cut_degree_sum G Sᶜ
  rw [cutSize_compl] at hSc
  have hsum : (∑ v ∈ S, (G.degree v : ℤ)) + (∑ v ∈ Sᶜ, (G.degree v : ℤ)) =
      2 * G.edgeFinset.card := by
    rw [sum_add_sum_compl]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  omega

lemma card_cliques_induce_finset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (n : ℕ) :
    ((G.induce (S : Set V)).cliqueFinset n).card =
      ((G.cliqueFinset n).filter fun p ↦ p ⊆ S).card := by
  let f : (S : Set V) ↪ V := Function.Embedding.subtype _
  apply card_bij (fun p _ ↦ p.map f)
  · intro p hp
    apply mem_filter.mpr
    constructor
    · apply G.mem_cliqueFinset_iff.mpr
      exact (SimpleGraph.isNClique_induce_iff (S : Set V) p n).mp
        ((G.induce (S : Set V)).mem_cliqueFinset_iff.mp hp)
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
      exact a.property
  · intro p hp q hq heq
    exact Finset.map_injective f heq
  · intro p hp
    obtain ⟨hpG, hpS⟩ := mem_filter.mp hp
    let q : Finset (S : Set V) := p.subtype fun v ↦ v ∈ S
    have hmap : q.map f = p := subtype_map_of_mem hpS
    refine ⟨q, ?_, hmap⟩
    apply (G.induce (S : Set V)).mem_cliqueFinset_iff.mpr
    apply (SimpleGraph.isNClique_induce_iff (S : Set V) q n).mpr
    rw [show q.map (Function.Embedding.subtype _) = p from hmap]
    exact G.mem_cliqueFinset_iff.mp hpG

lemma card_internalPairs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (internalPairs G S).card = (G.induce (S : Set V)).edgeFinset.card := by
  rw [← card_cliqueFinset_two, card_cliques_induce_finset]
  rfl

def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun p ↦ v ∈ p

lemma card_internalPairs_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (internalPairs G (G.neighborFinset v)).card = (trianglesAt G v).card := by
  apply card_bij (fun p _ ↦ insert v p)
  · intro p hp
    obtain ⟨hpG, hpN⟩ := mem_filter.mp hp
    apply mem_filter.mpr
    refine ⟨G.mem_cliqueFinset_iff.mpr ?_, mem_insert_self _ _⟩
    exact (G.mem_cliqueFinset_iff.mp hpG).insert
      (fun w hw ↦ G.mem_neighborFinset v w |>.mp (hpN hw))
  · intro p hp q hq heq
    have hvp : v ∉ p := by
      intro h
      exact (G.mem_neighborFinset v v |>.mp ((mem_filter.mp hp).2 h)).ne rfl
    have hvq : v ∉ q := by
      intro h
      exact (G.mem_neighborFinset v v |>.mp ((mem_filter.mp hq).2 h)).ne rfl
    have h := congrArg (fun p : Finset V ↦ p.erase v) heq
    simpa [hvp, hvq] using h
  · intro p hp
    obtain ⟨hpG, hvp⟩ := mem_filter.mp hp
    have ht := G.mem_cliqueFinset_iff.mp hpG
    refine ⟨p.erase v, mem_filter.mpr ⟨G.mem_cliqueFinset_iff.mpr ?_, ?_⟩, insert_erase hvp⟩
    · exact ht.erase_of_mem hvp
    · intro w hw
      apply G.mem_neighborFinset v w |>.mpr
      exact ht.isClique hvp (mem_of_mem_erase hw) (ne_of_mem_erase hw).symm

lemma sum_card_trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, (trianglesAt G v).card) = 3 * (G.cliqueFinset 3).card := by
  unfold trianglesAt
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ p ∈ G.cliqueFinset 3, p.card := by
      apply sum_congr rfl
      intro p hp
      simp
    _ = ∑ _p ∈ G.cliqueFinset 3, 3 := by
      apply sum_congr rfl
      intro p hp
      exact (G.mem_cliqueFinset_iff.mp hp).card_eq
    _ = _ := by simp [mul_comm]

lemma sum_neighbor_cuts (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, (cutSize G (G.neighborFinset v) : ℤ)) + 6 * (G.cliqueFinset 3).card =
      ∑ v, (G.degree v : ℤ) ^ 2 := by
  have h := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ ↦ cut_degree_sum G (G.neighborFinset v))
  simp only [card_internalPairs_neighbors, sum_add_distrib, ← mul_sum] at h
  have htri : (∑ v, ((trianglesAt G v).card : ℤ)) = 3 * (G.cliqueFinset 3).card := by
    exact_mod_cast sum_card_trianglesAt G
  rw [htri] at h
  have hdeg : (∑ v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℤ)) = ∑ v, (G.degree v : ℤ) ^ 2 := by
    have heq : ∀ v, G.neighborFinset v = univ.filter (G.Adj v) := by
      intro v
      ext u
      simp
    simp_rw [heq, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    simp_rw [G.adj_comm]
    rw [← sum_filter, ← heq]
    simp [SimpleGraph.card_neighborFinset_eq_degree, pow_two]
  rw [hdeg] at h
  nlinarith only [h]

def IsMaximumCut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ T : Finset V, cutSize G T ≤ cutSize G S

def cutImbalance (S : Finset V) : ℕ := max S.card Sᶜ.card

lemma isMaximumCut_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsMaximumCut G Sᶜ ↔ IsMaximumCut G S := by simp only [IsMaximumCut, cutSize_compl]

lemma cutImbalance_compl (S : Finset V) : cutImbalance Sᶜ = cutImbalance S := by
  simp [cutImbalance, max_comm]

lemma exists_min_imbalance_maximum_cut (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, IsMaximumCut G S ∧ S.card ≤ Sᶜ.card ∧
      ∀ T : Finset V, IsMaximumCut G T → cutImbalance S ≤ cutImbalance T := by
  classical
  obtain ⟨S₀, hS₀, hmax⟩ := (univ : Finset (Finset V)).exists_max_image (cutSize G)
    ⟨∅, mem_univ _⟩
  have hS₀max : IsMaximumCut G S₀ := fun T ↦ hmax T (mem_univ _)
  let F := (univ : Finset (Finset V)).filter (IsMaximumCut G)
  have hF : F.Nonempty := ⟨S₀, mem_filter.mpr ⟨mem_univ _, hS₀max⟩⟩
  obtain ⟨S, hSF, hmin⟩ := F.exists_min_image cutImbalance hF
  have hSmax := (mem_filter.mp hSF).2
  have hSmin : ∀ T, IsMaximumCut G T → cutImbalance S ≤ cutImbalance T :=
    fun T hT ↦ hmin T (mem_filter.mpr ⟨mem_univ _, hT⟩)
  by_cases hcard : S.card ≤ Sᶜ.card
  · exact ⟨S, hSmax, hcard, hSmin⟩
  · refine ⟨Sᶜ, (isMaximumCut_compl G S).mpr hSmax, ?_, ?_⟩
    · simp only [compl_compl]
      omega
    · intro T hT
      rw [cutImbalance_compl]
      exact hSmin T hT

lemma pair_eq_of_mem {p : Finset V} {v : V} (hp : p.card = 2) (hv : v ∈ p) :
    ∃ w, w ≠ v ∧ p = {v, w} := by
  have hc : (p.erase v).card = 1 := by rw [card_erase_of_mem hv, hp]
  obtain ⟨w, hw⟩ := card_eq_one.mp hc
  have hwm : w ∈ p.erase v := by rw [hw]; simp
  exact ⟨w, ne_of_mem_erase hwm, by rw [← hw, insert_erase hv]⟩

lemma internalPairs_insert (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : V) (hv : v ∉ S) :
    internalPairs G (insert v S) = internalPairs G S ∪
      (G.neighborFinset v ∩ S).image (fun w ↦ ({v, w} : Finset V)) := by
  ext p
  simp only [internalPairs, mem_filter, mem_union, mem_image]
  constructor
  · rintro ⟨hpG, hpS⟩
    by_cases hvp : v ∈ p
    · obtain ⟨w, hwv, hpw⟩ := pair_eq_of_mem (G.mem_cliqueFinset_iff.mp hpG).card_eq hvp
      have hwS : w ∈ S := (mem_insert.mp (hpS (by rw [hpw]; simp))).resolve_left hwv
      have hvw : G.Adj v w := (mem_pair_clique_iff G v w).mp (hpw ▸ hpG)
      exact Or.inr ⟨w, mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, hwS⟩, hpw.symm⟩
    · left
      refine ⟨hpG, fun w hw ↦ ?_⟩
      exact (mem_insert.mp (hpS hw)).resolve_left (fun h ↦ hvp (h ▸ hw))
  · rintro (⟨hpG, hpS⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨hpG, hpS.trans (subset_insert _ _)⟩
    · have hwN := (mem_inter.mp hw).1
      have hwS := (mem_inter.mp hw).2
      exact ⟨(mem_pair_clique_iff G v w).mpr ((G.mem_neighborFinset v w).mp hwN), by simp [hwS]⟩

lemma card_internalPairs_insert (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : V) (hv : v ∉ S) :
    (internalPairs G (insert v S)).card = (internalPairs G S).card + (G.neighborFinset v ∩ S).card := by
  rw [internalPairs_insert G S v hv, card_union_of_disjoint]
  · rw [card_image_of_injOn]
    intro a ha b hb heq
    have han : a ≠ v := ne_of_mem_of_not_mem (mem_inter.mp ha).2 hv
    change ({v, a} : Finset V) = {v, b} at heq
    have ham : a ∈ ({v, b} : Finset V) := by rw [← heq]; simp
    simpa [han] using ham
  · apply disjoint_left.mpr
    intro p hp hi
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hi
    exact hv ((mem_filter.mp hp).2 (by simp))

lemma cutSize_insert_relation (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : V) (hv : v ∉ S) :
    (cutSize G (insert v S) : ℤ) + 2 * (G.neighborFinset v ∩ S).card =
      (cutSize G S : ℤ) + G.degree v := by
  have hnew := cut_degree_sum G (insert v S)
  have hold := cut_degree_sum G S
  rw [card_internalPairs_insert G S v hv, Nat.cast_add, sum_insert hv] at hnew
  linarith

lemma neighbor_partition (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    (G.neighborFinset v ∩ S).card + (G.neighborFinset v ∩ Sᶜ).card = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact pair_inter_compl_card _ _

lemma maximum_cut_external_ge_internal (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hmax : IsMaximumCut G S) (v : V) (hv : v ∉ S) :
    (G.neighborFinset v ∩ Sᶜ).card ≤ (G.neighborFinset v ∩ S).card := by
  have hmove := cutSize_insert_relation G S v hv
  have hpart := neighbor_partition G S v
  have hm := hmax (insert v S)
  omega

lemma minimum_imbalance_insert_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hmax : IsMaximumCut G S)
    (hmin : ∀ T, IsMaximumCut G T → cutImbalance S ≤ cutImbalance T)
    (hcard : S.card + 2 ≤ Sᶜ.card) (v : V) (hv : v ∉ S) :
    cutSize G (insert v S) < cutSize G S := by
  have hnewpart := card_add_card_compl (insert v S)
  have hpart := card_add_card_compl S
  rw [card_insert_of_notMem hv] at hnewpart
  have hscore : cutImbalance (insert v S) < cutImbalance S := by
    unfold cutImbalance
    rw [card_insert_of_notMem hv]
    omega
  have hle := hmax (insert v S)
  by_contra! hn
  have heq : cutSize G (insert v S) = cutSize G S := by omega
  have hnewmax : IsMaximumCut G (insert v S) := fun T ↦ by rw [heq]; exact hmax T
  have hmin' := hmin (insert v S) hnewmax
  omega

lemma minimum_imbalance_external_gt_internal (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hmax : IsMaximumCut G S)
    (hmin : ∀ T, IsMaximumCut G T → cutImbalance S ≤ cutImbalance T)
    (hcard : S.card + 2 ≤ Sᶜ.card) (v : V) (hv : v ∉ S) :
    (G.neighborFinset v ∩ Sᶜ).card < (G.neighborFinset v ∩ S).card := by
  have hmove := cutSize_insert_relation G S v hv
  have hpart := neighbor_partition G S v
  have hm := minimum_imbalance_insert_lt G S hmax hmin hcard v hv
  omega

lemma maximum_cut_square_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hmax : IsMaximumCut G S) :
    (∑ v, (G.degree v : ℤ) ^ 2) ≤ (Fintype.card V : ℤ) * cutSize G S +
      6 * (G.cliqueFinset 3).card := by
  have h := sum_neighbor_cuts G
  have hle : (∑ v, (cutSize G (G.neighborFinset v) : ℤ)) ≤
      (Fintype.card V : ℤ) * cutSize G S := by
    calc
      _ ≤ ∑ _v : V, (cutSize G S : ℤ) := sum_le_sum fun v _ ↦ by exact_mod_cast hmax (G.neighborFinset v)
      _ = _ := by simp
  linarith

lemma degree_square_lower_even (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℤ)
    (hn : (Fintype.card V : ℤ) = 2 * r) (hm : (G.edgeFinset.card : ℤ) = r ^ 2 + t) :
    2 * r ^ 3 + 4 * r * t ≤ ∑ v, (G.degree v : ℤ) ^ 2 := by
  have hsum : (∑ v, (G.degree v : ℤ)) = 2 * (r ^ 2 + t) := by
    have h : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rwa [hm] at h
  have hnon : 0 ≤ ∑ v, ((G.degree v : ℤ) - r) ^ 2 := sum_nonneg fun v _ ↦ sq_nonneg _
  have heq : (∑ v, ((G.degree v : ℤ) - r) ^ 2) =
      (∑ v, (G.degree v : ℤ) ^ 2) - 2 * r * (∑ v, (G.degree v : ℤ)) +
      (Fintype.card V : ℤ) * r ^ 2 := by
    have hpoint : ∀ v, ((G.degree v : ℤ) - r) ^ 2 =
        (G.degree v : ℤ) ^ 2 - (2 * r) * (G.degree v : ℤ) + r ^ 2 := by intro v; ring
    simp_rw [hpoint]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    simp
  rw [heq, hsum, hn] at hnon
  nlinarith only [hnon]

lemma maximum_cut_defect_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (r t : ℤ) (hr : 0 < r)
    (hn : (Fintype.card V : ℤ) = 2 * r) (hm : (G.edgeFinset.card : ℤ) = r ^ 2 + t)
    (hmax : IsMaximumCut G S) (hT : ((G.cliqueFinset 3).card : ℤ) < r * t) :
    r ^ 2 - cutSize G S < t := by
  have hcut := maximum_cut_square_bound G S hmax
  have hsq := degree_square_lower_even G r t hn hm
  rw [hn] at hcut
  by_contra! hbad
  have hp := mul_nonneg (le_of_lt hr) (show 0 ≤ r ^ 2 - cutSize G S - t by omega)
  nlinarith

lemma cliques_induce_finset_map (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (n : ℕ) :
    ((G.induce (S : Set V)).cliqueFinset n).map
      ⟨Finset.map (Function.Embedding.subtype _), Finset.map_injective _⟩ =
      (G.cliqueFinset n).filter (fun p ↦ p ⊆ S) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
    apply mem_filter.mpr
    constructor
    · apply G.mem_cliqueFinset_iff.mpr
      exact (SimpleGraph.isNClique_induce_iff (S : Set V) q n).mp
        ((G.induce (S : Set V)).mem_cliqueFinset_iff.mp hq)
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
      exact a.property
  · intro hp
    obtain ⟨hpG, hpS⟩ := mem_filter.mp hp
    let q : Finset (S : Set V) := p.subtype (fun v ↦ v ∈ S)
    have hmap : q.map (Function.Embedding.subtype _) = p := subtype_map_of_mem hpS
    apply mem_map.mpr
    refine ⟨q, ?_, hmap⟩
    apply (G.induce (S : Set V)).mem_cliqueFinset_iff.mpr
    apply (SimpleGraph.isNClique_induce_iff (S : Set V) q n).mpr
    rw [hmap]
    exact G.mem_cliqueFinset_iff.mp hpG

lemma pairCharge_internalPairs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (w : V → ℤ) : pairCharge (internalPairs G S) w =
      ∑ v : (S : Set V), ((G.induce (S : Set V)).degree v : ℤ) * w v.val := by
  rw [← pairCharge_cliqueFinset_eq]
  unfold internalPairs
  rw [← cliques_induce_finset_map G S 2]
  simp [pairCharge]

end Erdos1010
