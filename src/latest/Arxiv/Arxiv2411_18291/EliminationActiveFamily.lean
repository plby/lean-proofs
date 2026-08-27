import Arxiv.Arxiv2411_18291.EliminationNearCounts

/-! # The part of an elimination family that can retain high multiplicity

Every replacement touching the old graph comes from the small near part
of its pattern. Replacements outside this family avoid the old graph, and
every edge of multiplicity greater than two is covered only by this family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

def EliminationFamily.activeCliques (F : EliminationFamily S N B P Q θ) :=
  F.cliques.filter fun R => (cliqueEdges (r + 1) R ∩ B).Nonempty

def EliminationFamily.activeGraph (F : EliminationFamily S N B P Q θ) :=
  B ∪ univ.biUnion fun i => mapGraph (F.embedding i)
    (newEdges (S.base.val ∪ N.val) (cliqueSupport (r + 1) (S.eliminationNear N)))

theorem EliminationFamily.copy_active_iff (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) {R : Block W q}
    (hR : R ∈ S.eliminationCliques N) :
    (cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ B).Nonempty ↔
      R ∈ S.eliminationNear N := by
  rw [F.clique_inter_original hpair i R (S.elimination_clique_subset N hR),
    ← F.positive_root i, ← F.negative_root i,
    ← map_cliqueEdges, ← map_cliqueEdges, ← map_cliqueEdges,
    ← mapGraph_union, ← mapGraph_inter]
  simp only [ExchangeSystem.eliminationNear, mem_filter, hR, true_and,
    mapGraph, map_nonempty]

theorem EliminationFamily.activeCliques_eq (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) :
    F.activeCliques = univ.biUnion fun i => mapGraph (F.embedding i) (S.eliminationNear N) := by
  ext R
  constructor
  · intro hR
    obtain ⟨hR, hactive⟩ := mem_filter.mp hR
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
    obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
    exact mem_biUnion.mpr ⟨i, mem_univ _, (mem_mapGraph _ _ _).mpr
      ⟨R₀, (F.copy_active_iff hpair i hR₀).mp hactive, rfl⟩⟩
  · intro hR
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
    obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
    have hmem := S.eliminationNear_subset N hR₀
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _,
      (mem_mapGraph _ _ _).mpr ⟨R₀, hmem, rfl⟩⟩,
      (F.copy_active_iff hpair i hmem).mpr hR₀⟩

theorem EliminationFamily.activeCliques_subset (F : EliminationFamily S N B P Q θ) :
    F.activeCliques ⊆ F.cliques := filter_subset _ _

theorem EliminationFamily.inactive_avoids (F : EliminationFamily S N B P Q θ)
    {R : Block V q} (hR : R ∈ F.cliques \ F.activeCliques) :
    Disjoint (cliqueEdges (r + 1) R) B := by
  apply disjoint_iff_inter_eq_empty.mpr
  apply not_nonempty_iff_eq_empty.mp
  exact fun h => (mem_sdiff.mp hR).2 (mem_filter.mpr ⟨(mem_sdiff.mp hR).1, h⟩)

theorem EliminationFamily.high_multiplicity_active (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {e : Block V (r + 1)}
    (he : 2 < (F.cliques.filter fun R => e.val ⊆ R.val).card) :
    F.cliques.filter (fun R => e.val ⊆ R.val) ⊆ F.activeCliques := by
  have heB : e ∈ B := by
    by_contra h
    exact (not_lt_of_ge (F.clique_count_outside hpair e h)) he
  intro R hR
  exact mem_filter.mpr ⟨(mem_filter.mp hR).1,
    ⟨e, mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr (mem_filter.mp hR).2, heB⟩⟩⟩

theorem EliminationFamily.inactive_multiplicity (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (e : Block V (r + 1)) :
    ((F.cliques \ F.activeCliques).filter fun R => e.val ⊆ R.val).card ≤ 2 := by
  by_cases heB : e ∈ B
  · have hempty : (F.cliques \ F.activeCliques).filter (fun R => e.val ⊆ R.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro R hR
      exact disjoint_left.mp (F.inactive_avoids (mem_filter.mp hR).1)
        ((mem_cliqueEdges _ _).mpr (mem_filter.mp hR).2) heB
    rw [hempty, card_empty]
    omega
  · exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
      (F.clique_count_outside hpair e heB)

theorem EliminationFamily.activeCliques_card_le (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) :
    F.activeCliques.card ≤ Fintype.card I * (2 * (q.choose (r + 1) - 1)) := by
  rw [F.activeCliques_eq hpair]
  calc
    _ ≤ ∑ i, (mapGraph (F.embedding i) (S.eliminationNear N)).card := card_biUnion_le
    _ = Fintype.card I * (S.eliminationNear N).card := by
      simp only [mapGraph, card_map, sum_const, card_univ, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_left _ (S.eliminationNear_card_le hpair)

theorem EliminationFamily.active_support (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) :
    cliqueSupport (r + 1) F.activeCliques ⊆ F.activeGraph := by
  intro e he
  by_cases heB : e ∈ B
  · exact mem_union_left _ heB
  · obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
    rw [F.activeCliques_eq hpair] at hR
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
    obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
    have hem : e ∈ mapGraph (F.embedding i)
        (cliqueSupport (r + 1) (S.eliminationNear N)) :=
      mapGraph_mono _ (subset_biUnion_of_mem (fun R => cliqueEdges (r + 1) R) hR₀)
        (by rwa [map_cliqueEdges])
    obtain ⟨f, hf, rfl⟩ := (mem_mapGraph _ _ _).mp hem
    have hnew := F.copy_new_of_notMem hpair i (mapBlock (F.embedding i) f)
      ((mem_mapGraph _ _ _).mpr ⟨f, S.eliminationNear_support_subset N hf, rfl⟩) heB
    obtain ⟨g, hg, hgf⟩ := (mem_mapGraph _ _ _).mp hnew
    have hgeq : g = f := mapBlock_injective (F.embedding i) hgf
    subst g
    exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
      (mem_mapGraph _ _ _).mpr ⟨f, mem_filter.mpr ⟨hf, (mem_filter.mp hg).2⟩, rfl⟩⟩)

end Arxiv2411_18291
