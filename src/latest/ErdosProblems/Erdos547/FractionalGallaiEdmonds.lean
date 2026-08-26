import ErdosProblems.Erdos547.GallaiEdmonds
import ErdosProblems.Erdos547.FractionalExtension

/-!
# Fractional matchings associated with a Gallai–Edmonds partition

The separator matching is completed inside each block. Matched blocks use
near-perfect integral matchings; unmatched nontrivial blocks use the proved
factor-critical averaging construction.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_fractional_avoiding_subsingleton (hG : IsFactorCritical G)
    (K : Set V) (hK : K.Subsingleton) :
    ∃ μ : FractionalMatching G, (∀ v ∈ K, μ.load v = 0) ∧
      (1 < Fintype.card V → ∀ v ∉ K, μ.load v = 1) := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨r, hr⟩ := hne
    obtain ⟨M, hM, hverts⟩ := hG r
    let μ := FractionalMatching.ofMatching M hM
    have hload (v : V) : μ.load v = if v = r then 0 else 1 := by
      change (FractionalMatching.ofMatching M hM).load v = _
      rw [FractionalMatching.ofMatching_load, hverts]
      simp
    refine ⟨μ, ?_, ?_⟩
    · intro v hv
      rw [hload, if_pos (hK hv hr)]
    · intro _ v hv
      rw [hload, if_neg (show v ≠ r from fun hvr ↦ hv (hvr ▸ hr))]
  · by_cases hcard : 1 < Fintype.card V
    · let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
      obtain ⟨μ, hμ⟩ := exists_perfect_fractional_of_factorCritical G hG
      exact ⟨μ, fun v hv ↦ (hne ⟨v, hv⟩).elim, fun _ v _ ↦ hμ v⟩
    · refine ⟨FractionalMatching.zero G, ?_, ?_⟩
      · intro v _
        simp [FractionalMatching.load, FractionalMatching.zero]
      · exact fun hc ↦ (hcard hc).elim

variable [DecidableEq V]

namespace GallaiEdmondsPartition

def nontrivialVertices (D : GallaiEdmondsPartition G) : Finset V :=
  (D.blocks.filter fun C ↦ 1 < C.card).biUnion id

/-- The initial completion needs only the separator matching and edges
internal to nontrivial blocks. -/
def CompletionSupport (D : GallaiEdmondsPartition G) (u v : V) : Prop :=
  D.matching.Adj u v ∨ ∃ C ∈ D.blocks, 1 < C.card ∧ u ∈ C ∧ v ∈ C

theorem exists_fractional_completion (D : GallaiEdmondsPartition G) :
    ∃ μ : FractionalMatching G,
      (∀ u ∈ D.separator, μ.load u = 1) ∧
      (∀ u ∈ D.nontrivialVertices, μ.load u = 1) ∧
      (∀ u v, ¬ D.CompletionSupport u v → μ.weight u v = 0) := by
  classical
  have hex (C : (D.blocks : Set (Finset V))) :
      ∃ μ : FractionalMatching (G.induce (C.val : Set V)),
        (∀ u : (C.val : Set V), u.val ∈ D.matching.verts → μ.load u = 0) ∧
        (1 < C.val.card → ∀ u : (C.val : Set V), u.val ∉ D.matching.verts → μ.load u = 1) := by
    let K : Set (C.val : Set V) := {u | u.val ∈ D.matching.verts}
    have hK : K.Subsingleton := by
      intro u hu v hv
      exact Subtype.ext (D.one_per_block C.val C.property ⟨u.property, hu⟩ ⟨v.property, hv⟩)
    obtain ⟨μ, hzero, hfull⟩ := exists_fractional_avoiding_subsingleton
      (D.factorCritical C.val C.property) K hK
    refine ⟨μ, hzero, ?_⟩
    intro hcard u hu
    apply hfull
    · have hc : Fintype.card (C.val : Set V) = C.val.card :=
        Fintype.card_of_subtype C.val (fun _ ↦ Iff.rfl)
      rw [hc]
      exact hcard
    · exact hu
  choose μ hzero hfull using hex
  let ν := fun C : (D.blocks : Set (Finset V)) ↦ (μ C).liftInduced (C.val : Set V)
  let base := FractionalMatching.ofMatching D.matching D.isMatching
  have hbase (u : V) : base.load u = if u ∈ D.matching.verts then 1 else 0 :=
    FractionalMatching.ofMatching_load D.matching D.isMatching u
  have hsum_at (C : (D.blocks : Set (Finset V))) {u : V} (hu : u ∈ C.val) :
      (∑ B, (ν B).load u) = (μ C).load ⟨u, hu⟩ := by
    rw [Finset.sum_eq_single C]
    · exact FractionalMatching.liftInduced_load_of_mem _ _ hu
    · intro B _ hBC
      apply FractionalMatching.liftInduced_load_of_notMem
      intro huB
      apply hBC
      exact Subtype.ext (D.separates.eq_of_mem_parts B.property C.property huB hu)
    · intro h
      exact (h (Finset.mem_univ C)).elim
  have hsum_sep {u : V} (hu : u ∈ D.separator) : (∑ B, (ν B).load u) = 0 := by
    apply Finset.sum_eq_zero
    intro B _
    apply FractionalMatching.liftInduced_load_of_notMem
    intro huB
    exact Finset.disjoint_left.mp (D.separates.part_disjoint_separator B.property) huB hu
  have hcap : ∀ u, base.load u + (∑ B, (ν B).load u) ≤ 1 := by
    intro u
    by_cases hu : u ∈ D.separator
    · rw [hsum_sep hu, add_zero]
      exact base.load_le_one u
    · obtain ⟨C, hC, huC⟩ := D.separates.exists_part
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩)
      rw [hsum_at ⟨C, hC⟩ huC, hbase]
      split_ifs with hm
      · rw [hzero ⟨C, hC⟩ ⟨u, huC⟩ hm]
        norm_num
      · simpa only [zero_add] using (μ ⟨C, hC⟩).load_le_one ⟨u, huC⟩
  have hνcap : ∀ u, (∑ B, (ν B).load u) ≤ 1 := fun u ↦
    (le_add_of_nonneg_left (base.load_nonneg u)).trans (hcap u)
  let ρ := FractionalMatching.sum ν hνcap
  have hρload (u : V) : ρ.load u = ∑ B, (ν B).load u := FractionalMatching.sum_load_at ν hνcap u
  have hfinal : ∀ u, base.load u + ρ.load u ≤ 1 := by simpa only [hρload] using hcap
  refine ⟨base.add ρ hfinal, ?_, ?_, ?_⟩
  · intro u hu
    rw [FractionalMatching.add_load, hρload, hsum_sep hu, hbase, if_pos (D.covers hu), add_zero]
  · intro u hu
    obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hC, hlarge⟩ := Finset.mem_filter.mp hC
    rw [FractionalMatching.add_load, hρload, hsum_at ⟨C, hC⟩ huC, hbase]
    split_ifs with hm
    · rw [hzero ⟨C, hC⟩ ⟨u, huC⟩ hm]
      norm_num
    · rw [hfull ⟨C, hC⟩ hlarge ⟨u, huC⟩ hm, zero_add]
  · intro u v hnot
    have hm : ¬ D.matching.Adj u v := fun huv ↦ hnot (Or.inl huv)
    have hb : base.weight u v = 0 := by
      simp [base, FractionalMatching.ofMatching, hm]
    change base.weight u v + (∑ C, (ν C).weight u v) = 0
    rw [hb, zero_add]
    apply Finset.sum_eq_zero
    intro C _
    by_cases hu : u ∈ C.val
    · by_cases hv : v ∈ C.val
      · have hnadj : ¬ G.Adj u v := by
          intro huv
          exact hnot (Or.inr ⟨C.val, C.property,
            Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv.ne⟩, hu, hv⟩)
        exact (ν C).supported u v hnadj
      · exact FractionalMatching.liftInduced_weight_eq_zero_of_notMem _ _ (Or.inr hv)
    · exact FractionalMatching.liftInduced_weight_eq_zero_of_notMem _ _ (Or.inl hu)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_fractional_completion
