import ErdosProblems.Erdos577.ChainExchange

/-! A positive two-cycle witness extends to a spanning factor. -/

namespace Erdos577

open Finset

variable {V W : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Two specified quadrilaterals partition the local vertex set. -/
def LocalFactor (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ q ⊆ s, QuadOn G q ∧ QuadOn G (s \ q)

lemma LocalFactor.image [DecidableEq W] {H : SimpleGraph W} {s : Finset V}
    (h : LocalFactor G s) (f : G.Copy H) : LocalFactor H (s.image f) := by
  obtain ⟨q, hqs, hq, hr⟩ := h
  have hinj : Function.Injective (f : V → W) := f.injective
  refine ⟨q.image f, image_subset_image hqs, hq.image f, ?_⟩
  have he : (s \ q).image f = s.image f \ q.image f := image_sdiff s q hinj
  exact he ▸ hr.image f

lemma LocalFactor.partition {s : Finset V} (h : LocalFactor G s) :
    Nonempty (BlockPartition G s) := by
  obtain ⟨q, hqs, hq, hr⟩ := h
  have he : q ∪ (s \ q) = s := union_sdiff_of_subset hqs
  exact ⟨he ▸ (BlockPartition.single hq).union (BlockPartition.single hr)
    disjoint_sdiff_self_right⟩

namespace BlockPartition

variable [Fintype V] {r : Finset V} {k : ℕ}

lemma hasPacking_of_local_factor (p : BlockPartition G (univ \ r))
    (hcard : Fintype.card V = 4 * k) {b : Finset V} (hb : b ∈ p.blocks)
    (h : LocalFactor G (r ∪ b)) : HasPacking G k := by
  obtain ⟨localPart⟩ := h.partition
  have hd : Disjoint ((univ \ r) \ b) (r ∪ b) := by
    apply disjoint_left.mpr
    intro v hv hvr
    rcases mem_union.mp hvr with hr | hb'
    · exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hr
    · exact (mem_sdiff.mp hv).2 hb'
  have he : ((univ \ r) \ b) ∪ (r ∪ b) = univ := by
    ext v
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    tauto
  let p' := (p.remove b hb).union localPart hd
  apply p'.hasPacking_of_card k
  rw [he, card_univ, hcard]

end BlockPartition

lemma TriangleChain.no_local_factor [Fintype V] (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) : ¬LocalFactor G (c.remainder ∪ b) :=
  fun h ↦ hn (c.complementPartition.hasPacking_of_local_factor hcard hb h)

end Erdos577
