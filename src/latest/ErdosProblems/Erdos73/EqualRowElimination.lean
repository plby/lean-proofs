import ErdosProblems.Erdos73.HandleFamilySelection
import ErdosProblems.Erdos73.SameRowHandleCycles

/-! Equal-row handles either already pack odd cycles or can be discarded at bounded cost. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddPacking_or_strict_row_selection (F : ColumnHandleFamily S col I)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (hrow : ∀ i, (F.sourceNail i).val.1.val ≤ (F.targetNail i).val.1.val)
    (s : Finset I) (k m : ℕ) (hsize : k - 1 + m ≤ s.card) :
    HasOddCyclePacking k G ∨ ∃ f : Fin m → I,
      Function.Injective f ∧ (∀ i, f i ∈ s) ∧
      ∀ i, (F.sourceNail (f i)).val.1.val < (F.targetNail (f i)).val.1.val := by
  let e := s.filter (fun i => (F.sourceNail i).val.1.val = (F.targetNail i).val.1.val)
  by_cases he : k ≤ e.card
  · obtain ⟨f, hf, hfe, _⟩ := exists_rank_ordered_selection e
      (fun i => (F.sourceNail i).val.1.val) (F.sourceRow_injective hdis).injOn k he
    apply Or.inl
    apply (F.reindex f hf).oddCyclePacking_of_same_row
    · intro i
      exact Fin.ext (mem_filter.mp (hfe i)).2
    · intro i j hij heq
      exact (hf.ne hij) (F.sourceRow_injective hdis (congrArg Fin.val heq))
  · have hes : e ⊆ s := filter_subset _ _
    have hcard := card_sdiff_add_card_eq_card hes
    have hlarge : m ≤ (s \ e).card := by omega
    obtain ⟨f, hf, hft, _⟩ := exists_rank_ordered_selection (s \ e)
      (fun i => (F.sourceNail i).val.1.val) (F.sourceRow_injective hdis).injOn m hlarge
    refine Or.inr ⟨f, hf, fun i => (mem_sdiff.mp (hft i)).1, ?_⟩
    intro i
    have hh := hrow (f i)
    have hne : (F.sourceNail (f i)).val.1.val ≠ (F.targetNail (f i)).val.1.val := by
      intro heq
      exact (mem_sdiff.mp (hft i)).2 (mem_filter.mpr ⟨(mem_sdiff.mp (hft i)).1, heq⟩)
    omega

end
end Erdos73.ColumnHandleFamily
