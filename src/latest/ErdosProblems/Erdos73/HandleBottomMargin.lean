import ErdosProblems.Erdos73.HandleRowSelection
import ErdosProblems.Erdos73.OrderedFiniteSelection
import ErdosProblems.Erdos73.PathCongestion

/-! Reserve a bottom wall margin by discarding only one handle per forbidden row. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

theorem disjointFamily_meeting_card_le {I W : Type*} [DecidableEq I] [DecidableEq W]
    (s : Finset I) (R : I → Finset W) (X : Finset W)
    (hR : Pairwise (fun i j => Disjoint (R i) (R j))) :
    (s.filter (fun i => ¬ Disjoint (R i) X)).card ≤ X.card := by
  let bad := s.filter (fun i => ¬ Disjoint (R i) X)
  have hh := card_le_mul_of_hits_with_congestion bad R X 1
    (fun i hi => Finset.not_disjoint_iff.mp (mem_filter.mp hi).2) (by
      intro x hx
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      exact Finset.disjoint_left.mp (hR hij) (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  simpa only [Nat.mul_one] using hh

def bottomWallRows (r D : ℕ) : Finset (Fin r) := univ.filter (fun i => r - D ≤ i.val)

theorem bottomWallRows_card_le (r D : ℕ) : (bottomWallRows r D).card ≤ D := by
  let f (i : bottomWallRows r D) : Fin D :=
    ⟨i.val.val - (r - D), by
      have hi := (mem_filter.mp i.property).2
      have hh := i.val.isLt
      omega⟩
  have hf : Function.Injective f := by
    intro i j he
    have hi := (mem_filter.mp i.property).2
    have hj := (mem_filter.mp j.property).2
    have hh := congrArg Fin.val he
    change i.val.val - (r - D) = j.val.val - (r - D) at hh
    exact Subtype.ext (Fin.ext (by omega))
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

namespace ColumnHandleFamily
variable {V : Type*} {G : SimpleGraph V} {c r K : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem exists_ordered_avoiding_bottom (F : ColumnHandleFamily S col (Fin K))
    (hR : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (N D : ℕ) (hsize : N + D ≤ K) :
    ∃ f : Fin N → Fin K, StrictMono f ∧
      ∀ i, (F.sourceNail (f i)).val.1.val < r - D ∧
        (F.targetNail (f i)).val.1.val < r - D := by
  let good := univ.filter (fun i : Fin K => Disjoint (F.rows i) (bottomWallRows r D))
  have hbad := disjointFamily_meeting_card_le univ F.rows (bottomWallRows r D) hR
  have htail := bottomWallRows_card_le r D
  have htotal := card_filter_add_card_filter_not (s := (univ : Finset (Fin K)))
    (fun i : Fin K => Disjoint (F.rows i) (bottomWallRows r D))
  have hgood : N ≤ good.card := by
    simp only [card_univ, Fintype.card_fin] at htotal
    change good.card + _ = K at htotal
    omega
  obtain ⟨f, _, hf, hmono⟩ := exists_rank_ordered_selection good Fin.val
    Fin.val_injective.injOn N hgood
  refine ⟨f, fun i j hij => hmono hij, ?_⟩
  intro i
  have hdis := (mem_filter.mp (hf i)).2
  have hsrc : (F.sourceNail (f i)).val.1 ∈ F.rows (f i) := mem_insert_self _ _
  have htgt : (F.targetNail (f i)).val.1 ∈ F.rows (f i) := mem_insert_of_mem (mem_singleton_self _)
  constructor
  · by_contra hh
    exact Finset.disjoint_left.mp hdis hsrc (mem_filter.mpr ⟨mem_univ _, by omega⟩)
  · by_contra hh
    exact Finset.disjoint_left.mp hdis htgt (mem_filter.mpr ⟨mem_univ _, by omega⟩)

end ColumnHandleFamily
end
end Erdos73
