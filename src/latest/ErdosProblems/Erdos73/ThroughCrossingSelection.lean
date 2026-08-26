import ErdosProblems.Erdos73.HandleFamilySelection
import ErdosProblems.Erdos73.MonotonePairSelection
import ErdosProblems.Erdos73.ThroughHandleCycles

/-! Opposite-side handles yield an odd-cycle packing or a reversed-row crossing family. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

def HasThroughCrossingHandles (k : ℕ) : Prop :=
  ∃ E : ColumnHandleFamily S col (Fin k),
    Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) ∧
    (∀ i, (E.sourceNail i).val.2.val ≤ 1) ∧
    (∀ i, 2 * (c - 1) ≤ (E.targetNail i).val.2.val) ∧
    ∀ i j, i < j → (E.sourceNail i).val.1.val < (E.sourceNail j).val.1.val ∧
      (E.targetNail j).val.1.val < (E.targetNail i).val.1.val

theorem oddPacking_or_through_crossing (F : ColumnHandleFamily S col I)
    (k : ℕ) (hc : k + 2 ≤ c)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 1)
    (ht : ∀ i, 2 * (c - 1) ≤ (F.targetNail i).val.2.val)
    (s : Finset I) (hsize : 2 * twoColorRamseyBound k k ≤ s.card) :
    HasOddCyclePacking k G ∨ ∃ E : ColumnHandleFamily S col (Fin k),
      Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) ∧
      (∀ i, (E.sourceNail i).val.2.val ≤ 1) ∧
      (∀ i, 2 * (c - 1) ≤ (E.targetNail i).val.2.val) ∧
      ∀ i j, i < j → (E.sourceNail i).val.1.val < (E.sourceNail j).val.1.val ∧
        (E.targetNail j).val.1.val < (E.targetNail i).val.1.val := by
  let a (i : I) := (F.sourceNail i).val.1.val
  let b (i : I) := (F.targetNail i).val.1.val
  obtain ⟨down, t, hts, htcard, hdown⟩ := exists_large_finite_fiber s
    (fun i => decide (a i ≤ b i)) (twoColorRamseyBound k k)
    (by simpa only [Fintype.card_bool] using hsize)
  have hbinj : Function.Injective b := by
    intro i j he
    by_contra hn
    exact F.endpoint_row_ne hdis hn true true he
  obtain ⟨f, hf, hft, hmono, hm | hm⟩ := exists_monotone_pair_selection t a b
    (F.sourceRow_injective hdis).injOn hbinj.injOn k htcard
  · let E := F.reindex f hf
    apply Or.inl
    cases down with
    | true =>
      apply E.oddCyclePacking_of_through_ordered true (by omega)
        (fun i => of_decide_eq_true (hdown (f i) (hft i)))
        (fun i => hs (f i)) (fun i => ht (f i))
      intro i j hij
      exact ⟨hmono hij, hm hij⟩
    | false =>
      let D := E.reverseWhere (fun _ => true)
      refine D.oddCyclePacking_of_through_ordered false (by omega) ?_
        (fun i => ht (f i)) (fun i => hs (f i)) ?_
      · intro i
        have hh := hdown (f i) (hft i)
        simp only [decide_eq_false_iff_not] at hh
        exact (lt_of_not_ge hh).le
      · intro i j hij
        exact ⟨hm hij, hmono hij⟩
  · let E := F.reindex f hf
    exact Or.inr ⟨E, (fun _ _ hij => hdis (hf.ne hij)),
      (fun i => hs (f i)), (fun i => ht (f i)), fun i j hij => ⟨hmono hij, hm hij⟩⟩

end
end Erdos73.ColumnHandleFamily
