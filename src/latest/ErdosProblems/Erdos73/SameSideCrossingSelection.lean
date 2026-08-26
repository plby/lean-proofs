import ErdosProblems.Erdos73.PureRowFamilies
import ErdosProblems.Erdos73.LeftHandleCycles
import ErdosProblems.Erdos73.RightHandleCycles

/-! All noncrossing same-side pure families are discharged by actual wall routing. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

def HasSameSideCrossingHandles (leftSide : Bool) (k : ℕ) : Prop :=
  ∃ E : ColumnHandleFamily S col (Fin k),
    Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) ∧
    (∀ i, (E.sourceNail i).val.1.val < (E.targetNail i).val.1.val) ∧
    (∀ i, if leftSide then (E.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (E.sourceNail i).val.2.val) ∧
    (∀ i, if leftSide then (E.targetNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (E.targetNail i).val.2.val) ∧
    ∀ i j, i < j → (E.sourceNail i).val.1.val < (E.sourceNail j).val.1.val ∧
      (E.sourceNail j).val.1.val < (E.targetNail i).val.1.val ∧
      (E.targetNail i).val.1.val < (E.targetNail j).val.1.val

theorem oddPacking_or_sameSide_crossing (F : ColumnHandleFamily S col I)
    (leftSide : Bool) (k : ℕ) (hc : k + 2 ≤ c)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (hrow : ∀ i, (F.sourceNail i).val.1.val < (F.targetNail i).val.1.val)
    (hs : ∀ i, if leftSide then (F.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.sourceNail i).val.2.val)
    (ht : ∀ i, if leftSide then (F.targetNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.targetNail i).val.2.val)
    (s : Finset I) (hsize : pureEndpointPairBound k ≤ s.card) :
    HasOddCyclePacking k G ∨ ∃ E : ColumnHandleFamily S col (Fin k),
      Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) ∧
      (∀ i, (E.sourceNail i).val.1.val < (E.targetNail i).val.1.val) ∧
      (∀ i, if leftSide then (E.sourceNail i).val.2.val ≤ 1
        else 2 * (c - 1) ≤ (E.sourceNail i).val.2.val) ∧
      (∀ i, if leftSide then (E.targetNail i).val.2.val ≤ 1
        else 2 * (c - 1) ≤ (E.targetNail i).val.2.val) ∧
      ∀ i j, i < j → (E.sourceNail i).val.1.val < (E.sourceNail j).val.1.val ∧
        (E.sourceNail j).val.1.val < (E.targetNail i).val.1.val ∧
        (E.targetNail i).val.1.val < (E.targetNail j).val.1.val := by
  by_cases hk : k = 0
  · subst k
    exact Or.inl (hasOddCyclePacking_zero G)
  obtain ⟨f, hf, _, hmono, shape, hpure⟩ :=
    F.exists_pure_row_ordered_selection hdis hrow s k hsize
  let E := F.reindex f hf
  have hEs (i : Fin k) := hs (f i)
  have hEt (i : Fin k) := ht (f i)
  have hEr (i : Fin k) : (E.sourceNail i).val.1.val ≤ (E.targetNail i).val.1.val :=
    (hrow (f i)).le
  cases shape with
  | series =>
    have hseries (i j : Fin k) (hij : i < j) :
        (E.targetNail i).val.1.val < (E.sourceNail j).val.1.val := by
      have hh := hpure i j hij
      have hm := hmono hij
      dsimp only at hm
      have hr := hrow (f j)
      dsimp only [EndpointPairShape.Rel] at hh
      change (F.targetNail (f i)).val.1.val < (F.sourceNail (f j)).val.1.val
      omega
    apply Or.inl
    cases leftSide
    · exact E.oddCyclePacking_of_right_series (by omega) hEr hEs hEt hseries
    · exact E.oddCyclePacking_of_left_series (by omega) hEr hEs hEt hseries
  | nested =>
    have hnested (i j : Fin k) (hij : i < j) :
        (E.sourceNail i).val.1.val < (E.sourceNail j).val.1.val ∧
        (E.targetNail j).val.1.val < (E.targetNail i).val.1.val := by
      have hh := hpure i j hij
      have hm := hmono hij
      dsimp only at hm
      dsimp only [EndpointPairShape.Rel] at hh
      change (F.sourceNail (f i)).val.1.val < (F.sourceNail (f j)).val.1.val ∧
        (F.targetNail (f j)).val.1.val < (F.targetNail (f i)).val.1.val
      omega
    apply Or.inl
    cases leftSide
    · exact E.oddCyclePacking_of_right_nested (by omega) hEr hEs hEt hnested
    · exact E.oddCyclePacking_of_left_nested (by omega) hEr hEs hEt hnested
  | crossing =>
    refine Or.inr ⟨E, (fun _ _ hij => hdis (hf.ne hij)),
      (fun i => hrow (f i)), hEs, hEt, ?_⟩
    intro i j hij
    have hh := hpure i j hij
    have hm := hmono hij
    dsimp only at hm
    dsimp only [EndpointPairShape.Rel] at hh
    change (F.sourceNail (f i)).val.1.val < (F.sourceNail (f j)).val.1.val ∧
      (F.sourceNail (f j)).val.1.val < (F.targetNail (f i)).val.1.val ∧
      (F.targetNail (f i)).val.1.val < (F.targetNail (f j)).val.1.val
    omega

end
end Erdos73.ColumnHandleFamily
