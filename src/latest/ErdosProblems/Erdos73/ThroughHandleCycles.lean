import ErdosProblems.Erdos73.BrickThroughHooks
import ErdosProblems.Erdos73.HandleReturnCycles

/-! Increasing opposite-side endpoint rows close by disjoint staircase paths. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r k : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddCyclePacking_of_through_ordered (F : ColumnHandleFamily S col (Fin k))
    (goRight : Bool) (hc : k + 1 < c)
    (hrow : ∀ i, (F.sourceNail i).val.1.val ≤ (F.targetNail i).val.1.val)
    (hs : ∀ i, if goRight then (F.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.sourceNail i).val.2.val)
    (ht : ∀ i, if goRight then 2 * (c - 1) ≤ (F.targetNail i).val.2.val
      else (F.targetNail i).val.2.val ≤ 1)
    (horder : ∀ i l, i < l →
      (F.sourceNail i).val.1.val < (F.sourceNail l).val.1.val ∧
      (F.targetNail i).val.1.val < (F.targetNail l).val.1.val) :
    HasOddCyclePacking k G := by
  let j (i : Fin k) := if goRight then k - i.val else i.val + 1
  have hj (i : Fin k) : 0 < j i := by
    have hi := i.isLt
    dsimp only [j]
    split_ifs <;> omega
  have hjc (i : Fin k) : j i + 1 < c := by
    have hi := i.isLt
    dsimp only [j]
    split_ifs <;> omega
  have hsc (i : Fin k) : if goRight then (F.sourceNail i).val.2.val ≤ 2 * j i + 1
      else 2 * j i ≤ (F.sourceNail i).val.2.val := by
    have hh := hs i
    have hi := i.isLt
    cases goRight <;> simp only [j, Bool.false_eq_true, ↓reduceIte] at hh ⊢ <;> omega
  have htc (i : Fin k) : if goRight then 2 * j i ≤ (F.targetNail i).val.2.val
      else (F.targetNail i).val.2.val ≤ 2 * j i + 1 := by
    have hh := ht i
    have hi := i.isLt
    cases goRight <;> simp only [j, Bool.false_eq_true, ↓reduceIte] at hh ⊢ <;> omega
  have hex (i : Fin k) := S.exists_through_hook_path goRight (F.sourceNail i) (F.targetNail i)
    (hrow i) (j i) (hj i) (hjc i) (hsc i) (htc i)
  choose Q hQs hQt hQ using hex
  apply F.oddCyclePacking_of_disjoint_return_paths Q
    (fun i => (hQs i).trans (F.source_eq i).symm)
    (fun i => (hQt i).trans (F.target_eq i).symm)
    (fun i => (hQ i).trans (S.supportOver_mono (subset_univ _)))
  have hdis {i l : Fin k} (hil : i < l) :
      Disjoint (brickThroughHook (c := c) (r := r) goRight
        (F.sourceNail i).val.1.val (F.targetNail i).val.1.val (j i))
        (brickThroughHook goRight (F.sourceNail l).val.1.val (F.targetNail l).val.1.val (j l)) := by
    obtain ⟨ha, hb⟩ := horder i l hil
    apply brickThroughHook_disjoint (hrow i) (hrow l) ha hb
    have hi := i.isLt
    have hl := l.isLt
    change i.val < l.val at hil
    cases goRight <;> simp only [j, Bool.false_eq_true, ↓reduceIte] <;> omega
  intro i l hil
  rcases lt_or_gt_of_ne hil with h | h
  · exact (S.supportOver_disjoint (hdis h)).mono (hQ i) (hQ l)
  · exact ((S.supportOver_disjoint (hdis h)).mono (hQ l) (hQ i)).symm

end
end Erdos73.ColumnHandleFamily
