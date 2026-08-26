import ErdosProblems.Erdos73.BrickHookRegions
import ErdosProblems.Erdos73.HandleReturnCycles

/-! Series and nested handles on the left boundary give integral odd-cycle packings. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r k : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddCyclePacking_of_left_hooks (F : ColumnHandleFamily S col (Fin k))
    (j : Fin k → ℕ) (hj : ∀ i, 0 < j i) (hjc : ∀ i, j i + 1 < c)
    (hrow : ∀ i, (F.sourceNail i).val.1.val ≤ (F.targetNail i).val.1.val)
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 2 * j i + 1)
    (ht : ∀ i, (F.targetNail i).val.2.val ≤ 2 * j i + 1)
    (hdis : Pairwise (fun i l => Disjoint
      (brickLeftHook (c := c) (r := r) (F.sourceNail i).val.1.val
        (F.targetNail i).val.1.val (j i))
      (brickLeftHook (F.sourceNail l).val.1.val (F.targetNail l).val.1.val (j l)))) :
    HasOddCyclePacking k G := by
  have hex (i : Fin k) := S.exists_left_hook_path (F.sourceNail i) (F.targetNail i)
    (hrow i) (j i) (hj i) (hjc i) (hs i) (ht i)
  choose Q hQs hQt hQ using hex
  apply F.oddCyclePacking_of_disjoint_return_paths Q
    (fun i => (hQs i).trans (F.source_eq i).symm)
    (fun i => (hQt i).trans (F.target_eq i).symm)
    (fun i => (hQ i).trans (S.supportOver_mono (subset_univ _)))
  intro i l hil
  exact (S.supportOver_disjoint (hdis hil)).mono (hQ i) (hQ l)

theorem oddCyclePacking_of_left_series (F : ColumnHandleFamily S col (Fin k))
    (hc : 3 ≤ c)
    (hrow : ∀ i, (F.sourceNail i).val.1.val ≤ (F.targetNail i).val.1.val)
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 1)
    (ht : ∀ i, (F.targetNail i).val.2.val ≤ 1)
    (hseries : ∀ i l, i < l → (F.targetNail i).val.1.val < (F.sourceNail l).val.1.val) :
    HasOddCyclePacking k G := by
  apply F.oddCyclePacking_of_left_hooks (fun _ => 1) (fun _ => by omega)
    (fun _ => by omega) hrow (fun i => by have hh := hs i; omega)
    (fun i => by have hh := ht i; omega)
  intro i l hil
  rcases lt_or_gt_of_ne hil with h | h
  · exact brickLeftHook_disjoint_series (hrow i) (hrow l) (hseries i l h)
  · exact (brickLeftHook_disjoint_series (hrow l) (hrow i) (hseries l i h)).symm

theorem oddCyclePacking_of_left_nested (F : ColumnHandleFamily S col (Fin k))
    (hc : k + 1 < c)
    (hrow : ∀ i, (F.sourceNail i).val.1.val ≤ (F.targetNail i).val.1.val)
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 1)
    (ht : ∀ i, (F.targetNail i).val.2.val ≤ 1)
    (hnested : ∀ i l, i < l →
      (F.sourceNail i).val.1.val < (F.sourceNail l).val.1.val ∧
      (F.targetNail l).val.1.val < (F.targetNail i).val.1.val) :
    HasOddCyclePacking k G := by
  let j (i : Fin k) := k - i.val
  have hj (i : Fin k) : 0 < j i := by have hi := i.isLt; dsimp [j]; omega
  have hjc (i : Fin k) : j i + 1 < c := by dsimp [j]; omega
  apply F.oddCyclePacking_of_left_hooks j hj hjc hrow
    (fun i => by have hh := hs i; omega) (fun i => by have hh := ht i; omega)
  intro i l hil
  rcases lt_or_gt_of_ne hil with h | h
  · obtain ⟨ha, hb⟩ := hnested i l h
    apply brickLeftHook_disjoint_nested ha (hrow l) hb
    have hi := i.isLt
    have hl := l.isLt
    change i.val < l.val at h
    dsimp [j]
    omega
  · obtain ⟨ha, hb⟩ := hnested l i h
    apply Disjoint.symm
    apply brickLeftHook_disjoint_nested ha (hrow i) hb
    have hi := i.isLt
    have hl := l.isLt
    change l.val < i.val at h
    dsimp [j]
    omega

end
end Erdos73.ColumnHandleFamily
