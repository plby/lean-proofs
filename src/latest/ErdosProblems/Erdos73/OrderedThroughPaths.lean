import ErdosProblems.Erdos73.BrickThroughHooks

/-! Order-preserving boundary pairings have disjoint staircases even with mixed vertical directions. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r N : ℕ}

theorem brickThroughHook_row_bounds {dir : Bool} {a b j : ℕ} (hab : a ≤ b)
    {w : ElementaryWallVertex c r} (hw : w ∈ brickThroughHook dir a b j) :
    a ≤ w.val.1.val ∧ w.val.1.val ≤ b := by
  rw [mem_brickThroughHook] at hw
  omega

theorem brickThroughHook_disjoint_series {dir dir' : Bool} {a b j a' b' j' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') (hsep : b < a') :
    Disjoint (brickThroughHook (c := c) (r := r) dir a b j)
      (brickThroughHook dir' a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hh := brickThroughHook_row_bounds hab hw
  have hh' := brickThroughHook_row_bounds hab' hw'
  omega

def orderedThroughRegion (u v : Fin N → ElementaryWallVertex c r) (i : Fin N) :
    Finset (ElementaryWallVertex c r) :=
  if (u i).val.1.val ≤ (v i).val.1.val then
    brickThroughHook true (u i).val.1.val (v i).val.1.val (N - i.val)
  else brickThroughHook false (v i).val.1.val (u i).val.1.val (i.val + 1)

theorem orderedThroughRegion_disjoint (u v : Fin N → ElementaryWallVertex c r)
    (hu : StrictMono (fun i => (u i).val.1.val)) (hv : StrictMono (fun i => (v i).val.1.val)) :
    Pairwise (fun i j => Disjoint (orderedThroughRegion u v i) (orderedThroughRegion u v j)) := by
  have hordered {i j : Fin N} (hij : i < j) :
      Disjoint (orderedThroughRegion u v i) (orderedThroughRegion u v j) := by
    have hU := hu hij
    have hV := hv hij
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hU hV
    dsimp only [orderedThroughRegion]
    split_ifs with h₁ h₂ h₃
    · exact brickThroughHook_disjoint h₁ h₂ hU hV (by change N - j.val < N - i.val; omega)
    · exact brickThroughHook_disjoint_series h₁ (by omega) hV
    · exact brickThroughHook_disjoint_series (by omega) h₃ hU
    · exact brickThroughHook_disjoint (by omega) (by omega) hV hU
        (by change i.val + 1 < j.val + 1; omega)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact hordered hh
  · exact (hordered hh).symm

theorem exists_orderedThroughRegion_path (u v : Fin N → ElementaryWallVertex c r)
    (hleft : ∀ i, (u i).val.2.val ≤ 1) (hright : ∀ i, 2 * (c - 1) ≤ (v i).val.2.val)
    (hc : N + 2 ≤ c) (i : Fin N) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u i ∧ P.target = v i ∧
      P.vertexSet ⊆ orderedThroughRegion u v i := by
  have hi := i.isLt
  have hl := hleft i
  have hr := hright i
  by_cases huv : (u i).val.1.val ≤ (v i).val.1.val
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_through_hook_path true (u i) (v i) huv
      (N - i.val) (by omega) (by omega) (by change (u i).val.2.val ≤ 2 * (N - i.val) + 1; omega)
      (by change 2 * (N - i.val) ≤ (v i).val.2.val; omega)
    refine ⟨P, hs, ht, ?_⟩
    rw [orderedThroughRegion, if_pos huv]
    simpa only [GraphPath.vertexSet, Finset.subset_iff, List.mem_toFinset] using hP
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_through_hook_path false (v i) (u i) (by omega)
      (i.val + 1) (by omega) (by omega) (by change 2 * (i.val + 1) ≤ (v i).val.2.val; omega)
      (by change (u i).val.2.val ≤ 2 * (i.val + 1) + 1; omega)
    refine ⟨P.reverse, by simpa only [GraphPath.reverse_source] using ht,
      by simpa only [GraphPath.reverse_target] using hs, ?_⟩
    rw [orderedThroughRegion, if_neg huv, GraphPath.reverse_vertexSet]
    simpa only [GraphPath.vertexSet, Finset.subset_iff, List.mem_toFinset] using hP

theorem orderedThroughRegion_left_boundary (u v : Fin N → ElementaryWallVertex c r)
    (i : Fin N) {x : ElementaryWallVertex c r} (hx : x ∈ orderedThroughRegion u v i)
    (hleft : x.val.2.val ≤ 1) : x.val.1.val = (u i).val.1.val := by
  have hi := i.isLt
  dsimp only [orderedThroughRegion] at hx
  split_ifs at hx <;> rw [mem_brickThroughHook] at hx <;>
    simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at hx <;> omega

theorem orderedThroughRegion_right_boundary (u v : Fin N → ElementaryWallVertex c r)
    (hc : N + 2 ≤ c) (i : Fin N) {x : ElementaryWallVertex c r}
    (hx : x ∈ orderedThroughRegion u v i) (hright : 2 * (c - 1) ≤ x.val.2.val) :
    x.val.1.val = (v i).val.1.val := by
  have hi := i.isLt
  dsimp only [orderedThroughRegion] at hx
  split_ifs at hx <;> rw [mem_brickThroughHook] at hx <;>
    simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at hx <;> omega

theorem exists_disjoint_ordered_through_paths (u v : Fin N → ElementaryWallVertex c r)
    (hu : StrictMono (fun i => (u i).val.1.val)) (hv : StrictMono (fun i => (v i).val.1.val))
    (hleft : ∀ i, (u i).val.2.val ≤ 1) (hright : ∀ i, 2 * (c - 1) ≤ (v i).val.2.val)
    (hc : N + 2 ≤ c) :
    ∃ P : Fin N → GraphPath (elementaryWall c r),
      (∀ i, (P i).source = u i ∧ (P i).target = v i) ∧
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) := by
  choose P hs ht hsub using exists_orderedThroughRegion_path u v hleft hright hc
  exact ⟨P, fun i => ⟨hs i, ht i⟩,
    fun i j hij => (orderedThroughRegion_disjoint u v hu hv hij).mono (hsub i) (hsub j)⟩

end
end Erdos73
