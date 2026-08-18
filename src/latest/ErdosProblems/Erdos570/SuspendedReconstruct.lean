/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SuspendedPath

/-!
# Reconstructing a shortened suspended path

An embedding of the shortcut graph can be expanded to an embedding of the
original graph whenever the shortcut endpoints are joined by a fresh path of
the original length.  This is the target-side bookkeeping in the long
suspended-path branch.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

@[simp] theorem suspendedInteriorEquiv_apply_val
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (i : Fin t) :
    ((suspendedInteriorEquiv hp i : ↥(suspendedInterior p)) : V) =
      p (suspendedMidIndex i) := by
  rfl

/-- Expanding the shortcut edge along a fresh host path reconstructs the
original suspended path and hence the whole target graph. -/
theorem isContained_of_shortenSuspended_copy_and_path
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (shortenSuspendedGraph G hp) C)
    (q : Fin (t + 2) → W) (hqinj : Function.Injective q)
    (hqadj : ∀ i j : Fin (t + 2), i.val + 1 = j.val → C.Adj (q i) (q j))
    (hqleft : q 0 = copy (suspendedLeft hp))
    (hqright : q (suspendedLastIndex t) = copy (suspendedRight hp))
    (hqfresh : ∀ i : Fin t,
      q (suspendedMidIndex i) ∉ Set.range copy) :
    G ⊑ C := by
  classical
  let e : Fin t ≃ ↥(suspendedInterior p) := suspendedInteriorEquiv hp
  let f : V → W := fun v ↦
    if hv : v ∈ suspendedInterior p then
      q (suspendedMidIndex (e.symm ⟨v, hv⟩))
    else
      copy ⟨v, by simpa using hv⟩
  have heval (i : Fin t) : (e i).1 = p (suspendedMidIndex i) := by
    exact suspendedInteriorEquiv_apply_val hp i
  have hfmid (i : Fin t) :
      f (p (suspendedMidIndex i)) = q (suspendedMidIndex i) := by
    have hi : p (suspendedMidIndex i) ∈ suspendedInterior p := by
      rw [mem_suspendedInterior]
      exact ⟨i, rfl⟩
    dsimp only [f]
    rw [dif_pos hi]
    have heq : (⟨p (suspendedMidIndex i), hi⟩ :
        ↥(suspendedInterior p)) = e i := by
      apply Subtype.ext
      exact (heval i).symm
    rw [heq, e.symm_apply_apply]
  have hfret (x : SuspendedRetained p) : f x.1 = copy x := by
    dsimp only [f]
    have hx : x.1 ∉ suspendedInterior p := by
      exact x.2
    rw [dif_neg hx]
  have hfinj : Function.Injective f := by
    intro v w hvw
    by_cases hv : v ∈ suspendedInterior p <;>
      by_cases hw : w ∈ suspendedInterior p
    · let i := e.symm ⟨v, hv⟩
      let j := e.symm ⟨w, hw⟩
      have hfi : f v = q (suspendedMidIndex i) := by
        dsimp only [f]
        rw [dif_pos hv]
      have hfj : f w = q (suspendedMidIndex j) := by
        dsimp only [f]
        rw [dif_pos hw]
      have hijIndex : suspendedMidIndex i = suspendedMidIndex j :=
        hqinj (hfi.symm.trans (hvw.trans hfj))
      have hij : i = j := by
        apply Fin.ext
        have := Fin.ext_iff.mp hijIndex
        simp only [suspendedMidIndex] at this
        omega
      have hsub : (⟨v, hv⟩ : ↥(suspendedInterior p)) = ⟨w, hw⟩ := by
        calc
          (⟨v, hv⟩ : ↥(suspendedInterior p)) = e i :=
            (e.apply_symm_apply ⟨v, hv⟩).symm
          _ = e j := congrArg e hij
          _ = ⟨w, hw⟩ := e.apply_symm_apply ⟨w, hw⟩
      exact congrArg Subtype.val hsub
    · let i := e.symm ⟨v, hv⟩
      have hfi : f v = q (suspendedMidIndex i) := by
        dsimp only [f]
        rw [dif_pos hv]
      have hfw : f w = copy ⟨w, by simpa using hw⟩ := by
        dsimp only [f]
        rw [dif_neg hw]
      exfalso
      apply hqfresh i
      exact ⟨⟨w, by simpa using hw⟩,
        (hfi.symm.trans (hvw.trans hfw)).symm⟩
    · let j := e.symm ⟨w, hw⟩
      have hfv : f v = copy ⟨v, by simpa using hv⟩ := by
        dsimp only [f]
        rw [dif_neg hv]
      have hfj : f w = q (suspendedMidIndex j) := by
        dsimp only [f]
        rw [dif_pos hw]
      exfalso
      apply hqfresh j
      exact ⟨⟨v, by simpa using hv⟩,
        (hfj.symm.trans (hvw.symm.trans hfv)).symm⟩
    · have hfv : f v = copy ⟨v, by simpa using hv⟩ := by
        dsimp only [f]
        rw [dif_neg hv]
      have hfw : f w = copy ⟨w, by simpa using hw⟩ := by
        dsimp only [f]
        rw [dif_neg hw]
      have hc := copy.injective (hfv.symm.trans (hvw.trans hfw))
      exact congrArg Subtype.val hc
  let hom : G →g C :=
    { toFun := f
      map_rel' := by
        intro v w hvw
        by_cases hv : v ∈ suspendedInterior p <;>
          by_cases hw : w ∈ suspendedInterior p
        · let i := e.symm ⟨v, hv⟩
          let j := e.symm ⟨w, hw⟩
          have hvi : v = p (suspendedMidIndex i) := by
            have hs := e.apply_symm_apply ⟨v, hv⟩
            exact (congrArg Subtype.val hs).symm.trans (heval i)
          have hwj : w = p (suspendedMidIndex j) := by
            have hs := e.apply_symm_apply ⟨w, hw⟩
            exact (congrArg Subtype.val hs).symm.trans (heval j)
          have hadj : G.Adj (p (suspendedMidIndex i)) w := hvi ▸ hvw
          rcases (suspended_neighbor_iff hp i w).mp hadj with hprev | hnext
          · have hidx := Fin.ext_iff.mp (hp.injective (hwj.symm.trans hprev))
            have hji : j.val + 1 = i.val := by
              simpa [suspendedMidIndex, suspendedPrevIndex] using hidx
            rw [hvi, hwj, hfmid, hfmid]
            exact (hqadj (suspendedMidIndex j) (suspendedMidIndex i) (by
              simp [suspendedMidIndex]
              omega)).symm
          · have hidx := Fin.ext_iff.mp (hp.injective (hwj.symm.trans hnext))
            have hij : i.val + 1 = j.val := by
              simpa [suspendedMidIndex, suspendedNextIndex] using hidx.symm
            rw [hvi, hwj, hfmid, hfmid]
            exact hqadj (suspendedMidIndex i) (suspendedMidIndex j) (by
              simp [suspendedMidIndex]
              omega)
        · let i := e.symm ⟨v, hv⟩
          have hvi : v = p (suspendedMidIndex i) := by
            have hs := e.apply_symm_apply ⟨v, hv⟩
            exact (congrArg Subtype.val hs).symm.trans (heval i)
          have hadj : G.Adj (p (suspendedMidIndex i)) w := hvi ▸ hvw
          rcases suspended_mid_adj_retained_cases hp i w hw hadj with
            ⟨hi0, hw0⟩ | ⟨hilast, hwlast⟩
          · rw [hvi, hfmid]
            have hfw : f w = copy (suspendedLeft hp) := by
              rw [hw0]
              exact hfret (suspendedLeft hp)
            rw [hfw, ← hqleft]
            exact (hqadj 0 (suspendedMidIndex i) (by
              simp [suspendedMidIndex, hi0])).symm
          · rw [hvi, hfmid]
            have hfw : f w = copy (suspendedRight hp) := by
              rw [hwlast]
              exact hfret (suspendedRight hp)
            rw [hfw, ← hqright]
            exact hqadj (suspendedMidIndex i) (suspendedLastIndex t) (by
              simp [suspendedMidIndex, suspendedLastIndex]
              omega)
        · let j := e.symm ⟨w, hw⟩
          have hwj : w = p (suspendedMidIndex j) := by
            have hs := e.apply_symm_apply ⟨w, hw⟩
            exact (congrArg Subtype.val hs).symm.trans (heval j)
          have hadj : G.Adj (p (suspendedMidIndex j)) v := hwj ▸ hvw.symm
          rcases suspended_mid_adj_retained_cases hp j v hv hadj with
            ⟨hj0, hv0⟩ | ⟨hjlast, hvlast⟩
          · rw [hwj, hfmid]
            have hfv : f v = copy (suspendedLeft hp) := by
              rw [hv0]
              exact hfret (suspendedLeft hp)
            rw [hfv, ← hqleft]
            exact hqadj 0 (suspendedMidIndex j) (by
              simp [suspendedMidIndex, hj0])
          · rw [hwj, hfmid]
            have hfv : f v = copy (suspendedRight hp) := by
              rw [hvlast]
              exact hfret (suspendedRight hp)
            rw [hfv, ← hqright]
            exact (hqadj (suspendedMidIndex j) (suspendedLastIndex t) (by
              simp [suspendedMidIndex, suspendedLastIndex]
              omega)).symm
        · rw [hfret ⟨v, by simpa using hv⟩, hfret ⟨w, by simpa using hw⟩]
          apply copy.toHom.map_adj
          change (G.induce ((suspendedInterior p : Set V)ᶜ) ⊔
            SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).Adj
              ⟨v, by simpa using hv⟩ ⟨w, by simpa using hw⟩
          rw [SimpleGraph.sup_adj]
          exact Or.inl hvw }
  exact ⟨hom.toCopy hfinj⟩

end Erdos570
