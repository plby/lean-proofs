/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleSequence

/-!
# Closing an odd cycle across a complete bipartite pair

The sparse-target argument produces `r+1` copied parent vertices and `r+2`
vertices adjacent to every parent.  Alternating between the two sides and
using one additional edge inside the second side gives `C_(2r+3)`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- Interleave `r+2` vertices `w` with `r+1` vertices `p`, beginning and
ending on the `w` side. -/
def leafAlternatingSequence
    {V : Type*} {r : ℕ} (p : Fin (r + 1) → V)
    (w : Fin (r + 2) → V) (z : Fin (2 * r + 3)) : V :=
  if hz : z.val % 2 = 0 then
    w ⟨z.val / 2, by omega⟩
  else
    p ⟨z.val / 2, by omega⟩

theorem leafAlternatingSequence_injective
    {V : Type*} {r : ℕ} {p : Fin (r + 1) → V}
    {w : Fin (r + 2) → V}
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hdisj : ∀ i j, p i ≠ w j) :
    Function.Injective (leafAlternatingSequence p w) := by
  intro a b hab
  simp only [leafAlternatingSequence] at hab
  split at hab <;> rename_i ha
  · split at hab <;> rename_i hb
    · have hq := congrArg Fin.val (hw hab)
      simp only [Fin.val_mk] at hq
      apply Fin.ext
      omega
    · exact (hdisj _ _ hab.symm).elim
  · split at hab <;> rename_i hb
    · exact (hdisj _ _ hab).elim
    · have hq := congrArg Fin.val (hp hab)
      simp only [Fin.val_mk] at hq
      apply Fin.ext
      omega

@[simp] theorem leafAlternatingSequence_zero
    {V : Type*} {r : ℕ} (p : Fin (r + 1) → V)
    (w : Fin (r + 2) → V) :
    leafAlternatingSequence p w 0 = w 0 := by
  simp [leafAlternatingSequence]

@[simp] theorem leafAlternatingSequence_last
    {V : Type*} {r : ℕ} (p : Fin (r + 1) → V)
    (w : Fin (r + 2) → V) :
    leafAlternatingSequence p w (Fin.last (2 * r + 2)) =
      w (Fin.last (r + 1)) := by
  unfold leafAlternatingSequence
  split <;> rename_i hz
  · congr 1
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_last]
    omega
  · simp only [Fin.val_last] at hz
    omega

/-- Consecutive cross edges, plus the edge joining the two endpoints on the
larger side, contain the required odd cycle. -/
theorem cycleGraph_odd_isContained_of_consecutive_cross
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (p : Fin (r + 1) → V) (w : Fin (r + 2) → V)
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hdisj : ∀ i j, p i ≠ w j)
    (hleft : ∀ i, G.Adj (p i) (w i.castSucc))
    (hright : ∀ i, G.Adj (p i) (w i.succ))
    (hwrap : G.Adj (w 0) (w (Fin.last (r + 1)))) :
    SimpleGraph.cycleGraph (2 * r + 3) ⊑ G := by
  let f := leafAlternatingSequence p w
  have hf : Function.Injective f :=
    leafAlternatingSequence_injective hp hw hdisj
  apply cycleGraph_isContained_of_sequence f hf
  · intro a b hab
    simp only [f, leafAlternatingSequence]
    split <;> rename_i ha
    · split <;> rename_i hb
      · omega
      · let i : Fin (r + 1) := ⟨b.val / 2, by omega⟩
        have hwidx : (⟨a.val / 2, by omega⟩ : Fin (r + 2)) =
            i.castSucc := by
          apply Fin.ext
          simp only [i, Fin.val_mk, Fin.val_castSucc]
          omega
        simpa [i, hwidx] using (hleft i).symm
    · split <;> rename_i hb
      · let i : Fin (r + 1) := ⟨a.val / 2, by omega⟩
        have hwidx : (⟨b.val / 2, by omega⟩ : Fin (r + 2)) =
            i.succ := by
          apply Fin.ext
          simp only [i, Fin.val_mk, Fin.val_succ]
          omega
        simpa [i, hwidx] using hright i
      · omega
  · intro a b ha hb
    have ha0 : a = 0 := Fin.ext ha
    have hblast : b = Fin.last (2 * r + 2) := Fin.ext (by
      simp only [Fin.val_last]
      omega)
    subst a
    subst b
    simpa [f] using hwrap

/-- A complete set of cross edges is a convenient specialization of the
consecutive-cross lemma. -/
theorem cycleGraph_odd_isContained_of_complete_cross
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (p : Fin (r + 1) → V) (w : Fin (r + 2) → V)
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hdisj : ∀ i j, p i ≠ w j)
    (hcross : ∀ i j, G.Adj (p i) (w j))
    (hwrap : G.Adj (w 0) (w (Fin.last (r + 1)))) :
    SimpleGraph.cycleGraph (2 * r + 3) ⊑ G :=
  cycleGraph_odd_isContained_of_consecutive_cross p w hp hw hdisj
    (fun i ↦ hcross i i.castSucc) (fun i ↦ hcross i i.succ) hwrap

end Erdos570
