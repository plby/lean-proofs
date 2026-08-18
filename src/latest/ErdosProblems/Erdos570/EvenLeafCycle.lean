/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleSequence

/-!
# Even cycles across a complete bipartite pair

The sparse even-cycle branch needs only the elementary fact that two
disjoint sets of `h` vertices with all cross edges contain `C_(2h)`.
The explicit alternating sequence below is convenient for later obstruction
families.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

def evenAlternatingSequence
    {V : Type*} {h : ℕ} (p w : Fin h → V) (z : Fin (2 * h)) : V :=
  if z.val % 2 = 0 then
    p ⟨z.val / 2, by omega⟩
  else
    w ⟨z.val / 2, by omega⟩

theorem evenAlternatingSequence_injective
    {V : Type*} {h : ℕ} {p w : Fin h → V}
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hdisj : ∀ i j, p i ≠ w j) :
    Function.Injective (evenAlternatingSequence p w) := by
  intro a b hab
  simp only [evenAlternatingSequence] at hab
  split at hab <;> rename_i ha
  · split at hab <;> rename_i hb
    · have hq := congrArg Fin.val (hp hab)
      apply Fin.ext
      simp only [Fin.val_mk] at hq
      omega
    · exact (hdisj _ _ hab).elim
  · split at hab <;> rename_i hb
    · exact (hdisj _ _ hab.symm).elim
    · have hq := congrArg Fin.val (hw hab)
      apply Fin.ext
      simp only [Fin.val_mk] at hq
      omega

/-- A complete bipartite graph with two parts of size `h` contains the
alternating cycle of length `2h`. -/
theorem cycleGraph_even_isContained_of_complete_cross
    {V : Type*} {G : SimpleGraph V} {h : ℕ} (hh : 2 ≤ h)
    (p w : Fin h → V)
    (hp : Function.Injective p) (hw : Function.Injective w)
    (hdisj : ∀ i j, p i ≠ w j)
    (hcross : ∀ i j, G.Adj (p i) (w j)) :
    SimpleGraph.cycleGraph (2 * h) ⊑ G := by
  let f := evenAlternatingSequence p w
  have hf : Function.Injective f :=
    evenAlternatingSequence_injective hp hw hdisj
  apply cycleGraph_isContained_of_sequence f hf
  · intro a b hab
    simp only [f, evenAlternatingSequence]
    split <;> rename_i ha
    · split <;> rename_i hb
      · omega
      · exact hcross _ _
    · split <;> rename_i hb
      · exact (hcross _ _).symm
      · omega
  · intro a b ha hb
    let a0 : Fin (2 * h) := ⟨0, by omega⟩
    let blast : Fin (2 * h) := ⟨2 * h - 1, by omega⟩
    have ha0 : a = a0 := Fin.ext ha
    have hblast : b = blast := Fin.ext (by simp [blast]; omega)
    rw [ha0, hblast]
    simp only [f, evenAlternatingSequence, a0, blast, Fin.val_zero, Nat.zero_mod,
      if_pos]
    have hodd : (2 * h - 1) % 2 ≠ 0 := by omega
    rw [if_neg hodd]
    let p0 : Fin h := ⟨0, by omega⟩
    let wlast : Fin h := ⟨h - 1, by omega⟩
    have hidx0 : (⟨0 / 2, by omega⟩ : Fin h) = p0 := by ext <;> simp [p0]
    have hidxlast : (⟨(2 * h - 1) / 2, by omega⟩ : Fin h) = wlast := by
      ext
      simp [wlast]
      omega
    rw [hidx0, hidxlast]
    exact hcross p0 wlast

end Erdos570
