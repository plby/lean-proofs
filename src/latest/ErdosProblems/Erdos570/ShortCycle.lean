/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EvenLeafCycle
import ErdosProblems.Erdos570.Support

/-!
# Small extension and quadrilateral lemmas

These are the two local constructions used in the exceptional `C₄`
induction: four rectangle edges close to a quadrilateral, and a blue copy of
a one-vertex deletion extends across a blue apex.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Four distinct rectangle corners with all four cross edges contain the
standard four-cycle. -/
theorem cycleGraph_four_isContained_of_rectangle
    {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hcb : G.Adj c b)
    (hcd : G.Adj c d) (had : G.Adj a d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    SimpleGraph.cycleGraph 4 ⊑ G := by
  let p : Fin 2 → V := ![a, c]
  let w : Fin 2 → V := ![b, d]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  have hw : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [w]
  have hdisj : ∀ i j, p i ≠ w j := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [p, w] using hab.ne
    · simpa [p, w] using had.ne
    · simpa [p, w] using hcb.ne
    · simpa [p, w] using hcd.ne
  have hcross : ∀ i j, G.Adj (p i) (w j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [p, w] using hab
    · simpa [p, w] using had
    · simpa [p, w] using hcb
    · simpa [p, w] using hcd
  simpa using cycleGraph_even_isContained_of_complete_cross
    (G := G) (h := 2) (by omega) p w hp hw hdisj hcross

/-- A specified copy of `H-v` extends across a fresh apex when the apex has
all blue adjacencies required at `v`. -/
theorem isContained_of_deleteVertex_copy_and_apex_on_copy
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) (v : Fin H.vertexCount)
    (C : SimpleGraph W) (S : Finset W) (w : W)
    (hwS : w ∉ S)
    (copy : SimpleGraph.Copy
      (H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ)
      (Cᶜ.induce (S : Set W)))
    (hblue : ∀ x : {x : Fin H.vertexCount //
        x ∈ ({v} : Set (Fin H.vertexCount))ᶜ},
      H.graph.Adj v x.1 → Cᶜ.Adj w (copy x).1) :
    H.graph ⊑ Cᶜ := by
  classical
  let D := {x : Fin H.vertexCount // x ≠ v}
  let lift : D → {x : Fin H.vertexCount //
      x ∈ ({v} : Set (Fin H.vertexCount))ᶜ} := fun x ↦ ⟨x.1, by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2⟩
  let fD : D → W := fun x ↦ copy (lift x)
  have hfD : Function.Injective fD := by
    intro x y hxy
    dsimp only [fD] at hxy
    have hlift : lift x = lift y := copy.injective (Subtype.ext hxy)
    apply Subtype.ext
    exact congrArg Subtype.val hlift
  have hfDmem (x : D) : fD x ∈ S := (copy _).2
  let f : Fin H.vertexCount → W := fun x ↦ if hx : x = v then w else fD ⟨x, hx⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact hx.trans hy.symm
    · dsimp only [f] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exact (hwS (hxy ▸ hfDmem ⟨y, hy⟩)).elim
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exact (hwS (hxy ▸ hfDmem ⟨x, hx⟩)).elim
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (hfD hxy)
  let hom : H.graph →g Cᶜ :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · subst x
          subst y
          exact (hxy.ne rfl).elim
        · subst x
          dsimp only [f]
          rw [dif_pos rfl, dif_neg hy]
          exact hblue (lift ⟨y, hy⟩) hxy
        · subst y
          dsimp only [f]
          rw [dif_neg hx, dif_pos rfl]
          exact (hblue (lift ⟨x, hx⟩) hxy.symm).symm
        · dsimp only [f]
          rw [dif_neg hx, dif_neg hy]
          exact copy.toHom.map_adj hxy }
  exact ⟨hom.toCopy hf⟩

/-- A copy of `H-v` inside `S` extends to a copy of `H` when a fresh apex is
blue-adjacent to every vertex of `S`. -/
theorem isContained_of_deleteVertex_copy_and_apex
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) (v : Fin H.vertexCount)
    (C : SimpleGraph W) (S : Finset W) (w : W)
    (hwS : w ∉ S)
    (hcopy : H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑
      Cᶜ.induce (S : Set W))
    (hblue : ∀ x ∈ S, Cᶜ.Adj w x) :
    H.graph ⊑ Cᶜ := by
  obtain ⟨copy⟩ := hcopy
  apply isContained_of_deleteVertex_copy_and_apex_on_copy
    H v C S w hwS copy
  intro x _
  exact hblue (copy x).1 (copy x).2

end Erdos570
