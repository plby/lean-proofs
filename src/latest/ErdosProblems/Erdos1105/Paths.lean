import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- A star with a distinct color on each of its edges, and one common color
on the remaining edges. -/
def starColoring (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin n :=
  EdgeLabeling.mk (fun a b _ ↦ if a.val = 0 then b else if b.val = 0 then a else
    ⟨0, a.pos⟩) (by
      intro a b h
      by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
        simp only [ha, hb, if_true, if_false]
      exact Fin.ext (ha.trans hb.symm))

@[simp] lemma starColoring_apply {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    starColoring n ⟨s(a, b), h⟩ =
      if a.val = 0 then b else if b.val = 0 then a else ⟨0, a.pos⟩ := rfl

lemma starColoring_surjective {n : ℕ} (hn : 3 ≤ n) :
    Function.Surjective (starColoring n) := by
  intro i
  by_cases hi : i.val = 0
  · let a : Fin n := ⟨1, by omega⟩
    let b : Fin n := ⟨2, by omega⟩
    have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
    refine ⟨⟨s(a, b), hab⟩, ?_⟩
    apply Fin.ext
    simp [a, b, hi]
  · let a : Fin n := ⟨0, by omega⟩
    have hai : a ≠ i := by intro h; exact hi (congrArg Fin.val h.symm)
    exact ⟨⟨s(a, i), hai⟩, by simp [a]⟩

private def pathFiveEdge (i : Fin 4) : (pathGraph 5).edgeSet :=
  ⟨s(i.castSucc, i.succ), by simp [SimpleGraph.mem_edgeSet, pathGraph_adj]⟩

lemma starColoring_no_rainbow_path_five (n : ℕ)
    (f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n))) :
    ¬IsRainbow f (starColoring n) := by
  intro hf
  have hne (i j : Fin 5) (hij : i ≠ j) (hj : (f j).val = 0) : (f i).val ≠ 0 := by
    intro hi
    exact hij (f.injective (Fin.ext (hi.trans hj.symm)))
  have hzero (i : Fin 4) (hi : (f i.castSucc).val ≠ 0) (hj : (f i.succ).val ≠ 0) :
      (starColoring n (f.mapEdgeSet (pathFiveEdge i))).val = 0 := by
    have hne' : f i.castSucc ≠ f i.succ :=
      f.injective.ne (Fin.ne_of_val_ne (by simp))
    change (starColoring n ⟨s(f i.castSucc, f i.succ), hne'⟩).val = 0
    simp [hi, hj]
  have hcollision (i j : Fin 4) (hneij : pathFiveEdge i ≠ pathFiveEdge j)
      (hi : (starColoring n (f.mapEdgeSet (pathFiveEdge i))).val = 0)
      (hj : (starColoring n (f.mapEdgeSet (pathFiveEdge j))).val = 0) : False :=
    hneij (hf (Fin.ext (hi.trans hj.symm)))
  by_cases h1 : (f 1).val = 0
  · exact hcollision 2 3 (by decide)
      (hzero 2 (hne 2 1 (by decide) h1) (hne 3 1 (by decide) h1))
      (hzero 3 (hne 3 1 (by decide) h1) (hne 4 1 (by decide) h1))
  by_cases h2 : (f 2).val = 0
  · exact hcollision 0 3 (by decide)
      (hzero 0 (hne 0 2 (by decide) h2) h1)
      (hzero 3 (hne 3 2 (by decide) h2) (hne 4 2 (by decide) h2))
  by_cases h3 : (f 3).val = 0
  · exact hcollision 0 1 (by decide)
      (hzero 0 (hne 0 3 (by decide) h3) h1) (hzero 1 h1 h2)
  · exact hcollision 1 2 (by decide) (hzero 1 h1 h2) (hzero 2 h2 h3)

/-- The star construction gives the proposed lower bound for the first path case. -/
theorem self_le_antiRamseyNum_pathGraph_five {n : ℕ} (hn : 3 ≤ n) :
    n ≤ antiRamseyNum (pathGraph 5) n :=
  le_antiRamseyNum (starColoring n) (starColoring_surjective hn)
    (starColoring_no_rainbow_path_five n)

end Erdos1105
