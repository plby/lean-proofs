import ErdosProblems.Erdos547.LabelledEmbedding

/-!
# Rooted tree embedding in two pools with large cross degrees
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*} [Fintype U]

theorem exists_rooted_copy_of_cross_degrees (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (A B : Finset V) (hdis : Disjoint A B)
    (hA : ∀ z ∈ A, Fintype.card U ≤ degreeIn G B z)
    (hB : ∀ z ∈ B, Fintype.card U ≤ degreeIn G A z)
    (r : U) (z : V) (hz : z ∈ A) :
    ∃ f : T.Copy G, f r = z ∧ ∀ u,
      (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  classical
  let col : T.Coloring (Fin 2) := hT.coloringTwoOfVert r
  let pool : Fin 2 → Finset V := fun i ↦ if i = 0 then A else B
  have hcol (u : U) : col u = 0 ↔ T.dist r u % 2 = 0 := by
    change (⟨T.dist r u % 2, _⟩ : Fin 2) = 0 ↔ _
    exact Fin.ext_iff
  have hroot : col r = 0 := (hcol r).mpr (by simp)
  have hsep (i j : Fin 2) (hij : i ≠ j) : Disjoint (pool i) (pool j) := by
    fin_cases i <;> fin_cases j <;> simp_all [pool, disjoint_comm]
  have hdeg (u v : U) (huv : T.Adj u v) (x : V) (hx : x ∈ pool (col u)) :
      ((Finset.univ : Finset U).filter fun y ↦ col y = col v).card ≤
        degreeIn G (pool (col v)) x := by
    have hcount : ((Finset.univ : Finset U).filter fun y ↦ col y = col v).card ≤
        Fintype.card U := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq Finset.card_univ
    have hne := col.valid huv
    by_cases hu : col u = 0
    · have hv : col v ≠ 0 := fun hv ↦ hne (hu.trans hv.symm)
      change x ∈ (if col u = 0 then A else B) at hx
      rw [if_pos hu] at hx
      change _ ≤ degreeIn G (if col v = 0 then A else B) x
      rw [if_neg hv]
      exact hcount.trans (hA x hx)
    · have hv : col v = 0 := by
        by_contra hv
        exact hne ((Fin.eq_one_of_ne_zero _ hu).trans (Fin.eq_one_of_ne_zero _ hv).symm)
      change x ∈ (if col u = 0 then A else B) at hx
      rw [if_neg hu] at hx
      change _ ≤ degreeIn G (if col v = 0 then A else B) x
      rw [if_pos hv]
      exact hcount.trans (hB x hx)
  obtain ⟨f, hf, hfp⟩ := exists_copy_of_labelled_degree T G hT (fun u ↦ col u) pool hsep
    (fun u v huv x hx ↦ by simpa only [col, pool] using hdeg u v huv x hx) r z
    (by simpa only [pool, hroot, if_true] using hz)
  refine ⟨f, hf, fun u ↦ ⟨?_, ?_⟩⟩
  · intro hu
    simpa only [pool, if_pos ((hcol u).mpr hu)] using hfp u
  · intro hu
    simpa only [pool, if_neg (fun hh ↦ hu ((hcol u).mp hh))] using hfp u

end Erdos547

#print axioms Erdos547.exists_rooted_copy_of_cross_degrees
