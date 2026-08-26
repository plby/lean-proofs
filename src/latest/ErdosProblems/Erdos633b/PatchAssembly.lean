import ErdosProblems.Erdos633b.EdgeSplit
import ErdosProblems.Erdos633b.Similarity
import ErdosProblems.Erdos633b.TriquadraticTiling

/-! Congruent quadratic patches and two-region geometric assembly. -/

namespace Erdos633b

namespace Patch

noncomputable def glueTwo {R : Triangle} {S U : Set Plane} {n m : ℕ}
    (d : Patch R S n) (e : Patch R U m)
    (hd : Disjoint (interior S) (interior U)) : Patch R (S ∪ U) (n + m) := by
  let sets : Fin 2 → Set Plane := ![S, U]
  let counts : Fin 2 → ℕ := ![n, m]
  have patches : ∀ i, Patch R (sets i) (counts i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact d
    · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      exact e
  have hdis : Pairwise fun i j => Disjoint (interior (sets i)) (interior (sets j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  have hu : (⋃ i, sets i) = S ∪ U := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have hc : (∑ i, counts i) = n + m := by simp [Fin.sum_univ_two, counts]
  have result := glue R sets counts patches hdis
  rwa [hu, hc] at result

end Patch

noncomputable def quadratic_patch_congruent (R S : Triangle) (n : ℕ) (hn : 0 < n)
    (hside : ∀ i, S.side i = (n : ℝ) * R.side i) : Patch R S.support (n ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let U := R.homothetic (R.points 0) n hnr.ne'
  have hs (i : Fin 3) : U.side i = S.side i := by
    change Triangle.side ((R.dilate n hnr.ne').move _) i = _
    rw [Triangle.side_move, Triangle.side_dilate, abs_of_pos hnr]
    exact (hside i).symm
  have hdist := U.distances_of_sides S hs
  let g := U.vertexIsometry S hdist
  have hg : g '' U.support = S.support := by
    rw [← U.support_move g, U.move_vertexIsometry S hdist]
  have result := (quadratic_patch R n hn).move g
  change Patch R (g '' U.support) (n ^ 2) at result
  rwa [hg] at result

noncomputable def edge_patch_assemble (T R : Triangle) (w : ℝ) (hw : 0 < w) (hw1 : w < 1)
    (n m : ℕ) (d : Patch R (T.edgeFirst w hw).support n)
    (e : Patch R (T.edgeSecond w hw1).support m) : Tiling T (n + m) := by
  have result := d.glueTwo e (T.edgeParts_disjoint_interiors w hw hw1)
  rw [T.edgeParts_cover w hw hw1] at result
  exact result.toTiling

end Erdos633b
