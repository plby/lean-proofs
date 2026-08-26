import ErdosProblems.Erdos547.FixedVertexEmbedding

/-!
# A tree with two separated roots in the same colour class
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*} [Fintype U]

theorem exists_two_rooted_copy_of_cross_degrees (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (col : T.Coloring (Fin 2))
    (r x : U) (hrx : r ≠ x) (hrcol : col r = 0) (hxcol : col x = 0)
    (hno : ∀ u, T.Adj r u → ¬ T.Adj x u)
    (A B C : Finset V) (hCB : C ⊆ B) (v w : V) (hvw : v ≠ w)
    (hwA : w ∉ A) (hwB : w ∉ B) (hC : ∀ z ∈ C, G.Adj w z)
    (hcardC : Fintype.card U ≤ C.card)
    (hA : ∀ z ∈ A, Fintype.card U ≤ degreeIn G C z)
    (hB : ∀ z ∈ B, Fintype.card U ≤ degreeIn G A z)
    (hv : Fintype.card U ≤ degreeIn G B v) :
    ∃ f : T.Copy G, f r = v ∧ f x = w ∧ ∀ u, u ≠ r → u ≠ x →
      (col u = 0 → f u ∈ A) ∧ (col u ≠ 0 → f u ∈ B) := by
  classical
  let pool : U → Finset V := fun u ↦ if u = r then {v} else if u = x then {w} else
    if col u = 0 then A else if T.Adj r u then B else C
  have hpoolR : pool r = {v} := by simp [pool]
  have hpoolX : pool x = {w} := by simp [pool, hrx.symm]
  have hcol_ne {u y : U} (huy : T.Adj u y) (hu : col u = 0) : col y ≠ 0 :=
    fun hy ↦ col.valid huy (hu.trans hy.symm)
  have hcol_zero {u y : U} (huy : T.Adj u y) (hu : col u ≠ 0) : col y = 0 := by
    by_contra hy
    exact col.valid huy ((Fin.eq_one_of_ne_zero _ hu).trans (Fin.eq_one_of_ne_zero _ hy).symm)
  have hinto (y : U) (hyr : y ≠ r) (hyx : y ≠ x) (hycol : col y ≠ 0)
      (z : V) (hz : Fintype.card U ≤ degreeIn G C z) :
      Fintype.card U ≤ degreeIn G (pool y) z := by
    simp only [pool, if_neg hyr, if_neg hyx, if_neg hycol]
    split_ifs
    · exact hz.trans (degreeIn_mono G hCB z)
    · exact hz
  have havoid (u : U) (hux : u ≠ x) : w ∉ pool u := by
    by_cases hur : u = r
    · subst u
      simpa only [hpoolR, Finset.mem_singleton] using hvw.symm
    · simp only [pool, if_neg hur, if_neg hux]
      split_ifs
      · exact hwA
      · exact hwB
      · exact fun hu ↦ hwB (hCB hu)
  have hdegree (u y : U) (huy : T.Adj u y) (hyr : y ≠ r) (hyx : y ≠ x)
      (z : V) (hz : z ∈ pool u) : Fintype.card U ≤ degreeIn G (pool y) z := by
    by_cases hur : u = r
    · subst u
      have hzv : z = v := by simpa only [hpoolR, Finset.mem_singleton] using hz
      subst z
      have hpy : pool y = B := by
        simp only [pool, if_neg hyr, if_neg hyx, if_neg (hcol_ne huy hrcol), if_pos huy]
      simpa only [hpy] using hv
    · by_cases hux : u = x
      · subst u
        have hzw : z = w := by simpa only [hpoolX, Finset.mem_singleton] using hz
        subst z
        apply hinto y hyr hyx (hcol_ne huy hxcol) w
        have he : degreeIn G C w = C.card := by
          rw [degreeIn, Finset.filter_eq_self.mpr hC]
        rwa [he]
      · by_cases hu0 : col u = 0
        · have hzA : z ∈ A := by simpa only [pool, if_neg hur, if_neg hux, if_pos hu0] using hz
          exact hinto y hyr hyx (hcol_ne huy hu0) z (hA z hzA)
        · have hzB : z ∈ B := by
            simp only [pool, if_neg hur, if_neg hux, if_neg hu0] at hz
            split_ifs at hz
            · exact hz
            · exact hCB hz
          have hpy : pool y = A := by
            simp only [pool, if_neg hyr, if_neg hyx, if_pos (hcol_zero huy hu0)]
          rw [hpy]
          exact hB z hzB
  have hattach (u : U) (hux : T.Adj u x) (z : V) (hz : z ∈ pool u) : G.Adj z w := by
    have hu0 : col u ≠ 0 := hcol_ne hux.symm hxcol
    have hur : u ≠ r := fun hh ↦ hu0 (hh ▸ hrcol)
    have hun : ¬ T.Adj r u := fun hh ↦ hno u hh hux.symm
    have hzC : z ∈ C := by
      simpa only [pool, if_neg hur, if_neg hux.ne, if_neg hu0, if_neg hun] using hz
    exact (hC z hzC).symm
  obtain ⟨f, hf, hfx, hfp⟩ := exists_copy_of_two_prescribed_vertices T G hT r x v w pool
    (by rw [hpoolR]; exact Finset.mem_singleton_self _) hpoolX havoid hdegree hattach
  refine ⟨f, hf, hfx, ?_⟩
  intro u hur hux
  constructor
  · intro hu0
    simpa only [pool, if_neg hur, if_neg hux, if_pos hu0] using hfp u
  · intro hu0
    have hh := hfp u
    simp only [pool, if_neg hur, if_neg hux, if_neg hu0] at hh
    split_ifs at hh
    · exact hh
    · exact hCB hh

end Erdos547

#print axioms Erdos547.exists_two_rooted_copy_of_cross_degrees
