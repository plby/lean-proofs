import ErdosProblems.Erdos547.RootedCrossEmbedding
import ErdosProblems.Erdos547.RegularityPruning

/-!
# Embedding a small tree in a regular pair with a prescribed root
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*} [Fintype U]

theorem exists_rooted_copy_in_regular_pair (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) {ε : ℝ} {X Y A B : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y) (hA : A ⊆ X) (hB : B ⊆ Y)
    (hAsize : (X.card : ℝ) * ε ≤ A.card) (hBsize : (Y.card : ℝ) * ε ≤ B.card)
    (hroomA : (Fintype.card U : ℝ) ≤
      ((G.edgeDensity X Y : ℝ) - ε) * B.card - (Y.card : ℝ) * ε)
    (hroomB : (Fintype.card U : ℝ) ≤
      ((G.edgeDensity X Y : ℝ) - ε) * A.card - (X.card : ℝ) * ε)
    (r : U) (v : V) (hv : v ∈ X)
    (hroot : (Fintype.card U : ℝ) + (Y.card : ℝ) * ε ≤ degreeIn G B v) :
    ∃ f : T.Copy G, f r = v ∧ ∀ u, u ≠ r →
      (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  classical
  obtain ⟨A', B', hA', hB', _hlossA, hlossB, hdegA, hdegB⟩ :=
    exists_regular_pair_core G hreg hA hB hAsize hBsize
  have hcross : Disjoint (insert v A') B' := Finset.disjoint_left.mpr fun z hz hzB ↦ by
    have hzX : z ∈ X := by
      rcases Finset.mem_insert.mp hz with rfl | hzA
      · exact hv
      · exact hA (hA' hzA)
    exact Finset.disjoint_left.mp hdis hzX (hB (hB' hzB))
  have hleft (z : V) (hz : z ∈ insert v A') : Fintype.card U ≤ degreeIn G B' z := by
    rcases Finset.mem_insert.mp hz with hzv | hzA
    · subst z
      have hlose : (degreeIn G B v : ℝ) ≤ degreeIn G B' v + ((B \ B').card : ℝ) := by
        exact_mod_cast degreeIn_le_add_removed G B B' v
      have hh : (Fintype.card U : ℝ) ≤ degreeIn G B' v := by linarith
      exact_mod_cast hh
    · exact_mod_cast hroomA.trans (hdegA z hzA)
  have hright (z : V) (hz : z ∈ B') : Fintype.card U ≤ degreeIn G (insert v A') z := by
    have hh : Fintype.card U ≤ degreeIn G A' z := by exact_mod_cast hroomB.trans (hdegB z hz)
    exact hh.trans (degreeIn_mono G (Finset.subset_insert _ _) z)
  obtain ⟨f, hf, hpart⟩ := exists_rooted_copy_of_cross_degrees T G hT (insert v A') B'
    hcross hleft hright r v (Finset.mem_insert_self _ _)
  refine ⟨f, hf, ?_⟩
  intro u hur
  constructor
  · intro heven
    have hfu := (hpart u).1 heven
    have hne : f u ≠ v := fun hh ↦ hur (f.injective (hh.trans hf.symm))
    exact hA' ((Finset.mem_insert.mp hfu).resolve_left hne)
  · intro hodd
    exact hB' ((hpart u).2 hodd)

end Erdos547

#print axioms Erdos547.exists_rooted_copy_in_regular_pair
