import ErdosProblems.Erdos547.TwoRootCrossEmbedding
import ErdosProblems.Erdos547.RegularityShrubCore

/-!
# Embedding a shrub whose second root must lie in a reserved set
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*} [Fintype U]

theorem exists_two_rooted_copy_in_regular_pair (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (r x : U)
    (hxeven : T.dist r x % 2 = 0) (hxdist : 4 ≤ T.dist r x)
    {ε : ℝ} {X Y A B P : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y)
    (hA : A ⊆ X) (hB : B ⊆ Y) (hP : P ⊆ X) (hPA : Disjoint P A)
    (hAsize : (X.card : ℝ) * ε ≤ A.card) (hBsize : (Y.card : ℝ) * ε ≤ B.card)
    (hPsize : (X.card : ℝ) * ε < P.card) (hεD : ε ≤ (G.edgeDensity X Y : ℝ))
    (hroomN : (Fintype.card U : ℝ) + (Y.card : ℝ) * ε ≤
      ((G.edgeDensity X Y : ℝ) - ε) * B.card)
    (hroomA : (Fintype.card U : ℝ) ≤
      ((G.edgeDensity X Y : ℝ) - ε) ^ 2 * B.card - (Y.card : ℝ) * ε)
    (hroomB : (Fintype.card U : ℝ) ≤
      ((G.edgeDensity X Y : ℝ) - ε) * A.card - (X.card : ℝ) * ε)
    (v : V) (hvP : v ∉ P)
    (hroot : (Fintype.card U : ℝ) + (Y.card : ℝ) * ε ≤ degreeIn G B v) :
    ∃ f : T.Copy G, f r = v ∧ f x ∈ P ∧ ∀ u, u ≠ r → u ≠ x →
      (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  classical
  obtain ⟨w, hwP, htyp⟩ := exists_typical_in_large_subset G hreg hB hBsize hP hPsize
  let N := B.filter (G.Adj w)
  have hN : ((G.edgeDensity X Y : ℝ) - ε) * B.card ≤ (N.card : ℝ) := htyp
  have hNsize : (Y.card : ℝ) * ε ≤ N.card := by
    linarith [Nat.cast_nonneg (Fintype.card U) (α := ℝ)]
  obtain ⟨A', B', C, hA', hB', hCB, hCN, hlossB, hcardC, hdegA, hdegB⟩ :=
    exists_regular_shrub_core G hreg hA hB (Finset.filter_subset _ _) hAsize hNsize
  have hC (z : V) (hz : z ∈ C) : G.Adj w z := (Finset.mem_filter.mp (hCN hz)).2
  have hCsize : Fintype.card U ≤ C.card := by
    have hh : (Fintype.card U : ℝ) ≤ C.card := by linarith
    exact_mod_cast hh
  have hDA (z : V) (hz : z ∈ A') : Fintype.card U ≤ degreeIn G C z := by
    have hh := mul_le_mul_of_nonneg_left hN (sub_nonneg.mpr hεD)
    have hc := hdegA z hz
    have he : (Fintype.card U : ℝ) ≤ degreeIn G C z := by nlinarith only [hh, hc, hroomA]
    exact_mod_cast he
  have hDB (z : V) (hz : z ∈ B') : Fintype.card U ≤ degreeIn G A' z := by
    exact_mod_cast hroomB.trans (hdegB z hz)
  have hv : Fintype.card U ≤ degreeIn G B' v := by
    have hh : (degreeIn G B v : ℝ) ≤ degreeIn G B' v + ((B \ B').card : ℝ) := by
      exact_mod_cast degreeIn_le_add_removed G B B' v
    have he : (Fintype.card U : ℝ) ≤ degreeIn G B' v := by linarith
    exact_mod_cast he
  let col : T.Coloring (Fin 2) := hT.coloringTwoOfVert r
  have hcol (u : U) : col u = 0 ↔ T.dist r u % 2 = 0 := by
    change (⟨T.dist r u % 2, _⟩ : Fin 2) = 0 ↔ _
    exact Fin.ext_iff
  have hrcol : col r = 0 := (hcol r).mpr (by simp)
  have hxcol : col x = 0 := (hcol x).mpr hxeven
  have hrx : r ≠ x := by
    intro hh
    rw [hh, SimpleGraph.dist_self] at hxdist
    omega
  have hno (u : U) (hru : T.Adj r u) (hxu : T.Adj x u) : False := by
    have hh := hT.connected.dist_triangle (u := r) (v := u) (w := x)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hru,
      SimpleGraph.dist_eq_one_iff_adj.mpr hxu.symm] at hh
    omega
  have hvw : v ≠ w := fun hh ↦ hvP (hh.symm ▸ hwP)
  have hwA : w ∉ A' := fun hw ↦ Finset.disjoint_left.mp hPA hwP (hA' hw)
  have hwB : w ∉ B' := fun hw ↦ Finset.disjoint_left.mp hdis (hP hwP) (hB (hB' hw))
  obtain ⟨f, hf, hfx, hpart⟩ := exists_two_rooted_copy_of_cross_degrees T G hT col r x
    hrx hrcol hxcol hno A' B' C hCB v w hvw hwA hwB hC hCsize hDA hDB hv
  refine ⟨f, hf, hfx.symm ▸ hwP, ?_⟩
  intro u hur hux
  refine ⟨fun hu ↦ hA' ((hpart u hur hux).1 ((hcol u).mpr hu)), ?_⟩
  exact fun hu ↦ hB' ((hpart u hur hux).2 (fun hh ↦ hu ((hcol u).mp hh)))

end Erdos547

#print axioms Erdos547.exists_two_rooted_copy_in_regular_pair
