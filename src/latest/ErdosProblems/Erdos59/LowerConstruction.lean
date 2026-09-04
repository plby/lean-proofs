import ErdosProblems.Erdos59.AffineCount
import ErdosProblems.Erdos59.Averaging
import ErdosProblems.Erdos59.CycleAdapters
import ErdosProblems.Erdos59.DensityAsymptotics

/-!
# The dense triangle- and hexagon-free FNV graphs

This file joins the affine polarity graph, the deterministic fixed-size
averaging lemma, and the FNV duplication construction.  Its final theorem is
the unconditional lower construction used in the negative solution of
Erdős problem 59: at unbounded orders there is a labelled triangle-free and
`C₆`-free graph with more than

`(2669 / 5000) n ^ (4 / 3)`

edges.  All powers and inequalities in the density conclusion are over
`ℝ`, exactly as in `DensityAsymptotics`.
-/

namespace Erdos59

open Finset
open scoped BigOperators

namespace LowerConstruction

noncomputable section

open AffinePolarity

private noncomputable instance graphAdjDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

private def increasingOrientation {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : FNV.Orientation G A where
  Dir x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A ∧ x < y
  dir_adj h := h.1
  dir_fst_mem h := h.2.1
  dir_snd_mem h := h.2.2.1
  exactly_one := by
    intro x y hxy hx hy
    constructor
    · rintro ⟨_, _, _, hlt⟩ ⟨_, _, _, hrev⟩
      exact hlt.asymm hrev
    · intro hnrev
      refine ⟨hxy, hx, hy, ?_⟩
      have hnlt : ¬ y < x := by
        intro hyx
        exact hnrev ⟨hxy.symm, hy, hx, hyx⟩
      exact lt_of_le_of_ne (le_of_not_gt hnlt) hxy.ne

private noncomputable instance increasingOrientationDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    DecidableRel (increasingOrientation G A).Dir :=
  Classical.decRel _

private theorem fnvK_le_fnvN (a : ℕ) : fnvK a ≤ fnvN a := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_lower : (2 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hsqrt_upper : Real.sqrt 5 - 2 ≤ 1 := by nlinarith
  have hNnonneg : (0 : ℝ) ≤ fnvN a := by positivity
  have hfloor : (fnvK a : ℝ) ≤
      (Real.sqrt 5 - 2) * (fnvN a : ℝ) := by
    exact Nat.floor_le (mul_nonneg (sub_nonneg.mpr hsqrt_lower) hNnonneg)
  exact_mod_cast (show (fnvK a : ℝ) ≤ fnvN a by
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_upper hNnonneg])

private theorem two_le_fnvN (a : ℕ) : 2 ≤ fnvN a := by
  have hq : 2 ≤ fnvQ a := by
    rw [fnvQ, show 2 * a + 1 = 2 * a + 1 from rfl, pow_succ]
    have hpos : 0 < 2 ^ (2 * a) := pow_pos (by norm_num) _
    omega
  rw [fnvN]
  exact hq.trans (le_self_pow₀ (by omega) (by norm_num))

private theorem baseEdgeCard_cast (a : ℕ) :
    ((AffineCount.graph a).edgeFinset.card : ℝ) = fnvBaseEdges a := by
  rw [AffineCount.card_graph_edges, fnvBaseEdges]
  have h2q : 2 ∣ AffineCount.q a := by
    rw [AffineCount.q, show 2 * a + 1 = 2 * a + 1 from rfl, pow_succ]
    simpa [mul_comm] using dvd_mul_right 2 (2 ^ (2 * a))
  have h2q2 : 2 ∣ AffineCount.q a ^ 2 :=
    dvd_pow h2q (by norm_num)
  have h2q4 : 2 ∣ AffineCount.q a ^ 4 :=
    dvd_pow h2q (by norm_num)
  have hdiv : 2 ∣ AffineCount.q a ^ 4 - AffineCount.q a ^ 2 :=
    Nat.dvd_sub h2q4 h2q2
  have hle : AffineCount.q a ^ 2 ≤ AffineCount.q a ^ 4 := by
    rw [show AffineCount.q a ^ 4 =
      AffineCount.q a ^ 2 * AffineCount.q a ^ 2 by ring]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by simp [AffineCount.q]) _)
  rw [Nat.cast_div hdiv (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Nat.cast_sub hle]
  norm_num [AffineCount.q, fnvQ]

private theorem baseC4Free (a : ℕ) :
    FNV.C4Free (AffineCount.graph a) := by
  apply (CycleAdapters.duplication_c4Free_iff_cycleGraph_four_free _).2
  apply (SimpleGraph.free_congr_right (AffineCount.graphIso a)).mp
  exact (CycleAdapters.affine_no_c4_iff_cycleGraph_four_free _).1
    (AffinePolarity.polarityGraph_no_C4 a)

/-- For every affine parameter `a ≥ 3`, the complete FNV construction gives
a labelled graph on exactly `fnvVertices a` vertices with the required
forbidden subgraphs and density. -/
theorem exists_graph (a : ℕ) (ha : 3 ≤ a) :
    ∃ B : SimpleGraph (Fin (fnvVertices a)),
      B.CliqueFree 3 ∧
      (SimpleGraph.cycleGraph 6).Free B ∧
      (B.edgeFinset.card : ℝ) >
        (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  let G := AffineCount.graph a
  have hcardG : Fintype.card (Fin (AffineCount.q a ^ 3)) = fnvN a := by
    simp [fnvN, fnvQ, AffineCount.q]
  have hN : 2 ≤ Fintype.card (Fin (AffineCount.q a ^ 3)) := by
    simpa [hcardG] using two_le_fnvN a
  have hK : fnvK a ≤ Fintype.card (Fin (AffineCount.q a ^ 3)) := by
    simpa [hcardG] using fnvK_le_fnvN a
  obtain ⟨A, hAcard, haverage⟩ :=
    FNV.exists_subset_incidentEdges_fnv_rat (G := G) hN hK
  let O : FNV.Orientation G A := increasingOrientation G A
  let D : SimpleGraph (FNV.DuplicateVertex A) := FNV.duplication G A O
  have htriG : FNV.TriangleFree G := AffineCount.graph_cliqueFree_three a
  have hfourG : FNV.C4Free G := baseC4Free a
  have hsixG : FNV.C6Free G :=
    (CycleAdapters.duplication_c6Free_iff_cycleGraph_six_free G).2
      (AffineCount.graph_cycleGraph_six_free a)
  have htriD : D.CliqueFree 3 := by
    exact FNV.duplication_triangleFree (G := G) (A := A) (O := O) htriG
  have hsixD : (SimpleGraph.cycleGraph 6).Free D := by
    apply (CycleAdapters.duplication_c6Free_iff_cycleGraph_six_free D).1
    exact FNV.duplication_c6Free (G := G) (A := A) (O := O)
      htriG hfourG hsixG
  have hcardD : Fintype.card (FNV.DuplicateVertex A) = fnvVertices a := by
    simp [FNV.DuplicateVertex, fnvVertices, hcardG, hAcard]
  let B : SimpleGraph (Fin (fnvVertices a)) := D.overFin hcardD
  let : DecidableRel B.Adj := Classical.decRel _
  let e : D ≃g B := D.overFinIso hcardD
  have haverageR :
      (G.edgeFinset.card : ℝ) * (fnvK a : ℝ) / (fnvN a : ℝ) *
          (2 - ((fnvK a : ℝ) - 1) / ((fnvN a : ℝ) - 1)) ≤
        ((FNV.incidentEdges G A).card : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 haverage
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_ofNat] at hcast
    simpa [hcardG] using hcast
  have hlowerD : fnvLower a ≤ (D.edgeFinset.card : ℝ) := by
    have hbase : (G.edgeFinset.card : ℝ) = fnvBaseEdges a := by
      simpa [G] using baseEdgeCard_cast a
    rw [fnvLower, ← hbase]
    rw [FNV.card_edgeFinset_duplication (G := G) (A := A) (O := O)]
    push_cast
    convert add_le_add_left haverageR (G.edgeFinset.card : ℝ) using 1 <;> ring
  have hlowerB : fnvLower a ≤ (B.edgeFinset.card : ℝ) := by
    rw [← e.card_edgeFinset_eq]
    exact hlowerD
  refine ⟨B, ?_, ?_, ?_⟩
  · exact htriD.comap e.symm.toEmbedding.isContained
  · exact (SimpleGraph.free_congr_right e).mp hsixD
  · exact lt_of_lt_of_le (fnvLower_gt ha) hlowerB

/-- The dense labelled graphs above occur at unbounded vertex counts. -/
theorem infinitely_often :
    ∀ M : ℕ, ∃ a : ℕ, ∃ B : SimpleGraph (Fin (fnvVertices a)),
      M ≤ fnvVertices a ∧
      B.CliqueFree 3 ∧
      (SimpleGraph.cycleGraph 6).Free B ∧
      (B.edgeFinset.card : ℝ) >
        (2669 / 5000 : ℝ) *
          (fnvVertices a : ℝ) ^ (4 / 3 : ℝ) := by
  intro M
  let a := M + 3
  have ha : 3 ≤ a := by simp [a]
  have hMq : M < fnvQ a := by
    apply lt_of_le_of_lt (show M ≤ 2 * a + 1 by dsimp [a]; omega)
    simpa [fnvQ] using (2 * a + 1).lt_two_pow_self
  have hqN : fnvQ a ≤ fnvN a := by
    rw [fnvN]
    exact le_self_pow₀ (show 1 ≤ fnvQ a by
      exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))) (by norm_num)
  have hM : M ≤ fnvVertices a :=
    hMq.le.trans (hqN.trans (Nat.le_add_right _ _))
  obtain ⟨B, htri, hsix, hdense⟩ := exists_graph a ha
  exact ⟨a, B, hM, htri, hsix, hdense⟩

end

end LowerConstruction

end Erdos59
