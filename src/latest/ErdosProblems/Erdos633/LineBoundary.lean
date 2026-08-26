import ErdosProblems.Erdos633.LineCoordinates

/-!
# Boundary cancellation on each supporting line

The density of an actual triangle edge on a chosen line is a signed interval
density in the line parameter. The finite interval-chain theorem then makes
the original dissection cancel against every endpoint potential on that line.
No regularity or order preservation of the potential is required.
-/

namespace Erdos633

open scoped BigOperators

theorem Triangle.axisDirection_zero_of_nonaxis (P : Triangle) (k : Fin 3)
    (p d z : ℂ) (hz : OnAxis p d z) (hseg : z ∈ P.edge k)
    (hline : ¬(OnAxis p d (P.edgeStart k) ∧ OnAxis p d (P.edgeEnd k))) :
    axisDirection d (P.unitEdgeVector k) = 0 := by
  unfold axisDirection
  split_ifs with him
  · have hsign : P.orientationSign ≠ 0 := by
      unfold Triangle.orientationSign
      split_ifs <;> norm_num
    have hcoef : (P.sideLength k)⁻¹ * P.orientationSign ≠ 0 :=
      mul_ne_zero (inv_ne_zero (ne_of_gt (P.sideLength_pos k))) hsign
    rw [P.unitEdgeVector_div, Complex.smul_im, smul_eq_mul] at him
    have hdir := (mul_eq_zero.mp him).resolve_left hcoef
    exact False.elim (hline (onAxis_endpoints_of_parallel_segment p d
      (P.edgeStart k) (P.edgeEnd k) z hz hseg hdir))
  · rfl

noncomputable def Triangle.axisEdgeWeight (P : Triangle) (p d : ℂ) (k : Fin 3) : ℝ := by
  classical
  exact if OnAxis p d (P.edgeStart k) ∧ OnAxis p d (P.edgeEnd k) then P.orientationSign else 0

theorem Triangle.edgeDensity_eq_axis_flow (P : Triangle) (k : Fin 3)
    (p d : ℂ) (hd : d ≠ 0) (t : ℝ)
    (hs : axisMap p d t ≠ P.edgeStart k) (he : axisMap p d t ≠ P.edgeEnd k) :
    P.edgeDensity (axisDirection d) k (axisMap p d t) =
      P.axisEdgeWeight p d k * intervalFlow (axisParameter p d (P.edgeStart k))
        (axisParameter p d (P.edgeEnd k)) t := by
  classical
  by_cases hline : OnAxis p d (P.edgeStart k) ∧ OnAxis p d (P.edgeEnd k)
  · rw [Triangle.axisEdgeWeight, if_pos hline]
    let a := axisParameter p d (P.edgeStart k)
    let b := axisParameter p d (P.edgeEnd k)
    have ha : P.edgeStart k = axisMap p d a :=
      (axisMap_axisParameter p d (P.edgeStart k) hd hline.1).symm
    have hb : P.edgeEnd k = axisMap p d b :=
      (axisMap_axisParameter p d (P.edgeEnd k) hd hline.2).symm
    have hab : a ≠ b := fun h => P.edgeStart_ne_edgeEnd k (by rw [ha, hb, h])
    have hta : t ≠ a := fun h => hs (by rw [h, ← ha])
    have htb : t ≠ b := fun h => he (by rw [h, ← hb])
    have hmem : axisMap p d t ∈ P.edge k ↔ t ∈ Set.uIcc a b := by
      change axisMap p d t ∈ segment ℝ (P.edgeStart k) (P.edgeEnd k) ↔ _
      rw [ha, hb]
      exact axisMap_mem_segment p d hd a b t
    change _ = P.orientationSign * intervalFlow a b t
    rw [intervalFlow_eq_indicator a b t hab hta htb]
    by_cases ht : t ∈ Set.uIcc a b
    · rw [P.edgeDensity_of_mem _ k (hmem.mpr ht), Set.indicator_of_mem ht]
      exact P.axisDirection_unitEdge k p d hd a b ha hb
    · rw [P.edgeDensity_of_not_mem _ k (fun hz => ht (hmem.mp hz)),
        Set.indicator_of_notMem ht, mul_zero]
  · rw [Triangle.axisEdgeWeight, if_neg hline, zero_mul]
    by_cases hz : axisMap p d t ∈ P.edge k
    · rw [P.edgeDensity_of_mem _ k hz]
      exact P.axisDirection_zero_of_nonaxis k p d (axisMap p d t)
        (onAxis_axisMap p d hd t) hz hline
    · exact P.edgeDensity_of_not_mem _ k hz

theorem TriangleDissection.axis_flow_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (p d : ℂ) (hd : d ≠ 0) (t : ℝ) (hv : axisMap p d t ∉ T.vertexFinset) :
    (∑ k : Fin 3, P.axisEdgeWeight p d k *
      intervalFlow (axisParameter p d (P.edgeStart k))
        (axisParameter p d (P.edgeEnd k)) t) =
    ∑ i : Fin N, ∑ k : Fin 3, (T.tile i).axisEdgeWeight p d k *
      intervalFlow (axisParameter p d ((T.tile i).edgeStart k))
        (axisParameter p d ((T.tile i).edgeEnd k)) t := by
  have hP := T.not_outer_vertex_of_not_vertexFinset hv
  have hQ := T.not_tile_vertex_of_not_vertexFinset hv
  have heq (Q : Triangle) (hq : axisMap p d t ∉ Set.range Q.vertex) (k : Fin 3) :=
    Q.edgeDensity_eq_axis_flow k p d hd t
      (fun h => hq (h.symm ▸ Q.edgeStart_mem_vertices k))
      (fun h => hq (h.symm ▸ Q.edgeEnd_mem_vertices k))
  have h := T.boundaryDensity_eq_sum_of_not_vertex (axisDirection d)
    (axisDirection_odd d) hv
  unfold Triangle.boundaryDensity at h
  simpa only [heq P hP, heq (T.tile _) (hQ _)] using h

noncomputable def Triangle.axisEndpointSum (P : Triangle) (p d : ℂ) (g : ℝ → ℝ) : ℝ :=
  ∑ k : Fin 3, P.axisEdgeWeight p d k *
    (g (axisParameter p d (P.edgeEnd k)) - g (axisParameter p d (P.edgeStart k)))

/-- Actual geometric tilings cancel against every potential on one supporting
line, including discontinuous potentials induced by field embeddings. -/
theorem TriangleDissection.axisEndpointSum_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (p d : ℂ) (hd : d ≠ 0) (g : ℝ → ℝ) :
    P.axisEndpointSum p d g = ∑ i : Fin N, (T.tile i).axisEndpointSum p d g := by
  let F := (axisMap p d) ⁻¹' (T.vertexFinset : Set ℂ)
  have hF : F.Finite := T.vertexFinset.finite_toSet.preimage (axisMap_injective p d hd).injOn
  have h := interval_flow_balance_potential_eq
    (fun k : Fin 3 => axisParameter p d (P.edgeStart k))
    (fun k : Fin 3 => axisParameter p d (P.edgeEnd k))
    (P.axisEdgeWeight p d)
    (fun j : Fin N × Fin 3 => axisParameter p d ((T.tile j.1).edgeStart j.2))
    (fun j : Fin N × Fin 3 => axisParameter p d ((T.tile j.1).edgeEnd j.2))
    (fun j : Fin N × Fin 3 => (T.tile j.1).axisEdgeWeight p d j.2)
    F hF (fun t ht => by
      simpa only [Fintype.sum_prod_type] using T.axis_flow_eq_sum p d hd t ht) g
  simpa only [Triangle.axisEndpointSum, Fintype.sum_prod_type] using h

end Erdos633
