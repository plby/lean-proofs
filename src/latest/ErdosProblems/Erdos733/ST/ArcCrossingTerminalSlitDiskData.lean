import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.ArcCrossingEarlierPrefix
import ErdosProblems.Erdos733.ST.PlanarSlitDiskEndpointConesAvoidRay
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import ErdosProblems.Erdos733.ST.PolygonalArcTargetEndpointRayCover
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingTerminalSlitDiskData]
lemma ArcCrossingTerminalSlitDiskData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2)) (r₀ r₁ η : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτtarget : τ.target = δ.target)
    (hIso : PolygonalArcEndpointIsolation τ r₀ r₁)
    (hηpos : 0 < η)
    (hηsep :
      ∀ a, a ∈
          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
        ∀ b, b ∈ τ.carrier → η ≤ dist a b) :
    ∃ ρ rT K₁ : ℝ,
      0 < ρ ∧ 0 < rT ∧ rT < r₁ ∧ 0 < K₁ ∧
        (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
            have hlen := τ.length_ge_two
            omega
         let base : EuclideanSpace ℝ (Fin 2) :=
            τ.vertices[τ.vertices.length - 2]'hprev - τ.target
         let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
            {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
         let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
            Metric.ball τ.target ρ \
              (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
         Dstar ⊆ (K ∪ δ.carrier)ᶜ) ∧
          (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
              have hlen := τ.length_ge_two
              omega
           let base : EuclideanSpace ℝ (Fin 2) :=
              τ.vertices[τ.vertices.length - 2]'hprev - τ.target
           let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
              {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
           let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
              Metric.ball τ.target ρ \
                (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
           IsOpen Dstar) ∧
            (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                have hlen := τ.length_ge_two
                omega
             let base : EuclideanSpace ℝ (Fin 2) :=
                τ.vertices[τ.vertices.length - 2]'hprev - τ.target
             let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
             let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                Metric.ball τ.target ρ \
                  (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
             IsConnected Dstar) ∧
              PolygonalArcEndpointIsolation τ r₀ rT ∧
                (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                    have hlen := τ.length_ge_two
                    omega
                 let base : EuclideanSpace ℝ (Fin 2) :=
                    τ.vertices[τ.vertices.length - 2]'hprev - τ.target
                 let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                    {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
                 let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                    Metric.ball τ.target ρ \
                      (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
                 PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar) ∧
                  (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                      have hlen := τ.length_ge_two
                      omega
                   let base : EuclideanSpace ℝ (Fin 2) :=
                      τ.vertices[τ.vertices.length - 2]'hprev - τ.target
                   let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                      {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
                   let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                      Metric.ball τ.target ρ \
                        (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
                   PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
                    Dstar) := by
-- BODY
  obtain ⟨Rδ, hRδpos, hδray⟩ := PolygonalArcTargetEndpointRayCover δ
  let ρ : ℝ := min (Rδ / 2) (η / 2)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  have hρ_le_Rδ : ρ ≤ Rδ := by
    dsimp [ρ]
    have hle : min (Rδ / 2) (η / 2) ≤ Rδ / 2 := min_le_left _ _
    linarith
  have hρ_lt_η : ρ < η := by
    dsimp [ρ]
    have hle : min (Rδ / 2) (η / 2) ≤ η / 2 := min_le_right _ _
    linarith
  let hprevτ : τ.vertices.length - 2 < τ.vertices.length := by
    have hlen := τ.length_ge_two
    omega
  let base : EuclideanSpace ℝ (Fin 2) :=
    τ.vertices[τ.vertices.length - 2]'hprevτ - τ.target
  have htarget_len_pos : 0 < PolygonalArcTerminalEndpointSegmentLength τ :=
    lt_trans hIso.target_pos hIso.target_lt_terminal_length
  have hdist_base_pos :
      0 < dist τ.target (τ.vertices[τ.vertices.length - 2]'hprevτ) := by
    simpa [PolygonalArcTerminalEndpointSegmentLength, hprevτ] using htarget_len_pos
  have hbase_norm_pos : 0 < ‖base‖ := by
    rw [dist_eq_norm] at hdist_base_pos
    have hneg :
        τ.target - τ.vertices[τ.vertices.length - 2]'hprevτ = -base := by
      dsimp [base]
      abel
    simpa [hneg] using hdist_base_pos
  have hbase_ne : base ≠ 0 := norm_pos_iff.mp hbase_norm_pos
  rcases PlanarSlitDiskEndpointConesAvoidRay τ.target base ρ hρpos hbase_ne with
    ⟨hDopen, hDconn, rSlit, KSlit, hrSlit, hKSlit, hnegCone, hposCone⟩
  let rT : ℝ := min r₁ rSlit / 2
  let K₁ : ℝ := KSlit
  have hrTpos : 0 < rT := by
    dsimp [rT]
    have hminpos : 0 < min r₁ rSlit := lt_min hIso.target_pos hrSlit
    linarith
  have hrTlt : rT < r₁ := by
    dsimp [rT]
    have hle : min r₁ rSlit ≤ r₁ := min_le_left _ _
    have hminpos : 0 < min r₁ rSlit := lt_min hIso.target_pos hrSlit
    linarith
  have hrTle : rT ≤ r₁ := le_of_lt hrTlt
  have hrTleSlit : rT ≤ rSlit := by
    dsimp [rT]
    have hle : min r₁ rSlit ≤ rSlit := min_le_right _ _
    linarith
  have hIsoShrink : PolygonalArcEndpointIsolation τ r₀ rT := by
    refine
      { source_pos := hIso.source_pos
        target_pos := hrTpos
        source_lt_initial_length := hIso.source_lt_initial_length
        target_lt_terminal_length := lt_of_le_of_lt hrTle hIso.target_lt_terminal_length
        endpoint_closedBalls_disjoint := ?_
        source_closedBall_carrier_subset_initial_segment :=
          hIso.source_closedBall_carrier_subset_initial_segment
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact hIso.endpoint_closedBalls_disjoint.mono_right
        (Metric.closedBall_subset_closedBall hrTle)
    · dsimp
      intro z hz
      exact hIso.target_closedBall_carrier_subset_terminal_segment
        ⟨Metric.closedBall_subset_closedBall hrTle hz.1, hz.2⟩
  have hτtarget_mem : τ.target ∈ τ.carrier := by
    rw [τ.carrier_eq]
    let last : ℕ := τ.vertices.length - 2
    have hlast : last + 1 < τ.vertices.length := by
      dsimp [last]
      have hlen := τ.length_ge_two
      omega
    refine ⟨last, hlast, ?_⟩
    have htarget_last : τ.vertices[last + 1] = τ.target := by
      have hidx : last + 1 = τ.vertices.length - 1 := by
        dsimp [last]
        omega
      have hget : τ.vertices.getLast? = some τ.vertices[τ.vertices.length - 1] := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by
          have hlen := τ.length_ge_two
          omega)]
      have hlast_value : τ.vertices[τ.vertices.length - 1] = τ.target :=
        Option.some.inj (by rw [← hget, τ.target_eq_last])
      simpa [hidx] using hlast_value
    simpa [htarget_last] using right_mem_segment ℝ τ.vertices[last] τ.vertices[last + 1]
  have hdelta_terminal_ray_subset :
      (let hprevδ : δ.vertices.length - 2 < δ.vertices.length := by
          have hlen := δ.length_ge_two
          omega
       {x : EuclideanSpace ℝ (Fin 2) |
          ∃ s : ℝ, 0 ≤ s ∧
            x = δ.target + s • (δ.vertices[δ.vertices.length - 2]'hprevδ - δ.target)})
        ⊆
      ({x : EuclideanSpace ℝ (Fin 2) |
          ∃ s : ℝ, 0 < s ∧ x = τ.target + s • base} ∪
        ({τ.target} : Set (EuclideanSpace ℝ (Fin 2)))) := by
    dsimp
    intro x hx
    rcases hx with ⟨s, hs_nonneg, hx⟩
    by_cases hs_zero : s = 0
    · right
      rw [hx, hs_zero]
      simp [hτtarget]
    have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
    have hτlen : τ.vertices.length = δ.vertices.length - j := by
      rw [hτvertices]
      simp [List.length_drop]
      omega
    by_cases hlastcase : j + 2 = δ.vertices.length
    · have hδprev_eq_j :
          δ.vertices[δ.vertices.length - 2] = δ.vertices[j] := by
        have hidx : δ.vertices.length - 2 = j := by omega
        simpa [hidx]
      have hδtarget_last : δ.vertices[j + 1] = δ.target := by
        have hidx : j + 1 = δ.vertices.length - 1 := by omega
        have hget : δ.vertices.getLast? = some δ.vertices[δ.vertices.length - 1] := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by
            have hlen := δ.length_ge_two
            omega)]
        have hlast_value : δ.vertices[δ.vertices.length - 1] = δ.target :=
          Option.some.inj (by rw [← hget, δ.target_eq_last])
        simpa [hidx] using hlast_value
      have hτprev_eq_c :
          τ.vertices[τ.vertices.length - 2] = c := by
        have hτlen2 : τ.vertices.length = 2 := by
          rw [hτlen]
          omega
        have hidx : τ.vertices.length - 2 = 0 := by omega
        have hget0 : τ.vertices[0] = c := by
          simpa [hτvertices]
        simpa [hidx] using hget0
      have hcParam := hcOpen
      rw [openSegment_eq_image_lineMap] at hcParam
      rcases hcParam with ⟨t, ht, htc⟩
      have hone_minus_pos : 0 < 1 - t := sub_pos.mpr ht.2
      have hbase_final :
          base = (1 - t) • (δ.vertices[j] - δ.target) := by
        dsimp [base]
        rw [hτprev_eq_c, hτtarget, ← htc, hδtarget_last]
        ext k
        simp [AffineMap.lineMap_apply_module]
        ring
      left
      refine ⟨s / (1 - t), div_pos hs_pos hone_minus_pos, ?_⟩
      calc
        x = δ.target +
            s • (δ.vertices[δ.vertices.length - 2] - δ.target) := hx
        _ = δ.target + s • (δ.vertices[j] - δ.target) := by
          simpa [hδprev_eq_j]
        _ = τ.target + (s / (1 - t)) • base := by
          rw [hτtarget, hbase_final, smul_smul]
          congr 1
          field_simp [ne_of_gt hone_minus_pos]
    · have hnotlast : j + 2 < δ.vertices.length := by omega
      have hτprev_eqδprev :
          τ.vertices[τ.vertices.length - 2] =
            δ.vertices[δ.vertices.length - 2] := by
        let k : ℕ := τ.vertices.length - 3
        have hidxτ : τ.vertices.length - 2 = k + 1 := by
          dsimp [k]
          omega
        have hkdrop : k < (δ.vertices.drop (j + 1)).length := by
          dsimp [k]
          rw [hτlen]
          simp [List.length_drop]
          omega
        have htail_get :
            τ.vertices[k + 1] = (δ.vertices.drop (j + 1))[k] := by
          simpa [hτvertices]
        have hdrop_get :
            (δ.vertices.drop (j + 1))[k] =
              δ.vertices[j + 1 + k] := by
          simpa using
            (List.getElem_drop (xs := δ.vertices) (i := j + 1) (j := k)
              (h := hkdrop))
        have hsum : j + 1 + k = δ.vertices.length - 2 := by
          dsimp [k]
          rw [hτlen]
          omega
        calc
          τ.vertices[τ.vertices.length - 2] = τ.vertices[k + 1] := by
            simpa [hidxτ]
          _ = (δ.vertices.drop (j + 1))[k] := htail_get
          _ = δ.vertices[j + 1 + k] := hdrop_get
          _ = δ.vertices[δ.vertices.length - 2] := by
            simpa [hsum]
      have hbase_eq :
          base = δ.vertices[δ.vertices.length - 2] - δ.target := by
        dsimp [base]
        rw [hτprev_eqδprev, hτtarget]
      left
      refine ⟨s, hs_pos, ?_⟩
      simpa [hbase_eq, hτtarget] using hx
  have hDsubset :
      (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
          have hlen := τ.length_ge_two
          omega
       let base : EuclideanSpace ℝ (Fin 2) :=
          τ.vertices[τ.vertices.length - 2]'hprev - τ.target
       let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
          {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
       let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
          Metric.ball τ.target ρ \
            (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
       Dstar ⊆ (K ∪ δ.carrier)ᶜ) := by
    dsimp
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxbad
    rcases hx with ⟨hxball, hxnot_deleted⟩
    rcases hxbad with hxK | hxδ
    · have hsep := hηsep x
          (by exact Or.inl hxK) τ.target hτtarget_mem
      have hxltη : dist x τ.target < η :=
        lt_trans (Metric.mem_ball.mp hxball) hρ_lt_η
      exact (not_lt_of_ge hsep) hxltη
    · have hxballδ : x ∈ Metric.ball δ.target Rδ := by
        rw [Metric.mem_ball] at hxball ⊢
        have hxltR : dist x τ.target < Rδ :=
          lt_of_lt_of_le hxball hρ_le_Rδ
        simpa [hτtarget] using hxltR
      have hxrayδ := hδray ⟨hxballδ, hxδ⟩
      exact hxnot_deleted (hdelta_terminal_ray_subset hxrayδ)
  have hterminalCone :
      (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
          have hlen := τ.length_ge_two
          omega
       let base : EuclideanSpace ℝ (Fin 2) :=
          τ.vertices[τ.vertices.length - 2]'hprev - τ.target
       let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
          {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
       let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
          Metric.ball τ.target ρ \
            (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
       PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar) := by
    dsimp
    intro q hq
    change q ∈
      ((fun z : EuclideanSpace ℝ (Fin 2) =>
          τ.target + z 0 • base + z 1 • PlanarRot90 base) ''
        {z | 0 < z 0 ∧
          z 0 ^ 2 + z 1 ^ 2 <
            (rT / dist τ.target (τ.vertices[τ.vertices.length - 2]'hprevτ)) ^ 2 ∧
          -K₁ * z 0 < z 1 ∧ z 1 < 0}) at hq
    dsimp at hq ⊢
    rcases hq with ⟨z, hz, rfl⟩
    apply hnegCone
    refine ⟨z, ?_, rfl⟩
    rcases hz with ⟨hz0, hzrad, hzlow, hzhigh⟩
    refine ⟨hz0, ?_, ?_, hzhigh⟩
    · have hdist_eq_norm :
          dist τ.target (τ.vertices[τ.vertices.length - 2]'hprevτ) = ‖base‖ := by
        rw [dist_eq_norm]
        have hneg :
            τ.target - τ.vertices[τ.vertices.length - 2]'hprevτ = -base := by
          dsimp [base]
          abel
        simp [hneg]
      have hdiv_le : rT / ‖base‖ ≤ rSlit / ‖base‖ :=
        div_le_div_of_nonneg_right hrTleSlit (le_of_lt hbase_norm_pos)
      have hdiv_nonneg : 0 ≤ rT / ‖base‖ :=
        div_nonneg (le_of_lt hrTpos) (le_of_lt hbase_norm_pos)
      have hsquare_le : (rT / ‖base‖) ^ 2 ≤ (rSlit / ‖base‖) ^ 2 :=
        pow_le_pow_left₀ hdiv_nonneg hdiv_le 2
      exact lt_of_lt_of_le (by simpa [K₁, hdist_eq_norm, base] using hzrad)
        hsquare_le
    · simpa [K₁] using hzlow
  have hinitialReverseCone :
      (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
          have hlen := τ.length_ge_two
          omega
       let base : EuclideanSpace ℝ (Fin 2) :=
          τ.vertices[τ.vertices.length - 2]'hprev - τ.target
       let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
          {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
       let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
          Metric.ball τ.target ρ \
            (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
       PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
        Dstar) := by
    dsimp
    intro q hq
    have hrevFirst : 1 < (PolygonalArcReverse τ).vertices.length := by
      simpa [PolygonalArcReverse, List.length_reverse] using
        Nat.lt_of_succ_le τ.length_ge_two
    change q ∈
      ((fun z : EuclideanSpace ℝ (Fin 2) =>
          (PolygonalArcReverse τ).source +
            z 0 • ((PolygonalArcReverse τ).vertices[1]'hrevFirst -
              (PolygonalArcReverse τ).source) +
            z 1 • PlanarRot90
              ((PolygonalArcReverse τ).vertices[1]'hrevFirst -
                (PolygonalArcReverse τ).source)) ''
        {z | 0 < z 0 ∧
          z 0 ^ 2 + z 1 ^ 2 <
            (rT / dist (PolygonalArcReverse τ).source
              ((PolygonalArcReverse τ).vertices[1]'hrevFirst)) ^ 2 ∧
          0 < z 1 ∧ z 1 < K₁ * z 0}) at hq
    dsimp at hq ⊢
    rcases hq with ⟨z, hz, hqeq⟩
    apply hposCone
    refine ⟨z, ?_, ?_⟩
    · rcases hz with ⟨hz0, hzrad, hzlow, hzhigh⟩
      refine ⟨hz0, ?_, hzlow, ?_⟩
      · have hrev_first_index : τ.vertices.length - 1 - 1 = τ.vertices.length - 2 := by
          have hlen := τ.length_ge_two
          omega
        have hdist_eq_norm :
            dist τ.target (τ.vertices[τ.vertices.length - 2]'hprevτ) = ‖base‖ := by
          rw [dist_eq_norm]
          have hneg :
              τ.target - τ.vertices[τ.vertices.length - 2]'hprevτ = -base := by
            dsimp [base]
            abel
          simp [hneg]
        have hdiv_le : rT / ‖base‖ ≤ rSlit / ‖base‖ :=
          div_le_div_of_nonneg_right hrTleSlit (le_of_lt hbase_norm_pos)
        have hdiv_nonneg : 0 ≤ rT / ‖base‖ :=
          div_nonneg (le_of_lt hrTpos) (le_of_lt hbase_norm_pos)
        have hsquare_le : (rT / ‖base‖) ^ 2 ≤ (rSlit / ‖base‖) ^ 2 :=
          pow_le_pow_left₀ hdiv_nonneg hdiv_le 2
        exact lt_of_lt_of_le
          (by
            simpa [K₁, PolygonalArcReverse, List.length_reverse, hrev_first_index,
              hdist_eq_norm, base] using hzrad)
          hsquare_le
      · simpa [K₁] using hzhigh
    · have hrev_first_index : τ.vertices.length - 1 - 1 = τ.vertices.length - 2 := by
        have hlen := τ.length_ge_two
        omega
      simpa [K₁, base, PolygonalArcReverse, List.length_reverse, hrev_first_index]
        using hqeq
  refine ⟨ρ, rT, K₁, hρpos, hrTpos, hrTlt, by simpa [K₁] using hKSlit,
    ?_, ?_, ?_, hIsoShrink, ?_, ?_⟩
  · simpa [base] using hDsubset
  · simpa [base] using hDopen
  · simpa [base] using hDconn
  · simpa [base] using hterminalCone
  · simpa [base] using hinitialReverseCone
