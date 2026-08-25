import Util.IncidenceGeometry.OrdinaryCrossingLocalBranchData
import Util.IncidenceGeometry.PolygonalArcVertexAvoidsNonincidentSegment
import Util.IncidenceGeometry.StraightSegmentEndpointSphereBranch
import Util.IncidenceGeometry.StraightSegmentInteriorSphereBranch
import Mathlib.Tactic

open Classical
noncomputable section

lemma OrdinaryCrossingLocalBranchDataExistsBelow
    (gamma : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ gamma.relativeInterior) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ radius : ℝ, 0 < radius → radius < epsilon →
        Nonempty (OrdinaryCrossingLocalBranchData gamma p radius) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have local_carrier :
      ∀ (beforeIndex afterIndex : ℕ)
        (hbefore : beforeIndex + 1 < gamma.vertices.length)
        (hafter : afterIndex + 1 < gamma.vertices.length),
        (∀ (j : ℕ), (hj : j + 1 < gamma.vertices.length) →
          j ≠ beforeIndex → j ≠ afterIndex →
            p ∉ segment ℝ gamma.vertices[j] gamma.vertices[j + 1]) →
        ∃ delta : ℝ, 0 < delta ∧
          ∀ radius : ℝ, 0 < radius → radius < delta →
            Metric.closedBall p radius ∩ gamma.carrier =
              Metric.closedBall p radius ∩
                (segment ℝ gamma.vertices[beforeIndex]
                    gamma.vertices[beforeIndex + 1] ∪
                  segment ℝ gamma.vertices[afterIndex]
                    gamma.vertices[afterIndex + 1]) := by
    intro beforeIndex afterIndex hbefore hafter hp_other
    let forbidden : Set E :=
      ⋃ j : Fin (gamma.vertices.length - 1),
        if j.1 = beforeIndex ∨ j.1 = afterIndex then (∅ : Set E)
        else segment ℝ gamma.vertices[j.1] gamma.vertices[j.1 + 1]
    have hforbidden_closed : IsClosed forbidden := by
      exact isClosed_iUnion_of_finite fun j => by
        split_ifs
        · exact isClosed_empty
        · rw [← convexHull_pair]
          exact (by simp : ({gamma.vertices[j.1], gamma.vertices[j.1 + 1]} : Set E).Finite).isClosed_convexHull ℝ
    have hp_not_forbidden : p ∉ forbidden := by
      intro hp_forbidden
      rcases Set.mem_iUnion.mp hp_forbidden with ⟨j, hpj⟩
      by_cases hj_allowed : j.1 = beforeIndex ∨ j.1 = afterIndex
      · simp [hj_allowed] at hpj
      · rw [show (if j.1 = beforeIndex ∨ j.1 = afterIndex then (∅ : Set E)
              else segment ℝ gamma.vertices[j.1] gamma.vertices[j.1 + 1]) =
            segment ℝ gamma.vertices[j.1] gamma.vertices[j.1 + 1] by
          simp [hj_allowed]] at hpj
        exact hp_other j.1 (by omega) (fun h => hj_allowed (Or.inl h))
          (fun h => hj_allowed (Or.inr h)) hpj
    have hopen : IsOpen forbiddenᶜ := hforbidden_closed.isOpen_compl
    rcases Metric.isOpen_iff.mp hopen p hp_not_forbidden with
      ⟨delta, hdelta, hball⟩
    refine ⟨delta, hdelta, ?_⟩
    intro radius hradius hradius_delta
    ext q
    constructor
    · rintro ⟨hq_closed, hq_carrier⟩
      refine ⟨hq_closed, ?_⟩
      rw [gamma.carrier_eq] at hq_carrier
      rcases hq_carrier with ⟨j, hj, hqj⟩
      by_cases hj_before : j = beforeIndex
      · exact Or.inl (by simpa [hj_before] using hqj)
      · by_cases hj_after : j = afterIndex
        · exact Or.inr (by simpa [hj_after] using hqj)
        · have hj_lt : j < gamma.vertices.length - 1 := by omega
          let jf : Fin (gamma.vertices.length - 1) := ⟨j, hj_lt⟩
          have hq_forbidden : q ∈ forbidden := by
            apply Set.mem_iUnion.mpr
            refine ⟨jf, ?_⟩
            simp [jf, hj_before, hj_after, hqj]
          have hq_ball : q ∈ Metric.ball p delta := by
            rw [Metric.mem_ball]
            have hq_dist : dist q p ≤ radius := by
              simpa [Metric.mem_closedBall] using hq_closed
            exact hq_dist.trans_lt hradius_delta
          exact (hball hq_ball hq_forbidden).elim
    · rintro ⟨hq_closed, hq_local⟩
      refine ⟨hq_closed, ?_⟩
      rw [gamma.carrier_eq]
      rcases hq_local with hq_before | hq_after
      · exact ⟨beforeIndex, hbefore, hq_before⟩
      · exact ⟨afterIndex, hafter, hq_after⟩
  rw [gamma.relativeInterior_eq] at hp
  rcases hp with ⟨hp_carrier, hp_endpoints⟩
  have hp_both : p ≠ gamma.source ∧ p ≠ gamma.target := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hp_endpoints
  have hp_ne_source : p ≠ gamma.source := hp_both.1
  have hp_ne_target : p ≠ gamma.target := by
    exact hp_both.2
  by_cases hp_listed : p ∈ gamma.vertices
  · rcases List.getElem_of_mem hp_listed with ⟨k, hk, hkp⟩
    have hsource : gamma.vertices[0] = gamma.source := by
      have hhead := gamma.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hk_pos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      apply hp_ne_source
      simpa [← hkp, hk0] using hsource
    have htarget : gamma.vertices[gamma.vertices.length - 1] = gamma.target := by
      have hlast := gamma.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      exact Option.some.inj hlast
    have hk_next : k + 1 < gamma.vertices.length := by
      by_contra h
      have hklast : k = gamma.vertices.length - 1 := by omega
      apply hp_ne_target
      simpa [← hkp, hklast] using htarget
    let beforeIndex := k - 1
    let afterIndex := k
    have hk_prev_eq : beforeIndex + 1 = k := by
      dsimp [beforeIndex]
      omega
    have hbefore : beforeIndex + 1 < gamma.vertices.length := by
      rw [hk_prev_eq]
      omega
    have hafter : afterIndex + 1 < gamma.vertices.length := by
      simpa [afterIndex] using hk_next
    have hp_other :
        ∀ (j : ℕ), (hj : j + 1 < gamma.vertices.length) →
          j ≠ beforeIndex → j ≠ afterIndex →
            p ∉ segment ℝ gamma.vertices[j] gamma.vertices[j + 1] := by
      intro j hj hj_before hj_after hpj
      have hk_ne_j : k ≠ j := by simpa [afterIndex] using Ne.symm hj_after
      have hk_ne_jsucc : k ≠ j + 1 := by
        intro h
        apply hj_before
        dsimp [beforeIndex]
        omega
      have hvertex_avoid :=
        PolygonalArcVertexAvoidsNonincidentSegment gamma hk hj hk_ne_j hk_ne_jsucc
      exact hvertex_avoid (by simpa [hkp] using hpj)
    rcases local_carrier beforeIndex afterIndex hbefore hafter hp_other with
      ⟨delta, hdelta, hlocal⟩
    have hpa : p ≠ gamma.vertices[beforeIndex] := by
      intro h
      have hidx := (gamma.simple_vertices.getElem_inj_iff
        (i := k) (j := beforeIndex) (hi := hk) (hj := by omega)).1
        (hkp.trans h)
      dsimp [beforeIndex] at hidx
      omega
    have hpb : p ≠ gamma.vertices[afterIndex + 1] := by
      intro h
      have hidx := (gamma.simple_vertices.getElem_inj_iff
        (i := k) (j := afterIndex + 1) (hi := hk) (hj := hafter)).1
        (hkp.trans h)
      dsimp [afterIndex] at hidx
      omega
    let epsilon := min delta
      (min (dist p gamma.vertices[beforeIndex])
        (dist p gamma.vertices[afterIndex + 1]))
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact lt_min hdelta (lt_min (dist_pos.mpr hpa) (dist_pos.mpr hpb))
    refine ⟨epsilon, hepsilon, ?_⟩
    intro radius hradius hradius_epsilon
    have hr_delta : radius < delta :=
      hradius_epsilon.trans_le (min_le_left _ _)
    have hr_before : radius < dist p gamma.vertices[beforeIndex] :=
      hradius_epsilon.trans_le ((min_le_right delta _).trans (min_le_left _ _))
    have hr_after : radius < dist p gamma.vertices[afterIndex + 1] :=
      hradius_epsilon.trans_le ((min_le_right delta _).trans (min_le_right _ _))
    obtain ⟨beforeGate, hbeforeGate, hbeforeGate_unique⟩ :=
      StraightSegmentEndpointSphereBranch hpa hradius hr_before
    obtain ⟨afterGate, hafterGate, hafterGate_unique⟩ :=
      StraightSegmentEndpointSphereBranch hpb hradius hr_after
    have hbeforeGate_open :
        beforeGate ∈ openSegment ℝ gamma.vertices[beforeIndex] p := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        have hsphere := hbeforeGate.1
        rw [← h, Metric.mem_sphere, dist_comm] at hsphere
        linarith
      · intro h
        have hsphere := hbeforeGate.1
        rw [← h, Metric.mem_sphere, dist_self] at hsphere
        linarith
      · simpa [segment_symm] using hbeforeGate.2
    have hafterGate_open :
        afterGate ∈ openSegment ℝ p gamma.vertices[afterIndex + 1] := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        have hsphere := hafterGate.1
        rw [← h, Metric.mem_sphere, dist_self] at hsphere
        linarith
      · intro h
        have hsphere := hafterGate.1
        rw [← h, Metric.mem_sphere] at hsphere
        rw [dist_comm] at hsphere
        linarith
      · exact hafterGate.2
    have hgates_ne : beforeGate ≠ afterGate := by
      intro hgates
      have hboth : beforeGate ∈
          segment ℝ gamma.vertices[beforeIndex] gamma.vertices[beforeIndex + 1] ∩
            segment ℝ gamma.vertices[afterIndex] gamma.vertices[afterIndex + 1] := by
        constructor
        · simpa [hk_prev_eq, hkp] using
            (openSegment_subset_segment ℝ gamma.vertices[beforeIndex] p
              hbeforeGate_open)
        · simpa [hgates, afterIndex, hkp] using hafterGate.2
      have hinter := gamma.segment_intersections hbefore hafter (by
        dsimp [beforeIndex, afterIndex]
        omega)
      rw [hinter, if_pos (by simpa [afterIndex] using hk_prev_eq.symm)] at hboth
      have hgate_p : beforeGate = p := by simpa [hkp, afterIndex] using hboth
      have hsphere := hbeforeGate.1
      rw [hgate_p, Metric.mem_sphere, dist_self] at hsphere
      linarith
    have hsphere_carrier :
        Metric.sphere p radius ∩ gamma.carrier = {beforeGate, afterGate} := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        have hq_closed : q ∈ Metric.closedBall p radius :=
          Metric.sphere_subset_closedBall hq.1
        have hq_local : q ∈
            segment ℝ gamma.vertices[beforeIndex] gamma.vertices[beforeIndex + 1] ∪
              segment ℝ gamma.vertices[afterIndex] gamma.vertices[afterIndex + 1] := by
          have hmem : q ∈ Metric.closedBall p radius ∩ gamma.carrier :=
            ⟨hq_closed, hq.2⟩
          rw [hlocal radius hradius hr_delta] at hmem
          exact hmem.2
        rcases hq_local with hq_before | hq_after
        · left
          apply hbeforeGate_unique
          exact ⟨hq.1, by simpa [hk_prev_eq, hkp, segment_symm] using hq_before⟩
        · right
          apply hafterGate_unique
          exact ⟨hq.1, by simpa [afterIndex, hkp] using hq_after⟩
      · rintro (rfl | rfl)
        · refine ⟨hbeforeGate.1, ?_⟩
          rw [gamma.carrier_eq]
          exact ⟨beforeIndex, hbefore,
            by simpa [hk_prev_eq, hkp] using
              (openSegment_subset_segment ℝ gamma.vertices[beforeIndex] p
                hbeforeGate_open)⟩
        · refine ⟨hafterGate.1, ?_⟩
          rw [gamma.carrier_eq]
          exact ⟨afterIndex, hafter,
            by simpa [afterIndex, hkp] using
              (openSegment_subset_segment ℝ p gamma.vertices[afterIndex + 1]
                hafterGate_open)⟩
    exact ⟨{
      radius_pos := hradius
      beforeIndex := beforeIndex
      afterIndex := afterIndex
      beforeIndex_valid := hbefore
      afterIndex_valid := hafter
      center_case := Or.inr ⟨by simpa [beforeIndex, afterIndex] using hk_prev_eq.symm,
        by simpa [afterIndex] using hkp.symm⟩
      beforeGate := beforeGate
      afterGate := afterGate
      beforeGate_open := hbeforeGate_open
      afterGate_open := hafterGate_open
      beforeGate_on_sphere := hbeforeGate.1
      afterGate_on_sphere := hafterGate.1
      gates_ne := hgates_ne
      closedBall_carrier_eq := hlocal radius hradius hr_delta
      sphere_carrier_eq := hsphere_carrier }⟩
  · rw [gamma.carrier_eq] at hp_carrier
    rcases hp_carrier with ⟨i, hi, hp_segment⟩
    have hleft : gamma.vertices[i] ≠ p := by
      intro h
      apply hp_listed
      rw [← h]
      exact List.getElem_mem (by omega)
    have hright : gamma.vertices[i + 1] ≠ p := by
      intro h
      apply hp_listed
      rw [← h]
      exact List.getElem_mem hi
    have hp_open : p ∈ openSegment ℝ gamma.vertices[i] gamma.vertices[i + 1] :=
      mem_openSegment_of_ne_left_right hleft hright hp_segment
    have hp_other :
        ∀ (j : ℕ), (hj : j + 1 < gamma.vertices.length) →
          j ≠ i → j ≠ i →
            p ∉ segment ℝ gamma.vertices[j] gamma.vertices[j + 1] := by
      intro j hj hj_ne _ hpj
      rcases lt_trichotomy i j with hij | hij | hji
      · have hp_inter : p ∈
            segment ℝ gamma.vertices[i] gamma.vertices[i + 1] ∩
              segment ℝ gamma.vertices[j] gamma.vertices[j + 1] :=
          ⟨hp_segment, hpj⟩
        have hinter := gamma.segment_intersections hi hj hij
        rw [hinter] at hp_inter
        by_cases hadj : j = i + 1
        · rw [if_pos hadj] at hp_inter
          apply hp_listed
          have hp_eq : p = gamma.vertices[j] := by simpa using hp_inter
          rw [hp_eq]
          exact List.getElem_mem (by omega)
        · rw [if_neg hadj] at hp_inter
          exact hp_inter.elim
      · exact (hj_ne hij.symm).elim
      · have hp_inter : p ∈
            segment ℝ gamma.vertices[j] gamma.vertices[j + 1] ∩
              segment ℝ gamma.vertices[i] gamma.vertices[i + 1] :=
          ⟨hpj, hp_segment⟩
        have hinter := gamma.segment_intersections hj hi hji
        rw [hinter] at hp_inter
        by_cases hadj : i = j + 1
        · rw [if_pos hadj] at hp_inter
          apply hp_listed
          have hp_eq : p = gamma.vertices[i] := by simpa using hp_inter
          rw [hp_eq]
          exact List.getElem_mem (by omega)
        · rw [if_neg hadj] at hp_inter
          exact hp_inter.elim
    rcases local_carrier i i hi hi hp_other with ⟨delta, hdelta, hlocal⟩
    let epsilon := min delta
      (min (dist p gamma.vertices[i]) (dist p gamma.vertices[i + 1]))
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact lt_min hdelta (lt_min (dist_pos.mpr hleft.symm) (dist_pos.mpr hright.symm))
    refine ⟨epsilon, hepsilon, ?_⟩
    intro radius hradius hradius_epsilon
    have hr_delta : radius < delta :=
      hradius_epsilon.trans_le (min_le_left _ _)
    have hr_left : radius < dist p gamma.vertices[i] :=
      hradius_epsilon.trans_le ((min_le_right delta _).trans (min_le_left _ _))
    have hr_right : radius < dist p gamma.vertices[i + 1] :=
      hradius_epsilon.trans_le ((min_le_right delta _).trans (min_le_right _ _))
    obtain ⟨beforeGate, hbeforeGate, hbeforeGate_unique⟩ :=
      StraightSegmentEndpointSphereBranch hleft.symm hradius hr_left
    obtain ⟨afterGate, hafterGate, hafterGate_unique⟩ :=
      StraightSegmentEndpointSphereBranch hright.symm hradius hr_right
    have hbeforeGate_open : beforeGate ∈ openSegment ℝ gamma.vertices[i] p := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        have hsphere := hbeforeGate.1
        rw [← h, Metric.mem_sphere, dist_comm] at hsphere
        linarith
      · intro h
        have hsphere := hbeforeGate.1
        rw [← h, Metric.mem_sphere, dist_self] at hsphere
        linarith
      · simpa [segment_symm] using hbeforeGate.2
    have hafterGate_open : afterGate ∈ openSegment ℝ p gamma.vertices[i + 1] := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        have hsphere := hafterGate.1
        rw [← h, Metric.mem_sphere, dist_self] at hsphere
        linarith
      · intro h
        have hsphere := hafterGate.1
        rw [← h, Metric.mem_sphere] at hsphere
        rw [dist_comm] at hsphere
        linarith
      · exact hafterGate.2
    rw [openSegment_eq_image_lineMap] at hp_open
    rcases hp_open with ⟨t, ht, hpt⟩
    have hsegment_split :
        ∀ {q : E}, q ∈ segment ℝ gamma.vertices[i] gamma.vertices[i + 1] →
          q ∈ segment ℝ gamma.vertices[i] p ∨
            q ∈ segment ℝ p gamma.vertices[i + 1] := by
      intro q hq
      rw [segment_eq_image_lineMap] at hq
      rcases hq with ⟨s, hs, rfl⟩
      by_cases hst : s ≤ t
      · left
        rw [segment_eq_image_lineMap]
        refine ⟨s / t, ?_, ?_⟩
        · constructor
          · exact div_nonneg hs.1 ht.1.le
          · exact (div_le_one ht.1).2 hst
        · apply PiLp.ext
          intro m
          rw [← hpt]
          simp [AffineMap.lineMap_apply_module]
          field_simp [ht.1.ne']
          ring
      · right
        have hts : t ≤ s := le_of_not_ge hst
        rw [segment_eq_image_lineMap]
        refine ⟨(s - t) / (1 - t), ?_, ?_⟩
        · have hden : 0 < 1 - t := sub_pos.mpr ht.2
          constructor
          · exact div_nonneg (sub_nonneg.mpr hts) hden.le
          · rw [div_le_one hden]
            linarith [hs.2]
        · apply PiLp.ext
          intro m
          rw [← hpt]
          simp [AffineMap.lineMap_apply_module]
          have hden : 1 - t ≠ 0 := by linarith [ht.2]
          field_simp [hden]
          ring
    have hgates_ne : beforeGate ≠ afterGate := by
      obtain ⟨q1, q2, hq_ne, hq1_sphere, hq1_segment, hq2_sphere,
          hq2_segment, _⟩ :=
        StraightSegmentInteriorSphereBranch
          (by rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, hpt⟩)
          hradius hr_left hr_right
      intro hgates
      have hq1_eq : q1 = beforeGate := by
        rcases hsegment_split hq1_segment with hq1_left | hq1_right
        · exact hbeforeGate_unique q1
            ⟨hq1_sphere, by simpa [segment_symm] using hq1_left⟩
        · have := hafterGate_unique q1 ⟨hq1_sphere, hq1_right⟩
          exact this.trans hgates.symm
      have hq2_eq : q2 = beforeGate := by
        rcases hsegment_split hq2_segment with hq2_left | hq2_right
        · exact hbeforeGate_unique q2
            ⟨hq2_sphere, by simpa [segment_symm] using hq2_left⟩
        · have := hafterGate_unique q2 ⟨hq2_sphere, hq2_right⟩
          exact this.trans hgates.symm
      exact hq_ne (hq1_eq.trans hq2_eq.symm)
    have hsphere_carrier :
        Metric.sphere p radius ∩ gamma.carrier = {beforeGate, afterGate} := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        have hq_closed : q ∈ Metric.closedBall p radius :=
          Metric.sphere_subset_closedBall hq.1
        have hq_segment : q ∈ segment ℝ gamma.vertices[i] gamma.vertices[i + 1] := by
          have hmem : q ∈ Metric.closedBall p radius ∩ gamma.carrier :=
            ⟨hq_closed, hq.2⟩
          rw [hlocal radius hradius hr_delta] at hmem
          rcases hmem.2 with h | h
          · exact h
          · exact h
        rcases hsegment_split hq_segment with hq_left | hq_right
        · left
          exact hbeforeGate_unique q
            ⟨hq.1, by simpa [segment_symm] using hq_left⟩
        · right
          exact hafterGate_unique q ⟨hq.1, hq_right⟩
      · rintro (rfl | rfl)
        · refine ⟨hbeforeGate.1, ?_⟩
          rw [gamma.carrier_eq]
          exact ⟨i, hi,
            (convex_segment gamma.vertices[i] gamma.vertices[i + 1]).segment_subset
              (left_mem_segment ℝ _ _)
              (openSegment_subset_segment ℝ _ _
                (by rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, hpt⟩))
              (openSegment_subset_segment ℝ gamma.vertices[i] p hbeforeGate_open)⟩
        · refine ⟨hafterGate.1, ?_⟩
          rw [gamma.carrier_eq]
          exact ⟨i, hi,
            (convex_segment gamma.vertices[i] gamma.vertices[i + 1]).segment_subset
              (openSegment_subset_segment ℝ _ _
                (by rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, hpt⟩))
              (right_mem_segment ℝ _ _)
              (openSegment_subset_segment ℝ p gamma.vertices[i + 1] hafterGate_open)⟩
    exact ⟨{
      radius_pos := hradius
      beforeIndex := i
      afterIndex := i
      beforeIndex_valid := hi
      afterIndex_valid := hi
      center_case := Or.inl ⟨rfl,
        by rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, hpt⟩⟩
      beforeGate := beforeGate
      afterGate := afterGate
      beforeGate_open := hbeforeGate_open
      afterGate_open := hafterGate_open
      beforeGate_on_sphere := hbeforeGate.1
      afterGate_on_sphere := hafterGate.1
      gates_ne := hgates_ne
      closedBall_carrier_eq := hlocal radius hradius hr_delta
      sphere_carrier_eq := hsphere_carrier }⟩
