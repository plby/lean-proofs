import Mathlib.Tactic
import Util.IncidenceGeometry.OrdinaryCrossingLocalBranchGateCarrier
import Util.IncidenceGeometry.StraightSegmentRetainedOrder

open Classical
noncomputable section


lemma OrdinaryCrossingLocalBranchDataPrefixTruncation
    (Q P : PolygonalArc)
    (c p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) (cutIndex : ℕ)
    (hcutValid : cutIndex + 1 < Q.vertices.length)
    (hcOpen : c ∈ openSegment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1])
    (hvertices : P.vertices = Q.vertices.take (cutIndex + 1) ++ [c])
    (branch : OrdinaryCrossingLocalBranchData Q p radius)
    (hcOutside : c ∉ Metric.closedBall p radius)
    (hlocalCarrier :
      segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆ P.carrier)
    (hclosed : Metric.closedBall p radius ∩ P.carrier =
      Metric.closedBall p radius ∩ Q.carrier)
    (hsphere : Metric.sphere p radius ∩ P.carrier =
      Metric.sphere p radius ∩ Q.carrier) :
    ∃ branchP : OrdinaryCrossingLocalBranchData P p radius,
      branchP.beforeGate = branch.beforeGate ∧
        branchP.afterGate = branch.afterGate := by
  have hPlen : P.vertices.length = cutIndex + 2 := by
    rw [hvertices]
    simp [List.length_take]
    omega
  have hPold : ∀ n (hn : n < cutIndex + 1), P.vertices[n] = Q.vertices[n] := by
    intro n hn
    have hnP : n < P.vertices.length := by rw [hPlen]; omega
    have htake : n < (Q.vertices.take (cutIndex + 1)).length := by
      simp [List.length_take]
      omega
    have hnR : n < (Q.vertices.take (cutIndex + 1) ++ [c]).length := by
      simp [List.length_take]
      omega
    have hopt := congrArg (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[n]?) hvertices
    rw [List.getElem?_eq_getElem hnP, List.getElem?_eq_getElem hnR] at hopt
    have hval := Option.some.inj hopt
    calc
      P.vertices[n] = (Q.vertices.take (cutIndex + 1) ++ [c])[n] := hval
      _ = (Q.vertices.take (cutIndex + 1))[n] := List.getElem_append_left htake
      _ = Q.vertices[n] := List.getElem_take
  have hPcut : P.vertices[cutIndex + 1] = c := by
    have hnP : cutIndex + 1 < P.vertices.length := by rw [hPlen]; omega
    have htakeLen : (Q.vertices.take (cutIndex + 1)).length = cutIndex + 1 := by
      simp [List.length_take]
      omega
    have hnR : cutIndex + 1 <
        (Q.vertices.take (cutIndex + 1) ++ [c]).length := by simp [htakeLen]
    have hopt := congrArg
      (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[cutIndex + 1]?) hvertices
    rw [List.getElem?_eq_getElem hnP, List.getElem?_eq_getElem hnR] at hopt
    have hval := Option.some.inj hopt
    calc
      P.vertices[cutIndex + 1] =
          (Q.vertices.take (cutIndex + 1) ++ [c])[cutIndex + 1] := hval
      _ = c := by
        simpa [htakeLen] using List.getElem_append_right
          (as := Q.vertices.take (cutIndex + 1)) (bs := [c])
          (i := cutIndex + 1)
  have open_right_trans :
      ∀ {a b d x : EuclideanSpace ℝ (Fin 2)},
        b ∈ openSegment ℝ a d → x ∈ openSegment ℝ b d →
          x ∈ openSegment ℝ a d := by
    intro a b d x hb hx
    rw [openSegment_eq_image_lineMap] at hb hx ⊢
    rcases hb with ⟨t, ht, hbt⟩
    rcases hx with ⟨s, hs, hxs⟩
    refine ⟨1 - (1 - s) * (1 - t), ⟨?_, ?_⟩, ?_⟩
    · have hpos : 0 < t + s * (1 - t) :=
        add_pos ht.1 (mul_pos hs.1 (sub_pos.mpr ht.2))
      nlinarith [hpos]
    · nlinarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr ht.2)]
    · rw [← hxs, ← hbt]
      exact (AffineMap.lineMap_lineMap_left a d t s).symm
  have hafter0 : branch.afterIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.afterIndex_valid
  have after_open_full : branch.afterGate ∈ openSegment ℝ
      (Q.vertices.get ⟨branch.afterIndex, hafter0⟩)
        (Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩) := by
    rcases branch.center_case with hcenter | hcenter
    · have hbefore1 : branch.beforeIndex + 1 < Q.vertices.length := by
        simpa only [hcenter.1] using branch.afterIndex_valid
      have hbefore0 : branch.beforeIndex < Q.vertices.length := by omega
      have hp : p ∈ openSegment ℝ
          (Q.vertices.get ⟨branch.beforeIndex, hbefore0⟩)
          (Q.vertices.get ⟨branch.beforeIndex + 1, hbefore1⟩) := by
        simpa only [List.get_eq_getElem] using hcenter.2
      have hg : branch.afterGate ∈ openSegment ℝ p
          (Q.vertices.get ⟨branch.beforeIndex + 1, hbefore1⟩) := by
        simpa only [List.get_eq_getElem, hcenter.1] using branch.afterGate_open
      have hfull := open_right_trans hp hg
      simpa only [List.get_eq_getElem, hcenter.1] using hfull
    · simpa only [List.get_eq_getElem, hcenter.2] using branch.afterGate_open
  have hafterMemP : branch.afterGate ∈ P.carrier :=
    hlocalCarrier (Or.inr (right_mem_segment ℝ p branch.afterGate))
  have hafterLe : branch.afterIndex ≤ cutIndex := by
    by_contra hnot
    have hcutLt : cutIndex < branch.afterIndex := by omega
    rw [P.carrier_eq] at hafterMemP
    rcases hafterMemP with ⟨j, hj, hjmem⟩
    have hjLe : j ≤ cutIndex := by rw [hPlen] at hj; omega
    have hjQ : branch.afterGate ∈
        segment ℝ Q.vertices[j] Q.vertices[j + 1] := by
      by_cases hjlt : j < cutIndex
      · simpa [hPold j (by omega), hPold (j + 1) (by omega)] using hjmem
      · have hjeq : j = cutIndex := by omega
        subst j
        have hseg : segment ℝ Q.vertices[cutIndex] c ⊆
            segment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] :=
          (convex_segment Q.vertices[cutIndex] Q.vertices[cutIndex + 1]).segment_subset
            (left_mem_segment ℝ _ _)
            (openSegment_subset_segment ℝ _ _ hcOpen)
        exact hseg (by simpa [hPold cutIndex (by omega), hPcut] using hjmem)
    have hjQvalid : j + 1 < Q.vertices.length := by omega
    have hjAfter : j < branch.afterIndex := lt_of_le_of_lt hjLe hcutLt
    have hinter := Q.segment_intersections hjQvalid branch.afterIndex_valid hjAfter
    have hjQ' : branch.afterGate ∈
        segment ℝ (Q.vertices.get ⟨j, by omega⟩)
          (Q.vertices.get ⟨j + 1, hjQvalid⟩) := by
      simpa only [List.get_eq_getElem] using hjQ
    have hboth : branch.afterGate ∈
        segment ℝ (Q.vertices.get ⟨j, by omega⟩)
            (Q.vertices.get ⟨j + 1, hjQvalid⟩) ∩
          segment ℝ (Q.vertices.get ⟨branch.afterIndex, hafter0⟩)
            (Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩) :=
      ⟨hjQ', openSegment_subset_segment ℝ _ _ after_open_full⟩
    have hinter' :
        segment ℝ (Q.vertices.get ⟨j, by omega⟩)
            (Q.vertices.get ⟨j + 1, hjQvalid⟩) ∩
          segment ℝ (Q.vertices.get ⟨branch.afterIndex, hafter0⟩)
            (Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩) =
          if branch.afterIndex = j + 1 then
            {Q.vertices.get ⟨branch.afterIndex, hafter0⟩} else ∅ := by
      simpa only [List.get_eq_getElem] using hinter
    rw [hinter'] at hboth
    split at hboth
    · have heq : branch.afterGate =
          Q.vertices.get ⟨branch.afterIndex, hafter0⟩ := by
        simpa using hboth
      have hleft : Q.vertices.get ⟨branch.afterIndex, hafter0⟩ =
          Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩ :=
        left_mem_openSegment_iff.mp (by simpa only [heq] using after_open_full)
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := branch.afterIndex) (j := branch.afterIndex + 1)
        (hi := hafter0) (hj := branch.afterIndex_valid)).1 hleft
      omega
    · simpa using hboth
  have last_segment_of_open : ∀ z,
      z ∈ P.carrier →
        z ∈ openSegment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] →
          z ∈ segment ℝ Q.vertices[cutIndex] c := by
    intro z hzP hzOpen
    rw [P.carrier_eq] at hzP
    rcases hzP with ⟨j, hj, hjmem⟩
    have hjLe : j ≤ cutIndex := by rw [hPlen] at hj; omega
    by_cases hjlt : j < cutIndex
    · have hjQvalid : j + 1 < Q.vertices.length := by omega
      have hjQ : z ∈ segment ℝ Q.vertices[j] Q.vertices[j + 1] := by
        simpa [hPold j (by omega), hPold (j + 1) (by omega)] using hjmem
      have hinter := Q.segment_intersections hjQvalid hcutValid hjlt
      have hboth : z ∈
          segment ℝ Q.vertices[j] Q.vertices[j + 1] ∩
            segment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] :=
        ⟨hjQ, openSegment_subset_segment ℝ _ _ hzOpen⟩
      rw [hinter] at hboth
      split at hboth
      · have hzeq : z = Q.vertices[cutIndex] := by simpa using hboth
        have hleft : Q.vertices[cutIndex] = Q.vertices[cutIndex + 1] :=
          left_mem_openSegment_iff.mp (by simpa only [hzeq] using hzOpen)
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := cutIndex) (j := cutIndex + 1)
          (hi := by omega) (hj := hcutValid)).1 hleft
        omega
      · simpa using hboth
    · have hjeq : j = cutIndex := by omega
      subst j
      simpa [hPold cutIndex (by omega), hPcut] using hjmem
  rcases lt_or_eq_of_le hafterLe with hafterLt | hafterEq
  · have hbeforeLt : branch.beforeIndex < cutIndex := by
      rcases branch.center_case with h | h <;> omega
    refine ⟨{
      radius_pos := branch.radius_pos
      beforeIndex := branch.beforeIndex
      afterIndex := branch.afterIndex
      beforeIndex_valid := by rw [hPlen]; omega
      afterIndex_valid := by rw [hPlen]; omega
      center_case := ?_
      beforeGate := branch.beforeGate
      afterGate := branch.afterGate
      beforeGate_open := ?_
      afterGate_open := ?_
      beforeGate_on_sphere := branch.beforeGate_on_sphere
      afterGate_on_sphere := branch.afterGate_on_sphere
      gates_ne := branch.gates_ne
      closedBall_carrier_eq := ?_
      sphere_carrier_eq := ?_
    }, rfl, rfl⟩
    · rcases branch.center_case with h | h
      · left
        simpa only [hPold branch.beforeIndex (by omega),
          hPold (branch.beforeIndex + 1) (by omega)] using h
      · right
        simpa only [hPold branch.afterIndex (by omega)] using h
    · simpa only [hPold branch.beforeIndex (by omega)] using branch.beforeGate_open
    · simpa only [hPold (branch.afterIndex + 1) (by omega)] using branch.afterGate_open
    · rw [hclosed, branch.closedBall_carrier_eq]
      simp only [hPold branch.beforeIndex (by omega),
        hPold (branch.beforeIndex + 1) (by omega),
        hPold branch.afterIndex (by omega),
        hPold (branch.afterIndex + 1) (by omega)]
    · rw [hsphere, branch.sphere_carrier_eq]
  · have hafterEq' : branch.afterIndex = cutIndex := hafterEq
    have hafterLast : branch.afterGate ∈
        segment ℝ Q.vertices[cutIndex] c :=
      last_segment_of_open branch.afterGate hafterMemP
        (by
          simpa only [List.get_eq_getElem, hafterEq'] using after_open_full)
    have hcNeAfter : c ≠ branch.afterGate := by
      intro h
      apply hcOutside
      rw [h]
      exact Metric.sphere_subset_closedBall branch.afterGate_on_sphere
    have hcutNe : Q.vertices[cutIndex] ≠ Q.vertices[cutIndex + 1] := by
      intro h
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := cutIndex) (j := cutIndex + 1)
        (hi := by omega) (hj := hcutValid)).1 h
      omega
    have hgateCarrier := OrdinaryCrossingLocalBranchGateCarrier Q p radius branch
    rcases branch.center_case with hsame | hlisted
    · have hbeforeEq : branch.beforeIndex = cutIndex := by omega
      have hpOpenFull : p ∈ openSegment ℝ Q.vertices[cutIndex]
          Q.vertices[cutIndex + 1] := by
        simpa only [hbeforeEq] using hsame.2
      have hpMemP : p ∈ P.carrier :=
        hlocalCarrier (Or.inl (right_mem_segment ℝ branch.beforeGate p))
      have hpLast : p ∈ segment ℝ Q.vertices[cutIndex] c :=
        last_segment_of_open p hpMemP hpOpenFull
      have hcNeP : p ≠ c := by
        intro hpc
        apply hcOutside
        rw [← hpc]
        simpa [Metric.mem_closedBall] using branch.radius_pos.le
      have hordered := StraightSegmentRetainedOrder Q.vertices[cutIndex]
        Q.vertices[cutIndex + 1] p branch.afterGate c hcutNe hpOpenFull
        (by simpa only [hafterEq'] using branch.afterGate_open) hcOpen
        hpLast hafterLast hcNeP hcNeAfter.symm
      have hbeforeNew : branch.beforeGate ∈ openSegment ℝ
          P.vertices[cutIndex] p := by
        simpa only [hPold cutIndex (by omega), hbeforeEq] using branch.beforeGate_open
      have hafterNew : branch.afterGate ∈ openSegment ℝ p
          P.vertices[cutIndex + 1] := by
        simpa only [hPcut] using hordered.2
      have hpNewP : p ∈ openSegment ℝ P.vertices[cutIndex]
          P.vertices[cutIndex + 1] := by
        simpa only [hPold cutIndex (by omega), hPcut] using hordered.1
      have hbeforeFull : branch.beforeGate ∈
          segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] :=
        (convex_segment P.vertices[cutIndex] P.vertices[cutIndex + 1]).segment_subset
          (left_mem_segment ℝ _ _)
          (openSegment_subset_segment ℝ _ _ hpNewP)
          (openSegment_subset_segment ℝ _ _ hbeforeNew)
      have hafterFull : branch.afterGate ∈
          segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] :=
        (convex_segment P.vertices[cutIndex] P.vertices[cutIndex + 1]).segment_subset
          (openSegment_subset_segment ℝ _ _ hpNewP)
          (right_mem_segment ℝ _ _)
          (openSegment_subset_segment ℝ _ _ hafterNew)
      have hlocalSegment :
          segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆
            segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] := by
        apply Set.union_subset
        · exact (convex_segment _ _).segment_subset
            hbeforeFull (openSegment_subset_segment ℝ _ _ hpNewP)
        · exact (convex_segment _ _).segment_subset
            (openSegment_subset_segment ℝ _ _ hpNewP) hafterFull
      have hnewClosed : Metric.closedBall p radius ∩ P.carrier =
          Metric.closedBall p radius ∩
            (segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] ∪
              segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1]) := by
        rw [Set.union_self]
        apply Set.Subset.antisymm
        · intro z hz
          have hzQ : z ∈ Metric.closedBall p radius ∩ Q.carrier := by
            rw [← hclosed]
            exact hz
          rw [hgateCarrier] at hzQ
          exact ⟨hz.1, hlocalSegment hzQ⟩
        · intro z hz
          refine ⟨hz.1, ?_⟩
          rw [P.carrier_eq]
          exact ⟨cutIndex, by rw [hPlen]; omega, hz.2⟩
      refine ⟨{
        radius_pos := branch.radius_pos
        beforeIndex := cutIndex
        afterIndex := cutIndex
        beforeIndex_valid := by rw [hPlen]; omega
        afterIndex_valid := by rw [hPlen]; omega
        center_case := Or.inl ⟨rfl, by simpa only [hPold cutIndex (by omega), hPcut]
          using hordered.1⟩
        beforeGate := branch.beforeGate
        afterGate := branch.afterGate
        beforeGate_open := hbeforeNew
        afterGate_open := hafterNew
        beforeGate_on_sphere := branch.beforeGate_on_sphere
        afterGate_on_sphere := branch.afterGate_on_sphere
        gates_ne := branch.gates_ne
        closedBall_carrier_eq := hnewClosed
        sphere_carrier_eq := by rw [hsphere, branch.sphere_carrier_eq]
      }, rfl, rfl⟩
    · have hbeforeEq : branch.beforeIndex + 1 = cutIndex := by omega
      have hpEq : p = Q.vertices[cutIndex] := by
        simpa only [hafterEq'] using hlisted.2
      have hafterNewQ : branch.afterGate ∈ openSegment ℝ p c := by
        apply mem_openSegment_of_ne_left_right
        · intro hgp
          have hsph := branch.afterGate_on_sphere
          rw [Metric.mem_sphere] at hsph
          have hzero : dist branch.afterGate p = 0 := by
            rw [← hgp, dist_self]
          linarith [branch.radius_pos]
        · exact hcNeAfter
        · simpa only [hpEq] using hafterLast
      have hbeforeNew : branch.beforeGate ∈ openSegment ℝ
          P.vertices[branch.beforeIndex] p := by
        simpa only [hPold branch.beforeIndex (by omega)] using branch.beforeGate_open
      have hafterNew : branch.afterGate ∈ openSegment ℝ p P.vertices[cutIndex + 1] := by
        simpa only [hPcut] using hafterNewQ
      have hlocalSegments :
          segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆
            segment ℝ P.vertices[branch.beforeIndex]
                P.vertices[branch.beforeIndex + 1] ∪
              segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] := by
        intro z hz
        rcases hz with hz | hz
        · left
          have hpVertex : P.vertices[branch.beforeIndex + 1] = p := by
            calc
              P.vertices[branch.beforeIndex + 1] =
                  Q.vertices[branch.beforeIndex + 1] :=
                hPold (branch.beforeIndex + 1) (by omega)
              _ = Q.vertices[cutIndex] := by
                apply congrArg Q.vertices.get
                exact Fin.ext hbeforeEq
              _ = p := hpEq.symm
          have hbeforeFull : branch.beforeGate ∈
              segment ℝ P.vertices[branch.beforeIndex]
                P.vertices[branch.beforeIndex + 1] :=
            openSegment_subset_segment ℝ _ _
              (by simpa only [hpVertex] using hbeforeNew)
          exact (convex_segment P.vertices[branch.beforeIndex]
              P.vertices[branch.beforeIndex + 1]).segment_subset
            hbeforeFull
            (right_mem_segment ℝ P.vertices[branch.beforeIndex]
              P.vertices[branch.beforeIndex + 1])
            (by simpa only [hpVertex] using hz)
        · right
          have hpVertex : P.vertices[cutIndex] = p := by
            exact (hPold cutIndex (by omega)).trans hpEq.symm
          have hafterFull : branch.afterGate ∈
              segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1] :=
            openSegment_subset_segment ℝ _ _
              (by simpa only [hpVertex] using hafterNew)
          exact (convex_segment P.vertices[cutIndex] P.vertices[cutIndex + 1]).segment_subset
            (left_mem_segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1])
            hafterFull (by simpa only [hpVertex] using hz)
      have hnewClosed : Metric.closedBall p radius ∩ P.carrier =
          Metric.closedBall p radius ∩
            (segment ℝ P.vertices[branch.beforeIndex]
                P.vertices[branch.beforeIndex + 1] ∪
              segment ℝ P.vertices[cutIndex] P.vertices[cutIndex + 1]) := by
        apply Set.Subset.antisymm
        · intro z hz
          have hzQ : z ∈ Metric.closedBall p radius ∩ Q.carrier := by
            rw [← hclosed]
            exact hz
          rw [hgateCarrier] at hzQ
          exact ⟨hz.1, hlocalSegments hzQ⟩
        · intro z hz
          refine ⟨hz.1, ?_⟩
          rw [P.carrier_eq]
          rcases hz.2 with hz | hz
          · exact ⟨branch.beforeIndex, by rw [hPlen]; omega, hz⟩
          · exact ⟨cutIndex, by rw [hPlen]; omega, hz⟩
      refine ⟨{
        radius_pos := branch.radius_pos
        beforeIndex := branch.beforeIndex
        afterIndex := cutIndex
        beforeIndex_valid := by rw [hPlen]; omega
        afterIndex_valid := by rw [hPlen]; omega
        center_case := Or.inr ⟨by omega,
          by simpa only [hPold cutIndex (by omega), hpEq]⟩
        beforeGate := branch.beforeGate
        afterGate := branch.afterGate
        beforeGate_open := hbeforeNew
        afterGate_open := hafterNew
        beforeGate_on_sphere := branch.beforeGate_on_sphere
        afterGate_on_sphere := branch.afterGate_on_sphere
        gates_ne := branch.gates_ne
        closedBall_carrier_eq := hnewClosed
        sphere_carrier_eq := by rw [hsphere, branch.sphere_carrier_eq]
      }, rfl, rfl⟩
