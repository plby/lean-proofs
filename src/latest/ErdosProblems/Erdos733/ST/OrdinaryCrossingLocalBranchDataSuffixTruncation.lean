import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchGateCarrier
import ErdosProblems.Erdos733.ST.StraightSegmentRetainedOrder

open Classical
noncomputable section


-- [TABLET NODE: OrdinaryCrossingLocalBranchDataSuffixTruncation]
lemma OrdinaryCrossingLocalBranchDataSuffixTruncation
    (Q S : PolygonalArc)
    (c p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) (cutIndex : ℕ)
    (hcutValid : cutIndex + 1 < Q.vertices.length)
    (hcOpen : c ∈ openSegment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1])
    (hvertices : S.vertices = c :: Q.vertices.drop (cutIndex + 1))
    (branch : OrdinaryCrossingLocalBranchData Q p radius)
    (hcOutside : c ∉ Metric.closedBall p radius)
    (hlocalCarrier :
      segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆ S.carrier)
    (hclosed : Metric.closedBall p radius ∩ S.carrier =
      Metric.closedBall p radius ∩ Q.carrier)
    (hsphere : Metric.sphere p radius ∩ S.carrier =
      Metric.sphere p radius ∩ Q.carrier) :
    ∃ branchS : OrdinaryCrossingLocalBranchData S p radius,
      branchS.beforeGate = branch.beforeGate ∧
        branchS.afterGate = branch.afterGate := by
-- BODY
  have hSlen : S.vertices.length = Q.vertices.length - cutIndex := by
    rw [hvertices]
    simp [List.length_drop]
    omega
  have hSzero : S.vertices[0] = c := by
    have hopt := congrArg
      (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[0]?) hvertices
    rw [List.getElem?_eq_getElem (by rw [hSlen]; omega),
      List.getElem?_eq_getElem (by simp)] at hopt
    exact Option.some.inj hopt
  have hSsucc : ∀ n (hn : n + 1 < S.vertices.length),
      S.vertices[n + 1] = Q.vertices[cutIndex + 1 + n]'(by
        rw [hSlen] at hn
        omega) := by
    intro n hn
    have hdrop : n < (Q.vertices.drop (cutIndex + 1)).length := by
      simp [List.length_drop]
      rw [hSlen] at hn
      omega
    have hopt := congrArg
      (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[n + 1]?) hvertices
    rw [List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem (by simpa using hdrop)] at hopt
    simpa using Option.some.inj hopt
  have hSpos : ∀ n (hnpos : 0 < n) (hn : n < S.vertices.length),
      S.vertices[n] = Q.vertices[cutIndex + n]'(by
        rw [hSlen] at hn
        omega) := by
    intro n hnpos hn
    cases n with
    | zero => omega
    | succ q =>
        simpa [Nat.add_assoc, Nat.add_comm 1 q] using
          hSsucc q (by simpa using hn)
  have open_left_trans :
      ∀ {a b d x : EuclideanSpace ℝ (Fin 2)},
        b ∈ openSegment ℝ a d → x ∈ openSegment ℝ a b →
          x ∈ openSegment ℝ a d := by
    intro a b d x hb hx
    rw [openSegment_eq_image_lineMap] at hb hx ⊢
    rcases hb with ⟨t, ht, hbt⟩
    rcases hx with ⟨s, hs, hxs⟩
    refine ⟨s * t, ⟨mul_pos hs.1 ht.1, ?_⟩, ?_⟩
    · have hlt : s * t < t := by
        simpa using mul_lt_mul_of_pos_right hs.2 ht.1
      exact hlt.trans ht.2
    · rw [← hxs, ← hbt]
      exact (AffineMap.lineMap_lineMap_right a d t s).symm
  have hbefore0 : branch.beforeIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.beforeIndex_valid
  have before_open_full : branch.beforeGate ∈ openSegment ℝ
      (Q.vertices.get ⟨branch.beforeIndex, hbefore0⟩)
        (Q.vertices.get ⟨branch.beforeIndex + 1, branch.beforeIndex_valid⟩) := by
    rcases branch.center_case with hcenter | hcenter
    · have hafter1 : branch.afterIndex + 1 < Q.vertices.length :=
        branch.afterIndex_valid
      have hp : p ∈ openSegment ℝ
          (Q.vertices.get ⟨branch.afterIndex, by omega⟩)
          (Q.vertices.get ⟨branch.afterIndex + 1, hafter1⟩) := by
        simpa only [List.get_eq_getElem, hcenter.1] using hcenter.2
      have hg : branch.beforeGate ∈ openSegment ℝ
          (Q.vertices.get ⟨branch.afterIndex, by omega⟩) p := by
        simpa only [List.get_eq_getElem, hcenter.1] using branch.beforeGate_open
      have hfull := open_left_trans hp hg
      simpa only [List.get_eq_getElem, hcenter.1] using hfull
    · simpa only [List.get_eq_getElem, hcenter.1, hcenter.2] using
        branch.beforeGate_open
  have hbeforeMemS : branch.beforeGate ∈ S.carrier :=
    hlocalCarrier (Or.inl (left_mem_segment ℝ branch.beforeGate p))
  have hbeforeGe : cutIndex ≤ branch.beforeIndex := by
    by_contra hnot
    have hbeforeLt : branch.beforeIndex < cutIndex := by omega
    rw [S.carrier_eq] at hbeforeMemS
    rcases hbeforeMemS with ⟨j, hj, hjmem⟩
    let m := cutIndex + j
    have hmValid : m + 1 < Q.vertices.length := by
      dsimp [m]
      rw [hSlen] at hj
      omega
    have hmGe : cutIndex ≤ m := by dsimp [m]; omega
    have hjQ : branch.beforeGate ∈
        segment ℝ Q.vertices[m] Q.vertices[m + 1] := by
      by_cases hj0 : j = 0
      · subst j
        dsimp [m]
        have hSone : S.vertices[1] = Q.vertices[cutIndex + 1] := by
          simpa using hSsucc 0 hj
        have hseg : segment ℝ c Q.vertices[cutIndex + 1] ⊆
            segment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] :=
          (convex_segment Q.vertices[cutIndex] Q.vertices[cutIndex + 1]).segment_subset
            (openSegment_subset_segment ℝ _ _ hcOpen)
            (right_mem_segment ℝ _ _)
        exact hseg (by simpa [hSzero, hSone] using hjmem)
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hleft := hSpos j hjpos (by omega)
        have hright := hSsucc j hj
        simpa [m, hleft, hright, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hjmem
    have hIndexLt : branch.beforeIndex < m := lt_of_lt_of_le hbeforeLt hmGe
    have hinter := Q.segment_intersections branch.beforeIndex_valid hmValid hIndexLt
    have hboth : branch.beforeGate ∈
        segment ℝ Q.vertices[branch.beforeIndex] Q.vertices[branch.beforeIndex + 1] ∩
          segment ℝ Q.vertices[m] Q.vertices[m + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ before_open_full, hjQ⟩
    rw [hinter] at hboth
    split at hboth
    · rename_i hmEq
      have heq : branch.beforeGate = Q.vertices[m] := by simpa using hboth
      have heq' : branch.beforeGate = Q.vertices[branch.beforeIndex + 1] := by
        simpa only [hmEq] using heq
      have hright : Q.vertices[branch.beforeIndex] =
          Q.vertices[branch.beforeIndex + 1] :=
        right_mem_openSegment_iff.mp (by
          simpa only [List.get_eq_getElem, heq'] using before_open_full)
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := branch.beforeIndex) (j := branch.beforeIndex + 1)
        (hi := hbefore0) (hj := branch.beforeIndex_valid)).1 hright
      omega
    · simpa using hboth
  have first_segment_of_open : ∀ z,
      z ∈ S.carrier →
        z ∈ openSegment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] →
          z ∈ segment ℝ c Q.vertices[cutIndex + 1] := by
    intro z hzS hzOpen
    rw [S.carrier_eq] at hzS
    rcases hzS with ⟨j, hj, hjmem⟩
    by_cases hj0 : j = 0
    · subst j
      have hSone : S.vertices[1] = Q.vertices[cutIndex + 1] := by
        simpa using hSsucc 0 hj
      simpa [hSzero, hSone] using hjmem
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      let m := cutIndex + j
      have hmValid : m + 1 < Q.vertices.length := by
        dsimp [m]
        rw [hSlen] at hj
        omega
      have hmGt : cutIndex < m := by dsimp [m]; omega
      have hjQ : z ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1] := by
        have hleft := hSpos j hjpos (by omega)
        have hright := hSsucc j hj
        simpa [m, hleft, hright, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hjmem
      have hinter := Q.segment_intersections hcutValid hmValid hmGt
      have hboth : z ∈
          segment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1] ∩
            segment ℝ Q.vertices[m] Q.vertices[m + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hzOpen, hjQ⟩
      rw [hinter] at hboth
      split at hboth
      · rename_i hmEq
        have hzeq : z = Q.vertices[m] := by simpa using hboth
        have hzeq' : z = Q.vertices[cutIndex + 1] := by
          simpa only [hmEq] using hzeq
        have hright : Q.vertices[cutIndex] = Q.vertices[cutIndex + 1] :=
          right_mem_openSegment_iff.mp (by simpa only [hzeq'] using hzOpen)
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := cutIndex) (j := cutIndex + 1)
          (hi := by omega) (hj := hcutValid)).1 hright
        omega
      · simpa using hboth
  have shifted_segment : ∀ i (hiCut : cutIndex < i)
      (hi : i + 1 < Q.vertices.length),
      let n := i - cutIndex
      n + 1 < S.vertices.length ∧
        S.vertices[n] = Q.vertices[i] ∧ S.vertices[n + 1] = Q.vertices[i + 1] := by
    intro i hiCut hi
    dsimp
    have hnpos : 0 < i - cutIndex := by omega
    have hnvalid : i - cutIndex + 1 < S.vertices.length := by
      rw [hSlen]
      omega
    refine ⟨hnvalid, ?_, ?_⟩
    · simpa [Nat.add_sub_of_le hiCut.le] using
        hSpos (i - cutIndex) hnpos (by omega)
    · have hsucc := hSsucc (i - cutIndex) hnvalid
      have hind : cutIndex + 1 + (i - cutIndex) = i + 1 := by omega
      simpa only [hind] using hsucc
  rcases lt_or_eq_of_le hbeforeGe with hbeforeGt | hbeforeEq
  · have hbeforeGt' : cutIndex < branch.beforeIndex := hbeforeGt
    have hafterGt : cutIndex < branch.afterIndex := by
      rcases branch.center_case with h | h <;> omega
    have hb := shifted_segment branch.beforeIndex hbeforeGt'
      branch.beforeIndex_valid
    have ha := shifted_segment branch.afterIndex hafterGt branch.afterIndex_valid
    let beforeIndex := branch.beforeIndex - cutIndex
    let afterIndex := branch.afterIndex - cutIndex
    refine ⟨{
      radius_pos := branch.radius_pos
      beforeIndex := beforeIndex
      afterIndex := afterIndex
      beforeIndex_valid := hb.1
      afterIndex_valid := ha.1
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
        refine ⟨by dsimp [beforeIndex, afterIndex]; omega, ?_⟩
        simpa only [beforeIndex, hb.2.1, hb.2.2] using h.2
      · right
        refine ⟨by dsimp [beforeIndex, afterIndex]; omega, ?_⟩
        simpa only [afterIndex, ha.2.1] using h.2
    · simpa only [beforeIndex, hb.2.1] using branch.beforeGate_open
    · simpa only [afterIndex, ha.2.2] using branch.afterGate_open
    · rw [hclosed, branch.closedBall_carrier_eq]
      simp only [beforeIndex, afterIndex, hb.2.1, hb.2.2, ha.2.1, ha.2.2]
    · rw [hsphere, branch.sphere_carrier_eq]
  · have hbeforeEq' : branch.beforeIndex = cutIndex := hbeforeEq.symm
    have hbeforeFirst : branch.beforeGate ∈
        segment ℝ c Q.vertices[cutIndex + 1] :=
      first_segment_of_open branch.beforeGate hbeforeMemS
        (by
          simpa only [List.get_eq_getElem, hbeforeEq'] using before_open_full)
    have hcNeBefore : c ≠ branch.beforeGate := by
      intro h
      apply hcOutside
      rw [h]
      exact Metric.sphere_subset_closedBall branch.beforeGate_on_sphere
    have hcutNe : Q.vertices[cutIndex + 1] ≠ Q.vertices[cutIndex] := by
      intro h
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := cutIndex + 1) (j := cutIndex)
        (hi := hcutValid) (hj := by omega)).1 h
      omega
    have hgateCarrier := OrdinaryCrossingLocalBranchGateCarrier Q p radius branch
    rcases branch.center_case with hsame | hlisted
    · have hafterEq : branch.afterIndex = cutIndex := by omega
      have hpOpenFull : p ∈ openSegment ℝ Q.vertices[cutIndex + 1]
          Q.vertices[cutIndex] := by
        simpa only [hbeforeEq', openSegment_symm ℝ] using hsame.2
      have hpMemS : p ∈ S.carrier :=
        hlocalCarrier (Or.inl (right_mem_segment ℝ branch.beforeGate p))
      have hpFirst : p ∈ segment ℝ Q.vertices[cutIndex + 1] c := by
        simpa only [segment_symm ℝ] using
          first_segment_of_open p hpMemS
            (by simpa only [openSegment_symm ℝ] using hpOpenFull)
      have hbeforeFirst' : branch.beforeGate ∈
          segment ℝ Q.vertices[cutIndex + 1] c := by
        simpa only [segment_symm ℝ] using hbeforeFirst
      have hcNeP : p ≠ c := by
        intro hpc
        apply hcOutside
        rw [← hpc]
        simpa [Metric.mem_closedBall] using branch.radius_pos.le
      have hordered := StraightSegmentRetainedOrder Q.vertices[cutIndex + 1]
        Q.vertices[cutIndex] p branch.beforeGate c hcutNe hpOpenFull
        (by simpa only [hbeforeEq', openSegment_symm ℝ] using
          branch.beforeGate_open)
        (by simpa only [openSegment_symm ℝ] using hcOpen)
        hpFirst hbeforeFirst' hcNeP hcNeBefore.symm
      have hcenterNew : p ∈ openSegment ℝ S.vertices[0] S.vertices[1] := by
        have hSone : S.vertices[1] = Q.vertices[cutIndex + 1] := by
          simpa using hSsucc 0 (by rw [hSlen]; omega)
        simpa only [hSzero, hSone, openSegment_symm ℝ] using hordered.1
      have hbeforeNew : branch.beforeGate ∈ openSegment ℝ S.vertices[0] p := by
        simpa only [hSzero, openSegment_symm ℝ] using hordered.2
      have hafterNew : branch.afterGate ∈ openSegment ℝ p S.vertices[1] := by
        have hSone : S.vertices[1] = Q.vertices[cutIndex + 1] := by
          simpa using hSsucc 0 (by rw [hSlen]; omega)
        simpa only [hSone, hafterEq] using branch.afterGate_open
      have hbeforeFull : branch.beforeGate ∈ segment ℝ S.vertices[0] S.vertices[1] :=
        (convex_segment S.vertices[0] S.vertices[1]).segment_subset
          (left_mem_segment ℝ _ _)
          (openSegment_subset_segment ℝ _ _ hcenterNew)
          (openSegment_subset_segment ℝ _ _ hbeforeNew)
      have hafterFull : branch.afterGate ∈ segment ℝ S.vertices[0] S.vertices[1] :=
        (convex_segment S.vertices[0] S.vertices[1]).segment_subset
          (openSegment_subset_segment ℝ _ _ hcenterNew)
          (right_mem_segment ℝ _ _)
          (openSegment_subset_segment ℝ _ _ hafterNew)
      have hlocalSegment :
          segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆
            segment ℝ S.vertices[0] S.vertices[1] := by
        apply Set.union_subset
        · exact (convex_segment _ _).segment_subset hbeforeFull
            (openSegment_subset_segment ℝ _ _ hcenterNew)
        · exact (convex_segment _ _).segment_subset
            (openSegment_subset_segment ℝ _ _ hcenterNew) hafterFull
      have hnewClosed : Metric.closedBall p radius ∩ S.carrier =
          Metric.closedBall p radius ∩
            (segment ℝ S.vertices[0] S.vertices[1] ∪
              segment ℝ S.vertices[0] S.vertices[1]) := by
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
          rw [S.carrier_eq]
          exact ⟨0, by rw [hSlen]; omega, hz.2⟩
      refine ⟨{
        radius_pos := branch.radius_pos
        beforeIndex := 0
        afterIndex := 0
        beforeIndex_valid := by rw [hSlen]; omega
        afterIndex_valid := by rw [hSlen]; omega
        center_case := Or.inl ⟨rfl, hcenterNew⟩
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
    · have hafterEq : branch.afterIndex = cutIndex + 1 := by omega
      have hpEq : p = Q.vertices[cutIndex + 1] := by
        simpa only [hafterEq] using hlisted.2
      have hbeforeNewQ : branch.beforeGate ∈ openSegment ℝ c p := by
        apply mem_openSegment_of_ne_left_right
        · exact hcNeBefore
        · intro hgp
          have hsph := branch.beforeGate_on_sphere
          rw [Metric.mem_sphere] at hsph
          have hzero : dist branch.beforeGate p = 0 := by
            calc
              dist branch.beforeGate p = dist p p :=
                congrArg (fun x => dist x p) hgp.symm
              _ = 0 := dist_self p
          linarith [branch.radius_pos]
        · simpa only [hpEq] using hbeforeFirst
      have hcut2 : cutIndex + 2 < Q.vertices.length := by
        simpa [hafterEq, Nat.add_assoc] using branch.afterIndex_valid
      have hS2 : 2 < S.vertices.length := by
        rw [hSlen]
        omega
      have hSone : S.vertices[1] = Q.vertices[cutIndex + 1] := by
        simpa using hSsucc 0 (by rw [hSlen]; omega)
      have hStwo : S.vertices[2] = Q.vertices[cutIndex + 2] := by
        simpa [Nat.add_assoc] using hSsucc 1 hS2
      have hbeforeNew : branch.beforeGate ∈ openSegment ℝ S.vertices[0] p := by
        simpa only [hSzero] using hbeforeNewQ
      have hafterNew : branch.afterGate ∈ openSegment ℝ p S.vertices[2] := by
        simpa only [hStwo, hafterEq, Nat.add_assoc] using branch.afterGate_open
      have hlocalSegments :
          segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate ⊆
            segment ℝ S.vertices[0] S.vertices[1] ∪
              segment ℝ S.vertices[1] S.vertices[2] := by
        intro z hz
        rcases hz with hz | hz
        · left
          have hbeforeFull : branch.beforeGate ∈ segment ℝ S.vertices[0] S.vertices[1] :=
            openSegment_subset_segment ℝ _ _
              (by simpa only [hSone, hpEq] using hbeforeNew)
          exact (convex_segment S.vertices[0] S.vertices[1]).segment_subset
            hbeforeFull (right_mem_segment ℝ _ _)
            (by simpa only [hSone, hpEq] using hz)
        · right
          have hafterFull : branch.afterGate ∈ segment ℝ S.vertices[1] S.vertices[2] :=
            openSegment_subset_segment ℝ _ _
              (by simpa only [hSone, hpEq] using hafterNew)
          exact (convex_segment S.vertices[1] S.vertices[2]).segment_subset
            (left_mem_segment ℝ _ _) hafterFull
            (by simpa only [hSone, hpEq] using hz)
      have hnewClosed : Metric.closedBall p radius ∩ S.carrier =
          Metric.closedBall p radius ∩
            (segment ℝ S.vertices[0] S.vertices[1] ∪
              segment ℝ S.vertices[1] S.vertices[2]) := by
        apply Set.Subset.antisymm
        · intro z hz
          have hzQ : z ∈ Metric.closedBall p radius ∩ Q.carrier := by
            rw [← hclosed]
            exact hz
          rw [hgateCarrier] at hzQ
          exact ⟨hz.1, hlocalSegments hzQ⟩
        · intro z hz
          refine ⟨hz.1, ?_⟩
          rw [S.carrier_eq]
          rcases hz.2 with hz | hz
          · exact ⟨0, by rw [hSlen]; omega, hz⟩
          · exact ⟨1, by rw [hSlen]; omega, hz⟩
      refine ⟨{
        radius_pos := branch.radius_pos
        beforeIndex := 0
        afterIndex := 1
        beforeIndex_valid := by rw [hSlen]; omega
        afterIndex_valid := hS2
        center_case := Or.inr ⟨rfl, by simpa only [hSone, hpEq]⟩
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
