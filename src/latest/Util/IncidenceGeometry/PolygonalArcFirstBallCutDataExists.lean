import Util.IncidenceGeometry.PolygonalArcFirstBallCutData
import Util.IncidenceGeometry.PolygonalArcPointCutDataExists
import Mathlib.Tactic

open Classical
noncomputable section


lemma PolygonalArcFirstBallCutDataExists
    (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (hsource : Q.source ∉ Metric.closedBall p radius)
    (htarget : Q.target ∉ Metric.ball p radius)
    (hhit : (Q.relativeInterior ∩ Metric.ball p radius).Nonempty) :
    Nonempty (PolygonalArcFirstBallCutData Q p radius) := by
  let J : Set ℕ := {i | ∃ hi : i + 1 < Q.vertices.length,
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap Q.vertices[i] Q.vertices[i + 1] t ∈
        Metric.ball p radius}
  have hJ : J.Nonempty := by
    rcases hhit with ⟨z, hzRel, hzBall⟩
    rw [Q.relativeInterior_eq] at hzRel
    rw [Q.carrier_eq] at hzRel
    rcases hzRel.1 with ⟨i, hi, hzi⟩
    rw [segment_eq_image_lineMap] at hzi
    rcases hzi with ⟨t, ht, rfl⟩
    exact ⟨i, hi, t, ht, hzBall⟩
  let i₀ := sInf J
  have hi₀J : i₀ ∈ J := Nat.sInf_mem hJ
  have hi₀min : ∀ j ∈ J, i₀ ≤ j := by
    intro j hj
    exact Nat.sInf_le hj
  rcases hi₀J with ⟨hi₀, t₀, ht₀, ht₀Ball⟩
  let F : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap Q.vertices[i₀] Q.vertices[i₀ + 1]
  let U : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ F t ∈ Metric.ball p radius}
  have hU : U.Nonempty := ⟨t₀, ht₀, ht₀Ball⟩
  have hUsub : U ⊆ Set.Icc (0 : ℝ) 1 := fun _ ht => ht.1
  have hUbdd : BddBelow U := ⟨0, fun _ ht => ht.1.1⟩
  let a := sInf U
  have haClosure : a ∈ closure U := by
    exact csInf_mem_closure hU hUbdd
  have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
    exact (isClosed_Icc.closure_subset_iff.mpr hUsub) haClosure
  have haLower : ∀ t ∈ U, a ≤ t := by
    intro t ht
    exact csInf_le hUbdd ht
  have hFaClosed : F a ∈ Metric.closedBall p radius := by
    have hmap := map_mem_closure AffineMap.lineMap_continuous haClosure
      (fun t ht => Metric.ball_subset_closedBall ht.2)
    simpa only [Metric.isClosed_closedBall.closure_eq] using hmap
  have hFaClosure : F a ∈ closure (Q.carrier ∩ Metric.ball p radius) := by
    apply map_mem_closure AffineMap.lineMap_continuous haClosure
    intro t ht
    refine ⟨?_, ht.2⟩
    rw [Q.carrier_eq]
    refine ⟨i₀, hi₀, ?_⟩
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht.1, rfl⟩
  have hFaNotBall : F a ∉ Metric.ball p radius := by
    intro hFaBall
    have hpre : F ⁻¹' Metric.ball p radius ∈ nhds a :=
      AffineMap.lineMap_continuous.continuousAt
        (Metric.isOpen_ball.mem_nhds hFaBall)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨eps, heps, hepsSub⟩
    by_cases ha0 : a = 0
    · by_cases hi0 : i₀ = 0
      · have hsource0 : Q.vertices[0] = Q.source := by
          have hhead := Q.source_eq_head
          rw [List.head?_eq_getElem?] at hhead
          rw [List.getElem?_eq_getElem (by omega)] at hhead
          exact Option.some.inj hhead
        apply hsource
        have : F a = Q.source := by simp [F, ha0, hi0, hsource0]
        exact this ▸ hFaClosed
      · have hi₀pos : 0 < i₀ := Nat.pos_of_ne_zero hi0
        let G : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
          AffineMap.lineMap Q.vertices[i₀ - 1] Q.vertices[i₀]
        have hG1 : G 1 = F a := by
          simp [G, F, ha0, Nat.sub_add_cancel hi₀pos]
        have hGpre : G ⁻¹' Metric.ball p radius ∈ nhds (1 : ℝ) :=
          AffineMap.lineMap_continuous.continuousAt
            (Metric.isOpen_ball.mem_nhds (hG1 ▸ hFaBall))
        rcases Metric.mem_nhds_iff.mp hGpre with ⟨eta, heta, hetaSub⟩
        let s : ℝ := 1 - min (eta / 2) (1 / 2)
        have hmins : 0 < min (eta / 2) (1 / 2) := by positivity
        have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
          dsimp [s]
          constructor <;> linarith [min_le_right (eta / 2) (1 / 2)]
        have hsNear : s ∈ Metric.ball (1 : ℝ) eta := by
          rw [Metric.mem_ball, Real.dist_eq]
          have hsDiff : s - 1 = -min (eta / 2) (1 / 2) := by
            dsimp [s]
            ring
          rw [hsDiff, abs_neg, abs_of_nonneg hmins.le]
          exact (min_le_left (eta / 2) (1 / 2)).trans_lt (by linarith)
        have hprevJ : i₀ - 1 ∈ J := by
          have hprevValid : i₀ - 1 + 1 < Q.vertices.length := by omega
          refine ⟨hprevValid, s, hsIcc, ?_⟩
          simpa [G, Nat.sub_add_cancel hi₀pos] using hetaSub hsNear
        have := hi₀min (i₀ - 1) hprevJ
        omega
    · have haPos : 0 < a := lt_of_le_of_ne haIcc.1 (Ne.symm ha0)
      let d : ℝ := min (eps / 2) (a / 2)
      let s : ℝ := a - d
      have hdPos : 0 < d := by dsimp [d]; positivity
      have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [s, d]
        constructor
        · linarith [min_le_right (eps / 2) (a / 2)]
        · linarith [haIcc.2]
      have hsNear : s ∈ Metric.ball a eps := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hsDiff : s - a = -d := by dsimp [s]; ring
        rw [hsDiff, abs_neg, abs_of_pos hdPos]
        exact (min_le_left (eps / 2) (a / 2)).trans_lt (by linarith)
      have hsU : s ∈ U := ⟨hsIcc, hepsSub hsNear⟩
      have has := haLower s hsU
      dsimp [s] at has
      linarith
  have hFaSphere : F a ∈ Metric.sphere p radius := by
    rw [Metric.mem_sphere]
    rw [Metric.mem_closedBall] at hFaClosed
    have hnotlt : ¬dist (F a) p < radius := by
      simpa only [Metric.mem_ball] using hFaNotBall
    exact le_antisymm hFaClosed (le_of_not_gt hnotlt)
  have haStrictUpper : a < 1 := by
    rcases hU with ⟨t, ht⟩
    have hat := haLower t ht
    by_contra hnot
    have ha1 : a = 1 := by linarith [haIcc.2]
    have ht1 : t = 1 := by linarith [ht.1.2]
    exact hFaNotBall (by simpa [ha1, ht1] using ht.2)
  let q := F a
  have hqCarrier : q ∈ Q.carrier := by
    rw [Q.carrier_eq]
    refine ⟨i₀, hi₀, ?_⟩
    rw [segment_eq_image_lineMap]
    exact ⟨a, haIcc, rfl⟩
  have hqSource : q ≠ Q.source := by
    intro hEq
    apply hsource
    exact hEq ▸ hFaClosed
  have hgetEq (l : List (EuclideanSpace ℝ (Fin 2))) (x y : ℕ)
      (hx : x < l.length) (hy : y < l.length) (hxy : x = y) :
      l[x]'hx = l[y]'hy := by
    subst y
    rfl
  have hqTarget : q ≠ Q.target := by
    intro hEq
    have hlastIdx : Q.vertices.length - 1 < Q.vertices.length := by omega
    have htargetLast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have hlast := Q.target_eq_last
      rw [List.getLast?_eq_getLast_of_ne_nil (by
        exact List.ne_nil_of_length_pos (by omega))] at hlast
      have hget : Q.vertices.getLast (by
          exact List.ne_nil_of_length_pos (by omega)) = Q.target :=
        Option.some.inj hlast
      simpa [List.getLast_eq_getElem] using hget
    let lastSeg := Q.vertices.length - 2
    have hlastSeg : lastSeg + 1 < Q.vertices.length := by
      dsimp [lastSeg]
      omega
    have hqLast : q ∈ segment ℝ Q.vertices[lastSeg] Q.vertices[lastSeg + 1] := by
      have hlastVertex : Q.vertices[lastSeg + 1] = Q.target := by
        have hidx : lastSeg + 1 = Q.vertices.length - 1 := by dsimp [lastSeg]; omega
        exact hgetEq Q.vertices (lastSeg + 1) (Q.vertices.length - 1)
          (by omega) hlastIdx hidx |>.trans htargetLast
      rw [hEq, ← hlastVertex]
      exact right_mem_segment ℝ _ _
    have hiEq : i₀ = lastSeg := by
      by_contra hne
      have hilast : i₀ < lastSeg := by dsimp [lastSeg]; omega
      have hraw := Q.segment_intersections hi₀ hlastSeg hilast
      have hinter : q ∈ segment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1] ∩
          segment ℝ Q.vertices[lastSeg] Q.vertices[lastSeg + 1] := by
        refine ⟨?_, hqLast⟩
        rw [segment_eq_image_lineMap]
        exact ⟨a, haIcc, rfl⟩
      by_cases hadj : lastSeg = i₀ + 1
      · rw [hraw, if_pos hadj] at hinter
        have hqCommon : q = Q.vertices[lastSeg] := by simpa using hinter
        have hdistinct : Q.vertices[lastSeg] ≠ Q.vertices[lastSeg + 1] := by
          intro hv
          have hindices := (Q.simple_vertices.getElem_inj_iff
            (i := lastSeg) (j := lastSeg + 1) (hi := by omega) (hj := hlastSeg)).1 hv
          omega
        apply hdistinct
        rw [← hqCommon, hEq, ← htargetLast]
        apply hgetEq Q.vertices (Q.vertices.length - 1) (lastSeg + 1)
          hlastIdx (by omega)
        dsimp [lastSeg]
        omega
      · rw [hraw, if_neg hadj] at hinter
        exact False.elim hinter
    have hF1 : F 1 = Q.target := by
      have hright : Q.vertices[i₀ + 1] = Q.target := by
        have hidx : lastSeg + 1 = Q.vertices.length - 1 := by dsimp [lastSeg]; omega
        have hiIndex : i₀ + 1 = lastSeg + 1 := congrArg Nat.succ hiEq
        exact (hgetEq Q.vertices (i₀ + 1) (lastSeg + 1)
          (by omega) (by omega) hiIndex).trans
            ((hgetEq Q.vertices (lastSeg + 1) (Q.vertices.length - 1)
              (by omega) hlastIdx hidx).trans htargetLast)
      simp [F, hright]
    have hsegNe : Q.vertices[i₀] ≠ Q.vertices[i₀ + 1] := by
      intro hv
      have hindices := (Q.simple_vertices.getElem_inj_iff
        (i := i₀) (j := i₀ + 1) (hi := by omega) (hj := hi₀)).1 hv
      omega
    have ha1 : a = 1 := (AffineMap.lineMap_injective ℝ hsegNe)
      (by simpa [q, hEq, hF1] using rfl : F a = F 1)
    linarith
  have hqRel : q ∈ Q.relativeInterior := by
    rw [Q.relativeInterior_eq]
    exact ⟨hqCarrier, by simp [hqSource, hqTarget]⟩
  obtain ⟨D⟩ := PolygonalArcPointCutDataExists Q q hqRel
  have hsegmentBallJ : ∀ m (hm : m + 1 < Q.vertices.length),
      (segment ℝ Q.vertices[m] Q.vertices[m + 1] ∩ Metric.ball p radius).Nonempty →
        m ∈ J := by
    intro m hm hne
    rcases hne with ⟨z, hzseg, hzball⟩
    rw [segment_eq_image_lineMap] at hzseg
    rcases hzseg with ⟨s, hs, rfl⟩
    exact ⟨hm, s, hs, hzball⟩
  have hNoEarlier : ∀ m (hm : m + 1 < Q.vertices.length), m < i₀ →
      Disjoint (segment ℝ Q.vertices[m] Q.vertices[m + 1])
        (Metric.ball p radius) := by
    intro m hm hmi
    rw [Set.disjoint_left]
    intro z hzseg hzball
    have hmJ := hsegmentBallJ m hm ⟨z, hzseg, hzball⟩
    exact (Nat.not_lt_of_ge (hi₀min m hmJ)) hmi
  have hopenUnique : ∀ z d e
      (hd : d + 1 < Q.vertices.length) (he : e + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[d] Q.vertices[d + 1] →
      z ∈ segment ℝ Q.vertices[e] Q.vertices[e + 1] → d = e := by
    intro z d e hd he hzd hze
    have hdne : Q.vertices[d] ≠ Q.vertices[d + 1] := by
      intro hv
      have hindices := (Q.simple_vertices.getElem_inj_iff
        (i := d) (j := d + 1) (hi := by omega) (hj := hd)).1 hv
      omega
    have hzleft : z ≠ Q.vertices[d] := by
      intro hz
      subst z
      exact hdne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hzd)
    have hzright : z ≠ Q.vertices[d + 1] := by
      intro hz
      subst z
      exact hdne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hzd)
    rcases lt_trichotomy d e with hde | rfl | hed
    · have hraw := Q.segment_intersections hd he hde
      have hzint : z ∈ segment ℝ Q.vertices[d] Q.vertices[d + 1] ∩
          segment ℝ Q.vertices[e] Q.vertices[e + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hzd, hze⟩
      by_cases hadj : e = d + 1
      · rw [hraw, if_pos hadj] at hzint
        exact False.elim (hzright (by simpa [hadj] using hzint))
      · rw [hraw, if_neg hadj] at hzint
        exact False.elim hzint
    · rfl
    · have hraw := Q.segment_intersections he hd hed
      have hzint : z ∈ segment ℝ Q.vertices[e] Q.vertices[e + 1] ∩
          segment ℝ Q.vertices[d] Q.vertices[d + 1] :=
        ⟨hze, openSegment_subset_segment ℝ _ _ hzd⟩
      by_cases hadj : d = e + 1
      · rw [hraw, if_pos hadj] at hzint
        exact False.elim (hzleft (by simpa [hadj] using hzint))
      · rw [hraw, if_neg hadj] at hzint
        exact False.elim hzint
  have hcutLeftValid : D.cutIndex < Q.vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) D.cutIndex_valid
  have hcutRightValid : D.cutIndex + 1 < Q.vertices.length := D.cutIndex_valid
  let cutLeft := Q.vertices[D.cutIndex]'hcutLeftValid
  let cutRight := Q.vertices[D.cutIndex + 1]'hcutRightValid
  have hqNotCutLeft : q ≠ cutLeft := by
    intro hEq
    have hmem : q ∈ Q.vertices.take (D.cutIndex + 1) := by
      rw [List.mem_take_iff_getElem]
      refine ⟨D.cutIndex, lt_min (Nat.lt_succ_self _) hcutLeftValid, ?_⟩
      simpa only [cutLeft] using hEq.symm
    have hnod := D.prefixArc.simple_vertices
    rw [D.prefix_vertices_exact, List.nodup_append] at hnod
    exact (hnod.2.2 q hmem q (by simp)) rfl
  have hqSelectedSegment : q ∈ segment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1] := by
    rw [segment_eq_image_lineMap]
    exact ⟨a, haIcc, rfl⟩
  have hcutCases :
      (D.cutIndex = i₀ ∧ q ∈ openSegment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1]) ∨
        (D.cutIndex + 1 = i₀ ∧ q = Q.vertices[i₀]) := by
    rcases D.suffix_drop_index_spec with hinterior | hlisted
    · have hqOpen : q ∈ openSegment ℝ cutLeft cutRight :=
        mem_openSegment_of_ne_left_right (Ne.symm hqNotCutLeft)
          (Ne.symm (by simpa only [cutRight] using hinterior.2))
          (by simpa only [cutLeft, cutRight] using D.cut_mem_segment)
      have hdi : D.cutIndex = i₀ :=
        hopenUnique q D.cutIndex i₀ D.cutIndex_valid hi₀ hqOpen hqSelectedSegment
      exact Or.inl ⟨hdi, by simpa only [cutLeft, cutRight, hdi] using hqOpen⟩
    · have hqRight : q = cutRight := by simpa only [cutRight] using hlisted.2
      by_cases ha0 : a = 0
      · have hqi : q = Q.vertices[i₀] := by simp [q, F, ha0]
        have hidx : D.cutIndex + 1 = i₀ := by
          apply (Q.simple_vertices.getElem_inj_iff
            (i := D.cutIndex + 1) (j := i₀)
            (hi := D.cutIndex_valid) (hj := by omega)).1
          exact hqRight.symm.trans hqi
        exact Or.inr ⟨hidx, hqi⟩
      · have haPos : 0 < a := lt_of_le_of_ne haIcc.1 (Ne.symm ha0)
        have hqOpenSelected : q ∈ openSegment ℝ Q.vertices[i₀]
            Q.vertices[i₀ + 1] := by
          rw [openSegment_eq_image_lineMap]
          exact ⟨a, ⟨haPos, haStrictUpper⟩, rfl⟩
        have hrightIndex : D.cutIndex + 1 = i₀ := by
          by_contra hne
          have hneSucc : D.cutIndex + 1 ≠ i₀ + 1 := by
            intro heq
            have hqEndpoint : Q.vertices[i₀ + 1] ∈
                openSegment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1] := by
              have hvertexEq : Q.vertices[D.cutIndex + 1] = Q.vertices[i₀ + 1] :=
                hgetEq Q.vertices (D.cutIndex + 1) (i₀ + 1)
                  (by omega) (by omega) heq
              have hcutOpen : cutRight ∈
                  openSegment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1] :=
                hqRight ▸ hqOpenSelected
              simpa only [cutRight, hvertexEq] using hcutOpen
            have hsegNe : Q.vertices[i₀] ≠ Q.vertices[i₀ + 1] := by
              intro hv
              have hindices := (Q.simple_vertices.getElem_inj_iff
                (i := i₀) (j := i₀ + 1) (hi := by omega) (hj := hi₀)).1 hv
              omega
            exact hsegNe ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hqEndpoint)
          have havoid := Q.vertices_avoid_nonincident_interiors
            (i := i₀) (k := D.cutIndex + 1) hi₀ D.cutIndex_valid hne hneSucc
          have hcutOpen : cutRight ∈
              openSegment ℝ Q.vertices[i₀] Q.vertices[i₀ + 1] :=
            hqRight ▸ hqOpenSelected
          exact havoid (by simpa only [cutRight] using hcutOpen)
        have hqi : q = Q.vertices[i₀] := by
          exact hqRight.trans (hgetEq Q.vertices (D.cutIndex + 1) i₀
            (by omega) (by omega) hrightIndex)
        exact Or.inr ⟨hrightIndex, hqi⟩
  have hprefixAvoid : Disjoint D.prefixArc.carrier (Metric.ball p radius) := by
    rw [Set.disjoint_left]
    intro z hzP hzBall
    rw [D.prefix_carrier_region] at hzP
    rcases hzP with ⟨m, hm, hmd, hzm⟩ | hzPartial
    · have hdi : D.cutIndex ≤ i₀ := by
        rcases hcutCases with h | h <;> omega
      exact Set.disjoint_left.mp (hNoEarlier m hm (lt_of_lt_of_le hmd hdi)) hzm hzBall
    · rcases hcutCases with hInterior | hListed
      · have hdi := hInterior.1
        have hleftEq : Q.vertices[D.cutIndex] = Q.vertices[i₀] :=
          hgetEq Q.vertices D.cutIndex i₀ hcutLeftValid (by omega) hdi
        have hzPartial' : z ∈ segment ℝ Q.vertices[i₀] q := by
          simpa only [hleftEq] using hzPartial
        have hleftParam : segment ℝ Q.vertices[i₀] q =
            F '' Set.Icc (0 : ℝ) a := by
          calc
            segment ℝ Q.vertices[i₀] q = segment ℝ (F 0) (F a) := by
              simp [F, q]
            _ = F '' segment ℝ (0 : ℝ) a :=
              (image_segment ℝ F 0 a).symm
            _ = F '' Set.Icc 0 a := by rw [segment_eq_Icc haIcc.1]
        rw [hleftParam] at hzPartial'
        rcases hzPartial' with ⟨s, hs, rfl⟩
        have hsU : s ∈ U := ⟨⟨hs.1, hs.2.trans haIcc.2⟩, hzBall⟩
        have has := haLower s hsU
        have hsa : s = a := le_antisymm hs.2 has
        subst s
        exact hFaNotBall hzBall
      · have hdi : D.cutIndex < i₀ := by omega
        have hqRight : q = Q.vertices[D.cutIndex + 1] := by
          exact hListed.2.trans (hgetEq Q.vertices i₀ (D.cutIndex + 1)
            (by omega) D.cutIndex_valid hListed.1.symm)
        have hzFull : z ∈ segment ℝ Q.vertices[D.cutIndex]
            Q.vertices[D.cutIndex + 1] := by
          simpa only [hqRight] using hzPartial
        exact Set.disjoint_left.mp
          (hNoEarlier D.cutIndex D.cutIndex_valid hdi) hzFull hzBall
  have hballInSuffix : Q.carrier ∩ Metric.ball p radius ⊆
      D.suffixArc.relativeInterior := by
    intro z hz
    have hzNotPrefix : z ∉ D.prefixArc.carrier := by
      intro hzP
      exact Set.disjoint_left.mp hprefixAvoid hzP hz.2
    have hzSuffix : z ∈ D.suffixArc.carrier := by
      have hzUnion : z ∈ D.prefixArc.carrier ∪ D.suffixArc.carrier := by
        rw [← D.carrier_decomposition]
        exact hz.1
      exact hzUnion.resolve_left hzNotPrefix
    rw [D.suffixArc.relativeInterior_eq]
    refine ⟨hzSuffix, ?_⟩
    have hzq : z ≠ q := by
      intro hEq
      subst z
      exact hFaNotBall hz.2
    have hzt : z ≠ Q.target := by
      intro hEq
      subst z
      exact htarget hz.2
    simpa only [D.suffix_source, D.suffix_target, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] using And.intro hzq hzt
  exact ⟨{
    gate := q
    cut := D
    gate_mem_relativeInterior := hqRel
    gate_mem_sphere := hFaSphere
    gate_mem_closure_ball_part := hFaClosure
    prefix_avoids_ball := hprefixAvoid
    ball_part_in_suffix := hballInSuffix }⟩
