import Util.IncidenceGeometry.JordanLocalSideData
import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.PolygonallyPathConnected
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.FinitePolygonalPerturbation
import Util.IncidenceGeometry.ClosedPolygonalPathEvenIntersections
import Util.IncidenceGeometry.PolygonalPathInGeneralPosition
import Util.IncidenceGeometry.PolygonalPathIntersectionMultiplicity
import Util.IncidenceGeometry.SimpleClosedPolygonalCurveComplementOpen
import Util.IncidenceGeometry.SimpleClosedCurveAsFinitePolygonalSet
import Util.IncidenceGeometry.ConnectedSubsetContainedInUniqueComplementComponent

open Classical
noncomputable section

lemma JordanLocalSideDistinctComponents
    (J : SimpleClosedPolygonalCurve) (S : JordanLocalSideData J) :
    ∃ leftComponent rightComponent : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent J.carrier leftComponent ∧
        ComplementComponent J.carrier rightComponent ∧
          leftComponent ≠ rightComponent ∧
            S.leftRegion ⊆ leftComponent ∧
              S.rightRegion ⊆ rightComponent := by
  classical
  obtain ⟨leftComponent, hleftComponent, hleftSubset⟩ :=
    ExistsUnique.exists
      (ConnectedSubsetContainedInUniqueComplementComponent
        J.carrier S.leftRegion S.left_nonempty S.left_subset_complement
        S.left_connected)
  obtain ⟨rightComponent, hrightComponent, hrightSubset⟩ :=
    ExistsUnique.exists
      (ConnectedSubsetContainedInUniqueComplementComponent
        J.carrier S.rightRegion S.right_nonempty S.right_subset_complement
        S.right_connected)
  refine ⟨leftComponent, rightComponent, hleftComponent, hrightComponent, ?_,
    hleftSubset, hrightSubset⟩
  intro hcomponents
  rcases S.transverse_segment with
    ⟨γ, K, hKJ, s, hs, a, b, x, ha, hb, hab, hxγ, hxab, hxs,
      hsegment, hpoints, hoverlap, htransverse, hcount⟩
  have haLeft : a ∈ leftComponent := hleftSubset ha
  have hbLeft : b ∈ leftComponent := by
    rw [hcomponents]
    exact hrightSubset hb
  have hcomplementOpen : IsOpen J.carrierᶜ :=
    SimpleClosedPolygonalCurveComplementOpen J
  have hleftPolygonal : PolygonallyPathConnected leftComponent :=
    OpenConnectedComponentPolygonallyConnected J.carrierᶜ leftComponent
      hcomplementOpen (by simpa using hleftComponent)
  obtain ⟨β, hβsource, hβtarget, hβcarrier⟩ :=
    hleftPolygonal hbLeft haLeft
  have hbComplement : b ∈ J.carrierᶜ :=
    hleftComponent.2.1 hbLeft
  have haComplement : a ∈ J.carrierᶜ :=
    hleftComponent.2.1 haLeft
  have hβComplement : β.carrier ⊆ J.carrierᶜ :=
    fun _ hp => hleftComponent.2.1 (hβcarrier hp)
  obtain ⟨β', hβ'source, hβ'target, hβ'carrier, _hβ'near, hβ'gp,
      _hβ'avoid⟩ :=
    FinitePolygonalPerturbation K J.carrierᶜ β ∅ 1
      hcomplementOpen hβComplement
      ⟨by simpa [hβsource] using hbComplement,
        by simpa [hKJ, hβsource] using hbComplement⟩
      ⟨by simpa [hβtarget] using haComplement,
        by simpa [hKJ, hβtarget] using haComplement⟩
      (by norm_num) isCompact_empty (by simp)
  let Γ : PolygonalPath :=
    { vertices := β'.vertices ++ [b]
      vertices_nonempty := by simp [β'.vertices_nonempty]
      source := b
      target := b
      source_eq_head := by
        rw [List.head?_append_of_ne_nil _ β'.vertices_nonempty]
        simpa [hβ'source, hβsource] using β'.source_eq_head
      target_eq_last := by simp
      carrier :=
        ({b, b} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          {p | ∃ i : ℕ, ∃ hi : i + 1 < (β'.vertices ++ [b]).length,
            p ∈ segment ℝ (β'.vertices ++ [b])[i]
              (β'.vertices ++ [b])[i + 1]}
      carrier_eq := rfl }
  have hβ'length : 0 < β'.vertices.length :=
    List.length_pos_of_ne_nil β'.vertices_nonempty
  have hβ'last : β'.vertices[β'.vertices.length - 1] = a := by
    have hlast := β'.target_eq_last
    rw [List.getLast?_eq_getLast_of_ne_nil β'.vertices_nonempty] at hlast
    have hlast' : β'.vertices[β'.vertices.length - 1] = β'.target := by
      simpa [List.getLast_eq_getElem] using Option.some.inj hlast
    exact hlast'.trans (hβ'target.trans hβtarget)
  have hΓcarrier : Γ.carrier ⊆ β'.carrier ∪ segment ℝ a b := by
    intro p hp
    change p ∈
      (({b, b} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p | ∃ i : ℕ, ∃ hi : i + 1 < (β'.vertices ++ [b]).length,
          p ∈ segment ℝ (β'.vertices ++ [b])[i]
            (β'.vertices ++ [b])[i + 1]}) at hp
    rcases hp with hpEnd | ⟨i, hi, hpseg⟩
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnd
      rcases hpEnd with hpEnd | hpEnd
      · simpa [hpEnd] using right_mem_segment ℝ a b
      · simpa [hpEnd] using right_mem_segment ℝ a b
    · have hiBound : i + 1 < β'.vertices.length + 1 := by simpa using hi
      have hiLe : i + 1 ≤ β'.vertices.length := Nat.lt_succ_iff.mp hiBound
      rcases lt_or_eq_of_le hiLe with hiOld | hiLast
      · left
        rw [β'.carrier_eq]
        right
        refine ⟨i, hiOld, ?_⟩
        simpa [List.getElem_append_left (bs := [b]) (Nat.lt_of_succ_lt hiOld),
          List.getElem_append_left (bs := [b]) hiOld] using hpseg
      · right
        have hiEq : i = β'.vertices.length - 1 := by omega
        subst i
        have hidx : β'.vertices.length - 1 + 1 = β'.vertices.length := by
          omega
        have hnext :
            (β'.vertices ++ [b])[β'.vertices.length - 1 + 1] = b := by
          simpa [hidx]
        have hlastAppend :
            (β'.vertices ++ [b])[β'.vertices.length - 1] = a := by
          rw [List.getElem_append_left (bs := [b])
            (Nat.sub_one_lt_of_lt hβ'length)]
          exact hβ'last
        simpa [hlastAppend, hnext] using hpseg
  have hΓgp : PolygonalPathInGeneralPosition Γ K := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      change v ∈ β'.vertices ++ [b] at hv
      rw [List.mem_append] at hv
      rcases hv with hv | hv
      · exact hβ'gp.1 v hv
      · simp only [List.mem_singleton] at hv
        rw [hv, hKJ]
        exact hbComplement
    · intro p hpK hpΓ
      rcases hΓcarrier hpΓ with hpβ | hpseg
      · have hpComplement : p ∈ J.carrierᶜ := hβ'carrier hpβ
        apply hpComplement
        rw [← hKJ]
        rw [K.carrier_eq]
        exact Or.inl (by simpa using hpK)
      · exact hpoints p hpK hpseg
    · intro i hi t ht
      change i + 1 < (β'.vertices ++ [b]).length at hi
      change ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
        p ≠ q ∧ segment ℝ p q ⊆
          segment ℝ (β'.vertices ++ [b])[i] (β'.vertices ++ [b])[i + 1] ∩
            segment ℝ t.1 t.2
      have hiBound : i + 1 < β'.vertices.length + 1 := by simpa using hi
      have hiLe : i + 1 ≤ β'.vertices.length := Nat.lt_succ_iff.mp hiBound
      rcases lt_or_eq_of_le hiLe with hiOld | hiLast
      · have hold := hβ'gp.2.2.1 i hiOld t ht
        simpa [List.getElem_append_left (bs := [b]) (Nat.lt_of_succ_lt hiOld),
          List.getElem_append_left (bs := [b]) hiOld] using hold
      · have hiEq : i = β'.vertices.length - 1 := by omega
        subst i
        have hidx : β'.vertices.length - 1 + 1 = β'.vertices.length := by
          omega
        have hnext :
            (β'.vertices ++ [b])[β'.vertices.length - 1 + 1] = b := by
          simpa [hidx]
        have hlastAppend :
            (β'.vertices ++ [b])[β'.vertices.length - 1] = a := by
          rw [List.getElem_append_left (bs := [b])
            (Nat.sub_one_lt_of_lt hβ'length)]
          exact hβ'last
        simpa [hlastAppend, hnext] using hoverlap t ht
    · intro i hi t ht p hpPath hpSegment
      change i + 1 < (β'.vertices ++ [b]).length at hi
      change p ∈ openSegment ℝ (β'.vertices ++ [b])[i]
        (β'.vertices ++ [b])[i + 1] at hpPath
      change ¬ ∃ c : ℝ, t.2 - t.1 =
        c • ((β'.vertices ++ [b])[i + 1] - (β'.vertices ++ [b])[i])
      have hiBound : i + 1 < β'.vertices.length + 1 := by simpa using hi
      have hiLe : i + 1 ≤ β'.vertices.length := Nat.lt_succ_iff.mp hiBound
      rcases lt_or_eq_of_le hiLe with hiOld | hiLast
      · have hold := hβ'gp.2.2.2.1 i hiOld t ht p
        simpa [List.getElem_append_left (bs := [b]) (Nat.lt_of_succ_lt hiOld),
          List.getElem_append_left (bs := [b]) hiOld] using
          (hold (by
            simpa [List.getElem_append_left (bs := [b]) (Nat.lt_of_succ_lt hiOld),
              List.getElem_append_left (bs := [b]) hiOld] using hpPath) hpSegment)
      · have hiEq : i = β'.vertices.length - 1 := by omega
        subst i
        have hidx : β'.vertices.length - 1 + 1 = β'.vertices.length := by
          omega
        have hnext :
            (β'.vertices ++ [b])[β'.vertices.length - 1 + 1] = b := by
          simpa [hidx]
        have hlastAppend :
            (β'.vertices ++ [b])[β'.vertices.length - 1] = a := by
          rw [List.getElem_append_left (bs := [b])
            (Nat.sub_one_lt_of_lt hβ'length)]
          exact hβ'last
        simpa [hlastAppend, hnext] using
          (htransverse t ht p (by simpa [hlastAppend, hnext] using hpPath)
            hpSegment)
    · apply Set.finite_singleton x |>.subset
      intro p hp
      rcases hΓcarrier hp.1 with hpβ | hpseg
      · exact False.elim (hβ'carrier hpβ (by simpa [hKJ] using hp.2))
      · have hpJ : p ∈ J.carrier := by simpa [hKJ] using hp.2
        have hpSingleton : p ∈ ({x} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [← hsegment]
          exact ⟨hpseg, hpJ⟩
        simpa using hpSingleton
  have hΓmultiplicity : PolygonalPathIntersectionMultiplicity Γ K = 1 := by
    have hOldCount :
        ∀ (i : ℕ) (hi : i + 1 < β'.vertices.length)
          (t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
          t ∈ K.segments →
            Set.ncard (openSegment ℝ β'.vertices[i] β'.vertices[i + 1] ∩
              openSegment ℝ t.1 t.2) = 0 := by
      intro i hi t ht
      have hempty :
          openSegment ℝ β'.vertices[i] β'.vertices[i + 1] ∩
              openSegment ℝ t.1 t.2 = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro p hp
        have hpβ : p ∈ β'.carrier := by
          rw [β'.carrier_eq]
          right
          exact ⟨i, hi,
            (openSegment_subset_segment ℝ β'.vertices[i] β'.vertices[i + 1]) hp.1⟩
        have hpK : p ∈ K.carrier := by
          rw [K.carrier_eq]
          right
          rw [Set.mem_iUnion]
          exact ⟨⟨t, ht⟩, (openSegment_subset_segment ℝ t.1 t.2) hp.2⟩
        exact hβ'carrier hpβ (by simpa [hKJ] using hpK)
      rw [hempty]
      simp
    unfold PolygonalPathIntersectionMultiplicity
    change
      (Finset.range (β'.vertices ++ [b]).length).sum (fun i =>
        if hi : i + 1 < (β'.vertices ++ [b]).length then
          if (β'.vertices ++ [b])[i] = (β'.vertices ++ [b])[i + 1] then 0
          else K.segments.sum fun t =>
            Set.ncard (openSegment ℝ (β'.vertices ++ [b])[i]
              (β'.vertices ++ [b])[i + 1] ∩ openSegment ℝ t.1 t.2)
        else 0) = 1
    simp only [List.length_append, List.length_singleton]
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceDIte, add_zero]
    rw [Finset.sum_eq_single_of_mem (β'.vertices.length - 1)
      (Finset.mem_range.mpr (Nat.sub_one_lt_of_lt hβ'length))]
    · have hlastSucc : β'.vertices.length - 1 + 1 = β'.vertices.length := by
        omega
      have hlastLt : β'.vertices.length - 1 < β'.vertices.length := by
        omega
      have hlastAppendLt :
          β'.vertices.length - 1 < (β'.vertices ++ [b]).length := by
        simp
      have hnextAppendLt :
          β'.vertices.length - 1 + 1 < (β'.vertices ++ [b]).length := by
        simpa [hlastSucc]
      have hlastAppend :
          (β'.vertices ++ [b])[β'.vertices.length - 1]'hlastAppendLt = a := by
        rw [List.getElem_append_left (bs := [b]) hlastLt]
        exact hβ'last
      have hnextAppend :
          (β'.vertices ++ [b])[β'.vertices.length - 1 + 1]'hnextAppendLt = b := by
        simpa [hlastSucc]
      rw [dif_pos (by omega)]
      rw [hlastAppend, hnextAppend]
      simp only [hab, ↓reduceIte]
      calc
        K.segments.sum (fun t =>
            Set.ncard (openSegment ℝ a b ∩ openSegment ℝ t.1 t.2)) =
            K.segments.sum (fun t => if t = s then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro t ht
              exact hcount t ht
        _ = 1 := by simp [hs]
    · intro i hiRange hiNe
      have hiLt : i < β'.vertices.length := Finset.mem_range.mp hiRange
      have hiOld : i + 1 < β'.vertices.length := by
        omega
      have hiAppend : i + 1 < β'.vertices.length + 1 := by omega
      rw [dif_pos hiAppend]
      have hiAppendIndex : i < (β'.vertices ++ [b]).length := by
        simp
        omega
      have hiAppendSucc : i + 1 < (β'.vertices ++ [b]).length := by
        simp
        omega
      have hgetI :
          (β'.vertices ++ [b])[i]'hiAppendIndex = β'.vertices[i] := by
        exact List.getElem_append_left (bs := [b]) hiLt
      have hgetSucc :
          (β'.vertices ++ [b])[i + 1]'hiAppendSucc = β'.vertices[i + 1] := by
        exact List.getElem_append_left (bs := [b]) hiOld
      rw [hgetI, hgetSucc]
      by_cases heq : β'.vertices[i] = β'.vertices[i + 1]
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        exact Finset.sum_eq_zero (fun t ht => hOldCount i hiOld t ht)
  have hEven := ClosedPolygonalPathEvenIntersections J Γ K hKJ rfl hΓgp
  rw [hΓmultiplicity] at hEven
  exact (Nat.not_even_one hEven)
