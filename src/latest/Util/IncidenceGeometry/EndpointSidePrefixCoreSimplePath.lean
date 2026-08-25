import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.PolygonalArcFinitePolygonalSet
import Util.IncidenceGeometry.StraightSegmentPolygonalArc
import Util.IncidenceGeometry.FinitePolygonalSetUnionOfFiniteIntersection
import Util.IncidenceGeometry.FinitePolygonalSetSegmentIntersectionOfEndpointOffLines
import Util.IncidenceGeometry.FinitePolygonalPerturbation
import Util.IncidenceGeometry.PolygonalPathToPolygonalArc


open Classical
noncomputable section

private lemma appended_middle_left {X : Type*} (a b : X) (xs : List X)
    (i : ℕ) (hiPos : 0 < i) (hiMiddle : i < xs.length) :
    (([a] ++ xs) ++ [b])[i]'(by simp; omega) =
      xs[i - 1]'(by omega) := by
  have hiPrefix : i < ([a] ++ xs).length := by
    simp
    omega
  calc
    (([a] ++ xs) ++ [b])[i]'(by simp; omega) =
        ([a] ++ xs)[i]'hiPrefix :=
      List.getElem_append_left (as := [a] ++ xs) (bs := [b])
        (i := i) hiPrefix
    _ = xs[i - 1]'(by omega) :=
      List.getElem_append_right (as := [a]) (bs := xs)
        (i := i) (by simp; omega)

private lemma appended_middle_right {X : Type*} (a b : X) (xs : List X)
    (i : ℕ) (hiMiddle : i < xs.length) :
    (([a] ++ xs) ++ [b])[i + 1]'(by simp; omega) = xs[i]'hiMiddle := by
  have hiPrefix : i + 1 < ([a] ++ xs).length := by
    simp
    omega
  calc
    (([a] ++ xs) ++ [b])[i + 1]'(by simp; omega) =
        ([a] ++ xs)[i + 1]'hiPrefix :=
      List.getElem_append_left (as := [a] ++ xs) (bs := [b])
        (i := i + 1) hiPrefix
    _ = xs[(i + 1) - 1]'(by omega) :=
      List.getElem_append_right (as := [a]) (bs := xs)
        (i := i + 1) (by simp)
    _ = xs[i]'hiMiddle := by congr

private lemma appended_middle_last {X : Type*} (a b : X) (xs : List X)
    (hxs : xs ≠ []) :
    (([a] ++ xs) ++ [b])[xs.length]'(by simp) =
      xs[xs.length - 1]'(by
        exact Nat.sub_lt (List.length_pos_of_ne_nil hxs) (by omega)) := by
  have hlastAppend : xs.length < ([a] ++ xs).length := by simp
  calc
    (([a] ++ xs) ++ [b])[xs.length]'(by simp) =
        ([a] ++ xs)[xs.length]'hlastAppend :=
      List.getElem_append_left (as := [a] ++ xs) (bs := [b])
        (i := xs.length) hlastAppend
    _ = xs[xs.length - 1]'(by
          exact Nat.sub_lt (List.length_pos_of_ne_nil hxs) (by omega)) :=
      List.getElem_append_right (as := [a]) (bs := xs)
        (i := xs.length) (by
          simp only [List.length_singleton]
          exact Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (List.length_pos_of_ne_nil hxs)))

private lemma appended_middle_successor {X : Type*} (a b : X) (xs : List X) :
    (([a] ++ xs) ++ [b])[xs.length + 1]'(by simp) = b := by
  simpa using
    (List.getElem_append_right
      (as := [a] ++ xs) (bs := [b])
      (i := ([a] ++ xs).length))

private lemma polygonalArc_source_mem_carrier (A : PolygonalArc) :
    A.source ∈ A.carrier := by
  rw [A.carrier_eq]
  have hseg : 0 + 1 < A.vertices.length := A.length_ge_two
  refine ⟨0, hseg, ?_⟩
  have hzero : 0 < A.vertices.length := by omega
  have hsource : A.vertices[0]'hzero = A.source := by
    have hhead := A.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hzero] at hhead
    exact Option.some.inj hhead
  rw [← hsource]
  exact left_mem_segment ℝ
    (A.vertices[0]'hzero) (A.vertices[1]'hseg)

private lemma first_vertices_ne_of_nodup {X : Type*} (xs : List X)
    (hnodup : xs.Nodup) (hlen : 1 < xs.length) :
    xs[0]'(by omega) ≠ xs[1]'hlen := by
  intro heq
  have hidx : (0 : ℕ) = 1 :=
    (hnodup.getElem_inj_iff
      (i := 0) (j := 1) (hi := by omega) (hj := hlen)).1 heq
  omega

private lemma openSegment_subset_of_segment_subset_union_left
    (a b : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hne : a ≠ b) (hsegment : segment ℝ a b ⊆ S ∪ ({a} : Set _)) :
    openSegment ℝ a b ⊆ S := by
  intro p hp
  rcases hsegment (openSegment_subset_segment ℝ a b hp) with hpS | hpa
  · exact hpS
  · have hpEq : p = a := by simpa using hpa
    subst p
    exact False.elim
      (hne ((left_mem_openSegment_iff (𝕜 := ℝ) (x := a) (y := b)).1 hp))

private lemma polygonalArc_first_open_subset
    (P : PolygonalArc) (a : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hlen : 1 < P.vertices.length)
    (hzero : P.vertices[0] = a) (hne : P.vertices[0] ≠ P.vertices[1])
    (hsegment :
      segment ℝ P.vertices[0] P.vertices[1] ⊆ S ∪ ({a} : Set _)) :
    openSegment ℝ P.vertices[0] P.vertices[1] ⊆ S := by
  rw [← hzero] at hsegment
  exact openSegment_subset_of_segment_subset_union_left
    P.vertices[0] P.vertices[1] S hne hsegment

private lemma build_prefix_whole_path
    (Aarc predecessor : PolygonalArc) (middle : PolygonalPath)
    (a0 b0 : EuclideanSpace ℝ (Fin 2))
    (SelectedSide StartSector terminalCarrier :
      Set (EuclideanSpace ℝ (Fin 2)))
    (hmiddleSource : middle.source = a0)
    (hmiddleTarget : middle.target = b0)
    (hInitial :
      segment ℝ Aarc.source a0 ⊆
        StartSector ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))))
    (hStartSubset : StartSector ⊆ SelectedSide)
    (hmiddleCarrier : middle.carrier ⊆ SelectedSide)
    (hFinalSegment :
      segment ℝ b0 predecessor.source ⊆ SelectedSide)
    (hInitialFinite :
      Set.Finite (segment ℝ Aarc.source a0 ∩ terminalCarrier))
    (hmiddleFinite :
      Set.Finite (middle.carrier ∩ terminalCarrier))
    (hFinalFinite :
      Set.Finite
        (segment ℝ b0 predecessor.source ∩ terminalCarrier)) :
    ∃ whole : PolygonalPath,
      whole.source = Aarc.source ∧
        whole.target = predecessor.source ∧
          ∃ hwholeLength : 2 ≤ whole.vertices.length,
            whole.vertices[0]'(by omega) = Aarc.source ∧
              whole.vertices[1]'(by omega) = a0 ∧
                whole.carrier ⊆
                SelectedSide ∪
                  ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                Set.Finite (whole.carrier ∩ terminalCarrier) ∧
                  ∀ j : ℕ,
                    (hj : j + 1 < whole.vertices.length) → j ≠ 0 →
                      segment ℝ whole.vertices[j] whole.vertices[j + 1] ⊆
                        SelectedSide := by
  let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
    ([Aarc.source] ++ middle.vertices) ++ [predecessor.source]
  let edgeSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
      p ∈ segment ℝ vertices[i] vertices[i + 1]}
  let whole : PolygonalPath :=
    { vertices := vertices
      vertices_nonempty := by simp [vertices]
      source := Aarc.source
      target := predecessor.source
      source_eq_head := by simp [vertices]
      target_eq_last := by
        simp [vertices, List.getLast?_eq_getLast_of_ne_nil]
      carrier :=
        ({Aarc.source, predecessor.source} :
          Set (EuclideanSpace ℝ (Fin 2))) ∪ edgeSet
      carrier_eq := rfl }
  have hmiddleLength : 0 < middle.vertices.length :=
    List.length_pos_of_ne_nil middle.vertices_nonempty
  have hmiddleZero : middle.vertices[0] = a0 := by
    have hhead := middle.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hmiddleLength] at hhead
    exact (Option.some.inj hhead).trans hmiddleSource
  have hmiddleLast :
      middle.vertices[middle.vertices.length - 1] = b0 := by
    have hlast := middle.target_eq_last
    rw [List.getLast?_eq_getLast_of_ne_nil middle.vertices_nonempty] at hlast
    have hgetlast :
        middle.vertices.getLast middle.vertices_nonempty = middle.target :=
      Option.some.inj hlast
    simpa [List.getLast_eq_getElem, hmiddleTarget] using hgetlast
  have hwholeVerticesLength :
      whole.vertices.length = middle.vertices.length + 2 := by
    simp [whole, vertices]
  have hwholeSource : whole.source = Aarc.source := rfl
  have hwholeTarget : whole.target = predecessor.source := rfl
  have hwholeLength : 2 ≤ whole.vertices.length := by
    rw [hwholeVerticesLength]
    omega
  have hwholeZero : whole.vertices[0] = Aarc.source := by
    simp [whole, vertices]
  have hwholeOne : whole.vertices[1] = a0 := by
    have honePrefix :
        1 < ([Aarc.source] ++ middle.vertices).length := by
      simp
      omega
    calc
      whole.vertices[1] =
          ([Aarc.source] ++ middle.vertices)[1] :=
        List.getElem_append_left
          (as := [Aarc.source] ++ middle.vertices)
          (bs := [predecessor.source]) (i := 1) honePrefix
      _ = middle.vertices[0] :=
        List.getElem_append_right (as := [Aarc.source])
          (bs := middle.vertices) (i := 1) (by simp)
      _ = a0 := hmiddleZero
  have hwholeMiddleLeft :
      ∀ (i : ℕ) (hiPos : 0 < i) (hiMiddle : i < middle.vertices.length),
        whole.vertices[i] = middle.vertices[i - 1] := by
    intro i hiPos hiMiddle
    change getElem (([Aarc.source] ++ middle.vertices) ++ [predecessor.source])
        i (by simp; omega) = getElem middle.vertices (i - 1) (by omega)
    exact appended_middle_left Aarc.source predecessor.source
      middle.vertices i hiPos hiMiddle
  have hwholeMiddleRight :
      ∀ (i : ℕ) (hiMiddle : i < middle.vertices.length),
        whole.vertices[i + 1] = middle.vertices[i] := by
    intro i hiMiddle
    change getElem (([Aarc.source] ++ middle.vertices) ++ [predecessor.source])
        (i + 1) (by simp; omega) = getElem middle.vertices i hiMiddle
    exact appended_middle_right Aarc.source predecessor.source
      middle.vertices i hiMiddle
  have hwholeFinalLeft :
      whole.vertices[middle.vertices.length] = b0 := by
    change getElem (([Aarc.source] ++ middle.vertices) ++ [predecessor.source])
      middle.vertices.length (by simp) = b0
    rw [appended_middle_last Aarc.source predecessor.source middle.vertices
      middle.vertices_nonempty]
    exact hmiddleLast
  have hwholeFinalRight :
      whole.vertices[middle.vertices.length + 1] = predecessor.source := by
    change getElem (([Aarc.source] ++ middle.vertices) ++ [predecessor.source])
      (middle.vertices.length + 1) (by simp) = predecessor.source
    exact appended_middle_successor Aarc.source predecessor.source middle.vertices
  have hsegmentParts :
      ∀ i : ℕ, (hi : i + 1 < whole.vertices.length) →
        segment ℝ whole.vertices[i] whole.vertices[i + 1] ⊆
          segment ℝ Aarc.source a0 ∪
            (middle.carrier ∪ segment ℝ b0 predecessor.source) := by
    intro i hi p hp
    by_cases hiZero : i = 0
    · subst i
      have hp' :
          p ∈ segment ℝ whole.vertices[0] whole.vertices[1] := by
        simpa using hp
      have hsegEq :
          segment ℝ whole.vertices[0] whole.vertices[1] =
            segment ℝ Aarc.source a0 := by
        congr
      rw [hsegEq] at hp'
      exact Or.inl hp'
    · have hiPos : 0 < i := Nat.pos_of_ne_zero hiZero
      by_cases hiMiddle : i < middle.vertices.length
      · let k := i - 1
        have hk : k + 1 < middle.vertices.length := by
          dsimp [k]
          omega
        have hik : i = k + 1 := by
          dsimp [k]
          omega
        apply Or.inr
        apply Or.inl
        rw [middle.carrier_eq]
        right
        refine ⟨k, hk, ?_⟩
        rw [hwholeMiddleLeft i hiPos hiMiddle,
          hwholeMiddleRight i hiMiddle] at hp
        have hki : k + 1 = i := hik.symm
        simpa only [hki] using hp
      · have hiLast : i = middle.vertices.length := by
          rw [hwholeVerticesLength] at hi
          omega
        subst i
        apply Or.inr
        apply Or.inr
        simpa [hwholeFinalLeft, hwholeFinalRight] using hp
  have hwholeCarrierParts :
      whole.carrier ⊆
        segment ℝ Aarc.source a0 ∪
          (middle.carrier ∪ segment ℝ b0 predecessor.source) := by
    intro p hp
    rw [whole.carrier_eq] at hp
    rcases hp with hpEndpoint | hpEdge
    · rw [hwholeSource, hwholeTarget] at hpEndpoint
      rcases hpEndpoint with rfl | rfl
      · exact Or.inl (left_mem_segment ℝ Aarc.source a0)
      · exact Or.inr (Or.inr
          (right_mem_segment ℝ b0 predecessor.source))
    · rcases hpEdge with ⟨i, hi, hp⟩
      exact hsegmentParts i hi hp
  have hwholeCarrier :
      whole.carrier ⊆
        SelectedSide ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp
    rcases hwholeCarrierParts hp with hpInitial | hpMiddle | hpFinal
    · rcases hInitial hpInitial with hpStart | hpSource
      · exact Or.inl (hStartSubset hpStart)
      · exact Or.inr hpSource
    · exact Or.inl (hmiddleCarrier hpMiddle)
    · exact Or.inl (hFinalSegment hpFinal)
  have hwholeFinite :
      Set.Finite (whole.carrier ∩ terminalCarrier) := by
    have hunionFinite :
        Set.Finite
          ((segment ℝ Aarc.source a0 ∩ terminalCarrier) ∪
            ((middle.carrier ∩ terminalCarrier) ∪
              (segment ℝ b0 predecessor.source ∩ terminalCarrier))) :=
      hInitialFinite.union (hmiddleFinite.union hFinalFinite)
    apply hunionFinite.subset
    intro p hp
    rcases hwholeCarrierParts hp.1 with hpInitial | hpMiddle | hpFinal
    · exact Or.inl ⟨hpInitial, hp.2⟩
    · exact Or.inr (Or.inl ⟨hpMiddle, hp.2⟩)
    · exact Or.inr (Or.inr ⟨hpFinal, hp.2⟩)
  have hwholeRest :
      ∀ j : ℕ, (hj : j + 1 < whole.vertices.length) → j ≠ 0 →
        segment ℝ whole.vertices[j] whole.vertices[j + 1] ⊆
          SelectedSide := by
    intro j hj hjne p hp
    have hjPos : 0 < j := Nat.pos_of_ne_zero hjne
    by_cases hjMiddle : j < middle.vertices.length
    · let k := j - 1
      have hk : k + 1 < middle.vertices.length := by
        dsimp [k]
        omega
      have hjk : j = k + 1 := by
        dsimp [k]
        omega
      apply hmiddleCarrier
      rw [middle.carrier_eq]
      right
      refine ⟨k, hk, ?_⟩
      rw [hwholeMiddleLeft j hjPos hjMiddle,
        hwholeMiddleRight j hjMiddle] at hp
      have hkj : k + 1 = j := hjk.symm
      simpa only [hkj] using hp
    · have hjLast : j = middle.vertices.length := by
        rw [hwholeVerticesLength] at hj
        omega
      subst j
      apply hFinalSegment
      simpa [hwholeFinalLeft, hwholeFinalRight] using hp
  exact ⟨whole, hwholeSource, hwholeTarget, hwholeLength, hwholeZero,
    hwholeOne, hwholeCarrier, hwholeFinite, hwholeRest⟩

private lemma finish_prefix_core_simple_path
    (Aarc predecessor P : PolygonalArc) (whole : PolygonalPath)
    (a0 : EuclideanSpace ℝ (Fin 2))
    (SelectedSide StartSector Reserved terminalCarrier :
      Set (EuclideanSpace ℝ (Fin 2)))
    (hPsourceWhole : P.source = whole.source)
    (hPtargetWhole : P.target = whole.target)
    (hPwhole : P.carrier ⊆ whole.carrier)
    (hPlocal :
      ∀ i : ℕ, (hi : i + 1 < P.vertices.length) →
        ∃ j : ℕ, ∃ hj : j + 1 < whole.vertices.length,
          segment ℝ P.vertices[i] P.vertices[i + 1] ⊆
            segment ℝ whole.vertices[j] whole.vertices[j + 1])
    (hwholeSource : whole.source = Aarc.source)
    (hwholeTarget : whole.target = predecessor.source)
    (hwholeLength : 2 ≤ whole.vertices.length)
    (hwholeZero : whole.vertices[0] = Aarc.source)
    (hwholeOne : whole.vertices[1] = a0)
    (hInitial :
      segment ℝ Aarc.source a0 ⊆
        StartSector ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))))
    (hSourceNotSide : Aarc.source ∉ SelectedSide)
    (hwholeRest :
      ∀ j : ℕ, (hj : j + 1 < whole.vertices.length) → j ≠ 0 →
        segment ℝ whole.vertices[j] whole.vertices[j + 1] ⊆
          SelectedSide)
    (hwholeCarrier :
      whole.carrier ⊆
        SelectedSide ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))))
    (hwholeFinite :
      Set.Finite (whole.carrier ∩ terminalCarrier))
    (hSideReserved :
      SelectedSide ∩ Reserved =
        (∅ : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ Q : PolygonalArc,
      Q.source = Aarc.source ∧
        Q.target = predecessor.source ∧
          Q.carrier ⊆
            SelectedSide ∪
              ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            Q.relativeInterior ⊆ SelectedSide ∧
              Q.relativeInterior ∩ Reserved =
                (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
              Set.Finite (Q.carrier ∩ terminalCarrier) ∧
                Q.vertices.Nodup ∧
                  (∀ ⦃i j : ℕ⦄,
                    (hi : i + 1 < Q.vertices.length) →
                      (hj : j + 1 < Q.vertices.length) →
                        i < j →
                          (segment ℝ Q.vertices[i] Q.vertices[i + 1] ∩
                              segment ℝ Q.vertices[j] Q.vertices[j + 1]) =
                            if j = i + 1 then {Q.vertices[j]} else ∅) ∧
                    (∀ ⦃i k : ℕ⦄,
                      (hi : i + 1 < Q.vertices.length) →
                        (hk : k < Q.vertices.length) →
                          k ≠ i → k ≠ i + 1 →
                            Q.vertices[k] ∉
                              openSegment ℝ
                                Q.vertices[i] Q.vertices[i + 1]) ∧
                      ∃ hfirst : 0 + 1 < Q.vertices.length,
                        segment ℝ Q.vertices[0] Q.vertices[1] ⊆
                            StartSector ∪
                              ({Aarc.source} :
                                Set (EuclideanSpace ℝ (Fin 2))) ∧
                          openSegment ℝ Q.vertices[0] Q.vertices[1] ⊆
                            StartSector := by
  have hPsource : P.source = Aarc.source :=
    hPsourceWhole.trans hwholeSource
  have hPtarget : P.target = predecessor.source :=
    hPtargetWhole.trans hwholeTarget
  have hfirst : 0 + 1 < P.vertices.length := P.length_ge_two
  have hPzero : P.vertices[0] = Aarc.source := by
    have hhead := P.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    exact (Option.some.inj hhead).trans hPsource
  have hfirst_ne : P.vertices[0] ≠ P.vertices[1] :=
    first_vertices_ne_of_nodup P.vertices P.simple_vertices (by omega)
  rcases hPlocal 0 hfirst with ⟨j, hj, hrefines⟩
  have hjzero : j = 0 := by
    by_contra hjne
    have hsP :
        Aarc.source ∈ segment ℝ P.vertices[0] P.vertices[1] := by
      rw [← hPzero]
      exact left_mem_segment ℝ P.vertices[0] P.vertices[1]
    have hsWhole :
        Aarc.source ∈ segment ℝ whole.vertices[j] whole.vertices[j + 1] :=
      hrefines hsP
    exact hSourceNotSide (hwholeRest j hj hjne hsWhole)
  have hfirstCarrier :
      segment ℝ P.vertices[0] P.vertices[1] ⊆
        StartSector ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp
    apply hInitial
    have hpWhole := hrefines hp
    subst j
    simpa only [hwholeZero, hwholeOne] using hpWhole
  have hfirstOpen :
      openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector :=
    polygonalArc_first_open_subset P Aarc.source StartSector
      hfirst hPzero hfirst_ne hfirstCarrier
  have hPcarrier :
      P.carrier ⊆
        SelectedSide ∪
          ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp
    exact hwholeCarrier (hPwhole hp)
  have hPinterior : P.relativeInterior ⊆ SelectedSide := by
    intro p hp
    rw [P.relativeInterior_eq] at hp
    have hpUnion := hwholeCarrier (hPwhole hp.1)
    rcases hpUnion with hpSide | hpSource
    · exact hpSide
    · have hpEq : p = Aarc.source := by simpa using hpSource
      exact False.elim
        (hp.2 (Or.inl (hpEq.trans hPsource.symm)))
  refine ⟨P, hPsource, hPtarget, hPcarrier, hPinterior, ?_, ?_,
    P.simple_vertices, P.segment_intersections,
    P.vertices_avoid_nonincident_interiors, hfirst, hfirstCarrier,
    hfirstOpen⟩
  · ext p
    constructor
    · rintro ⟨hpInterior, hpReserved⟩
      have hpEmpty : p ∈ SelectedSide ∩ Reserved :=
        ⟨hPinterior hpInterior, hpReserved⟩
      rw [hSideReserved] at hpEmpty
      exact hpEmpty
    · intro hp
      exact hp.elim
  · exact hwholeFinite.subset (by
      intro p hp
      exact ⟨hPwhole hp.1, hp.2⟩)

lemma EndpointSidePrefixCoreSimplePath
    (Aarc predecessor approach : PolygonalArc)
    (S : PolygonalSideStrips Aarc)
    (SelectedSide StartSector Reserved :
      Set (EuclideanSpace ℝ (Fin 2)))
    (h terminalGate lastGate : EuclideanSpace ℝ (Fin 2)) :
    (SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip) →
      IsOpen StartSector →
        Convex ℝ StartSector →
          StartSector ⊆ SelectedSide →
            Aarc.source ∈ closure StartSector →
              Aarc.source ∉ StartSector →
                predecessor.carrier ⊆ SelectedSide →
                  approach.carrier ⊆ SelectedSide →
                    predecessor.target = lastGate →
                      approach.source = lastGate →
                        predecessor.carrier ∩ approach.carrier =
                          ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
                          approach.target = h →
                            approach.carrier ∩ segment ℝ h terminalGate =
                              ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
                              Disjoint predecessor.carrier
                                (segment ℝ h terminalGate) →
                                h ≠ terminalGate →
                                  openSegment ℝ h terminalGate ⊆ SelectedSide →
                                    SelectedSide ∩ Reserved =
                                      (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ P : PolygonalArc,
        P.source = Aarc.source ∧
          P.target = predecessor.source ∧
            P.carrier ⊆
              SelectedSide ∪
                ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              P.relativeInterior ⊆ SelectedSide ∧
                P.relativeInterior ∩ Reserved =
                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                Set.Finite
                  (P.carrier ∩
                    (predecessor.carrier ∪ approach.carrier ∪
                      segment ℝ h terminalGate)) ∧
                  P.vertices.Nodup ∧
                    (∀ ⦃i j : ℕ⦄,
                      (hi : i + 1 < P.vertices.length) →
                        (hj : j + 1 < P.vertices.length) →
                          i < j →
                            (segment ℝ P.vertices[i] P.vertices[i + 1] ∩
                                segment ℝ P.vertices[j] P.vertices[j + 1]) =
                              if j = i + 1 then {P.vertices[j]} else ∅) ∧
                      (∀ ⦃i k : ℕ⦄,
                        (hi : i + 1 < P.vertices.length) →
                          (hk : k < P.vertices.length) →
                            k ≠ i → k ≠ i + 1 →
                              P.vertices[k] ∉
                                openSegment ℝ
                                  P.vertices[i] P.vertices[i + 1]) ∧
                        ∃ hfirst : 0 + 1 < P.vertices.length,
                          segment ℝ P.vertices[0] P.vertices[1] ⊆
                              StartSector ∪
                                ({Aarc.source} :
                                  Set (EuclideanSpace ℝ (Fin 2))) ∧
                            openSegment ℝ P.vertices[0] P.vertices[1] ⊆
                              StartSector := by
  intro hSelected hStartOpen hStartConvex hStartSubset hSourceClosure
    hSourceNotStart hPredecessorSide hApproachSide hPredecessorTarget
    hApproachSource hPredecessorApproach hApproachTarget hApproachIncoming
    hPredecessorIncoming hhNeGate hIncomingSide hSideReserved
  let E := EuclideanSpace ℝ (Fin 2)
  have hSelectedOpen : IsOpen SelectedSide := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_open
    · simpa [hright] using S.right_open
  have hSelectedConnected : IsConnected SelectedSide := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_connected
    · simpa [hright] using S.right_connected
  have hSelectedDisjointA : Disjoint SelectedSide Aarc.carrier := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_disjoint_arc
    · simpa [hright] using S.right_disjoint_arc
  have hSourceNotSide : Aarc.source ∉ SelectedSide := by
    intro hs
    exact (Set.disjoint_left.mp hSelectedDisjointA hs)
      (polygonalArc_source_mem_carrier Aarc)
  obtain ⟨Kpredecessor, hKpredecessor⟩ :=
    PolygonalArcFinitePolygonalSet predecessor
  obtain ⟨Kapproach, hKapproach⟩ :=
    PolygonalArcFinitePolygonalSet approach
  have hfinitePredecessorApproach :
      Set.Finite (Kpredecessor.carrier ∩ Kapproach.carrier) := by
    rw [hKpredecessor, hKapproach, hPredecessorApproach]
    exact Set.finite_singleton lastGate
  obtain ⟨Kpa, hKpa⟩ :=
    FinitePolygonalSetUnionOfFiniteIntersection
      Kpredecessor Kapproach hfinitePredecessorApproach
  obtain ⟨incomingArc, hincomingSource, hincomingTarget,
      hincomingCarrier, _hincomingInterior⟩ :=
    StraightSegmentPolygonalArc h terminalGate hhNeGate
  obtain ⟨Kincoming, hKincoming⟩ :=
    PolygonalArcFinitePolygonalSet incomingArc
  have hfinitePaIncoming :
      Set.Finite (Kpa.carrier ∩ Kincoming.carrier) := by
    apply (Set.finite_singleton h).subset
    intro p hp
    rw [hKpa, hKpredecessor, hKapproach, hKincoming,
      hincomingCarrier] at hp
    rcases hp.1 with hpPredecessor | hpApproach
    · exact False.elim
        ((Set.disjoint_left.mp hPredecessorIncoming hpPredecessor) hp.2)
    · have hp' :
          p ∈ approach.carrier ∩ segment ℝ h terminalGate :=
        ⟨hpApproach, hp.2⟩
      rw [hApproachIncoming] at hp'
      simpa using hp'
  obtain ⟨K, hK⟩ :=
    FinitePolygonalSetUnionOfFiniteIntersection Kpa Kincoming
      hfinitePaIncoming
  have hKcarrier :
      K.carrier =
        predecessor.carrier ∪ approach.carrier ∪
          segment ℝ h terminalGate := by
    rw [hK, hKpa, hKpredecessor, hKapproach, hKincoming,
      hincomingCarrier]
  let supportLine : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({s.1, s.2} : Set E)
  have supportLineData :
      ∀ s : E × E, s ∈ K.segments →
        ((supportLine s : Set E).Nonempty ∧
          Module.finrank ℝ (supportLine s).direction = 1) := by
    intro s hs
    constructor
    · exact ⟨s.1, left_mem_affineSpan_pair ℝ s.1 s.2⟩
    · dsimp [supportLine]
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (sub_ne_zero.mpr (K.segment_nondegenerate s hs))
  let terminalLines : Finset (AffineSubspace ℝ E) :=
    K.segments.image supportLine
  have hterminalLines :
      ∀ line ∈ terminalLines,
        ((line : Set E).Nonempty ∧
          Module.finrank ℝ line.direction = 1) := by
    intro line hline
    rcases Finset.mem_image.mp hline with ⟨s, hs, rfl⟩
    exact supportLineData s hs
  have hStartNonempty : StartSector.Nonempty :=
    (show (closure StartSector).Nonempty from
      ⟨Aarc.source, hSourceClosure⟩).of_closure
  obtain ⟨a0, ha0Start, ha0Points, ha0Lines⟩ :=
    FinitePointLineAvoidance StartSector
      (insert Aarc.source (insert predecessor.source K.points))
      terminalLines hStartOpen hStartNonempty hterminalLines
  have ha0NeSource : a0 ≠ Aarc.source := by
    intro h
    exact hSourceNotStart (h ▸ ha0Start)
  have ha0NeTarget : a0 ≠ predecessor.source := by
    intro h
    apply ha0Points
    simp [h]
  have ha0NotK : a0 ∉ K.carrier := by
    intro ha0K
    rw [K.carrier_eq] at ha0K
    rcases ha0K with ha0Point | ha0Segment
    · exact ha0Points (by simp [ha0Point])
    · rcases Set.mem_iUnion.mp ha0Segment with ⟨s, ha0s⟩
      have ha0Support : a0 ∈ (supportLine s.1 : Set E) := by
        rw [segment_eq_image_lineMap] at ha0s
        rcases ha0s with ⟨t, _ht, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t s.1.1 s.1.2
      apply ha0Lines (supportLine s.1)
      · exact Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩
      · exact ha0Support
  have ha0Side : a0 ∈ SelectedSide := hStartSubset ha0Start
  have hInitialOpen :
      openSegment ℝ Aarc.source a0 ⊆ StartSector := by
    have ha0Interior : a0 ∈ interior StartSector := by
      simpa [hStartOpen.interior_eq] using ha0Start
    simpa [hStartOpen.interior_eq] using
      hStartConvex.openSegment_closure_interior_subset_interior
        hSourceClosure ha0Interior
  have hInitial :
      segment ℝ Aarc.source a0 ⊆
        StartSector ∪ ({Aarc.source} : Set E) := by
    intro p hp
    by_cases hpSource : p = Aarc.source
    · exact Or.inr (by simpa [hpSource])
    by_cases hpa0 : p = a0
    · exact Or.inl (by simpa [hpa0] using ha0Start)
    · exact Or.inl
        (hInitialOpen
          (mem_openSegment_of_ne_left_right
            (Ne.symm hpSource) (Ne.symm hpa0) hp))
  have hInitialFinite :
      Set.Finite (segment ℝ Aarc.source a0 ∩ K.carrier) := by
    apply FinitePolygonalSetSegmentIntersectionOfEndpointOffLines K
      Aarc.source a0
    intro s hs
    exact ha0Lines (supportLine s)
      (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hPredecessorSourceSide :
      predecessor.source ∈ SelectedSide :=
    hPredecessorSide (polygonalArc_source_mem_carrier predecessor)
  obtain ⟨r, hrpos, hballSide⟩ :=
    Metric.isOpen_iff.mp hSelectedOpen predecessor.source
      hPredecessorSourceSide
  let protectedLine : AffineSubspace ℝ E :=
    affineSpan ℝ ({Aarc.source, a0} : Set E)
  let finalLines : Finset (AffineSubspace ℝ E) :=
    insert protectedLine terminalLines
  have hprotectedLine :
      ((protectedLine : Set E).Nonempty ∧
        Module.finrank ℝ protectedLine.direction = 1) := by
    constructor
    · exact ⟨Aarc.source,
        left_mem_affineSpan_pair ℝ Aarc.source a0⟩
    · dsimp [protectedLine]
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (sub_ne_zero.mpr ha0NeSource.symm)
  have hfinalLines :
      ∀ line ∈ finalLines,
        ((line : Set E).Nonempty ∧
          Module.finrank ℝ line.direction = 1) := by
    intro line hline
    simp only [finalLines, Finset.mem_insert] at hline
    rcases hline with rfl | hline
    · exact hprotectedLine
    · exact hterminalLines line hline
  obtain ⟨b0, hb0Ball, hb0Points, hb0Lines⟩ :=
    FinitePointLineAvoidance (Metric.ball predecessor.source r)
      (insert predecessor.source (insert a0 K.points))
      finalLines (Metric.isOpen_ball) (Metric.nonempty_ball.2 hrpos)
      hfinalLines
  have hb0Side : b0 ∈ SelectedSide := hballSide hb0Ball
  have hb0NeTarget : b0 ≠ predecessor.source := by
    intro h
    exact hb0Points (by simp [h])
  have hb0NeA0 : b0 ≠ a0 := by
    intro h
    exact hb0Points (by simp [h])
  have hb0NotK : b0 ∉ K.carrier := by
    intro hb0K
    rw [K.carrier_eq] at hb0K
    rcases hb0K with hb0Point | hb0Segment
    · exact hb0Points (by simp [hb0Point])
    · rcases Set.mem_iUnion.mp hb0Segment with ⟨s, hb0s⟩
      have hb0Support : b0 ∈ (supportLine s.1 : Set E) := by
        rw [segment_eq_image_lineMap] at hb0s
        rcases hb0s with ⟨t, _ht, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t s.1.1 s.1.2
      apply hb0Lines (supportLine s.1)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩)
      · exact hb0Support
  have hFinalSegment :
      segment ℝ b0 predecessor.source ⊆ SelectedSide := by
    have hcenter :
        predecessor.source ∈ Metric.ball predecessor.source r :=
      Metric.mem_ball_self hrpos
    intro p hp
    exact hballSide
      ((convex_ball predecessor.source r).segment_subset hb0Ball hcenter hp)
  have hFinalFinite :
      Set.Finite
        (segment ℝ b0 predecessor.source ∩ K.carrier) := by
    have hfinite :=
      FinitePolygonalSetSegmentIntersectionOfEndpointOffLines
        K predecessor.source b0 (by
          intro s hs
          exact hb0Lines (supportLine s)
            (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨s, hs, rfl⟩)))
    simpa [segment_symm ℝ predecessor.source b0] using hfinite
  have hSelectedComponent :
      ComplementComponent SelectedSideᶜ SelectedSide := by
    refine ⟨hSelectedConnected.1, by simp, hSelectedConnected, ?_⟩
    intro C _hCnonempty hCsubset _hCconnected _hSelectedC
    simpa using hCsubset
  have hSelectedPolygonal :
      PolygonallyPathConnected SelectedSide :=
    OpenConnectedComponentPolygonallyConnected
      SelectedSide SelectedSide hSelectedOpen hSelectedComponent
  obtain ⟨middle0, hmiddle0Source, hmiddle0Target,
      hmiddle0Carrier⟩ :=
    hSelectedPolygonal ha0Side hb0Side
  obtain ⟨middle, hmiddleSource, hmiddleTarget, hmiddleCarrier,
      _hmiddleNear, hmiddleGeneral, _hmiddleAvoid⟩ :=
    FinitePolygonalPerturbation K SelectedSide middle0 ∅ 1
      hSelectedOpen hmiddle0Carrier
      ⟨by simpa [hmiddle0Source] using ha0Side,
        by simpa [hmiddle0Source] using ha0NotK⟩
      ⟨by simpa [hmiddle0Target] using hb0Side,
        by simpa [hmiddle0Target] using hb0NotK⟩
      (by norm_num) isCompact_empty (Set.empty_subset SelectedSideᶜ)
  have hmiddleFinite :
      Set.Finite (middle.carrier ∩ K.carrier) :=
    hmiddleGeneral.2.2.2.2
  obtain ⟨whole, hwholeSource, hwholeTarget, hwholeLength, hwholeZero,
      hwholeOne, hwholeCarrier, hwholeFinite, hwholeRest⟩ :=
    build_prefix_whole_path Aarc predecessor middle a0 b0 SelectedSide
      StartSector K.carrier
      (hmiddleSource.trans hmiddle0Source)
      (hmiddleTarget.trans hmiddle0Target) hInitial hStartSubset
      hmiddleCarrier hFinalSegment hInitialFinite hmiddleFinite hFinalFinite
  have hSourceNeTarget : Aarc.source ≠ predecessor.source := by
    intro heq
    exact hSourceNotSide (heq ▸ hPredecessorSourceSide)
  obtain ⟨P, hPsourceWhole, hPtargetWhole, hPwhole, hPlocal⟩ :=
    PolygonalPathToPolygonalArc whole
      (by simpa [hwholeSource, hwholeTarget] using hSourceNeTarget)
  have hwholeFiniteTerminal :
      Set.Finite
        (whole.carrier ∩
          (predecessor.carrier ∪ approach.carrier ∪
            segment ℝ h terminalGate)) := by
    rw [← hKcarrier]
    exact hwholeFinite
  exact finish_prefix_core_simple_path Aarc predecessor P whole a0
    SelectedSide StartSector Reserved
    (predecessor.carrier ∪ approach.carrier ∪ segment ℝ h terminalGate)
    hPsourceWhole hPtargetWhole hPwhole hPlocal hwholeSource hwholeTarget
    hwholeLength hwholeZero hwholeOne hInitial hSourceNotSide hwholeRest
    hwholeCarrier hwholeFiniteTerminal hSideReserved
