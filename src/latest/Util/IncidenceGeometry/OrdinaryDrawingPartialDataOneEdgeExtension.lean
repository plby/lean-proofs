import Util.IncidenceGeometry.OrdinaryDrawingPartialDataOneEdgeAvoidance

open Classical
noncomputable section


lemma OrdinaryDrawingPartialDataOneEdgeExtension {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    {drawn : Finset G.edgeFinset}
    (P : OrdinaryDrawingPartialData G drawn)
    (e : G.edgeFinset) (he : e ∉ drawn) :
    Nonempty (OrdinaryDrawingPartialData G (insert e drawn)) := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  obtain ⟨u, v, z, Γ, huv, heuv, hΓvertices, hΓsource, hΓtarget, hΓcarrier,
      hΓrelativeInterior, hNoVertex, hNoOldCrossing, hNoOldVertex, hzNotOldSegment,
      hNoOverlapLeft, hNoOverlapRight, hNonparallelLeft, hNonparallelRight⟩ :=
    OrdinaryDrawingPartialDataOneEdgeAvoidance G P e he
  let a : E := P.vertexPlacement u
  let b : E := P.vertexPlacement v
  let newDrawn : Finset G.edgeFinset := insert e drawn
  let newEdge : {f : G.edgeFinset // f ∈ newDrawn} := ⟨e, by simp [newDrawn]⟩
  let oldEdge : {f : G.edgeFinset // f ∈ drawn} → {f : G.edgeFinset // f ∈ newDrawn} :=
    fun old => ⟨old.1, by simp [newDrawn, old.2]⟩
  let edgeArc' : {f : G.edgeFinset // f ∈ newDrawn} → PolygonalArc :=
    fun f =>
      if hf : f.1 = e then Γ
      else
        have hfmem : f.1 ∈ insert e drawn := by
          change f.1 ∈ newDrawn
          exact f.2
        P.edgeArc ⟨f.1, (Finset.mem_insert.mp hfmem).resolve_left hf⟩
  have edge_cases :
      ∀ f : {f : G.edgeFinset // f ∈ newDrawn},
        f = newEdge ∨ ∃ old : {f : G.edgeFinset // f ∈ drawn}, f = oldEdge old := by
    intro f
    have hfmem : f.1 ∈ insert e drawn := by
      change f.1 ∈ newDrawn
      exact f.2
    rcases Finset.mem_insert.mp hfmem with hf | hf
    · left
      exact Subtype.ext hf
    · right
      refine ⟨⟨f.1, hf⟩, ?_⟩
      exact Subtype.ext rfl
  have edgeArc_new : edgeArc' newEdge = Γ := by
    simp [edgeArc', newEdge]
  have edgeArc_old :
      ∀ old : {f : G.edgeFinset // f ∈ drawn}, edgeArc' (oldEdge old) = P.edgeArc old := by
    intro old
    have hne : old.1 ≠ e := by
      intro h
      exact he (by simpa [h] using old.2)
    simp [edgeArc', oldEdge, hne]
  let oldStart (old : {f : G.edgeFinset // f ∈ drawn})
      (j : Fin ((P.edgeArc old).vertices.length - 1)) : E :=
    (P.edgeArc old).vertices[j.1]'(by
      have hlen : 2 ≤ (P.edgeArc old).vertices.length := (P.edgeArc old).length_ge_two
      omega)
  let oldEnd (old : {f : G.edgeFinset // f ∈ drawn})
      (j : Fin ((P.edgeArc old).vertices.length - 1)) : E :=
    (P.edgeArc old).vertices[j.1 + 1]'(by
      have hlen : 2 ≤ (P.edgeArc old).vertices.length := (P.edgeArc old).length_ge_two
      omega)
  have oldIndex (old : {f : G.edgeFinset // f ∈ drawn})
      (j : Fin ((P.edgeArc old).vertices.length - 1)) :
      j.1 + 1 < (P.edgeArc old).vertices.length := by
    have hlen : 2 ≤ (P.edgeArc old).vertices.length := (P.edgeArc old).length_ge_two
    omega
  let leftCondition (old : {f : G.edgeFinset // f ∈ drawn})
      (j : Fin ((P.edgeArc old).vertices.length - 1)) (p : E) : Prop :=
    p ∈ segment ℝ a z ∧ p ∈ Γ.relativeInterior ∧
      p ∈ segment ℝ (oldStart old j) (oldEnd old j) ∧
        p ∈ (P.edgeArc old).relativeInterior
  let rightCondition (old : {f : G.edgeFinset // f ∈ drawn})
      (j : Fin ((P.edgeArc old).vertices.length - 1)) (p : E) : Prop :=
    p ∈ segment ℝ z b ∧ p ∈ Γ.relativeInterior ∧
      p ∈ segment ℝ (oldStart old j) (oldEnd old j) ∧
        p ∈ (P.edgeArc old).relativeInterior
  let chooseSet (Q : E → Prop) : Finset E :=
    if h : ∃ p : E, Q p then {Classical.choose h} else ∅
  let leftCrossings : Finset E :=
    drawn.attach.biUnion (fun old : {f : G.edgeFinset // f ∈ drawn} =>
      (Finset.univ : Finset (Fin ((P.edgeArc old).vertices.length - 1))).biUnion
        (fun j => chooseSet (leftCondition old j)))
  let rightCrossings : Finset E :=
    drawn.attach.biUnion (fun old : {f : G.edgeFinset // f ∈ drawn} =>
      (Finset.univ : Finset (Fin ((P.edgeArc old).vertices.length - 1))).biUnion
        (fun j => chooseSet (rightCondition old j)))
  let newCrossings : Finset E := leftCrossings ∪ rightCrossings
  have left_unique :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p q : E⦄,
        leftCondition old j p → leftCondition old j q → q = p := by
    intro old j p q hp hq
    by_contra hqp
    have hpq : p ≠ q := by
      intro hpq
      exact hqp hpq.symm
    have hsubset :
        segment ℝ p q ⊆ segment ℝ a z ∩ segment ℝ (oldStart old j) (oldEnd old j) := by
      intro r hr
      refine ⟨?_, ?_⟩
      · exact (convex_segment a z).segment_subset hp.1 hq.1 hr
      · exact (convex_segment (oldStart old j) (oldEnd old j)).segment_subset hp.2.2.1
          hq.2.2.1 hr
    have hbad := hNoOverlapLeft old j.1 (oldIndex old j)
    apply hbad
    refine ⟨p, q, hpq, ?_⟩
    simpa [oldStart, oldEnd, a] using hsubset
  have right_unique :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p q : E⦄,
        rightCondition old j p → rightCondition old j q → q = p := by
    intro old j p q hp hq
    by_contra hqp
    have hpq : p ≠ q := by
      intro hpq
      exact hqp hpq.symm
    have hsubset :
        segment ℝ p q ⊆ segment ℝ z b ∩ segment ℝ (oldStart old j) (oldEnd old j) := by
      intro r hr
      refine ⟨?_, ?_⟩
      · exact (convex_segment z b).segment_subset hp.1 hq.1 hr
      · exact (convex_segment (oldStart old j) (oldEnd old j)).segment_subset hp.2.2.1
          hq.2.2.1 hr
    have hbad := hNoOverlapRight old j.1 (oldIndex old j)
    apply hbad
    refine ⟨p, q, hpq, ?_⟩
    simpa [oldStart, oldEnd, b] using hsubset
  have mem_leftCrossings :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p : E⦄,
        leftCondition old j p → p ∈ leftCrossings := by
    intro old j p hp
    have hex : ∃ q : E, leftCondition old j q := ⟨p, hp⟩
    have hchoose : Classical.choose hex = p :=
      left_unique old j hp (Classical.choose_spec hex)
    dsimp [leftCrossings]
    rw [Finset.mem_biUnion]
    refine ⟨old, by simp, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨j, by simp, ?_⟩
    simp [chooseSet, hex, hchoose]
  have mem_rightCrossings :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p : E⦄,
        rightCondition old j p → p ∈ rightCrossings := by
    intro old j p hp
    have hex : ∃ q : E, rightCondition old j q := ⟨p, hp⟩
    have hchoose : Classical.choose hex = p :=
      right_unique old j hp (Classical.choose_spec hex)
    dsimp [rightCrossings]
    rw [Finset.mem_biUnion]
    refine ⟨old, by simp, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨j, by simp, ?_⟩
    simp [chooseSet, hex, hchoose]
  have crossingSetSet_finite :
      ({p : E |
        ∃ e₁ e₂ : {f : G.edgeFinset // f ∈ newDrawn},
          e₁ ≠ e₂ ∧ p ∈ (edgeArc' e₁).relativeInterior ∧
            p ∈ (edgeArc' e₂).relativeInterior}).Finite := by
    refine (P.crossingSet ∪ newCrossings).finite_toSet.subset ?_
    intro p hp
    rcases hp with ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
    rcases edge_cases e₁ with rfl | ⟨old₁, rfl⟩
    · rcases edge_cases e₂ with hnew₂ | ⟨old₂, rfl⟩
      · exact False.elim (h₁₂ hnew₂.symm)
      ·
        have hpΓ : p ∈ Γ.relativeInterior := by simpa [edgeArc_new] using hp₁
        have hpOld : p ∈ (P.edgeArc old₂).relativeInterior := by
          simpa [edgeArc_old] using hp₂
        have hpNewUnion : p ∈ segment ℝ a z ∪ segment ℝ z b := by
          have htmp := hpΓ
          rw [hΓrelativeInterior] at htmp
          exact htmp.1
        have hpOldCarrier : p ∈ (P.edgeArc old₂).carrier := by
          have htmp := hpOld
          rw [(P.edgeArc old₂).relativeInterior_eq] at htmp
          exact htmp.1
        rw [(P.edgeArc old₂).carrier_eq] at hpOldCarrier
        rcases hpOldCarrier with ⟨j, hj, hpOldSeg⟩
        let jf : Fin ((P.edgeArc old₂).vertices.length - 1) := ⟨j, by
          have hlen : 2 ≤ (P.edgeArc old₂).vertices.length := (P.edgeArc old₂).length_ge_two
          omega⟩
        rcases hpNewUnion with hpLeft | hpRight
        · have hmem : p ∈ newCrossings := by
            have hleft : p ∈ leftCrossings := by
              apply mem_leftCrossings old₂ jf
              refine ⟨hpLeft, hpΓ, ?_, hpOld⟩
              simpa [oldStart, oldEnd, jf] using hpOldSeg
            simp [newCrossings, hleft]
          simp [hmem]
        · have hmem : p ∈ newCrossings := by
            have hright : p ∈ rightCrossings := by
              apply mem_rightCrossings old₂ jf
              refine ⟨hpRight, hpΓ, ?_, hpOld⟩
              simpa [oldStart, oldEnd, jf] using hpOldSeg
            simp [newCrossings, hright]
          simp [hmem]
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      ·
        have hpOld : p ∈ (P.edgeArc old₁).relativeInterior := by
          simpa [edgeArc_old] using hp₁
        have hpΓ : p ∈ Γ.relativeInterior := by simpa [edgeArc_new] using hp₂
        have hpNewUnion : p ∈ segment ℝ a z ∪ segment ℝ z b := by
          have htmp := hpΓ
          rw [hΓrelativeInterior] at htmp
          exact htmp.1
        have hpOldCarrier : p ∈ (P.edgeArc old₁).carrier := by
          have htmp := hpOld
          rw [(P.edgeArc old₁).relativeInterior_eq] at htmp
          exact htmp.1
        rw [(P.edgeArc old₁).carrier_eq] at hpOldCarrier
        rcases hpOldCarrier with ⟨j, hj, hpOldSeg⟩
        let jf : Fin ((P.edgeArc old₁).vertices.length - 1) := ⟨j, by
          have hlen : 2 ≤ (P.edgeArc old₁).vertices.length := (P.edgeArc old₁).length_ge_two
          omega⟩
        rcases hpNewUnion with hpLeft | hpRight
        · have hmem : p ∈ newCrossings := by
            have hleft : p ∈ leftCrossings := by
              apply mem_leftCrossings old₁ jf
              refine ⟨hpLeft, hpΓ, ?_, hpOld⟩
              simpa [oldStart, oldEnd, jf] using hpOldSeg
            simp [newCrossings, hleft]
          simp [hmem]
        · have hmem : p ∈ newCrossings := by
            have hright : p ∈ rightCrossings := by
              apply mem_rightCrossings old₁ jf
              refine ⟨hpRight, hpΓ, ?_, hpOld⟩
              simpa [oldStart, oldEnd, jf] using hpOldSeg
            simp [newCrossings, hright]
          simp [hmem]
      ·
        have h₁₂old : old₁ ≠ old₂ := by
          intro h
          apply h₁₂
          rw [h]
        have hmem : p ∈ P.crossingSet := by
          apply (P.crossingSet_spec p).mpr
          refine ⟨old₁, old₂, h₁₂old, ?_, ?_⟩
          · simpa [edgeArc_old] using hp₁
          · simpa [edgeArc_old] using hp₂
        simp [hmem]
  let crossingSet' : Finset E := crossingSetSet_finite.toFinset
  have no_new_two_old :
      ∀ ⦃old₁ old₂ : {f : G.edgeFinset // f ∈ drawn}⦄ ⦃p : E⦄,
        old₁ ≠ old₂ →
          p ∈ Γ.relativeInterior →
            p ∈ (P.edgeArc old₁).relativeInterior →
              p ∈ (P.edgeArc old₂).relativeInterior → False := by
    intro old₁ old₂ p h₁₂ hpΓ hp₁ hp₂
    have hpCross : p ∈ P.crossingSet := by
      apply (P.crossingSet_spec p).mpr
      exact ⟨old₁, old₂, h₁₂, hp₁, hp₂⟩
    exact hNoOldCrossing p hpCross hpΓ
  have hΓnodup : [a, z, b].Nodup := by
    simpa [hΓvertices, a, b] using Γ.simple_vertices
  have hΓnodup_props : (a ≠ z ∧ a ≠ b) ∧ z ≠ b := by
    simpa [List.nodup_cons, List.mem_cons] using hΓnodup
  have haz : a ≠ z := by
    exact hΓnodup_props.1.1
  have hzb : z ≠ b := by
    exact hΓnodup_props.2
  have old_open_of_new_rel :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p : E⦄,
        p ∈ Γ.relativeInterior →
          p ∈ segment ℝ (oldStart old j) (oldEnd old j) →
            p ∈ openSegment ℝ (oldStart old j) (oldEnd old j) := by
    intro old j p hpΓ hpSeg
    refine mem_openSegment_of_ne_left_right ?_ ?_ hpSeg
    · intro hp
      exact hNoOldVertex old j.1 (Nat.lt_of_succ_lt (oldIndex old j))
        (by simpa [oldStart, hp] using hpΓ)
    · intro hp
      exact hNoOldVertex old (j.1 + 1) (oldIndex old j)
        (by simpa [oldEnd, hp] using hpΓ)
  have new_left_open_of_old_seg :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p : E⦄,
        p ∈ Γ.relativeInterior →
          p ∈ segment ℝ (oldStart old j) (oldEnd old j) →
            p ∈ segment ℝ a z → p ∈ openSegment ℝ a z := by
    intro old j p hpΓ hpOldSeg hpNewSeg
    refine mem_openSegment_of_ne_left_right ?_ ?_ hpNewSeg
    · intro hp
      have hpNot : p ∉ ({a, b} : Set E) := by
        have htmp := hpΓ
        rw [hΓrelativeInterior] at htmp
        simpa [a, b] using htmp.2
      exact hpNot (by simp [hp])
    · intro hp
      exact hzNotOldSegment old j.1 (oldIndex old j)
        (by simpa [oldStart, oldEnd, hp] using hpOldSeg)
  have new_right_open_of_old_seg :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn})
        (j : Fin ((P.edgeArc old).vertices.length - 1)) ⦃p : E⦄,
        p ∈ Γ.relativeInterior →
          p ∈ segment ℝ (oldStart old j) (oldEnd old j) →
            p ∈ segment ℝ z b → p ∈ openSegment ℝ z b := by
    intro old j p hpΓ hpOldSeg hpNewSeg
    refine mem_openSegment_of_ne_left_right ?_ ?_ hpNewSeg
    · intro hp
      exact hzNotOldSegment old j.1 (oldIndex old j)
        (by simpa [oldStart, oldEnd, hp] using hpOldSeg)
    · intro hp
      have hpNot : p ∉ ({a, b} : Set E) := by
        have htmp := hpΓ
        rw [hΓrelativeInterior] at htmp
        simpa [a, b] using htmp.2
      exact hpNot (by simp [hp])
  have not_smul_symm :
      ∀ {x y : E}, x ≠ 0 →
        (¬ ∃ c : ℝ, y = c • x) → ¬ ∃ c : ℝ, x = c • y := by
    intro x y hx hnot hxy
    rcases hxy with ⟨c, hc⟩
    have hcne : c ≠ 0 := by
      intro hc0
      apply hx
      simpa [hc0] using hc
    apply hnot
    refine ⟨c⁻¹, ?_⟩
    calc
      y = c⁻¹ • x := by
        rw [hc]
        simp [hcne]
      _ = c⁻¹ • x := rfl
  have transverse_new_old :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn}) ⦃p : E⦄,
        p ∈ Γ.relativeInterior →
          p ∈ (P.edgeArc old).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < Γ.vertices.length)
                (hj : j + 1 < (P.edgeArc old).vertices.length),
                p ∈ segment ℝ Γ.vertices[i] Γ.vertices[i + 1] ∧
                  p ∈ segment ℝ (P.edgeArc old).vertices[j]
                    (P.edgeArc old).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (P.edgeArc old).vertices[j + 1] - (P.edgeArc old).vertices[j] =
                        c • (Γ.vertices[i + 1] - Γ.vertices[i]) := by
    intro old p hpΓ hpOld
    have hpNewUnion : p ∈ segment ℝ a z ∪ segment ℝ z b := by
      have htmp := hpΓ
      rw [hΓrelativeInterior] at htmp
      exact htmp.1
    have hpOldCarrier : p ∈ (P.edgeArc old).carrier := by
      have htmp := hpOld
      rw [(P.edgeArc old).relativeInterior_eq] at htmp
      exact htmp.1
    rw [(P.edgeArc old).carrier_eq] at hpOldCarrier
    rcases hpOldCarrier with ⟨j, hj, hpOldSeg⟩
    let jf : Fin ((P.edgeArc old).vertices.length - 1) := ⟨j, by
      have hlen : 2 ≤ (P.edgeArc old).vertices.length := (P.edgeArc old).length_ge_two
      omega⟩
    have hpOldSeg' : p ∈ segment ℝ (oldStart old jf) (oldEnd old jf) := by
      simpa [oldStart, oldEnd, jf] using hpOldSeg
    have hpOldOpen : p ∈ openSegment ℝ (oldStart old jf) (oldEnd old jf) :=
      old_open_of_new_rel old jf hpΓ hpOldSeg'
    rcases hpNewUnion with hpLeft | hpRight
    · have hpNewOpen : p ∈ openSegment ℝ a z :=
        new_left_open_of_old_seg old jf hpΓ hpOldSeg' hpLeft
      refine ⟨0, j, ?_, hj, ?_, hpOldSeg, ?_⟩
      · simp [hΓvertices]
      · simpa [hΓvertices, a] using hpLeft
      · simpa [hΓvertices, a, oldStart, oldEnd, jf] using
          hNonparallelLeft old j hj p hpNewOpen hpOldOpen
    · have hpNewOpen : p ∈ openSegment ℝ z b :=
        new_right_open_of_old_seg old jf hpΓ hpOldSeg' hpRight
      refine ⟨1, j, ?_, hj, ?_, hpOldSeg, ?_⟩
      · simp [hΓvertices]
      · simpa [hΓvertices, b] using hpRight
      · simpa [hΓvertices, b, oldStart, oldEnd, jf] using
          hNonparallelRight old j hj p hpNewOpen hpOldOpen
  have transverse_old_new :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn}) ⦃p : E⦄,
        p ∈ (P.edgeArc old).relativeInterior →
          p ∈ Γ.relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (P.edgeArc old).vertices.length)
                (hj : j + 1 < Γ.vertices.length),
                p ∈ segment ℝ (P.edgeArc old).vertices[i]
                    (P.edgeArc old).vertices[i + 1] ∧
                  p ∈ segment ℝ Γ.vertices[j] Γ.vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      Γ.vertices[j + 1] - Γ.vertices[j] =
                        c • ((P.edgeArc old).vertices[i + 1] -
                          (P.edgeArc old).vertices[i]) := by
    intro old p hpOld hpΓ
    have hpNewUnion : p ∈ segment ℝ a z ∪ segment ℝ z b := by
      have htmp := hpΓ
      rw [hΓrelativeInterior] at htmp
      exact htmp.1
    have hpOldCarrier : p ∈ (P.edgeArc old).carrier := by
      have htmp := hpOld
      rw [(P.edgeArc old).relativeInterior_eq] at htmp
      exact htmp.1
    rw [(P.edgeArc old).carrier_eq] at hpOldCarrier
    rcases hpOldCarrier with ⟨i, hi, hpOldSeg⟩
    let jf : Fin ((P.edgeArc old).vertices.length - 1) := ⟨i, by
      have hlen : 2 ≤ (P.edgeArc old).vertices.length := (P.edgeArc old).length_ge_two
      omega⟩
    have hpOldSeg' : p ∈ segment ℝ (oldStart old jf) (oldEnd old jf) := by
      simpa [oldStart, oldEnd, jf] using hpOldSeg
    have hpOldOpen : p ∈ openSegment ℝ (oldStart old jf) (oldEnd old jf) :=
      old_open_of_new_rel old jf hpΓ hpOldSeg'
    rcases hpNewUnion with hpLeft | hpRight
    · have hpNewOpen : p ∈ openSegment ℝ a z :=
        new_left_open_of_old_seg old jf hpΓ hpOldSeg' hpLeft
      have hnot := hNonparallelLeft old i hi p hpNewOpen hpOldOpen
      have hnew_ne : z - a ≠ 0 := sub_ne_zero.mpr haz.symm
      refine ⟨i, 0, hi, ?_, hpOldSeg, ?_, ?_⟩
      · simp [hΓvertices]
      · simpa [hΓvertices, a] using hpLeft
      · simpa [hΓvertices, a, oldStart, oldEnd, jf] using
          not_smul_symm hnew_ne
            (by simpa [oldStart, oldEnd, jf] using hnot)
    · have hpNewOpen : p ∈ openSegment ℝ z b :=
        new_right_open_of_old_seg old jf hpΓ hpOldSeg' hpRight
      have hnot := hNonparallelRight old i hi p hpNewOpen hpOldOpen
      have hnew_ne : b - z ≠ 0 := sub_ne_zero.mpr hzb.symm
      refine ⟨i, 1, hi, ?_, hpOldSeg, ?_, ?_⟩
      · simp [hΓvertices]
      · simpa [hΓvertices, b] using hpRight
      · simpa [hΓvertices, b, oldStart, oldEnd, jf] using
          not_smul_symm hnew_ne
            (by simpa [oldStart, oldEnd, jf] using hnot)
  refine ⟨({
    vertexPlacement := P.vertexPlacement
    vertexPlacement_injective := P.vertexPlacement_injective
    edgeArc := edgeArc'
    edgeArc_endpoints := ?_
    crossingSet := crossingSet'
    no_vertex_in_edge_interior := ?_
    no_three_edge_interiors_meet := ?_
    transverse_intersections := ?_
    no_shared_nondegenerate_subarc := ?_
    crossingSet_spec := ?_ } :
      OrdinaryDrawingPartialData G (insert e drawn))⟩
  · intro f
    rcases edge_cases f with rfl | ⟨old, rfl⟩
    · refine ⟨u, v, huv, heuv, Or.inl ?_⟩
      exact ⟨by simpa [edgeArc_new, a] using hΓsource,
        by simpa [edgeArc_new, b] using hΓtarget⟩
    · simpa [edgeArc_old] using P.edgeArc_endpoints old
  · intro w f
    rcases edge_cases f with rfl | ⟨old, rfl⟩
    · simpa [edgeArc_new] using hNoVertex w
    · simpa [edgeArc_old] using P.no_vertex_in_edge_interior w old
  · intro e₁ e₂ e₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
    rcases edge_cases e₁ with rfl | ⟨old₁, rfl⟩
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · exact h₁₂ rfl
      · rcases edge_cases e₃ with rfl | ⟨old₃, rfl⟩
        · exact h₁₃ rfl
        · have hold₂₃ : old₂ ≠ old₃ := by
            intro h
            exact h₂₃ (by rw [h])
          exact no_new_two_old hold₂₃ (by simpa [edgeArc_new] using hp₁)
            (by simpa [edgeArc_old] using hp₂)
            (by simpa [edgeArc_old] using hp₃)
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · rcases edge_cases e₃ with rfl | ⟨old₃, rfl⟩
        · exact h₂₃ rfl
        · have hold₁₃ : old₁ ≠ old₃ := by
            intro h
            exact h₁₃ (by rw [h])
          exact no_new_two_old hold₁₃ (by simpa [edgeArc_new] using hp₂)
            (by simpa [edgeArc_old] using hp₁)
            (by simpa [edgeArc_old] using hp₃)
      · rcases edge_cases e₃ with rfl | ⟨old₃, rfl⟩
        · have hold₁₂ : old₁ ≠ old₂ := by
            intro h
            exact h₁₂ (by rw [h])
          exact no_new_two_old hold₁₂ (by simpa [edgeArc_new] using hp₃)
            (by simpa [edgeArc_old] using hp₁)
            (by simpa [edgeArc_old] using hp₂)
        · have hold₁₂ : old₁ ≠ old₂ := by
            intro h
            exact h₁₂ (by rw [h])
          have hold₁₃ : old₁ ≠ old₃ := by
            intro h
            exact h₁₃ (by rw [h])
          have hold₂₃ : old₂ ≠ old₃ := by
            intro h
            exact h₂₃ (by rw [h])
          exact P.no_three_edge_interiors_meet hold₁₂ hold₁₃ hold₂₃
            (by simpa [edgeArc_old] using hp₁)
            (by simpa [edgeArc_old] using hp₂)
            (by simpa [edgeArc_old] using hp₃)
  · intro e₁ e₂ p h₁₂ hp₁ hp₂
    rcases edge_cases e₁ with rfl | ⟨old₁, rfl⟩
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · exact False.elim (h₁₂ rfl)
      · simpa [edgeArc_new, edgeArc_old] using
          transverse_new_old old₂ (by simpa [edgeArc_new] using hp₁)
            (by simpa [edgeArc_old] using hp₂)
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · simpa [edgeArc_new, edgeArc_old] using
          transverse_old_new old₁ (by simpa [edgeArc_old] using hp₁)
            (by simpa [edgeArc_new] using hp₂)
      · have hold₁₂ : old₁ ≠ old₂ := by
          intro h
          exact h₁₂ (by rw [h])
        simpa [edgeArc_old] using
          P.transverse_intersections hold₁₂
            (by simpa [edgeArc_old] using hp₁)
            (by simpa [edgeArc_old] using hp₂)
  · intro e₁ e₂ h₁₂ hoverlap
    rcases hoverlap with ⟨i, j, hi, hj, p, q, hpq, hsubset⟩
    rcases edge_cases e₁ with rfl | ⟨old₁, rfl⟩
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · exact h₁₂ rfl
      · have hiΓ : i + 1 < Γ.vertices.length := by
          simpa [edgeArc_new] using hi
        have hjOld : j + 1 < (P.edgeArc old₂).vertices.length := by
          simpa [edgeArc_old] using hj
        have hi_cases : i = 0 ∨ i = 1 := by
          have : i + 1 < 3 := by simpa [hΓvertices] using hiΓ
          omega
        rcases hi_cases with rfl | rfl
        · apply hNoOverlapLeft old₂ j hjOld
          refine ⟨p, q, hpq, ?_⟩
          intro r hr
          have h := hsubset hr
          refine ⟨?_, ?_⟩
          · simpa [edgeArc_new, hΓvertices, a] using h.1
          · simpa [edgeArc_old] using h.2
        · apply hNoOverlapRight old₂ j hjOld
          refine ⟨p, q, hpq, ?_⟩
          intro r hr
          have h := hsubset hr
          refine ⟨?_, ?_⟩
          · simpa [edgeArc_new, hΓvertices, b] using h.1
          · simpa [edgeArc_old] using h.2
    · rcases edge_cases e₂ with rfl | ⟨old₂, rfl⟩
      · have hiOld : i + 1 < (P.edgeArc old₁).vertices.length := by
          simpa [edgeArc_old] using hi
        have hjΓ : j + 1 < Γ.vertices.length := by
          simpa [edgeArc_new] using hj
        have hj_cases : j = 0 ∨ j = 1 := by
          have : j + 1 < 3 := by simpa [hΓvertices] using hjΓ
          omega
        rcases hj_cases with rfl | rfl
        · apply hNoOverlapLeft old₁ i hiOld
          refine ⟨p, q, hpq, ?_⟩
          intro r hr
          have h := hsubset hr
          refine ⟨?_, ?_⟩
          · simpa [edgeArc_new, hΓvertices, a] using h.2
          · simpa [edgeArc_old] using h.1
        · apply hNoOverlapRight old₁ i hiOld
          refine ⟨p, q, hpq, ?_⟩
          intro r hr
          have h := hsubset hr
          refine ⟨?_, ?_⟩
          · simpa [edgeArc_new, hΓvertices, b] using h.2
          · simpa [edgeArc_old] using h.1
      · have hold₁₂ : old₁ ≠ old₂ := by
          intro h
          exact h₁₂ (by rw [h])
        apply P.no_shared_nondegenerate_subarc hold₁₂
        refine ⟨i, j, ?_, ?_, p, q, hpq, ?_⟩
        · simpa [edgeArc_old] using hi
        · simpa [edgeArc_old] using hj
        · intro r hr
          have h := hsubset hr
          simpa [edgeArc_old] using h
  · intro p
    change p ∈ crossingSetSet_finite.toFinset ↔
      p ∈ ({p : E |
      ∃ e₁ e₂ : {f : G.edgeFinset // f ∈ newDrawn},
        e₁ ≠ e₂ ∧ p ∈ (edgeArc' e₁).relativeInterior ∧
          p ∈ (edgeArc' e₂).relativeInterior} : Set E)
    exact Set.Finite.mem_toFinset crossingSetSet_finite
