import ErdosProblems.Erdos733.ST.OrdinaryDrawingPartialData
import ErdosProblems.Erdos733.ST.OrdinaryDrawingAuxiliaryBendPointAvoidance

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingPartialDataOneEdgeAvoidance]
lemma OrdinaryDrawingPartialDataOneEdgeAvoidance {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    {drawn : Finset G.edgeFinset}
    (P : OrdinaryDrawingPartialData G drawn)
    (e : G.edgeFinset) (he : e ∉ drawn) :
    ∃ u v : V, ∃ z : EuclideanSpace ℝ (Fin 2), ∃ Γ : PolygonalArc,
      G.Adj u v ∧ e.1 = Sym2.mk u v ∧
        Γ.vertices = [P.vertexPlacement u, z, P.vertexPlacement v] ∧
          Γ.source = P.vertexPlacement u ∧
            Γ.target = P.vertexPlacement v ∧
              Γ.carrier =
                segment ℝ (P.vertexPlacement u) z ∪
                  segment ℝ z (P.vertexPlacement v) ∧
                Γ.relativeInterior =
                  (segment ℝ (P.vertexPlacement u) z ∪
                      segment ℝ z (P.vertexPlacement v)) \
                    ({P.vertexPlacement u, P.vertexPlacement v} :
                      Set (EuclideanSpace ℝ (Fin 2))) ∧
                  (∀ w : V, P.vertexPlacement w ∉ Γ.relativeInterior) ∧
                    (∀ p : EuclideanSpace ℝ (Fin 2),
                      p ∈ P.crossingSet → p ∉ Γ.relativeInterior) ∧
                      (∀ old : {f : G.edgeFinset // f ∈ drawn},
                        ∀ k : ℕ, ∀ hk : k < (P.edgeArc old).vertices.length,
                          (P.edgeArc old).vertices[k] ∉ Γ.relativeInterior) ∧
                        (∀ old : {f : G.edgeFinset // f ∈ drawn},
                          ∀ j : ℕ, ∀ hj : j + 1 < (P.edgeArc old).vertices.length,
                            z ∉ segment ℝ (P.edgeArc old).vertices[j]
                              (P.edgeArc old).vertices[j + 1]) ∧
                        (∀ old : {f : G.edgeFinset // f ∈ drawn},
                          ∀ j : ℕ, ∀ hj : j + 1 < (P.edgeArc old).vertices.length,
                            ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
                              segment ℝ p q ⊆
                                segment ℝ (P.vertexPlacement u) z ∩
                                  segment ℝ (P.edgeArc old).vertices[j]
                                    (P.edgeArc old).vertices[j + 1]) ∧
                          (∀ old : {f : G.edgeFinset // f ∈ drawn},
                            ∀ j : ℕ, ∀ hj : j + 1 < (P.edgeArc old).vertices.length,
                              ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
                                segment ℝ p q ⊆
                                  segment ℝ z (P.vertexPlacement v) ∩
                                    segment ℝ (P.edgeArc old).vertices[j]
                                      (P.edgeArc old).vertices[j + 1]) ∧
                            (∀ old : {f : G.edgeFinset // f ∈ drawn},
                              ∀ j : ℕ, ∀ hj : j + 1 < (P.edgeArc old).vertices.length,
                                ∀ p : EuclideanSpace ℝ (Fin 2),
                                  p ∈ openSegment ℝ (P.vertexPlacement u) z →
                                    p ∈ openSegment ℝ (P.edgeArc old).vertices[j]
                                      (P.edgeArc old).vertices[j + 1] →
                                      ¬ ∃ c : ℝ,
                                        (P.edgeArc old).vertices[j + 1] -
                                            (P.edgeArc old).vertices[j] =
                                          c • (z - P.vertexPlacement u)) ∧
                              (∀ old : {f : G.edgeFinset // f ∈ drawn},
                                ∀ j : ℕ, ∀ hj : j + 1 < (P.edgeArc old).vertices.length,
                                  ∀ p : EuclideanSpace ℝ (Fin 2),
                                    p ∈ openSegment ℝ z (P.vertexPlacement v) →
                                      p ∈ openSegment ℝ (P.edgeArc old).vertices[j]
                                        (P.edgeArc old).vertices[j + 1] →
                                        ¬ ∃ c : ℝ,
                                          (P.edgeArc old).vertices[j + 1] -
                                              (P.edgeArc old).vertices[j] =
                                            c • (P.vertexPlacement v - z)) := by
-- BODY
  classical
  have _he_not_drawn : e ∉ drawn := he
  let E := EuclideanSpace ℝ (Fin 2)
  obtain ⟨u, v, huv, heuv⟩ : ∃ u v : V, G.Adj u v ∧ e.1 = Sym2.mk u v := by
    refine ⟨e.1.out.1, e.1.out.2, ?_, ?_⟩
    · have he_mem : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        simpa [Sym2.mk, e.1.out_eq] using SimpleGraph.mem_edgeFinset.mp e.2
      exact (SimpleGraph.mem_edgeSet (G := G)).mp he_mem
    · rw [Sym2.mk, e.1.out_eq]
  let a : E := P.vertexPlacement u
  let b : E := P.vertexPlacement v
  have hab : a ≠ b := by
    intro h
    exact huv.ne (P.vertexPlacement_injective h)
  let vertexPoints : Finset E := (Finset.univ : Finset V).image P.vertexPlacement
  let oldArcVertices : Finset E :=
    drawn.attach.biUnion (fun old : {f : G.edgeFinset // f ∈ drawn} =>
      (P.edgeArc old).vertices.toFinset)
  let points : Finset E := vertexPoints ∪ P.crossingSet ∪ oldArcVertices
  let oldSegments : Finset (E × E) :=
    drawn.attach.biUnion (fun old : {f : G.edgeFinset // f ∈ drawn} =>
      (Finset.univ : Finset (Fin ((P.edgeArc old).vertices.length - 1))).image
        (fun j =>
          ((P.edgeArc old).vertices[j.1]'(by omega),
            (P.edgeArc old).vertices[j.1 + 1]'(by omega))))
  have segment_endpoint_ne :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn}) ⦃j : ℕ⦄,
        (hj : j + 1 < (P.edgeArc old).vertices.length) →
          (P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj) ≠
            (P.edgeArc old).vertices[j + 1]'hj := by
    intro old j hj hEq
    have hi0 : j < (P.edgeArc old).vertices.length := by omega
    have hnodup := (P.edgeArc old).simple_vertices
    rw [List.nodup_iff_injective_getElem] at hnodup
    have hfin :
        (⟨j, hi0⟩ : Fin (P.edgeArc old).vertices.length) =
          ⟨j + 1, hj⟩ := by
      apply hnodup
      simpa using hEq
    have : j = j + 1 := congrArg Fin.val hfin
    omega
  have hseg : ∀ s ∈ oldSegments, s.1 ≠ s.2 := by
    intro s hs
    dsimp [oldSegments] at hs
    rw [Finset.mem_biUnion] at hs
    rcases hs with ⟨old, _holdmem, hs⟩
    rcases Finset.mem_image.mp hs with ⟨j, _hjmem, rfl⟩
    exact segment_endpoint_ne old (j := j.1) (by omega)
  let pointLineA : E → AffineSubspace ℝ E := fun p => affineSpan ℝ ({a, p} : Set E)
  let pointLineB : E → AffineSubspace ℝ E := fun p => affineSpan ℝ ({b, p} : Set E)
  let lines : Finset (AffineSubspace ℝ E) :=
    ((points.filter (fun p => p ≠ a)).image pointLineA) ∪
      ((points.filter (fun p => p ≠ b)).image pointLineB)
  have line_dim_test :
      ∀ (x y : E), x ≠ y →
        ((affineSpan ℝ ({x, y} : Set E) : Set E).Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ ({x, y} : Set E)).direction = 1) := by
    intro x y hxy
    constructor
    · exact ⟨x, left_mem_affineSpan_pair ℝ x y⟩
    · rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (sub_ne_zero.mpr hxy)
  have hline : ∀ ℓ ∈ lines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    dsimp [lines] at hℓ
    rw [Finset.mem_union] at hℓ
    rcases hℓ with hA | hB
    · rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
      have hpne : p ≠ a := by
        exact (Finset.mem_filter.mp hp).2
      exact line_dim_test a p hpne.symm
    · rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
      have hpne : p ≠ b := by
        exact (Finset.mem_filter.mp hp).2
      exact line_dim_test b p hpne.symm
  obtain ⟨z, hzpoints, hzlines, hzsupport, hzparallelA, hzparallelB, haz, hncol⟩ :=
    OrdinaryDrawingAuxiliaryBendPointAvoidance a b points oldSegments lines hab hseg hline
  have hLI_az_ab : LinearIndependent ℝ ![z - a, b - a] := by
    rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr haz.symm)]
    intro c hc
    exact hncol ⟨c, hc.symm⟩
  have hLI_za_zb : LinearIndependent ℝ ![a - z, b - z] := by
    rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr haz)]
    intro c hc
    apply hncol
    refine ⟨1 - c, ?_⟩
    calc
      b - a = (b - z) + (z - a) := by abel
      _ = c • (a - z) + (z - a) := by rw [← hc]
      _ = (1 - c) • (z - a) := by module
  have haz_inter :
      segment ℝ a z ∩ segment ℝ z b = ({z} : Set E) := by
    have h :=
      segment_inter_eq_endpoint_of_linearIndependent_sub
        (𝕜 := ℝ) (c := z) (x := a) (y := b) hLI_za_zb
    simpa [segment_symm, Set.inter_comm] using h
  have hzb : z ≠ b := by
    intro h
    apply hncol
    refine ⟨1, ?_⟩
    simp [h]
  have hb_not_open_az : b ∉ openSegment ℝ a z := by
    intro hb
    have hb_inter : b ∈ segment ℝ a z ∩ segment ℝ z b :=
      ⟨openSegment_subset_segment ℝ a z hb, right_mem_segment ℝ z b⟩
    have hbz : b ∈ ({z} : Set E) := by
      simpa [haz_inter] using hb_inter
    have hb_eq_z : b = z := by simpa using hbz
    exact hzb hb_eq_z.symm
  have ha_not_open_zb : a ∉ openSegment ℝ z b := by
    intro ha
    have ha_inter : a ∈ segment ℝ a z ∩ segment ℝ z b :=
      ⟨left_mem_segment ℝ a z, openSegment_subset_segment ℝ z b ha⟩
    have haz' : a ∈ ({z} : Set E) := by
      simpa [haz_inter] using ha_inter
    exact haz (by simpa using haz')
  let Γ : PolygonalArc :=
    { vertices := [a, z, b]
      length_ge_two := by norm_num
      source := a
      target := b
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := segment ℝ a z ∪ segment ℝ z b
      relativeInterior := (segment ℝ a z ∪ segment ℝ z b) \ ({a, b} : Set E)
      carrier_eq := by
        ext p
        constructor
        · intro hp
          rcases hp with hp | hp
          · refine ⟨0, by norm_num, ?_⟩
            simpa using hp
          · refine ⟨1, by norm_num, ?_⟩
            simpa using hp
        · rintro ⟨i, hi, hp⟩
          have hi' : i + 1 < 3 := by simpa using hi
          have hi_cases : i = 0 ∨ i = 1 := by omega
          rcases hi_cases with rfl | rfl
          · exact Or.inl (by simpa using hp)
          · exact Or.inr (by simpa using hp)
      relativeInterior_eq := rfl
      simple_vertices := by simp [haz, hzb, hab]
      segment_intersections := by
        intro i j hi hj hij
        have hi' : i + 1 < 3 := by simpa using hi
        have hj' : j + 1 < 3 := by simpa using hj
        have hi_cases : i = 0 ∨ i = 1 := by omega
        have hj_cases : j = 0 ∨ j = 1 := by omega
        rcases hi_cases with rfl | rfl <;> rcases hj_cases with rfl | rfl
        · omega
        · simp [haz_inter]
        · omega
        · omega
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hkine
        have hi' : i + 1 < 3 := by simpa using hi
        have hk' : k < 3 := by simpa using hk
        have hi_cases : i = 0 ∨ i = 1 := by omega
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hi_cases with rfl | rfl
        · rcases hk_cases with rfl | h
          · exact (hki rfl).elim
          · rcases h with rfl | rfl
            · exact (hkine rfl).elim
            · simpa using hb_not_open_az
        · rcases hk_cases with rfl | h
          · simpa using ha_not_open_zb
          · rcases h with rfl | rfl
            · exact (hki rfl).elim
            · exact (hkine rfl).elim }
  have segment_subset_line :
      ∀ (x y : E), segment ℝ x y ⊆ (affineSpan ℝ ({x, y} : Set E) : Set E) := by
    intro x y r hr
    rw [segment_eq_image_lineMap] at hr
    rcases hr with ⟨t, _ht, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t x y
  have point_mem_line_of_mem_segment_left :
      ∀ {p : E}, p ≠ a → p ∈ segment ℝ a z → z ∈ (pointLineA p : Set E) := by
    intro p hpa hpseg
    have hp_line : p ∈ (affineSpan ℝ ({a, z} : Set E) : Set E) :=
      segment_subset_line a z hpseg
    have hline_eq : affineSpan ℝ ({a, p} : Set E) = affineSpan ℝ ({a, z} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ a z) hp_line hpa.symm
    change z ∈ (affineSpan ℝ ({a, p} : Set E) : Set E)
    rw [hline_eq]
    exact right_mem_affineSpan_pair ℝ a z
  have point_mem_line_of_mem_segment_right :
      ∀ {p : E}, p ≠ b → p ∈ segment ℝ z b → z ∈ (pointLineB p : Set E) := by
    intro p hpb hpseg
    have hp_line : p ∈ (affineSpan ℝ ({z, b} : Set E) : Set E) :=
      segment_subset_line z b hpseg
    have hline_eq : affineSpan ℝ ({b, p} : Set E) = affineSpan ℝ ({z, b} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (right_mem_affineSpan_pair ℝ z b) hp_line hpb.symm
    change z ∈ (affineSpan ℝ ({b, p} : Set E) : Set E)
    rw [hline_eq]
    exact left_mem_affineSpan_pair ℝ z b
  have point_in_points_vertex :
      ∀ w : V, P.vertexPlacement w ∈ points := by
    intro w
    dsimp [points, vertexPoints]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    left
    exact Finset.mem_image.mpr ⟨w, by simp, rfl⟩
  have crossing_in_points :
      ∀ {p : E}, p ∈ P.crossingSet → p ∈ points := by
    intro p hp
    dsimp [points]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    exact Or.inr hp
  have old_arc_vertex_in_points :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn}) (k : ℕ)
        (hk : k < (P.edgeArc old).vertices.length),
          (P.edgeArc old).vertices[k] ∈ points := by
    intro old k hk
    dsimp [points, oldArcVertices]
    rw [Finset.mem_union]
    right
    rw [Finset.mem_biUnion]
    refine ⟨old, by simp, ?_⟩
    exact List.mem_toFinset.mpr (List.getElem_mem (l := (P.edgeArc old).vertices) hk)
  have no_point_rel :
      ∀ {p : E}, p ∈ points → p ∉ Γ.relativeInterior := by
    intro p hp hprel
    change p ∈ (segment ℝ a z ∪ segment ℝ z b) \ ({a, b} : Set E) at hprel
    rcases hprel.1 with hpaz | hpzb
    · have hpa : p ≠ a := by
        intro h
        exact hprel.2 (by simp [h])
      have hzline : z ∈ (pointLineA p : Set E) :=
        point_mem_line_of_mem_segment_left hpa hpaz
      have hlinemem : pointLineA p ∈ lines := by
        dsimp [lines]
        rw [Finset.mem_union]
        left
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpa⟩, rfl⟩
      exact hzlines (pointLineA p) hlinemem hzline
    · have hpb : p ≠ b := by
        intro h
        exact hprel.2 (by simp [h])
      have hzline : z ∈ (pointLineB p : Set E) :=
        point_mem_line_of_mem_segment_right hpb hpzb
      have hlinemem : pointLineB p ∈ lines := by
        dsimp [lines]
        rw [Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpb⟩, rfl⟩
      exact hzlines (pointLineB p) hlinemem hzline
  have old_segment_mem :
      ∀ (old : {f : G.edgeFinset // f ∈ drawn}) (j : ℕ)
        (hj : j + 1 < (P.edgeArc old).vertices.length),
          ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
            (P.edgeArc old).vertices[j + 1]'hj) ∈ oldSegments := by
    intro old j hj
    dsimp [oldSegments]
    rw [Finset.mem_biUnion]
    refine ⟨old, by simp, ?_⟩
    refine Finset.mem_image.mpr ?_
    let jj : Fin ((P.edgeArc old).vertices.length - 1) := ⟨j, by omega⟩
    refine ⟨jj, by simp, ?_⟩
    simp [jj]
  have no_overlap_left_all :
      ∀ s ∈ oldSegments,
        ¬ ∃ p q : E, p ≠ q ∧
          segment ℝ p q ⊆ segment ℝ a z ∩ segment ℝ s.1 s.2 := by
    intro s hs hoverlap
    rcases hoverlap with ⟨p, q, hpq, hsubset⟩
    have hp_az : p ∈ segment ℝ a z := (hsubset (left_mem_segment ℝ p q)).1
    have hq_az : q ∈ segment ℝ a z := (hsubset (right_mem_segment ℝ p q)).1
    have hp_s : p ∈ segment ℝ s.1 s.2 := (hsubset (left_mem_segment ℝ p q)).2
    have hq_s : q ∈ segment ℝ s.1 s.2 := (hsubset (right_mem_segment ℝ p q)).2
    have hp_az_line : p ∈ (affineSpan ℝ ({a, z} : Set E) : Set E) :=
      segment_subset_line a z hp_az
    have hq_az_line : q ∈ (affineSpan ℝ ({a, z} : Set E) : Set E) :=
      segment_subset_line a z hq_az
    have hp_s_line : p ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hp_s
    have hq_s_line : q ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hq_s
    have hline_eq_az :
        affineSpan ℝ ({p, q} : Set E) = affineSpan ℝ ({a, z} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_az_line hq_az_line hpq
    have hline_eq_s :
        affineSpan ℝ ({p, q} : Set E) = affineSpan ℝ ({s.1, s.2} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_s_line hq_s_line hpq
    have hz_support : z ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) := by
      rw [← hline_eq_s, hline_eq_az]
      exact right_mem_affineSpan_pair ℝ a z
    exact hzsupport s hs hz_support
  have no_overlap_right_all :
      ∀ s ∈ oldSegments,
        ¬ ∃ p q : E, p ≠ q ∧
          segment ℝ p q ⊆ segment ℝ z b ∩ segment ℝ s.1 s.2 := by
    intro s hs hoverlap
    rcases hoverlap with ⟨p, q, hpq, hsubset⟩
    have hp_zb : p ∈ segment ℝ z b := (hsubset (left_mem_segment ℝ p q)).1
    have hq_zb : q ∈ segment ℝ z b := (hsubset (right_mem_segment ℝ p q)).1
    have hp_s : p ∈ segment ℝ s.1 s.2 := (hsubset (left_mem_segment ℝ p q)).2
    have hq_s : q ∈ segment ℝ s.1 s.2 := (hsubset (right_mem_segment ℝ p q)).2
    have hp_zb_line : p ∈ (affineSpan ℝ ({z, b} : Set E) : Set E) :=
      segment_subset_line z b hp_zb
    have hq_zb_line : q ∈ (affineSpan ℝ ({z, b} : Set E) : Set E) :=
      segment_subset_line z b hq_zb
    have hp_s_line : p ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hp_s
    have hq_s_line : q ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hq_s
    have hline_eq_zb :
        affineSpan ℝ ({p, q} : Set E) = affineSpan ℝ ({z, b} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_zb_line hq_zb_line hpq
    have hline_eq_s :
        affineSpan ℝ ({p, q} : Set E) = affineSpan ℝ ({s.1, s.2} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_s_line hq_s_line hpq
    have hz_support : z ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) := by
      rw [← hline_eq_s, hline_eq_zb]
      exact left_mem_affineSpan_pair ℝ z b
    exact hzsupport s hs hz_support
  have smul_parallel_mem_line_left :
      ∀ {s : E × E}, (∃ c : ℝ, s.2 - s.1 = c • (z - a)) → s.1 ≠ s.2 →
        z ∈ (affineSpan ℝ ({a, a + (s.2 - s.1)} : Set E) : Set E) := by
    intro s hc hsne
    rcases hc with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hzero : s.2 - s.1 = 0 := by simpa [hc0] using hc
      exact hsne ((sub_eq_zero.mp hzero).symm)
    have hz_sub : z - a = c⁻¹ • (s.2 - s.1) := by
      calc
        z - a = c⁻¹ • (c • (z - a)) := by simp [hc_ne]
        _ = c⁻¹ • (s.2 - s.1) := by rw [hc]
    have hz_eq : z = a + c⁻¹ • (s.2 - s.1) := by
      calc
        z = a + (z - a) := by abel
        _ = a + c⁻¹ • (s.2 - s.1) := by rw [hz_sub]
    rw [hz_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := a) (p₂ := a + (s.2 - s.1)) (c⁻¹)
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  have smul_parallel_mem_line_right :
      ∀ {s : E × E}, (∃ c : ℝ, s.2 - s.1 = c • (b - z)) → s.1 ≠ s.2 →
        z ∈ (affineSpan ℝ ({b, b + (s.2 - s.1)} : Set E) : Set E) := by
    intro s hc hsne
    rcases hc with ⟨c, hc⟩
    have hc' : ∃ d : ℝ, s.2 - s.1 = d • (z - b) := by
      refine ⟨-c, ?_⟩
      calc
        s.2 - s.1 = c • (b - z) := hc
        _ = c • (-(z - b)) := by
          congr 1
          abel
        _ = (-c) • (z - b) := by rw [smul_neg, neg_smul]
    rcases hc' with ⟨d, hd⟩
    have hd_ne : d ≠ 0 := by
      intro hd0
      have hzero : s.2 - s.1 = 0 := by simpa [hd0] using hd
      exact hsne ((sub_eq_zero.mp hzero).symm)
    have hz_sub : z - b = d⁻¹ • (s.2 - s.1) := by
      calc
        z - b = d⁻¹ • (d • (z - b)) := by simp [hd_ne]
        _ = d⁻¹ • (s.2 - s.1) := by rw [hd]
    have hz_eq : z = b + d⁻¹ • (s.2 - s.1) := by
      calc
        z = b + (z - b) := by abel
        _ = b + d⁻¹ • (s.2 - s.1) := by rw [hz_sub]
    rw [hz_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := b) (p₂ := b + (s.2 - s.1)) (d⁻¹)
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  refine ⟨u, v, z, Γ, huv, heuv, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro w
    exact no_point_rel (point_in_points_vertex w)
  · intro p hp
    exact no_point_rel (crossing_in_points hp)
  · intro old k hk
    exact no_point_rel (old_arc_vertex_in_points old k hk)
  · intro old j hj hzseg
    let s : E × E :=
      ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
        (P.edgeArc old).vertices[j + 1]'hj)
    have hs : s ∈ oldSegments := old_segment_mem old j hj
    have hz_support : z ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) := by
      exact segment_subset_line s.1 s.2 (by simpa [s] using hzseg)
    exact hzsupport s hs hz_support
  · intro old j hj
    have hs := old_segment_mem old j hj
    simpa using no_overlap_left_all
      ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
        (P.edgeArc old).vertices[j + 1]'hj) hs
  · intro old j hj
    have hs := old_segment_mem old j hj
    simpa using no_overlap_right_all
      ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
        (P.edgeArc old).vertices[j + 1]'hj) hs
  · intro old j hj p hpnew hpold hparallel
    let s : E × E :=
      ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
        (P.edgeArc old).vertices[j + 1]'hj)
    have hs : s ∈ oldSegments := old_segment_mem old j hj
    have hsne : s.1 ≠ s.2 := hseg s hs
    have hmem : z ∈
        (affineSpan ℝ ({a, a + (s.2 - s.1)} : Set E) : Set E) :=
      smul_parallel_mem_line_left (s := s) (by
        rcases hparallel with ⟨c, hc⟩
        exact ⟨c, by simpa [s] using hc⟩) hsne
    exact hzparallelA s hs hmem
  · intro old j hj p hpnew hpold hparallel
    let s : E × E :=
      ((P.edgeArc old).vertices[j]'(Nat.lt_of_succ_lt hj),
        (P.edgeArc old).vertices[j + 1]'hj)
    have hs : s ∈ oldSegments := old_segment_mem old j hj
    have hsne : s.1 ≠ s.2 := hseg s hs
    have hmem : z ∈
        (affineSpan ℝ ({b, b + (s.2 - s.1)} : Set E) : Set E) :=
      smul_parallel_mem_line_right (s := s) (by
        rcases hparallel with ⟨c, hc⟩
        exact ⟨c, by simpa [s] using hc⟩) hsne
    exact hzparallelB s hs hmem
