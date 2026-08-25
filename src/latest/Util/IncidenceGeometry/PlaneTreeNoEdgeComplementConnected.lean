import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.PolygonalPathConstant
import Util.IncidenceGeometry.PolygonalPathExtendSegment
import Util.IncidenceGeometry.PolygonalPathSegment
import Util.IncidenceGeometry.PolygonallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

lemma PlaneTreeNoEdgeComplementConnected {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (hTree : G.IsTree) (hNoEdges : G.edgeSet = ∅) :
    PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have hEdgeFinsetEmpty : G.edgeFinset = ∅ := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, hNoEdges]
    simp
  have hEdgeCard : G.edgeFinset.card = 0 := by
    simp [hEdgeFinsetEmpty]
  have hVcard : Fintype.card V = 1 := by
    have hcard := hTree.card_edgeFinset
    omega
  obtain ⟨v0, hv0⟩ := Fintype.card_eq_one_iff.mp hVcard
  let a : E := D.vertexPlacement v0
  have hRange : Set.range D.vertexPlacement = ({a} : Set E) := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      have hv : v = v0 := hv0 v
      simp [a, hv]
    · intro hy
      rcases hy with rfl
      exact ⟨v0, rfl⟩
  have hEdgesUnion : (⋃ e : G.edgeFinset, (D.edgeArc e).carrier) = (∅ : Set E) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨e, _hye⟩
    have he : (e : Sym2 V) ∈ G.edgeSet := by
      exact (SimpleGraph.mem_edgeFinset).mp e.2
    rw [hNoEdges] at he
    simp at he
  have hImage : OrdinaryDrawingImage G D = ({a} : Set E) := by
    simp [OrdinaryDrawingImage, hRange, hEdgesUnion]
  have singleton_connected : PolygonallyPathConnected (({a} : Set E)ᶜ) := by
    intro p q hp hq
    by_cases hpq : p = q
    · subst q
      rcases PolygonalPathConstant p with ⟨γ, hsrc, htgt, hcarrier⟩
      refine ⟨γ, hsrc, htgt, ?_⟩
      intro x hx
      rw [hcarrier] at hx
      exact hx ▸ hp
    · by_cases hseg_a : a ∈ segment ℝ p q
      · have hpa : p ≠ a := by
          intro h
          exact hp (by simp [h])
        have hqa : q ≠ a := by
          intro h
          exact hq (by simp [h])
        have line_dim_test :
            ∀ (u v : E), u ≠ v →
              ((affineSpan ℝ ({u, v} : Set E) : Set E).Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ ({u, v} : Set E)).direction = 1) := by
          intro u v huv
          constructor
          · exact ⟨u, left_mem_affineSpan_pair ℝ u v⟩
          · rw [direction_affineSpan, vectorSpan_pair]
            exact finrank_span_singleton (sub_ne_zero.mpr huv)
        have segment_subset_line :
            ∀ (u v : E), segment ℝ u v ⊆ (affineSpan ℝ ({u, v} : Set E) : Set E) := by
          intro u v x hx
          rw [segment_eq_image_lineMap] at hx
          rcases hx with ⟨t, _ht, rfl⟩
          exact AffineMap.lineMap_mem_affineSpan_pair t u v
        have point_mem_line_of_mem_segment_left :
            ∀ {u x r : E}, r ≠ u → r ∈ segment ℝ u x →
              x ∈ (affineSpan ℝ ({u, r} : Set E) : Set E) := by
          intro u x r hru hrseg
          have hr_line_ux : r ∈ (affineSpan ℝ ({u, x} : Set E) : Set E) :=
            segment_subset_line u x hrseg
          have hline_eq :
              affineSpan ℝ ({u, r} : Set E) = affineSpan ℝ ({u, x} : Set E) :=
            affineSpan_pair_eq_of_mem_of_mem_of_ne
              (left_mem_affineSpan_pair ℝ u x) hr_line_ux hru.symm
          rw [hline_eq]
          exact right_mem_affineSpan_pair ℝ u x
        have point_mem_line_of_mem_segment_right :
            ∀ {x u r : E}, r ≠ u → r ∈ segment ℝ x u →
              x ∈ (affineSpan ℝ ({u, r} : Set E) : Set E) := by
          intro x u r hru hrseg
          have hr_line_xu : r ∈ (affineSpan ℝ ({x, u} : Set E) : Set E) :=
            segment_subset_line x u hrseg
          have hline_eq :
              affineSpan ℝ ({u, r} : Set E) = affineSpan ℝ ({x, u} : Set E) :=
            affineSpan_pair_eq_of_mem_of_mem_of_ne
              (right_mem_affineSpan_pair ℝ x u) hr_line_xu hru.symm
          rw [hline_eq]
          exact left_mem_affineSpan_pair ℝ x u
        let pLine : AffineSubspace ℝ E := affineSpan ℝ ({p, a} : Set E)
        let qLine : AffineSubspace ℝ E := affineSpan ℝ ({q, a} : Set E)
        let lines : Finset (AffineSubspace ℝ E) := {pLine, qLine}
        have hline :
            ∀ ℓ ∈ lines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
          intro ℓ hℓ
          simp only [lines, Finset.mem_insert, Finset.mem_singleton] at hℓ
          rcases hℓ with rfl | rfl
          · exact line_dim_test p a hpa
          · exact line_dim_test q a hqa
        have hWnonempty : (Set.univ : Set E).Nonempty := ⟨p, trivial⟩
        obtain ⟨z, _hzW, _hzPoints, hzlines⟩ :=
          FinitePointLineAvoidance (Set.univ : Set E) (∅ : Finset E) lines
            isOpen_univ hWnonempty hline
        have hpz_segment : segment ℝ p z ⊆ (({a} : Set E)ᶜ) := by
          intro x hxseg hxsing
          have hxa : x = a := by simpa using hxsing
          subst x
          have hz_pLine : z ∈ (pLine : Set E) :=
            point_mem_line_of_mem_segment_left hpa.symm hxseg
          have hpLine_mem : pLine ∈ lines := by simp [lines]
          exact hzlines pLine hpLine_mem hz_pLine
        have hzq_segment : segment ℝ z q ⊆ (({a} : Set E)ᶜ) := by
          intro x hxseg hxsing
          have hxa : x = a := by simpa using hxsing
          subst x
          have hz_qLine : z ∈ (qLine : Set E) :=
            point_mem_line_of_mem_segment_right hqa.symm hxseg
          have hqLine_mem : qLine ∈ lines := by simp [lines]
          exact hzlines qLine hqLine_mem hz_qLine
        rcases PolygonalPathSegment p z with ⟨γ, hγsrc, hγtgt, hγcarrier⟩
        have hγsub : γ.carrier ⊆ (({a} : Set E)ᶜ) := by
          intro x hx
          exact hpz_segment (by simpa [hγcarrier] using hx)
        rcases PolygonalPathExtendSegment (({a} : Set E)ᶜ) γ q hγsub (by
            intro x hx
            exact hzq_segment (by simpa [hγtgt] using hx)) with
          ⟨η, hηsrc, hηtgt, hηcarrier⟩
        exact ⟨η, hγsrc ▸ hηsrc, hηtgt, hηcarrier⟩
      · rcases PolygonalPathSegment p q with ⟨γ, hγsrc, hγtgt, hγcarrier⟩
        refine ⟨γ, hγsrc, hγtgt, ?_⟩
        intro x hx hxsing
        have hxa : x = a := by simpa using hxsing
        subst x
        exact hseg_a (by simpa [hγcarrier] using hx)
  simpa [hImage] using singleton_connected
