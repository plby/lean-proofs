import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.FinitePointLineAvoidance
import ErdosProblems.Erdos733.ST.PolygonalPathCarrierConnected
import ErdosProblems.Erdos733.ST.PolygonalPathConstant
import ErdosProblems.Erdos733.ST.PolygonalPathExtendSegment
import ErdosProblems.Erdos733.ST.PolygonalPathSegment
import ErdosProblems.Erdos733.ST.PolygonallyPathConnected

open Classical
noncomputable section

-- [TABLET NODE: FinitePointComplementBaseCase]
lemma FinitePointComplementBaseCase
    (V : Finset (EuclideanSpace ℝ (Fin 2))) :
    PolygonallyPathConnected ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) ∧
      ComplementComponent (V : Set (EuclideanSpace ℝ (Fin 2)))
        ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent (V : Set (EuclideanSpace ℝ (Fin 2))) C →
            C = ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  have polygonally_connected : PolygonallyPathConnected ((V : Set E)ᶜ) := by
    intro p q hp hq
    by_cases hpq : p = q
    · subst q
      rcases PolygonalPathConstant p with ⟨γ, hsrc, htgt, hcarrier⟩
      refine ⟨γ, hsrc, htgt, ?_⟩
      intro x hx
      rw [hcarrier] at hx
      exact hx ▸ hp
    · have line_dim_test :
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
          ∀ {a x r : E}, r ≠ a → r ∈ segment ℝ a x →
            x ∈ (affineSpan ℝ ({a, r} : Set E) : Set E) := by
        intro a x r hra hrseg
        have hr_line_ax : r ∈ (affineSpan ℝ ({a, x} : Set E) : Set E) :=
          segment_subset_line a x hrseg
        have hline_eq :
            affineSpan ℝ ({a, r} : Set E) = affineSpan ℝ ({a, x} : Set E) :=
          affineSpan_pair_eq_of_mem_of_mem_of_ne
            (left_mem_affineSpan_pair ℝ a x) hr_line_ax hra.symm
        rw [hline_eq]
        exact right_mem_affineSpan_pair ℝ a x
      have point_mem_line_of_mem_segment_right :
          ∀ {x a r : E}, r ≠ a → r ∈ segment ℝ x a →
            x ∈ (affineSpan ℝ ({a, r} : Set E) : Set E) := by
        intro x a r hra hrseg
        have hr_line_xa : r ∈ (affineSpan ℝ ({x, a} : Set E) : Set E) :=
          segment_subset_line x a hrseg
        have hline_eq :
            affineSpan ℝ ({a, r} : Set E) = affineSpan ℝ ({x, a} : Set E) :=
          affineSpan_pair_eq_of_mem_of_mem_of_ne
            (right_mem_affineSpan_pair ℝ x a) hr_line_xa hra.symm
        rw [hline_eq]
        exact left_mem_affineSpan_pair ℝ x a
      let pLine : E → AffineSubspace ℝ E := fun v => affineSpan ℝ ({p, v} : Set E)
      let qLine : E → AffineSubspace ℝ E := fun v => affineSpan ℝ ({q, v} : Set E)
      let pqLine : AffineSubspace ℝ E := affineSpan ℝ ({p, q} : Set E)
      let lines : Finset (AffineSubspace ℝ E) :=
        (V.image pLine) ∪ ((V.image qLine) ∪ {pqLine})
      have hline :
          ∀ ℓ ∈ lines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
        intro ℓ hℓ
        simp only [lines, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hℓ
        rcases hℓ with hℓ | hℓ
        · rcases hℓ with ⟨v, hv, rfl⟩
          have hpv : p ≠ v := by
            intro hpv
            exact hp (hpv ▸ hv)
          exact line_dim_test p v hpv
        · rcases hℓ with hℓ | hℓ
          · rcases hℓ with ⟨v, hv, rfl⟩
            have hqv : q ≠ v := by
              intro hqv
              exact hq (hqv ▸ hv)
            exact line_dim_test q v hqv
          · subst ℓ
            exact line_dim_test p q hpq
      have hWnonempty : (Set.univ : Set E).Nonempty := ⟨p, trivial⟩
      obtain ⟨z, _hzW, _hzV, hzlines⟩ :=
        FinitePointLineAvoidance (Set.univ : Set E) V lines isOpen_univ hWnonempty hline
      have hpz_segment : segment ℝ p z ⊆ ((V : Set E)ᶜ) := by
        intro x hxseg hxV
        have hxp : x ≠ p := by
          intro hxp
          exact hp (hxp ▸ hxV)
        have hz_pLine : z ∈ (pLine x : Set E) :=
          point_mem_line_of_mem_segment_left hxp hxseg
        have hpLine_mem : pLine x ∈ lines := by
          simp only [lines, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
          exact Or.inl ⟨x, hxV, rfl⟩
        exact hzlines (pLine x) hpLine_mem hz_pLine
      have hzq_segment : segment ℝ z q ⊆ ((V : Set E)ᶜ) := by
        intro x hxseg hxV
        have hxq : x ≠ q := by
          intro hxq
          exact hq (hxq ▸ hxV)
        have hz_qLine : z ∈ (qLine x : Set E) :=
          point_mem_line_of_mem_segment_right hxq hxseg
        have hqLine_mem : qLine x ∈ lines := by
          simp only [lines, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
          exact Or.inr (Or.inl ⟨x, hxV, rfl⟩)
        exact hzlines (qLine x) hqLine_mem hz_qLine
      rcases PolygonalPathSegment p z with ⟨γ, hγsrc, hγtgt, hγcarrier⟩
      have hγsub : γ.carrier ⊆ ((V : Set E)ᶜ) := by
        intro x hx
        exact hpz_segment (by simpa [hγcarrier] using hx)
      rcases PolygonalPathExtendSegment ((V : Set E)ᶜ) γ q hγsub (by
          intro x hx
          exact hzq_segment (by simpa [hγtgt] using hx)) with
        ⟨η, hηsrc, hηtgt, hηcarrier⟩
      exact ⟨η, hγsrc ▸ hηsrc, hηtgt, hηcarrier⟩
  have complement_nonempty : ((V : Set E)ᶜ).Nonempty := by
    have hWnonempty : (Set.univ : Set E).Nonempty := ⟨0, trivial⟩
    have hline_empty :
        ∀ ℓ ∈ (∅ : Finset (AffineSubspace ℝ E)),
          (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
      intro ℓ hℓ
      simp at hℓ
    obtain ⟨x, _hxW, hxV, _hxlines⟩ :=
      FinitePointLineAvoidance (Set.univ : Set E) V
        (∅ : Finset (AffineSubspace ℝ E)) isOpen_univ hWnonempty hline_empty
    exact ⟨x, hxV⟩
  have complement_preconnected : IsPreconnected ((V : Set E)ᶜ) := by
    intro U W hUopen hWopen hcover hUmeet hWmeet
    rcases hUmeet with ⟨p, hpcomp, hpU⟩
    rcases hWmeet with ⟨q, hqcomp, hqW⟩
    rcases polygonally_connected hpcomp hqcomp with ⟨γ, hγsource, hγtarget, hγcarrier⟩
    have hγconn : IsConnected γ.carrier := PolygonalPathCarrierConnected γ
    have hγcover : γ.carrier ⊆ U ∪ W := by
      intro x hx
      exact hcover (hγcarrier hx)
    have hsource_mem : γ.source ∈ γ.carrier := by
      rw [γ.carrier_eq]
      left
      exact Or.inl rfl
    have htarget_mem : γ.target ∈ γ.carrier := by
      rw [γ.carrier_eq]
      left
      exact Or.inr rfl
    have hγU : (γ.carrier ∩ U).Nonempty :=
      ⟨p, by simpa [hγsource] using hsource_mem, hpU⟩
    have hγW : (γ.carrier ∩ W).Nonempty :=
      ⟨q, by simpa [hγtarget] using htarget_mem, hqW⟩
    rcases hγconn.2 U W hUopen hWopen hγcover hγU hγW with
      ⟨x, hxγ, hxUW⟩
    exact ⟨x, hγcarrier hxγ, hxUW⟩
  have complement_connected : IsConnected ((V : Set E)ᶜ) :=
    ⟨complement_nonempty, complement_preconnected⟩
  have self_component :
      ComplementComponent (V : Set E) ((V : Set E)ᶜ) := by
    refine ⟨complement_nonempty, ?_, complement_connected, ?_⟩
    · intro x hx
      exact hx
    · intro C _hCne hCsub _hCconn _hcontains
      exact hCsub
  have component_unique :
      ∀ C : Set E, ComplementComponent (V : Set E) C → C = ((V : Set E)ᶜ) := by
    intro C hC
    rcases hC with ⟨_hCne, hCsub, _hCconn, hCmax⟩
    apply le_antisymm
    · exact hCsub
    · exact hCmax ((V : Set E)ᶜ) complement_nonempty (by intro x hx; exact hx)
        complement_connected hCsub
  exact ⟨polygonally_connected, self_component, component_unique⟩
