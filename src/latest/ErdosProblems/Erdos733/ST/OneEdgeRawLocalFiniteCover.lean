import ErdosProblems.Erdos733.ST.ComplementComponentAbsorbsConnectedSubset

open Classical
noncomputable section

-- [TABLET NODE: OneEdgeRawLocalFiniteCover]
lemma OneEdgeRawLocalFiniteCover
    (A Csigma : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2)) (ra rb : ℝ)
    {ιA ιB : Type} [Fintype ιA] [Fintype ιB]
    (sectorA : ιA → Set (EuclideanSpace ℝ (Fin 2)))
    (sectorB : ιB → Set (EuclideanSpace ℝ (Fin 2)))
    (middleRect middleLeft middleRight : Set (EuclideanSpace ℝ (Fin 2)))
    (hCsigma : ComplementComponent A Csigma)
    (hsectorA_data :
      ∀ i, IsOpen (sectorA i) ∧ IsConnected (sectorA i) ∧
        sectorA i ⊆ Metric.ball a ra ∧
        sectorA i ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hsectorB_data :
      ∀ i, IsOpen (sectorB i) ∧ IsConnected (sectorB i) ∧
        sectorB i ⊆ Metric.ball b rb ∧
        sectorB i ⊆ (A ∪ segment ℝ b a)ᶜ)
    (hmiddleLeft_connected : IsConnected middleLeft)
    (hmiddleRight_connected : IsConnected middleRight)
    (hmiddleLeft_subset_compl : middleLeft ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hmiddleRight_subset_compl : middleRight ⊆ (A ∪ segment ℝ a b)ᶜ)
    (hmiddle_cover : middleRect \ segment ℝ a b ⊆ middleLeft ∪ middleRight)
    (hsectorA_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball a ra → x ∈ (A ∪ segment ℝ a b)ᶜ →
          ∃ i, x ∈ sectorA i)
    (hsectorB_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball b rb → x ∈ (A ∪ segment ℝ b a)ᶜ →
          ∃ i, x ∈ sectorB i)
    (hmiddleLeft_sectorA : ∃ i, (middleLeft ∩ sectorA i).Nonempty)
    (hmiddleRight_sectorA : ∃ i, (middleRight ∩ sectorA i).Nonempty)
    (hmiddleLeft_sectorB : ∃ i, (middleLeft ∩ sectorB i).Nonempty)
    (hmiddleRight_sectorB : ∃ i, (middleRight ∩ sectorB i).Nonempty) :
    ∃ rawPieces : Finset ((ιA ⊕ ιB) ⊕ Bool),
      ∃ piece : ((ιA ⊕ ιB) ⊕ Bool) → Set (EuclideanSpace ℝ (Fin 2)),
        (∀ i, piece (Sum.inl (Sum.inl i)) = sectorA i) ∧
          (∀ i, piece (Sum.inl (Sum.inr i)) = sectorB i) ∧
          piece (Sum.inr false) = middleLeft ∧
          piece (Sum.inr true) = middleRight ∧
          (∀ k, k ∈ rawPieces ↔ (Csigma ∩ piece k).Nonempty) ∧
          (∀ k ∈ rawPieces,
            (piece k).Nonempty ∧ IsConnected (piece k) ∧
              piece k ⊆ (A ∪ segment ℝ a b)ᶜ ∧ piece k ⊆ Csigma) ∧
          (∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) ∩
                Csigma →
              x ∉ segment ℝ a b →
              ∃ k ∈ rawPieces, x ∈ piece k) ∧
          (((Sum.inr false : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
              ((∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleLeft ∩ sectorA i).Nonempty) ∧
                (∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleLeft ∩ sectorB i).Nonempty))) ∧
            ((Sum.inr true : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
              ((∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleRight ∩ sectorA i).Nonempty) ∧
                (∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
                  (middleRight ∩ sectorB i).Nonempty)))) := by
-- BODY
  classical
  let piece : ((ιA ⊕ ιB) ⊕ Bool) → Set (EuclideanSpace ℝ (Fin 2)) := fun k =>
    match k with
    | Sum.inl (Sum.inl i) => sectorA i
    | Sum.inl (Sum.inr i) => sectorB i
    | Sum.inr false => middleLeft
    | Sum.inr true => middleRight
  let rawPieces : Finset ((ιA ⊕ ιB) ⊕ Bool) :=
    Finset.univ.filter (fun k => (Csigma ∩ piece k).Nonempty)
  have hraw_mem :
      ∀ k, k ∈ rawPieces ↔ (Csigma ∩ piece k).Nonempty := by
    intro k
    simp [rawPieces]
  have hpiece_core :
      ∀ k, IsConnected (piece k) ∧
        piece k ⊆ (A ∪ segment ℝ a b)ᶜ := by
    intro k
    cases k with
    | inl s =>
        cases s with
        | inl i =>
            exact ⟨(hsectorA_data i).2.1, (hsectorA_data i).2.2.2⟩
        | inr i =>
            refine ⟨(hsectorB_data i).2.1, ?_⟩
            intro x hx hxUnion
            exact (hsectorB_data i).2.2.2 hx (by
              simpa [segment_symm] using hxUnion)
    | inr flag =>
        cases flag
        · exact ⟨hmiddleLeft_connected, hmiddleLeft_subset_compl⟩
        · exact ⟨hmiddleRight_connected, hmiddleRight_subset_compl⟩
  have hpiece_retained :
      ∀ k ∈ rawPieces,
        (piece k).Nonempty ∧ IsConnected (piece k) ∧
          piece k ⊆ (A ∪ segment ℝ a b)ᶜ ∧ piece k ⊆ Csigma := by
    intro k hk
    have hmeet : (Csigma ∩ piece k).Nonempty := (hraw_mem k).mp hk
    have hne : (piece k).Nonempty := by
      rcases hmeet with ⟨x, _hxC, hxpiece⟩
      exact ⟨x, hxpiece⟩
    have hconn : IsConnected (piece k) := (hpiece_core k).1
    have hcompl : piece k ⊆ (A ∪ segment ℝ a b)ᶜ := (hpiece_core k).2
    have hAcompl : piece k ⊆ Aᶜ := by
      intro x hx hxA
      exact hcompl hx (Or.inl hxA)
    have hsubsetCsigma : piece k ⊆ Csigma :=
      ComplementComponentAbsorbsConnectedSubset A Csigma (piece k)
        hCsigma hne hAcompl hconn hmeet
    exact ⟨hne, hconn, hcompl, hsubsetCsigma⟩
  have hcover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) ∩ Csigma →
          x ∉ segment ℝ a b →
          ∃ k ∈ rawPieces, x ∈ piece k := by
    intro x hx hxnotseg
    have hxloc := hx.1
    have hxC := hx.2
    have hxcompl_ab : x ∈ (A ∪ segment ℝ a b)ᶜ := by
      intro hxUnion
      rcases hxUnion with hxA | hxseg
      · exact hCsigma.2.1 hxC hxA
      · exact hxnotseg hxseg
    rcases hxloc with hx_left | hxballB
    · rcases hx_left with hxballA | hxmiddle
      · rcases hsectorA_cover x hxballA hxcompl_ab with ⟨i, hxi⟩
        refine ⟨Sum.inl (Sum.inl i), ?_, ?_⟩
        · exact (hraw_mem _).mpr ⟨x, hxC, hxi⟩
        · exact hxi
      · have hxmiddle_minus : x ∈ middleRect \ segment ℝ a b :=
          ⟨hxmiddle, hxnotseg⟩
        rcases hmiddle_cover hxmiddle_minus with hxmid | hxmid
        · refine ⟨Sum.inr false, ?_, ?_⟩
          · exact (hraw_mem _).mpr ⟨x, hxC, hxmid⟩
          · exact hxmid
        · refine ⟨Sum.inr true, ?_, ?_⟩
          · exact (hraw_mem _).mpr ⟨x, hxC, hxmid⟩
          · exact hxmid
    · have hxcompl_ba : x ∈ (A ∪ segment ℝ b a)ᶜ := by
        simpa [segment_symm] using hxcompl_ab
      rcases hsectorB_cover x hxballB hxcompl_ba with ⟨i, hxi⟩
      refine ⟨Sum.inl (Sum.inr i), ?_, ?_⟩
      · exact (hraw_mem _).mpr ⟨x, hxC, hxi⟩
      · exact hxi
  have hleft_overlapA :
      (Sum.inr false : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
        ∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
          (middleLeft ∩ sectorA i).Nonempty := by
    intro hleft_mem
    have hleft_subset_Csigma :
        middleLeft ⊆ Csigma := by
      simpa [piece] using (hpiece_retained (Sum.inr false) hleft_mem).2.2.2
    rcases hmiddleLeft_sectorA with ⟨i, hmeet⟩
    have hsector_mem :
        (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces := by
      apply (hraw_mem _).mpr
      rcases hmeet with ⟨x, hxleft, hxsec⟩
      exact ⟨x, hleft_subset_Csigma hxleft, hxsec⟩
    exact ⟨i, hsector_mem, hmeet⟩
  have hleft_overlapB :
      (Sum.inr false : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
        ∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
          (middleLeft ∩ sectorB i).Nonempty := by
    intro hleft_mem
    have hleft_subset_Csigma :
        middleLeft ⊆ Csigma := by
      simpa [piece] using (hpiece_retained (Sum.inr false) hleft_mem).2.2.2
    rcases hmiddleLeft_sectorB with ⟨i, hmeet⟩
    have hsector_mem :
        (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces := by
      apply (hraw_mem _).mpr
      rcases hmeet with ⟨x, hxleft, hxsec⟩
      exact ⟨x, hleft_subset_Csigma hxleft, hxsec⟩
    exact ⟨i, hsector_mem, hmeet⟩
  have hright_overlapA :
      (Sum.inr true : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
        ∃ i, (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
          (middleRight ∩ sectorA i).Nonempty := by
    intro hright_mem
    have hright_subset_Csigma :
        middleRight ⊆ Csigma := by
      simpa [piece] using (hpiece_retained (Sum.inr true) hright_mem).2.2.2
    rcases hmiddleRight_sectorA with ⟨i, hmeet⟩
    have hsector_mem :
        (Sum.inl (Sum.inl i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces := by
      apply (hraw_mem _).mpr
      rcases hmeet with ⟨x, hxright, hxsec⟩
      exact ⟨x, hright_subset_Csigma hxright, hxsec⟩
    exact ⟨i, hsector_mem, hmeet⟩
  have hright_overlapB :
      (Sum.inr true : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces →
        ∃ i, (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces ∧
          (middleRight ∩ sectorB i).Nonempty := by
    intro hright_mem
    have hright_subset_Csigma :
        middleRight ⊆ Csigma := by
      simpa [piece] using (hpiece_retained (Sum.inr true) hright_mem).2.2.2
    rcases hmiddleRight_sectorB with ⟨i, hmeet⟩
    have hsector_mem :
        (Sum.inl (Sum.inr i) : ((ιA ⊕ ιB) ⊕ Bool)) ∈ rawPieces := by
      apply (hraw_mem _).mpr
      rcases hmeet with ⟨x, hxright, hxsec⟩
      exact ⟨x, hright_subset_Csigma hxright, hxsec⟩
    exact ⟨i, hsector_mem, hmeet⟩
  refine ⟨rawPieces, piece, ?_, ?_, ?_, ?_, hraw_mem, hpiece_retained,
    hcover, ?_⟩
  · intro i
    rfl
  · intro i
    rfl
  · rfl
  · rfl
  · exact ⟨fun hmem => ⟨hleft_overlapA hmem, hleft_overlapB hmem⟩,
      fun hmem => ⟨hright_overlapA hmem, hright_overlapB hmem⟩⟩
