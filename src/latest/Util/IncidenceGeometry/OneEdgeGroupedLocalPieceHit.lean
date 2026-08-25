import Util.IncidenceGeometry.ComplementComponentAbsorbsConnectedSubset
import Util.IncidenceGeometry.PolygonalPathOrderedFirstHitPrefix
import Util.IncidenceGeometry.PolygonallyPathConnected

open Classical
noncomputable section

lemma OneEdgeGroupedLocalPieceHit
    (A Csigma C localUnion : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    {ι : Type*}
    (rawPieces : Finset ι)
    (piece : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (groupedLocalPieces : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (groupedLocalPieceOf : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hC : ComplementComponent (A ∪ segment ℝ a b) C)
    (hC_subset_Csigma : C ⊆ Csigma)
    (hCsigma_subset_old_compl : Csigma ⊆ Aᶜ)
    (hCsigma_path : PolygonallyPathConnected Csigma)
    (hOpenSegment_Csigma : openSegment ℝ a b ⊆ Csigma)
    (hLocalUnion_open : IsOpen localUnion)
    (hSegment_subset_localUnion : segment ℝ a b ⊆ localUnion)
    (hraw_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ localUnion ∩ Csigma →
          x ∉ segment ℝ a b →
            ∃ k ∈ rawPieces, x ∈ piece k)
    (hgroupedLocalPiece_mem :
      ∀ i, i ∈ rawPieces → groupedLocalPieceOf i ∈ groupedLocalPieces)
    (hrawPiece_subset_groupedLocalPiece :
      ∀ i, i ∈ rawPieces → piece i ⊆ groupedLocalPieceOf i) :
    ∃ G ∈ groupedLocalPieces, (C ∩ G).Nonempty := by
  classical
  rcases hC.1 with ⟨x, hxC⟩
  have hxCsigma : x ∈ Csigma := hC_subset_Csigma hxC
  let z : EuclideanSpace ℝ (Fin 2) := midpoint ℝ a b
  have hzOpen : z ∈ openSegment ℝ a b := by
    simpa [z] using midpoint_mem_openSegment (𝕜 := ℝ) a b
  have hzCsigma : z ∈ Csigma := hOpenSegment_Csigma hzOpen
  rcases hCsigma_path hxCsigma hzCsigma with
    ⟨γ, hγsource, hγtarget, hγcarrier_subset⟩
  have hsource_not : γ.source ∉ segment ℝ a b := by
    rw [hγsource]
    intro hxseg
    exact hC.2.1 hxC (Or.inr hxseg)
  have htarget_mem : γ.target ∈ segment ℝ a b := by
    rw [hγtarget]
    exact openSegment_subset_segment ℝ a b hzOpen
  rcases PolygonalPathOrderedFirstHitPrefix γ a b localUnion
      hLocalUnion_open hSegment_subset_localUnion hsource_not htarget_mem with
    ⟨y, P, hyCarrier, hyLocal, hyNotSegment, hP_connected,
      hsourceP, hyP, hP_subset⟩
  have hxP : x ∈ P := by
    simpa [hγsource] using hsourceP
  have hP_nonempty : P.Nonempty := ⟨x, hxP⟩
  have hP_subset_new_compl : P ⊆ (A ∪ segment ℝ a b)ᶜ := by
    intro w hw hAw
    have hw_info := hP_subset hw
    have hwCsigma : w ∈ Csigma := hγcarrier_subset hw_info.1
    rcases hAw with hwA | hwSegment
    · exact hCsigma_subset_old_compl hwCsigma hwA
    · exact hw_info.2 hwSegment
  have hC_meets_P : (C ∩ P).Nonempty := ⟨x, hxC, hxP⟩
  have hP_subset_C : P ⊆ C :=
    ComplementComponentAbsorbsConnectedSubset (A ∪ segment ℝ a b) C P
      hC hP_nonempty hP_subset_new_compl hP_connected hC_meets_P
  have hyC : y ∈ C := hP_subset_C hyP
  have hyCsigma : y ∈ Csigma := hC_subset_Csigma hyC
  rcases hraw_cover y ⟨hyLocal, hyCsigma⟩ hyNotSegment with
    ⟨k, hkraw, hyPiece⟩
  exact
    ⟨groupedLocalPieceOf k, hgroupedLocalPiece_mem k hkraw,
      ⟨y, hyC, hrawPiece_subset_groupedLocalPiece k hkraw hyPiece⟩⟩
