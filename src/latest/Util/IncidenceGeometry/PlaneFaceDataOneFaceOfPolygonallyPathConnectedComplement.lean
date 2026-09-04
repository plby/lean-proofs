import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.PolygonallyPathConnected
import Util.IncidenceGeometry.PolygonalPathCarrierConnected

open Classical
noncomputable section

lemma PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement {V : Type*}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneFaceData G D) :
    PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) →
      ((OrdinaryDrawingImage G D)ᶜ).Nonempty →
        @Fintype.card A.Face A.faceFintype = 1 := by
  intro hPathConnected hNonempty
  have hPreconnected : IsPreconnected ((OrdinaryDrawingImage G D)ᶜ) := by
    intro U W hUopen hWopen hcover hUmeet hWmeet
    rcases hUmeet with ⟨p, hpCompl, hpU⟩
    rcases hWmeet with ⟨q, hqCompl, hqW⟩
    rcases hPathConnected hpCompl hqCompl with
      ⟨γ, hγsource, hγtarget, hγcarrier⟩
    have hγconn : IsConnected γ.carrier := PolygonalPathCarrierConnected γ
    have hγcover : γ.carrier ⊆ U ∪ W := by
      intro x hx
      exact hcover (hγcarrier hx)
    have hsource_mem : γ.source ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact Or.inl (Or.inl rfl)
    have htarget_mem : γ.target ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact Or.inl (Or.inr rfl)
    have hγU : (γ.carrier ∩ U).Nonempty :=
      ⟨p, by simpa [hγsource] using hsource_mem, hpU⟩
    have hγW : (γ.carrier ∩ W).Nonempty :=
      ⟨q, by simpa [hγtarget] using htarget_mem, hqW⟩
    rcases hγconn.2 U W hUopen hWopen hγcover hγU hγW with
      ⟨x, hxγ, hxUW⟩
    exact ⟨x, hγcarrier hxγ, hxUW⟩
  have hConnected : IsConnected ((OrdinaryDrawingImage G D)ᶜ) :=
    ⟨hNonempty, hPreconnected⟩
  have hFaceFull :
      ∀ F : A.Face, A.faceSet F = (OrdinaryDrawingImage G D)ᶜ := by
    intro F
    have hComp :
        ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
      simpa [DrawingFaceComponent] using A.face_component F
    rcases hComp with ⟨_hFaceNonempty, hFaceSubset, _hFaceConnected, hMaximal⟩
    apply Set.Subset.antisymm
    · exact hFaceSubset
    · exact hMaximal ((OrdinaryDrawingImage G D)ᶜ) hNonempty
        (by intro x hx; exact hx) hConnected hFaceSubset
  rcases hNonempty with ⟨p, hpCompl⟩
  rcases A.complement_point_face p hpCompl with ⟨F₀, _hpF₀, hUnique⟩
  have hAllEq : ∀ F : A.Face, F = F₀ := by
    intro F
    have hpF : p ∈ A.faceSet F := by
      simpa [hFaceFull F] using hpCompl
    exact hUnique F hpF
  let : Fintype A.Face := A.faceFintype
  have : Unique A.Face := { default := F₀, uniq := hAllEq }
  simp
