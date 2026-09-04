import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.ComplementComponentAbsorbsConnectedSubset
import Util.IncidenceGeometry.ComplementComponentDisjointUnionRight
import Util.IncidenceGeometry.ComplementComponentsFiniteHitFamily
import Util.IncidenceGeometry.ConnectedSubsetContainedInUniqueComplementComponent
import Util.IncidenceGeometry.FinitePointComplementBaseCase
import Util.IncidenceGeometry.FinitePolygonalSetElementaryComplexExists
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.FiniteStraightLineComplexComplementComponents
import Util.IncidenceGeometry.FiniteStraightLineComplexOneEdgeComplementComponents
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma FinitePolygonalSetComplementComponents (K : FinitePolygonalSet) :
    ∃ Face : Type, ∃ _ : Fintype Face,
      ∃ faceSet : Face → Set (EuclideanSpace ℝ (Fin 2)),
        (∀ F : Face, ComplementComponent K.carrier (faceSet F)) ∧
          (∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent K.carrier C → ∃! F : Face, faceSet F = C) ∧
          (∀ p : EuclideanSpace ℝ (Fin 2),
            p ∈ K.carrierᶜ → ∃! F : Face, p ∈ faceSet F) := by
  have point_component_unique :
      ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.carrierᶜ →
        ∃! C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent K.carrier C ∧ p ∈ C := by
    intro p hp
    simpa [Set.singleton_subset_iff] using
      (ConnectedSubsetContainedInUniqueComplementComponent
        K.carrier ({p} : Set (EuclideanSpace ℝ (Fin 2)))
        (Set.singleton_nonempty p)
        (by
          intro x hx
          simpa [Set.mem_singleton_iff.mp hx] using hp)
        (by
          simpa using
            (isConnected_singleton :
              IsConnected ({p} : Set (EuclideanSpace ℝ (Fin 2))))))
  have components_eq_of_mem :
      ∀ C D : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent K.carrier C →
          ComplementComponent K.carrier D →
            ∀ x, x ∈ C → x ∈ D → C = D := by
    intro C D hC hD x hxC hxD
    have hxK : x ∈ K.carrierᶜ := hC.2.1 hxC
    exact
      ExistsUnique.unique (point_component_unique x hxK)
        ⟨hC, hxC⟩ ⟨hD, hxD⟩
  have components_disjoint_or_equal :
      ∀ C D : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent K.carrier C →
          ComplementComponent K.carrier D →
            C ∩ D = ∅ ∨ C = D := by
    intro C D hC hD
    by_cases hmeet : (C ∩ D).Nonempty
    · rcases hmeet with ⟨x, hx⟩
      exact Or.inr (components_eq_of_mem C D hC hD x hx.1 hx.2)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hmeet)
  have finite_point_base_case := FinitePointComplementBaseCase K.points
  have finite_point_base_connected := finite_point_base_case.1
  have finite_point_base_component := finite_point_base_case.2.1
  have finite_point_base_unique := finite_point_base_case.2.2
  have unchanged_old_component_step :
      ∀ A B C : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent A C → Disjoint C B →
          ComplementComponent (A ∪ B) C := by
    intro A B C hC hCB
    exact ComplementComponentDisjointUnionRight A B C hC hCB
  have local_piece_absorption :
      ∀ C T : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent K.carrier C →
          T.Nonempty → T ⊆ K.carrierᶜ → IsConnected T →
            (C ∩ T).Nonempty → T ⊆ C := by
    intro C T hC hTne hTK hTconn hmeet
    exact
      ComplementComponentAbsorbsConnectedSubset
        K.carrier C T hC hTne hTK hTconn hmeet
  have finite_components_from_local_hit_family :
      ∀ {ι : Type} [Fintype ι]
        (P : ι → Set (EuclideanSpace ℝ (Fin 2))),
          (∀ i, (P i).Nonempty) →
            (∀ i, P i ⊆ K.carrierᶜ) →
              (∀ i, IsConnected (P i)) →
                (∀ C : Set (EuclideanSpace ℝ (Fin 2)),
                  ComplementComponent K.carrier C →
                    ∃ i, (C ∩ P i).Nonempty) →
                  ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
                    (∀ C ∈ comps, ComplementComponent K.carrier C) ∧
                      ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
                        ComplementComponent K.carrier C → C ∈ comps := by
    intro ι _inst P hPne hPsub hPconn hhit
    exact
      ComplementComponentsFiniteHitFamily K.carrier P
        hPne hPsub hPconn hhit
  have elementary_complex_exists :
      Nonempty (FinitePolygonalSetElementaryComplex K) :=
    FinitePolygonalSetElementaryComplexExists K
  rcases elementary_complex_exists with ⟨elementary_complex⟩
  have finite_elementary_complex_components :
      ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
        (∀ C ∈ comps,
          ComplementComponent
            ((elementary_complex.vertices :
                Set (EuclideanSpace ℝ (Fin 2))) ∪
              ⋃ e : {e // e ∈ elementary_complex.edges},
                segment ℝ e.1.1 e.1.2) C) ∧
          ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent
              ((elementary_complex.vertices :
                  Set (EuclideanSpace ℝ (Fin 2))) ∪
                ⋃ e : {e // e ∈ elementary_complex.edges},
                  segment ℝ e.1.1 e.1.2) C →
              C ∈ comps :=
    FiniteStraightLineComplexComplementComponents
      elementary_complex.vertices elementary_complex.edges
      elementary_complex.edge_source_mem
      elementary_complex.edge_target_mem
      elementary_complex.edge_nondegenerate
      elementary_complex.no_vertex_in_edge_interior
      elementary_complex.edge_open_interiors_disjoint
      FiniteStraightLineComplexOneEdgeComplementComponents
  have finite_carrier_components :
      ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
        (∀ C ∈ comps, ComplementComponent K.carrier C) ∧
          ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent K.carrier C → C ∈ comps := by
    simpa [elementary_complex.carrier_eq] using finite_elementary_complex_components
  have one_edge_update_step := FiniteStraightLineComplexOneEdgeComplementComponents
  rcases finite_carrier_components with ⟨comps, hcomp_mem, hcomp_cover⟩
  let Face : Type := {C : Set (EuclideanSpace ℝ (Fin 2)) // C ∈ comps}
  let faceSet : Face → Set (EuclideanSpace ℝ (Fin 2)) := fun F => F.1
  have : Fintype Face := by
    dsimp [Face]
    infer_instance
  refine ⟨Face, inferInstance, faceSet, ?_, ?_, ?_⟩
  · intro F
    simpa [faceSet] using hcomp_mem F.1 F.2
  · intro C hC
    refine ⟨⟨C, hcomp_cover C hC⟩, ?_, ?_⟩
    · simp [faceSet]
    · intro F hF
      apply Subtype.ext
      simpa [faceSet] using hF
  · intro p hp
    rcases ExistsUnique.exists (point_component_unique p hp) with
      ⟨C, hCcomp, hpC⟩
    refine ⟨⟨C, hcomp_cover C hCcomp⟩, ?_, ?_⟩
    · simpa [faceSet] using hpC
    · intro F hpF
      apply Subtype.ext
      exact
        ExistsUnique.unique (point_component_unique p hp)
          ⟨hcomp_mem F.1 F.2, by simpa [faceSet] using hpF⟩
          ⟨hCcomp, hpC⟩
