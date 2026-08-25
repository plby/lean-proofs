import Util.IncidenceGeometry.FinitePointComplementBaseCase

open Classical
noncomputable section

lemma FiniteStraightLineComplexComplementComponents
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hNoVertexInEdgeInterior :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ V → v ∉ openSegment ℝ e.1 e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hOneEdge :
      ∀ (A : Set (EuclideanSpace ℝ (Fin 2)))
        (V0 : Finset (EuclideanSpace ℝ (Fin 2)))
        (E0 : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
        (a b : EuclideanSpace ℝ (Fin 2)),
        A =
          (V0 : Set (EuclideanSpace ℝ (Fin 2))) ∪
            ⋃ e : {e // e ∈ E0}, segment ℝ e.1.1 e.1.2 →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.1 ∈ V0) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.2 ∈ V0) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.1 ≠ e.2) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 →
            ∀ v : EuclideanSpace ℝ (Fin 2),
              v ∈ V0 → v ∉ openSegment ℝ e.1 e.2) →
        (∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → f ∈ E0 → e ≠ f →
            Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2)) →
        a ∈ V0 → b ∈ V0 → a ≠ b →
        Disjoint (openSegment ℝ a b) A →
        (∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
          (∀ C ∈ comps, ComplementComponent A C) ∧
            ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
              ComplementComponent A C → C ∈ comps) →
        ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
          (∀ C ∈ comps, ComplementComponent (A ∪ segment ℝ a b) C) ∧
            ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
              ComplementComponent (A ∪ segment ℝ a b) C → C ∈ comps) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps,
        ComplementComponent
          ((V : Set (EuclideanSpace ℝ (Fin 2))) ∪
            ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent
            ((V : Set (EuclideanSpace ℝ (Fin 2))) ∪
              ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) C →
            C ∈ comps := by
  classical
  let P := EuclideanSpace ℝ (Fin 2)
  let carrier : Finset (P × P) → Set P := fun F =>
    (V : Set P) ∪ ⋃ e : {e // e ∈ F}, segment ℝ e.1.1 e.1.2
  have main :
      ∀ F : Finset (P × P), F ⊆ E →
        ∃ comps : Finset (Set P),
          (∀ C ∈ comps, ComplementComponent (carrier F) C) ∧
            ∀ C : Set P, ComplementComponent (carrier F) C → C ∈ comps := by
    intro F
    refine Finset.induction_on F ?base ?step
    · intro _hFsub
      have hbase := FinitePointComplementBaseCase V
      refine ⟨{((V : Set P)ᶜ)}, ?_, ?_⟩
      · intro C hCmem
        have hCeq : C = (V : Set P)ᶜ := by
          simpa using Finset.mem_singleton.mp hCmem
        subst C
        simpa [carrier] using hbase.2.1
      · intro C hC
        have hCV : ComplementComponent (V : Set P) C := by
          simpa [carrier] using hC
        have hCeq : C = (V : Set P)ᶜ := hbase.2.2 C hCV
        simp [hCeq]
    · intro e F he_not ih hInsertSub
      have hFsub : F ⊆ E := by
        intro f hf
        exact hInsertSub (Finset.mem_insert_of_mem hf)
      have heE : e ∈ E := hInsertSub (Finset.mem_insert_self e F)
      let oldA : Set P := carrier F
      have hOldFinite :
          ∃ comps : Finset (Set P),
            (∀ C ∈ comps, ComplementComponent oldA C) ∧
              ∀ C : Set P, ComplementComponent oldA C → C ∈ comps := by
        simpa [oldA] using ih hFsub
      have hEdgeSourceF :
          ∀ f : P × P, f ∈ F → f.1 ∈ V := by
        intro f hf
        exact hEdgeSource f (hFsub hf)
      have hEdgeTargetF :
          ∀ f : P × P, f ∈ F → f.2 ∈ V := by
        intro f hf
        exact hEdgeTarget f (hFsub hf)
      have hEdgeNondegenerateF :
          ∀ f : P × P, f ∈ F → f.1 ≠ f.2 := by
        intro f hf
        exact hEdgeNondegenerate f (hFsub hf)
      have hNoVertexInEdgeInteriorF :
          ∀ f : P × P, f ∈ F → ∀ v : P,
            v ∈ V → v ∉ openSegment ℝ f.1 f.2 := by
        intro f hf v hv
        exact hNoVertexInEdgeInterior f (hFsub hf) v hv
      have hEdgeOpenInteriorsDisjointF :
          ∀ f g : P × P, f ∈ F → g ∈ F → f ≠ g →
            Disjoint (openSegment ℝ f.1 f.2) (openSegment ℝ g.1 g.2) := by
        intro f g hf hg hfg
        exact hEdgeOpenInteriorsDisjoint f g (hFsub hf) (hFsub hg) hfg
      have hNewInteriorDisjoint : Disjoint (openSegment ℝ e.1 e.2) oldA := by
        rw [Set.disjoint_left]
        intro x hx hxo
        dsimp [oldA, carrier] at hxo
        rcases hxo with hxV | hxEdges
        · exact hNoVertexInEdgeInterior e heE x hxV hx
        · rcases Set.mem_iUnion.mp hxEdges with ⟨f, hxfseg⟩
          rw [← insert_endpoints_openSegment (𝕜 := ℝ) f.1.1 f.1.2] at hxfseg
          rcases hxfseg with hxf_src | hxf_rest
          · subst x
            exact hNoVertexInEdgeInterior e heE f.1.1
              (hEdgeSource f.1 (hFsub f.2)) hx
          · rcases hxf_rest with hxf_tgt | hxf_open
            · subst x
              exact hNoVertexInEdgeInterior e heE f.1.2
                (hEdgeTarget f.1 (hFsub f.2)) hx
            · have hef : e ≠ f.1 := by
                intro hef
                exact he_not (by simp [hef, f.2])
              have hdis :=
                hEdgeOpenInteriorsDisjoint e f.1 heE (hFsub f.2) hef
              rw [Set.disjoint_left] at hdis
              exact hdis hx hxf_open
      have hStep :
          ∃ comps : Finset (Set P),
            (∀ C ∈ comps,
              ComplementComponent (oldA ∪ segment ℝ e.1 e.2) C) ∧
              ∀ C : Set P,
                ComplementComponent (oldA ∪ segment ℝ e.1 e.2) C →
                  C ∈ comps := by
        exact
          hOneEdge
            oldA V F e.1 e.2
            (by dsimp [oldA, carrier])
            hEdgeSourceF hEdgeTargetF hEdgeNondegenerateF
            hNoVertexInEdgeInteriorF hEdgeOpenInteriorsDisjointF
            (hEdgeSource e heE) (hEdgeTarget e heE)
            (hEdgeNondegenerate e heE) hNewInteriorDisjoint hOldFinite
      have hCarrierInsert :
          carrier (insert e F) = oldA ∪ segment ℝ e.1 e.2 := by
        ext x
        simp [carrier, oldA, Finset.mem_insert, Set.mem_iUnion, exists_prop,
          or_left_comm, or_comm]
      rcases hStep with ⟨comps, hComp, hCover⟩
      refine ⟨comps, ?_, ?_⟩
      · intro C hCmem
        simpa [hCarrierInsert] using hComp C hCmem
      · intro C hC
        exact hCover C (by simpa [hCarrierInsert] using hC)
  simpa [carrier, P] using main E (fun _ h => h)
