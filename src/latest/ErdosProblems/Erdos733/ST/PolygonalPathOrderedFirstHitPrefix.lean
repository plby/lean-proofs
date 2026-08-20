import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.StraightSegmentFirstHitPrefix

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathOrderedFirstHitPrefix]
lemma PolygonalPathOrderedFirstHitPrefix
    (γ : PolygonalPath)
    (a b : EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : IsOpen U)
    (hsegment_subset_U : segment ℝ a b ⊆ U)
    (hsource_not : γ.source ∉ segment ℝ a b)
    (htarget_mem : γ.target ∈ segment ℝ a b) :
    ∃ (y : EuclideanSpace ℝ (Fin 2)) (P : Set (EuclideanSpace ℝ (Fin 2))),
      y ∈ γ.carrier ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
        IsConnected P ∧ γ.source ∈ P ∧ y ∈ P ∧
          P ⊆ γ.carrier ∩ (segment ℝ a b)ᶜ := by
-- BODY
  let S : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ a b
  let Carrier :=
    fun (xs : List (EuclideanSpace ℝ (Fin 2)))
        (source target : EuclideanSpace ℝ (Fin 2)) =>
      (({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p : EuclideanSpace ℝ (Fin 2) |
          ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
            p ∈ segment ℝ xs[i] xs[i + 1]})
  have list_first :
      ∀ (xs : List (EuclideanSpace ℝ (Fin 2)))
        (source target : EuclideanSpace ℝ (Fin 2)),
        xs ≠ [] →
          xs.head? = some source →
            xs.getLast? = some target →
              source ∉ S →
                target ∈ S →
                  ∃ (y : EuclideanSpace ℝ (Fin 2))
                    (P : Set (EuclideanSpace ℝ (Fin 2))),
                    y ∈ Carrier xs source target ∧ y ∈ U ∧ y ∉ S ∧
                      IsConnected P ∧ source ∈ P ∧ y ∈ P ∧
                        P ⊆ Carrier xs source target ∩ Sᶜ := by
    intro xs
    induction xs with
    | nil =>
        intro source target hne _ _ _ _
        exact False.elim (hne rfl)
    | cons x xs ih =>
        intro source target _hne hhead hlast hsource_not htarget_mem
        cases xs with
        | nil =>
            simp at hhead hlast
            subst source
            subst target
            exact False.elim (hsource_not htarget_mem)
        | cons x' rest =>
            simp at hhead
            subst source
            let tailSet : Set (EuclideanSpace ℝ (Fin 2)) :=
              Carrier (x' :: rest) x' target
            let fullSet : Set (EuclideanSpace ℝ (Fin 2)) :=
              Carrier (x :: x' :: rest) x target
            have htail_ne : (x' :: rest) ≠ [] := by simp
            have htail_head : (x' :: rest).head? = some x' := by simp
            have htail_last : (x' :: rest).getLast? = some target := by
              simpa using hlast
            have hfirst_subset_full : segment ℝ x x' ⊆ fullSet := by
              intro p hp
              right
              refine ⟨0, ?_, ?_⟩
              · simp
              · simpa [fullSet, Carrier] using hp
            have htail_subset_full : tailSet ⊆ fullSet := by
              intro p hp
              change p ∈ Carrier (x' :: rest) x' target at hp
              change p ∈ Carrier (x :: x' :: rest) x target
              rcases hp with hpEnd | hpSeg
              · rcases hpEnd with hpx' | hpt
                · right
                  refine ⟨0, ?_, ?_⟩
                  · simp
                  · simpa [hpx'] using right_mem_segment ℝ x x'
                · left
                  exact Or.inr hpt
              · rcases hpSeg with ⟨j, hj, hpj⟩
                right
                refine ⟨j + 1, ?_, ?_⟩
                · simpa using hj
                · simpa using hpj
            by_cases hhit : (segment ℝ x x' ∩ S).Nonempty
            · rcases StraightSegmentFirstHitPrefix a b x x' U hUopen
                  hsegment_subset_U (by simpa [S] using hsource_not)
                  (by simpa [S] using hhit) with
                ⟨y, hyxx', hyU, hyNotS, hPconn, hxP, hyP, hPsub⟩
              refine
                ⟨y, segment ℝ x y, ?_, hyU, by simpa [S] using hyNotS,
                  hPconn, hxP, hyP, ?_⟩
              · exact hfirst_subset_full hyxx'
              · intro p hp
                have hp' := hPsub hp
                exact ⟨hfirst_subset_full hp'.1, by simpa [S] using hp'.2⟩
            · have hx'_not : x' ∉ S := by
                intro hx'S
                exact hhit ⟨x', right_mem_segment ℝ x x', hx'S⟩
              rcases ih x' target htail_ne htail_head htail_last hx'_not htarget_mem with
                ⟨y, P, hyTail, hyU, hyNotS, hPconn, hx'P, hyP, hPsubTail⟩
              have hsegNoS : segment ℝ x x' ⊆ Sᶜ := by
                intro p hp hpS
                exact hhit ⟨p, hp, hpS⟩
              refine
                ⟨y, segment ℝ x x' ∪ P, ?_, hyU, hyNotS, ?_,
                  Or.inl (left_mem_segment ℝ x x'), Or.inr hyP, ?_⟩
              · exact htail_subset_full hyTail
              · have hsegConn : IsConnected (segment ℝ x x') :=
                  (convex_segment x x').isConnected
                    ⟨x, left_mem_segment ℝ x x'⟩
                have hmeet : (segment ℝ x x' ∩ P).Nonempty :=
                  ⟨x', right_mem_segment ℝ x x', hx'P⟩
                exact hsegConn.union hmeet hPconn
              · intro p hp
                rcases hp with hpseg | hpP
                · exact ⟨hfirst_subset_full hpseg, hsegNoS hpseg⟩
                · have hpTail := hPsubTail hpP
                  exact ⟨htail_subset_full hpTail.1, hpTail.2⟩
  rcases
      list_first γ.vertices γ.source γ.target γ.vertices_nonempty
        γ.source_eq_head γ.target_eq_last
        (by simpa [S] using hsource_not)
        (by simpa [S] using htarget_mem) with
    ⟨y, P, hyCarrierExpr, hyU, hyNotS, hPconn, hsrcP, hyP, hPsubExpr⟩
  refine
    ⟨y, P, ?_, hyU, by simpa [S] using hyNotS, hPconn, hsrcP, hyP, ?_⟩
  · rw [γ.carrier_eq]
    exact hyCarrierExpr
  · intro p hp
    have hpExpr := hPsubExpr hp
    constructor
    · rw [γ.carrier_eq]
      exact hpExpr.1
    · simpa [S] using hpExpr.2

