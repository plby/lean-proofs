import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathCarrierConnected (γ : PolygonalPath) : IsConnected γ.carrier := by
  let E := EuclideanSpace ℝ (Fin 2)
  have listChain_connected :
      ∀ (xs : List E) (source target : E),
        xs ≠ [] →
          xs.head? = some source →
            xs.getLast? = some target →
              IsConnected (({source, target} : Set E) ∪
                {p : E | ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                  p ∈ segment ℝ xs[i] xs[i + 1]}) := by
    intro xs
    induction xs with
    | nil =>
        intro source target hne _hhead _hlast
        exact False.elim (hne rfl)
    | cons a xs ih =>
        intro source target _hne hhead hlast
        cases xs with
        | nil =>
            simp at hhead hlast
            subst source
            subst target
            simpa using (isConnected_singleton : IsConnected ({a} : Set E))
        | cons b rest =>
            have hsource : a = source := Option.some.inj hhead
            subst source
            have htail_ne : (b :: rest) ≠ [] := by simp
            have htail_head : (b :: rest).head? = some b := by simp
            have htail_last : (b :: rest).getLast? = some target := by
              simpa using hlast
            have htail_conn := ih b target htail_ne htail_head htail_last
            let tailSet : Set E :=
              ({b, target} : Set E) ∪
                {p : E | ∃ i : ℕ, ∃ hi : i + 1 < (b :: rest).length,
                  p ∈ segment ℝ (b :: rest)[i] (b :: rest)[i + 1]}
            have hseg_conn : IsConnected (segment ℝ a b) :=
              (convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩
            have hmeet : (segment ℝ a b ∩ tailSet).Nonempty := by
              refine ⟨b, right_mem_segment ℝ a b, ?_⟩
              left
              exact Or.inl rfl
            have hEq :
                (({a, target} : Set E) ∪
                  {p : E | ∃ i : ℕ, ∃ hi : i + 1 < (a :: b :: rest).length,
                    p ∈ segment ℝ (a :: b :: rest)[i]
                      (a :: b :: rest)[i + 1]}) =
                  segment ℝ a b ∪ tailSet := by
              ext p
              constructor
              · intro hp
                rcases hp with hpEnd | hpSeg
                · rcases hpEnd with hpa | hpt
                  · left
                    simpa [hpa] using left_mem_segment ℝ a b
                  · right
                    left
                    exact Or.inr hpt
                · rcases hpSeg with ⟨i, hi, hpi⟩
                  cases i with
                  | zero =>
                      left
                      simpa using hpi
                  | succ j =>
                      right
                      right
                      refine ⟨j, ?_, ?_⟩
                      · simpa using hi
                      · simpa using hpi
              · intro hp
                rcases hp with hpSeg | hpTail
                · right
                  refine ⟨0, ?_, ?_⟩
                  · simp
                  · simpa using hpSeg
                · rcases hpTail with hpEnd | hpTailSeg
                  · rcases hpEnd with hpb | hpt
                    · right
                      refine ⟨0, ?_, ?_⟩
                      · simp
                      · simpa [hpb] using right_mem_segment ℝ a b
                    · left
                      exact Or.inr hpt
                  · rcases hpTailSeg with ⟨j, hj, hpj⟩
                    right
                    refine ⟨j + 1, ?_, ?_⟩
                    · simpa using hj
                    · simpa using hpj
            have hunion_conn : IsConnected (segment ℝ a b ∪ tailSet) :=
              IsConnected.union hmeet hseg_conn htail_conn
            rw [hEq]
            exact hunion_conn
  rw [γ.carrier_eq]
  exact listChain_connected γ.vertices γ.source γ.target γ.vertices_nonempty
    γ.source_eq_head γ.target_eq_last
