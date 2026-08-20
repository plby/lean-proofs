import ErdosProblems.Erdos733.ST.PolygonalPathConcat

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathFiniteChainConcat]
lemma PolygonalPathFiniteChainConcat
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    ∀ (pieces : List PolygonalPath) (first last : PolygonalPath),
      pieces.head? = some first →
        pieces.getLast? = some last →
          (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ S) →
            (∀ (i : ℕ) (hi : i + 1 < pieces.length),
              (pieces[i]).target = (pieces[i + 1]).source) →
              ∃ ζ : PolygonalPath,
                ζ.source = first.source ∧
                  ζ.target = last.target ∧
                    ζ.carrier ⊆ S := by
-- BODY
  intro pieces
  induction pieces with
  | nil =>
      intro first last hhead _hlast _hsub _hchain
      simp at hhead
  | cons p ps ih =>
      intro first last hhead hlast hsub hchain
      cases ps with
      | nil =>
          simp at hhead hlast
          subst first
          subst last
          exact ⟨p, rfl, rfl, hsub p (by simp)⟩
      | cons q qs =>
          simp at hhead
          subst first
          have htail_last : (q :: qs).getLast? = some last := by
            simpa using hlast
          have htail_sub :
              ∀ η : PolygonalPath, η ∈ q :: qs → η.carrier ⊆ S := by
            intro η hη
            exact hsub η (by simp [hη])
          have htail_chain :
              ∀ (i : ℕ) (hi : i + 1 < (q :: qs).length),
                ((q :: qs)[i]).target = ((q :: qs)[i + 1]).source := by
            intro i hi
            have hi' : (i + 1) + 1 < (p :: q :: qs).length := by
              simpa using hi
            have h := hchain (i + 1) hi'
            simpa using h
          rcases ih q last (by simp) htail_last htail_sub htail_chain with
            ⟨tail, htail_source, htail_target, htail_carrier⟩
          have hp_sub : p.carrier ⊆ S := hsub p (by simp)
          have hpq : p.target = q.source := by
            have h := hchain 0 (by simp : 0 + 1 < (p :: q :: qs).length)
            simpa using h
          have hmatch : p.target = tail.source := by
            rw [htail_source]
            exact hpq
          rcases PolygonalPathConcat S p tail hmatch hp_sub htail_carrier with
            ⟨ζ, hζsource, hζtarget, hζcarrier⟩
          refine ⟨ζ, ?_, ?_, hζcarrier⟩
          · exact hζsource
          · rw [hζtarget, htail_target]
