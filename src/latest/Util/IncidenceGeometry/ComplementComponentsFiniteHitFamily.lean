import Util.IncidenceGeometry.ComplementComponentAbsorbsConnectedSubset

open Classical
noncomputable section

lemma ComplementComponentsFiniteHitFamily
    (K : Set (EuclideanSpace ℝ (Fin 2))) {ι : Type} [Fintype ι]
    (P : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hPne : ∀ i, (P i).Nonempty)
    (hPsub : ∀ i, P i ⊆ Kᶜ)
    (hPconn : ∀ i, IsConnected (P i))
    (hhit : ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent K C → ∃ i, (C ∩ P i).Nonempty) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps, ComplementComponent K C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent K C → C ∈ comps := by
  classical
  let candidate : ι → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    if h : ∃ C : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent K C ∧ (C ∩ P i).Nonempty then
      Classical.choose h
    else
      ∅
  let comps : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    (Finset.univ.image candidate).filter (fun C => ComplementComponent K C)
  refine ⟨comps, ?_, ?_⟩
  · intro C hCmem
    exact (Finset.mem_filter.mp hCmem).2
  · intro C hC
    rcases hhit C hC with ⟨i, hCi⟩
    have hExists :
        ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent K D ∧ (D ∩ P i).Nonempty :=
      ⟨C, hC, hCi⟩
    have hCandidateComp : ComplementComponent K (candidate i) := by
      dsimp [candidate]
      rw [dif_pos hExists]
      exact (Classical.choose_spec hExists).1
    have hCandidateMeet : (candidate i ∩ P i).Nonempty := by
      dsimp [candidate]
      rw [dif_pos hExists]
      exact (Classical.choose_spec hExists).2
    have hPsubC : P i ⊆ C :=
      ComplementComponentAbsorbsConnectedSubset K C (P i)
        hC (hPne i) (hPsub i) (hPconn i) hCi
    have hPsubCandidate : P i ⊆ candidate i :=
      ComplementComponentAbsorbsConnectedSubset K (candidate i) (P i)
        hCandidateComp (hPne i) (hPsub i) (hPconn i) hCandidateMeet
    rcases hPne i with ⟨p, hpP⟩
    have hCandidateEq : candidate i = C := by
      apply le_antisymm
      · exact
          ComplementComponentAbsorbsConnectedSubset K C (candidate i)
            hC hCandidateComp.1 hCandidateComp.2.1
            hCandidateComp.2.2.1
            ⟨p, hPsubC hpP, hPsubCandidate hpP⟩
      · exact
          ComplementComponentAbsorbsConnectedSubset K (candidate i) C
            hCandidateComp hC.1 hC.2.1 hC.2.2.1
            ⟨p, hPsubCandidate hpP, hPsubC hpP⟩
    have hCandidateMemImage : candidate i ∈ Finset.univ.image candidate :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hCandidateMemComps : candidate i ∈ comps := by
      exact Finset.mem_filter.mpr ⟨hCandidateMemImage, hCandidateComp⟩
    simpa [hCandidateEq] using hCandidateMemComps
