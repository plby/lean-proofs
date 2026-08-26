import ErdosProblems.Erdos633b.CaseTwo

/-! Vertex-order invariance and finite sorting for the reptiling reduction.
Reference reindexing preserves the exact same placed sets. -/

namespace Erdos633b

namespace Tiling

noncomputable def reindexTile {T : Triangle} {n : ℕ} (d : Tiling T n) (e : Equiv.Perm (Fin 3)) :
    Tiling T n where
  tile := d.tile.reindex e
  place := d.place
  covers := by rw [Triangle.support_reindex]; exact d.covers
  disjoint_interiors := by
    simpa only [Triangle.support_reindex] using d.disjoint_interiors

end Tiling

theorem eightCases_of_reindex (T : Triangle) (e : Equiv.Perm (Fin 3))
    (h : EightCases (T.reindex e)) : EightCases T := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.trans e.symm, ?_⟩
  simpa only [Triangle.angle_reindex, Triangle.side_reindex, Equiv.trans_apply] using hf

theorem eightCases_reindex_iff (T : Triangle) (e : Equiv.Perm (Fin 3)) :
    EightCases (T.reindex e) ↔ EightCases T := by
  refine ⟨eightCases_of_reindex T e, ?_⟩
  rintro ⟨f, hf⟩
  refine ⟨f.trans e, ?_⟩
  simpa only [Triangle.angle_reindex, Triangle.side_reindex, Equiv.trans_apply,
    Equiv.symm_apply_apply] using hf

theorem three_values_ordered (f : Fin 3 → ℝ) :
    ∃ e : Equiv.Perm (Fin 3), f (e 0) ≤ f (e 1) ∧ f (e 1) ≤ f (e 2) := by
  by_cases h01 : f 0 ≤ f 1
  · by_cases h12 : f 1 ≤ f 2
    · exact ⟨Equiv.refl _, h01, h12⟩
    · by_cases h20 : f 2 ≤ f 0
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro h20 h01
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h20) (le_of_not_ge h12)
  · by_cases h02 : f 0 ≤ f 2
    · refine ⟨Equiv.swap 0 1, ?_⟩
      simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h01) h02
    · by_cases h12 : f 1 ≤ f 2
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro h12 (le_of_not_ge h02)
      · refine ⟨Equiv.swap 0 2, ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h12) (le_of_not_ge h01)

end Erdos633b
