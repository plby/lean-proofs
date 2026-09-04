import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Refining a coloring into small covered vertex sets -/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

theorem exists_small_class_recoloring {V K : Type*} [Fintype V] [Fintype K]
    (H : SetHypergraph V) (c : H.EdgeColoring K) (A : ℕ)
    (hsize : ∀ e : H, e.1.ncard ≤ A) :
    ∃ m : ℕ, ∃ recolor : H.EdgeColoring (Fin m),
      (∀ i, (H.colorCovered recolor i).ncard ≤ A) ∧
      m ≤ Fintype.card K + ((∑ e : H, e.1.ncard) / (A + 1)) *
        (Fintype.card V / (A / 2 + 1)) := by
  classical
  obtain ⟨L, hL, c₀, hbounded, hcard⟩ := H.exists_cover_bounded_recoloring c A
  let : Fintype L := hL
  let sigma := Fintype.equivFin L
  let recolor : H.EdgeColoring (Fin (Fintype.card L)) :=
    ⟨fun e ↦ sigma (c₀.color e), fun _ _ hef hinter heq ↦
      c₀.valid hef hinter (sigma.injective heq)⟩
  have hlarge := H.large_colorClasses_mul_le_total_incidence c A
  have hcount : ({i : K | A < (H.coveredVertices {e | c.color e = i}).ncard} : Set K).ncard ≤
      (∑ e : H, e.1.ncard) / (A + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr hlarge
  refine ⟨Fintype.card L, recolor, ?_, ?_⟩
  · intro i
    rw [colorCovered_eq_coveredVertices]
    have hclass : ({e : H | recolor.color e = i} : Set H) =
        {e : H | c₀.color e = sigma.symm i} := by
      ext e
      exact sigma.apply_eq_iff_eq_symm_apply
    rw [hclass]
    rcases hbounded (sigma.symm i) with hsingle | hsmall
    · exact H.coveredVertices_ncard_le_of_singleton_class _ A hsingle hsize
    · exact hsmall
  · exact hcard.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcount) _)

#print axioms exists_small_class_recoloring

end Erdos19.SetHypergraph
