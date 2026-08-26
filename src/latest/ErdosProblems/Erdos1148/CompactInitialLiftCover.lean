import ErdosProblems.Erdos1148.CoherentNeighborhoods

/-! # A finite coherent lift cover of any compact quotient subset -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compact_initial_lift_cover {K : Set ModularOrbitSpace} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      K ⊆ ⋃ i, modularMk '' B i ∧ ∀ i, LiftForwardClose η 0 (B i) := by
  classical
  have hex (x : ModularOrbitSpace) := exists_open_coherent_modular_neighborhood hη x
  choose U E hU hx himage hclose using hex
  obtain ⟨s, hcover⟩ := hK.elim_finite_subcover U hU (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := s.equivFin
  refine ⟨s.card, fun i => E (e.symm i).val, ?_, fun i => hclose (e.symm i).val⟩
  intro x hxK
  obtain ⟨y, hy, hxU⟩ := Set.mem_iUnion₂.mp (hcover hxK)
  refine Set.mem_iUnion.mpr ⟨e ⟨y, hy⟩, ?_⟩
  change x ∈ modularMk '' E (e.symm (e ⟨y, hy⟩)).val
  have he : e.symm (e ⟨y, hy⟩) = ⟨y, hy⟩ := e.symm_apply_apply _
  rw [he, himage]
  exact hxU

end Erdos1148.DukeArithmetic
