import ErdosProblems.Erdos556.FourMatchingCores
import ErdosProblems.Erdos556.CubeMatchingClassification
import ErdosProblems.Erdos556.ColourRelabelling
import ErdosProblems.Erdos556.FourCorePatternOne
import ErdosProblems.Erdos556.FourCorePatternTwo

/-! Every four-edge cube matching is covered by one of the two exact finishers. -/

namespace Erdos556

open SimpleGraph Finset

theorem monochromatic_cycle_of_four_matching_cores {V : Type*}
    [Fintype V] [DecidableEq V] (c : ThreeColouring V) (r d : ℕ)
    (hr : 4 ≤ r) (hN : 8 * r < Fintype.card V)
    (h : FourMatchingCores c (r + 2 * d + 3) d) :
    ∃ i, cycleGraph (2 * r + 1) ⊑ c.graph i := by
  classical
  obtain ⟨s, k, hs, hk, hpat⟩ := disjoint_cube_edges_have_four_core_pattern
    h.profiles h.dimension h.profile_disjoint
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective k ⟨hk, (Finite.injective_iff_surjective).mp hk⟩
  let c' := c.relabel e
  let A : Fin 4 → Finset V := fun i => h.cores (s i)
  have hgraph (i : Fin 3) : c'.graph i = c.graph (k i) := c.graph_relabel e i
  have hdis (i j : Fin 4) (hij : i ≠ j) : Disjoint (A i) (A j) :=
    h.core_disjoint _ _ (hs.ne hij)
  have hlarge (i : Fin 4) : r + 2 * d + 3 ≤ (A i).card := h.large (s i)
  have hdense (a b : Fin 4) (i : Fin 3)
      (hsep : uniqueProfileSeparator (h.profiles (s a)) (h.profiles (s b)) (k i)) :
      BipartiteDefect (c'.graph i) (A a) (A b) d := by
    have hh := h.dense (s a) (s b) (k i) hsep
    simpa only [hgraph] using hh
  have hcycle : ∃ i, cycleGraph (2 * r + 1) ⊑ c'.graph i := by
    rcases hpat with hp | hp
    · obtain ⟨h02, h13, h01, h23⟩ := hp
      have hpattern : FourCorePatternOne c' A d :=
        ⟨hdis, hdense 0 2 0 h02, hdense 1 3 0 h13, hdense 0 1 1 h01, hdense 2 3 1 h23⟩
      exact monochromatic_cycle_of_four_core_pattern_one c' A r d hr hN hpattern hlarge
    · obtain ⟨h02, h03, h12, h13, h01, h23⟩ := hp
      have hpattern : FourCorePatternTwo c' A d :=
        ⟨hdis, hdense 0 2 0 h02, hdense 0 3 0 h03, hdense 1 2 0 h12,
          hdense 1 3 0 h13, hdense 0 1 1 h01, hdense 2 3 2 h23⟩
      exact monochromatic_cycle_of_four_core_pattern_two c' A r d (by omega) hN hpattern
        (fun i => by have hh := hlarge i; omega)
  obtain ⟨i, hi⟩ := hcycle
  rw [hgraph] at hi
  exact ⟨k i, hi⟩

#print axioms monochromatic_cycle_of_four_matching_cores

end Erdos556
