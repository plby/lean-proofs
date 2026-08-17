/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.Blocks
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Finite graph lemmas for Erdős Problem 110

The key lemma below avoids a missing library equivalence between
bipartiteness and absence of odd cycles.  A spanning forest supplies a
two-coloring.  Any edge violating that coloring closes a forest path to a
short odd walk, which can then be ruled out after applying a homomorphism.
-/

noncomputable section

namespace Erdos110
namespace GraphLemmas

/-- A finite graph is two-colorable if it maps to a graph with no odd closed
walk of length at most the number of its vertices. -/
theorem colorable_two_of_hom_no_short_odd_walk
    {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (K : SimpleGraph W) (f : G →g K)
    (hK : ∀ (u : W) (p : K.Walk u u), Odd p.length →
      p.length ≤ Fintype.card V → False) :
    G.Colorable 2 := by
  classical
  obtain ⟨F, hFG, hFac, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  let cF : F.Coloring Bool :=
    F.recolorOfEquiv finTwoEquiv hFac.coloringTwo
  let cG : G.Coloring Bool := SimpleGraph.Coloring.mk (fun v ↦ cF v) (by
    intro u v huv
    intro huvColor
    have huvReach : F.Reachable u v := by
      rw [hreach]
      exact huv.reachable
    let p : F.Walk u v := huvReach.some.toPath
    have hpPath : p.IsPath := huvReach.some.toPath.prop
    have hpEven : Even p.length := by
      apply (cF.even_length_iff_congr p).2
      rw [huvColor]
    let inc : F →g G := SimpleGraph.Hom.ofLE hFG
    let w : G.Walk u u := (p.map inc).concat huv.symm
    have hwOdd : Odd w.length := by
      simp only [w, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_map]
      exact hpEven.add_one
    have hwBound : w.length ≤ Fintype.card V := by
      simp only [w, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_map]
      exact hpPath.length_lt
    exact hK (f u) (w.map f) (by simpa using hwOdd) (by simpa using hwBound))
  simpa using cG.colorable

end GraphLemmas
end Erdos110
