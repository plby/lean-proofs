/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos182

def ContainsRegularSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

def IsRegularSubgraphFree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ ContainsRegularSubgraph G k

noncomputable def regularSubgraphFreeGraphs (n k : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  open scoped Classical in
  Finset.univ.filter fun G ↦ IsRegularSubgraphFree G k

noncomputable def regularExtremalNumber (n k : ℕ) : ℕ :=
  open scoped Classical in
  @Finset.sup ℕ (SimpleGraph (Fin n))
    (@Lattice.toSemilatticeSup ℕ (@DistribLattice.toLattice ℕ instDistribLatticeNat))
    Nat.instOrderBot (regularSubgraphFreeGraphs n k) fun G ↦ G.edgeFinset.card

noncomputable def logLog (n : ℕ) : ℝ :=
  Real.log (Real.log (n : ℝ))

theorem erdos_182 (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ))
      =Θ[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) * logLog n) := by
  sorry

end Erdos182
