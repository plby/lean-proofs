import Mathlib

noncomputable section


namespace Erdos182

open scoped Classical in
def ContainsRegularSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

end Erdos182

namespace Erdos182

open scoped Classical in
def IsRegularSubgraphFree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ ContainsRegularSubgraph G k

end Erdos182

namespace Erdos182

open scoped Classical in
noncomputable def regularSubgraphFreeGraphs (n k : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  open scoped Classical in
  Finset.univ.filter fun G ↦ IsRegularSubgraphFree G k

end Erdos182

namespace Erdos182

open scoped Classical in
noncomputable def regularExtremalNumber (n k : ℕ) : ℕ :=
  open scoped Classical in
  @Finset.sup ℕ (SimpleGraph (Fin n))
    (@Lattice.toSemilatticeSup ℕ (@DistribLattice.toLattice ℕ instDistribLatticeNat))
    Nat.instOrderBot (regularSubgraphFreeGraphs n k) fun G ↦ G.edgeFinset.card

end Erdos182

namespace Erdos182

open scoped Classical in
noncomputable def logLog (n : ℕ) : ℝ :=
  Real.log (Real.log (n : ℝ))

end Erdos182

namespace Erdos182

open scoped Classical in
theorem erdos_182 (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ))
      =Θ[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) * logLog n) := by
  sorry

end Erdos182

end
