import Mathlib

open scoped SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos79

abbrev GraphCode := Σ n : ℕ, SimpleGraph (Fin n)

end Erdos79

namespace Erdos79.GraphCode

abbrev vertexCount (G : GraphCode) : ℕ := G.1

end Erdos79.GraphCode

namespace Erdos79.GraphCode

abbrev graph (G : GraphCode) : SimpleGraph (Fin G.vertexCount) := G.2

end Erdos79.GraphCode

namespace Erdos79

def NoIsolated (G : GraphCode) : Prop :=
  ∀ v, ¬ G.graph.IsIsolated v

end Erdos79

namespace Erdos79

def RamseyAt (F H : GraphCode) (N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), F.graph ⊑ C ∨ H.graph ⊑ Cᶜ

end Erdos79

namespace Erdos79.GraphCode

noncomputable def edgeCount (G : GraphCode) : ℕ :=
  Nat.card G.graph.edgeSet

end Erdos79.GraphCode

namespace Erdos79

def RamseySizeLinear (F : GraphCode) : Prop :=
  ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H → RamseyAt F H (C * H.edgeCount)

end Erdos79

namespace Erdos79

abbrev IsContained (F G : GraphCode) : Prop := F.graph ⊑ G.graph

end Erdos79

namespace Erdos79

abbrev Isomorphic (F G : GraphCode) : Prop := Nonempty (F.graph ≃g G.graph)

end Erdos79

namespace Erdos79

def ProperSubgraph (F G : GraphCode) : Prop :=
  IsContained F G ∧ ¬ Isomorphic F G

end Erdos79

namespace Erdos79

def MinimallyNonRamseySizeLinear (G : GraphCode) : Prop :=
  ¬ RamseySizeLinear G ∧
    ∀ F : GraphCode, ProperSubgraph F G → RamseySizeLinear F

end Erdos79

namespace Erdos79

theorem erdos79 :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  sorry

end Erdos79

end
