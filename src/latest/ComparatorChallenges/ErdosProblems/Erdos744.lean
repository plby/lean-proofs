import Mathlib

open Filter SimpleGraph
open Function

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos744

def threshold (q : ℕ) : ℕ := max (2 * q) (2 * q.choose 2 - 1)

end Erdos744

namespace Erdos744

def IsCritical {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
    ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < (k : ℕ∞)

end Erdos744

namespace Erdos744

def CanBipartizeBy {V : Type u} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Set (Sym2 V),
    E ⊆ G.edgeSet ∧ E.ncard = m ∧ (G.deleteEdges E).IsBipartite

end Erdos744

namespace Erdos744

noncomputable def deletionNumber {V : Type u} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | CanBipartizeBy G m}

end Erdos744

namespace Erdos744

def criticalDeletionNumbers (k n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ G : SimpleGraph (Fin n),
    IsCritical G k ∧ deletionNumber G = m}

end Erdos744

namespace Erdos744

noncomputable def f (k n : ℕ) : ℕ :=
  sInf (criticalDeletionNumbers k n)

end Erdos744

namespace Erdos744

theorem erdos_744 {q n : ℕ} (hq : 3 ≤ q) (hn : threshold q ≤ n) :
    f (q + 1) n = q.choose 2 := by
  sorry

end Erdos744

end
