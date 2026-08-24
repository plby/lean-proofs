/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset SimpleGraph

namespace Erdos426

namespace UniqueSubgraphs

instance graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G₁ G₂ := Nonempty (G₁.Iso G₂)
  iseqv := {
    refl := fun _ => ⟨Iso.refl⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

noncomputable def paperDenom (n : ℕ) : ℝ :=
  (2 ^ n.choose 2 : ℝ) / (Nat.factorial n : ℝ)

def IsUniqueSubgraph {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! S : H.Subgraph, S.IsSpanning ∧ Nonempty (S.spanningCoe.Iso G)

open scoped Classical in
noncomputable def uniqueSubgraphClasses {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Quotient (graphIsoSetoid n)) :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsUniqueSubgraph G H)).image
    (Quotient.mk (graphIsoSetoid n))

noncomputable def fH {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  ((uniqueSubgraphClasses H).card : ℝ) / paperDenom n

noncomputable def fSeq (n : ℕ) : ℝ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup' ⟨⊥, mem_univ _⟩ fH

theorem erdos_426 : Filter.Tendsto fSeq Filter.atTop (nhds 0) := by
  sorry

end UniqueSubgraphs

end Erdos426
