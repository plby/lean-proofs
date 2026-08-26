/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.Arithmetic
import ErdosProblems.Erdos569.Partition
import ErdosProblems.Erdos570.Join
import ErdosProblems.Erdos570.RamseyRegion
import ErdosProblems.Erdos570.CycleCode

/-! # Constructing the blue target from the two regions -/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

theorem isContained_induce_of_clique
    {W V : Type*} [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsClique (S : Set V)) (hcard : Fintype.card W ≤ S.card) :
    H ⊑ G.induce (S : Set V) := by
  classical
  let f : W ↪ S := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
  let hom : H →g G.induce (S : Set V) :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        apply hS (f x).2 (f y).2
        intro heq
        exact hxy.ne (f.injective (Subtype.ext heq)) }
  exact ⟨hom.toCopy f.injective⟩

/-- Apply the induction hypothesis to the support of the sampled target,
restore its isolated vertices, and join it to the blue clique. -/
theorem partition_forces_blue
    {H : GraphCode} {k N : ℕ} {budget : ℕ → ℕ} (C : SimpleGraph (Fin N))
    (hcycle : ¬ (cycleCode k).graph ⊑ C)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      RamseyAt (cycleCode k) Q (budget Q.edgeCount))
    (S : Finset (Fin H.vertexCount))
    (hsmall : (inducedCode H S).edgeCount < H.edgeCount)
    (U₁ U₂ : Finset (Fin N))
    (hdisj : Disjoint U₁ U₂)
    (hclique : Cᶜ.IsClique (U₁ : Set (Fin N)))
    (hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, Cᶜ.Adj x y)
    (hcard₁ : H.vertexCount - S.card ≤ U₁.card)
    (hcard₂ : S.card ≤ U₂.card)
    (hbudget : budget (inducedCode H S).edgeCount ≤ U₂.card) :
    H.graph ⊑ Cᶜ := by
  classical
  let H₂raw := inducedCode H S
  let H₁ := inducedCode H Sᶜ
  let H₂ := supportCode H₂raw
  have hH₂edge : H₂.edgeCount = H₂raw.edgeCount := supportCode_edgeCount _
  have hH₂lt : H₂.edgeCount < H.edgeCount := by rw [hH₂edge]; exact hsmall
  have hram := hIH H₂ (supportCode_noIsolated _) hH₂lt
  have hcore : H₂.graph ⊑ Cᶜ.induce (U₂ : Set (Fin N)) := by
    have hroom : budget H₂.edgeCount ≤ U₂.card := by
      rw [hH₂edge]
      exact hbudget
    rcases Erdos570.RamseyAt.on_finset hram C U₂ hroom with hred | hblue
    · exact (hcycle (hred.trans (SimpleGraph.Embedding.induce _).isContained)).elim
    · exact hblue
  have hblue₂ : H₂raw.graph ⊑ Cᶜ.induce (U₂ : Set (Fin N)) := by
    apply isContained_induce_of_supportCode_isContained Cᶜ U₂ hcore
    simpa only [H₂raw, inducedCode_vertexCount] using hcard₂
  have hblue₁ : H₁.graph ⊑ Cᶜ.induce (U₁ : Set (Fin N)) := by
    apply isContained_induce_of_clique H₁.graph Cᶜ U₁ hclique
    simpa only [Fintype.card_fin, H₁, inducedCode_vertexCount,
      Finset.card_compl, Fintype.card_fin] using hcard₁
  have hjoin : (joinCode H₂raw H₁).graph ⊑ Cᶜ := by
    apply joinCode_isContained_of_induced_copies
      (S := (U₂ : Set (Fin N))) (T := (U₁ : Set (Fin N)))
    · rw [Set.disjoint_left]
      intro x hx₂ hx₁
      exact Finset.disjoint_left.mp hdisj hx₁ hx₂
    · exact hblue₂
    · exact hblue₁
    · intro x y
      exact (hcross y.1 y.2 x.1 x.2).symm
  exact SimpleGraph.IsContained.trans (isContained_joinCode_induced_partition H S) hjoin

end Erdos569
