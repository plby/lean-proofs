import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bounding irregular pairs inside a cluster set by the partition's non-uniform count

The graph-side plumbing for the `α(Q) < ηℓ` step.  For a Szemerédi partition `P`
with regular-pairs graph `Rg` on the parts, and any subset `𝒜` of parts, the
number of irregular (non-`Rg`) pairs inside `𝒜` is at most the partition's total
non-uniform count `#(P.nonUniforms G ε)`.  Combined with `Finpartition.IsUniform`
(which gives `#(P.nonUniforms G ε) ≤ ℓ(ℓ−1)ε < εℓ²`), this discharges the "few
irregular pairs" hypothesis of `Erdos550.alphaQ_dense_regular_pair`.
-/

open SimpleGraph Finset Classical

namespace Erdos550

/-
The number of irregular pairs inside `𝒜` (non-edges of the regular-pairs graph
`Rg`, induced on `𝒜`) is at most the partition's total non-uniform count.
-/
lemma induce_compl_edges_le_nonUniforms {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (P : Finpartition (univ : Finset V))
    (Rg : SimpleGraph {x // x ∈ P.parts}) [DecidableRel Rg.Adj]
    (hRg : ∀ U W : {x // x ∈ P.parts}, U ≠ W →
      (Rg.Adj U W ↔ G.IsUniform ε U.val W.val))
    (𝒜 : Finset {x // x ∈ P.parts}) :
    ((Rg.induce (↑𝒜 : Set {x // x ∈ P.parts}))ᶜ).edgeFinset.card
      ≤ (P.nonUniforms G ε).card := by
  refine' le_trans _ ( Finset.card_mono _ );
  rotate_left;
  exact Finset.image ( fun e : Sym2 { x // x ∈ 𝒜 } => ( ( e.out.1 : { x // x ∈ P.parts } ).val, ( e.out.2 : { x // x ∈ P.parts } ).val ) ) ( ( SimpleGraph.comap ( fun x : { x // x ∈ 𝒜 } => ( x : { x // x ∈ P.parts } ) ) Rg )ᶜ ).edgeFinset;
  · intro e he;
    rw [ Finset.mem_image ] at he
    obtain ⟨e', he', rfl⟩ := he;
    cases h : Quot.out e' ; simp_all +decide;
    have := Quot.out_eq e'; aesop;
  · rw [ Finset.card_image_of_injOn ];
    · convert! rfl.le;
    · intro e he f hf h; simp_all +decide [ SimpleGraph.comap, SimpleGraph.edgeFinset ] ;
      rw [ ← Quot.out_eq e, ← Quot.out_eq f ];
      grind

end Erdos550
