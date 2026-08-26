import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final reduction: the Ramsey capacity contradiction (Section 7 of the paper)

This is the finite-combinatorial climax of the proof.  Suppose the vertex set of
a red/blue colouring of `K_N` (with `N = q(r-1)+a`) decomposes as `Z ⊎ ⋃ᵢ Bᵢ`
where `Bᵢ = Wᵢ ∪ Xᵢ`, with:

* `|Z| ≤ a-1`,
* the `Bᵢ` pairwise disjoint and disjoint from `Z`, covering everything,
* each `Gr[Bᵢ]` is `H`-free,
* there is no blue `T` at all, and
* `r` is a Ramsey witness: every `≥ r`-set contains a red `H` or a blue `T`.

Then `|Bᵢ| ≤ r-1`, so `N = |Z| + ∑|Bᵢ| ≤ (a-1) + q(r-1) < q(r-1)+a = N`, a
contradiction.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Ramsey capacity contradiction.**
-/
theorem final_reduction {V : Type*} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) {Ht Tt : Type*} (H : SimpleGraph Ht) (T : SimpleGraph Tt)
    (q a r : ℕ) (ha : 1 ≤ a)
    (B : Fin q → Finset V) (Z : Finset V)
    (hZ : Z.card ≤ a - 1)
    (hdisjB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hdisjZ : ∀ i, Disjoint (B i) Z)
    (hcover : (Finset.univ.biUnion B) ∪ Z = Finset.univ)
    (hHfree : ∀ i, ¬ H ⊑ Gr.induce (↑(B i)))
    (hNoBlueT : ¬ T ⊑ Grᶜ)
    (hRamsey : ∀ S : Finset V, r ≤ S.card →
      H ⊑ Gr.induce (↑S) ∨ T ⊑ (Gr.induce (↑S))ᶜ)
    (hcard : Fintype.card V = q * (r - 1) + a) :
    False := by
  -- Next, we show that for each i, (B i).card ≤ r - 1.
  have hBcard : ∀ i, (B i).card ≤ r - 1 := by
    intro i
    by_contra h_contra
    have h_card_ge_r : r ≤ (B i).card := by
      exact Nat.le_of_pred_lt ( lt_of_not_ge h_contra )
    have h_embedding : H ⊑ Gr.induce (B i) ∨ T ⊑ (Gr.induce (B i))ᶜ := by
      exact hRamsey _ h_card_ge_r
    cases' h_embedding with hH hT
    exact hHfree i hH
    have hT_embedding : T ⊑ Grᶜ := by
      have hT_embedding : T ⊑ (Grᶜ.induce (B i)) := by
        convert! hT using 1;
        ext; simp [SimpleGraph.induce]
      have hT_embedding : T ⊑ Grᶜ := by
        exact hT_embedding.trans ⟨ ( SimpleGraph.Embedding.induce ( G := Grᶜ ) ( B i ) ).toCopy ⟩
      exact hT_embedding
    exact hNoBlueT hT_embedding;
  -- By counting, we have Fintype.card V = ∑ i, (B i).card + Z.card.
  have hcount : Fintype.card V = ∑ i, (B i).card + Z.card := by
    rw [ ← Finset.card_biUnion ];
    · rw [ ← Finset.card_union_of_disjoint, hcover, Finset.card_univ ];
      exact Finset.disjoint_left.mpr fun x hx hx' => by obtain ⟨ i, _, hi ⟩ := Finset.mem_biUnion.mp hx; exact Finset.disjoint_left.mp ( hdisjZ i ) hi hx';
    · exact fun i _ j _ hij => hdisjB i j hij;
  linarith [ Nat.sub_add_cancel ha, show ∑ i, # ( B i ) ≤ q * ( r - 1 ) from le_trans ( Finset.sum_le_sum fun _ _ => hBcard _ ) ( by simp +decide ) ]

end Erdos550
