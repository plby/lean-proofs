import ErdosProblems.Erdos118.Reused591.MacroDescendants
import ErdosProblems.Erdos118.Reused591.LexPrefix

namespace Erdos118.Reused591

/-!
# Exact order type of the constructed macro family

The descendant lower bound is proved by the two finite rank parameters,
using the checked macro transitions and ordered child cylinders. Root
label sizes are unbounded, so the completed family has the exact type
`omega ^ (omega ^ 2)`.
-/

open Ordinal

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact Erdos591.Negative.LexPrefix

/-- Countably many consecutive copies of a lower bound `a` supply
the ordinal product `a * omega`. -/
theorem mul_omega_le_type_of_blocks {X : Type} [LinearOrder X] [WellFoundedLT X]
    (s : Set X) (f : ℕ → Set X) (a : Ordinal.{0})
    (hsub : ∀ j, f j ⊆ s)
    (hsep : ∀ i j, i < j → ∀ x ∈ f i, ∀ y ∈ f j, x < y)
    (ha : ∀ j, a ≤ typeLT (f j)) : a * ω ≤ typeLT s := by
  classical
  have he (j : ℕ) : Nonempty
      (((· < ·) : a.ToType → a.ToType → Prop) ↪r ((· < ·) : f j → f j → Prop)) := by
    apply Ordinal.type_le_iff'.mp
    simpa only [Ordinal.type_toType] using ha j
  let e (j : ℕ) := Classical.choice (he j)
  let g (x : ℕ ×ₗ a.ToType) : s :=
    ⟨e (ofLex x).1 (ofLex x).2, hsub (ofLex x).1 (e (ofLex x).1 (ofLex x).2).property⟩
  have hg : StrictMono g := by
    intro x y hxy
    change (e (ofLex x).1 (ofLex x).2).val < (e (ofLex y).1 (ofLex y).2).val
    rcases Prod.Lex.lt_iff.mp hxy with hij | ⟨heq, hxy⟩
    · exact hsep _ _ hij _ (e (ofLex x).1 (ofLex x).2).property
        _ (e (ofLex y).1 (ofLex y).2).property
    · rw [heq]
      exact (e (ofLex y).1).map_rel_iff.mpr hxy
  have ht : typeLT (ℕ ×ₗ a.ToType) = a * ω := by
    change Ordinal.type (Prod.Lex ((· < ·) : ℕ → ℕ → Prop)
      ((· < ·) : a.ToType → a.ToType → Prop)) = _
    rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_nat_lt]
  rw [← ht]
  exact (RelEmbedding.ofMonotone g hg).ordinal_type_le

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem node_live_of_rank (p : ℕ)
    (hp : 0 < bodyRank (node hH b p).cursor ∨ 0 < leafRank (node hH b p).cursor) :
    (node hH b p).cursor.terminal = false := by
  cases ht : (node hH b p).cursor.terminal with
  | false => rfl
  | true =>
      have hz := terminal_ranks (node hH b p).invariant ht
      omega

theorem vertices_one_le (p : ℕ) : 1 ≤ typeLT (vertices hH b p) := by
  apply Order.one_le_iff_ne_zero.mpr
  apply Ordinal.type_ne_zero_iff_nonempty.mpr
  exact (vertices_nonempty hH b p).to_subtype

/-- The rank estimate applies to all constructed cursors. At rank zero
the separately proved existence of a completed descendant supplies the
base case. -/
theorem vertices_rank_bound (t k p : ℕ)
    (ht : bodyRank (node hH b p).cursor = t)
    (hk : leafRank (node hH b p).cursor = k) :
    (ω ^ ω : Ordinal.{0}) ^ t * ω ^ k ≤ typeLT (vertices hH b p) := by
  induction t using Nat.strong_induction_on generalizing k p with
  | h t ih =>
      induction k generalizing p with
      | zero =>
          cases t with
          | zero => simpa using vertices_one_le hH b p
          | succ t =>
              have hp := node_live_of_rank hH b p (Or.inl (by omega))
              rw [pow_succ, pow_zero, mul_one,
                ← Ordinal.iSup_pow_natCast Ordinal.omega0_pos, Ordinal.mul_iSup]
              simp only [Ordinal.iSup_pow_natCast Ordinal.omega0_pos]
              apply Ordinal.iSup_le
              intro j
              have hr := (child_extension hH b p j hp).future_rank (Nat.succ_pos j)
                (node hH b p).invariant hk (by omega)
              have hct : bodyRank (node hH b (child p j)).cursor = t := by omega
              have hck : leafRank (node hH b (child p j)).cursor = j := by omega
              exact (ih t (Nat.lt_succ_self t) j (child p j) hct hck).trans
                (typeLT_mono_set (vertices_subset hH b (child_descendant p j)))
      | succ k ihk =>
          have hp := node_live_of_rank hH b p (Or.inr (by omega))
          rw [pow_succ (ω : Ordinal.{0}), ← mul_assoc]
          apply mul_omega_le_type_of_blocks (vertices hH b p)
            (fun j => vertices hH b (child p j)) ((ω ^ ω) ^ t * ω ^ k)
          · exact fun j => vertices_subset hH b (child_descendant p j)
          · exact fun i j hij => child_vertices_separated hH b p hp hij
          · intro j
            have hr := (child_extension hH b p j hp).current_rank
              (node hH b p).invariant (by omega)
            apply ihk (child p j) (hr.2.1.trans ht)
            omega

theorem root_type_lower (j : ℕ) :
    (ω ^ ω : Ordinal.{0}) ^ j ≤ typeLT (vertices hH b (child 0 j)) := by
  have hr := root_ranks hH b j
  have hb := vertices_rank_bound hH b j j (child 0 j) hr.2.1 hr.2.2
  apply le_trans _ hb
  apply Ordinal.le_mul_left
  exact pow_pos Ordinal.omega0_pos _

/-- The actual set of completed constructed words has the intended
endpoint order type; this is not just a family of possible extensions. -/
theorem vertices_type : typeLT (vertices hH b 0) = (ω ^ (ω ^ 2) : Ordinal.{0}) := by
  apply le_antisymm
  · exact (Ordinal.type_set_le (vertices hH b 0)).trans_eq Erdos591.Negative.Exact.type_G
  · rw [← Erdos591.Negative.thetaOmega_eq,
      ← Ordinal.iSup_pow_natCast (Ordinal.opow_pos _ Ordinal.omega0_pos)]
    apply Ordinal.iSup_le
    intro j
    exact (root_type_lower hH b j).trans
      (typeLT_mono_set (vertices_subset hH b (child_descendant 0 j)))

#print axioms mul_omega_le_type_of_blocks
#print axioms vertices_rank_bound
#print axioms root_type_lower
#print axioms vertices_type

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
