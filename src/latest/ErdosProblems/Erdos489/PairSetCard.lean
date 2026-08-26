import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- A finite pair set whose coordinates lie below `M` has at most `M²`
elements. -/
theorem pair_finset_card_le_sq
    (J : Finset (ℕ × ℕ)) (M : ℕ)
    (hJ : ∀ z ∈ J, z.1 < M ∧ z.2 < M) :
    J.card ≤ M ^ 2 := by
  have hsub : J ⊆ Finset.range M ×ˢ Finset.range M := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hJ z hz).1,
        Finset.mem_range.mpr (hJ z hz).2⟩
  calc
    J.card ≤ (Finset.range M ×ˢ Finset.range M).card :=
      Finset.card_le_card hsub
    _ = M ^ 2 := by simp [pow_two]

/-- Ranks of enumerated predicate elements not exceeding `X` lie below the
strict count through `X+1`. -/
theorem nth_rank_lt_count_succ_of_le
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (r X : ℕ) (hr : Nat.nth p r ≤ X) :
    r < Nat.count p (X + 1) := by
  have hcount := Nat.count_nth_succ_of_infinite hp r
  have hmono : Nat.count p (Nat.nth p r + 1) ≤ Nat.count p (X + 1) :=
    Nat.count_monotone p (by omega)
  rw [hcount] at hmono
  omega

/-- Hence a pair set whose enumerated moduli are at most `X` has at most the
square of the forbidden counting function through `X+1` elements. -/
theorem rank_pair_finset_card_le_count_sq
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (J : Finset (ℕ × ℕ)) (X : ℕ)
    (hJ : ∀ z ∈ J, Nat.nth p z.1 ≤ X ∧ Nat.nth p z.2 ≤ X) :
    J.card ≤ (Nat.count p (X + 1)) ^ 2 := by
  apply pair_finset_card_le_sq J (Nat.count p (X + 1))
  intro z hz
  exact ⟨nth_rank_lt_count_succ_of_le p hp z.1 X (hJ z hz).1,
    nth_rank_lt_count_succ_of_le p hp z.2 X (hJ z hz).2⟩

end Erdos489
