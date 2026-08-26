import ErdosProblems.Erdos591.ExtractionBudget

open Set Ordinal

namespace Erdos591.Negative.Exact.Levels

/-! A large extracted level must lie beyond every already fixed outer
prefix.  This is needed when the extraction lemma is used a second time
inside a previously chosen continuation. -/

theorem prefix_length_lt_root_of_level_nonempty
    {W : Set G} {p : List (List ℕ)} {m : ℕ}
    (hroot : ∀ x ∈ W, x.1.length = m)
    (hlevel : (Level W p).Nonempty) : p.length < m := by
  rcases hlevel with ⟨a, x, hx⟩
  have hlen := hx.2.length_le
  rw [List.length_append] at hlen
  change p.length + 1 ≤ x.1.length at hlen
  rw [hroot x hx.1] at hlen
  omega

theorem fixed_prefix_of_large_level
    {W : Set G} (s p : List (List ℕ))
    (hs : ∀ x ∈ W, s <+: x.1)
    (hlevel : 1 < typeLT (Level W p)) : s <+: p := by
  by_cases hlen : s.length ≤ p.length
  · have hn : Nonempty (Level W p) :=
      Ordinal.type_ne_zero_iff_nonempty.mp
        (ne_of_gt (zero_lt_one.trans hlevel))
    rcases hn with ⟨⟨a, x, hx⟩⟩
    exact List.prefix_of_prefix_length_le (hs x hx.1)
      (child_subset_fiber W p a hx).2 hlen
  · have hlen' : p.length < s.length := lt_of_not_ge hlen
    have : Subsingleton (Level W p) := by
      refine ⟨fun a b ↦ ?_⟩
      rcases a.2 with ⟨x, hx⟩
      rcases b.2 with ⟨y, hy⟩
      have ha : p ++ [show List ℕ from a.1] <+: s :=
        List.prefix_of_prefix_length_le hx.2 (hs x hx.1) (by
          rw [List.length_append]
          change p.length + 1 ≤ s.length
          omega)
      have hb : p ++ [show List ℕ from b.1] <+: s :=
        List.prefix_of_prefix_length_le hy.2 (hs y hy.1) (by
          rw [List.length_append]
          change p.length + 1 ≤ s.length
          omega)
      have heq : p ++ [show List ℕ from a.1] =
          p ++ [show List ℕ from b.1] := by
        have hlength : (p ++ [show List ℕ from a.1]).length =
            (p ++ [show List ℕ from b.1]).length := by
          rw [List.length_append, List.length_append]
          rfl
        exact (List.prefix_of_prefix_length_le ha hb hlength.le).eq_of_length hlength
      have hab := List.append_right_injective p heq
      exact Subtype.ext (List.cons.inj hab).1
    exact ((not_le_of_gt hlevel)
      (LexPrefix.typeLT_le_one_of_subsingleton (Level W p))).elim

/-- Extraction inside a fixed continuation never goes back into an
already fixed block. -/
theorem exists_large_level_extending_prefix
    (W : Set G) {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m)
    (s : List (List ℕ)) (hs : ∀ x ∈ W, s <+: x.1)
    (r d : ℕ) (hW : continuationBound (r + 2) ≤ typeLT W) :
    ∃ (U : Set G) (p : List (List ℕ)),
      U ⊆ W ∧ s <+: p ∧ Fiber U p = U ∧
      ω ^ (d : Ordinal.{0}) < typeLT (Level U p) ∧
      ∀ a ∈ Level U p, continuationBound r ≤ typeLT (Child U p a) := by
  obtain ⟨U, p, hUW, hUp, hlevel, hchildren⟩ :=
    exists_large_level_with_slack W hroot r d hW
  have hlarge : 1 < typeLT (Level U p) :=
    (Order.one_le_iff_pos.mpr (Ordinal.opow_pos (d : Ordinal.{0})
      Ordinal.omega0_pos)).trans_lt hlevel
  have hsp : s <+: p :=
    fixed_prefix_of_large_level s p (fun x hx ↦ hs x (hUW hx)) hlarge
  exact ⟨U, p, hUW, hsp, hUp, hlevel, hchildren⟩

end Erdos591.Negative.Exact.Levels
