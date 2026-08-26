import ErdosProblems.Erdos591.ExactLevelProgress

open Set Ordinal

namespace Erdos591.Negative.BodyPrefix

open WeakPigeon

/-! Maximal body prefixes with explicit nonempty extensions above any
finite numerical bound.  These are the nonbox segments in the alternating
pair construction. -/

structure Maximal {n : ℕ} (A : Set (RawLevel n)) (u : List ℕ) (k : ℕ) : Prop where
  length_le : u.length ≤ n
  type_eq : typeLT (LexPrefix.Fiber A u) = ω ^ (k : Ordinal.{0})
  child_small : ∀ a, typeLT (LexPrefix.Child A u a) < ω ^ (k : Ordinal.{0})

theorem Maximal.nonempty {n k : ℕ} {A : Set (RawLevel n)} {u : List ℕ}
    (h : Maximal A u k) : (LexPrefix.Fiber A u).Nonempty := by
  have hpos : 0 < typeLT (LexPrefix.Fiber A u) := by
    rw [h.type_eq]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hn : Nonempty (LexPrefix.Fiber A u) :=
    Ordinal.type_ne_zero_iff_nonempty.mp (ne_of_gt hpos)
  rcases hn with ⟨x⟩
  exact ⟨x.1, x.2⟩

theorem Maximal.pairwise {n k : ℕ} {A : Set (RawLevel n)} {u : List ℕ}
    (h : Maximal A u k)
    (hA : ∀ a ∈ A, a.1.Pairwise (· < ·)) : u.Pairwise (· < ·) := by
  obtain ⟨a, ha⟩ := h.nonempty
  exact List.Pairwise.sublist ha.2.sublist (hA a ha.1)

theorem Maximal.length_lt {n k : ℕ} {A : Set (RawLevel n)} {u : List ℕ}
    (h : Maximal A u k) (hk : 0 < k) : u.length < n := by
  apply lt_of_le_of_ne h.length_le
  intro heq
  have : Subsingleton (LexPrefix.Fiber A u) :=
    LexPrefix.fiber_subsingleton_of_length_eq A u heq
  have hle := LexPrefix.typeLT_le_one_of_subsingleton (LexPrefix.Fiber A u)
  rw [h.type_eq] at hle
  have hgt : 1 < ω ^ (k : Ordinal.{0}) :=
    Ordinal.one_lt_opow.mpr
      ⟨Ordinal.one_lt_omega0, by exact_mod_cast Nat.ne_of_gt hk⟩
  exact (not_le_of_gt hgt) hle

theorem all_above_of_pairwise_cons {a bound : ℕ} {t : List ℕ}
    (ha : bound < a) (h : (a :: t).Pairwise (· < ·)) :
    ∀ z ∈ a :: t, bound < z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact ha
  · exact ha.trans ((List.pairwise_cons.mp h).1 z hz)

/-- Descend to a smaller maximal rank, appending a nonempty body segment
all of whose coordinates exceed `bound`. -/
theorem Maximal.extend_above {n k j : ℕ} {A : Set (RawLevel n)} {u : List ℕ}
    (h : Maximal A u k)
    (hA : ∀ a ∈ A, a.1.Pairwise (· < ·))
    (hjk : j < k) (bound : ℕ) :
    ∃ t : List ℕ, t ≠ [] ∧ (∀ z ∈ t, bound < z) ∧ Maximal A (u ++ t) j := by
  obtain ⟨a, v, hba, huv, hvn, htype, hsmall⟩ :=
    LexPrefix.exists_maximal_prefix_above A u h.length_le h.type_eq
      h.child_small hjk bound
  rcases huv with ⟨t, ht⟩
  have heq : u ++ (a :: t) = v := by
    simpa only [List.append_assoc, List.singleton_append] using ht
  have hv : Maximal A v j := ⟨hvn, htype, hsmall⟩
  have hpair : (a :: t).Pairwise (· < ·) := by
    have hp := hv.pairwise hA
    rw [← heq] at hp
    exact (List.pairwise_append.mp hp).2.1
  refine ⟨a :: t, List.cons_ne_nil _ _, all_above_of_pairwise_cons hba hpair, ?_⟩
  rwa [heq]

/-- Complete a positive-rank body prefix, with every appended coordinate
above `bound`.  The result remains in the selected fixed-length family. -/
theorem Maximal.complete_above {n k : ℕ} {A : Set (RawLevel n)} {u : List ℕ}
    (h : Maximal A u k)
    (hA : ∀ a ∈ A, a.1.Pairwise (· < ·))
    (hk : 0 < k) (bound : ℕ) :
    ∃ a ∈ A, ∃ t : List ℕ,
      t ≠ [] ∧ (∀ z ∈ t, bound < z) ∧ u ++ t = a.1 := by
  obtain ⟨b, hbb, hlarge⟩ :=
    LexPrefix.exists_large_child_above A u h.length_le h.type_eq
      h.child_small (j := 0) hk bound
  have hpos : 0 < typeLT (LexPrefix.Child A u b) :=
    (Ordinal.opow_pos (0 : Ordinal.{0}) Ordinal.omega0_pos).trans_le hlarge
  have hn : Nonempty (LexPrefix.Child A u b) :=
    Ordinal.type_ne_zero_iff_nonempty.mp (ne_of_gt hpos)
  rcases hn with ⟨⟨a, ha⟩⟩
  rcases ha.2 with ⟨t, ht⟩
  have heq : u ++ (b :: t) = a.1 := by
    simpa only [List.append_assoc, List.singleton_append] using ht
  have hpair : (b :: t).Pairwise (· < ·) := by
    have hp := hA a ha.1
    rw [← heq] at hp
    exact (List.pairwise_append.mp hp).2.1
  exact ⟨a, ha.1, b :: t, List.cons_ne_nil _ _,
    all_above_of_pairwise_cons hbb hpair, heq⟩

end Erdos591.Negative.BodyPrefix

namespace Erdos591.Negative.Exact

theorem body_pairwise (x : G) {a : List ℕ} (ha : a ∈ x.1) :
    a.Pairwise (· < ·) := by
  have hflat : (x.1.flatMap levelWord).Pairwise (· < ·) := x.2.tail
  have hlevel := (List.pairwise_flatMap.mp hflat).1 a ha
  exact hlevel.tail

namespace Levels

theorem level_body_pairwise {W : Set G} {p : List (List ℕ)}
    {a : InnerLevels.OrderedSL} (ha : a ∈ Level W p) :
    (show List ℕ from a).Pairwise (· < ·) := by
  rcases ha with ⟨x, hx⟩
  apply body_pairwise x
  apply hx.2.sublist.subset
  exact List.mem_append_right p (List.mem_singleton_self _)

theorem rawLevel_pairwise (W : Set G) (p : List (List ℕ)) (n : ℕ) :
    ∀ a ∈ InnerLevels.RawFiber (Level W p) n, a.1.Pairwise (· < ·) := by
  intro a ha
  exact level_body_pairwise ha

end Levels
end Erdos591.Negative.Exact
