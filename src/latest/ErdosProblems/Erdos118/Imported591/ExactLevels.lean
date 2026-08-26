import ErdosProblems.Erdos118.Imported591.ExactOuterLevels
import ErdosProblems.Erdos118.Imported591.InnerLevels
import ErdosProblems.Erdos118.Imported591.LexPrefix

open Set Ordinal

namespace Erdos118.Negative.Exact.Levels

open WeakPigeon

/-!
The source's levels live one recursion step below `G_{omega^2}`.  In the
literal nested-list presentation, a level prefix is an outer prefix `p`, a
member of its level is the next `G_omega` block `a`, and the continuation
fiber is the set of exact good sequences extending `p ++ [a]`.

This file deliberately keeps these three objects separate.  In particular,
the level is ordered by raw shortlex (`SL`), exactly as `G_omega` is, while
continuation fibers retain the ambient order on exact height-two sequences.
-/

/-- Exact good sequences in `W` whose outer block list extends `p`. -/
def Fiber (W : Set G) (p : List (List ℕ)) : Set G :=
  {x | x ∈ W ∧ p <+: x.1}

@[simp] theorem mem_fiber {W : Set G} {p : List (List ℕ)} {x : G} :
    x ∈ Fiber W p ↔ x ∈ W ∧ p <+: x.1 := Iff.rfl

/-- The continuation fiber after choosing the next `G_omega` block `a`. -/
def Child (W : Set G) (p : List (List ℕ)) (a : List ℕ) : Set G :=
  Fiber W (p ++ [a])

/-- The source level `L(W,p)`, represented by the bodies of its literal
`G_omega` blocks and equipped with their shortlex order. -/
def Level (W : Set G) (p : List (List ℕ)) :
    Set InnerLevels.OrderedSL :=
  {a | (Child W p a).Nonempty}

@[simp] theorem mem_level {W : Set G} {p : List (List ℕ)}
    {a : InnerLevels.OrderedSL} :
    a ∈ Level W p ↔ (Child W p a).Nonempty := Iff.rfl

theorem child_subset_fiber (W : Set G) (p : List (List ℕ)) (a : List ℕ) :
    Child W p a ⊆ Fiber W p := by
  rintro x ⟨hxW, hpa⟩
  exact ⟨hxW, (List.prefix_append p [a]).trans hpa⟩

theorem mem_level_iff_exists (W : Set G) (p : List (List ℕ))
    (a : InnerLevels.OrderedSL) :
    a ∈ Level W p ↔ ∃ x : G, x ∈ W ∧
      p ++ [show List ℕ from a] <+: x.1 := by
  simp only [mem_level, Child, mem_fiber, Set.nonempty_def]

theorem child_nonempty_of_mem_level {W : Set G} {p : List (List ℕ)}
    {a : InnerLevels.OrderedSL} (ha : a ∈ Level W p) :
    (Child W p a).Nonempty := ha

theorem child_disjoint (W : Set G) (p : List (List ℕ))
    {a b : List ℕ} (hab : a ≠ b) :
    Disjoint (Child W p a) (Child W p b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  rcases hxa.2 with ⟨u, hu⟩
  rcases hxb.2 with ⟨v, hv⟩
  have h : p ++ [a] ++ u = p ++ [b] ++ v := hu.trans hv.symm
  have h' : a :: u = b :: v := by
    apply List.append_right_injective p
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  exact hab (List.cons.inj h').1

/-- Distinct level members occur in the same order as their continuation
fibers in the ambient exact good-sequence order. -/
theorem child_separated (W : Set G) (p : List (List ℕ))
    (hroot : ∀ x ∈ W, ∀ y ∈ W, x.1.length = y.1.length)
    {a b : List ℕ} (hab : SL a b) :
    ∀ x ∈ Child W p a, ∀ y ∈ Child W p b, x < y := by
  intro x hx y hy
  rcases hx.2 with ⟨u, hu⟩
  rcases hy.2 with ⟨v, hv⟩
  change List.Shortlex SL (show G2 from x.1) (show G2 from y.1)
  rw [List.shortlex_def]
  apply Or.inr
  refine ⟨hroot x hx.1 y hy.1, ?_⟩
  rw [← hu, ← hv, List.append_assoc, List.append_assoc]
  exact List.Lex.append_left SL (List.Lex.rel hab) p

/-- Restrict `W` to exactly the children selected by `A` at prefix `p`. -/
def Thin (W : Set G) (p : List (List ℕ))
    (A : Set InnerLevels.OrderedSL) : Set G :=
  {x | x ∈ Fiber W p ∧
    ∃ a : InnerLevels.OrderedSL, a ∈ A ∧
      p ++ [show List ℕ from a] <+: x.1}

theorem thin_subset (W : Set G) (p : List (List ℕ))
    (A : Set InnerLevels.OrderedSL) : Thin W p A ⊆ W := by
  intro x hx
  exact hx.1.1

theorem thin_fiber (W : Set G) (p : List (List ℕ))
    (A : Set InnerLevels.OrderedSL) : Fiber (Thin W p A) p = Thin W p A := by
  ext x
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, hx.1.2⟩

theorem child_thin_of_mem (W : Set G) (p : List (List ℕ))
    (A : Set InnerLevels.OrderedSL) {a : InnerLevels.OrderedSL}
    (ha : a ∈ A) :
    Child (Thin W p A) p a = Child W p a := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1.1, hx.2⟩
  · intro hx
    refine ⟨?_, hx.2⟩
    exact ⟨child_subset_fiber W p a hx, a, ha, hx.2⟩

theorem level_thin (W : Set G) (p : List (List ℕ))
    (A : Set InnerLevels.OrderedSL) (hA : A ⊆ Level W p) :
    Level (Thin W p A) p = A := by
  ext a
  constructor
  · intro ha
    rcases ha with ⟨x, hx⟩
    rcases hx.1.2 with ⟨b, hbA, hpbx⟩
    have hsame : b = a := by
      by_contra hne
      exact Set.disjoint_left.mp (child_disjoint W p hne)
        ⟨hx.1.1.1, hpbx⟩ ⟨hx.1.1.1, hx.2⟩
    simpa [hsame] using hbA
  · intro ha
    have hnonempty : (Child W p a).Nonempty := hA ha
    change (Child (Thin W p A) p a).Nonempty
    rw [child_thin_of_mem W p A ha]
    exact hnonempty

/-! ## Maximal prefixes inside a large source level -/

/-- The empty body prefix does not restrict a fixed raw length. -/
theorem lexFiber_nil {n : ℕ} (A : Set (RawLevel n)) :
    LexPrefix.Fiber A [] = A := by
  ext x
  simp [LexPrefix.Fiber]

/-- If a source level has type above `omega^(k+1)`, then after fixing its
box coordinate (the block length) it contains a maximal body prefix of type
`omega^k`.  This combines the source's fixed-level extraction with the
finite maximal-prefix lemma, and is the exact interface used in Lemma 9.31. -/
theorem exists_level_maximal_prefix {W : Set G} {p : List (List ℕ)}
    {k : ℕ} (hlevel : ω ^ ((k + 1 : ℕ) : Ordinal) < typeLT (Level W p)) :
    ∃ (n : ℕ) (u : List ℕ), u.length ≤ n ∧
      typeLT (LexPrefix.Fiber
        (InnerLevels.RawFiber (Level W p) n) u) = ω ^ (k : Ordinal) ∧
      ∀ a, typeLT (LexPrefix.Child
        (InnerLevels.RawFiber (Level W p) n) u a) < ω ^ (k : Ordinal) := by
  obtain ⟨n, hn⟩ := InnerLevels.exists_large_rawFiber hlevel
  have hlarge : ω ^ (k : Ordinal) ≤
      typeLT (LexPrefix.Fiber
        (InnerLevels.RawFiber (Level W p) n) []) := by
    rw [lexFiber_nil]
    exact hn
  obtain ⟨u, -, hun, hutype, humax⟩ :=
    LexPrefix.exists_maximal_prefix
      (InnerLevels.RawFiber (Level W p) n) [] (by simp) hlarge
  exact ⟨n, u, hun, hutype, humax⟩

/-- The corresponding arbitrarily-high descent from a maximal `omega^k`
body prefix to a maximal `omega^j` body prefix. -/
theorem exists_level_maximal_prefix_above
    {W : Set G} {p : List (List ℕ)} {n k j : ℕ}
    (u : List ℕ) (hun : u.length ≤ n)
    (hutype : typeLT (LexPrefix.Fiber
      (InnerLevels.RawFiber (Level W p) n) u) = ω ^ (k : Ordinal))
    (humax : ∀ a, typeLT (LexPrefix.Child
      (InnerLevels.RawFiber (Level W p) n) u a) < ω ^ (k : Ordinal))
    (hjk : j < k) (bound : ℕ) :
    ∃ a v, bound < a ∧ u ++ [a] <+: v ∧ v.length ≤ n ∧
      typeLT (LexPrefix.Fiber
        (InnerLevels.RawFiber (Level W p) n) v) = ω ^ (j : Ordinal) ∧
      ∀ b, typeLT (LexPrefix.Child
        (InnerLevels.RawFiber (Level W p) n) v b) < ω ^ (j : Ordinal) := by
  exact LexPrefix.exists_maximal_prefix_above
    (InnerLevels.RawFiber (Level W p) n) u hun hutype humax hjk bound

end Erdos118.Negative.Exact.Levels
