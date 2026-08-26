-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.E2Construction
import ErdosProblems.Erdos1177.ErdosHajnalGirth

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The genuine Erdős–Hajnal / generalized Specker high-odd-girth graph `GS_n(κ)`

This file develops the **correct** Erdős–Hajnal high-odd-girth construction, the
generalized Specker graph `GS_n(κ)` of Erdős–Galvin–Hajnal (Bolyai 10, 1975,
Definition 8.2), on top of the `n = 1` (triangle-free) base case
`ErdosProblems.Erdos1177.ErdosHajnalGirth`.

**Construction (Def. 8.2).**  Fix `κ` and a parameter `n ≥ 1`.  Let
`Pt = κ.ord.ToType` (so `|Pt| = κ`).  Put `L = L n = n² + n + 1`.  The vertices
are the strictly increasing `L`-tuples `u = (u₀ < u₁ < ⋯ < u_{L-1})` of `Pt`.
Two tuples `u`, `v` are joined when the coordinates interleave as the chain
```
  u_n < v_0 < u_{n+1} < v_1 < u_{n+2} < v_2 < ⋯ < u_{n²+n} < v_{n²}
```
(or symmetrically with `u`, `v` swapped).  Concretely the oriented edge
`IsEdge u v` (with `u` "below") is
```
  (∀ t ≤ n²,   u_{n+t} < v_t)   ∧   (∀ t < n²,   v_t < u_{n+t+1}).
```

For `n = 1` (so `L = 3`) this is exactly the Erdős–Rado graph of
`ErdosHajnalGirth` (the chain `u₁ < v₀ < u₂ < v₁`, with `u₀ < u₁` and `v₁ < v₂`
supplied by monotonicity).

The key facts (Lemma 8.3) are:
* `card_le` — `|V| ≤ κ`;
* no odd cycle `C_{2i+1}` for `1 ≤ i ≤ n` (`NoShortOddCycle (graph n κ) n`);
* the chromatic lower bound `χ(GS_n(κ)) = κ`.

This file establishes the construction, the cardinality bound, and the two
"index comparison" workhorse lemmas `edge_lt_of_index_le` and
`edge_gt_of_index_ge` that drive the odd-girth argument.  The odd-girth theorem
itself is in `ErdosProblems.Erdos1177.GSnOddGirth` and the chromatic bound in
`ErdosProblems.Erdos1177.GSnChromatic`.
-/

open Cardinal Ordinal

namespace Erdos1177
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

/-- The tuple length `L n = n² + n + 1`. -/
abbrev L (n : ℕ) : ℕ := n * n + n + 1

theorem L_pos (n : ℕ) : 0 < L n := by positivity

/-- `n + t < L n` when `t ≤ n²`. -/
theorem nt_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : n + t < L n := by
  simp only [L]; omega

/-- `t < L n` when `t ≤ n²`. -/
theorem t_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : t < L n := by
  simp only [L]; omega

/-- Vertices: strictly increasing `L n`-tuples of `Pt κ`. -/
abbrev Vtx (n : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin (L n) → Pt κ // StrictMono t}

/-- The oriented interleaving edge relation `IsEdge u v` (`u` below):
`u_n < v_0 < u_{n+1} < v_1 < ⋯ < u_{n²+n} < v_{n²}`, expressed via the two
families of cross conditions. -/
def IsEdge (u v : Fin (L n) → Pt κ) : Prop :=
  (∀ t : ℕ, (h : t ≤ n * n) → u ⟨n + t, nt_lt n h⟩ < v ⟨t, t_lt n h⟩) ∧
  (∀ t : ℕ, (h : t < n * n) → v ⟨t, t_lt n (le_of_lt h)⟩ < u ⟨n + t + 1, by simp only [L]; omega⟩)

/-- Symmetric adjacency. -/
def Adjr (u v : Vtx n κ) : Prop := IsEdge u.1 v.1 ∨ IsEdge v.1 u.1

theorem isEdge_irrefl (a : Fin (L n) → Pt κ) (ha : StrictMono a) : ¬ IsEdge a a := by
  rintro ⟨h1, -⟩
  have h := h1 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at h
  have hle : a ⟨0, t_lt n (Nat.zero_le _)⟩ ≤ a ⟨n, nt_lt n (Nat.zero_le _)⟩ :=
    ha.monotone (by simp only [Fin.le_def]; omega)
  exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)

/-- The generalized Specker / Erdős–Hajnal graph `GS_n(κ)` on increasing
`L n`-tuples. -/
def graph (n : ℕ) (κ : Cardinal.{u}) : SimpleGraph (Vtx n κ) where
  Adj u v := Adjr u v
  symm := by constructor; intro a b h; exact h.symm
  loopless := ⟨by rintro a (h | h) <;> exact isEdge_irrefl _ a.2 h⟩

/-! ### Cardinality -/

theorem card_le (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx n κ) ≤ κ := by
  have h_card : #(Fin (L n) → Pt κ) = κ ^ (L n : ℕ) := by
    simp +decide [Cardinal.mk_toType, Cardinal.card_ord]
    norm_cast
  refine le_trans (Cardinal.mk_subtype_le _) ?_
  rw [h_card, Cardinal.power_nat_eq]
  · exact hκ
  · exact L_pos n

/-! ### The index-comparison workhorse lemmas

In an oriented edge `IsEdge u v` (`u` below, both strictly increasing), the order
between a coordinate `u_a` and a coordinate `v_b` is decided entirely by comparing
the indices `a` and `b + n`:
* `u_a < v_b` whenever `a ≤ b + n`   (`edge_lt_of_index_le`);
* `v_b < u_a` whenever `a ≥ b + n + 1` (`edge_gt_of_index_ge`).
These two are complementary and capture every cross-relation of an edge. -/

/-
If `IsEdge u v` and `a ≤ b + n` (with `a, b` valid indices), then
`u_a < v_b`.  Proof: pick `t = a - n` (or `t = 0` if `a ≤ n`); then
`u_a ≤ u_{n+t} < v_t ≤ v_b`.
-/
theorem edge_lt_of_index_le {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : a ≤ b + n) :
    u ⟨a, ha⟩ < v ⟨b, hb⟩ := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t ≤ n * n ∧ a ≤ n + t ∧ t ≤ b := by
    exact ⟨ Min.min ( a - n ) b, le_trans ( min_le_left _ _ ) ( Nat.sub_le_of_le_add <| by linarith [ show L n = n * n + n + 1 from rfl ] ), by omega, min_le_right _ _ ⟩;
  exact lt_of_le_of_lt ( hu.monotone ( by exact Nat.le_trans ( Nat.le_refl _ ) ht.2.1 ) ) ( lt_of_lt_of_le ( h.1 t ht.1 ) ( hv.monotone ( by exact Nat.le_trans ht.2.2 ( Nat.le_refl _ ) ) ) )

/-
If `IsEdge u v` and `a ≥ b + n + 1` (with `a, b` valid indices), then
`v_b < u_a`.  Proof: pick `t = b`; then `v_b < u_{n+b+1} ≤ u_a` (the hypothesis
`a ≥ b + n + 1` together with `a < L n` forces `b < n²`, so `v_b < u_{n+b+1}`
is a valid edge inequality).
-/
theorem edge_gt_of_index_ge {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : b + n + 1 ≤ a) :
    v ⟨b, hb⟩ < u ⟨a, ha⟩ := by
  exact lt_of_lt_of_le ( h.2 b ( by unfold L at *; omega ) ) ( hu.monotone ( by exact Nat.le_trans ( by simp +arith +decide ) hab ) )

/-- An oriented edge dominates in the `0`-coordinate: `IsEdge u v ⟹ u₀ < v₀`. -/
theorem isEdge_fst_lt {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) :
    u ⟨0, L_pos n⟩ < v ⟨0, L_pos n⟩ :=
  edge_lt_of_index_le hu hv h (L_pos n) (L_pos n) (by omega)

/-- The two orientations of an edge are mutually exclusive. -/
theorem not_isEdge_both {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) : ¬ IsEdge v u := by
  intro h'
  have h1 := isEdge_fst_lt hu hv h
  have h2 := isEdge_fst_lt hv hu h'
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

end GSn
end Erdos1177
