-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.E2Construction
import ErdosProblems.Erdos1177.ErdosHajnalGirth

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The general Erdős–Hajnal high-odd-girth graph `GS_k(κ)`

This file develops the general Erdős–Hajnal high-odd-girth construction, the
combinatorial engine behind the irreducible core `Erdos1177.E2Core` of E2, on top
of the `n = 1` (triangle-free) base case of `ErdosProblems.Erdos1177.ErdosHajnalGirth`.

**Construction.**  Fix `κ` and a parameter `k ≥ 2`.  Let `Pt = κ.ord.ToType`
(so `|Pt| = κ`).  The vertices are the strictly increasing `k`-tuples
`a = (a₀ < a₁ < ⋯ < a_{k-1})` of `Pt`.  Two tuples `a`, `b` are joined when the
`2k` coordinates interleave as the chain
```
  a₀ < a₁ < b₀ < a₂ < b₁ < a₃ < b₂ < ⋯ < a_{k-1} < b_{k-2} < b_{k-1}
```
(or symmetrically with `a`, `b` swapped).  Equivalently, using that each tuple
is already strictly increasing, the *cross* conditions are
`a_{i+1} < b_i` (for `i+1 < k`) and `b_i < a_{i+2}` (for `i+2 < k`).

For `k = 3` this is exactly the Erdős–Rado graph of `ErdosHajnalGirth`.

**Correction / warning.**  This interleaving generalization does **not** have odd
girth `2k-1`.  An earlier claim to that effect ("validated for `k ≤ 5`") was
*wrong*: `ErdosProblems.Erdos1177.Attic.E2OddGirthFalse` (`EHG.oddGirthGeneral_false`) exhibits
an explicit `5`-cycle in `graph 4 κ`, so already for `k = 4` there is an odd cycle
of length `2k-3 = 5`.  Thus `graph k κ` is high-chromatic but *not* a valid E2
witness; only its triangle-freeness (`k ≥ 3`, below) and its chromatic lower
bound hold.  E2 remains carried as the literature hypothesis `E2_EH_oddgirth`.

## What is proved here (`sorry`-free, axiom-clean)

* `graph` — the construction; `card_le` — `|V| ≤ κ`.
* `isEdge_coord_lt` — an oriented edge dominates coordinatewise (`a j < b j`);
  `isEdge_gap` — the shift/gap bound (`b l < a (l+2)`).  These are the two
  structural facts driving the odd-girth argument.
* `proj3` — the first-three-coordinates map is a graph homomorphism
  `graph k κ → ER60.graph κ`, so short odd cycles push down to the base case.
* `triangleFree` / `noShortOddCycle_one` — the general graph is triangle-free
  (no odd cycle of length `≤ 3`) for every `k ≥ 3`.

## Status of the high-odd-girth bound

The high-odd-girth bound (no odd cycle of length `≤ 2k-3`) is **false** for this
interleaving construction (`EHG.oddGirthGeneral_false`).  The genuine
Erdős–Hajnal high-odd-girth graph uses a different, "half-shift" edge relation
(on longer tuples) not formalized here.  The chromatic lower bound `χ = κ` for
general `k` *is* proved (`ErdosProblems.Erdos1177.EHGirthChromatic`,
`ErdosProblems.Erdos1177.Attic.E2CoreProof.not_colorableBy_general`).  E2 is carried by the paper
as the literature hypothesis `E2_EH_oddgirth`.
-/

open Cardinal Ordinal

namespace Erdos1177
namespace EHG

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {k : ℕ}

/-- Vertices: strictly increasing `k`-tuples of `Pt κ`. -/
abbrev Vtx (k : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin k → Pt κ // StrictMono t}

/-- The oriented interleaving edge relation:
`a₀ < a₁ < b₀ < a₂ < b₁ < ⋯ < a_{k-1} < b_{k-2} < b_{k-1}`, expressed via the
cross conditions (the within-tuple order is supplied by `StrictMono`). -/
def IsEdge (a b : Fin k → Pt κ) : Prop :=
  (∀ i : ℕ, (h : i + 1 < k) → a ⟨i + 1, h⟩ < b ⟨i, by omega⟩) ∧
  (∀ i : ℕ, (h : i + 2 < k) → b ⟨i, by omega⟩ < a ⟨i + 2, h⟩)

/-- Symmetric adjacency. -/
def Adjr (a b : Vtx k κ) : Prop := IsEdge a.1 b.1 ∨ IsEdge b.1 a.1

theorem isEdge_irrefl (hk : 2 ≤ k) (a : Fin k → Pt κ) (ha : StrictMono a) :
    ¬ IsEdge a a := by
  rintro ⟨h1, -⟩
  have := h1 0 (by omega)
  have hmono := ha (show (⟨0, by omega⟩ : Fin k) < ⟨1, by omega⟩ by
    simp [Fin.lt_def])
  exact absurd this (not_lt.mpr (le_of_lt hmono))

/-- The generalized Specker / Erdős–Hajnal graph on increasing `k`-tuples. -/
def graph (k : ℕ) (κ : Cardinal.{u}) (hk : 2 ≤ k) : SimpleGraph (Vtx k κ) where
  Adj a b := Adjr a b
  symm := by constructor; intro a b h; exact h.symm
  loopless := ⟨by
    rintro a (h | h) <;> exact isEdge_irrefl hk _ a.2 h⟩

/-! ### Cardinality -/

theorem card_le (hk : 1 ≤ k) (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx k κ) ≤ κ := by
  have h_card : #(Fin k → Pt κ) = κ ^ (k : ℕ) := by
    simp [Cardinal.mk_toType, Cardinal.card_ord]
  refine le_trans (Cardinal.mk_subtype_le _) ?_
  rw [h_card, Cardinal.power_nat_eq hκ]
  omega

/-! ### Structural lemmas driving the odd-girth argument -/

/-- Coordinatewise domination from an oriented edge: if `IsEdge a b` then
`a j < b j` for every coordinate `j`. -/
theorem isEdge_coord_lt (hk : 2 ≤ k) {a b : Fin k → Pt κ} (ha : StrictMono a)
    (hb : StrictMono b) (h : IsEdge a b) (j : Fin k) : a j < b j := by
  obtain ⟨h1, _⟩ := h
  have hjk : (j : ℕ) < k := j.2
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
  · have e1 : a j < a ⟨1, by omega⟩ := ha (by simp [Fin.lt_def, hj0])
    have e2 := h1 0 (by omega)
    have hb0 : (⟨0, by omega⟩ : Fin k) = j := by ext; simp [hj0]
    rw [hb0] at e2
    exact lt_trans e1 e2
  · have e1 := h1 (j - 1) (by omega)
    have e2 : b ⟨j - 1, by omega⟩ < b j := hb (by simp [Fin.lt_def]; omega)
    have hj1 : (⟨(j-1)+1, by omega⟩ : Fin k) = j := by ext; simp; omega
    rw [hj1] at e1
    exact lt_trans e1 e2

/-- The gap condition of an oriented edge: `IsEdge a b` gives `b l < a (l+2)`. -/
theorem isEdge_gap {a b : Fin k → Pt κ} (h : IsEdge a b) (l : ℕ) (hl : l + 2 < k) :
    b ⟨l, by omega⟩ < a ⟨l + 2, hl⟩ := h.2 l hl

/-! ### Triangle-freeness via projection to the base case

The first-three-coordinates map is a graph homomorphism into the `k = 3`
Erdős–Rado graph `ER60.graph`, so triangle-freeness of the base case lifts to all
`k ≥ 3`. -/

/-- The first three coordinates of a `k`-tuple (`k ≥ 3`) form an increasing
triple, i.e. a vertex of the base graph `ER60.graph κ`. -/
def proj3 (hk : 3 ≤ k) (a : Vtx k κ) : ER60.Vtx κ :=
  ⟨fun i : Fin 3 => a.1 ⟨i, by omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    exact a.2 (Fin.mk_lt_mk.mpr hij')⟩

/-- `proj3` sends oriented edges of `graph k κ` to oriented edges of the base
Erdős–Rado graph. -/
theorem isEdge_proj3 (hk : 3 ≤ k) {a b : Fin k → Pt κ}
    (ha : StrictMono a) (hb : StrictMono b) (h : IsEdge a b) :
    ER60.IsEdge (fun i : Fin 3 => a ⟨i, by omega⟩) (fun i : Fin 3 => b ⟨i, by omega⟩) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ha (by simp [Fin.lt_def])
  · exact h1 0 (by omega)
  · exact h2 0 (by omega)
  · exact h1 1 (by omega)
  · exact hb (by simp [Fin.lt_def])

/-- `proj3` is a graph homomorphism `graph k κ → ER60.graph κ`. -/
theorem proj3_adj (hk : 3 ≤ k) {a b : Vtx k κ}
    (h : (graph k κ (by omega)).Adj a b) :
    (ER60.graph κ).Adj (proj3 hk a) (proj3 hk b) := by
  rcases h with h | h
  · exact Or.inl (isEdge_proj3 hk a.2 b.2 h)
  · exact Or.inr (isEdge_proj3 hk b.2 a.2 h)

/-- **Triangle-freeness for every `k ≥ 3`.** -/
theorem triangleFree (hk : 3 ≤ k) (a b c : Vtx k κ)
    (hab : (graph k κ (by omega)).Adj a b)
    (hbc : (graph k κ (by omega)).Adj b c)
    (hac : (graph k κ (by omega)).Adj a c) : False :=
  ER60.triangleFree _ _ _ (proj3_adj hk hab) (proj3_adj hk hbc) (proj3_adj hk hac)

/-- No odd cycle of length `≤ 3` (i.e. `NoShortOddCycle (graph k κ) 1`) for
every `k ≥ 3`. -/
theorem noShortOddCycle_one (hk : 3 ≤ k) :
    NoShortOddCycle (graph k κ (by omega)) 1 := by
  intro m hm₁ hm₂ hm₃
  interval_cases m
  simp_all only [not_exists, not_and, not_forall]
  rintro x hx_inj
  by_contra h_contra
  push_neg at h_contra
  exact triangleFree hk _ _ _ (h_contra 0) (h_contra 1)
    ((h_contra 2).symm)

/-! ### The chromatic lower bound (Erdős–Rado peeling, general `k`)

Generalizes `ER60.not_colorableBy` (the `k = 3` case) to arbitrary `k`. -/

/-- Colourability transfers down initial segments: an order embedding
`Pt μ ↪o Pt κ` induces a coordinatewise graph embedding `graph k μ → graph k κ`,
and a proper colouring pulls back.  (Generalizes `ER60.colorableBy_of_le`.) -/
theorem colorableBy_of_le (hk : 2 ≤ k) {μ : Cardinal.{u}} (hμκ : μ ≤ κ)
    {θ : Cardinal.{u}}
    (h : (SimpleGraph.toHG (graph k κ hk)).ColorableBy θ) :
    (SimpleGraph.toHG (graph k μ hk)).ColorableBy θ := by
  obtain ⟨e, -⟩ : ∃ _ : Pt μ ↪o Pt κ, True :=
    ⟨Classical.choice (ER60.exists_pt_orderEmbedding hμκ), trivial⟩
  obtain ⟨c, hc⟩ := h
  have hadjκ : ∀ a b : Vtx k κ, (graph k κ hk).Adj a b → c a ≠ c b := by
    intro a b hab
    exact (toHG_proper_iff _ c).1 hc a b hab
  refine ⟨fun a => c ⟨fun i => e (a.1 i), e.strictMono.comp a.2⟩, ?_⟩
  rw [toHG_proper_iff]
  intro x y hxy
  refine hadjκ ⟨fun i => e (x.1 i), e.strictMono.comp x.2⟩
    ⟨fun i => e (y.1 i), e.strictMono.comp y.2⟩ ?_
  rcases hxy with h | h
  · refine Or.inl ⟨fun i hi => ?_, fun i hi => ?_⟩
    · exact e.strictMono (h.1 i hi)
    · exact e.strictMono (h.2 i hi)
  · refine Or.inr ⟨fun i hi => ?_, fun i hi => ?_⟩
    · exact e.strictMono (h.1 i hi)
    · exact e.strictMono (h.2 i hi)

/-
**Remaining chromatic lower bound.**  The exact chromatic lower bound
`χ(graph k κ) = κ` (i.e. `graph k κ` is not `θ`-colourable for any `θ < κ`) is,
for general `k`, the Erdős–Rado transfinite `2k`-level cofinal "peeling"
argument generalizing `ER60.not_colorableBy_regular`.  The base case `k = 3` is
fully proved in `ErdosProblems.Erdos1177.ErdosHajnalGirth`; `colorableBy_of_le` above is
the general-`k` initial-segment reduction that would feed the regular-cardinal
case.  The remaining piece is the depth-`k` cofinal-colour recursion, carried by
the paper as the literature input E2.
-/

end EHG
end Erdos1177
