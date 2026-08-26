-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.External

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Formalizing the elementary part of E2 (Erdős–Hajnal exact high-odd-girth)

`Erdos1177.E2_EH_oddgirth` states: for every uncountable cardinal `κ` and every
`s`, there is a graph `A` with `|V(A)| = χ(A) = κ` and no odd cycle of length
`≤ 2s+1`.

The genuinely deep content of this theorem is the **chromatic lower bound**
combined with the **odd-girth constraint** — the Erdős–Hajnal transfinite
construction, whose successor-cardinal step rests on a partition relation of
Erdős–Rado type that is not available in Mathlib.  Everything *around* that core
— the exactness of the cardinality `|V(A)| = κ` and the chromatic upper bound
`χ(A) ≤ κ` — is elementary and is formalized here, `sorry`-free, isolating
exactly the irreducible core.

* `colorableBy_of_mk_eq` — the chromatic upper bound: a graph on `κ` vertices is
  `κ`-colourable.
* `E2Core` — the irreducible Erdős–Hajnal content: for every uncountable `κ` and
  every `s`, a graph on at most `κ` vertices whose chromatic number is not below
  `κ` (not `θ`-colourable for any `θ < κ`) and with no short odd cycle.
* `E2_of_core : E2Core → E2_EH_oddgirth` — the reduction, proved here from
  `E2Core` by padding with isolated vertices to reach cardinality exactly `κ`
  and adding the trivial upper bound.

The missing ingredient for `E2Core` (`s ≥ 1`) is infinite partition calculus of
Erdős–Rado type.  `RequestProject/PartitionCalculus.lean` begins building that
foundation from scratch: it proves the infinite Ramsey theorem for pairs and,
more generally, for every finite exponent (`ℵ₀ → (ℵ₀)ⁿ_k`), which is the base of
the Erdős–Rado hierarchy the successor-cardinal step of `E2Core` builds on.
-/

open Cardinal

namespace Erdos1177

universe u

/-- Trivial upper bound: a simple graph on a vertex set of cardinality `κ` is
properly colourable with `κ` colours (colour each vertex by itself under a
bijection `V ≃ κ.out`). -/
theorem colorableBy_of_mk_eq {V : Type u} (A : SimpleGraph V) {κ : Cardinal.{u}}
    (h : Cardinal.mk V = κ) : (SimpleGraph.toHG A).ColorableBy κ := by
  have e : V ≃ κ.out := by
    apply Cardinal.outMkEquiv.symm.trans
    rw [h]
  refine ⟨e, ?_⟩
  intro edge he
  obtain ⟨x, y, hxy, rfl⟩ := he
  exact ⟨x, by simp, y, by simp, fun hc => (A.ne_of_adj hxy) (e.injective hc)⟩

/-- **The irreducible Erdős–Hajnal core.**  For every uncountable cardinal `κ`
and every `s`, there is a graph `G` on at most `κ` vertices whose chromatic
number is not below `κ` — i.e. `G` is not `θ`-colourable for any `θ < κ` — and
which has no odd cycle of length `≤ 2s+1`.

This is exactly the content of the Erdős–Hajnal high-odd-girth theorem stripped
of the elementary cardinality/upper-bound bookkeeping.  It is carried here as a
named proposition (never an `axiom`); its proof is the transfinite construction
of Erdős–Hajnal, Acta Math. Hungar. 17 (1966), Thm 7.4. -/
def E2Core : Prop :=
  ∀ (κ : Cardinal.{u}), ℵ₀ < κ → ∀ (s : ℕ),
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G s

/-- The padded graph: `G` on `W`, together with `κ.out`-many isolated vertices,
living on the sum type `W ⊕ κ.out`.  Adjacency holds only between two vertices
of the `W`-part that are `G`-adjacent. -/
def paddedGraph {W : Type u} (G : SimpleGraph W) (κ : Cardinal.{u}) :
    SimpleGraph (W ⊕ κ.out) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | _, _ => False
  symm := by
    constructor
    rintro (x | x) (y | y) h <;> simp_all [G.adj_comm]
  loopless := ⟨by rintro (x | x) h <;> simp_all⟩

/-
**The reduction `E2Core → E2_EH_oddgirth`.**  Given the irreducible core,
pad with isolated vertices to reach cardinality exactly `κ` and supply the
trivial chromatic upper bound; the odd-girth constraint and the chromatic lower
bound transfer from the core graph unchanged.
-/
theorem E2_of_core (h : E2Core.{u}) : E2_EH_oddgirth.{u} := by
  intro κ hκ s;
  obtain ⟨ W, G, hW, hG, hgirth ⟩ := h κ hκ s;
  refine' ⟨ W ⊕ κ.out, paddedGraph G κ, _, _, _ ⟩;
  · simp +decide [ Cardinal.mk_sum, Cardinal.mk_out ];
    grind +suggestions;
  · refine' ⟨ _, _ ⟩;
    · convert! colorableBy_of_mk_eq ( paddedGraph G κ ) _;
      simp +decide [ Cardinal.mk_sum, Cardinal.mk_out ];
      rw [ Cardinal.add_eq_right ];
      · exact le_of_lt hκ;
      · exact hW;
    · intro θ hθ hcolorable
      obtain ⟨c, hc⟩ := hcolorable
      have hcolorable_G : (SimpleGraph.toHG G).ColorableBy θ := by
        use fun w => c (Sum.inl w);
        intro e he; obtain ⟨ x, y, hxy, rfl ⟩ := he; specialize hc ( { Sum.inl x, Sum.inl y } : Set ( W ⊕ Quotient.out κ ) ) ; simp_all +decide [ SimpleGraph.toHG ] ;
        exact hc <| Or.inl ⟨ x, Or.inl ⟨ y, by simpa [ paddedGraph ] using! hxy, by simp +decide [ Set.pair_comm ] ⟩ ⟩
      exact hG θ hθ hcolorable_G;
  · intro m hm₁ hm₂ hm₃ ⟨ v, hv₁, hv₂ ⟩;
    -- Since $v$ is injective and $v i$ and $v (i + 1)$ are adjacent in the padded graph, they must both be in $W$.
    have hvW : ∀ i : ZMod m, ∃ w : W, v i = Sum.inl w := by
      intro i; specialize hv₂ i; rcases v_i : v i with ( _ | _ ) <;> simp_all +decide [ paddedGraph ] ;
    choose w hw using hvW;
    exact hgirth m hm₁ hm₂ hm₃ ⟨ w, fun i j hij => by have := hv₁ ( by aesop : v i = v j ) ; aesop, fun i => by have := hv₂ i; aesop ⟩

/-! ### Progress towards `E2Core`: the chromatic lower bound via the complete graph

The genuinely deep part of `E2Core` is producing, on `≤ κ` vertices, a graph
whose chromatic number is *as large as* `κ` **while** avoiding all short odd
cycles.  The chromatic lower bound alone (ignoring the odd-girth constraint) is
elementary: the complete graph on `κ` vertices already achieves chromatic number
exactly `κ`.  We record this as a reusable lemma and use it to discharge the
`s = 0` slice of `E2Core` completely.

The remaining, irreducible content of `E2Core` is the case `s ≥ 1`: forbidding
short odd cycles while keeping the chromatic number equal to the vertex count is
exactly the Erdős–Hajnal transfinite high-odd-girth construction, whose
successor-cardinal step rests on an Erdős–Rado-type partition relation that is
not available in Mathlib (see the file header). -/

/-- **Chromatic lower bound for the complete graph.**  If `|W| = κ` then the
complete graph `⊤` on `W` is not `θ`-colourable for any `θ < κ`: a proper
colouring of a complete graph is injective, forcing `κ = |W| ≤ θ`. -/
theorem completeGraph_not_colorableBy {W : Type u} {κ : Cardinal.{u}}
    (h : Cardinal.mk W = κ) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (⊤ : SimpleGraph W)).ColorableBy θ := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro x y hxy
    by_contra hne
    obtain ⟨u, hu, v, hv, huv⟩ := hc ({x, y} : Set W) ⟨x, y, by simpa using! hne, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
  have : κ ≤ θ := by
    rw [← h]
    calc Cardinal.mk W ≤ Cardinal.mk θ.out := Cardinal.mk_le_of_injective hinj
      _ = θ := Cardinal.mk_out θ
  exact absurd this (not_le.mpr hθ)

/-- **The `s = 0` slice of `E2Core`, discharged unconditionally.**  When no odd
cycles need to be forbidden (`s = 0`, so `NoShortOddCycle _ 0` is vacuous), the
complete graph on `κ.out` realizes the required chromatic lower bound on exactly
`κ` vertices.  This is the `s = 0` case of `E2Core`; the deep content of
`E2Core` is the amplification to `s ≥ 1` (high odd girth).

(The uncountability hypothesis `ℵ₀ < κ` present in `E2Core` is not needed for the
`s = 0` slice, so it is dropped here for a cleaner, more general statement.) -/
theorem E2Core_zero (κ : Cardinal.{u}) :
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G 0 := by
  refine ⟨κ.out, ⊤, le_of_eq (Cardinal.mk_out κ), ?_, ?_⟩
  · intro θ hθ
    exact completeGraph_not_colorableBy (Cardinal.mk_out κ) hθ
  · -- `NoShortOddCycle _ 0` is vacuous: no `m` satisfies `3 ≤ m ≤ 1`.
    intro m _ hm3 hm1
    omega

end Erdos1177
