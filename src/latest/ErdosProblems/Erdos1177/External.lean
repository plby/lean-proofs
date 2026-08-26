-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Results
import ErdosProblems.Erdos1177.PropertyP
import ErdosProblems.Erdos1177.DeltaRho

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The external theorem interface: E1–E5

The paper arXiv:2606.24882 assembles its two headline results from five theorems
imported **verbatim from the literature** (its §2.2 "External theorem interface"
and its Appendix "Exact interfaces to the imported theorems").  This file states
those five theorems as *explicit, faithfully-typed named propositions*, each with
its verified source, so that the paper's external interface is transparent and
auditable in Lean.  Verified bibliographic details and proof strategies for all
five are collected in `SOURCES_E1_E5.md`.

**None of E1–E5 is in Mathlib**, and each depends on infrastructure that is
itself a substantial standalone formalization (Erdős–Rado for E1; the
Erdős–Hajnal transfinite high-odd-girth construction for E2; the generalized
Specker graph and property `P` for E3; the Erdős–Hajnal base case plus Zykov
submultiplicativity and a delta-system argument for E4; the Hajnal–Komjáth
argument for E5).  They are therefore carried as **explicit hypotheses, never as
`axiom`s** (an `axiom` would compromise soundness).  This is exactly the paper's
own "external theorem interface" methodology.

The statements below are the precise consequences used by the paper:

* `E1_EHR_nonlinear` — Erdős–Hajnal–Rothschild (`thm:EHR-nonlinear`):
  a non-linear finite triple system is non-obligatory.
  Source: Erdős–Hajnal–Rothschild, LNM 337 (1973), Thm 2, p. 532.
* `E2_EH_oddgirth` — Erdős–Hajnal (`thm:EH-odd-girth`): exact high-odd-girth
  graphs of prescribed uncountable size and chromatic number.
  Source: Erdős–Hajnal, Acta Math. Hungar. 17 (1966), Thm 7.4, p. 76
  (= Erdős–Galvin–Hajnal, Bolyai 10 (1975), Thm C, p. 428).
* `E3_EGH_P` — Erdős–Galvin–Hajnal (`thm:EGH-P`): the simultaneous
  common-colour edge-labelling property `P` at `δ(ρ)`.
  Source: Erdős–Galvin–Hajnal, Bolyai 10 (1975), Def 6.2 p. 448 & Cor 9.7 p. 461.
* `E4_Reiher` — Reiher (`thm:Reiher`): the private expansion `K_{n,n}⁺` is
  obligatory.  Source: C. Reiher, *Obligatory hypergraphs*, arXiv:2403.11223,
  Proc. AMS (to appear), Thm 1.2.
* `E5_HK_loose7` — Hajnal–Komjáth: the loose `7`-cycle is linearly obligatory.
  Source: A. Hajnal, P. Komjáth, Acta Math. Hungar. 119 (2008), 1–13
  (cycle convention in Reiher's girth survey arXiv:2403.13571, §3.7).
-/

open Cardinal

namespace Erdos1177

universe u

/-! ### E1 — Erdős–Hajnal–Rothschild (nonlinear ⟹ non-obligatory) -/

/-- **E1** (`thm:EHR-nonlinear`).  A finite triple system that is *not linear*
(i.e. has two distinct edges meeting in at least two vertices) is non-obligatory.
Equivalently, every obligatory finite triple system is linear.

Source: P. Erdős, A. Hajnal, B. L. Rothschild, *On chromatic number of graphs
and set-systems*, LNM 337 (1973), Theorem 2, p. 532.  The witness is an
uncountably chromatic *linear* triple system (Reiher records the explicit
construction on `[(2^ℵ₀)⁺]²`), whose uncountable chromatic number comes from the
Erdős–Rado partition relation `(2^ℵ₀)⁺ → (3)²_{ℵ₀}`. -/
def E1_EHR_nonlinear : Prop :=
  ∀ (F : FTS), ¬ F.Linear → ¬ FTS.Obligatory.{u} F

/-! ### E2 — Erdős–Hajnal (exact high-odd-girth graphs) -/

/-- `A` has *no short odd cycle up to `2s+1`*: for every odd `m` with
`3 ≤ m ≤ 2s+1` there is no `m`-cycle subgraph, i.e. no injective cyclic sequence
`v : ZMod m → V` with consecutive vertices adjacent. -/
def NoShortOddCycle {V : Type u} (A : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ m : ℕ, Odd m → 3 ≤ m → m ≤ 2 * s + 1 →
    ¬ ∃ v : ZMod m → V, Function.Injective v ∧ ∀ i : ZMod m, A.Adj (v i) (v (i + 1))

/-- **E2** (`thm:EH-odd-girth`).  For every uncountable cardinal `κ` and every
`s`, there is a graph `A` with `|V(A)| = χ(A) = κ` that contains no odd cycle of
length at most `2s+1`.  (`χ` is the chromatic number of the associated
hypergraph `SimpleGraph.toHG A`.)

Source: P. Erdős, A. Hajnal, Acta Math. Hungar. 17 (1966), Theorem 7.4, p. 76
(restated as Theorem C, p. 428 of Erdős–Galvin–Hajnal, Bolyai 10, 1975). -/
def E2_EH_oddgirth : Prop :=
  ∀ (κ : Cardinal.{u}), ℵ₀ < κ → ∀ (s : ℕ),
    ∃ (V : Type u) (A : SimpleGraph V),
      Cardinal.mk V = κ ∧ (SimpleGraph.toHG A).HasChromatic κ ∧ NoShortOddCycle A s

/-! ### E3 — Erdős–Galvin–Hajnal (property P for the generalized Specker graph) -/

/-- **E3** (`thm:EGH-P`).  For every infinite cardinal `ρ` there is a graph `S`
with an edge labelling by a set of size `ρ` satisfying the simultaneous
common-colour property `P` at `δ(ρ) = min{δ : ρ^δ > ρ}`.  In the paper `S` is the
generalized Specker graph `GS₂(ρ)` and the labels are `ρ`.

Source: P. Erdős, F. Galvin, A. Hajnal, Bolyai 10 (1975), Definition 6.2, p. 448
and Corollary 9.7, p. 461 (with `n = 2`). -/
def E3_EGH_P : Prop :=
  ∀ (ρ : Cardinal.{u}), ℵ₀ ≤ ρ →
    ∃ (S : Type u) (G : SimpleGraph S) (I : Type u),
      Cardinal.mk S = ρ ∧ Cardinal.mk I = ρ ∧
        ∃ ℓ : G.edgeSet → I, SimpleGraph.PropertyP G ℓ (deltaRho ρ)

/-! ### E4 — Reiher (K_{n,n}⁺ is obligatory) -/

open Classical in
/-- **E4** (`thm:Reiher`).  For every `n`, the private-vertex triple-system
expansion `K_{n,n}⁺` of the complete bipartite graph is obligatory.

Source: C. Reiher, *Obligatory hypergraphs*, arXiv:2403.11223, Proc. AMS (to
appear), Theorem 1.2 (case `k = 3`). -/
def E4_Reiher : Prop :=
  ∀ n : ℕ,
    FTS.Obligatory.{u} (graphExpansion (completeBipartiteGraph (Fin n) (Fin n)))

open Classical in
/-- The complete bipartite graph is `2`-colourable. -/
theorem completeBipartite_colorable_two (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin n)).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => Sum.elim (fun _ => 0) (fun _ => 1) x) ?_⟩
  rintro (a | a) (b | b) hadj <;> simp_all [completeBipartiteGraph]

open Classical in
/-- **E4 is exactly the `K_{n,n}` instance of `ReiherExpansion`.**  The carried
hypothesis `ReiherExpansion` (every bipartite `J⁺` obligatory) implies `E4`;
conversely `E4` implies `ReiherExpansion` by Reiher's subhypergraph passage
(`J` bipartite `⟹ J ↪ K_{n,n} ⟹ J⁺ ↪ K_{n,n}⁺`), which is the content beyond
this file.  This shows the carried hypothesis is precisely the published
Theorem 1.2. -/
theorem E4_Reiher_of_reiherExpansion (h : ReiherExpansion.{u}) : E4_Reiher.{u} :=
  fun n => h (J := completeBipartiteGraph (Fin n) (Fin n)) (completeBipartite_colorable_two n)

/-! #### Zykov submultiplicativity ingredients used in the proof of E4

Reiher's proof of E4 (Theorem 1.2) rests on the submultiplicativity of the
chromatic number (Zykov) and its Corollary 2.2.  These two-piece / difference
forms are elementary and fully proved here; they are the reusable colouring
core of the E4 argument. -/

/-- Colourability is monotone under removing edges: a colouring proper for a
larger edge family is proper for a smaller one. -/
theorem colorableBy_mono {V : Type u} {E F : Set (Set V)} (hEF : E ⊆ F)
    {θ : Cardinal.{u}} (h : (⟨F⟩ : Hypergraph V).ColorableBy θ) :
    (⟨E⟩ : Hypergraph V).ColorableBy θ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun e he => hc e (hEF he)⟩

/-- **Zykov, two-piece form.**  If a hypergraph's edge set splits as `E' ∪ E''`
with both parts `ℵ₀`-colourable, then the whole is `ℵ₀`-colourable (a special case
of `χ(H) ≤ ∏ᵢ χ(V, Eᵢ)`, since `ℵ₀ · ℵ₀ = ℵ₀`). -/
theorem colorableBy_aleph0_union {V : Type u} (E' E'' : Set (Set V))
    (h' : (⟨E'⟩ : Hypergraph V).ColorableBy ℵ₀)
    (h'' : (⟨E''⟩ : Hypergraph V).ColorableBy ℵ₀) :
    (⟨E' ∪ E''⟩ : Hypergraph V).ColorableBy ℵ₀ := by
  obtain ⟨c', hc'⟩ := h'
  obtain ⟨c'', hc''⟩ := h''
  have hle : Cardinal.mk ((ℵ₀ : Cardinal.{u}).out × (ℵ₀ : Cardinal.{u}).out)
      ≤ Cardinal.mk ((ℵ₀ : Cardinal.{u}).out) := by
    simp only [Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id]
    exact le_of_eq Cardinal.aleph0_mul_aleph0
  obtain ⟨g, hg⟩ := hle
  refine ⟨fun v => g (c' v, c'' v), ?_⟩
  intro e he
  rcases he with he | he
  · obtain ⟨u, hu, v, hv, huv⟩ := hc' e he
    exact ⟨u, hu, v, hv, fun h => huv (congrArg Prod.fst (hg h))⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hc'' e he
    exact ⟨u, hu, v, hv, fun h => huv (congrArg Prod.snd (hg h))⟩

/-- **Reiher's Corollary 2.2.**  If `H = (V, E)` has uncountable chromatic number
and a subfamily `E'` is `ℵ₀`-colourable, then `(V, E \ E')` still has uncountable
chromatic number. -/
theorem uncountablyChromatic_diff {V : Type u} (E E' : Set (Set V))
    (hE : (⟨E⟩ : Hypergraph V).UncountablyChromatic)
    (hE' : (⟨E'⟩ : Hypergraph V).ColorableBy ℵ₀) :
    (⟨E \ E'⟩ : Hypergraph V).UncountablyChromatic := by
  intro hdiff
  exact hE (colorableBy_mono
    (by intro x hx; by_cases h : x ∈ E' <;> [left; right] <;> simp_all)
    (colorableBy_aleph0_union E' (E \ E') hE' hdiff))

/-! ### E5 — Hajnal–Komjáth (the linearly obligatory loose 7-cycle) -/

/-- A finite triple system is *linearly obligatory* if it occurs in every
**linear** triple system of uncountable chromatic number. -/
def FTS.LinearlyObligatory (F : FTS) : Prop :=
  ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.Linear → H.UncountablyChromatic → F.Embeds H

open Classical in
/-- The *loose (private-vertex) 7-cycle* `C_7^{(3)}`: `14` vertices `x_i, y_i`
(`i ∈ ℤ/7`) and `7` edges `{x_i, x_{i+1}, y_i}`.  Here `x_i = Sum.inl i` and
`y_i = Sum.inr i`. -/
noncomputable def looseCycle7 : FTS where
  V := Fin 7 ⊕ Fin 7
  edges := (Finset.univ : Finset (Fin 7)).image
      (fun i => ({Sum.inl i, Sum.inl (i + 1), Sum.inr i} : Finset (Fin 7 ⊕ Fin 7)))
  card3 := by
    have hne : ∀ j : Fin 7, j ≠ j + 1 := by decide
    intro e he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨i, rfl⟩ := he
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hne i (Sum.inl_injective h), fun h => Sum.inl_ne_inr h⟩

/-- **E5**.  The loose `7`-cycle `C_7^{(3)}` is linearly obligatory: it occurs in
every linear triple system of uncountable chromatic number.

Source: A. Hajnal, P. Komjáth, *Obligatory subsystems of triple systems*, Acta
Math. Hungar. 119 (2008), 1–13 (the loose cycle `C_n^{(3)}` is linearly
obligatory for `n ∉ {2,3,5}`; here `n = 7`); cycle convention recorded in
C. Reiher, *Graphs of large girth*, arXiv:2403.13571, §3.7. -/
def E5_HK_loose7 : Prop :=
  FTS.LinearlyObligatory.{u} looseCycle7

end Erdos1177
