/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 753.
https://www.erdosproblems.com/forum/thread/753

Informal authors:
- Noga Alon

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/753#post-5373
- https://gist.githubusercontent.com/madeve-unipi/80eaf8008c7c798b4f7b5baeb8c1812b/raw/70704b54755e9012597c99bab7db153786abfa8a/Erdos753.lean
-/
/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered

namespace Erdos753

/-!
# Erdős Problem 753: List Chromatic Numbers of Complementary Graphs

## Problem Statement (Erdős 753)

Does there exist some constant `c > 0` such that `χ_L(G) + χ_L(Gᶜ) > n^{1/2+c}`
for every graph `G` on `n` vertices?

## Answer: NO

Following Alon's paper "Choice numbers of graphs; a probabilistic approach" (1993),
we show that for every `n`, there exists a graph `G` on `n` vertices such that
`χ_L(G) + χ_L(Gᶜ) = O(√(n log n))`, which is `o(n^{1/2+c})` for any `c > 0`.

The construction uses the **complete equipartite graph** `K_{m×r}` (the complete
`r`-partite graph with `m` vertices in each part). Alon's Theorem 1.1 shows
`ch(K_{m×r}) = Θ(r log m)`. Taking `m ≈ √(n log n)` and `r ≈ √(n/log n)`:
- `ch(G) = O(r log m) = O(√(n log n))` (by Theorem 1.1)
- `ch(Gᶜ) = m = O(√(n log n))` (complement is `r` disjoint copies of `K_m`)

## Key Results

- `IsKChoosable`: predicate for k-choosability
- `listChromaticNumber`: the list chromatic number (choice number)
- `completeEquipartite`: the complete equipartite graph `K_{m×r}`
- `compl_completeEquipartite_choosable`: complement of `K_{m×r}` is m-choosable
- `alon_prop_2_1`: Alon's upper bound `ch(K_{m×r}) ≤ C·r·log m` (Proposition 2.1)
- `erdos_753`: the answer to Erdős Problem 753 is **NO**
-/

open Real Finset

/-! ### Definition of List Chromatic Number -/

/-- A graph `G` on vertex set `V` is **k-choosable** if for every assignment of color lists
from `ℕ` with each list having exactly `k` colors, there exists a proper coloring
choosing from the lists.

We use `ℕ` as the color type because list chromatic number is defined by quantifying over
all possible list assignments. Any finite or countable color universe can be embedded into
`ℕ`, so this is without loss of generality.

The definition uses `SimpleGraph.Coloring` to express proper coloring: a `G.Coloring ℕ`
is a graph homomorphism from `G` to the complete graph on `ℕ`, i.e., a function
`V → ℕ` mapping adjacent vertices to distinct colors. -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, (L v).card = k) →
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

/-- The **list chromatic number** (choice number) of a graph `G` is the minimum `k`
such that `G` is k-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-! ### Basic Properties of Choosability -/

/-- If a graph is j-choosable and `j ≤ k`, then it is k-choosable. When given lists of
exactly `k` colors, we restrict each list to a subset of exactly `j` colors and apply
the j-choosability hypothesis. -/
lemma IsKChoosable.mono {V : Type*} {G : SimpleGraph V} {j k : ℕ}
    (h : IsKChoosable G j) (hjk : j ≤ k) : IsKChoosable G k := by
  intro L hL
  choose L' hL'_sub hL'_card using fun v =>
    Finset.exists_subset_card_eq (hjk.trans (hL v).symm.le)
  obtain ⟨f, hf⟩ := h L' hL'_card
  exact ⟨f, fun v => hL'_sub v (hf v)⟩

/-- If `G` is k-choosable, then `listChromaticNumber G ≤ k`. -/
lemma listChromaticNumber_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : IsKChoosable G k) : listChromaticNumber G ≤ k :=
  Nat.sInf_le h

/-- Any finite graph is `|V|`-choosable (greedy argument via Hall's marriage theorem). -/
lemma isKChoosable_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsKChoosable G (Fintype.card V) := by
  intro L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion (fun v => L v)).card := by
    intro s
    by_cases hs : s.Nonempty
    · exact le_trans (Finset.card_le_univ s)
        (le_trans (hL hs.choose).symm.le
          (Finset.card_le_card (Finset.subset_biUnion_of_mem _ hs.choose_spec)))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun v => L v)).mp hall
  exact ⟨SimpleGraph.Coloring.mk f (fun hadj => hf_inj.ne hadj.ne), hf_mem⟩

-- Keep the finite-graph API statement even though the proof only needs nonemptiness.
lemma choosable_set_nonempty {V : Type*} [Finite V] (G : SimpleGraph V) :
    {k : ℕ | IsKChoosable G k}.Nonempty :=
  letI := Fintype.ofFinite V
  ⟨_, isKChoosable_card G⟩

/-- The list chromatic number of a finite graph is at most `|V|`. -/
lemma listChromaticNumber_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    listChromaticNumber G ≤ Fintype.card V :=
  listChromaticNumber_le (isKChoosable_card G)

/-! ### Complete Equipartite Graph -/

/-- The **complete equipartite graph** `K_{r×m}` on vertex set `Fin r × Fin m`.
Vertices `(i₁, j₁)` and `(i₂, j₂)` are adjacent iff they belong to different parts,
i.e., `i₁ ≠ i₂`. This is the complete `r`-partite graph with `m` vertices per part. -/
def completeEquipartite (r m : ℕ) : SimpleGraph (Fin r × Fin m) where
  Adj v w := v.1 ≠ w.1
  symm _ _ := Ne.symm
  loopless := ⟨fun _ h => absurd rfl h⟩

@[simp]
lemma completeEquipartite_adj {r m : ℕ} {v w : Fin r × Fin m} :
    (completeEquipartite r m).Adj v w ↔ v.1 ≠ w.1 := Iff.rfl

/-! ### Complement of K_{r×m} is m-choosable

The complement of `K_{r×m}` has adjacency `v.1 = w.1 ∧ v.2 ≠ w.2` (same part,
different index). This is a disjoint union of `r` copies of `K_m`. Each copy is
m-choosable by Hall's marriage theorem: given lists of size `m` for `m` vertices
forming a complete graph, the union of any `k` lists has size `≥ k`, so
Hall's condition is satisfied and a system of distinct representatives exists. -/

/-- The complement of the complete equipartite graph `K_{r×m}` is m-choosable. -/
theorem compl_completeEquipartite_choosable (r m : ℕ) :
    IsKChoosable (completeEquipartite r m)ᶜ m := by
  intro L hL
  have hall_row : ∀ i : Fin r, ∃ f : Fin m → ℕ,
      Function.Injective f ∧ ∀ j : Fin m, f j ∈ L (i, j) := by
    intro i
    rw [← Finset.all_card_le_biUnion_card_iff_exists_injective (fun j => L (i, j))]
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨j₀, hj₀⟩ := hs
      calc s.card
          ≤ Fintype.card (Fin m) := Finset.card_le_univ s
        _ = m := Fintype.card_fin m
        _ = (L (i, j₀)).card := (hL (i, j₀)).symm
        _ ≤ (s.biUnion fun j => L (i, j)).card :=
            Finset.card_le_card (Finset.subset_biUnion_of_mem (fun j => L (i, j)) hj₀)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  choose f hf_inj hf_mem using hall_row
  refine ⟨SimpleGraph.Coloring.mk (fun ⟨i, j⟩ => f i j) (fun {u v} hadj => ?_),
    fun ⟨i, j⟩ => hf_mem i j⟩
  simp only [SimpleGraph.compl_adj, completeEquipartite_adj, not_not] at hadj
  obtain ⟨hne, heq⟩ := hadj
  intro h
  have : f u.1 u.2 = f v.1 v.2 := h
  rw [heq] at this
  exact hne (Prod.ext heq (hf_inj v.1 this))

/-- The list chromatic number of the complement of `K_{r×m}` is at most `m`. -/
lemma listChromaticNumber_compl_le (r m : ℕ) :
    listChromaticNumber (completeEquipartite r m)ᶜ ≤ m :=
  listChromaticNumber_le (compl_completeEquipartite_choosable r m)

/-! ### Choosability transport along equivalences -/

/-- Transport choosability along an equivalence of vertex types. -/
lemma IsKChoosable.equiv {V W : Type*} {G : SimpleGraph V} {k : ℕ}
    (e : V ≃ W) (h : IsKChoosable G k) :
    IsKChoosable (G.comap e.symm) k := by
  intro L hL
  obtain ⟨f, hf⟩ := h (L ∘ e) (fun v => by simpa using hL (e v))
  refine ⟨SimpleGraph.Coloring.mk (f ∘ e.symm) (fun {u v} hadj => ?_),
    fun w => by simpa using hf (e.symm w)⟩
  exact f.valid (by rwa [SimpleGraph.comap_adj] at hadj)

/-- The complement commutes with `comap` along an equivalence. -/
lemma compl_comap_equiv {V W : Type*} (e : V ≃ W) (G : SimpleGraph V) :
    (G.comap e.symm)ᶜ = Gᶜ.comap e.symm := by
  ext u v
  simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj, e.symm.injective.ne_iff]

-- Keep the finite-graph API statement aligned with nearby list-chromatic lemmas.
/-- The list chromatic number is preserved (up to ≤) under graph isomorphism. -/
lemma listChromaticNumber_comap_equiv_le {V W : Type*} [Finite V]
    (e : V ≃ W) (G : SimpleGraph V) :
    listChromaticNumber (G.comap e.symm) ≤ listChromaticNumber G :=
  letI := Fintype.ofFinite V
  csInf_le_csInf (OrderBot.bddBelow _)
    (choosable_set_nonempty G) (fun _ hk => IsKChoosable.equiv e hk)

/-! ### Alon's Proposition 2.1 (Upper Bound)

**Proposition 2.1** (Alon, 1993): There exists a positive constant `C` such that
for all integers `m ≥ 2` and `r` with `1 ≤ r ≤ m`,

  `ch(K_{m×r}) ≤ C · r · log m`.

**Proof sketch** (from the paper, Case 1: `r ≤ m`, this is the only strictly
required case for us):
Let `S = ∪_v S(v)` be the union of all color lists, where `|S(v)| ≥ ⌈Cr·log m⌉`.
Consider a random function `f : S → {1, ..., r}` (uniform and independent for each
color). Colors mapped to group `i` are available for vertices in part `Vᵢ`.

For a vertex `v ∈ Vᵢ`, the probability that no color in `S(v)` maps to `i` is:
  `P = (1 - 1/r)^{|S(v)|} ≤ e^{-C · log m} = m^{-C}`.

By the union bound over all `rm` vertices:
  `P[failure] ≤ rm · m^{-C} = r · m^{1-C} ≤ m^{2-C} < 1` for `C ≥ 3`.

So a valid assignment exists. Given such `f`, each vertex `v ∈ Vᵢ` picks any color
`c ∈ S(v)` with `f(c) = i`. Since colors in different groups are distinct, this gives
a proper coloring. -/

/-- A partition function `f : ℕ → Fin r` that assigns at least one color from each
vertex's list to the correct group yields a proper coloring of `K_{r×m}`. -/
lemma proper_coloring_from_partition {r m : ℕ} {L : Fin r × Fin m → Finset ℕ}
    {f : ℕ → Fin r} (hf : ∀ i j, ∃ c ∈ L (i, j), f c = i) :
    ∃ g : (completeEquipartite r m).Coloring ℕ, ∀ v, g v ∈ L v := by
  choose g hg_mem hg_eq using hf
  refine ⟨SimpleGraph.Coloring.mk (fun v => g v.1 v.2) (fun {u v} hadj => ?_),
    fun v => hg_mem v.1 v.2⟩
  simp only [completeEquipartite_adj] at hadj
  intro heq
  have h1 := hg_eq u.1 u.2
  have h2 := hg_eq v.1 v.2
  have heq' : g u.1 u.2 = g v.1 v.2 := heq
  exact hadj (by rw [← h1, heq', h2])

/-! ### Counting argument for the partition function

The probabilistic method / counting argument. For large enough lists,
a partition function exists. The proof uses the union bound: if each vertex has
≥ k colors and `r · m · (1 - 1/r)^k < 1`, then a good partition function exists. -/

/-- Counting functions avoiding a given color on a subset: if `T` has at least `k`
elements, the number of functions `S → Fin r` with `f(c) ≠ i` for all `c ∈ T` is at most
`|Fin r|^|S| · ((r-1)/r)^|T|`. -/
private lemma fiber_count_for_subset {r : ℕ} {S : Finset ℕ}
    (T : Finset ↥S) (i : Fin r) :
    ((Finset.univ : Finset (↥S → Fin r)).filter
      (fun f => ∀ c ∈ T, f c ≠ i)).card =
    (∏ _ ∈ T, (r - 1)) * (∏ _ ∈ Finset.univ \ T, r) := by
  have h_count :
      (Finset.univ.filter (fun f : S → Fin r => ∀ c ∈ T, f c ≠ i)).card =
        (∏ c ∈ T, (Finset.univ.filter (fun j : Fin r => j ≠ i)).card) *
          (∏ c ∈ Finset.univ \ T, (Finset.univ : Finset (Fin r)).card) := by
    have h_count :
        (Finset.univ.filter (fun f : S → Fin r => ∀ c ∈ T, f c ≠ i)).card =
          (∏ c ∈ Finset.univ,
            (Finset.univ.filter (fun j : Fin r => j ≠ i ∨ c ∉ T)).card) := by
      convert Finset.card_pi _ _ using 2
      · convert rfl
        refine Finset.card_bij (fun a ha c => a c (Finset.mem_univ c)) ?_ ?_ ?_
        · grind
        · simp +contextual [funext_iff]
        · intro b hb
          use fun c _ => b c
          grind
      · infer_instance
    rw [h_count, ← Finset.prod_sdiff <| Finset.subset_univ T]
    rw [mul_comm]
    exact congrArg₂ _
      (Finset.prod_congr rfl fun x hx => by
        simp_all only [ne_eq, Subtype.forall, Finset.univ_eq_attach,
          not_true_eq_false, or_false])
      (Finset.prod_congr rfl fun x hx => by
        simp_all only [ne_eq, Subtype.forall, Finset.univ_eq_attach,
          Finset.mem_sdiff, Finset.mem_attach, true_and, not_false_eq_true, or_true,
          Finset.filter_true, Finset.card_univ, Fintype.card_fin])
  simp_all +decide [Finset.filter_ne']

/-- Each fiber of functions avoiding color `i` on `L_ij` has the expected cardinality
bound relative to the total function space. -/
private lemma fiber_card_bound {r : ℕ} (hr : 1 ≤ r)
    {k : ℕ} {S : Finset ℕ} {L_ij : Finset ℕ} (hL_ij : k ≤ L_ij.card)
    (hL_sub : L_ij ⊆ S) (i : Fin r) :
    ((Finset.univ : Finset (↥S → Fin r)).filter
      (fun f => ∀ c : ↥S, ↑c ∈ L_ij → f c ≠ i)).card ≤
    (Finset.univ : Finset (↥S → Fin r)).card * ((1 - 1 / (r : ℝ)) ^ k : ℝ) := by
  nontriviality
  obtain ⟨T, hT⟩ : ∃ T : Finset ↥S, T.card = k ∧ ∀ c ∈ T, c.val ∈ L_ij := by
    obtain ⟨T, hT⟩ := Finset.exists_subset_card_eq hL_ij
    use Finset.subtype (fun x => x ∈ S) T
    constructor
    · rw [Finset.card_subtype,
        Finset.filter_true_of_mem fun x hx => hL_sub (hT.1 hx), hT.2]
    · intro c hc
      exact hT.1 (by simpa using hc)
  have h_filter_T :
      (((Finset.univ : Finset (↥S → Fin r)).filter
        (fun f => ∀ c ∈ T, f c ≠ i)).card : ℝ) ≤
        (((Finset.univ : Finset (↥S → Fin r)).card : ℝ) * ((r - 1) / r) ^ k) := by
      rw [fiber_count_for_subset]
      simp_all +decide only [Finset.prod_const, Finset.univ_eq_attach, Nat.cast_mul,
        Nat.cast_pow, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
        Finset.card_attach]
      rw [show #(S.attach \ T) = #S - k from by
        have hT_sub_attach : T ⊆ S.attach := by
          intro x _
          simp
        rw [Finset.card_sdiff_of_subset hT_sub_attach, Finset.card_attach, hT.1],
        mul_comm]
      · rw [div_pow, mul_div, le_div_iff₀]
        all_goals first | positivity | ring_nf
        rw [← pow_add,
          Nat.sub_add_cancel
            (show k ≤ #S from hL_ij.trans (Finset.card_le_card hL_sub))]
        have h_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          rw [Nat.cast_sub hr]
          norm_num
        rw [h_cast, show (r : ℝ) - 1 = -1 + r by ring]
  refine le_trans ?_ (h_filter_T.trans ?_)
  · exact_mod_cast Finset.card_le_card fun f hf => by
      simp_all only [Subtype.forall, ne_eq, Finset.card_univ, Fintype.card_pi,
        Finset.univ_eq_attach, Fintype.card_fin, Finset.prod_const, Finset.card_attach,
        Nat.cast_pow, SetLike.coe_mem, Finset.mem_filter, Finset.mem_univ, true_and,
        not_false_eq_true, implies_true, and_self]
  · rw [sub_div, div_self (by positivity)]

/-- The total function space is covered by the union of fibers of bad vertices. -/
private lemma sum_fiber_bound {r m : ℕ} (hr : 1 ≤ r)
    {L : Fin r × Fin m → Finset ℕ}
    (S : Finset ℕ)
    (h_contra : ∀ f : ℕ → Fin r, ∃ i j, ∀ c, c ∈ L (i, j) → f c ≠ i) :
    (Finset.univ : Finset (↥S → Fin r)).card ≤
    ∑ i : Fin r, ∑ j : Fin m,
      ((Finset.univ : Finset (↥S → Fin r)).filter
        (fun f => ∀ c : ↥S, ↑c ∈ L (i, j) → f c ≠ i)).card := by
  have h_mem : ∀ f : ↥S → Fin r, ∃ i : Fin r, ∃ j : Fin m,
      ∀ c : ↥S, ↑c ∈ L (i, j) → f c ≠ i := by
    intro f
    obtain ⟨i, j, hi⟩ := h_contra (fun c => if hc : c ∈ S then f ⟨c, hc⟩ else ⟨0, by omega⟩)
    exact ⟨i, j, fun c hc => by simpa [c.2] using hi c.1 hc⟩
  have h_sub : (Finset.univ : Finset (↥S → Fin r)) ⊆
      Finset.biUnion Finset.univ (fun i =>
        Finset.biUnion Finset.univ (fun j =>
          (Finset.univ : Finset (↥S → Fin r)).filter
            (fun f => ∀ c : ↥S, ↑c ∈ L (i, j) → f c ≠ i))) := by
    intro f _
    obtain ⟨i, j, h⟩ := h_mem f
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using h⟩⟩
  exact le_trans (Finset.card_le_card h_sub)
    (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun i _ => Finset.card_biUnion_le))

/-- The core counting argument: if `r · m · (1 - 1/r)^k < 1` and every vertex has
at least `k` colors in its list, then a good partition function `f : ℕ → Fin r` exists
such that every vertex gets at least one color mapped to its group. -/
lemma exists_partition_function {r m : ℕ} (hr : 1 ≤ r)
    {k : ℕ} (hk : (r * m : ℝ) * ((1 - 1 / (r : ℝ)) ^ k) < 1)
    {L : Fin r × Fin m → Finset ℕ} (hL : ∀ v, k ≤ (L v).card) :
    ∃ f : ℕ → Fin r, ∀ (i : Fin r) (j : Fin m), ∃ c ∈ L (i, j), f c = i := by
  set S := Finset.biUnion Finset.univ L with hS_def
  by_contra h_neg
  simp only [not_exists, not_forall, not_and] at h_neg
  have h_contra : ∀ f : ℕ → Fin r, ∃ i j, ∀ c, c ∈ L (i, j) → f c ≠ i := by
    intro f
    obtain ⟨i, j, hc⟩ := h_neg f
    exact ⟨i, j, fun c hc' heq => hc c hc' heq⟩
  have h_L_sub : ∀ v, L v ⊆ S :=
    fun v c hc => hS_def ▸ Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hc⟩
  have h_fiber := fun i j => fiber_card_bound hr (hL (i, j)) (h_L_sub (i, j)) i
  have h_sum := sum_fiber_bound hr S h_contra
  have h_contradiction :
      ((Finset.univ : Finset (↥S → Fin r)).card : ℝ) ≤
      (Finset.univ : Finset (↥S → Fin r)).card *
        ((r * m : ℝ) * (1 - 1 / (r : ℝ)) ^ k) := by
    calc ((Finset.univ : Finset (↥S → Fin r)).card : ℝ)
        ≤ ∑ i : Fin r, ∑ j : Fin m,
          (((Finset.univ : Finset (↥S → Fin r)).filter
            (fun f => ∀ c : ↥S, ↑c ∈ L (i, j) → f c ≠ i)).card : ℝ) := by
          exact_mod_cast h_sum
      _ ≤ ∑ i : Fin r, ∑ j : Fin m,
          ((Finset.univ : Finset (↥S → Fin r)).card *
            ((1 - 1 / (r : ℝ)) ^ k) : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_fiber i j
      _ = (Finset.univ : Finset (↥S → Fin r)).card *
          ((r * m : ℝ) * (1 - 1 / (r : ℝ)) ^ k) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  have hpos : (0 : ℝ) < (Finset.univ : Finset (↥S → Fin r)).card := by
    simp only [Finset.card_univ, Fintype.card_pi, Finset.univ_eq_attach,
      Fintype.card_fin, Finset.prod_const, Finset.card_attach, Nat.cast_pow]
    positivity
  nlinarith [mul_lt_mul_of_pos_left hk hpos]

/-! ### Union bound condition -/

/-- For `k ≥ 3 · r · ln(m)`, the union bound condition `r · m · (1 - 1/r)^k < 1` holds.
Uses the inequality `(1 - 1/r) ≤ exp(-1/r)` and that `r · m · exp(-3 log m) < 1`
when `r ≤ m` and `m ≥ 2`. -/
lemma union_bound_condition {r m : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m) (hrm : r ≤ m)
    {k : ℕ} (hk : (3 : ℝ) * r * Real.log m ≤ k) :
    (r * m : ℝ) * ((1 - 1 / (r : ℝ)) ^ k) < 1 := by
  have h_upper_bound :
      (r * m : ℝ) * ((1 - 1 / r) ^ k : ℝ) ≤
        (r * m : ℝ) * (Real.exp (-3 * r * Real.log m / r) : ℝ) := by
    gcongr
    have h_exp : (1 - 1 / (r : ℝ)) ^ k ≤ Real.exp (-k / (r : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos]
      all_goals norm_num
      · exact le_trans
          (mul_le_mul_of_nonneg_right
            (Real.log_le_sub_one_of_pos
              (sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| by norm_cast))
            (Nat.cast_nonneg _)) <| by
          ring_nf
          norm_num
      · exact inv_lt_one_of_one_lt₀ <| by norm_cast
    exact h_exp.trans
      (Real.exp_le_exp.mpr <| by
        rw [div_le_div_iff_of_pos_right <| by positivity]
        linarith)
  refine lt_of_le_of_lt h_upper_bound ?_
  field_simp
  rw [Real.exp_neg, mul_comm]
  rw [inv_mul_eq_div, div_lt_one (by positivity)]
  rw [mul_comm 3, Real.exp_mul, Real.exp_log]
  all_goals norm_cast
  · nlinarith [Nat.pow_le_pow_left hm 2]
  · linarith

/-- Alon's Proposition 2.1: there exists a constant `C > 0` such that for all `m ≥ 2`
and `1 ≤ r ≤ m`, we have `ch(K_{m×r}) ≤ C · r · log m`. -/
theorem alon_prop_2_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ m r : ℕ, 2 ≤ m → 1 ≤ r → r ≤ m →
      (listChromaticNumber (completeEquipartite r m) : ℝ) ≤ C * ↑r * Real.log ↑m := by
  refine ⟨6, by norm_num, fun m r hm hr hrm => ?_⟩
  by_cases hr1 : r = 1
  · have h_r1 : listChromaticNumber (completeEquipartite 1 m) ≤ 1 := by
      apply Nat.sInf_le
      intro L hL
      have hne : ∀ v : Fin 1 × Fin m, (L v).Nonempty :=
        fun v => Finset.card_pos.mp (by
          rw [hL v]
          omega)
      refine ⟨SimpleGraph.Coloring.mk (fun v => (L v).min' (hne v))
        (fun {u v} hadj => ?_),
        fun v => Finset.min'_mem _ (hne v)⟩
      simp only [completeEquipartite_adj] at hadj
      exact absurd (Subsingleton.elim u.1 v.1) hadj
    calc (listChromaticNumber (completeEquipartite r m) : ℝ)
        ≤ 1 := by
          rw [hr1]
          exact_mod_cast h_r1
      _ ≤ 6 * r * Real.log m := by
          nlinarith [Real.log_two_gt_d9,
            Real.log_le_log (by norm_num) (show (2 : ℝ) ≤ m by exact_mod_cast hm),
            show (r : ℝ) ≥ 1 by exact_mod_cast hr]
  · have hr2 : 2 ≤ r := Nat.lt_of_le_of_ne hr (Ne.symm hr1)
    have h_k_choosable :
        IsKChoosable (completeEquipartite r m) (Nat.ceil (3 * r * Real.log m) + 1) := by
      intro L hL
      have h_ub : (r * m : ℝ) *
          ((1 - 1 / (r : ℝ)) ^ (Nat.ceil (3 * r * Real.log m) + 1)) < 1 :=
        union_bound_condition hr2 hm (by omega)
          (le_of_lt (Nat.lt_of_ceil_lt (Nat.lt_succ_self _)))
      have hL' : ∀ v, Nat.ceil (3 * ↑r * Real.log ↑m) + 1 ≤ (L v).card :=
        fun v => (hL v).symm ▸ le_refl _
      obtain ⟨f, hf⟩ := exists_partition_function hr h_ub hL'
      exact proper_coloring_from_partition hf
    calc (listChromaticNumber (completeEquipartite r m) : ℝ)
        ≤ Nat.ceil (3 * ↑r * Real.log ↑m) + 1 := by
          exact_mod_cast listChromaticNumber_le h_k_choosable
      _ ≤ 3 * r * Real.log m + 1 + 1 := by
          have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * r * Real.log m by positivity)
          linarith
      _ ≤ 6 * r * Real.log m := by
          nlinarith [show (r : ℝ) ≥ 2 by exact_mod_cast hr2,
            show (m : ℝ) ≥ 2 by exact_mod_cast hm, Real.log_two_gt_d9,
            Real.log_le_log (by positivity) (show (2 : ℝ) ≤ m by exact_mod_cast hm)]

/-! ### Auxiliary: logarithm is dominated by any positive power -/

/-- For any `C > 0` and `c > 0`, there exists `M` such that for all `m ≥ M`,
`C · log(m) + 1 ≤ m^c`. -/
lemma log_dominated_by_rpow {C : ℝ} {c : ℝ} (hc : 0 < c) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → C * Real.log (↑m) + 1 ≤ (m : ℝ) ^ c := by
  suffices h_div : ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      C * Real.log m / (m : ℝ) ^ c + 1 / (m : ℝ) ^ c ≤ 1 by
    obtain ⟨M, hM⟩ := h_div
    exact ⟨M + 1, fun m hm => by
      have := hM m (by omega)
      rw [← add_div, div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _)] at this
      linarith⟩
  have h_log_div : Filter.Tendsto (fun m : ℕ => C * Real.log m / (m : ℝ) ^ c)
      Filter.atTop (nhds 0) := by
    suffices h_log : Filter.Tendsto (fun y : ℝ => C * y / Real.exp (c * y))
        Filter.atTop (nhds 0) by
      have := h_log.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact this.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with m hm
        simp [Real.rpow_def_of_pos (Nat.cast_pos.mpr hm), mul_comm])
    suffices h_z : Filter.Tendsto (fun z : ℝ => C * z / Real.exp z)
        Filter.atTop (nhds 0) by
      have := h_z.comp (Filter.tendsto_id.const_mul_atTop hc)
      have hc_ne : c ≠ 0 := hc.ne'
      convert this.div_const c using 1
      · ext x
        simp [div_eq_mul_inv, mul_assoc, mul_comm c, hc_ne]
      · simp
    simpa [Real.exp_neg, mul_div_assoc] using
      tendsto_const_nhds.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have := h_log_div.add (tendsto_inv_atTop_zero.comp
    (tendsto_rpow_atTop hc |>.comp tendsto_natCast_atTop_atTop))
  simpa using this.eventually (ge_mem_nhds (by norm_num))

/-! ### Main theorem -/

/-- **Erdős Problem 753**: For every `c > 0` and every `N`, there exists `n ≥ N` and a
graph `G` on `n` vertices such that `χ_L(G) + χ_L(Gᶜ) ≤ n^{1/2 + c}`.

The construction uses `G = K_{m×m}` (transported to `Fin (m²)`), where `m` is chosen
large enough. By Alon's Proposition 2.1, `χ_L(G) ≤ C·m·log m`, and the complement
(a disjoint union of cliques) has `χ_L(Gᶜ) ≤ m`. -/
theorem erdos_753 :
    ∀ c : ℝ, c > 0 →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        ∃ G : SimpleGraph (Fin n),
          ((listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ)) ≤
            (n : ℝ) ^ ((1 : ℝ) / 2 + c) := by
  intro c hc N
  obtain ⟨C, -, hC⟩ := alon_prop_2_1
  obtain ⟨M, hM⟩ := log_dominated_by_rpow (C := C) hc
  set m := max M (max N 2) with hm_def
  have hm_ge_M : M ≤ m := le_max_left _ _
  have hm_ge_N : N ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm_ge_2 : 2 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  use m * m, by nlinarith
  have ⟨e⟩ : Nonempty (Fin m × Fin m ≃ Fin (m * m)) :=
    ⟨Fintype.equivOfCardEq (by simp)⟩
  set G := (completeEquipartite m m).comap e.symm with hG_def
  have hG_ch : IsKChoosable G (listChromaticNumber (completeEquipartite m m)) :=
    IsKChoosable.equiv e (Nat.sInf_mem (choosable_set_nonempty (completeEquipartite m m)))
  have hGc_ch : IsKChoosable Gᶜ m := by
    rw [hG_def, compl_comap_equiv]
    exact IsKChoosable.equiv e (compl_completeEquipartite_choosable m m)
  refine ⟨G, ?_⟩
  have h_ch_G : (listChromaticNumber G : ℝ) ≤ C * m * Real.log m :=
    le_trans (by exact_mod_cast listChromaticNumber_le hG_ch)
      (hC m m hm_ge_2 (by omega) le_rfl)
  have h_ch_Gc : (listChromaticNumber Gᶜ : ℝ) ≤ m :=
    by exact_mod_cast listChromaticNumber_le hGc_ch
  -- Using the inequality $m * (C * \log m + 1) \leq m * m^c$, we can conclude.
  have h_final : m * (C * Real.log m + 1) ≤ m * m^c := by
    exact mul_le_mul_of_nonneg_left (hM m hm_ge_M) (Nat.cast_nonneg _)
  convert le_trans _ (h_final.trans _) using 1
  · linarith
  · rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_one_add']
    all_goals norm_num
    · rw [← Real.rpow_add (by positivity)]
      ring_nf
      exact Real.rpow_le_rpow_of_exponent_le
        (by
          norm_cast
          linarith)
        (by linarith)
    · finiteness

/-- The negation form: there is **no** constant `c > 0` such that
`n^{1/2+c} < χ_L(G) + χ_L(Gᶜ)` for all graphs on `n` vertices for large enough `n`. -/
theorem erdos_753_negation :
    ¬∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)),
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) <
          ((listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ)) := by
  intro ⟨c, hc, N, hN⟩
  obtain ⟨n, hn_ge, G, hG⟩ := erdos_753 c hc N
  exact not_lt.mpr hG (hN n hn_ge G)

end Erdos753

#print axioms Erdos753.erdos_753_negation
-- 'Erdos753.erdos_753_negation' depends on axioms: [propext, choice, Quot.sound]
