/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 804.
https://www.erdosproblems.com/forum/thread/804

Informal authors:
- Noga Alon
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos804.md
-/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Erdős Problem 804

Alon and Sudakov determined the independence number forced by the condition
that every induced subgraph of a prescribed polylogarithmic order contain an
independent set of logarithmic order.  The detailed mathematical proof,
including the rounding convention and a Leanization map, is in `tex/804.tex`.

All logarithms below are natural logarithms.  Since graph cardinalities are
natural numbers, the local independent-set threshold is rounded up and the
prescribed induced-subgraph order is rounded down.
-/

open Filter Finset Real
open scoped Topology

noncomputable section

namespace Erdos804

/-! ## The exact finite extremal problem -/

/-- Every `s`-vertex set in `G` contains an independent set of exactly `t`
vertices.  This is equivalent to saying that every induced `s`-vertex
subgraph has independence number at least `t`. -/
def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n))
    (s t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = s →
    ∃ I : Finset (Fin n), I ⊆ S ∧ G.IsNIndepSet t I

/-- The integer `q` is forced by the local `(s,t)` independence condition on
all labelled graphs of order `n`. -/
def GuaranteesIndependence (n s t q : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), HasLocalIndependence G s t → q ≤ G.indepNum

/-- The largest independence number forced by the local `(s,t)` condition.
The search is bounded by `n`, the order of every graph under consideration.
On the intended range `t ≤ s ≤ n`, this is the minimum independence number
among admissible graphs. -/
noncomputable def localIndependenceNumber (n s t : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (GuaranteesIndependence n s t) n

theorem guaranteesIndependence_zero (n s t : ℕ) :
    GuaranteesIndependence n s t 0 := by
  intro G _
  exact Nat.zero_le _

theorem guaranteesIndependence_mono {n s t q r : ℕ} (hrq : r ≤ q)
    (hq : GuaranteesIndependence n s t q) :
    GuaranteesIndependence n s t r := by
  intro G hG
  exact hrq.trans (hq G hG)

theorem localIndependenceNumber_le_order (n s t : ℕ) :
    localIndependenceNumber n s t ≤ n := by
  classical
  exact Nat.findGreatest_le n

theorem localIndependenceNumber_is_guaranteed (n s t : ℕ) :
    GuaranteesIndependence n s t (localIndependenceNumber n s t) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le n)
    (guaranteesIndependence_zero n s t)

theorem le_localIndependenceNumber_of_guaranteed {n s t q : ℕ}
    (hqn : q ≤ n) (hq : GuaranteesIndependence n s t q) :
    q ≤ localIndependenceNumber n s t := by
  classical
  exact Nat.le_findGreatest hqn hq

theorem localIndependenceNumber_le_of_witness {n s t : ℕ}
    {G : SimpleGraph (Fin n)} (hG : HasLocalIndependence G s t) :
    localIndependenceNumber n s t ≤ G.indepNum :=
  localIndependenceNumber_is_guaranteed n s t G hG

theorem indepNum_le_order {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.indepNum ≤ n := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  calc
    G.indepNum = I.card := hI.card_eq.symm
    _ ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ I)
    _ = n := Fintype.card_fin n

theorem localIndependenceNumber_eq_minimum {n s t : ℕ}
    (hts : t ≤ s) (hsn : s ≤ n) :
    ∃ G : SimpleGraph (Fin n),
      HasLocalIndependence G s t ∧
      G.indepNum = localIndependenceNumber n s t := by
  classical
  let goodGraphs : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter fun G ↦ HasLocalIndependence G s t
  have hbot : (⊥ : SimpleGraph (Fin n)) ∈ goodGraphs := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro S hS
    obtain ⟨I, hIS, hIcard⟩ :=
      Finset.exists_subset_card_eq (show t ≤ S.card by omega)
    refine ⟨I, hIS, ?_⟩
    refine ⟨?_, hIcard⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro v _hv w _hw _hvw
    simp
  obtain ⟨G, hGmem, hGmin⟩ :=
    Finset.exists_min_image goodGraphs SimpleGraph.indepNum ⟨_, hbot⟩
  have hGlocal : HasLocalIndependence G s t :=
    (Finset.mem_filter.mp hGmem).2
  refine ⟨G, hGlocal, le_antisymm ?_ ?_⟩
  · apply le_localIndependenceNumber_of_guaranteed
    · exact indepNum_le_order G
    · intro H hHlocal
      exact hGmin H (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHlocal⟩)
  · exact localIndependenceNumber_le_of_witness hGlocal

/-! ## Rounded logarithmic parameters -/

/-- The integer threshold corresponding to “at least `log n` vertices”. -/
def logThreshold (n : ℕ) : ℕ := ⌈Real.log (n : ℝ)⌉₊

/-- The integer order corresponding to `(log n)^j`. -/
def logWindow (j n : ℕ) : ℕ := ⌊(Real.log (n : ℝ)) ^ j⌋₊

/-- The scale appearing in the Alon--Sudakov lower bound and in the sharp
cubic-window estimate. -/
def resolutionScale (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ))

/-- Erdős's square-logarithmic local window. -/
def squareValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 2 n) (logThreshold n)

/-- Erdős's cubic-logarithmic local window. -/
def cubicValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 3 n) (logThreshold n)

/-! ## Finite double counting for the lower bound -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Independent `r`-subsets of `W`. -/
def independentSubsets (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (r : ℕ) : Finset (Finset V) :=
  W.powersetCard r |>.filter fun I ↦ G.IsIndepSet (I : Set V)

@[simp] theorem mem_independentSubsets_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {W I : Finset V} {r : ℕ} :
    I ∈ independentSubsets G W r ↔
      I ⊆ W ∧ I.card = r ∧ G.IsIndepSet (I : Set V) := by
  simp [independentSubsets, and_assoc]

/-- Double-count incidences between an `r`-uniform family and the `k`-sets
containing one of its members. -/
theorem sum_card_uniformFamily_inside
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r) (hrk : r ≤ k) :
    ∑ U ∈ X.powersetCard k, #(F.filter (· ⊆ U)) =
      #F * Nat.choose (#X - r) (k - r) := by
  classical
  have hdouble :
      ∑ U ∈ X.powersetCard k, #(F.filter (· ⊆ U)) =
        ∑ A ∈ F, #((X.powersetCard k).filter (fun U ↦ A ⊆ U)) := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun U A : Finset V => A ⊆ U)
        (s := X.powersetCard k) (t := F))
  rw [hdouble]
  calc
    ∑ A ∈ F, #((X.powersetCard k).filter (fun U ↦ A ⊆ U)) =
        ∑ A ∈ F, Nat.choose (#X - r) (k - r) := by
      apply sum_congr rfl
      intro A hA
      rw [Finset.card_filter_powersetCard_subset A X k (hFX A hA)]
      · rw [hFr A hA]
      · simpa [hFr A hA]
    _ = #F * Nat.choose (#X - r) (k - r) := by simp

/-- A member of a nonempty finite family is at least its average, stated
without division. -/
lemma exists_sum_le_card_mul_of_nonempty
    {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℕ) :
    ∃ x ∈ s, ∑ y ∈ s, f y ≤ #s * f x := by
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨x, hx, ?_⟩
  simpa [nsmul_eq_mul] using s.sum_le_card_nsmul f (f x) hmax

/-- The local hypothesis forces many independent `u`-sets in every ambient
set `W` of at least `s` vertices. -/
theorem choose_card_le_independentSubsets_mul_choose
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (s u : ℕ) (hus : u ≤ s) (hsW : s ≤ W.card)
    (hlocal : ∀ S ∈ W.powersetCard s,
      ∃ I : Finset V, I ⊆ S ∧ I.card = u ∧ G.IsIndepSet (I : Set V)) :
    Nat.choose W.card s ≤
      #(independentSubsets G W u) * Nat.choose (W.card - u) (s - u) := by
  classical
  let F := independentSubsets G W u
  have hFX : ∀ A ∈ F, A ⊆ W := by
    intro A hA
    exact (mem_independentSubsets_iff.mp hA).1
  have hFu : ∀ A ∈ F, A.card = u := by
    intro A hA
    exact (mem_independentSubsets_iff.mp hA).2.1
  have hone : ∀ S ∈ W.powersetCard s,
      1 ≤ #(F.filter (· ⊆ S)) := by
    intro S hS
    obtain ⟨I, hIS, hIcard, hIind⟩ := hlocal S hS
    exact Finset.card_pos.mpr ⟨I, Finset.mem_filter.mpr
      ⟨mem_independentSubsets_iff.mpr
        ⟨hIS.trans (Finset.mem_powersetCard.mp hS).1, hIcard, hIind⟩, hIS⟩⟩
  calc
    Nat.choose W.card s = #(W.powersetCard s) := by
      rw [Finset.card_powersetCard]
    _ = ∑ S ∈ W.powersetCard s, 1 := by simp
    _ ≤ ∑ S ∈ W.powersetCard s, #(F.filter (· ⊆ S)) := by
      exact Finset.sum_le_sum fun S hS ↦ hone S hS
    _ = #F * Nat.choose (W.card - u) (s - u) :=
      sum_card_uniformFamily_inside W F u s hFX hFu hus

/-- Double-count the pairs `(X,I)` with `X` an `h`-subset of an independent
`u`-set `I`. -/
theorem sum_card_independent_extensions
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (u h : ℕ) (hhu : h ≤ u) :
    ∑ X ∈ W.powersetCard h,
        #((independentSubsets G W u).filter (fun I ↦ X ⊆ I)) =
      #(independentSubsets G W u) * Nat.choose u h := by
  classical
  let F := independentSubsets G W u
  have hdouble :
      ∑ X ∈ W.powersetCard h, #(F.filter (fun I ↦ X ⊆ I)) =
        ∑ I ∈ F, #((W.powersetCard h).filter (fun X ↦ X ⊆ I)) := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun X I : Finset V => X ⊆ I)
        (s := W.powersetCard h) (t := F))
  rw [hdouble]
  calc
    ∑ I ∈ F, #((W.powersetCard h).filter (fun X ↦ X ⊆ I)) =
        ∑ I ∈ F, Nat.choose u h := by
      apply sum_congr rfl
      intro I hI
      have hIW : I ⊆ W := (mem_independentSubsets_iff.mp hI).1
      have hIcard : I.card = u := (mem_independentSubsets_iff.mp hI).2.1
      have heq : (W.powersetCard h).filter (fun X ↦ X ⊆ I) =
          I.powersetCard h := by
        ext X
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_hXW, hXcard⟩, hXI⟩
          exact ⟨hXI, hXcard⟩
        · rintro ⟨hXI, hXcard⟩
          exact ⟨⟨hXI.trans hIW, hXcard⟩, hXI⟩
      rw [heq, Finset.card_powersetCard, hIcard]
    _ = #F * Nat.choose u h := by simp

/-- A popular `h`-set belongs to at least the average number of independent
`u`-sets. -/
theorem exists_popular_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (u h : ℕ) (hhu : h ≤ u) (hhW : h ≤ W.card) :
    ∃ X ∈ W.powersetCard h,
      #(independentSubsets G W u) * Nat.choose u h ≤
        Nat.choose W.card h *
          #((independentSubsets G W u).filter (fun I ↦ X ⊆ I)) := by
  classical
  have hpowers : (W.powersetCard h).Nonempty :=
    Finset.powersetCard_nonempty.mpr hhW
  obtain ⟨X, hX, hAv⟩ := exists_sum_le_card_mul_of_nonempty hpowers
    (fun X ↦ #((independentSubsets G W u).filter (fun I ↦ X ⊆ I)))
  refine ⟨X, hX, ?_⟩
  rw [Finset.card_powersetCard] at hAv
  rw [sum_card_independent_extensions G W u h hhu] at hAv
  exact hAv

/-- Combining the two preceding double counts and the standard nested-choice
identities eliminates the total number of independent `u`-sets. -/
theorem exists_popular_subset_choose_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (s h : ℕ) (hh : 0 < h)
    (hu : 2 * h ≤ s) (hsW : s ≤ W.card)
    (hlocal : ∀ S ∈ W.powersetCard s,
      ∃ I : Finset V, I ⊆ S ∧ I.card = 2 * h ∧
        G.IsIndepSet (I : Set V)) :
    ∃ X ∈ W.powersetCard h,
      Nat.choose (W.card - h) h ≤
        #((independentSubsets G W (2 * h)).filter (fun I ↦ X ⊆ I)) *
          Nat.choose s (2 * h) := by
  classical
  let m := W.card
  let u := 2 * h
  have hhu : h ≤ u := by
    dsimp only [u]
    omega
  have hum : u ≤ m := hu.trans hsW
  have hhm : h ≤ m := hhu.trans hum
  have hmany := choose_card_le_independentSubsets_mul_choose
    G W s u hu hsW hlocal
  obtain ⟨X, hX, hpopular⟩ := exists_popular_subset G W u h hhu hhm
  refine ⟨X, hX, ?_⟩
  let Fcard := #(independentSubsets G W u)
  let Ecard := #((independentSubsets G W u).filter (fun I ↦ X ⊆ I))
  have hid₁ : Nat.choose m s * Nat.choose s u =
      Nat.choose m u * Nat.choose (m - u) (s - u) :=
    Nat.choose_mul hu
  have hid₂raw : Nat.choose m u * Nat.choose u h =
      Nat.choose m h * Nat.choose (m - h) (u - h) :=
    Nat.choose_mul hhu
  have huh : u - h = h := by
    dsimp only [u]
    omega
  have hid₂ : Nat.choose m u * Nat.choose u h =
      Nat.choose m h * Nat.choose (m - h) h := by
    simpa only [huh] using hid₂raw
  have hchain :
      Nat.choose m s * Nat.choose s u * Nat.choose u h ≤
        Nat.choose m h * Ecard * Nat.choose (m - u) (s - u) *
          Nat.choose s u := by
    calc
      Nat.choose m s * Nat.choose s u * Nat.choose u h ≤
          Fcard * Nat.choose (m - u) (s - u) *
            Nat.choose s u * Nat.choose u h := by
        dsimp only [m, u, Fcard] at hmany ⊢
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmany)
      _ = (Fcard * Nat.choose u h) *
            (Nat.choose (m - u) (s - u) * Nat.choose s u) := by
        ac_rfl
      _ ≤ (Nat.choose m h * Ecard) *
            (Nat.choose (m - u) (s - u) * Nat.choose s u) := by
        dsimp only [m, u, Fcard, Ecard] at hpopular ⊢
        exact Nat.mul_le_mul_right _ hpopular
      _ = Nat.choose m h * Ecard * Nat.choose (m - u) (s - u) *
            Nat.choose s u := by
        ac_rfl
  have hcancelled :
      (Nat.choose m h * Nat.choose (m - u) (s - u)) *
          Nat.choose (m - h) h ≤
        (Nat.choose m h * Nat.choose (m - u) (s - u)) *
          (Ecard * Nat.choose s u) := by
    calc
      (Nat.choose m h * Nat.choose (m - u) (s - u)) *
          Nat.choose (m - h) h =
          Nat.choose m s * Nat.choose s u * Nat.choose u h := by
        calc
          (Nat.choose m h * Nat.choose (m - u) (s - u)) *
              Nat.choose (m - h) h =
              (Nat.choose m h * Nat.choose (m - h) h) *
                Nat.choose (m - u) (s - u) := by ac_rfl
          _ = (Nat.choose m u * Nat.choose u h) *
                Nat.choose (m - u) (s - u) := by rw [hid₂]
          _ = (Nat.choose m u * Nat.choose (m - u) (s - u)) *
                Nat.choose u h := by ac_rfl
          _ = Nat.choose m s * Nat.choose s u * Nat.choose u h := by
            rw [hid₁]
      _ ≤ _ := hchain
      _ = (Nat.choose m h * Nat.choose (m - u) (s - u)) *
          (Ecard * Nat.choose s u) := by
        ac_rfl
  have hfactor :
      0 < Nat.choose m h * Nat.choose (m - u) (s - u) := by
    apply Nat.mul_pos
    · exact Nat.choose_pos hhm
    · exact Nat.choose_pos (Nat.sub_le_sub_right hsW u)
  have := Nat.le_of_mul_le_mul_left hcancelled hfactor
  simpa only [m, u, Ecard] using this

/-- The union of the complements of a popular half-set inside its independent
extensions. -/
def extensionRemainder (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X : Finset V) (u : ℕ) : Finset V :=
  ((independentSubsets G W u).filter (fun I ↦ X ⊆ I)).biUnion
    fun I ↦ I \ X

theorem extension_subset_remainder
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {W X I : Finset V} {u : ℕ}
    (hI : I ∈ independentSubsets G W u) (hXI : X ⊆ I) :
    I \ X ⊆ extensionRemainder G W X u := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨I, Finset.mem_filter.mpr ⟨hI, hXI⟩, hv⟩

theorem extensionRemainder_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X : Finset V) (u : ℕ) :
    extensionRemainder G W X u ⊆ W \ X := by
  intro v hv
  obtain ⟨I, hI, hvIX⟩ := Finset.mem_biUnion.mp hv
  have hImem := (Finset.mem_filter.mp hI).1
  have hIW := (mem_independentSubsets_iff.mp hImem).1
  exact Finset.mem_sdiff.mpr
    ⟨hIW (Finset.mem_sdiff.mp hvIX).1, (Finset.mem_sdiff.mp hvIX).2⟩

/-- Every vertex in the extension remainder is nonadjacent to every vertex
of the popular set. -/
theorem not_adj_of_mem_extensionRemainder
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {W X : Finset V} {u : ℕ} {x v : V}
    (hx : x ∈ X) (hv : v ∈ extensionRemainder G W X u) :
    ¬ G.Adj x v := by
  obtain ⟨I, hI, hvIX⟩ := Finset.mem_biUnion.mp hv
  have hIfilter := Finset.mem_filter.mp hI
  have hIind := (mem_independentSubsets_iff.mp hIfilter.1).2.2
  have hxI := hIfilter.2 hx
  have hvI := (Finset.mem_sdiff.mp hvIX).1
  have hxv : x ≠ v := by
    intro hxv
    subst v
    exact (Finset.mem_sdiff.mp hvIX).2 hx
  exact hIind hxI hvI hxv

/-- Independent extensions of `X` inject into the `h`-subsets of their
union outside `X`. -/
theorem card_extension_filter_le_choose_remainder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X : Finset V) (h : ℕ) (hXcard : X.card = h) :
    #((independentSubsets G W (2 * h)).filter (fun I ↦ X ⊆ I)) ≤
      Nat.choose (extensionRemainder G W X (2 * h)).card h := by
  classical
  let E := (independentSubsets G W (2 * h)).filter (fun I ↦ X ⊆ I)
  let R := extensionRemainder G W X (2 * h)
  let f : Finset V → Finset V := fun I ↦ I \ X
  have hfmem : ∀ I ∈ E, f I ∈ R.powersetCard h := by
    intro I hI
    have hIf := Finset.mem_filter.mp hI
    have hIcard := (mem_independentSubsets_iff.mp hIf.1).2.1
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · exact extension_subset_remainder hIf.1 hIf.2
    · change #(I \ X) = h
      rw [Finset.card_sdiff_of_subset hIf.2, hIcard, hXcard]
      omega
  have hfinj : Set.InjOn f (E : Set (Finset V)) := by
    intro I hI J hJ hEq
    have hXI := (Finset.mem_filter.mp hI).2
    have hXJ := (Finset.mem_filter.mp hJ).2
    apply Finset.ext
    intro v
    by_cases hvX : v ∈ X
    · simp [hXI hvX, hXJ hvX]
    · have hvI : v ∈ I ↔ v ∈ I \ X := by simp [hvX]
      have hvJ : v ∈ J ↔ v ∈ J \ X := by simp [hvX]
      change I \ X = J \ X at hEq
      rw [hvI, hvJ, hEq]
  have himage : E.image f ⊆ R.powersetCard h := by
    intro A hA
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hA
    exact hfmem I hI
  calc
    #E = #(E.image f) := (Finset.card_image_of_injOn hfinj).symm
    _ ≤ #(R.powersetCard h) := Finset.card_le_card himage
    _ = Nat.choose R.card h := Finset.card_powersetCard _ _

/-- The popular-set double count controls the cardinality of the
anticomplete remainder. -/
theorem choose_card_sub_half_le_remainder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (s h : ℕ) (hh : 0 < h)
    (hu : 2 * h ≤ s) (hsW : s ≤ W.card)
    (hlocal : ∀ S ∈ W.powersetCard s,
      ∃ I : Finset V, I ⊆ S ∧ I.card = 2 * h ∧
        G.IsIndepSet (I : Set V)) :
    ∃ X ∈ W.powersetCard h,
      Nat.choose (W.card - h) h ≤
        Nat.choose (extensionRemainder G W X (2 * h)).card h *
          Nat.choose s (2 * h) := by
  classical
  obtain ⟨X, hX, hbound⟩ :=
    exists_popular_subset_choose_bound G W s h hh hu hsW hlocal
  refine ⟨X, hX, hbound.trans ?_⟩
  exact Nat.mul_le_mul_right _
    (card_extension_filter_le_choose_remainder G W X h
      (Finset.mem_powersetCard.mp hX).2)

/-- A binomial-coefficient comparison implies a concrete lower bound for the
remainder size.  This deliberately coarse estimate is sufficient at every
fixed polylogarithmic window. -/
theorem card_mul_sq_ge_of_choose_bound
    {m r s h : ℕ} (hh : 0 < h) (h2hm : 2 * h ≤ m) (hs : 0 < s)
    (hchoose : Nat.choose (m - h) h ≤
      Nat.choose r h * Nat.choose s (2 * h)) :
    ((m + 1 - 2 * h : ℕ) : ℝ) ≤ (r : ℝ) * (s : ℝ) ^ 2 := by
  have hbase : m - h + 1 - h = m + 1 - 2 * h := by omega
  have hlower :
      ((m + 1 - 2 * h : ℕ) ^ h : ℝ) / (h.factorial : ℝ) ≤
        Nat.choose (m - h) h := by
    simpa only [hbase] using
      (Nat.pow_le_choose (α := ℝ) h (m - h))
  have hupperR : (Nat.choose r h : ℝ) ≤
      (r : ℝ) ^ h / (h.factorial : ℝ) :=
    Nat.choose_le_pow_div h r
  have hupperS : Nat.choose s (2 * h) ≤ s ^ (2 * h) :=
    Nat.choose_le_pow s (2 * h)
  have hpowdiv :
      ((m + 1 - 2 * h : ℕ) ^ h : ℝ) / (h.factorial : ℝ) ≤
        ((r : ℝ) ^ h / (h.factorial : ℝ)) * (s : ℝ) ^ (2 * h) := by
    calc
      ((m + 1 - 2 * h : ℕ) ^ h : ℝ) / (h.factorial : ℝ) ≤
          (Nat.choose (m - h) h : ℝ) := hlower
      _ ≤ (Nat.choose r h : ℝ) * Nat.choose s (2 * h) := by
        exact_mod_cast hchoose
      _ ≤ ((r : ℝ) ^ h / (h.factorial : ℝ)) * (s : ℝ) ^ (2 * h) := by
        gcongr
        exact_mod_cast hupperS
  have hfac : 0 < (h.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos h
  have hpows :
      ((m + 1 - 2 * h : ℕ) : ℝ) ^ h ≤
        (r : ℝ) ^ h * (s : ℝ) ^ (2 * h) := by
    apply (div_le_div_iff_of_pos_right hfac).mp
    calc
      ((m + 1 - 2 * h : ℕ) : ℝ) ^ h / (h.factorial : ℝ) ≤
          ((r : ℝ) ^ h / (h.factorial : ℝ)) *
            (s : ℝ) ^ (2 * h) := hpowdiv
      _ = ((r : ℝ) ^ h * (s : ℝ) ^ (2 * h)) /
            (h.factorial : ℝ) := by ring
  have hrewrite :
      (r : ℝ) ^ h * (s : ℝ) ^ (2 * h) =
        ((r : ℝ) * (s : ℝ) ^ 2) ^ h := by
    rw [mul_pow, pow_mul]
  rw [hrewrite] at hpows
  have hnonnegL : 0 ≤ ((m + 1 - 2 * h : ℕ) : ℝ) := by positivity
  have hnonnegR : 0 ≤ (r : ℝ) * (s : ℝ) ^ 2 := by positivity
  exact (pow_le_pow_iff_left₀ hnonnegL hnonnegR (Nat.ne_zero_of_lt hh)).mp hpows

/-- One round of the lower-bound construction.  The popular independent
half-set is anticomplete to a remainder which loses at most the factor
`2 * s ^ 2`. -/
theorem exists_anticomplete_block
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (s h : ℕ) (hh : 0 < h)
    (hfour : 4 * h ≤ W.card) (hu : 2 * h ≤ s) (hsW : s ≤ W.card)
    (hlocal : ∀ S ∈ W.powersetCard s,
      ∃ I : Finset V, I ⊆ S ∧ I.card = 2 * h ∧
        G.IsIndepSet (I : Set V)) :
    ∃ X R : Finset V,
      X ⊆ W ∧ X.card = h ∧ G.IsIndepSet (X : Set V) ∧
      R ⊆ W \ X ∧
      (∀ x ∈ X, ∀ v ∈ R, ¬ G.Adj x v) ∧
      W.card ≤ 2 * R.card * s ^ 2 := by
  classical
  obtain ⟨X, hXpower, hpopular⟩ :=
    exists_popular_subset_choose_bound G W s h hh hu hsW hlocal
  let E := (independentSubsets G W (2 * h)).filter (fun I ↦ X ⊆ I)
  let R := extensionRemainder G W X (2 * h)
  have hXW : X ⊆ W := (Finset.mem_powersetCard.mp hXpower).1
  have hXcard : X.card = h := (Finset.mem_powersetCard.mp hXpower).2
  have hchoose : Nat.choose (W.card - h) h ≤
      Nat.choose R.card h * Nat.choose s (2 * h) := by
    calc
      Nat.choose (W.card - h) h ≤ E.card * Nat.choose s (2 * h) := by
        simpa only [E] using hpopular
      _ ≤ Nat.choose R.card h * Nat.choose s (2 * h) := by
        exact Nat.mul_le_mul_right _
          (card_extension_filter_le_choose_remainder G W X h hXcard)
  have hRreal : ((W.card + 1 - 2 * h : ℕ) : ℝ) ≤
      (R.card : ℝ) * (s : ℝ) ^ 2 :=
    card_mul_sq_ge_of_choose_bound hh (by omega) (by omega) hchoose
  have htwobase : W.card ≤ 2 * (W.card + 1 - 2 * h) := by omega
  have hsizeReal : (W.card : ℝ) ≤
      2 * (R.card : ℝ) * (s : ℝ) ^ 2 := by
    have htwobaseReal : (W.card : ℝ) ≤
        2 * ((W.card + 1 - 2 * h : ℕ) : ℝ) := by
      exact_mod_cast htwobase
    nlinarith
  have hsize : W.card ≤ 2 * R.card * s ^ 2 := by
    exact_mod_cast hsizeReal
  have hEpos : 0 < E.card := by
    have hchoosepos : 0 < Nat.choose (W.card - h) h := by
      exact Nat.choose_pos (by omega)
    by_contra hnot
    have hEzero : E.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hEzero, zero_mul] at hpopular
    omega
  obtain ⟨I, hIE⟩ := Finset.card_pos.mp hEpos
  have hIfilter := Finset.mem_filter.mp hIE
  have hIind := (mem_independentSubsets_iff.mp hIfilter.1).2.2
  have hXind : G.IsIndepSet (X : Set V) := hIind.mono hIfilter.2
  refine ⟨X, R, hXW, hXcard, hXind,
    extensionRemainder_subset G W X (2 * h), ?_, hsize⟩
  intro x hx v hv
  exact not_adj_of_mem_extensionRemainder hx hv

/-- Iterating the anticomplete-block lemma constructs a large independent
set inside an arbitrary ambient vertex set. -/
theorem exists_independent_of_geometric_room
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (s h q : ℕ) (hh : 0 < h) (hs : 0 < s)
    (hfour : 4 * h ≤ s)
    (hroom : s * (2 * s ^ 2) ^ q ≤ W.card)
    (hlocal : ∀ S ∈ W.powersetCard s,
      ∃ I : Finset V, I ⊆ S ∧ I.card = 2 * h ∧
        G.IsIndepSet (I : Set V)) :
    ∃ I : Finset V, I ⊆ W ∧ G.IsIndepSet (I : Set V) ∧
      q * h ≤ I.card := by
  classical
  induction q generalizing W with
  | zero =>
      exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ q ih =>
      let D := 2 * s ^ 2
      have hDpos : 0 < D := by
        dsimp only [D]
        positivity
      have hsW : s ≤ W.card := by
        have hsbase : s ≤ s * D ^ (q + 1) := by
          have hpowpos : 0 < D ^ (q + 1) := pow_pos hDpos _
          nlinarith
        exact hsbase.trans (by simpa only [D, Nat.succ_eq_add_one] using hroom)
      obtain ⟨X, R, hXW, hXcard, hXind, hRWX, hanti, hWR⟩ :=
        exists_anticomplete_block G W s h hh (hfour.trans hsW)
          (by omega) hsW hlocal
      have hroomR : s * D ^ q ≤ R.card := by
        have hmul : (s * D ^ q) * D ≤ R.card * D := by
          calc
            (s * D ^ q) * D = s * D ^ (q + 1) := by
              rw [pow_succ]
              ac_rfl
            _ ≤ W.card := by
              simpa only [D, Nat.succ_eq_add_one] using hroom
            _ ≤ R.card * D := by
              simpa only [D, mul_assoc, mul_comm, mul_left_comm] using hWR
        exact Nat.le_of_mul_le_mul_right hmul hDpos
      have hlocalR : ∀ S ∈ R.powersetCard s,
          ∃ I : Finset V, I ⊆ S ∧ I.card = 2 * h ∧
            G.IsIndepSet (I : Set V) := by
        intro S hS
        have hSW : S ⊆ W :=
          (Finset.mem_powersetCard.mp hS).1.trans
            (hRWX.trans Finset.sdiff_subset)
        exact hlocal S (Finset.mem_powersetCard.mpr
          ⟨hSW, (Finset.mem_powersetCard.mp hS).2⟩)
      obtain ⟨J, hJR, hJind, hJcard⟩ :=
        ih R hroomR hlocalR
      have hXJ : Disjoint X J := by
        refine Finset.disjoint_left.mpr ?_
        intro v hvX hvJ
        exact (Finset.mem_sdiff.mp (hRWX (hJR hvJ))).2 hvX
      have hunionInd : G.IsIndepSet ((X ∪ J : Finset V) : Set V) := by
        rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hab
        have ha' : a ∈ X ∨ a ∈ J := by simpa using ha
        have hb' : b ∈ X ∨ b ∈ J := by simpa using hb
        rcases ha' with haX | haJ <;> rcases hb' with hbX | hbJ
        · exact hXind haX hbX hab
        · exact hanti a haX b (hJR hbJ)
        · intro hab'
          exact hanti b hbX a (hJR haJ) ((G.adj_comm a b).mp hab')
        · exact hJind haJ hbJ hab
      refine ⟨X ∪ J, Finset.union_subset hXW
        (hJR.trans (hRWX.trans Finset.sdiff_subset)),
        hunionInd, ?_⟩
      rw [Finset.card_union_of_disjoint hXJ, hXcard]
      simpa only [Nat.succ_eq_add_one, add_mul, one_mul, add_comm] using
        Nat.add_le_add_left hJcard h

/-- Finite lower bound stated directly for the extremal problem.  The even
threshold `2 * (t / 2)` is extracted from the local `t`-set, so no parity
assumption is needed. -/
theorem lower_bound_finite
    {n s t q : ℕ} (ht : 2 ≤ t) (hfour : 4 * (t / 2) ≤ s)
    (hroom : s * (2 * s ^ 2) ^ q ≤ n) :
    GuaranteesIndependence n s t (q * (t / 2)) := by
  intro G hG
  classical
  let h := t / 2
  have hh : 0 < h := by
    dsimp only [h]
    omega
  have hs : 0 < s := by omega
  have hevenle : 2 * h ≤ t := by
    dsimp only [h]
    omega
  have hlocalEven : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      ∃ I : Finset (Fin n), I ⊆ S ∧ I.card = 2 * h ∧
        G.IsIndepSet (I : Set (Fin n)) := by
    intro S hS
    obtain ⟨I, hIS, hIt⟩ := hG S (Finset.mem_powersetCard.mp hS).2
    obtain ⟨J, hJI, hJcard⟩ :=
      Finset.exists_subset_card_eq (show 2 * h ≤ I.card by
        rw [hIt.card_eq]
        exact hevenle)
    exact ⟨J, hJI.trans hIS, hJcard, hIt.isIndepSet.mono hJI⟩
  obtain ⟨I, _hIuniv, hIind, hIcard⟩ :=
    exists_independent_of_geometric_room G Finset.univ s h q hh hs hfour
      (by simpa using hroom) hlocalEven
  exact (by simpa only [h] using hIcard.trans hIind.card_le_indepNum)

/-! ## Exact finite counting for the upper bounds -/

/-- A coloring of `k` coordinates by `d + 1` colors is good when color zero
appears.  In the random-graph application zero means that the corresponding
edge is present. -/
abbrev GoodColoring (d k : ℕ) :=
  {f : Fin k → Fin (d + 1) // ∃ i, f i = 0}

abbrev NonzeroColoring (d k : ℕ) :=
  {f : Fin k → Fin (d + 1) // ∀ i, f i ≠ 0}

def nonzeroColoringEquiv (d k : ℕ) :
    NonzeroColoring d k ≃ (Fin k → {x : Fin (d + 1) // x ≠ 0}) where
  toFun f i := ⟨f.1 i, f.2 i⟩
  invFun f := ⟨fun i ↦ (f i).1, fun i hx ↦ (f i).2 hx⟩
  left_inv f := by cases f; rfl
  right_inv f := by funext i; rfl

lemma card_fin_nonzero (d : ℕ) :
    Fintype.card {x : Fin (d + 1) // x ≠ 0} = d := by
  rw [Fintype.card_subtype_compl (fun x : Fin (d + 1) ↦ x = 0)]
  simp

lemma card_nonzeroColoring (d k : ℕ) :
    Fintype.card (NonzeroColoring d k) = d ^ k := by
  rw [Fintype.card_congr (nonzeroColoringEquiv d k), Fintype.card_pi]
  simp

lemma card_goodColoring (d k : ℕ) :
    Fintype.card (GoodColoring d k) = (d + 1) ^ k - d ^ k := by
  have hcompl : Fintype.card (NonzeroColoring d k) =
      Fintype.card (Fin k → Fin (d + 1)) - Fintype.card (GoodColoring d k) := by
    simpa only [GoodColoring, NonzeroColoring, not_exists] using
      (Fintype.card_subtype_compl
        (fun f : Fin k → Fin (d + 1) ↦ ∃ i, f i = 0))
  rw [card_nonzeroColoring, Fintype.card_pi] at hcompl
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hcompl
  have hpow : d ^ k ≤ (d + 1) ^ k :=
    Nat.pow_le_pow_left (by omega) k
  have hgoodle : Fintype.card (GoodColoring d k) ≤ (d + 1) ^ k := by
    simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ] using
      (Fintype.card_subtype_le
        (fun f : Fin k → Fin (d + 1) ↦ ∃ i, f i = 0))
  omega

section DisjointCoordinateGroups

variable {E J : Type*} [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J]

/-- Restrict a coloring to each constrained group and to the complement of
their union. -/
def groupEncoding (d k : ℕ) (A : J → Finset E)
    (hcard : ∀ i, (A i).card = k)
    (f : {f : E → Fin (d + 1) // ∀ i, ∃ e ∈ A i, f e = 0}) :
    (J → GoodColoring d k) ×
      ({e : E // e ∉ (Finset.univ : Finset J).biUnion A} → Fin (d + 1)) :=
  (fun i ↦ (⟨fun j ↦ f.1 (((A i).equivFinOfCardEq (hcard i)).symm j), by
      obtain ⟨e, heA, he0⟩ := f.2 i
      let eA : ↑(A i) := ⟨e, heA⟩
      refine ⟨(A i).equivFinOfCardEq (hcard i) eA, ?_⟩
      simpa [eA] using he0⟩ : GoodColoring d k),
    fun e ↦ f.1 e)

lemma groupEncoding_injective (d k : ℕ) (A : J → Finset E)
    (hcard : ∀ i, (A i).card = k) :
    Function.Injective (groupEncoding d k A hcard) := by
  intro f f' heq
  apply Subtype.ext
  funext e
  by_cases heC : e ∈ (Finset.univ : Finset J).biUnion A
  · obtain ⟨i, _hi, heA⟩ := Finset.mem_biUnion.mp heC
    let eA : ↑(A i) := ⟨e, heA⟩
    let j : Fin k := (A i).equivFinOfCardEq (hcard i) eA
    have hfst := congrArg Prod.fst heq
    have hi := congrFun hfst i
    have hj := congrFun (congrArg Subtype.val hi) j
    simpa [groupEncoding, j, eA] using hj
  · let efree : {x : E // x ∉ (Finset.univ : Finset J).biUnion A} :=
      ⟨e, heC⟩
    have hsnd := congrArg Prod.snd heq
    have he := congrFun hsnd efree
    simpa [groupEncoding, efree] using he

/-- Exact product-space counting, in the upper-bound form needed later: if
`J` pairwise-disjoint groups each contain `k` coordinates, then color zero
appearing in every group costs the factor
`((d+1)^k-d^k) ^ card J`. -/
theorem card_group_constrained_le
    (d k : ℕ) (A : J → Finset E)
    (hcard : ∀ i, (A i).card = k)
    (hdisj : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint A) :
    Fintype.card {f : E → Fin (d + 1) // ∀ i, ∃ e ∈ A i, f e = 0} ≤
      ((d + 1) ^ k - d ^ k) ^ Fintype.card J *
        (d + 1) ^ (Fintype.card E - Fintype.card J * k) := by
  let C := (Finset.univ : Finset J).biUnion A
  have hCcard : C.card = Fintype.card J * k := by
    rw [Finset.card_biUnion hdisj]
    simp [hcard]
  have hinj := groupEncoding_injective d k A hcard
  have hle := Fintype.card_le_of_injective (groupEncoding d k A hcard) hinj
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi] at hle
  simp only [card_goodColoring, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hle
  have hfree :
      Fintype.card {e : E // e ∉ C} =
        Fintype.card E - Fintype.card J * k := by
    rw [Fintype.card_subtype_compl (fun e : E ↦ e ∈ C)]
    simp only [Fintype.card_coe, hCcard]
  simpa only [C, hfree] using hle

end DisjointCoordinateGroups

section OneCoordinateSet

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Count colorings whose values on a fixed coordinate set lie in a fixed
set of allowed colors. -/
theorem card_colorings_allowed_on (d : ℕ) (A : Finset E)
    (T : Finset (Fin (d + 1))) :
    Fintype.card {f : E → Fin (d + 1) // ∀ e ∈ A, f e ∈ T} =
      T.card ^ A.card * (d + 1) ^ (Fintype.card E - A.card) := by
  classical
  let choices : E → Finset (Fin (d + 1)) := fun e ↦
    if e ∈ A then T else Finset.univ
  have heq :
      (Finset.univ.filter fun f : E → Fin (d + 1) ↦ ∀ e ∈ A, f e ∈ T) =
        Fintype.piFinset choices := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, choices]
    constructor
    · intro hf e
      split_ifs with he
      · exact hf e he
      · exact Finset.mem_univ _
    · intro hf e he
      simpa [he] using hf e
  have hcardSubtype :
      Fintype.card {f : E → Fin (d + 1) // ∀ e ∈ A, f e ∈ T} =
        #(Finset.univ.filter fun f : E → Fin (d + 1) ↦ ∀ e ∈ A, f e ∈ T) := by
    calc
      Fintype.card {f : E → Fin (d + 1) // ∀ e ∈ A, f e ∈ T} =
          #(Finset.univ : Finset
            {f : E → Fin (d + 1) // ∀ e ∈ A, f e ∈ T}) := by simp
      _ = #((Finset.univ : Finset (E → Fin (d + 1))).subtype
            (fun f ↦ ∀ e ∈ A, f e ∈ T)) := by
          congr 1
          ext f
          simp
      _ = _ := Finset.card_subtype _ _
  rw [hcardSubtype, heq, Fintype.card_piFinset]
  simp only [choices]
  change (∏ x ∈ (Finset.univ : Finset E),
    #(if x ∈ A then T else (Finset.univ : Finset (Fin (d + 1))))) = _
  simp only [apply_ite, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite]
  have hfilter :
      (Finset.univ : Finset E).filter (fun x ↦ x ∈ A) = A := by
    ext x
    simp
  have hfilterNot :
      (Finset.univ : Finset E).filter (fun x ↦ x ∉ A) =
        (Finset.univ : Finset E) \ A := by
    ext x
    simp
  rw [Finset.prod_const, Finset.prod_const, hfilter, hfilterNot,
    Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]

end OneCoordinateSet

/-! ### Edge coordinates -/

/-- All unordered non-loop pairs spanned by a finite vertex set. -/
noncomputable def pairEdgeFinset {W : Type*} [DecidableEq W] (s : Finset W) :
    Finset (Sym2 W) :=
  ((⊤ : SimpleGraph {x // x ∈ (↑s : Set W)}).edgeFinset).map
    (Function.Embedding.subtype (fun x ↦ x ∈ (↑s : Set W))).sym2Map

lemma pairEdgeFinset_card {W : Type*} [DecidableEq W] (s : Finset W) :
    (pairEdgeFinset s).card = Nat.choose s.card 2 := by
  classical
  calc
    (pairEdgeFinset s).card =
        ((⊤ : SimpleGraph {x // x ∈ (↑s : Set W)}).edgeFinset).card :=
      Finset.card_map _
    _ = Nat.choose (Fintype.card {x // x ∈ (↑s : Set W)}) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose s.card 2 := by simp

lemma mem_pairEdgeFinset_iff {W : Type*} [Finite W] [DecidableEq W]
    (s : Finset W) {e : Sym2 W} :
    e ∈ pairEdgeFinset s ↔ e ∈ s.sym2 ∧ ¬ e.IsDiag := by
  classical
  let := Fintype.ofFinite W
  have hmap := SimpleGraph.map_edgeFinset_induce
    (G := (⊤ : SimpleGraph W)) (s := (↑s : Set W))
  have hind : SimpleGraph.induce (↑s : Set W) (⊤ : SimpleGraph W) =
      (⊤ : SimpleGraph {x // x ∈ (↑s : Set W)}) := by
    ext a b
    simp [SimpleGraph.induce]
  have hmem := Finset.ext_iff.mp hmap e
  simpa [and_comm, pairEdgeFinset, hind, SimpleGraph.mem_edgeFinset,
    Finset.mem_inter, Finset.mk_mem_sym2_iff] using hmem

lemma pairEdgeFinset_subset_diagCompl {W : Type*} [Finite W] [DecidableEq W]
    (s : Finset W) :
    (↑(pairEdgeFinset s) : Set (Sym2 W)) ⊆ Sym2.diagSetᶜ := by
  classical
  let := Fintype.ofFinite W
  intro e he
  simpa [Set.compl_ofPred] using (mem_pairEdgeFinset_iff s).1 he |>.2

lemma isIndepSet_iff_pairEdgeFinset_disjoint
    {W : Type*} [Finite W] [DecidableEq W]
    (G : SimpleGraph W) (s : Finset W) :
    G.IsIndepSet (↑s : Set W) ↔
      Disjoint (↑(pairEdgeFinset s) : Set (Sym2 W)) G.edgeSet := by
  classical
  let := Fintype.ofFinite W
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro e he hedg
    revert he hedg
    refine Sym2.inductionOn e ?_
    intro a b he' hedg'
    rcases (mem_pairEdgeFinset_iff s).1 he' with ⟨hmem, hndiag⟩
    have ha : a ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).1
    have hb : b ∈ s := (Finset.mk_mem_sym2_iff.mp hmem).2
    have hab : a ≠ b := by simpa using hndiag
    exact h ha hb hab (by simpa [SimpleGraph.mem_edgeSet] using hedg')
  · intro h a ha b hb hab hedg
    have he : (s(a, b) : Sym2 W) ∈ pairEdgeFinset s := by
      exact (mem_pairEdgeFinset_iff s).2
        ⟨by simpa [Finset.mk_mem_sym2_iff] using And.intro ha hb,
          by simpa using hab⟩
    exact h.le_bot ⟨he, by simpa [SimpleGraph.mem_edgeSet] using hedg⟩

/-- Turn an independent uniform `(d+1)`-coloring of unordered pairs into a
simple graph by declaring precisely the zero-colored non-loop pairs to be
edges. -/
def coloredGraph {W : Type*} (d : ℕ) (f : Sym2 W → Fin (d + 1)) :
    SimpleGraph W := SimpleGraph.fromEdgeSet {e | f e = 0}

theorem coloredGraph_isIndepSet_iff
    {W : Type*} [Finite W] [DecidableEq W]
    (d : ℕ) (f : Sym2 W → Fin (d + 1)) (s : Finset W) :
    (coloredGraph d f).IsIndepSet (s : Set W) ↔
      ∀ e ∈ pairEdgeFinset s, f e ≠ 0 := by
  rw [isIndepSet_iff_pairEdgeFinset_disjoint, coloredGraph,
    SimpleGraph.edgeSet_fromEdgeSet, Set.disjoint_left]
  constructor
  · intro h e he hzero
    exact h he ⟨hzero, pairEdgeFinset_subset_diagCompl s he⟩
  · intro h e he hedge
    exact h e he hedge.1

/-- Pair-colorings for which a prescribed vertex set is independent. -/
noncomputable def independentColorings
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (s : Finset W) : Finset (Sym2 W → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦
    (coloredGraph d f).IsIndepSet (s : Set W)

/-- Exact number of pair-colorings for which a prescribed vertex set is
independent. -/
theorem card_independentColorings
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (s : Finset W) :
    #(independentColorings d s) =
      d ^ Nat.choose s.card 2 *
        (d + 1) ^ (Fintype.card (Sym2 W) - Nat.choose s.card 2) := by
  classical
  let T : Finset (Fin (d + 1)) := Finset.univ.erase 0
  let e : {f : Sym2 W → Fin (d + 1) //
      (coloredGraph d f).IsIndepSet (s : Set W)} ≃
      {f : Sym2 W → Fin (d + 1) //
        ∀ a ∈ pairEdgeFinset s, f a ∈ T} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun f ↦ by
      simpa only [coloredGraph_isIndepSet_iff, T, Equiv.refl_apply,
        Finset.mem_erase, Finset.mem_univ, and_true]
  have hfilterCard : #(independentColorings d s) =
      Fintype.card {f : Sym2 W → Fin (d + 1) //
        (coloredGraph d f).IsIndepSet (s : Set W)} := by
    calc
      #(independentColorings d s) =
          #((Finset.univ : Finset (Sym2 W → Fin (d + 1))).subtype
            (fun f ↦ (coloredGraph d f).IsIndepSet (s : Set W))) := by
        rw [Finset.card_subtype]
        rfl
      _ = #(Finset.univ : Finset
          {f : Sym2 W → Fin (d + 1) //
            (coloredGraph d f).IsIndepSet (s : Set W)}) := by
        congr 1
        ext f
        simp
      _ = _ := Finset.card_univ
  rw [hfilterCard, Fintype.card_congr e, card_colorings_allowed_on,
    pairEdgeFinset_card]
  simp [T]

/-- Exact number of pair-colorings making every coordinate of `A` an edge. -/
theorem card_coloredGraph_all_present
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (A : Finset (Sym2 W)) :
    Fintype.card {f : Sym2 W → Fin (d + 1) //
      ∀ a ∈ A, f a = 0} =
      (d + 1) ^ (Fintype.card (Sym2 W) - A.card) := by
  classical
  let T : Finset (Fin (d + 1)) := {0}
  let e : {f : Sym2 W → Fin (d + 1) // ∀ a ∈ A, f a = 0} ≃
      {f : Sym2 W → Fin (d + 1) // ∀ a ∈ A, f a ∈ T} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun f ↦ by simp [T]
  rw [Fintype.card_congr e, card_colorings_allowed_on]
  simp [T]

/-- Colorings whose associated graph has an independent set of order at
least `q`. -/
noncomputable def globalBadColorings (n d q : ℕ) :
    Finset (Sym2 (Fin n) → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦ q ≤ (coloredGraph d f).indepNum

/-- First-moment count for large global independent sets. -/
theorem card_globalBadColorings_le (n d q : ℕ) :
    #(globalBadColorings n d q) ≤
      Nat.choose n q * d ^ Nat.choose q 2 *
        (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) := by
  classical
  let candidates := (Finset.univ : Finset (Fin n)).powersetCard q
  let fixedBad : Finset (Fin n) → Finset (Sym2 (Fin n) → Fin (d + 1)) :=
    fun s ↦ independentColorings d s
  have hsubset : globalBadColorings n d q ⊆
      candidates.biUnion fixedBad := by
    intro f hf
    have hq : q ≤ (coloredGraph d f).indepNum := by
      simpa [globalBadColorings] using hf
    obtain ⟨I, hI⟩ := (coloredGraph d f).exists_isNIndepSet_indepNum
    have hqI : q ≤ I.card := by simpa only [hI.card_eq] using hq
    obtain ⟨S, hSI, hScard⟩ :=
      Finset.exists_subset_card_eq (s := I) (n := q) hqI
    apply Finset.mem_biUnion.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr
      ⟨hSI.trans (Finset.subset_univ I), hScard⟩, ?_⟩
    simpa only [fixedBad, independentColorings, Finset.mem_filter,
      Finset.mem_univ, true_and] using hI.isIndepSet.mono hSI
  calc
    #(globalBadColorings n d q) ≤ #(candidates.biUnion fixedBad) :=
      Finset.card_le_card hsubset
    _ ≤ ∑ s ∈ candidates, #(fixedBad s) := Finset.card_biUnion_le
    _ = ∑ _s ∈ candidates,
        d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hscard := (Finset.mem_powersetCard.mp hs).2
      change #(independentColorings d s) = _
      simpa only [hscard] using card_independentColorings d s
    _ = Nat.choose n q * d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp only [nsmul_eq_mul]
      rw [Finset.card_univ, Fintype.card_fin]
      ac_rfl

/-- Number of zero-colored (present) pairs spanned by `s`. -/
def zeroEdgeCount {W : Type*} [DecidableEq W]
    (f : Sym2 W → Fin (d + 1)) (s : Finset W) : ℕ :=
  #((pairEdgeFinset s).filter fun e ↦ f e = 0)

/-- A graph and its complement partition all unordered non-loop pairs. -/
theorem card_edgeFinset_add_compl
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card =
      Nat.choose (Fintype.card V) 2 := by
  have heq : Gᶜ.edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset := by
    ext e
    refine Sym2.inductionOn e ?_
    intro a b
    simp [SimpleGraph.mem_edgeFinset]
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro a b hab
    have hadj : G.Adj a b := by
      simpa [SimpleGraph.mem_edgeFinset] using hab
    simpa [SimpleGraph.mem_edgeFinset] using G.ne_of_adj hadj
  have hcardle := Finset.card_le_card hsub
  rw [heq, Finset.card_sdiff_of_subset hsub,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at *
  omega

/-- The complement form of Turán's theorem: if `G` has no independent
`t`-set, then `G` has the stated minimum number of edges.  This exact
natural-number inequality is convenient for the local first-moment
construction below. -/
theorem turan_edge_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] {t : ℕ}
    (ht : 2 ≤ t) (hind : G.indepNum < t) :
    Fintype.card V * (Fintype.card V - (t - 1)) ≤
      2 * (t - 1) * G.edgeFinset.card := by
  let N := Fintype.card V
  let r := t - 1
  have hr : 0 < r := by omega
  have hcf : Gᶜ.CliqueFree (r + 1) := by
    intro I hI
    have hI' : G.IsNIndepSet t I := by
      have hIr : G.IsNIndepSet (r + 1) I := by simpa using hI
      have hrt : r + 1 = t := by
        simp [r, Nat.sub_add_cancel (show 1 ≤ t from by omega)]
      simpa only [hrt] using hIr
    have hle := hI'.isIndepSet.card_le_indepNum
    rw [hI'.card_eq] at hle
    omega
  obtain ⟨M, _inst, hM⟩ := SimpleGraph.exists_isTuranMaximal (V := V) hr
  have hcompM : Gᶜ.edgeFinset.card ≤ M.edgeFinset.card := hM.2 hcf
  obtain ⟨e⟩ := hM.nonempty_iso_turanGraph
  have hMcard : M.edgeFinset.card =
      (SimpleGraph.turanGraph N r).edgeFinset.card := by
    simpa [N] using e.card_edgeFinset_eq
  have hturan :
      2 * r * (SimpleGraph.turanGraph N r).edgeFinset.card ≤
        (r - 1) * N ^ 2 :=
    SimpleGraph.mul_card_edgeFinset_turanGraph_le
  have hcompBound : 2 * r * Gᶜ.edgeFinset.card ≤ (r - 1) * N ^ 2 := by
    calc
      2 * r * Gᶜ.edgeFinset.card ≤ 2 * r * M.edgeFinset.card := by
        gcongr
      _ = 2 * r * (SimpleGraph.turanGraph N r).edgeFinset.card := by rw [hMcard]
      _ ≤ (r - 1) * N ^ 2 := hturan
  have hsum0 : G.edgeFinset.card + Gᶜ.edgeFinset.card =
      Nat.choose N 2 := by
    simpa [N] using card_edgeFinset_add_compl G
  have htwice : 2 * Nat.choose N 2 = N * (N - 1) := by
    rw [mul_comm, Nat.choose_two_right,
      Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd]
  have hsum :
      2 * r * G.edgeFinset.card + 2 * r * Gᶜ.edgeFinset.card =
        r * N * (N - 1) := by
    calc
      _ = 2 * r * (G.edgeFinset.card + Gᶜ.edgeFinset.card) := by ring
      _ = 2 * r * Nat.choose N 2 := by rw [hsum0]
      _ = r * (2 * Nat.choose N 2) := by ring
      _ = r * (N * (N - 1)) := by rw [htwice]
      _ = r * N * (N - 1) := by ring
  by_cases hrN : r ≤ N
  · have hN : 1 ≤ N := hr.trans_le hrN
    have hr1 : 1 ≤ r := hr
    have hcompBoundZ0 :
        ((2 * r * Gᶜ.edgeFinset.card : ℕ) : ℤ) ≤
          (((r - 1) * N ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hcompBound
    have hcompBoundZ :
        (2 : ℤ) * r * Gᶜ.edgeFinset.card ≤ (r - 1) * N ^ 2 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_sub hr1, Nat.cast_pow] using hcompBoundZ0
    have hsumZ0 :
        ((2 * r * G.edgeFinset.card +
            2 * r * Gᶜ.edgeFinset.card : ℕ) : ℤ) =
          ((r * N * (N - 1) : ℕ) : ℤ) := by
      exact_mod_cast hsum
    have hsumZ :
        (2 : ℤ) * r * G.edgeFinset.card +
            2 * r * Gᶜ.edgeFinset.card = r * N * (N - 1) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_sub hN] using hsumZ0
    have htargetZ :
        (N : ℤ) * (N - r) ≤ 2 * r * G.edgeFinset.card := by
      nlinarith
    exact_mod_cast htargetZ
  · simp [N, r, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hrN)]

/-- The combinatorial zero count is exactly the edge count of the graph
induced on the chosen vertex set. -/
theorem zeroEdgeCount_eq_card_induce
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (f : Sym2 W → Fin (d + 1)) (S : Finset W)
    [DecidableRel (coloredGraph d f).Adj] :
    zeroEdgeCount f S =
      #((coloredGraph d f).induce (↑S : Set W)).edgeFinset := by
  classical
  rw [← SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  apply congrArg Finset.card
  ext e
  refine Sym2.inductionOn e ?_
  intro a b
  rw [Finset.mem_filter, Finset.mem_filter,
    mem_pairEdgeFinset_iff, SimpleGraph.mem_edgeFinset]
  simp [Finset.mk_mem_sym2_iff, SimpleGraph.mem_edgeSet, coloredGraph,
    SimpleGraph.fromEdgeSet_adj, Sym2.toFinset_mk_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff,
    and_assoc, and_left_comm, and_comm]

/-- Arithmetic form of the density consequence used with Turán's theorem. -/
theorem square_density_arithmetic {s t e : ℕ}
    (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (hT : s * (s - (t - 1)) ≤ 2 * (t - 1) * e) :
    s * s ≤ 4 * t * e := by
  have hts : t - 1 ≤ s := by omega
  have hcast :
      ((s * (s - (t - 1)) : ℕ) : ℤ) ≤
        ((2 * (t - 1) * e : ℕ) : ℤ) := by
    exact_mod_cast hT
  have hTz :
      (s : ℤ) * (s - (t - 1)) ≤ 2 * (t - 1) * e := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub (show 1 ≤ t from by omega), Nat.cast_sub hts] using hcast
  have hstz0 : (((2 * (t - 1) : ℕ) : ℤ) ≤ (s : ℤ)) := by
    exact_mod_cast hst
  have hstz : (2 : ℤ) * (t - 1) ≤ s := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub (show 1 ≤ t from by omega)] using hstz0
  have hgoalz : (s : ℤ) * s ≤ 4 * t * e := by
    nlinarith [show (0 : ℤ) ≤ e by positivity]
  exact_mod_cast hgoalz

/-- If every `s`-set spans fewer than the Turán density threshold,
then every such set contains an independent `t`-set. -/
theorem hasLocalIndependence_of_sparse_coloring
    {n d s t : ℕ} (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (f : Sym2 (Fin n) → Fin (d + 1))
    (hsparse : ∀ S : Finset (Fin n), S.card = s →
      4 * t * zeroEdgeCount f S < s * s) :
    HasLocalIndependence (coloredGraph d f) s t := by
  classical
  intro S hScard
  let H := (coloredGraph d f).induce (↑S : Set (Fin n))
  have hnotSmall : ¬ H.indepNum < t := by
    intro hind
    have hT0 := turan_edge_lower_bound H ht hind
    have hcard : Fintype.card {x // x ∈ (↑S : Set (Fin n))} = s := by
      simpa [hScard]
    have hT : s * (s - (t - 1)) ≤
        2 * (t - 1) * H.edgeFinset.card := by
      simpa only [hcard] using hT0
    have hdense := square_density_arithmetic ht hst hT
    have hedge : zeroEdgeCount f S = H.edgeFinset.card := by
      simpa only [H] using zeroEdgeCount_eq_card_induce d f S
    rw [← hedge] at hdense
    exact (Nat.not_lt_of_ge hdense) (hsparse S hScard)
  have htInd : t ≤ H.indepNum := Nat.le_of_not_gt hnotSmall
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  obtain ⟨J, hJI, hJcard⟩ :=
    Finset.exists_subset_card_eq (s := I) (n := t) (by simpa [hI.card_eq] using htInd)
  have hJind : H.IsNIndepSet t J := by
    refine ⟨hI.isIndepSet.mono ?_, hJcard⟩
    exact_mod_cast hJI
  let j : {x // x ∈ (↑S : Set (Fin n))} ↪ Fin n :=
    ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨J.map j, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  · have hJind' : ((coloredGraph d f).induce (↑S : Set (Fin n))).IsNIndepSet t J := by
      simpa only [H] using hJind
    rw [SimpleGraph.induce_eq_coe_induce_top] at hJind'
    have hJambient : (coloredGraph d f).IsNIndepSet t (J.map j) := by
      simpa only [j] using
        (SimpleGraph.isNIndepSet_induce (G := coloredGraph d f) (F := (↑S : Set (Fin n)))
          (s := J) (n := t)).mp hJind'
    exact hJambient

/-- Colorings making every coordinate in `A` present. -/
noncomputable def presentColorings
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (A : Finset (Sym2 W)) :
    Finset (Sym2 W → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦ ∀ a ∈ A, f a = 0

theorem card_presentColorings
    {W : Type*} [Fintype W] [DecidableEq W]
    (d : ℕ) (A : Finset (Sym2 W)) :
    #(presentColorings d A) =
      (d + 1) ^ (Fintype.card (Sym2 W) - A.card) := by
  classical
  have hfilterCard : #(presentColorings d A) =
      Fintype.card {f : Sym2 W → Fin (d + 1) // ∀ a ∈ A, f a = 0} := by
    calc
      #(presentColorings d A) =
          #((Finset.univ : Finset (Sym2 W → Fin (d + 1))).subtype
            (fun f ↦ ∀ a ∈ A, f a = 0)) := by
        rw [Finset.card_subtype]
        rfl
      _ = #(Finset.univ : Finset
          {f : Sym2 W → Fin (d + 1) // ∀ a ∈ A, f a = 0}) := by
        congr 1
        ext f
        simp
      _ = _ := Finset.card_univ
  rw [hfilterCard]
  exact card_coloredGraph_all_present d A

/-- Colorings for which some `s`-vertex set spans at least `r` present
edges. -/
noncomputable def denseLocalBadColorings (n d s r : ℕ) :
    Finset (Sym2 (Fin n) → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦
    ∃ S : Finset (Fin n), S.card = s ∧ r ≤ zeroEdgeCount f S

/-- Union-bound count for the dense local obstruction. -/
theorem card_denseLocalBadColorings_le (n d s r : ℕ) :
    #(denseLocalBadColorings n d s r) ≤
      Nat.choose n s * Nat.choose (Nat.choose s 2) r *
        (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) := by
  classical
  let vertexSets := (Finset.univ : Finset (Fin n)).powersetCard s
  let edgeSets : Finset (Fin n) → Finset (Finset (Sym2 (Fin n))) :=
    fun S ↦ (pairEdgeFinset S).powersetCard r
  let fixed : Finset (Sym2 (Fin n)) →
      Finset (Sym2 (Fin n) → Fin (d + 1)) := fun A ↦ presentColorings d A
  have hsubset : denseLocalBadColorings n d s r ⊆
      vertexSets.biUnion fun S ↦ (edgeSets S).biUnion fixed := by
    intro f hf
    obtain ⟨S, hScard, hredges⟩ :
        ∃ S : Finset (Fin n), S.card = s ∧ r ≤ zeroEdgeCount f S := by
      simpa [denseLocalBadColorings] using hf
    let present := (pairEdgeFinset S).filter fun e ↦ f e = 0
    obtain ⟨A, hApresent, hAcard⟩ :=
      Finset.exists_subset_card_eq (s := present) (n := r) hredges
    apply Finset.mem_biUnion.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, hScard⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨?_, hAcard⟩, ?_⟩
    · exact hApresent.trans (Finset.filter_subset _ _)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a ha
      exact (Finset.mem_filter.mp (hApresent ha)).2
  calc
    #(denseLocalBadColorings n d s r) ≤
        #(vertexSets.biUnion fun S ↦ (edgeSets S).biUnion fixed) :=
      Finset.card_le_card hsubset
    _ ≤ ∑ S ∈ vertexSets, #((edgeSets S).biUnion fixed) :=
      Finset.card_biUnion_le
    _ ≤ ∑ S ∈ vertexSets, ∑ A ∈ edgeSets S, #(fixed A) := by
      exact Finset.sum_le_sum fun S _hS ↦ Finset.card_biUnion_le
    _ = ∑ S ∈ vertexSets,
        Nat.choose (Nat.choose s 2) r *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      calc
        ∑ A ∈ edgeSets S, #(fixed A) =
            ∑ _A ∈ edgeSets S,
              (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) := by
          apply Finset.sum_congr rfl
          intro A hA
          have hAcard := (Finset.mem_powersetCard.mp hA).2
          change #(presentColorings d A) = _
          simpa only [hAcard] using card_presentColorings d A
        _ = Nat.choose (Nat.choose s 2) r *
              (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) := by
          rw [Finset.sum_const, Finset.card_powersetCard,
            pairEdgeFinset_card, hScard]
          simp [nsmul_eq_mul]
    _ = Nat.choose n s * Nat.choose (Nat.choose s 2) r *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) := by
      rw [Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Finite first-moment certificate for the square-window construction.
The displayed strict inequality is precisely the sum of the local and
global union bounds being smaller than the number of all colorings. -/
theorem exists_square_coloring_witness
    {n d s t q r : ℕ}
    (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (hr : 4 * t * r ≤ s * s)
    (hcount :
      Nat.choose n s * Nat.choose (Nat.choose s 2) r *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) +
        Nat.choose n q * d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) <
        (d + 1) ^ Fintype.card (Sym2 (Fin n))) :
    ∃ G : SimpleGraph (Fin n),
      HasLocalIndependence G s t ∧ G.indepNum < q := by
  classical
  let localBad := denseLocalBadColorings n d s r
  let globalBad := globalBadColorings n d q
  let all : Finset (Sym2 (Fin n) → Fin (d + 1)) := Finset.univ
  have hbadCard : #(localBad ∪ globalBad) < #all := by
    have hlocal := card_denseLocalBadColorings_le n d s r
    have hglobal := card_globalBadColorings_le n d q
    have hunion : #(localBad ∪ globalBad) ≤ #localBad + #globalBad :=
      Finset.card_union_le localBad globalBad
    have htotal : #all = (d + 1) ^ Fintype.card (Sym2 (Fin n)) := by
      simp [all]
    rw [htotal]
    exact lt_of_le_of_lt (hunion.trans (Nat.add_le_add hlocal hglobal)) hcount
  obtain ⟨f, _hfall, hfbad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadCard
  have hflocal : f ∉ localBad := by
    intro hf
    exact hfbad (Finset.mem_union_left globalBad hf)
  have hfglobal : f ∉ globalBad := by
    intro hf
    exact hfbad (Finset.mem_union_right localBad hf)
  refine ⟨coloredGraph d f, ?_, ?_⟩
  · apply hasLocalIndependence_of_sparse_coloring ht hst f
    intro S hScard
    have hnot : ¬ r ≤ zeroEdgeCount f S := by
      intro hre
      apply hflocal
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, S, hScard, hre⟩
    have hz : zeroEdgeCount f S < r := Nat.lt_of_not_ge hnot
    have htpos : 0 < 4 * t := by positivity
    exact lt_of_lt_of_le ((Nat.mul_lt_mul_left htpos).2 hz) hr
  · have hnot : ¬ q ≤ (coloredGraph d f).indepNum := by
      intro hq
      apply hfglobal
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    exact Nat.lt_of_not_ge hnot

/-- The finite extremal upper bound extracted from the square-window
coloring witness. -/
theorem square_upper_bound_finite
    {n d s t q r : ℕ}
    (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (hr : 4 * t * r ≤ s * s)
    (hcount :
      Nat.choose n s * Nat.choose (Nat.choose s 2) r *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - r) +
        Nat.choose n q * d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) <
        (d + 1) ^ Fintype.card (Sym2 (Fin n))) :
    localIndependenceNumber n s t < q := by
  obtain ⟨G, hlocal, hglobal⟩ :=
    exists_square_coloring_witness ht hst hr hcount
  exact lt_of_le_of_lt (localIndependenceNumber_le_of_witness hlocal) hglobal

/-! ## Greedy domination certificates for the cubic upper bound -/

/-- Independence number cannot increase on passing to an induced subgraph. -/
theorem indepNum_induce_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (U : Finset W) :
    (G.induce (↑U : Set W)).indepNum ≤ G.indepNum := by
  classical
  let H := G.induce (↑U : Set W)
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  have hI' : (G.induce (↑U : Set W)).IsNIndepSet H.indepNum I := by
    simpa only [H] using hI
  rw [SimpleGraph.induce_eq_coe_induce_top] at hI'
  let j : {x // x ∈ (↑U : Set W)} ↪ W :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hambient : G.IsNIndepSet H.indepNum (I.map j) := by
    simpa only [j] using
      (SimpleGraph.isNIndepSet_induce (G := G) (F := (↑U : Set W))
        (s := I) (n := H.indepNum)).mp hI'
  have hle := hambient.isIndepSet.card_le_indepNum
  rw [hambient.card_eq] at hle
  simpa only [H] using hle

/-- Monotonicity of the independence number for nested induced subgraphs. -/
theorem indepNum_induce_mono
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) {U V : Finset W} (hUV : U ⊆ V) :
    (G.induce (↑U : Set W)).indepNum ≤
      (G.induce (↑V : Set W)).indepNum := by
  classical
  let HU := G.induce (↑U : Set W)
  let HV := G.induce (↑V : Set W)
  obtain ⟨I, hI⟩ := HU.exists_isNIndepSet_indepNum
  let j : {x // x ∈ (↑U : Set W)} ↪ {x // x ∈ (↑V : Set W)} :=
    ⟨fun x ↦ ⟨x.1, hUV x.2⟩, fun x y h ↦
      Subtype.ext (congrArg (fun z : {x // x ∈ (↑V : Set W)} ↦ z.1) h)⟩
  have hmap : HV.IsNIndepSet HU.indepNum (I.map j) := by
    refine ⟨?_, by simpa [j] using hI.card_eq⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    obtain ⟨x, hxI, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hyI, rfl⟩ := Finset.mem_map.mp hb
    have hxy : x ≠ y := by
      intro hxy
      apply hab
      subst y
      rfl
    have hnot := hI.isIndepSet hxI hyI hxy
    have hnotG : ¬ G.Adj x.1 y.1 := by
      simpa only [HU, SimpleGraph.induce_adj] using hnot
    change ¬ G.Adj x.1 y.1
    exact hnotG
  have hle := hmap.isIndepSet.card_le_indepNum
  rw [hmap.card_eq] at hle
  simpa only [HU, HV] using hle

/-- Recursive certificate saying that `r` exact `k`-blocks are removed,
and that each removed block dominates the then-remaining vertices. -/
def IsBlockCertificate {W : Type*} [DecidableEq W]
    (d : ℕ) (f : Sym2 W → Fin (d + 1)) (k : ℕ) :
    (r : ℕ) → Finset W → (Fin r → Finset W) → Prop
  | 0, _U, _B => True
  | r + 1, U, B =>
      B 0 ⊆ U ∧ (B 0).card = k ∧
      (∀ v ∈ U \ B 0, ∃ x ∈ B 0, f s(x, v) = 0) ∧
      IsBlockCertificate d f k r (U \ B 0) (Fin.tail B)

/-- A maximum independent set dominates every vertex outside it. -/
theorem maximumIndepSet_dominates
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} (I : Finset W) (hI : G.IsMaximumIndepSet I) :
    ∀ v ∉ I, ∃ x ∈ I, G.Adj x v := by
  classical
  intro v hv
  by_contra hnone
  push Not at hnone
  have hins : G.IsIndepSet (↑(insert v I) : Set W) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact fun hadj ↦ hnone b hb hadj.symm
    · exact fun hadj ↦ hnone a ha hadj
    · exact hI.isIndepSet ha hb hab
  have hmax := hI.isMaximalIndepSet I
  have heq := hmax.2 hins (by simp)
  have : v ∈ I := by
    have hvins : v ∈ (↑(insert v I) : Set W) := by simp
    exact heq hvins
  exact hv this

/-- If the associated graph has independence number below `k`, the greedy
maximal-independent-set procedure supplies any number of domination blocks
for which there is room. -/
theorem exists_blockCertificate_of_indepNum_lt
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} (f : Sym2 W → Fin (d + 1)) (U : Finset W)
    (hind : ((coloredGraph d f).induce (↑U : Set W)).indepNum < k)
    (hroom : r * k ≤ U.card) :
    ∃ B : Fin r → Finset W, IsBlockCertificate d f k r U B := by
  classical
  induction r generalizing U with
  | zero =>
      exact ⟨fun i ↦ Fin.elim0 i, trivial⟩
  | succ r ihr =>
      have hkU : k ≤ U.card := by
        have : k ≤ (r + 1) * k := by
          rw [Nat.succ_mul]
          omega
        exact this.trans hroom
      let H := (coloredGraph d f).induce (↑U : Set W)
      have hHind : H.indepNum < k := by simpa only [H] using hind
      obtain ⟨I, hImax⟩ := H.maximumIndepSet_exists
      have hIcard : I.card = H.indepNum :=
        H.maximumIndepSet_card_eq_indepNum I hImax
      have hIle : I.card ≤ k := by omega
      have hkSubtype : k ≤ Fintype.card {x // x ∈ (↑U : Set W)} := by
        simpa using hkU
      obtain ⟨Bsub, hIBsub, _hBuniv, hBsubcard⟩ :=
        Finset.exists_subsuperset_card_eq
          (s := I) (t := (Finset.univ : Finset {x // x ∈ (↑U : Set W)}))
          (Finset.subset_univ I) hIle hkSubtype
      let j : {x // x ∈ (↑U : Set W)} ↪ W :=
        ⟨Subtype.val, Subtype.val_injective⟩
      let B0 : Finset W := Bsub.map j
      have hB0U : B0 ⊆ U := by
        intro x hx
        obtain ⟨y, _hy, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hB0card : B0.card = k := by simpa [B0, j] using hBsubcard
      have hdom : ∀ v ∈ U \ B0, ∃ x ∈ B0, f s(x, v) = 0 := by
        intro v hv
        have hvU : v ∈ U := (Finset.mem_sdiff.mp hv).1
        have hvB0 : v ∉ B0 := (Finset.mem_sdiff.mp hv).2
        let vv : {x // x ∈ (↑U : Set W)} := ⟨v, hvU⟩
        have hvI : vv ∉ I := by
          intro hvI
          apply hvB0
          apply Finset.mem_map.mpr
          exact ⟨vv, hIBsub hvI, rfl⟩
        obtain ⟨x, hxI, hxadj⟩ := maximumIndepSet_dominates I hImax vv hvI
        refine ⟨x.1, ?_, ?_⟩
        · apply Finset.mem_map.mpr
          exact ⟨x, hIBsub hxI, rfl⟩
        · have hadj : (coloredGraph d f).Adj x.1 v := by
            simpa only [H, SimpleGraph.induce_adj] using hxadj
          have hz : f s(x.1, v) = 0 ∧ x.1 ≠ v := by
            simpa [coloredGraph, SimpleGraph.fromEdgeSet_adj] using hadj
          exact hz.1
      have hdiffcard : (U \ B0).card = U.card - k := by
        rw [Finset.card_sdiff_of_subset hB0U, hB0card]
      have htailroom : r * k ≤ (U \ B0).card := by
        rw [hdiffcard]
        rw [Nat.succ_mul] at hroom
        omega
      have htailInd :
          ((coloredGraph d f).induce (↑(U \ B0) : Set W)).indepNum < k :=
        lt_of_le_of_lt
          (indepNum_induce_mono (coloredGraph d f) Finset.sdiff_subset) hind
      obtain ⟨Btail, hBtail⟩ := ihr (U := U \ B0) htailInd htailroom
      refine ⟨Fin.cons B0 Btail, ?_⟩
      simpa [IsBlockCertificate] using
        And.intro hB0U (And.intro hB0card (And.intro hdom hBtail))

/-- The `k` edge coordinates joining a block to one outside vertex. -/
def starEdgeFinset {W : Type*} [DecidableEq W]
    (B : Finset W) (v : W) : Finset (Sym2 W) :=
  B.image fun x ↦ s(x, v)

@[simp] theorem mem_starEdgeFinset_iff
    {W : Type*} [DecidableEq W] {B : Finset W} {v : W} {e : Sym2 W} :
    e ∈ starEdgeFinset B v ↔ ∃ x ∈ B, s(x, v) = e := by
  simp [starEdgeFinset]

theorem card_starEdgeFinset
    {W : Type*} [DecidableEq W] (B : Finset W) (v : W) :
    (starEdgeFinset B v).card = B.card := by
  rw [starEdgeFinset, Finset.card_image_iff]
  intro x _hx y _hy hxy
  rcases Sym2.eq_iff.mp hxy with h | h
  · exact h.1
  · exact h.1.trans h.2

theorem starEdgeFinset_injOn
    {W : Type*} [DecidableEq W] {B R : Finset W}
    (hB : B.Nonempty) (hRB : Disjoint R B) :
    Set.InjOn (starEdgeFinset B) (↑R : Set W) := by
  intro v hv w hw heq
  obtain ⟨x, hxB⟩ := hB
  have hxe : s(x, v) ∈ starEdgeFinset B v :=
    mem_starEdgeFinset_iff.mpr ⟨x, hxB, rfl⟩
  rw [heq] at hxe
  obtain ⟨y, hyB, hyx⟩ := mem_starEdgeFinset_iff.mp hxe
  rcases Sym2.eq_iff.mp hyx with h | h
  · exact h.2.symm
  · exfalso
    have hvB : v ∈ B := h.1 ▸ hyB
    exact (Finset.disjoint_left.mp hRB) hv hvB

/-- All domination-coordinate groups generated by a recursive block
certificate. -/
def dominationGroups {W : Type*} [DecidableEq W] :
    (r : ℕ) → Finset W → (Fin r → Finset W) →
      Finset (Finset (Sym2 W))
  | 0, _U, _B => ∅
  | r + 1, U, B =>
      (U \ B 0).image (starEdgeFinset (B 0)) ∪
        dominationGroups r (U \ B 0) (Fin.tail B)

theorem starEdgeFinset_subset_pairEdges
    {W : Type*} [Fintype W] [DecidableEq W]
    {U B : Finset W} {v : W} (hBU : B ⊆ U) (hv : v ∈ U \ B) :
    starEdgeFinset B v ⊆ pairEdgeFinset U := by
  intro e he
  obtain ⟨x, hxB, rfl⟩ := mem_starEdgeFinset_iff.mp he
  apply (mem_pairEdgeFinset_iff U).2
  refine ⟨?_, ?_⟩
  · simpa [Finset.mk_mem_sym2_iff] using
      And.intro (hBU hxB) (Finset.mem_sdiff.mp hv).1
  · have hxv : x ≠ v := by
      intro hxv
      apply (Finset.mem_sdiff.mp hv).2
      simpa [hxv] using hxB
    simpa using hxv

/-- Every group produced later in the recursion lies completely inside the
current ambient vertex set. -/
theorem dominationGroups_subset_pairEdges
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    ∀ A ∈ dominationGroups r U B, A ⊆ pairEdgeFinset U := by
  induction r generalizing U with
  | zero => simp [dominationGroups]
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      intro A hA
      rw [dominationGroups, Finset.mem_union] at hA
      rcases hA with hA | hA
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
        exact starEdgeFinset_subset_pairEdges hB0U hv
      · apply (ihr htail A hA).trans
        intro e he
        rcases (mem_pairEdgeFinset_iff (U \ B 0)).1 he with ⟨heU, hdiag⟩
        apply (mem_pairEdgeFinset_iff U).2
        exact ⟨Finset.sym2_mono Finset.sdiff_subset heU, hdiag⟩

theorem disjoint_starEdgeFinset
    {W : Type*} [DecidableEq W] {B R : Finset W} {v w : W}
    (hv : v ∈ R) (hw : w ∈ R) (hRB : Disjoint R B) (hvw : v ≠ w) :
    Disjoint (starEdgeFinset B v) (starEdgeFinset B w) := by
  rw [Finset.disjoint_left]
  intro e hev hew
  obtain ⟨x, hxB, rfl⟩ := mem_starEdgeFinset_iff.mp hev
  obtain ⟨y, hyB, hxy⟩ := mem_starEdgeFinset_iff.mp hew
  rcases Sym2.eq_iff.mp hxy with h | h
  · exact hvw h.2.symm
  · have hwB : w ∈ B := by simpa [h.2] using hxB
    exact (Finset.disjoint_left.mp hRB) hw hwB

theorem disjoint_starEdgeFinset_pairEdges
    {W : Type*} [Fintype W] [DecidableEq W]
    {U B : Finset W} {v : W} (hv : v ∈ U \ B) :
    Disjoint (starEdgeFinset B v) (pairEdgeFinset (U \ B)) := by
  rw [Finset.disjoint_left]
  intro e heStar hePair
  obtain ⟨x, hxB, rfl⟩ := mem_starEdgeFinset_iff.mp heStar
  have heSym := (mem_pairEdgeFinset_iff (U \ B)).1 hePair |>.1
  have hxDiff : x ∈ U \ B := by
    have hxmem : x ∈ s(x, v).toFinset := by
      simp [Sym2.toFinset_mk_eq]
    exact (Finset.mem_sym2_iff.mp heSym) x (Sym2.mem_toFinset.mp hxmem)
  exact (Finset.mem_sdiff.mp hxDiff).2 hxB

theorem dominationGroups_each_card
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    ∀ A ∈ dominationGroups r U B, A.card = k := by
  induction r generalizing U with
  | zero => simp [dominationGroups]
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      intro A hA
      rw [dominationGroups, Finset.mem_union] at hA
      rcases hA with hA | hA
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
        simpa [card_starEdgeFinset] using hB0card
      · exact ihr htail A hA

theorem dominationGroups_have_zero
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    ∀ A ∈ dominationGroups r U B, ∃ e ∈ A, f e = 0 := by
  induction r generalizing U with
  | zero => simp [dominationGroups]
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      intro A hA
      rw [dominationGroups, Finset.mem_union] at hA
      rcases hA with hA | hA
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨x, hx, hz⟩ := hdom v hv
        exact ⟨s(x, v), mem_starEdgeFinset_iff.mpr ⟨x, hx, rfl⟩, hz⟩
      · exact ihr htail A hA

theorem dominationGroups_pairwiseDisjoint
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    ((↑(dominationGroups r U B) : Set (Finset (Sym2 W))).PairwiseDisjoint id) := by
  induction r generalizing U with
  | zero => simp [dominationGroups, Set.PairwiseDisjoint]
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      let R := U \ B 0
      let head := R.image (starEdgeFinset (B 0))
      let tail := dominationGroups r R (Fin.tail B)
      have hRdisj : Disjoint R (B 0) := by
        exact Finset.sdiff_disjoint
      have hhead : ((↑head : Set (Finset (Sym2 W))).PairwiseDisjoint id) := by
        intro A hA C hC hAC
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hC
        apply disjoint_starEdgeFinset hv hw hRdisj
        intro hvw
        subst w
        exact hAC rfl
      have htailpw : ((↑tail : Set (Finset (Sym2 W))).PairwiseDisjoint id) :=
        ihr htail
      have hcross : ∀ ⦃A⦄, A ∈ (↑head : Set (Finset (Sym2 W))) →
          ∀ ⦃C⦄, C ∈ (↑tail : Set (Finset (Sym2 W))) →
          A ≠ C → Disjoint (id A) (id C) := by
        intro A hA C hC _hne
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
        exact (disjoint_starEdgeFinset_pairEdges hv).mono
          (Subset.rfl) (dominationGroups_subset_pairEdges htail C hC)
      have hunion := hhead.union htailpw hcross
      simpa only [dominationGroups, R, head, tail, Finset.coe_union] using hunion

/-- With `h` vertices still available after all requested removals, every
round contributes at least `h` pairwise-disjoint domination groups. -/
theorem dominationGroups_card_lower
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r h : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hk : 0 < k) (hcert : IsBlockCertificate d f k r U B)
    (hroom : r * k + h ≤ U.card) :
    r * h ≤ (dominationGroups r U B).card := by
  induction r generalizing U with
  | zero => simp [dominationGroups]
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      let R := U \ B 0
      let head := R.image (starEdgeFinset (B 0))
      let tail := dominationGroups r R (Fin.tail B)
      have hB0ne : (B 0).Nonempty := by
        apply Finset.card_pos.mp
        simpa only [hB0card] using hk
      have hRdisj : Disjoint R (B 0) := Finset.sdiff_disjoint
      have hheadcard : head.card = R.card := by
        exact Finset.card_image_iff.mpr (starEdgeFinset_injOn hB0ne hRdisj)
      have hheadtail : Disjoint head tail := by
        rw [Finset.disjoint_left]
        intro A hAhead hAtail
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hAhead
        have hsubset := dominationGroups_subset_pairEdges htail
          (starEdgeFinset (B 0) v) hAtail
        obtain ⟨e, he⟩ : (starEdgeFinset (B 0) v).Nonempty := by
          apply Finset.card_pos.mp
          simpa only [card_starEdgeFinset, hB0card] using hk
        exact (Finset.disjoint_left.mp (disjoint_starEdgeFinset_pairEdges hv))
          he (hsubset he)
      have hRcard : R.card = U.card - k := by
        simp [R, Finset.card_sdiff_of_subset hB0U, hB0card]
      have htailroom : r * k + h ≤ R.card := by
        rw [hRcard]
        rw [Nat.succ_mul] at hroom
        omega
      have htailbound : r * h ≤ tail.card := ihr htail htailroom
      have hhR : h ≤ R.card := by omega
      rw [dominationGroups, Finset.card_union_of_disjoint hheadtail,
        hheadcard]
      rw [Nat.succ_mul]
      simpa only [Nat.add_comm] using Nat.add_le_add htailbound hhR

/-- Colorings realizing one fixed recursive domination certificate. -/
noncomputable def certificateColorings
    {W : Type*} [Fintype W] [DecidableEq W]
    (d k r : ℕ) (U : Finset W) (B : Fin r → Finset W) :
    Finset (Sym2 W → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦ IsBlockCertificate d f k r U B

/-- Count for one fixed domination-block sequence. -/
theorem card_certificateColorings_le
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r h : ℕ} {U : Finset W} {B : Fin r → Finset W}
    (hk : 0 < k) (hroom : r * k + h ≤ U.card) :
    #(certificateColorings d k r U B) ≤
      ((d + 1) ^ k - d ^ k) ^ (r * h) *
        (d + 1) ^ (Fintype.card (Sym2 W) - (r * h) * k) := by
  classical
  by_cases hne : (certificateColorings d k r U B).Nonempty
  · obtain ⟨f₀, hf₀⟩ := hne
    have hcert₀ : IsBlockCertificate d f₀ k r U B := by
      simpa [certificateColorings] using hf₀
    let groups := dominationGroups r U B
    have hgroupCount : r * h ≤ groups.card :=
      dominationGroups_card_lower hk hcert₀ hroom
    obtain ⟨T, hTgroups, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := groups) (n := r * h) hgroupCount
    let J := {A // A ∈ T}
    let coords : J → Finset (Sym2 W) := fun A ↦ A.1
    have hcoordsCard : ∀ A : J, (coords A).card = k := by
      intro A
      exact dominationGroups_each_card hcert₀ A.1 (hTgroups A.2)
    have hcoordsDisj :
        ((Finset.univ : Finset J) : Set J).PairwiseDisjoint coords := by
      intro A _hA C _hC hAC
      have hdisj := dominationGroups_pairwiseDisjoint hcert₀
        (hTgroups A.2) (hTgroups C.2)
      apply hdisj
      intro hEq
      apply hAC
      exact Subtype.ext hEq
    let F := {f : Sym2 W → Fin (d + 1) //
      IsBlockCertificate d f k r U B}
    let Q := {f : Sym2 W → Fin (d + 1) //
      ∀ A : J, ∃ e ∈ coords A, f e = 0}
    let φ : F → Q := fun f ↦ ⟨f.1, fun A ↦ by
      have hcert : IsBlockCertificate d f.1 k r U B := f.2
      exact dominationGroups_have_zero hcert A.1 (hTgroups A.2)⟩
    have hφ : Function.Injective φ := by
      intro f g hfg
      apply Subtype.ext
      simpa [φ] using congrArg (fun q : Q ↦ q.1) hfg
    have hFleQ : Fintype.card F ≤ Fintype.card Q :=
      Fintype.card_le_of_injective φ hφ
    have hcertCard : #(certificateColorings d k r U B) = Fintype.card F := by
      calc
        #(certificateColorings d k r U B) =
            #((Finset.univ : Finset (Sym2 W → Fin (d + 1))).subtype
              (fun f ↦ IsBlockCertificate d f k r U B)) := by
          rw [Finset.card_subtype]
          rfl
        _ = #(Finset.univ : Finset F) := by
          congr 1
          ext f
          simp [F]
        _ = Fintype.card F := Finset.card_univ
    have hQbound : Fintype.card Q ≤
        ((d + 1) ^ k - d ^ k) ^ Fintype.card J *
          (d + 1) ^ (Fintype.card (Sym2 W) - Fintype.card J * k) := by
      simpa only [Q] using
        card_group_constrained_le d k coords hcoordsCard hcoordsDisj
    rw [hcertCard]
    refine hFleQ.trans (hQbound.trans_eq ?_)
    have hJcard : Fintype.card J = r * h := by
      simpa [J] using hTcard
    simp only [hJcard]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- All exact `k`-block sequences drawn from an ambient finite set. -/
noncomputable def blockSequences
    {W : Type*} [Fintype W] [DecidableEq W]
    (U : Finset W) (k r : ℕ) : Finset (Fin r → Finset W) := by
  classical
  exact Fintype.piFinset fun _ ↦ U.powersetCard k

theorem card_blockSequences
    {W : Type*} [Fintype W] [DecidableEq W]
    (U : Finset W) (k r : ℕ) :
    #(blockSequences U k r) = (Nat.choose U.card k) ^ r := by
  classical
  rw [blockSequences, Fintype.card_piFinset]
  simp [Finset.card_powersetCard]

theorem blockCertificate_block_spec
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    ∀ i, B i ⊆ U ∧ (B i).card = k := by
  induction r generalizing U with
  | zero => intro i; exact Fin.elim0 i
  | succ r ihr =>
      rcases hcert with ⟨hB0U, hB0card, hdom, htail⟩
      intro i
      refine Fin.cases ⟨hB0U, hB0card⟩ (fun j ↦ ?_) i
      have hj := ihr htail j
      exact ⟨hj.1.trans Finset.sdiff_subset, hj.2⟩

theorem blockCertificate_mem_blockSequences
    {W : Type*} [Fintype W] [DecidableEq W]
    {d k r : ℕ} {f : Sym2 W → Fin (d + 1)}
    {U : Finset W} {B : Fin r → Finset W}
    (hcert : IsBlockCertificate d f k r U B) :
    B ∈ blockSequences U k r := by
  classical
  rw [blockSequences, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_powersetCard.mpr (blockCertificate_block_spec hcert i)

/-- Colorings for which some `s`-vertex induced graph has independence
number below `k`. -/
noncomputable def cubicLocalBadColorings (n d s k : ℕ) :
    Finset (Sym2 (Fin n) → Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun f ↦
    ∃ S : Finset (Fin n), S.card = s ∧
      ((coloredGraph d f).induce (↑S : Set (Fin n))).indepNum < k

/-- Greedy-certificate union bound for all locally bad `s`-sets. -/
theorem card_cubicLocalBadColorings_le
    (n d s k r h : ℕ) (hk : 0 < k) (hroom : r * k + h ≤ s) :
    #(cubicLocalBadColorings n d s k) ≤
      Nat.choose n s * (Nat.choose s k) ^ r *
        (((d + 1) ^ k - d ^ k) ^ (r * h) *
          (d + 1) ^
            (Fintype.card (Sym2 (Fin n)) - (r * h) * k)) := by
  classical
  let vertexSets := (Finset.univ : Finset (Fin n)).powersetCard s
  let sequences : Finset (Fin n) → Finset (Fin r → Finset (Fin n)) :=
    fun S ↦ blockSequences S k r
  let fixed : Finset (Fin n) → (Fin r → Finset (Fin n)) →
      Finset (Sym2 (Fin n) → Fin (d + 1)) :=
    fun S B ↦ certificateColorings d k r S B
  have hsubset : cubicLocalBadColorings n d s k ⊆
      vertexSets.biUnion fun S ↦ (sequences S).biUnion (fixed S) := by
    intro f hf
    obtain ⟨S, hScard, hind⟩ :
        ∃ S : Finset (Fin n), S.card = s ∧
          ((coloredGraph d f).induce (↑S : Set (Fin n))).indepNum < k := by
      simpa [cubicLocalBadColorings] using hf
    have hroom' : r * k ≤ S.card := by omega
    obtain ⟨B, hcert⟩ :=
      exists_blockCertificate_of_indepNum_lt f S hind hroom'
    apply Finset.mem_biUnion.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, hScard⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨B, blockCertificate_mem_blockSequences hcert, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcert⟩
  let certBound := ((d + 1) ^ k - d ^ k) ^ (r * h) *
    (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - (r * h) * k)
  calc
    #(cubicLocalBadColorings n d s k) ≤
        #(vertexSets.biUnion fun S ↦ (sequences S).biUnion (fixed S)) :=
      Finset.card_le_card hsubset
    _ ≤ ∑ S ∈ vertexSets, #((sequences S).biUnion (fixed S)) :=
      Finset.card_biUnion_le
    _ ≤ ∑ S ∈ vertexSets, ∑ B ∈ sequences S, #(fixed S B) := by
      exact Finset.sum_le_sum fun S _hS ↦ Finset.card_biUnion_le
    _ ≤ ∑ S ∈ vertexSets, ∑ _B ∈ sequences S, certBound := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro B _hB
      have hScard := (Finset.mem_powersetCard.mp hS).2
      change #(certificateColorings d k r S B) ≤ certBound
      apply card_certificateColorings_le hk
      simpa only [hScard] using hroom
    _ = ∑ S ∈ vertexSets, (Nat.choose s k) ^ r * certBound := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_const, card_blockSequences]
      have hScard := (Finset.mem_powersetCard.mp hS).2
      simp [hScard, nsmul_eq_mul]
    _ = Nat.choose n s * (Nat.choose s k) ^ r * certBound := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_assoc, mul_comm, mul_left_comm]

/-- Avoiding the cubic local bad event gives the required local
independence property. -/
theorem hasLocalIndependence_of_not_mem_cubicLocalBadColorings
    {n d s k : ℕ} {f : Sym2 (Fin n) → Fin (d + 1)}
    (hbad : f ∉ cubicLocalBadColorings n d s k) :
    HasLocalIndependence (coloredGraph d f) s k := by
  classical
  intro S hScard
  have hnot : ¬
      ((coloredGraph d f).induce (↑S : Set (Fin n))).indepNum < k := by
    intro hind
    apply hbad
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, hScard, hind⟩
  have hle : k ≤
      ((coloredGraph d f).induce (↑S : Set (Fin n))).indepNum :=
    Nat.le_of_not_gt hnot
  let H := (coloredGraph d f).induce (↑S : Set (Fin n))
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq
    (s := I) (n := k) (by simpa [H, hI.card_eq] using hle)
  have hJ : H.IsNIndepSet k J := by
    refine ⟨hI.isIndepSet.mono ?_, hJcard⟩
    exact_mod_cast hJI
  let j : {x // x ∈ (↑S : Set (Fin n))} ↪ Fin n :=
    ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨J.map j, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  · have hJ' : ((coloredGraph d f).induce (↑S : Set (Fin n))).IsNIndepSet k J := by
      simpa only [H] using hJ
    rw [SimpleGraph.induce_eq_coe_induce_top] at hJ'
    simpa only [j] using
      (SimpleGraph.isNIndepSet_induce (G := coloredGraph d f)
        (F := (↑S : Set (Fin n))) (s := J) (n := k)).mp hJ'

/-- Finite first-moment certificate for the refined cubic-window
construction. -/
theorem exists_cubic_coloring_witness
    {n d s k r h q : ℕ} (hk : 0 < k) (hroom : r * k + h ≤ s)
    (hcount :
      Nat.choose n s * (Nat.choose s k) ^ r *
          (((d + 1) ^ k - d ^ k) ^ (r * h) *
            (d + 1) ^
              (Fintype.card (Sym2 (Fin n)) - (r * h) * k)) +
        Nat.choose n q * d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) <
        (d + 1) ^ Fintype.card (Sym2 (Fin n))) :
    ∃ G : SimpleGraph (Fin n),
      HasLocalIndependence G s k ∧ G.indepNum < q := by
  classical
  let localBad := cubicLocalBadColorings n d s k
  let globalBad := globalBadColorings n d q
  let all : Finset (Sym2 (Fin n) → Fin (d + 1)) := Finset.univ
  have hbadCard : #(localBad ∪ globalBad) < #all := by
    have hlocal := card_cubicLocalBadColorings_le n d s k r h hk hroom
    have hglobal := card_globalBadColorings_le n d q
    have hunion : #(localBad ∪ globalBad) ≤ #localBad + #globalBad :=
      Finset.card_union_le localBad globalBad
    have htotal : #all = (d + 1) ^ Fintype.card (Sym2 (Fin n)) := by
      simp [all]
    rw [htotal]
    exact lt_of_le_of_lt (hunion.trans (Nat.add_le_add hlocal hglobal)) hcount
  obtain ⟨f, _hfall, hfbad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadCard
  have hflocal : f ∉ localBad := by
    intro hf
    exact hfbad (Finset.mem_union_left globalBad hf)
  have hfglobal : f ∉ globalBad := by
    intro hf
    exact hfbad (Finset.mem_union_right localBad hf)
  refine ⟨coloredGraph d f, ?_, ?_⟩
  · exact hasLocalIndependence_of_not_mem_cubicLocalBadColorings hflocal
  · have hnot : ¬ q ≤ (coloredGraph d f).indepNum := by
      intro hq
      apply hfglobal
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    exact Nat.lt_of_not_ge hnot

theorem cubic_upper_bound_finite
    {n d s k r h q : ℕ} (hk : 0 < k) (hroom : r * k + h ≤ s)
    (hcount :
      Nat.choose n s * (Nat.choose s k) ^ r *
          (((d + 1) ^ k - d ^ k) ^ (r * h) *
            (d + 1) ^
              (Fintype.card (Sym2 (Fin n)) - (r * h) * k)) +
        Nat.choose n q * d ^ Nat.choose q 2 *
          (d + 1) ^ (Fintype.card (Sym2 (Fin n)) - Nat.choose q 2) <
        (d + 1) ^ Fintype.card (Sym2 (Fin n))) :
    localIndependenceNumber n s k < q := by
  obtain ⟨G, hlocal, hglobal⟩ :=
    exists_cubic_coloring_witness hk hroom hcount
  exact lt_of_le_of_lt (localIndependenceNumber_le_of_witness hlocal) hglobal

/-- A reusable normalization lemma for the two first-moment terms. -/
theorem two_normalized_counts_lt_total
    {b E a₁ a₂ C₁ C₂ : ℕ} (hb : 0 < b)
    (ha₁ : a₁ ≤ E) (ha₂ : a₂ ≤ E)
    (h₁ : 4 * C₁ ≤ b ^ a₁) (h₂ : 4 * C₂ ≤ b ^ a₂) :
    C₁ * b ^ (E - a₁) + C₂ * b ^ (E - a₂) < b ^ E := by
  have hpow₁ : b ^ E = b ^ a₁ * b ^ (E - a₁) := by
    conv_lhs => rw [← Nat.add_sub_of_le ha₁, pow_add]
  have hpow₂ : b ^ E = b ^ a₂ * b ^ (E - a₂) := by
    conv_lhs => rw [← Nat.add_sub_of_le ha₂, pow_add]
  have hterm₁ : 4 * (C₁ * b ^ (E - a₁)) ≤ b ^ E := by
    rw [hpow₁]
    nlinarith [Nat.mul_le_mul_right (b ^ (E - a₁)) h₁]
  have hterm₂ : 4 * (C₂ * b ^ (E - a₂)) ≤ b ^ E := by
    rw [hpow₂]
    nlinarith [Nat.mul_le_mul_right (b ^ (E - a₂)) h₂]
  have htotal : 0 < b ^ E := pow_pos hb E
  omega

/-- Convenient normalized form of the square finite upper bound. -/
theorem square_upper_bound_of_normalized_counts
    {n d s t q r : ℕ}
    (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (hr : 4 * t * r ≤ s * s)
    (hrE : r ≤ Fintype.card (Sym2 (Fin n)))
    (hqE : Nat.choose q 2 ≤ Fintype.card (Sym2 (Fin n)))
    (hlocal :
      4 * (Nat.choose n s * Nat.choose (Nat.choose s 2) r) ≤
        (d + 1) ^ r)
    (hglobal :
      4 * (Nat.choose n q * d ^ Nat.choose q 2) ≤
        (d + 1) ^ Nat.choose q 2) :
    localIndependenceNumber n s t < q := by
  apply square_upper_bound_finite (d := d) ht hst hr
  exact two_normalized_counts_lt_total (by positivity) hrE hqE hlocal hglobal

/-- Convenient normalized form of the refined cubic finite upper bound. -/
theorem cubic_upper_bound_of_normalized_counts
    {n d s k r h q : ℕ} (hk : 0 < k) (hroom : r * k + h ≤ s)
    (hlocalE : (r * h) * k ≤ Fintype.card (Sym2 (Fin n)))
    (hglobalE : Nat.choose q 2 ≤ Fintype.card (Sym2 (Fin n)))
    (hlocal :
      4 * (Nat.choose n s * (Nat.choose s k) ^ r *
        ((d + 1) ^ k - d ^ k) ^ (r * h)) ≤
        (d + 1) ^ ((r * h) * k))
    (hglobal :
      4 * (Nat.choose n q * d ^ Nat.choose q 2) ≤
        (d + 1) ^ Nat.choose q 2) :
    localIndependenceNumber n s k < q := by
  apply cubic_upper_bound_finite (d := d) hk hroom
  simpa [mul_assoc] using
    two_normalized_counts_lt_total (b := d + 1) (by positivity)
      hlocalE hglobalE hlocal hglobal

/-! ## Elementary exponential estimates used in the specializations -/

/-- A deliberately coarse form of Stirling's lower bound. -/
lemma pow_le_three_pow_mul_factorial (r : ℕ) :
    r ^ r ≤ 3 ^ r * r.factorial := by
  apply_mod_cast
    (show (r : ℝ) ^ r ≤ 3 ^ r * (r.factorial : ℝ) from ?_)
  by_cases hr : r = 0
  · subst r
    norm_num
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast Nat.pos_of_ne_zero hr
  have hrone : (1 : ℝ) ≤ r := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
  have hsqrt : 1 ≤ √(2 * Real.pi * (r : ℝ)) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hst := Stirling.le_factorial_stirling r
  have hfac : ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
    calc
      _ ≤ √(2 * Real.pi * (r : ℝ)) *
          ((r : ℝ) / Real.exp 1) ^ r :=
        le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ _ := hst
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  calc
    (r : ℝ) ^ r =
        (Real.exp 1) ^ r * ((r : ℝ) / Real.exp 1) ^ r := by
      rw [div_pow]
      field_simp [Real.exp_ne_zero]
    _ ≤ 3 ^ r * (r.factorial : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hexp r) hfac
        (by positivity) (by positivity)

lemma choose_mul_self_pow_le (S r : ℕ) :
    Nat.choose S r * r ^ r ≤ (3 * S) ^ r := by
  have hdesc : r.factorial * Nat.choose S r ≤ S ^ r := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow S r
  calc
    Nat.choose S r * r ^ r
        ≤ Nat.choose S r * (3 ^ r * r.factorial) :=
      Nat.mul_le_mul_left _ (pow_le_three_pow_mul_factorial r)
    _ = 3 ^ r * (r.factorial * Nat.choose S r) := by ac_rfl
    _ ≤ 3 ^ r * S ^ r := Nat.mul_le_mul_left _ hdesc
    _ = (3 * S) ^ r := by rw [mul_pow]

lemma choose_gain {b S r : ℕ} (hr : 0 < r)
    (hbase : 3 * 2 ^ 64 * S ≤ b * r) :
    2 ^ (64 * r) * Nat.choose S r ≤ b ^ r := by
  have hp := Nat.pow_le_pow_left hbase r
  have hchoose := choose_mul_self_pow_le S r
  have hmul :
      (2 ^ (64 * r) * Nat.choose S r) * r ^ r ≤ b ^ r * r ^ r := by
    calc
      (2 ^ (64 * r) * Nat.choose S r) * r ^ r
          = 2 ^ (64 * r) * (Nat.choose S r * r ^ r) := by ac_rfl
      _ ≤ 2 ^ (64 * r) * (3 * S) ^ r :=
        Nat.mul_le_mul_left _ hchoose
      _ = (3 * 2 ^ 64 * S) ^ r := by
        rw [pow_mul, ← mul_pow]
        congr 1
        ring
      _ ≤ (b * r) ^ r := hp
      _ = b ^ r * r ^ r := by rw [mul_pow]
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos hr r)

lemma local_square_normalized {n s r b ell : ℕ} (hr : 0 < r)
    (hn : n < 2 ^ ell) (hexp : ell * s + 2 ≤ 64 * r)
    (hbase : 3 * 2 ^ 64 * Nat.choose s 2 ≤ b * r) :
    4 * (Nat.choose n s * Nat.choose (Nat.choose s 2) r) ≤ b ^ r := by
  have hnchoose : Nat.choose n s ≤ 2 ^ (ell * s) := by
    calc
      Nat.choose n s ≤ n ^ s := Nat.choose_le_pow n s
      _ ≤ (2 ^ ell) ^ s := Nat.pow_le_pow_left hn.le s
      _ = 2 ^ (ell * s) := by rw [pow_mul]
  have hcoeff : 4 * Nat.choose n s ≤ 2 ^ (64 * r) := by
    calc
      4 * Nat.choose n s ≤ 4 * 2 ^ (ell * s) :=
        Nat.mul_le_mul_left _ hnchoose
      _ = 2 ^ (ell * s + 2) := by simp [pow_add]; ac_rfl
      _ ≤ 2 ^ (64 * r) := pow_le_pow_right₀ (by omega) hexp
  calc
    4 * (Nat.choose n s * Nat.choose (Nat.choose s 2) r)
        = (4 * Nat.choose n s) * Nat.choose (Nat.choose s 2) r := by
          ac_rfl
    _ ≤ 2 ^ (64 * r) * Nat.choose (Nat.choose s 2) r :=
      Nat.mul_le_mul_right _ hcoeff
    _ ≤ b ^ r := choose_gain hr hbase

lemma two_mul_pow_le_succ_pow (d : ℕ) (hd : 0 < d) :
    2 * d ^ d ≤ (d + 1) ^ d := by
  have h := pow_add_mul_le_add_pow (R := ℕ) (a := d) (b := 1)
    (by omega) (by omega) d
  have heq : d * d ^ (d - 1) = d ^ d := by
    calc
      d * d ^ (d - 1) = d ^ (d - 1) * d := by ac_rfl
      _ = d ^ ((d - 1) + 1) := by rw [pow_succ]
      _ = d ^ d := by rw [Nat.sub_add_cancel (show 1 ≤ d by omega)]
  simpa [heq, two_mul] using h

lemma pow_gain_blocks {d A Q : ℕ} (hd : 0 < d) (hAQ : d * A ≤ Q) :
    2 ^ A * d ^ Q ≤ (d + 1) ^ Q := by
  have hblock := Nat.pow_le_pow_left (two_mul_pow_le_succ_pow d hd) A
  have hblock' : 2 ^ A * d ^ (d * A) ≤ (d + 1) ^ (d * A) := by
    simpa [mul_pow, pow_mul] using hblock
  calc
    2 ^ A * d ^ Q
        = (2 ^ A * d ^ (d * A)) * d ^ (Q - d * A) := by
      conv_lhs => rw [show Q = d * A + (Q - d * A) by omega, pow_add]
      ac_rfl
    _ ≤ (d + 1) ^ (d * A) * d ^ (Q - d * A) :=
      Nat.mul_le_mul_right _ hblock'
    _ ≤ (d + 1) ^ (d * A) * (d + 1) ^ (Q - d * A) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (d + 1) ^ Q := by
      rw [← pow_add, Nat.add_sub_of_le hAQ]

lemma global_normalized {n q d ell : ℕ} (hd : 0 < d)
    (hn : n < 2 ^ ell)
    (hblocks : d * (q * ell + 2) ≤ Nat.choose q 2) :
    4 * (Nat.choose n q * d ^ Nat.choose q 2) ≤
      (d + 1) ^ Nat.choose q 2 := by
  have hnchoose : Nat.choose n q ≤ 2 ^ (ell * q) := by
    calc
      Nat.choose n q ≤ n ^ q := Nat.choose_le_pow n q
      _ ≤ (2 ^ ell) ^ q := Nat.pow_le_pow_left hn.le q
      _ = 2 ^ (ell * q) := by rw [pow_mul]
  calc
    4 * (Nat.choose n q * d ^ Nat.choose q 2)
        ≤ 4 * (2 ^ (ell * q) * d ^ Nat.choose q 2) := by gcongr
    _ = 2 ^ (q * ell + 2) * d ^ Nat.choose q 2 := by
      simp [pow_add]
      ac_rfl
    _ ≤ (d + 1) ^ Nat.choose q 2 := pow_gain_blocks hd hblocks

lemma succ_pow_le_four_pow_mul_pow {d k c : ℕ} (hd : 0 < d)
    (hkc : k ≤ d * c) :
    (d + 1) ^ k ≤ 4 ^ c * d ^ k := by
  apply_mod_cast
    (show ((d + 1 : ℕ) : ℝ) ^ k ≤ 4 ^ c * (d : ℝ) ^ k from ?_)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : ((d + 1 : ℕ) : ℝ) / d = 1 + (d : ℝ)⁻¹ := by
    norm_num [Nat.cast_add]
    field_simp
  have hunit := Real.one_add_inv_pow_le_exp (n := d)
  have hchunk : (((d + 1 : ℕ) : ℝ) / d) ^ d ≤ 4 := by
    rw [hratio]
    exact hunit.trans (Real.exp_one_lt_three.trans (by norm_num)).le
  have hdc : (((d + 1 : ℕ) : ℝ) / d) ^ (d * c) ≤ 4 ^ c := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hchunk c
  have hratio_one : 1 ≤ (((d + 1 : ℕ) : ℝ) / d) := by
    rw [hratio]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hdR.le)
  have hkdcR :
      (((d + 1 : ℕ) : ℝ) / d) ^ k ≤
        (((d + 1 : ℕ) : ℝ) / d) ^ (d * c) :=
    pow_le_pow_right₀ hratio_one hkc
  have hdiv : (((d + 1 : ℕ) : ℝ) / d) ^ k ≤ 4 ^ c :=
    hkdcR.trans hdc
  rw [div_pow] at hdiv
  calc
    ((d + 1 : ℕ) : ℝ) ^ k
        = ((((d + 1 : ℕ) : ℝ) ^ k / (d : ℝ) ^ k)) * (d : ℝ) ^ k := by
      field_simp
    _ ≤ 4 ^ c * (d : ℝ) ^ k := by gcongr

lemma two_pred_pow_le_pow {A : ℕ} (hA : 2 ≤ A) :
    2 * (A - 1) ^ A ≤ A ^ A := by
  have hpred : 0 < A - 1 := by omega
  have h := two_mul_pow_le_succ_pow (A - 1) hpred
  have he : A - 1 + 1 = A := Nat.sub_add_cancel (by omega)
  have h' : 2 * (A - 1) ^ (A - 1) ≤ A ^ (A - 1) := by
    simpa [he] using h
  calc
    2 * (A - 1) ^ A = 2 * (A - 1) ^ ((A - 1) + 1) := by rw [he]
    _ = (2 * (A - 1) ^ (A - 1)) * (A - 1) := by
      rw [pow_succ]
      ac_rfl
    _ ≤ A ^ (A - 1) * (A - 1) := Nat.mul_le_mul_right _ h'
    _ ≤ A ^ (A - 1) * A := Nat.mul_le_mul_left _ (by omega)
    _ = A ^ ((A - 1) + 1) := by rw [pow_succ]
    _ = A ^ A := by rw [he]

lemma bad_block_gain {b k A : ℕ} (hA : 2 ≤ A)
    (hmissing : b ^ k ≤ A * (b - 1) ^ k) :
    2 * (b ^ k - (b - 1) ^ k) ^ A ≤ (b ^ k) ^ A := by
  let y := b ^ k
  let z := (b - 1) ^ k
  let x := y - z
  have hzy : z ≤ y := Nat.pow_le_pow_left (by omega) k
  have hAx : A * x ≤ (A - 1) * y := by
    calc
      A * x = A * y - A * z := by
        dsimp [x]
        rw [Nat.mul_sub_left_distrib]
      _ ≤ A * y - y := Nat.sub_le_sub_left hmissing _
      _ = (A - 1) * y := by rw [Nat.sub_mul]; simp
  have hp := Nat.pow_le_pow_left hAx A
  have hpred := two_pred_pow_le_pow hA
  have hmul : (2 * x ^ A) * A ^ A ≤ y ^ A * A ^ A := by
    calc
      (2 * x ^ A) * A ^ A = 2 * (A * x) ^ A := by
        simp [mul_pow]
        ac_rfl
      _ ≤ 2 * ((A - 1) * y) ^ A := Nat.mul_le_mul_left _ hp
      _ = (2 * (A - 1) ^ A) * y ^ A := by rw [mul_pow]; ac_rfl
      _ ≤ A ^ A * y ^ A := Nat.mul_le_mul_right _ hpred
      _ = y ^ A * A ^ A := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by omega) A)

lemma repeated_block_gain {x y A B M : ℕ} (hxy : x ≤ y)
    (hblock : 2 * x ^ A ≤ y ^ A) (hAB : A * B ≤ M) :
    2 ^ B * x ^ M ≤ y ^ M := by
  have hp := Nat.pow_le_pow_left hblock B
  have hp' : 2 ^ B * x ^ (A * B) ≤ y ^ (A * B) := by
    simpa [mul_pow, pow_mul] using hp
  calc
    2 ^ B * x ^ M
        = (2 ^ B * x ^ (A * B)) * x ^ (M - A * B) := by
      conv_lhs => rw [show M = A * B + (M - A * B) by omega, pow_add]
      ac_rfl
    _ ≤ y ^ (A * B) * x ^ (M - A * B) :=
      Nat.mul_le_mul_right _ hp'
    _ ≤ y ^ (A * B) * y ^ (M - A * B) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy _)
    _ = y ^ M := by rw [← pow_add, Nat.add_sub_of_le hAB]

lemma local_cubic_normalized {n s k r h b ell u A B : ℕ}
    (hn : n < 2 ^ ell) (hs : s < 2 ^ u)
    (hB : ell * s + u * k * r + 2 ≤ B)
    (hAB : A * B ≤ r * h)
    (hgain : 2 * (b ^ k - (b - 1) ^ k) ^ A ≤ (b ^ k) ^ A) :
    4 * (Nat.choose n s * (Nat.choose s k) ^ r *
        (b ^ k - (b - 1) ^ k) ^ (r * h)) ≤
      b ^ ((r * h) * k) := by
  let x := b ^ k - (b - 1) ^ k
  let y := b ^ k
  have hxy : x ≤ y := Nat.sub_le _ _
  have hnchoose : Nat.choose n s ≤ 2 ^ (ell * s) := by
    calc
      Nat.choose n s ≤ n ^ s := Nat.choose_le_pow n s
      _ ≤ (2 ^ ell) ^ s := Nat.pow_le_pow_left hn.le s
      _ = 2 ^ (ell * s) := by rw [pow_mul]
  have hschoose : (Nat.choose s k) ^ r ≤ 2 ^ (u * k * r) := by
    have hsk : Nat.choose s k ≤ 2 ^ (u * k) := by
      calc
        Nat.choose s k ≤ s ^ k := Nat.choose_le_pow s k
        _ ≤ (2 ^ u) ^ k := Nat.pow_le_pow_left hs.le k
        _ = 2 ^ (u * k) := by rw [pow_mul]
    calc
      (Nat.choose s k) ^ r ≤ (2 ^ (u * k)) ^ r :=
        Nat.pow_le_pow_left hsk r
      _ = 2 ^ (u * k * r) := (pow_mul 2 (u * k) r).symm
  have hcoeff :
      4 * (Nat.choose n s * (Nat.choose s k) ^ r) ≤ 2 ^ B := by
    calc
      4 * (Nat.choose n s * (Nat.choose s k) ^ r)
          ≤ 4 * (2 ^ (ell * s) * 2 ^ (u * k * r)) := by gcongr
      _ = 2 ^ (ell * s + u * k * r + 2) := by
        simp [pow_add]
        ac_rfl
      _ ≤ 2 ^ B := pow_le_pow_right₀ (by omega) hB
  have hrep : 2 ^ B * x ^ (r * h) ≤ y ^ (r * h) :=
    repeated_block_gain hxy hgain hAB
  calc
    4 * (Nat.choose n s * (Nat.choose s k) ^ r * x ^ (r * h))
        = (4 * (Nat.choose n s * (Nat.choose s k) ^ r)) * x ^ (r * h) := by
      ac_rfl
    _ ≤ 2 ^ B * x ^ (r * h) := Nat.mul_le_mul_right _ hcoeff
    _ ≤ y ^ (r * h) := hrep
    _ = b ^ ((r * h) * k) := by simp [y, pow_mul, mul_comm]

/-! ## Binary bookkeeping and rounded specializations -/

/-- One more than the base-two logarithm.  This is the convenient exact
integer majorant used in the counting estimates. -/
def binaryLength (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma n_lt_two_pow_binaryLength (n : ℕ) : n < 2 ^ binaryLength n :=
  Nat.lt_pow_succ_log_self (by omega) n

lemma binaryLength_le_of_lt_two_pow {x a : ℕ} (ha : 0 < a)
    (hx : x < 2 ^ a) : binaryLength x ≤ a := by
  dsimp [binaryLength]
  exact Nat.succ_le_iff.mpr (Nat.log_lt_of_lt_pow' ha.ne' hx)

/-- The number of lower-bound iterations supplied by the binary
double-counting argument. -/
def lowerIterations (n s : ℕ) : ℕ :=
  Nat.log 2 n / (4 * binaryLength s)

/-- The exact integer room estimate behind the lower specialization. -/
lemma lower_room {n s : ℕ} (hn : n ≠ 0)
    (hlarge : 4 * binaryLength s ≤ Nat.log 2 n) :
    s * (2 * s ^ 2) ^ lowerIterations n s ≤ n := by
  let m := Nat.log 2 n
  let u := binaryLength s
  let q := lowerIterations n s
  have hu : 0 < u := by dsimp [u, binaryLength]; omega
  have hs : s < 2 ^ u := n_lt_two_pow_binaryLength s
  have hbase : 2 * s ^ 2 < 2 ^ (2 * u + 1) := by
    have hp := Nat.pow_lt_pow_left hs (by omega : (2 : ℕ) ≠ 0)
    calc
      2 * s ^ 2 < 2 * (2 ^ u) ^ 2 :=
        (Nat.mul_lt_mul_left (by omega)).2 hp
      _ = 2 * 2 ^ (u * 2) :=
        congrArg (fun z : ℕ => 2 * z) (pow_mul 2 u 2).symm
      _ = 2 ^ (u * 2 + 1) := by rw [pow_succ]; ac_rfl
      _ = 2 ^ (2 * u + 1) := by congr 1 <;> omega
  have hq : 4 * u * q ≤ m := by
    dsimp [q, lowerIterations, m, u]
    simpa [mul_comm] using
      Nat.div_mul_le_self (Nat.log 2 n) (4 * binaryLength s)
  have hexp : u + (2 * u + 1) * q ≤ m := by
    have hfour : 4 * (u + (2 * u + 1) * q) ≤ 4 * m := by
      calc
        4 * (u + (2 * u + 1) * q) ≤ 4 * u + 12 * u * q := by
          nlinarith [hu]
        _ ≤ m + 3 * m := by nlinarith [hlarge, hq]
        _ = 4 * m := by ring
    omega
  have hpow : (2 * s ^ 2) ^ q ≤ 2 ^ ((2 * u + 1) * q) := by
    simpa [pow_mul] using Nat.pow_le_pow_left hbase.le q
  have htotal : s * (2 * s ^ 2) ^ q <
      2 ^ (u + (2 * u + 1) * q) := by
    calc
      s * (2 * s ^ 2) ^ q < 2 ^ u * 2 ^ ((2 * u + 1) * q) :=
        Nat.mul_lt_mul_of_lt_of_le hs hpow (by positivity)
      _ = 2 ^ (u + (2 * u + 1) * q) := by rw [pow_add]
  have hpm : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn
  exact htotal.le.trans
    ((Nat.pow_le_pow_right (by omega) hexp).trans hpm)

def squareColorCount (t : ℕ) : ℕ := 3 * 2 ^ 70 * t

def squareDenseCount (n s : ℕ) : ℕ :=
  (binaryLength n * s + 2) ⌈/⌉ 64

def universalUpperTarget (d ell : ℕ) : ℕ :=
  4 * d * (ell + 2) + 2

lemma global_blocks_param (d ell : ℕ) (hd : 0 < d) :
    let q := universalUpperTarget d ell
    d * (q * ell + 2) ≤ Nat.choose q 2 := by
  dsimp [universalUpperTarget]
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by omega)).2
  let q := 4 * d * (ell + 2) + 2
  have hqsub : q - 1 = 4 * d * (ell + 2) + 1 := by dsimp [q]
  have hgap : 2 * d * ell + 1 ≤ q - 1 := by
    rw [hqsub]
    nlinarith [show 1 ≤ d from hd]
  have hfour : 4 * d ≤ q := by dsimp [q]; nlinarith
  calc
    d * (q * ell + 2) * 2 = q * (2 * d * ell) + 4 * d := by ring
    _ ≤ q * (2 * d * ell) + q := add_le_add_right hfour _
    _ = q * (2 * d * ell + 1) := by ring
    _ ≤ q * (q - 1) := Nat.mul_le_mul_left q hgap

lemma le_card_sym2_of_le {a n : ℕ} (hn : 1 ≤ n) (han : a ≤ n) :
    a ≤ Fintype.card (Sym2 (Fin n)) := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  apply han.trans
  apply (Nat.le_div_iff_mul_le (by omega)).2
  rw [show n + 1 - 1 = n by omega]
  calc
    n * 2 ≤ n * (n + 1) := Nat.mul_le_mul_left n (by omega)
    _ = (n + 1) * n := by ac_rfl

lemma choose_two_le_card_sym2 {q n : ℕ} (hqn : q ≤ n) :
    Nat.choose q 2 ≤ Fintype.card (Sym2 (Fin n)) := by
  rw [Sym2.card, Fintype.card_fin]
  exact Nat.choose_mono 2 (hqn.trans (Nat.le_succ n))

/-- A completely explicit square-window upper bound, separated from the
elementary eventual inequalities used to specialize it. -/
lemma square_upper_parameter_bound {n s t : ℕ}
    (hn : 1 ≤ n) (ht : 2 ≤ t) (hst : 2 * (t - 1) ≤ s)
    (hs : s ≤ t * binaryLength n)
    (hrT : 4 * t * squareDenseCount n s ≤ s * s)
    (hrn : squareDenseCount n s ≤ n)
    (hqn : universalUpperTarget (squareColorCount t) (binaryLength n) ≤ n) :
    localIndependenceNumber n s t <
      universalUpperTarget (squareColorCount t) (binaryLength n) := by
  let ell := binaryLength n
  let d := squareColorCount t
  let r := squareDenseCount n s
  let q := universalUpperTarget d ell
  have hd : 0 < d := by
    dsimp [d, squareColorCount]
    exact mul_pos (by norm_num) (by omega)
  have hr : 0 < r := by
    have hle : binaryLength n * s + 2 ≤
        64 * ((binaryLength n * s + 2) ⌈/⌉ 64) :=
      le_smul_ceilDiv (by omega : (0 : ℕ) < 64)
    dsimp [r, squareDenseCount]
    omega
  have hnexp : n < 2 ^ ell := n_lt_two_pow_binaryLength n
  have hexp : ell * s + 2 ≤ 64 * r :=
    le_smul_ceilDiv (by omega : (0 : ℕ) < 64)
  have hbase : 3 * 2 ^ 64 * Nat.choose s 2 ≤ (d + 1) * r := by
    have hc : Nat.choose s 2 ≤ s ^ 2 := Nat.choose_le_pow s 2
    have hrbase : ell * s ≤ 64 * r := by omega
    calc
      3 * 2 ^ 64 * Nat.choose s 2 ≤ 3 * 2 ^ 64 * s ^ 2 := by gcongr
      _ ≤ 3 * 2 ^ 64 * ((t * ell) * s) := by
        gcongr
        simpa [pow_two] using Nat.mul_le_mul_right s hs
      _ ≤ (3 * 2 ^ 70 * t) * r := by
        calc
          3 * 2 ^ 64 * ((t * ell) * s)
              = 3 * 2 ^ 64 * t * (ell * s) := by ring
          _ ≤ 3 * 2 ^ 64 * t * (64 * r) := by gcongr
          _ = (3 * 2 ^ 70 * t) * r := by norm_num; ring
      _ ≤ (d + 1) * r := by
        dsimp [d, squareColorCount]
        exact Nat.mul_le_mul_right r (Nat.le_succ _)
  apply square_upper_bound_of_normalized_counts (d := d) ht hst hrT
  · exact le_card_sym2_of_le hn hrn
  · exact choose_two_le_card_sym2 (by simpa [q, d, ell] using hqn)
  · exact local_square_normalized hr hnexp hexp hbase
  · exact global_normalized hd hnexp (global_blocks_param d ell hd)

def cubicChunk (n : ℕ) : ℕ := binaryLength (binaryLength n) / 64

def cubicColorCount (n t : ℕ) : ℕ := t ⌈/⌉ cubicChunk n

def cubicBlockCount (s t : ℕ) : ℕ := s / (2 * t)

def cubicRemainder (s t : ℕ) : ℕ := s - cubicBlockCount s t * t

def cubicLocalExponent (n s t : ℕ) : ℕ :=
  4 ^ cubicChunk n *
    (binaryLength n * s + binaryLength s * t * cubicBlockCount s t + 2)

/-- Explicit refined upper bound.  Its only remaining hypotheses are plain
integer size inequalities; no graph- or probability-theoretic fact is hidden
in them. -/
lemma cubic_upper_parameter_bound {n s t : ℕ}
    (hn : 1 ≤ n) (ht : 0 < t) (hc : 0 < cubicChunk n)
    (hlocal : cubicLocalExponent n s t ≤
      cubicBlockCount s t * cubicRemainder s t)
    (hlocalE :
      (cubicBlockCount s t * cubicRemainder s t) * t ≤ n)
    (hqn : universalUpperTarget (cubicColorCount n t) (binaryLength n) ≤ n) :
    localIndependenceNumber n s t <
      universalUpperTarget (cubicColorCount n t) (binaryLength n) := by
  let ell := binaryLength n
  let u := binaryLength s
  let c := cubicChunk n
  let d := cubicColorCount n t
  let r := cubicBlockCount s t
  let h := cubicRemainder s t
  let A := 4 ^ c
  let B := ell * s + u * t * r + 2
  let q := universalUpperTarget d ell
  have hd : 0 < d := by
    have hceil : t ≤ c * (t ⌈/⌉ c) := le_smul_ceilDiv hc
    dsimp [d, cubicColorCount, c] at hceil ⊢
    by_contra hd0
    have : t ⌈/⌉ cubicChunk n = 0 := Nat.eq_zero_of_not_pos hd0
    rw [this] at hceil
    simp at hceil
    omega
  have htc : t ≤ d * c := by
    have hceil : t ≤ c * (t ⌈/⌉ c) := le_smul_ceilDiv hc
    dsimp [d, cubicColorCount, c] at hceil ⊢
    simpa [mul_comm] using hceil
  have hroom : r * t + h ≤ s := by
    have hrt : cubicBlockCount s t * t ≤ s := by
      calc
        cubicBlockCount s t * t ≤ cubicBlockCount s t * (2 * t) := by
          exact Nat.mul_le_mul_left _ (by omega)
        _ ≤ s := by
          dsimp [cubicBlockCount]
          simpa [mul_comm] using Nat.div_mul_le_self s (2 * t)
    dsimp [r, h, cubicRemainder]
    omega
  have hnexp : n < 2 ^ ell := n_lt_two_pow_binaryLength n
  have hsexp : s < 2 ^ u := n_lt_two_pow_binaryLength s
  have hmissing : (d + 1) ^ t ≤ A * d ^ t := by
    simpa [A] using succ_pow_le_four_pow_mul_pow hd htc
  have hgain :
      2 * ((d + 1) ^ t - d ^ t) ^ A ≤ ((d + 1) ^ t) ^ A := by
    apply bad_block_gain
    · dsimp [A]
      have hp : 4 ^ 1 ≤ 4 ^ c := pow_le_pow_right₀ (by omega) hc
      norm_num at hp ⊢
      omega
    · simpa using hmissing
  have hnormalized :
      4 * (Nat.choose n s * (Nat.choose s t) ^ r *
          ((d + 1) ^ t - d ^ t) ^ (r * h)) ≤
        (d + 1) ^ ((r * h) * t) := by
    apply local_cubic_normalized hnexp hsexp (B := B) (A := A)
    · exact le_rfl
    · simpa [A, B, ell, u, r, h, cubicLocalExponent] using hlocal
    · simpa using hgain
  apply cubic_upper_bound_of_normalized_counts (d := d) ht hroom
  · exact le_card_sym2_of_le hn (by simpa [r, h] using hlocalE)
  · exact choose_two_le_card_sym2 (by simpa [q, d, ell] using hqn)
  · simpa [mul_assoc] using hnormalized
  · exact global_normalized hd hnexp (global_blocks_param d ell hd)

/-! ## Comparison with natural logarithms -/

lemma log_le_binaryLength {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ (binaryLength n : ℝ) := by
  have hpow := n_lt_two_pow_binaryLength n
  have hcast : (n : ℝ) < ((2 ^ binaryLength n : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_lt_log hnpos hcast
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  calc
    Real.log (n : ℝ) ≤ (binaryLength n : ℝ) * Real.log 2 := hlog.le
    _ ≤ (binaryLength n : ℝ) * 1 := by gcongr
    _ = _ := by ring

lemma binaryLength_le_two_log_add_one {n : ℕ} (hn : 1 ≤ n) :
    (binaryLength n : ℝ) ≤ 2 * Real.log (n : ℝ) + 1 := by
  let m := Nat.log 2 n
  have hp : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hpR : (((2 ^ m : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hp
  have htwo : (0 : ℝ) < (((2 ^ m : ℕ) : ℝ)) := by positivity
  have hlog := Real.log_le_log htwo hpR
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hm : (m : ℝ) / 2 ≤ Real.log (n : ℝ) := by nlinarith
  dsimp [binaryLength, m]
  push_cast
  linarith

lemma threshold_bounds {n : ℕ} (hL : 1 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) ≤ (logThreshold n : ℝ) ∧
      (logThreshold n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  constructor
  · exact Nat.le_ceil _
  · exact (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)

lemma window_bounds (j : ℕ) {n : ℕ}
    (hpow : 2 ≤ Real.log (n : ℝ) ^ j) :
    Real.log (n : ℝ) ^ j / 2 ≤ (logWindow j n : ℝ) ∧
      (logWindow j n : ℝ) ≤ Real.log (n : ℝ) ^ j := by
  have hpnonneg : 0 ≤ Real.log (n : ℝ) ^ j := by positivity
  constructor
  · have hlt := Nat.lt_floor_add_one (Real.log (n : ℝ) ^ j)
    dsimp [logWindow]
    linarith
  · exact Nat.floor_le hpnonneg

def discreteScale (n : ℕ) : ℝ :=
  (binaryLength n : ℝ) ^ 2 / binaryLength (binaryLength n)

lemma discrete_scale_bounds {n : ℕ} (hn : 1 ≤ n)
    (hH : 2 ≤ Real.log (Real.log (n : ℝ))) :
    (Real.log (n : ℝ)) ^ 2 /
          (5 * Real.log (Real.log (n : ℝ))) ≤ discreteScale n ∧
      discreteScale n ≤
        9 * ((Real.log (n : ℝ)) ^ 2 /
          Real.log (Real.log (n : ℝ))) := by
  let L := Real.log (n : ℝ)
  let e := binaryLength n
  let v := binaryLength e
  have hLpos : 0 < L := by
    have hLnonneg : 0 ≤ L := by
      apply Real.log_nonneg
      exact_mod_cast hn
    by_contra h
    have hLzero : L = 0 := le_antisymm (le_of_not_gt h) hLnonneg
    dsimp [L] at hH hLzero
    rw [hLzero, Real.log_zero] at hH
    norm_num at hH
  have hHpos : 0 < Real.log L := by dsimp [L] at hH ⊢; linarith
  have heone : 1 ≤ e := by dsimp [e, binaryLength]; omega
  have heposR : (0 : ℝ) < e := by exact_mod_cast heone
  have hvpos : (0 : ℝ) < v := by
    exact_mod_cast (show 0 < v by dsimp [v, binaryLength]; omega)
  have hLe : L ≤ (e : ℝ) := by
    simpa [L, e] using log_le_binaryLength hn
  have heupper : (e : ℝ) ≤ 3 * L := by
    have he := binaryLength_le_two_log_add_one hn
    have hLone : 1 ≤ Real.log (n : ℝ) := by
      have hexp := Real.exp_le_exp.mpr hH
      rw [Real.exp_log hLpos] at hexp
      have hexpone : (1 : ℝ) < Real.exp 2 :=
        lt_trans one_lt_two
          (Real.exp_one_gt_two.trans_le (Real.exp_monotone (by norm_num)))
      linarith
    dsimp [e, L] at he ⊢
    linarith
  have hHv : Real.log L ≤ (v : ℝ) := by
    have hloge : Real.log L ≤ Real.log (e : ℝ) :=
      Real.log_le_log hLpos hLe
    exact hloge.trans (by simpa [v] using log_le_binaryLength heone)
  have hvupper : (v : ℝ) ≤ 5 * Real.log L := by
    have hvraw := binaryLength_le_two_log_add_one heone
    have hloge : Real.log (e : ℝ) ≤ Real.log (3 * L) :=
      Real.log_le_log heposR heupper
    have h3pos : (0 : ℝ) < 3 := by norm_num
    rw [Real.log_mul h3pos.ne' hLpos.ne'] at hloge
    have hlog3 : Real.log 3 ≤ Real.log L := by
      apply Real.log_le_log (by norm_num)
      have hexp := Real.exp_le_exp.mpr hH
      rw [Real.exp_log hLpos] at hexp
      have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
        rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by
          rw [← Real.exp_add]
          norm_num]
        nlinarith [Real.exp_one_gt_two]
      linarith
    dsimp [v] at hvraw ⊢
    linarith
  constructor
  · dsimp [discreteScale, e, v]
    have hsquare : L ^ 2 ≤ (e : ℝ) ^ 2 := by nlinarith
    exact div_le_div₀ (by positivity) hsquare hvpos hvupper
  · dsimp [discreteScale, e, v]
    have hsquare : (e : ℝ) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
    calc
      (e : ℝ) ^ 2 / v ≤ (9 * L ^ 2) / Real.log L :=
        div_le_div₀ (by positivity) hsquare hHpos hHv
      _ = 9 * (L ^ 2 / Real.log L) := by ring

lemma eventually_const_mul_log_pow_le_nat (C j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (C : ℝ) * Real.log (n : ℝ) ^ j ≤ (n : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop,
      ‖(C : ℝ) * Real.log x ^ j‖ ≤ 1 * ‖x‖ :=
    (Real.isLittleO_pow_log_id_atTop.const_mul_left (C : ℝ)).bound one_pos
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (1 : ℕ)] with n hn hnone
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hnR : (0 : ℝ) ≤ n := by positivity
  rw [abs_of_nonneg hnR] at hn
  exact (le_abs_self _).trans hn

lemma mul_ceilDiv_64_le (x : ℕ) : 64 * (x ⌈/⌉ 64) ≤ x + 63 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h := Nat.div_mul_le_self (x + 64 - 1) 64
  rw [show x + 64 - 1 = x + 63 by omega] at h ⊢
  simpa [mul_comm] using h

lemma succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m + 1 + 1 ≤ 2 * (m + 1) := by omega
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ac_rfl

lemma sixteen_mul_succ_le_two_pow {m : ℕ} (hm : 8 ≤ m) :
    16 * (m + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      calc
        16 * (m + 1 + 1) ≤ 2 * (16 * (m + 1)) := by omega
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ac_rfl

lemma cubic_gain_small {e : ℕ} (he : e ≠ 0)
    (hm : 16 ≤ Nat.log 2 e) :
    4096 * 4 ^ (binaryLength e / 64) ≤ e := by
  let m := Nat.log 2 e
  let c := binaryLength e / 64
  have hexp : 12 + 2 * c ≤ m := by
    dsimp [c, binaryLength, m]
    omega
  have hp : 2 ^ (12 + 2 * c) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by omega) hexp
  have hme : 2 ^ m ≤ e := Nat.pow_log_le_self 2 he
  calc
    4096 * 4 ^ c = 2 ^ (12 + 2 * c) := by
      rw [pow_add]
      norm_num
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul,
        show 2 * c = c * 2 by omega, pow_mul]
    _ ≤ 2 ^ m := hp
    _ ≤ e := hme

lemma eventually_basic_rounding :
    ∀ᶠ n : ℕ in atTop,
      let L := Real.log (n : ℝ)
      let t := logThreshold n
      let s₂ := logWindow 2 n
      let s₃ := logWindow 3 n
      let e := binaryLength n
      100 ≤ L ∧
      L ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2 * L ∧
      L ^ 2 / 2 ≤ (s₂ : ℝ) ∧ (s₂ : ℝ) ≤ L ^ 2 ∧
      L ^ 3 / 2 ≤ (s₃ : ℝ) ∧ (s₃ : ℝ) ≤ L ^ 3 ∧
      L ≤ (e : ℝ) ∧ (e : ℝ) ≤ 3 * L := by
  have hL : ∀ᶠ n : ℕ in atTop, 100 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  filter_upwards [hL, eventually_ge_atTop (1 : ℕ)] with n hL hn
  have ht := threshold_bounds (n := n) (by linarith)
  have hs2 := window_bounds 2 (n := n) (by nlinarith)
  have hs3 := window_bounds 3 (n := n) (by nlinarith)
  have helo := log_le_binaryLength hn
  have hehi := binaryLength_le_two_log_add_one hn
  dsimp
  constructor
  · exact hL
  constructor
  · exact ht.1
  constructor
  · exact ht.2
  constructor
  · exact hs2.1
  constructor
  · exact hs2.2
  constructor
  · exact hs3.1
  constructor
  · exact hs3.2
  constructor
  · exact helo
  · linarith

lemma eventually_square_upper :
    ∀ᶠ n : ℕ in atTop,
      squareValue n <
        universalUpperTarget (squareColorCount (logThreshold n))
          (binaryLength n) := by
  let D : ℕ := 3 * 2 ^ 70
  have hgrowth3 := eventually_const_mul_log_pow_le_nat 4 3
  have hgrowth2 := eventually_const_mul_log_pow_le_nat (100 * D) 2
  filter_upwards [eventually_basic_rounding, hgrowth3, hgrowth2,
      eventually_ge_atTop (1 : ℕ)] with n hb hg3 hg2 hn
  let L := Real.log (n : ℝ)
  let t := logThreshold n
  let s := logWindow 2 n
  let e := binaryLength n
  have hL : 100 ≤ L := hb.1
  have htlo : L ≤ (t : ℝ) := hb.2.1
  have hthi : (t : ℝ) ≤ 2 * L := hb.2.2.1
  have hslo : L ^ 2 / 2 ≤ (s : ℝ) := hb.2.2.2.1
  have hshi : (s : ℝ) ≤ L ^ 2 := hb.2.2.2.2.1
  have helo : L ≤ (e : ℝ) := hb.2.2.2.2.2.2.2.1
  have hehi : (e : ℝ) ≤ 3 * L := hb.2.2.2.2.2.2.2.2
  have ht : 2 ≤ t := by exact_mod_cast (show (2 : ℝ) ≤ t by linarith)
  have hst : 2 * (t - 1) ≤ s := by
    have hstR : ((2 * (t - 1) : ℕ) : ℝ) ≤ (s : ℝ) := by
      push_cast
      have htminus : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast Nat.sub_le t 1
      nlinarith
    exact_mod_cast hstR
  have hs : s ≤ t * e := by
    have hsR : (s : ℝ) ≤ ((t * e : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hsR
  have hr64 : 64 * squareDenseCount n s ≤ e * s + 65 := by
    simpa [squareDenseCount, e] using mul_ceilDiv_64_le (e * s + 2)
  have hrT : 4 * t * squareDenseCount n s ≤ s * s := by
    have hscaled := Nat.mul_le_mul_left (4 * t) hr64
    have hrTR : ((4 * t * squareDenseCount n s : ℕ) : ℝ) ≤
        ((s * s : ℕ) : ℝ) := by
      have hscaledR : ((4 * t * (64 * squareDenseCount n s) : ℕ) : ℝ) ≤
          ((4 * t * (e * s + 65) : ℕ) : ℝ) := by exact_mod_cast hscaled
      push_cast at hscaledR ⊢
      have hte : (t : ℝ) * e ≤ 6 * L ^ 2 := by
        calc
          (t : ℝ) * e ≤ (2 * L) * (3 * L) :=
            mul_le_mul hthi hehi (by positivity) (by positivity)
          _ = 6 * L ^ 2 := by ring
      have hL2s : L ^ 2 ≤ 2 * (s : ℝ) := by linarith
      have htes : (t : ℝ) * e * s ≤ 12 * (s : ℝ) ^ 2 := by
        calc
          (t : ℝ) * e * s ≤ (6 * L ^ 2) * s :=
            mul_le_mul_of_nonneg_right hte (by positivity)
          _ ≤ 12 * (s : ℝ) ^ 2 := by nlinarith
      have hrem : 65 * (t : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (L ^ 2 - 8 * L)]
      nlinarith
    exact_mod_cast hrTR
  have hrn : squareDenseCount n s ≤ n := by
    have hg3' : (4 : ℝ) * L ^ 3 ≤ (n : ℝ) := by simpa [L] using hg3
    have hrR : (64 : ℝ) * squareDenseCount n s ≤ (e : ℝ) * s + 65 := by
      exact_mod_cast hr64
    have : (squareDenseCount n s : ℝ) ≤ (n : ℝ) := by
      nlinarith
    exact_mod_cast this
  have hqn : universalUpperTarget (squareColorCount t) e ≤ n := by
    have hg2' : (100 * D : ℝ) * L ^ 2 ≤ (n : ℝ) := by
      simpa [L] using hg2
    have hqR : (universalUpperTarget (squareColorCount t) e : ℝ) ≤
        (100 * D : ℝ) * L ^ 2 := by
      dsimp [universalUpperTarget, squareColorCount, D]
      push_cast
      nlinarith
    exact_mod_cast hqR.trans hg2'
  exact square_upper_parameter_bound hn ht hst hs hrT hrn
    (by simpa [t, e] using hqn)

lemma eventually_cubic_upper :
    ∀ᶠ n : ℕ in atTop,
      cubicValue n <
        universalUpperTarget (cubicColorCount n (logThreshold n))
          (binaryLength n) := by
  have hH : ∀ᶠ n : ℕ in atTop,
      100 ≤ Real.log (Real.log (n : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  have hgrowth6 := eventually_const_mul_log_pow_le_nat 1 6
  have hgrowth2 := eventually_const_mul_log_pow_le_nat 100 2
  filter_upwards [eventually_basic_rounding, hH, hgrowth6, hgrowth2,
      eventually_ge_atTop (1 : ℕ)] with n hb hHn hg6 hg2 hn
  let L := Real.log (n : ℝ)
  let t := logThreshold n
  let s := logWindow 3 n
  let e := binaryLength n
  let v := binaryLength e
  let c := cubicChunk n
  let d := cubicColorCount n t
  let r := cubicBlockCount s t
  let h := cubicRemainder s t
  let A := 4 ^ c
  let B := e * s + binaryLength s * t * r + 2
  have hL : 100 ≤ L := hb.1
  have htlo : L ≤ (t : ℝ) := hb.2.1
  have hthi : (t : ℝ) ≤ 2 * L := hb.2.2.1
  have hslo : L ^ 3 / 2 ≤ (s : ℝ) := hb.2.2.2.2.2.1
  have hshi : (s : ℝ) ≤ L ^ 3 := hb.2.2.2.2.2.2.1
  have helo : L ≤ (e : ℝ) := hb.2.2.2.2.2.2.2.1
  have hehi : (e : ℝ) ≤ 3 * L := hb.2.2.2.2.2.2.2.2
  have hLpos : 0 < L := by linarith
  have htpos : 0 < t := by
    exact_mod_cast (show (0 : ℝ) < (t : ℝ) by linarith)
  have heone : 1 ≤ e := by dsimp [e, binaryLength]; omega
  have hHv : Real.log L ≤ (v : ℝ) := by
    have hloge : Real.log L ≤ Real.log (e : ℝ) :=
      Real.log_le_log hLpos helo
    exact hloge.trans (by simpa [v] using log_le_binaryLength heone)
  have hv100 : 100 ≤ v := by
    exact_mod_cast (show (100 : ℝ) ≤ (v : ℝ) by
      exact hHn.trans hHv)
  have hc : 0 < c := by
    have : 0 < v / 64 := Nat.div_pos (by omega) (by omega)
    simpa [c, cubicChunk, v] using this
  have hm : 16 ≤ Nat.log 2 e := by
    dsimp [v, binaryLength] at hv100
    omega
  have hAsmall : 4096 * A ≤ e := by
    simpa [A, c, cubicChunk, v] using cubic_gain_small (by omega : e ≠ 0) hm
  have hvle : v ≤ e := by
    have hp : Nat.log 2 e + 1 ≤ 2 ^ Nat.log 2 e := succ_le_two_pow _
    have hp' : v ≤ 2 ^ Nat.log 2 e := by simpa [v, binaryLength] using hp
    exact hp'.trans (Nat.pow_log_le_self 2 (by omega))
  have hse : s ≤ e ^ 3 := by
    have hseR : (s : ℝ) ≤ ((e ^ 3 : ℕ) : ℝ) := by
      push_cast
      exact hshi.trans (pow_le_pow_left₀ (by positivity) helo 3)
    exact_mod_cast hseR
  have hu : binaryLength s ≤ 3 * v := by
    have hev : e < 2 ^ v := n_lt_two_pow_binaryLength e
    have hp := Nat.pow_lt_pow_left hev (by omega : (3 : ℕ) ≠ 0)
    have hslt : s < 2 ^ (3 * v) := by
      calc
        s ≤ e ^ 3 := hse
        _ < (2 ^ v) ^ 3 := hp
        _ = 2 ^ (3 * v) := by
          rw [show 3 * v = v * 3 by omega, pow_mul]
    exact binaryLength_le_of_lt_two_pow (by omega) hslt
  have hrt : r * t ≤ s := by
    calc
      r * t ≤ r * (2 * t) := Nat.mul_le_mul_left r (by omega)
      _ ≤ s := by
        dsimp [r, cubicBlockCount]
        simpa [mul_comm] using Nat.div_mul_le_self s (2 * t)
  have hh : h ≤ s := by dsimp [h, cubicRemainder]; omega
  have hB : B ≤ 6 * e * s := by
    have hterm : binaryLength s * t * r ≤ 3 * e * s := by
      calc
        binaryLength s * t * r = binaryLength s * (r * t) := by ring
        _ ≤ binaryLength s * s := Nat.mul_le_mul_left _ hrt
        _ ≤ (3 * v) * s := Nat.mul_le_mul_right _ hu
        _ ≤ (3 * e) * s := Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 3 hvle)
    dsimp [B]
    have hes : 1 ≤ e * s := by
      have hspos : 0 < s := by
        exact_mod_cast (show (0 : ℝ) < (s : ℝ) by nlinarith)
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hspos.ne')
    nlinarith
  have hs4t : 4 * t ≤ s := by
    have hs4tR : ((4 * t : ℕ) : ℝ) ≤ (s : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hs4tR
  have hfourtr : s ≤ 4 * t * r := by
    have hdenpos : 0 < 2 * t := Nat.mul_pos (by omega) htpos
    have hdiv : s < (r + 1) * (2 * t) := by
      change s < (s / (2 * t) + 1) * (2 * t)
      exact (Nat.div_lt_iff_lt_mul hdenpos).mp (Nat.lt_succ_self _)
    have hrpos : 0 < r := by
      change 0 < s / (2 * t)
      exact Nat.div_pos (by omega) hdenpos
    have hstep : (r + 1) * (2 * t) ≤ 4 * t * r := by
      nlinarith
    exact hdiv.le.trans hstep
  have htwoh : s ≤ 2 * h := by
    have hhalf : 2 * (r * t) ≤ s := by
      calc
        2 * (r * t) = r * (2 * t) := by ring
        _ ≤ s := by
          dsimp [r, cubicBlockCount]
          simpa [mul_comm] using Nat.div_mul_le_self s (2 * t)
    change s ≤ 2 * (s - r * t)
    omega
  have hrhlower : s * s ≤ 8 * t * (r * h) := by
    calc
      s * s ≤ (4 * t * r) * (2 * h) :=
        Nat.mul_le_mul hfourtr htwoh
      _ = 8 * t * (r * h) := by ring
  have hte2 : 6 * t * e ^ 2 ≤ 512 * s := by
    have hte2R : ((6 * t * e ^ 2 : ℕ) : ℝ) ≤ ((512 * s : ℕ) : ℝ) := by
      push_cast
      have he2 : (e : ℝ) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
      have hte : (t : ℝ) * e ^ 2 ≤ 18 * L ^ 3 := by
        calc
          (t : ℝ) * e ^ 2 ≤ (2 * L) * (9 * L ^ 2) :=
            mul_le_mul hthi he2 (by positivity) (by positivity)
          _ = 18 * L ^ 3 := by ring
      nlinarith
    exact_mod_cast hte2R
  have hlocal : A * B ≤ r * h := by
    have hleft : 4096 * (A * B) ≤ 6 * e ^ 2 * s := by
      calc
        4096 * (A * B) = (4096 * A) * B := by ring
        _ ≤ e * B := Nat.mul_le_mul hAsmall (le_refl B)
        _ ≤ e * (6 * e * s) := Nat.mul_le_mul_left e hB
        _ = 6 * e ^ 2 * s := by ring
    have hright : 6 * e ^ 2 * s ≤ 4096 * (r * h) := by
      have hsMul := Nat.mul_le_mul_right s hte2
      have hrr := Nat.mul_le_mul_left 512 hrhlower
      have hrr' : 512 * (s * s) ≤ 4096 * t * (r * h) := by
        calc
          512 * (s * s) ≤ 512 * (8 * t * (r * h)) := hrr
          _ = 4096 * t * (r * h) := by ring
      have hchain : 6 * t * e ^ 2 * s ≤ 4096 * t * (r * h) := by
        calc
          6 * t * e ^ 2 * s ≤ 512 * s * s := by simpa [mul_assoc] using hsMul
          _ = 512 * (s * s) := by ring
          _ ≤ 4096 * t * (r * h) := hrr'
      apply Nat.le_of_mul_le_mul_left (c := t)
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hchain
      · exact_mod_cast (show (0 : ℝ) < (t : ℝ) by linarith)
    exact Nat.le_of_mul_le_mul_left (hleft.trans hright) (by norm_num)
  have hlocalE : (r * h) * t ≤ n := by
    have hrs : r * h * t ≤ s ^ 2 := by
      calc
        r * h * t = (r * t) * h := by ring
        _ ≤ s ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hrt hh
    have hg6' : L ^ 6 ≤ (n : ℝ) := by simpa [L] using hg6
    have hs2R : ((s ^ 2 : ℕ) : ℝ) ≤ L ^ 6 := by
      push_cast
      calc
        (s : ℝ) ^ 2 ≤ (L ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hshi 2
        _ = L ^ 6 := by ring
    have hs2n : s ^ 2 ≤ n := by exact_mod_cast hs2R.trans hg6'
    exact hrs.trans hs2n
  have hdle : d ≤ t := by
    apply (ceilDiv_le_iff_le_mul hc).2
    simpa [d, c, cubicColorCount, mul_comm] using
      (Nat.le_mul_of_pos_left t hc)
  have hqn : universalUpperTarget d e ≤ n := by
    have hg2' : (100 : ℝ) * L ^ 2 ≤ (n : ℝ) := by simpa [L] using hg2
    have hqR : (universalUpperTarget d e : ℝ) ≤ 100 * L ^ 2 := by
      dsimp [universalUpperTarget]
      push_cast
      have hdR : (d : ℝ) ≤ t := by exact_mod_cast hdle
      nlinarith
    exact_mod_cast hqR.trans hg2'
  exact cubic_upper_parameter_bound hn htpos hc
    (by simpa [cubicLocalExponent, A, B, c, e, r, h] using hlocal)
    (by simpa [r, h, t] using hlocalE)
    (by simpa [d, e, t] using hqn)

def lowerTarget (j n : ℕ) : ℕ :=
  lowerIterations n (logWindow j n) * (logThreshold n / 2)

lemma lowerTarget_discrete_bound {j n e v m u t : ℕ}
    (he : e = m + 1) (hu : u ≤ 3 * v) (hm : 12 * v ≤ m)
    (het : e ≤ 3 * t) (ht : 2 ≤ t)
    (huDef : u = binaryLength (logWindow j n))
    (hmDef : m = Nat.log 2 n) (heDef : e = binaryLength n)
    (hvDef : v = binaryLength e) (htDef : t = logThreshold n) :
    e ^ 2 ≤ 432 * v * lowerTarget j n := by
  let q := lowerIterations n (logWindow j n)
  have hupos : 0 < u := by
    rw [huDef]
    dsimp [binaryLength]
    omega
  have hden : 0 < 4 * u := by positivity
  have hlarge : 4 * u ≤ m := by nlinarith
  have hqpos : 0 < q := by
    dsimp [q, lowerIterations]
    rw [← hmDef, ← huDef]
    exact Nat.div_pos hlarge hden
  have hdiv : m < (q + 1) * (4 * u) := by
    have hlt : m / (4 * u) < m / (4 * u) + 1 := Nat.lt_succ_self _
    have := (Nat.div_lt_iff_lt_mul hden).mp hlt
    simpa [q, lowerIterations, hmDef, huDef] using this
  have hmq : m ≤ 8 * u * q := by
    have hq2 : q + 1 ≤ 2 * q := by omega
    calc
      m ≤ (q + 1) * (4 * u) := hdiv.le
      _ ≤ (2 * q) * (4 * u) := Nat.mul_le_mul_right _ hq2
      _ = 8 * u * q := by ring
  have hem : e ≤ 2 * m := by omega
  have heq : e ≤ 48 * v * q := by
    calc
      e ≤ 2 * m := hem
      _ ≤ 2 * (8 * u * q) := Nat.mul_le_mul_left 2 hmq
      _ ≤ 2 * (8 * (3 * v) * q) := by gcongr
      _ = 48 * v * q := by ring
  have hehalf : e ≤ 9 * (t / 2) := by
    have htHalf : t ≤ 3 * (t / 2) := by omega
    exact het.trans (Nat.mul_le_mul_left 3 htHalf) |>.trans_eq (by ring)
  have hmul := Nat.mul_le_mul heq hehalf
  simpa [lowerTarget, q, htDef, heDef, hvDef, pow_two, mul_assoc,
    mul_comm, mul_left_comm] using hmul

lemma eventually_lower_targets_and_scale :
    ∀ᶠ n : ℕ in atTop,
      (lowerTarget 2 n ≤ squareValue n ∧
        lowerTarget 3 n ≤ cubicValue n) ∧
      (binaryLength n) ^ 2 ≤
          432 * binaryLength (binaryLength n) * lowerTarget 2 n ∧
      (binaryLength n) ^ 2 ≤
          432 * binaryLength (binaryLength n) * lowerTarget 3 n := by
  have hH : ∀ᶠ n : ℕ in atTop,
      100 ≤ Real.log (Real.log (n : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  have hgrowth2 := eventually_const_mul_log_pow_le_nat 10 2
  filter_upwards [eventually_basic_rounding, hH, hgrowth2,
      eventually_ge_atTop (1 : ℕ)] with n hb hHn hg2 hn
  let L := Real.log (n : ℝ)
  let t := logThreshold n
  let s₂ := logWindow 2 n
  let s₃ := logWindow 3 n
  let e := binaryLength n
  let v := binaryLength e
  let m := Nat.log 2 n
  have hL : 100 ≤ L := hb.1
  have htlo : L ≤ (t : ℝ) := hb.2.1
  have hthi : (t : ℝ) ≤ 2 * L := hb.2.2.1
  have hs2lo : L ^ 2 / 2 ≤ (s₂ : ℝ) := hb.2.2.2.1
  have hs2hi : (s₂ : ℝ) ≤ L ^ 2 := hb.2.2.2.2.1
  have hs3lo : L ^ 3 / 2 ≤ (s₃ : ℝ) := hb.2.2.2.2.2.1
  have hs3hi : (s₃ : ℝ) ≤ L ^ 3 := hb.2.2.2.2.2.2.1
  have helo : L ≤ (e : ℝ) := hb.2.2.2.2.2.2.2.1
  have hehi : (e : ℝ) ≤ 3 * L := hb.2.2.2.2.2.2.2.2
  have hLpos : 0 < L := by linarith
  have ht : 2 ≤ t := by exact_mod_cast (show (2 : ℝ) ≤ t by linarith)
  have heone : 1 ≤ e := by dsimp [e, binaryLength]; omega
  have hHv : Real.log L ≤ (v : ℝ) := by
    have hloge : Real.log L ≤ Real.log (e : ℝ) :=
      Real.log_le_log hLpos helo
    exact hloge.trans (by simpa [v] using log_le_binaryLength heone)
  have hv100 : 100 ≤ v := by
    exact_mod_cast (show (100 : ℝ) ≤ (v : ℝ) from hHn.trans hHv)
  have hmE : 8 ≤ Nat.log 2 e := by
    dsimp [v, binaryLength] at hv100
    omega
  have h16v : 16 * v ≤ e := by
    have hp := sixteen_mul_succ_le_two_pow hmE
    have hpe := Nat.pow_log_le_self 2 (by omega : e ≠ 0)
    have hp' : 16 * v ≤ 2 ^ Nat.log 2 e := by
      simpa [v, binaryLength] using hp
    exact hp'.trans hpe
  have hem : e = m + 1 := by simp [e, m, binaryLength]
  have h12vm : 12 * v ≤ m := by
    rw [hem] at h16v
    omega
  have hs2e : s₂ ≤ e ^ 2 := by
    exact_mod_cast (show (s₂ : ℝ) ≤ ((e ^ 2 : ℕ) : ℝ) by
      push_cast
      exact hs2hi.trans (pow_le_pow_left₀ (by positivity) helo 2))
  have hs3e : s₃ ≤ e ^ 3 := by
    exact_mod_cast (show (s₃ : ℝ) ≤ ((e ^ 3 : ℕ) : ℝ) by
      push_cast
      exact hs3hi.trans (pow_le_pow_left₀ (by positivity) helo 3))
  have hu2 : binaryLength s₂ ≤ 2 * v := by
    have hp := Nat.pow_lt_pow_left (n_lt_two_pow_binaryLength e)
      (by omega : (2 : ℕ) ≠ 0)
    apply binaryLength_le_of_lt_two_pow (by omega)
    calc
      s₂ ≤ e ^ 2 := hs2e
      _ < (2 ^ v) ^ 2 := hp
      _ = 2 ^ (2 * v) := by
        rw [show 2 * v = v * 2 by omega, pow_mul]
  have hu3 : binaryLength s₃ ≤ 3 * v := by
    have hp := Nat.pow_lt_pow_left (n_lt_two_pow_binaryLength e)
      (by omega : (3 : ℕ) ≠ 0)
    apply binaryLength_le_of_lt_two_pow (by omega)
    calc
      s₃ ≤ e ^ 3 := hs3e
      _ < (2 ^ v) ^ 3 := hp
      _ = 2 ^ (3 * v) := by
        rw [show 3 * v = v * 3 by omega, pow_mul]
  have hlarge2 : 4 * binaryLength s₂ ≤ m := by omega
  have hlarge3 : 4 * binaryLength s₃ ≤ m := by omega
  have hfour2 : 4 * (t / 2) ≤ s₂ := by
    have hR : ((4 * (t / 2) : ℕ) : ℝ) ≤ (s₂ : ℝ) := by
      have htdiv : ((t / 2 : ℕ) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast Nat.div_le_self t 2
      push_cast
      nlinarith
    exact_mod_cast hR
  have hfour3 : 4 * (t / 2) ≤ s₃ := by
    have hR : ((4 * (t / 2) : ℕ) : ℝ) ≤ (s₃ : ℝ) := by
      have htdiv : ((t / 2 : ℕ) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast Nat.div_le_self t 2
      push_cast
      nlinarith
    exact_mod_cast hR
  have htarget2 : lowerTarget 2 n ≤ n := by
    have hg2' : (10 : ℝ) * L ^ 2 ≤ (n : ℝ) := by simpa [L] using hg2
    have hR : (lowerTarget 2 n : ℝ) ≤ 10 * L ^ 2 := by
      have hqNat : lowerIterations n s₂ ≤ e :=
        (Nat.div_le_self (Nat.log 2 n) _).trans (by omega)
      have hhalfNat : t / 2 ≤ t := Nat.div_le_self t 2
      have hprod : lowerTarget 2 n ≤ e * t := by
        dsimp [lowerTarget]
        exact Nat.mul_le_mul hqNat hhalfNat
      have hprodR : (lowerTarget 2 n : ℝ) ≤ (e : ℝ) * t := by
        exact_mod_cast hprod
      nlinarith
    exact_mod_cast hR.trans hg2'
  have htarget3 : lowerTarget 3 n ≤ n := by
    have hg2' : (10 : ℝ) * L ^ 2 ≤ (n : ℝ) := by simpa [L] using hg2
    have hR : (lowerTarget 3 n : ℝ) ≤ 10 * L ^ 2 := by
      have hqNat : lowerIterations n s₃ ≤ e :=
        (Nat.div_le_self (Nat.log 2 n) _).trans (by omega)
      have hhalfNat : t / 2 ≤ t := Nat.div_le_self t 2
      have hprod : lowerTarget 3 n ≤ e * t := by
        dsimp [lowerTarget]
        exact Nat.mul_le_mul hqNat hhalfNat
      have hprodR : (lowerTarget 3 n : ℝ) ≤ (e : ℝ) * t := by
        exact_mod_cast hprod
      nlinarith
    exact_mod_cast hR.trans hg2'
  have het : e ≤ 3 * t := by
    exact_mod_cast (show (e : ℝ) ≤ 3 * (t : ℝ) by nlinarith)
  constructor
  · constructor
    · apply le_localIndependenceNumber_of_guaranteed htarget2
      simpa [lowerTarget, s₂, t] using
        lower_bound_finite (n := n) (s := s₂) (t := t)
          (q := lowerIterations n s₂) ht hfour2
          (lower_room (by omega) hlarge2)
    · apply le_localIndependenceNumber_of_guaranteed htarget3
      simpa [lowerTarget, s₃, t] using
        lower_bound_finite (n := n) (s := s₃) (t := t)
          (q := lowerIterations n s₃) ht hfour3
          (lower_room (by omega) hlarge3)
  · constructor
    · simpa [e, v, m, s₂, t] using
        lowerTarget_discrete_bound (j := 2) (n := n)
          (e := e) (v := v) (m := m) (u := binaryLength s₂) (t := t)
          hem (by omega) h12vm het ht rfl rfl rfl rfl
    · simpa [e, v, m, s₃, t] using
        lowerTarget_discrete_bound (j := 3) (n := n)
          (e := e) (v := v) (m := m) (u := binaryLength s₃) (t := t)
          hem hu3 h12vm het ht rfl rfl rfl rfl

lemma eventually_lower_targets :
    ∀ᶠ n : ℕ in atTop,
      lowerTarget 2 n ≤ squareValue n ∧
      lowerTarget 3 n ≤ cubicValue n :=
  eventually_lower_targets_and_scale.mono (fun _ h ↦ h.1)

lemma discreteScale_le_of_binary_bound {n q : ℕ}
    (h : (binaryLength n) ^ 2 ≤
      432 * binaryLength (binaryLength n) * q) :
    discreteScale n ≤ 432 * (q : ℝ) := by
  have hv : (0 : ℝ) < binaryLength (binaryLength n) := by
    exact_mod_cast (show 0 < binaryLength (binaryLength n) by
      simp [binaryLength])
  rw [discreteScale, div_le_iff₀ hv]
  have hR : ((binaryLength n : ℝ) ^ 2) ≤
      432 * (binaryLength (binaryLength n) : ℝ) * (q : ℝ) := by
    exact_mod_cast h
  nlinarith

lemma eventually_lower_target_scale :
    ∀ᶠ n : ℕ in atTop,
      discreteScale n ≤ 432 * (lowerTarget 2 n : ℝ) ∧
      discreteScale n ≤ 432 * (lowerTarget 3 n : ℝ) :=
  eventually_lower_targets_and_scale.mono fun _ h ↦
    ⟨discreteScale_le_of_binary_bound h.2.1,
      discreteScale_le_of_binary_bound h.2.2⟩

lemma eventually_resolution_discrete_bounds :
    ∀ᶠ n : ℕ in atTop,
      resolutionScale n / 5 ≤ discreteScale n ∧
      discreteScale n ≤ 9 * resolutionScale n := by
  have hH : ∀ᶠ n : ℕ in atTop,
      2 ≤ Real.log (Real.log (n : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hH, eventually_ge_atTop (1 : ℕ)] with n hHn hn
  have h := discrete_scale_bounds hn hHn
  constructor
  · calc
      resolutionScale n / 5 =
          Real.log (n : ℝ) ^ 2 /
            (5 * Real.log (Real.log (n : ℝ))) := by
              simp [resolutionScale]
              ring
      _ ≤ discreteScale n := h.1
  · simpa [resolutionScale] using h.2

def squareUpperConstant : ℕ := 100 * (3 * 2 ^ 70)

lemma eventually_square_target_bound :
    ∀ᶠ n : ℕ in atTop,
      (universalUpperTarget (squareColorCount (logThreshold n))
          (binaryLength n) : ℝ) ≤
        squareUpperConstant * Real.log (n : ℝ) ^ 2 := by
  filter_upwards [eventually_basic_rounding] with n hb
  let L := Real.log (n : ℝ)
  let t := logThreshold n
  let e := binaryLength n
  have hL : 100 ≤ L := hb.1
  have hthi : (t : ℝ) ≤ 2 * L := hb.2.2.1
  have hehi : (e : ℝ) ≤ 3 * L := hb.2.2.2.2.2.2.2.2
  dsimp [universalUpperTarget, squareColorCount, squareUpperConstant, t, e]
  push_cast
  nlinarith

lemma eventually_cubic_target_bound :
    ∀ᶠ n : ℕ in atTop,
      (universalUpperTarget (cubicColorCount n (logThreshold n))
          (binaryLength n) : ℝ) ≤ 10000 * discreteScale n := by
  have hH : ∀ᶠ n : ℕ in atTop,
      100 ≤ Real.log (Real.log (n : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  filter_upwards [eventually_basic_rounding, hH] with n hb hHn
  let L := Real.log (n : ℝ)
  let t := logThreshold n
  let e := binaryLength n
  let v := binaryLength e
  let c := cubicChunk n
  let d := cubicColorCount n t
  have hL : 100 ≤ L := hb.1
  have htlo : L ≤ (t : ℝ) := hb.2.1
  have hthi : (t : ℝ) ≤ 2 * L := hb.2.2.1
  have helo : L ≤ (e : ℝ) := hb.2.2.2.2.2.2.2.1
  have hLpos : 0 < L := by linarith
  have heone : 1 ≤ e := by dsimp [e, binaryLength]; omega
  have hHv : Real.log L ≤ (v : ℝ) := by
    have hloge : Real.log L ≤ Real.log (e : ℝ) :=
      Real.log_le_log hLpos helo
    exact hloge.trans (by simpa [v] using log_le_binaryLength heone)
  have hv100 : 100 ≤ v := by
    exact_mod_cast (show (100 : ℝ) ≤ (v : ℝ) from hHn.trans hHv)
  have hv64 : 64 ≤ v := by omega
  have hc : 0 < c := by
    change 0 < v / 64
    exact Nat.div_pos hv64 (by norm_num)
  have hvle : v ≤ e := by
    have hp : Nat.log 2 e + 1 ≤ 2 ^ Nat.log 2 e := succ_le_two_pow _
    have hp' : v ≤ 2 ^ Nat.log 2 e := by
      simpa [v, binaryLength] using hp
    exact hp'.trans (Nat.pow_log_le_self 2 (by omega))
  have htle : t ≤ 2 * e := by
    exact_mod_cast (show (t : ℝ) ≤ 2 * (e : ℝ) by linarith)
  have hcv : v ≤ 128 * c := by
    have hdiv : v < (v / 64 + 1) * 64 := by
      exact (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _)
    change v ≤ 128 * (v / 64)
    have hc1 : 1 ≤ v / 64 := Nat.div_pos hv64 (by norm_num)
    omega
  have hdc : d * c ≤ t + c := by
    have hdiv := Nat.div_mul_le_self (t + c - 1) c
    dsimp [d, cubicColorCount]
    rw [Nat.ceilDiv_eq_add_pred_div]
    simpa [mul_comm] using hdiv.trans (Nat.sub_le (t + c) 1)
  have hcle : c ≤ e := by
    exact (Nat.div_le_self v 64).trans hvle
  have hdv : d * v ≤ 384 * e := by
    calc
      d * v ≤ d * (128 * c) := Nat.mul_le_mul_left d hcv
      _ = 128 * (d * c) := by ring
      _ ≤ 128 * (t + c) := Nat.mul_le_mul_left 128 hdc
      _ ≤ 128 * (2 * e + e) := by omega
      _ = 384 * e := by ring
  have hqv : universalUpperTarget d e * v ≤ 10000 * e ^ 2 := by
    have hee : e ≤ e ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_le_mul_left e heone
    dsimp [universalUpperTarget]
    calc
      (4 * d * (e + 2) + 2) * v =
          4 * (d * v) * (e + 2) + 2 * v := by ring
      _ ≤ 4 * (384 * e) * (e + 2) + 2 * e := by gcongr
      _ = 1536 * e ^ 2 + 3074 * e := by ring
      _ ≤ 1536 * e ^ 2 + 3074 * e ^ 2 := by gcongr
      _ ≤ 10000 * e ^ 2 := by omega
  have hvposR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hqvR : (universalUpperTarget d e : ℝ) * (v : ℝ) ≤
      10000 * (e : ℝ) ^ 2 := by
    exact_mod_cast hqv
  rw [show 10000 * discreteScale n =
      (10000 * (e : ℝ) ^ 2) / (v : ℝ) by
        simp [discreteScale, e, v]
        ring]
  rw [le_div_iff₀ hvposR]
  simpa [d, e, t, v, mul_assoc, mul_comm, mul_left_comm] using hqvR

/-- The resolution of Erdős Problem 804.  With the integer rounding fixed by
`logWindow` and `logThreshold`, the square window is between constant
multiples of `log n ^ 2 / log (log n)` and `log n ^ 2`, while the cubic
window is between constant multiples of `log n ^ 2 / log (log n)`.

The constants are deliberately explicit.  Their numerical values are not
intended to be sharp. -/
theorem erdos_804 :
    ∃ c₂ C₂ c₃ C₃ : ℝ,
      0 < c₂ ∧ 0 < C₂ ∧ 0 < c₃ ∧ 0 < C₃ ∧
      ∀ᶠ n : ℕ in atTop,
        c₂ * resolutionScale n ≤ (squareValue n : ℝ) ∧
        (squareValue n : ℝ) ≤ C₂ * Real.log (n : ℝ) ^ 2 ∧
        c₃ * resolutionScale n ≤ (cubicValue n : ℝ) ∧
        (cubicValue n : ℝ) ≤ C₃ * resolutionScale n := by
  refine ⟨1 / 2160, (squareUpperConstant : ℝ), 1 / 2160, 90000,
    by norm_num, by norm_num [squareUpperConstant], by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_lower_targets, eventually_lower_target_scale,
      eventually_resolution_discrete_bounds, eventually_square_upper,
      eventually_square_target_bound, eventually_cubic_upper,
      eventually_cubic_target_bound] with n hlow hlowScale hscale hsquare
        hsquareTarget hcubic hcubicTarget
  have hlowSquareR : (lowerTarget 2 n : ℝ) ≤ squareValue n := by
    exact_mod_cast hlow.1
  have hlowCubicR : (lowerTarget 3 n : ℝ) ≤ cubicValue n := by
    exact_mod_cast hlow.2
  have hsquareR : (squareValue n : ℝ) ≤
      universalUpperTarget (squareColorCount (logThreshold n))
        (binaryLength n) := by
    exact_mod_cast hsquare.le
  have hcubicR : (cubicValue n : ℝ) ≤
      universalUpperTarget (cubicColorCount n (logThreshold n))
        (binaryLength n) := by
    exact_mod_cast hcubic.le
  constructor
  · calc
      (1 / 2160 : ℝ) * resolutionScale n ≤ lowerTarget 2 n := by
        nlinarith [hscale.1, hlowScale.1]
      _ ≤ squareValue n := hlowSquareR
  constructor
  · exact hsquareR.trans hsquareTarget
  constructor
  · calc
      (1 / 2160 : ℝ) * resolutionScale n ≤ lowerTarget 3 n := by
        nlinarith [hscale.1, hlowScale.2]
      _ ≤ cubicValue n := hlowCubicR
  · calc
      (cubicValue n : ℝ) ≤
          universalUpperTarget (cubicColorCount n (logThreshold n))
            (binaryLength n) := hcubicR
      _ ≤ 10000 * discreteScale n := hcubicTarget
      _ ≤ 90000 * resolutionScale n := by nlinarith [hscale.2]

end Erdos804

#print axioms Erdos804.erdos_804
