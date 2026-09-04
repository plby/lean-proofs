/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 752.
https://www.erdosproblems.com/forum/thread/752

Informal authors:
- Benny Sudakov
- Jacques Verstraëte

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos752.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos182.Elementary
import ErdosProblems.Erdos182.PRSEntry
import ErdosProblems.Erdos752.Erdos752Moore
import ErdosProblems.Erdos752.Erdos752Posa
import ErdosProblems.Erdos752.Erdos752BFS
import ErdosProblems.Erdos752.Erdos752Component
import ErdosProblems.Erdos752.Erdos752AssemblyAlt
import ErdosProblems.Erdos752.Erdos752Kernel

/-!
# Erdős Problem 752

Sudakov and Verstraëte proved that a finite graph of minimum degree at least
`k` and girth greater than `2 * s` has order `k ^ s` distinct cycle lengths.
They proved the stronger average-degree conclusion with consecutive even
lengths.  The detailed argument and the authors' correction to that stronger
proof are in `tex/752.tex`.
-/

open Finset
open SimpleGraph

namespace Erdos752

universe u

/-- `G` contains a simple cycle whose length is exactly `l`. -/
def HasCycleLength {V : Type u} (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = l

/-- A block of `m` consecutive even integers, starting at `2 * a`, consists
of cycle lengths of `G`. -/
def HasConsecutiveEvenCycleLengths {V : Type u} (G : SimpleGraph V)
    (a m : ℕ) : Prop :=
  ∀ i < m, HasCycleLength G (2 * (a + i))

/-- Cycle lengths are preserved by injective graph homomorphisms. -/
lemma HasCycleLength.of_injectiveHom {W : Type*} {F : SimpleGraph V}
    {G : SimpleGraph W} (f : F →g G) (hf : Function.Injective f) {l : ℕ}
    (h : HasCycleLength F l) : HasCycleLength G l := by
  exact exists_isCycle_length_of_injectiveHom f hf h

/-- An explicit uniform form of the original minimum-degree problem.  The
constant choices are those obtained from the distinct-length proof in
Sudakov--Verstraëte, Theorem 2.2. -/
def ExplicitMinimumDegreeResolution : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ (k : ℕ), 576 ≤ k →
    ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      k ≤ G.minDegree →
      GirthGreaterThan G (2 * s) →
      ∃ L : Finset ℕ,
        k ^ s ≤ (12 * 192 ^ s) * L.card ∧ ∀ l ∈ L, HasCycleLength G l

/-- The `≫_s k^s` formulation of Erdős Problem 752, with all uniform
quantifiers made explicit. -/
def MinimumDegreeResolution : Prop :=
  ∀ (s : ℕ), 1 ≤ s →
    ∃ C : ℕ, 0 < C ∧ ∃ k₀ : ℕ,
      ∀ (k : ℕ), k₀ ≤ k →
        ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          k ≤ G.minDegree →
          GirthGreaterThan G (2 * s) →
          ∃ L : Finset ℕ,
            k ^ s ≤ C * L.card ∧ ∀ l ∈ L, HasCycleLength G l

/-- The quantitative graph-theoretic kernel used in the proof.  The
divisibility condition makes `D ^ s / 3` exact in the DFS long-path step;
`6 ≤ D` ensures that this path has enough vertices for the branch assembly. -/
def DistinctLengthKernel : Prop :=
  ∀ (D : ℕ), 6 ≤ D → 3 ∣ D →
    ∀ (s : ℕ), 1 ≤ s →
      ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        48 * (D + 1) ≤ G.minDegree →
        GirthGreaterThan G (2 * s) →
        ∃ L : Finset ℕ,
          D ^ s ≤ 12 * L.card ∧ ∀ l ∈ L, HasCycleLength G l

/-- The lengths displayed by a consecutive-even block form a finset of the
same cardinality, all of whose members are cycle lengths. -/
lemma consecutiveEvenCycleLengths_finset {V : Type u} {G : SimpleGraph V}
    {a m : ℕ} (h : HasConsecutiveEvenCycleLengths G a m) :
    ∃ L : Finset ℕ, L.card = m ∧ ∀ l ∈ L, HasCycleLength G l := by
  classical
  let f : ℕ → ℕ := fun i ↦ 2 * (a + i)
  let e : ℕ ↪ ℕ := ⟨f, by
    intro i j hij
    dsimp [f] at hij
    omega⟩
  refine ⟨(Finset.range m).map e, by simp, ?_⟩
  · intro l hl
    rw [Finset.mem_map] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    exact h i (Finset.mem_range.mp hi)

/-- The handshake identity turns the minimum-degree hypothesis into the
cross-multiplied average-degree hypothesis. -/
lemma averageDegree_of_minDegree {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : k ≤ G.minDegree) :
    k * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    k * Fintype.card V = ∑ _v : V, k := by simp [Nat.mul_comm]
    _ ≤ ∑ v : V, G.degree v := by
      apply Finset.sum_le_sum
      intro v _hv
      exact hk.trans (G.minDegree_le_degree v)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A maximum cut preserves at least half of every individual vertex degree.
This local version is what lets the minimum-degree proof avoid a separate
dense-component averaging argument. -/
lemma exists_bipartite_subgraph_twice_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : k ≤ G.minDegree) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧ H.IsBipartite ∧ ∀ v, k ≤ 2 * H.degree v := by
  classical
  obtain ⟨c, hc⟩ := Erdos182.PRSEntry.exists_cutGraph_forall_degree G
  let H := Erdos182.PRSEntry.cutGraph G c
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, inferInstance, Erdos182.PRSEntry.cutGraph_le G c,
    (Erdos182.PRSEntry.cutGraph_isBipartiteWith G c).isBipartite, ?_⟩
  intro v
  have hGdeg : k ≤ Erdos182.PRSEntry.degreeNumber G v := by
    rw [Erdos182.PRSEntry.degreeNumber_eq_degree]
    exact hk.trans (G.minDegree_le_degree v)
  have hcut := hGdeg.trans (hc v)
  rw [Erdos182.PRSEntry.degreeNumber_eq_degree] at hcut
  exact hcut

/-- The explicit theorem implies the usual `≫_s k^s` formulation. -/
theorem minimumDegreeResolution_of_explicit
    (h : ExplicitMinimumDegreeResolution.{u}) : MinimumDegreeResolution.{u} := by
  intro s hs
  refine ⟨12 * 192 ^ s, by positivity, 576, ?_⟩
  intro k hk V _ _ G _ hmin hgirth
  exact h s hs k hk V G hmin hgirth

/-- The explicit scaling `D = 3 * (k / 288)` turns the graph-theoretic kernel
into the stated numerical resolution. -/
theorem explicitMinimumDegreeResolution_of_kernel
    (h : DistinctLengthKernel.{u}) : ExplicitMinimumDegreeResolution.{u} := by
  intro s hs k hk V _ _ G _ hmin hgirth
  let q := k / 288
  let D := 3 * q
  have hq : 2 ≤ q := by
    dsimp [q]
    omega
  have hD : 6 ≤ D := by
    dsimp [D]
    omega
  have hthree : 3 ∣ D := by
    exact ⟨q, rfl⟩
  have hthreshold : 48 * (D + 1) ≤ k := by
    dsimp [D, q]
    omega
  have hkD : k ≤ 192 * D := by
    dsimp [D, q]
    omega
  obtain ⟨L, hDL, hcycles⟩ :=
    h D hD hthree s hs V G (hthreshold.trans hmin) hgirth
  refine ⟨L, ?_, hcycles⟩
  calc
    k ^ s ≤ (192 * D) ^ s := by gcongr
    _ = 192 ^ s * D ^ s := by rw [Nat.mul_pow]
    _ ≤ 192 ^ s * (12 * L.card) := Nat.mul_le_mul_left _ hDL
    _ = (12 * 192 ^ s) * L.card := by ring

/-- The quantitative form of the Sudakov--Verstraëte resolution, with the
constants made explicit. -/
theorem explicitMinimumDegreeResolution : ExplicitMinimumDegreeResolution.{u} := by
  apply explicitMinimumDegreeResolution_of_kernel
  intro D hD hthree s hs V _ _ G _ hmin hgirth
  obtain ⟨L, hL, hcycles⟩ :=
    distinctLengthKernel D hD hthree s hs V G hmin hgirth
  refine ⟨L, hL, ?_⟩
  intro l hl
  simpa only [KernelHasCycleLength, HasCycleLength] using hcycles l hl

/-- Erdős Problem 752: a finite graph of minimum degree `k` and girth
greater than `2 * s` has `≫_s k ^ s` distinct cycle lengths. -/
theorem erdos_752 : (∀ (s : ℕ), 1 ≤ s →
  ∃ C : ℕ, 0 < C ∧ ∃ k₀ : ℕ,
    ∀ (k : ℕ), k₀ ≤ k →
      ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        k ≤ G.minDegree →
        Erdos752.GirthGreaterThan G (2 * s) →
        ∃ L : Finset ℕ,
          k ^ s ≤ C * L.card ∧ ∀ l ∈ L, Erdos752.HasCycleLength G l) :=
  minimumDegreeResolution_of_explicit explicitMinimumDegreeResolution

#print axioms distinctLengthKernel
#print axioms erdos_752

end Erdos752
