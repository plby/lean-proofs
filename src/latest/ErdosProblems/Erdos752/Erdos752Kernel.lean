/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos752.Erdos752Moore
import ErdosProblems.Erdos752.Erdos752Posa
import ErdosProblems.Erdos752.Erdos752BFS
import ErdosProblems.Erdos752.Erdos752Component
import ErdosProblems.Erdos752.Erdos752Assembly

/-!
# Kernel reductions for Erdős Problem 752

This file assembles the reductions in the distinct-cycle-length proof.  The
breadth-first-tree path-closing lemma is first isolated as
`PathAssemblyPrinciple`, proved from `Erdos752Assembly`, and then fed into the
cut, component, dense-slice, core, expansion, and DFS chain.
-/

open Finset
open SimpleGraph

namespace Erdos752

universe u

/-- The raw cycle-length witness used by the kernel, stated independently of
the public wrapper in `Erdos752.lean`. -/
def KernelHasCycleLength {V : Type u} (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = l

/-- The sole remaining geometric input: a long path contained in a subgraph
of two consecutive BFS layers yields at least one distinct cycle length per
eight path edges.  The cycles are returned in the connected BFS ambient graph.

The concrete BFS-tree construction proves this proposition; keeping it as a
named proposition makes the reduction chain independently type-checkable. -/
def PathAssemblyPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [Nonempty W]
      (F : SimpleGraph W) [DecidableRel F.Adj],
    F.Connected → F.IsBipartite →
    ∀ (root : W) (i : ℕ) (K : SimpleGraph W) [DecidableRel K.Adj],
      K ≤ bfsPair F root i → K.support.Nonempty →
      ∀ (a b : K.support) (p : (K.induce K.support).Walk a b),
        p.IsPath → 4 ≤ p.length →
        ∃ L : Finset ℕ, p.length ≤ 8 * L.card ∧
          ∀ l ∈ L, KernelHasCycleLength F l

/-- The BFS-tree path-closing theorem proves the isolated assembly
principle. -/
theorem pathAssemblyPrinciple : PathAssemblyPrinciple.{u} := by
  intro W _ _ F _ hconn _hbip root i K _ hKB _hKsupport a b p hp hlen
  obtain ⟨L, hL, hcycles⟩ :=
    exists_cycle_lengths_of_induce_support_path F hconn root i hKB p hp hlen
  refine ⟨L, hL, ?_⟩
  intro l hl
  exact hcycles l hl

/-- A maximum cut preserves at least half of every individual vertex degree. -/
private lemma exists_bipartite_subgraph_twice_degree
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : k ≤ G.minDegree) :
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

/-- All cut, component, dense-slice, core, expansion, DFS, and mapping
reductions in the distinct-length kernel. -/
theorem distinctLengthKernel_of_pathAssembly
    (hassemble : PathAssemblyPrinciple.{u})
    (D : ℕ) (hD : 6 ≤ D) (hthree : 3 ∣ D)
    (s : ℕ) (hs : 1 ≤ s)
    (V : Type u) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 48 * (D + 1) ≤ G.minDegree)
    (hgirth : GirthGreaterThan G (2 * s)) :
    ∃ L : Finset ℕ,
      D ^ s ≤ 12 * L.card ∧ ∀ l ∈ L, KernelHasCycleLength G l := by
  classical
  obtain ⟨H, instH, hHG, hHbip, hHdegree⟩ :=
    exists_bipartite_subgraph_twice_degree G hmin
  let : DecidableRel H.Adj := instH
  have hthreshold : 0 < 48 * (D + 1) := by positivity
  obtain ⟨c, instC, hconn, hbip, hCdegree, _hcEmb, hcG⟩ :=
    exists_connected_bipartite_component_of_le H hthreshold hHG hHbip hHdegree
  let : Nonempty c := c.nonempty_supp.to_subtype
  let F : SimpleGraph c := c.toSimpleGraph
  let : DecidableRel F.Adj := instC
  have hFconn : F.Connected := hconn
  have hFbip : F.IsBipartite := hbip
  have hFdegree : ∀ v : c, 2 * (12 * (D + 1)) ≤ F.degree v := by
    intro v
    have := hCdegree v
    dsimp [F]
    omega
  let root : c := Classical.choice inferInstance
  obtain ⟨i, hpairE, hpairDense⟩ :=
    exists_dense_bfs_pair hFconn hFbip
      (12 * (D + 1)) (by positivity) hFdegree root
  let B : SimpleGraph c := bfsPair F root i
  let : DecidableRel B.Adj := inferInstance
  obtain ⟨K, instK, hKsupport, hKB, _hEdges, hKmin⟩ :=
    Erdos182.exists_induced_minDegree_core B (12 * (D + 1)) hpairE hpairDense
  let : DecidableRel K.Adj := instK
  let J : SimpleGraph K.support := K.induce K.support
  let : Nonempty K.support := hKsupport.to_subtype
  let : DecidableRel J.Adj := inferInstance
  have hJmin : 6 * (D + 1) ≤ J.minDegree := by
    dsimp [J] at hKmin ⊢
    omega
  have hBF : B ≤ F := SimpleGraph.between_le
  let fJK : J →g K :=
    (SimpleGraph.Embedding.induce (G := K) K.support).toHom
  let fKB : K →g B := SimpleGraph.Hom.ofLE hKB
  let fBF : B →g F := SimpleGraph.Hom.ofLE hBF
  let fJF : J →g F := fBF.comp (fKB.comp fJK)
  have hfJF : Function.Injective fJF := by
    intro x y hxy
    exact Subtype.ext hxy
  have hFgirth : GirthGreaterThan F (2 * s) := by
    exact hgirth.of_injective_hom (componentHomToSupergraph H hHG c) hcG
  have hJgirth : GirthGreaterThan J (2 * s) :=
    hFgirth.of_injective_hom fJF hfJF
  let m := D ^ s / 3
  have hdivPow : 3 ∣ D ^ s := dvd_pow hthree (by omega)
  have hthree_m : 3 * m = D ^ s := by
    exact Nat.mul_div_cancel' hdivPow
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    have hpowzero : D ^ s = 0 := by omega
    exact (Nat.ne_of_gt (pow_pos (by omega : 0 < D) s)) hpowzero
  have hDlePow : D ≤ D ^ s := Nat.le_pow (by omega)
  have hmTwo : 2 ≤ m := by omega
  have hMoore : D ^ s ≤ Fintype.card K.support := by
    apply moore_bound (G := J)
    · have : D + 1 ≤ J.minDegree := by omega
      exact this
    · exact hJgirth
  have hmcard : m ≤ Fintype.card K.support := by omega
  have hexpand : ∀ X : Finset K.support, X.card = m →
      2 * m < (externalBoundary J X).card := by
    intro X hXm
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    have hXsmall : 3 * X.card ≤ D ^ s := by omega
    have hx := small_set_expansion (G := J) (d := D) (r := s)
      (by omega : 0 < s) hJmin hJgirth hXne hXsmall
    simpa only [hXm] using hx
  obtain ⟨a, b, p, hp, hplen⟩ :=
    exists_long_path_of_externalBoundary J m hmcard hexpand
  have hpFour : 4 ≤ p.length := by omega
  obtain ⟨L, hpL, hLcycles⟩ :=
    hassemble c F hFconn hFbip root i K hKB hKsupport a b p hp hpFour
  refine ⟨L, ?_, ?_⟩
  · omega
  · intro l hl
    exact exists_isCycle_length_of_component_of_le H hHG c (hLcycles l hl)

/-- The unconditional graph-theoretic kernel used in the resolution of
Erdős Problem 752. -/
theorem distinctLengthKernel
    (D : ℕ) (hD : 6 ≤ D) (hthree : 3 ∣ D)
    (s : ℕ) (hs : 1 ≤ s)
    (V : Type u) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 48 * (D + 1) ≤ G.minDegree)
    (hgirth : GirthGreaterThan G (2 * s)) :
    ∃ L : Finset ℕ,
      D ^ s ≤ 12 * L.card ∧ ∀ l ∈ L, KernelHasCycleLength G l := by
  exact distinctLengthKernel_of_pathAssembly pathAssemblyPrinciple
    D hD hthree s hs V G hmin hgirth

end Erdos752
