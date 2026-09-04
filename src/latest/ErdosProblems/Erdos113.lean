/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 113.
https://www.erdosproblems.com/forum/thread/113

Informal authors:
- Oliver Janzer

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos113.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Erdos113.Encode
import ErdosProblems.Erdos113.Moments
import ErdosProblems.Erdos113.ConflictSides
import ErdosProblems.Erdos113.MomentsBipartite
import ErdosProblems.Erdos113.CellPruning
import ErdosProblems.Erdos113.Paths
import ErdosProblems.Erdos113.Cycles
import ErdosProblems.Erdos113.Cycle56
import ErdosProblems.Erdos113.Encode56
import ErdosProblems.Erdos113.EncodeConsecutive56
import ErdosProblems.Erdos113.FourCycles
import ErdosProblems.Erdos113.Moments56
import ErdosProblems.Erdos113.CyclePruning
import ErdosProblems.Erdos113.ConflictSides56
import ErdosProblems.Erdos113.ConflictSidesConsecutive56
import ErdosProblems.Erdos113.Supersaturation28
import ErdosProblems.Erdos113.Incidence
import ErdosProblems.Erdos113.SelectedLift
import ErdosProblems.Erdos113.HostPruning
import ErdosProblems.Erdos113.AlmostRegular
import ErdosProblems.Erdos113.HostAsymptotics

/-!
# Erdős Problem 113

The mathematical proof and its correspondence with this development are
documented in `tex/113.tex`.
-/

open Filter
open scoped Asymptotics Real SimpleGraph

namespace Erdos113

/-- Every nonempty induced subgraph has a vertex of degree at most two. -/
def IsTwoDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty →
    ∃ v : S, (G.neighborSet v ∩ S).ncard ≤ 2

/-- The extremal number of `H` is `O(n^(3/2))`. -/
def HasThreeHalvesExtremalBound {V : Type*} (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2))

/-- A real-exponent version of the extremal bound, used to keep the
asymptotic bookkeeping separate from the combinatorial embedding theorem. -/
def HasExtremalBound {V : Type*} (a : ℝ) (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ a)

lemma hasExtremalBound_of_eventually_le {V : Type*} {H : SimpleGraph V} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ a) :
    HasExtremalBound a H := by
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [h] with n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  exact hn

lemma rpow_thirtyOne_div_twentyOne_isBigO_three_div_two :
    (fun n : ℕ ↦ (n : ℝ) ^ ((31 : ℝ) / 21)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  apply Asymptotics.IsBigO.of_bound' 
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn0 _),
    abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · norm_num

lemma hasThreeHalvesExtremalBound_of_thirtyOne_div_twentyOne {V : Type*}
    {H : SimpleGraph V} (h : HasExtremalBound ((31 : ℝ) / 21) H) :
    HasThreeHalvesExtremalBound H :=
  h.trans rpow_thirtyOne_div_twentyOne_isBigO_three_div_two

/-! ## A finite pruning engine

This is the deletion argument used in Janzer's good-to-nice cycle-family
lemma.  The conclusion packages a terminal subfamily, the bound on the total
number of deleted members, and the lower bound in every surviving fiber. -/

theorem exists_pruned_subfamily {α : Type*} [DecidableEq α] (t : ℕ)
    (C : Finset α) (fibers : Finset (Finset α)) :
    ∃ D : Finset α,
      D ⊆ C ∧
      C.card ≤ D.card + fibers.card * (t - 1) ∧
      ∀ F ∈ fibers, (D ∩ F).Nonempty → t ≤ (D ∩ F).card := by
  induction hn : fibers.card using Nat.strong_induction_on generalizing C fibers with
  | h n ih =>
      by_cases hsmall : ∃ F ∈ fibers, (C ∩ F).Nonempty ∧ (C ∩ F).card < t
      · obtain ⟨F, hFmem, _hFnonempty, hFsmall⟩ := hsmall
        have herase_lt : (fibers.erase F).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hFmem
        obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
          ih (fibers.erase F).card herase_lt (C \ F) (fibers.erase F) rfl
        refine ⟨D, hDsub.trans Finset.sdiff_subset, ?_, ?_⟩
        · have hsplit := Finset.card_sdiff_add_card_inter C F
          have herase := Finset.card_erase_add_one hFmem
          have hFbound : (C ∩ F).card ≤ t - 1 := Nat.le_sub_one_of_lt hFsmall
          calc
            C.card = (C \ F).card + (C ∩ F).card := hsplit.symm
            _ ≤ (D.card + (fibers.erase F).card * (t - 1)) + (t - 1) :=
              Nat.add_le_add hDcard hFbound
            _ = D.card + fibers.card * (t - 1) := by
              rw [← herase, Nat.add_mul, one_mul]
              omega
            _ = D.card + n * (t - 1) := by rw [← hn]
        · intro F' hF'mem hnonempty
          by_cases hF'eq : F' = F
          · subst F'
            have hempty : D ∩ F = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro x hx
              have hxD := hDsub (Finset.mem_inter.mp hx).1
              exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hx).2
            exact (by simpa [hempty] using hnonempty)
          · exact hDstab F' (Finset.mem_erase.mpr ⟨hF'eq, hF'mem⟩) hnonempty
      · refine ⟨C, Finset.Subset.rfl, by omega, ?_⟩
        intro F hFmem hnonempty
        exact le_of_not_gt fun hlt ↦ hsmall ⟨F, hFmem, hnonempty, hlt⟩

/-! ### Ordered 56-cycles and Janzer's good/nice conditions

The chosen value `k = 7` makes the cycle length `8k = 56`.  Restrictions to
all coordinates except one, or except a cyclic adjacent pair, give a
literal finite model of the fibers in Definitions 2.11 and 2.12 of Janzer's
paper. -/

abbrev CycleTuple (V : Type*) := Fin 56 → V

def IsGenuineCycleTuple {V : Type*} (G : SimpleGraph V) (x : CycleTuple V) : Prop :=
  Function.Injective x ∧ ∀ i, G.Adj (x i) (x (i + 1))

abbrev OffSingle (i : Fin 56) := {j : Fin 56 // j ≠ i}

abbrev OffPair (i : Fin 56) := {j : Fin 56 // j ≠ i ∧ j ≠ i + 1}

def restrictOffSingle {V : Type*} (i : Fin 56) (x : CycleTuple V) :
    OffSingle i → V := fun j ↦ x j

def restrictOffPair {V : Type*} (i : Fin 56) (x : CycleTuple V) :
    OffPair i → V := fun j ↦ x j

def singleFiber {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) (r : OffSingle i → V) : Finset (CycleTuple V) :=
  C.filter fun x ↦ restrictOffSingle i x = r

def pairFiber {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) (r : OffPair i → V) : Finset (CycleTuple V) :=
  C.filter fun x ↦ restrictOffPair i x = r

def pairPatterns {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (CycleTuple V))
    (i : Fin 56) : Finset (OffPair i → V) :=
  C.image (restrictOffPair i)

/-! The `54` retained coordinates of an adjacent-pair pattern occur in one
consecutive path.  This explicit cyclic ordering makes the standard
`|V| Δ^53` pattern bound a direct application of finite walk counting. -/

def shiftTwo56 (t : Fin 54) : Fin 56 := ⟨t.val + 2, by omega⟩

def offPairOrder (i : Fin 56) (t : Fin 54) : OffPair i :=
  ⟨i + shiftTwo56 t, by decide +revert, by decide +revert⟩

lemma offPairOrder_bijective (i : Fin 56) : Function.Bijective (offPairOrder i) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b hab
    have hab' : i + shiftTwo56 a = i + shiftTwo56 b :=
      congrArg Subtype.val hab
    have hs : shiftTwo56 a = shiftTwo56 b := add_left_cancel hab'
    apply Fin.ext
    have hv := congrArg Fin.val hs
    simpa [shiftTwo56] using hv
  · have hcard : Fintype.card (OffPair i) = 54 := by
      decide +revert
    simp [hcard]

lemma shiftTwo56_castSucc_add_one (t : Fin 53) :
    shiftTwo56 t.castSucc + 1 = shiftTwo56 t.succ := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [shiftTwo56]
  · simp [shiftTwo56]
    omega

def pairPatternPath {V : Type*} (i : Fin 56) (r : OffPair i → V) : Fin 54 → V :=
  fun t ↦ r (offPairOrder i t)

lemma pairPatternPath_injective {V : Type*} (i : Fin 56) :
    Function.Injective (pairPatternPath (V := V) i) := by
  intro r s hrs
  funext j
  obtain ⟨t, rfl⟩ := (offPairOrder_bijective i).2 j
  exact congrFun hrs t

noncomputable def pairPatternToPathTuple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    ↑(pairPatterns C i) → Erdos113Paths.PathTuple G 53 := fun r ↦ by
  refine ⟨pairPatternPath i r.1, ?_⟩
  obtain ⟨x, hxC, hxr⟩ := Finset.mem_image.mp r.2
  intro t
  have hadj := (hgen x hxC).2 (i + shiftTwo56 t.castSucc)
  change G.Adj
    (r.1 (offPairOrder i t.castSucc))
    (r.1 (offPairOrder i t.succ))
  rw [← hxr]
  simpa [restrictOffPair, offPairOrder, add_assoc,
    shiftTwo56_castSucc_add_one] using hadj

lemma pairPatternToPathTuple_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    Function.Injective (pairPatternToPathTuple G C hgen i) := by
  intro r s hrs
  apply Subtype.ext
  apply pairPatternPath_injective i
  exact congrArg Subtype.val hrs

lemma pairPatterns_card_cast_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ D) (i : Fin 56) :
    ((pairPatterns C i).card : ℝ) ≤ Fintype.card V * D ^ 53 := by
  classical
  have hcard : Fintype.card ↑(pairPatterns C i) ≤
      Fintype.card (Erdos113Paths.PathTuple G 53) :=
    Fintype.card_le_of_injective (pairPatternToPathTuple G C hgen i)
      (pairPatternToPathTuple_injective G C hgen i)
  calc
    ((pairPatterns C i).card : ℝ) = Fintype.card ↑(pairPatterns C i) := by simp
    _ ≤ Fintype.card (Erdos113Paths.PathTuple G 53) := by exact_mod_cast hcard
    _ ≤ Fintype.card V * D ^ 53 :=
      Erdos113Paths.card_pathTuple_cast_le G D hD hdeg 53

lemma pairPatterns_card_cast_le_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    ((pairPatterns C i).card : ℝ) ≤
      Fintype.card V *
        (D false ^ 27 * D true ^ 26 +
          D true ^ 27 * D false ^ 26) := by
  classical
  have hcard : Fintype.card ↑(pairPatterns C i) ≤
      Fintype.card (Erdos113Paths.PathTuple G 53) :=
    Fintype.card_le_of_injective (pairPatternToPathTuple G C hgen i)
      (pairPatternToPathTuple_injective G C hgen i)
  calc
    ((pairPatterns C i).card : ℝ) = Fintype.card ↑(pairPatterns C i) := by simp
    _ ≤ Fintype.card (Erdos113Paths.PathTuple G 53) := by exact_mod_cast hcard
    _ ≤ Fintype.card V *
        (D false ^ 27 * D true ^ 26 +
          D true ^ 27 * D false ^ 26) :=
      Erdos113Paths.card_pathTuple_53_cast_le_bipartite
        G side D hD hcross hdeg

lemma pairPatterns_card_cast_le_bipartite_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (C : Finset (CycleTuple V))
    (hgen : ∀ x ∈ C, IsGenuineCycleTuple G x) (i : Fin 56) :
    ((pairPatterns C i).card : ℝ) ≤
      2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
  classical
  have hcard : Fintype.card ↑(pairPatterns C i) ≤
      Fintype.card (Erdos113Paths.PathTuple G 53) :=
    Fintype.card_le_of_injective (pairPatternToPathTuple G C hgen i)
      (pairPatternToPathTuple_injective G C hgen i)
  calc
    ((pairPatterns C i).card : ℝ) = Fintype.card ↑(pairPatterns C i) := by simp
    _ ≤ Fintype.card (Erdos113Paths.PathTuple G 53) := by exact_mod_cast hcard
    _ ≤ 2 * G.edgeFinset.card * (D false * D true) ^ 26 :=
      Erdos113Paths.card_pathTuple_53_cast_le_bipartite_edges
        G side D hD hcross hdeg

def commonNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

def codegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (commonNeighborFinset G u v).card

@[simp] lemma mem_commonNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} :
    w ∈ commonNeighborFinset G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNeighborFinset, SimpleGraph.mem_neighborFinset]

def HasControlledTwoStepCodegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (x : CycleTuple V) : Prop :=
  ∀ i, codegree G (x i) (x (i + 2)) ≤ s

noncomputable def controlledGenuineCycles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) : Finset (CycleTuple V) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      IsGenuineCycleTuple G x ∧ HasControlledTwoStepCodegrees G s x

@[simp] lemma mem_controlledGenuineCycles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} {x : CycleTuple V} :
    x ∈ controlledGenuineCycles G s ↔
      IsGenuineCycleTuple G x ∧ HasControlledTwoStepCodegrees G s x := by
  classical
  simp [controlledGenuineCycles]

lemma fin56_sub_one_add_one (i : Fin 56) : i - 1 + 1 = i := by
  decide +revert

lemma fin56_sub_one_ne (i : Fin 56) : i - 1 ≠ i := by
  decide +revert

lemma fin56_add_one_ne_self (i : Fin 56) : i + 1 ≠ i := by
  decide +revert

lemma fin56_sub_one_add_two (i : Fin 56) : i - 1 + 2 = i + 1 := by
  decide +revert

lemma singleFiber_card_le_of_controlled {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (i : Fin 56)
    (r : OffSingle i → V) :
    (singleFiber (controlledGenuineCycles G s) i r).card ≤ s := by
  classical
  let F := singleFiber (controlledGenuineCycles G s) i r
  by_cases hF : F.Nonempty
  · let x₀ : CycleTuple V := hF.choose
    have hx₀F : x₀ ∈ F := hF.choose_spec
    have hx₀data := Finset.mem_filter.mp hx₀F
    have hx₀control := (mem_controlledGenuineCycles.mp hx₀data.1).2 (i - 1)
    let f : ↑F → ↑(commonNeighborFinset G (x₀ (i - 1)) (x₀ (i + 1))) :=
      fun x ↦ ⟨x.1 i, by
        rw [mem_commonNeighborFinset]
        have hxdata := Finset.mem_filter.mp x.2
        have hxgen := (mem_controlledGenuineCycles.mp hxdata.1).1
        have hrest : restrictOffSingle i x.1 = restrictOffSingle i x₀ :=
          hxdata.2.trans hx₀data.2.symm
        have hprev : x.1 (i - 1) = x₀ (i - 1) :=
          congrFun hrest ⟨i - 1, fin56_sub_one_ne i⟩
        have hnext : x.1 (i + 1) = x₀ (i + 1) :=
          congrFun hrest ⟨i + 1, fin56_add_one_ne_self i⟩
        constructor
        · simpa [hprev, fin56_sub_one_add_one] using hxgen.2 (i - 1)
        · simpa [hnext] using (hxgen.2 i).symm⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        exact congrArg Subtype.val hxy
      · have hxdata := Finset.mem_filter.mp x.2
        have hydata := Finset.mem_filter.mp y.2
        exact (congrFun hxdata.2 ⟨j, hji⟩).trans
          (congrFun hydata.2 ⟨j, hji⟩).symm
    have hcard : F.card ≤
        (commonNeighborFinset G (x₀ (i - 1)) (x₀ (i + 1))).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    exact hcard.trans (by
      simpa [codegree, fin56_sub_one_add_two] using hx₀control)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    simp [F, hF]

/-- Janzer's `β`-good condition, specialized to `k = 7`.  The third field is
the denominator-free form of
`patterns ≤ β |C| / (16 k s)`. -/
structure IsGoodCycleFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (β : ℝ) (C : Finset (CycleTuple V)) : Type where
  s : ℕ
  s_pos : 0 < s
  genuine : ∀ x ∈ C, IsGenuineCycleTuple G x
  single_card : ∀ (i : Fin 56) (r : OffSingle i → V),
    (singleFiber C i r).card ≤ s
  pattern_card : ∀ i : Fin 56,
    (16 * 7 * s : ℝ) * (pairPatterns C i).card ≤ β * C.card

noncomputable def controlledGenuineCycles_isGood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (hs : 0 < s)
    (β D L : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ D)
    (hcard : L ≤ ((controlledGenuineCycles G s).card : ℝ))
    (hnumeric : (16 * 7 * s : ℝ) * (Fintype.card V * D ^ 53) ≤ β * L) :
    IsGoodCycleFamily G β (controlledGenuineCycles G s) := by
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_controlledGenuineCycles.mp hx).1
  · exact singleFiber_card_le_of_controlled G s
  · intro i
    calc
      (16 * 7 * s : ℝ) * (pairPatterns (controlledGenuineCycles G s) i).card ≤
          (16 * 7 * s : ℝ) * (Fintype.card V * D ^ 53) := by
        gcongr
        exact pairPatterns_card_cast_le G (controlledGenuineCycles G s)
          (fun x hx ↦ (mem_controlledGenuineCycles.mp hx).1) D hD hdeg i
      _ ≤ β * L := hnumeric
      _ ≤ β * (controlledGenuineCycles G s).card :=
        mul_le_mul_of_nonneg_left hcard hβ

noncomputable def controlledGenuineCycles_isGood_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (s : ℕ) (hs : 0 < s) (β L₀ : ℝ) (hβ : 0 ≤ β)
    (hcard : L₀ ≤ ((controlledGenuineCycles G s).card : ℝ))
    (hnumeric : (16 * 7 * s : ℝ) *
        (Fintype.card V *
          (D false ^ 27 * D true ^ 26 +
            D true ^ 27 * D false ^ 26)) ≤ β * L₀) :
    IsGoodCycleFamily G β (controlledGenuineCycles G s) := by
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_controlledGenuineCycles.mp hx).1
  · exact singleFiber_card_le_of_controlled G s
  · intro i
    calc
      (16 * 7 * s : ℝ) *
          (pairPatterns (controlledGenuineCycles G s) i).card ≤
          (16 * 7 * s : ℝ) *
            (Fintype.card V *
              (D false ^ 27 * D true ^ 26 +
                D true ^ 27 * D false ^ 26)) := by
        gcongr
        exact pairPatterns_card_cast_le_bipartite
          G side D hD hcross hdeg (controlledGenuineCycles G s)
            (fun x hx ↦ (mem_controlledGenuineCycles.mp hx).1) i
      _ ≤ β * L₀ := hnumeric
      _ ≤ β * (controlledGenuineCycles G s).card :=
        mul_le_mul_of_nonneg_left hcard hβ

noncomputable def controlledGenuineCycles_isGood_bipartite_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (s : ℕ) (hs : 0 < s) (β L₀ : ℝ) (hβ : 0 ≤ β)
    (hcard : L₀ ≤ ((controlledGenuineCycles G s).card : ℝ))
    (hnumeric : (16 * 7 * s : ℝ) *
        (2 * G.edgeFinset.card * (D false * D true) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β (controlledGenuineCycles G s) := by
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_controlledGenuineCycles.mp hx).1
  · exact singleFiber_card_le_of_controlled G s
  · intro i
    calc
      (16 * 7 * s : ℝ) *
          (pairPatterns (controlledGenuineCycles G s) i).card ≤
          (16 * 7 * s : ℝ) *
            (2 * G.edgeFinset.card * (D false * D true) ^ 26) := by
        gcongr
        exact pairPatterns_card_cast_le_bipartite_edges
          G side D hD hcross hdeg (controlledGenuineCycles G s)
            (fun x hx ↦ (mem_controlledGenuineCycles.mp hx).1) i
      _ ≤ β * L₀ := hnumeric
      _ ≤ β * (controlledGenuineCycles G s).card :=
        mul_le_mul_of_nonneg_left hcard hβ

/-- The abstract many-four-cycle package.  Once the dyadic extraction gives
an auxiliary lift system and its two incidence-degree caps, the checked
supersaturation/lifting count and the edge-refined path estimate supply all
three fields of Janzer's good-family definition. -/
noncomputable def liftedCycles_isGood
    {T V : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V]
    (F : SimpleGraph T) (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Erdos113ManyLifts.LiftSystem F G)
    (cap : ℕ) (hcap : 0 < cap)
    (hmiddle : 2 * L.lower ≤ cap)
    (hbridge : ∀ u w, Erdos113ManyLifts.IsMiddleVertex L u →
      (Erdos113ManyLifts.bridgeAnchors L u w).card ≤ cap)
    (A B : ℕ)
    (hleft : ∀ t, (Erdos113Incidence.leftPartners L t).card ≤ A)
    (hright : ∀ y, (Erdos113Incidence.rightPartners L y).card ≤ B)
    (β L₀ : ℝ) (hβ : 0 ≤ β)
    (hcard : L₀ ≤ ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ))
    (hnumeric : (16 * 7 * cap : ℝ) *
        (2 * (Fintype.card T * A) * (B * A) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β (Erdos113ManyLifts.liftedCycles F G L) := by
  let I := Erdos113Incidence.incidenceGraph L
  let side := Erdos113Incidence.incidenceSide L
  let D : Bool → ℝ := fun b ↦ if b then A else B
  have hD : ∀ b, 0 ≤ D b := by intro b; positivity
  have hdeg : ∀ v, (I.degree v : ℝ) ≤ D (side v) := by
    intro v
    dsimp [I, D, side]
    exact_mod_cast Erdos113Incidence.incidenceGraph_degree_le L A B hleft hright v
  have hedge : (I.edgeFinset.card : ℝ) ≤ Fintype.card T * A := by
    exact_mod_cast Erdos113Incidence.incidenceGraph_edge_card_le L A hleft
  refine ⟨cap, hcap, ?_, ?_, ?_⟩
  · intro z hz
    exact Erdos113ManyLifts.liftedCycles_genuine L hz
  · intro i r
    change (Erdos113ManyLifts.singleFiber56
      (Erdos113ManyLifts.liftedCycles F G L) i r).card ≤ cap
    exact Erdos113ManyLifts.singleFiber56_liftedCycles_card_le
      L cap hmiddle hbridge i r
  · intro i
    norm_num [Nat.cast_mul] at hnumeric ⊢
    have hpattern : ((pairPatterns
        (Erdos113ManyLifts.liftedCycles F G L) i).card : ℝ) ≤
        2 * (Fintype.card T * A) * (B * A) ^ 26 := by
      calc
        ((pairPatterns (Erdos113ManyLifts.liftedCycles F G L) i).card : ℝ) ≤
            2 * I.edgeFinset.card * (D false * D true) ^ 26 :=
          pairPatterns_card_cast_le_bipartite_edges I side D hD
            (fun {_ _} h ↦ Erdos113Incidence.incidenceGraph_cross L h)
            hdeg (Erdos113ManyLifts.liftedCycles F G L) (fun z hz ↦
              Erdos113Incidence.liftedCycles_genuine_incidence L hz) i
        _ ≤ 2 * (Fintype.card T * A) * (B * A) ^ 26 := by
          dsimp [D]
          gcongr
    calc
      (112 * cap : ℝ) *
          (pairPatterns (Erdos113ManyLifts.liftedCycles F G L) i).card ≤
          (112 * cap : ℝ) *
            (2 * (Fintype.card T * A) * (B * A) ^ 26) := by
        gcongr
      _ ≤ β * L₀ := hnumeric
      _ ≤ β * (Erdos113ManyLifts.liftedCycles F G L).card :=
        mul_le_mul_of_nonneg_left hcard hβ

/-- The checked many-four-cycle construction, with all asymptotic
bookkeeping exposed as explicit numerical hypotheses. -/
noncomputable def manyFourCycleGoodFamily_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (S : Erdos113FourCycleSelection.FirstSelection G side)
    (R : S.SecondSelection)
    (Q : ℕ)
    (hcycle : ∀ t : Erdos113AnchorConstruction.NeighborVertex G S.anchor,
      (Erdos113Cycles.cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (hlift : 3136 * 2 ^ 27 ≤ 2 ^ R.index.val)
    (hsuper :
      702464 * (16 *
          (Erdos113Regular.degreeBinCount
            (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ)) *
          (2 * Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^
              ((1 : ℝ) / 14) ≤
        ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
          (32 *
            (Erdos113Regular.degreeBinCount
              (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
            Fintype.card
              (Erdos113AnchorConstruction.NeighborVertex G S.anchor)))
    (β : ℝ) (hβ : 0 ≤ β)
    (hnumeric :
      let A :=
        Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem
          S R hcross Q hcycle
      let δ := ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
        (32 *
          (Erdos113Regular.degreeBinCount
            (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
          Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor))
      let L₀ := (δ ^ 28 / (2 * (2 : ℝ) ^ 28)) *
        ((2 ^ R.index.val : ℕ) : ℝ) ^ 28 / 2
      (16 * 7 *
          (2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)) : ℝ) *
        (2 * (Fintype.card
            (Erdos113AnchorConstruction.NeighborVertex G S.anchor) * A.leftCap) *
          (A.rightCap * A.leftCap) ^ 26) ≤ β * L₀) :
    IsGoodCycleFamily G β
      (Erdos113ManyLifts.liftedCycles
        (S.auxiliaryGraph R.index) G
          (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
            S R hcross)) := by
  let F := S.auxiliaryGraph R.index
  let A :=
    Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem
      S R hcross Q hcycle
  let L := A.toLiftSystem
  let δ := (F.edgeFinset.card : ℝ) /
    (32 *
      (Erdos113Regular.degreeBinCount
        (W := Erdos113AnchorConstruction.NeighborVertex G S.anchor) : ℝ) ^ 3 *
      Fintype.card
        (Erdos113AnchorConstruction.NeighborVertex G S.anchor))
  let L₀ := (δ ^ 28 / (2 * (2 : ℝ) ^ 28)) *
    ((2 ^ R.index.val : ℕ) : ℝ) ^ 28 / 2
  have hFcycles : δ ^ 28 / (2 * (2 : ℝ) ^ 28) ≤
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact Erdos113Supersaturation28.genuineCycles28_lower_of_edgeDensity
      F R.auxiliary_edge (by simpa [F, δ] using hsuper)
  have hlower : 3136 * 2 ^ 27 ≤ L.lower := by
    change 3136 * 2 ^ 27 ≤ 2 ^ R.index.val
    exact hlift
  have hliftNat := Erdos113ManyLifts.liftedCycles_card_lower L hlower
  have hliftReal :
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) *
          (((2 ^ R.index.val : ℕ) : ℝ) ^ 28) ≤
        2 * ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ) := by
    exact_mod_cast hliftNat
  have hcard : L₀ ≤
      ((Erdos113ManyLifts.liftedCycles F G L).card : ℝ) := by
    have hpownonneg : 0 ≤ (((2 ^ R.index.val : ℕ) : ℝ) ^ 28) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hFcycles hpownonneg
    dsimp [L₀]
    nlinarith
  have hleft : ∀ t, (Erdos113Incidence.leftPartners L t).card ≤ A.leftCap :=
    A.left_cap
  have hright : ∀ y, (Erdos113Incidence.rightPartners L y).card ≤ A.rightCap :=
    Erdos113AnchoredLifts.rightPartners_card_le A
  refine liftedCycles_isGood F G L
    (2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)) (by positivity)
      ?_ ?_ A.leftCap A.rightCap hleft hright β L₀ hβ hcard ?_
  · dsimp [L, A]
    simp only [Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
      Erdos113AnchorConstruction.selectedAnchoredLiftSystem,
      Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem,
      Erdos113AnchorConstruction.selectedLiftSystem]
    change 2 * 2 ^ R.index.val ≤
      2 ^ (R.index.val + 1) + 2 ^ (S.scaleIndex.val + 1)
    simp only [pow_succ]
    omega
  · intro u w hu
    exact (Erdos113AnchoredLifts.bridgeAnchors_card_le A u w hu).trans (by
      dsimp [A]
      simp only [Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
        Erdos113AnchorConstruction.selectedAnchoredLiftSystem]
      omega)
  · simpa [A, L₀, δ, F] using hnumeric

/-! ### Removing the two kinds of bad homomorphic 56-cycles

The source proof first counts all homomorphic cycles, then removes cycles
with a repeated vertex and cycles having a high-codegree distance-two pair.
The two injective encodings below connect those tuple predicates to the
closed-walk estimates in `Encode56` and `EncodeConsecutive56`. -/

abbrev HomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :=
  {x : CycleTuple V // Erdos113Cycles.IsHomCycle G x}

abbrev RepeatedHomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :=
  {x : HomCycle56 G // ¬ Function.Injective x.1}

def HighCodegreeRelation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ s < codegree G u v

noncomputable instance instDecidableHighCodegreeRelation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    DecidableRel (HighCodegreeRelation G s) := Classical.decRel _

abbrev HighStepHomCycle56 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :=
  {x : HomCycle56 G // ∃ i,
    HighCodegreeRelation G s (x.1 i) (x.1 (i + 2))}

lemma fin56_ne_add_two (i : Fin 56) : i ≠ i + 2 := by
  decide +revert

noncomputable def homCyclePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    HomCycle56 G →
      ↑(controlledGenuineCycles G s) ⊕
        (RepeatedHomCycle56 G ⊕ HighStepHomCycle56 G s) := fun x ↦ by
  classical
  by_cases hinj : Function.Injective x.1
  · by_cases hcontrol : HasControlledTwoStepCodegrees G s x.1
    · exact Sum.inl ⟨x.1, mem_controlledGenuineCycles.mpr
        ⟨⟨hinj, x.2⟩, hcontrol⟩⟩
    · apply Sum.inr
      apply Sum.inr
      refine ⟨x, ?_⟩
      simp only [HasControlledTwoStepCodegrees, not_forall] at hcontrol
      obtain ⟨i, hi⟩ := hcontrol
      exact ⟨i, hinj.ne (fin56_ne_add_two i), Nat.lt_of_not_ge hi⟩
  · exact Sum.inr (Sum.inl ⟨x, hinj⟩)

def homCyclePartitionDecode {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} :
    ↑(controlledGenuineCycles G s) ⊕
        (RepeatedHomCycle56 G ⊕ HighStepHomCycle56 G s) →
      CycleTuple V
  | Sum.inl x => x.1
  | Sum.inr (Sum.inl x) => x.1.1
  | Sum.inr (Sum.inr x) => x.1.1

@[simp] lemma homCyclePartitionDecode_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (x : HomCycle56 G) :
    homCyclePartitionDecode (homCyclePartition G s x) = x.1 := by
  classical
  unfold homCyclePartition
  split
  · split <;> rfl
  · rfl

lemma homCyclePartition_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Function.Injective (homCyclePartition G s) := by
  intro x y hxy
  apply Subtype.ext
  have := congrArg homCyclePartitionDecode hxy
  simpa using this

noncomputable def repeatedHomCycleToBadClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RepeatedHomCycle56 G → Encode56.BadClosedWalk56 G (fun u v ↦ u = v) :=
  fun x ↦ by
    let P := Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp x.2
    refine ⟨i, j, hne, ?_⟩
    have hread := Erdos113Cycle56.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    exact (congrFun hread i).trans (hij.trans (congrFun hread j).symm)

lemma repeatedHomCycleToBadClosedWalk_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (repeatedHomCycleToBadClosedWalk G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode56.ClosedWalk56 G)) hxy
  change Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle56.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle56.closedWalkTuple G) hP
  simpa only [Erdos113Cycle56.closedWalkTuple_tupleClosedWalk] using hread

lemma cyclicAdd56_two (i : Fin 56) :
    EncodeConsecutive56.cyclicAdd56 i 2 = i + 2 := by
  apply Fin.ext
  simp only [EncodeConsecutive56.cyclicAdd56]
  omega

noncomputable def highStepHomCycleToBadClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    HighStepHomCycle56 G s →
      EncodeConsecutive56.BadClosedWalk56 G (HighCodegreeRelation G s) :=
  fun x ↦ by
    let P := Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, hi⟩ := x.2
    refine ⟨i, ?_⟩
    have hread := Erdos113Cycle56.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    have hread_i := congrFun hread i
    have hread_i2 := congrFun hread (i + 2)
    rw [← hread_i, ← hread_i2] at hi
    simpa [EncodeConsecutive56.cv, P,
      Erdos113Cycle56.closedWalkTuple, cyclicAdd56_two] using hi

lemma highStepHomCycleToBadClosedWalk_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Function.Injective (highStepHomCycleToBadClosedWalk G s) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg
    (fun z ↦ (z.1 : EncodeConsecutive56.ClosedWalk56 G)) hxy
  change Erdos113Cycle56.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle56.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle56.closedWalkTuple G) hP
  simpa only [Erdos113Cycle56.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle56_le_controlled_add_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Fintype.card (HomCycle56 G) ≤
      (controlledGenuineCycles G s).card +
        Fintype.card (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) +
        Fintype.card
          (EncodeConsecutive56.BadClosedWalk56 G (HighCodegreeRelation G s)) := by
  have hpartition := Fintype.card_le_of_injective (homCyclePartition G s)
    (homCyclePartition_injective G s)
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_coe] at hpartition
  have hrepeat := Fintype.card_le_of_injective
    (repeatedHomCycleToBadClosedWalk G)
    (repeatedHomCycleToBadClosedWalk_injective G)
  have hhigh := Fintype.card_le_of_injective
    (highStepHomCycleToBadClosedWalk G s)
    (highStepHomCycleToBadClosedWalk_injective G s)
  omega

lemma codegree_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    codegree G u v = codegree G v u := by
  simp [codegree, commonNeighborFinset, Finset.inter_comm]

lemma repeatedBadClosedWalk56_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t D : ℝ)
    (ht : 0 < t) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D) :
    (Fintype.card
      (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) : ℝ) ≤
      56 * (D * t * (Conflict56.closedWalkCount G 54 : ℝ) +
        28 * t⁻¹ * (Conflict56.closedWalkCount G 56 : ℝ)) := by
  have hlocal : ∀ u y,
      (((G.neighborFinset y).filter (fun v ↦ u = v)).card : ℝ) ≤ 1 := by
    intro u y
    have hsub : (G.neighborFinset y).filter (fun v ↦ u = v) ⊆ {u} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2.symm
    exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
  simpa only [mul_one, one_mul] using
    (Encode56.card_BadClosedWalk56_cast_le G (fun u v ↦ u = v)
      t D 1 ht (by norm_num) hdeg (fun _ _ h ↦ h.symm) hlocal)

lemma highCodegreeRelation_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    ∀ u v, HighCodegreeRelation G s u v →
      HighCodegreeRelation G s v u := by
  intro u v huv
  exact ⟨huv.1.symm, by simpa [codegree_comm G u v] using huv.2⟩

lemma highStepBadClosedWalk56_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (hs : 0 < s)
    (Q t D : ℝ) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤ Q) :
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
      (HighCodegreeRelation G s)) : ℝ) ≤
      56 * (D * t * (Consecutive56.closedWalkCount G 54 : ℝ) +
        (Q / s) * t⁻¹ * (Consecutive56.closedWalkCount G 56 : ℝ)) := by
  have hlocal : ∀ u y, G.Adj y u →
      (((G.neighborFinset y).filter (HighCodegreeRelation G s u)).card : ℝ) ≤
        Q / s := by
    intro u y huy
    have heq : (G.neighborFinset y).filter (HighCodegreeRelation G s u) =
        Erdos113FourCycles.highCodegreeNeighbors G s u y := by
      ext x
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        HighCodegreeRelation, Erdos113FourCycles.mem_highCodegreeNeighbors]
      rfl
    rw [heq]
    exact Erdos113FourCycles.card_highCodegreeNeighbors_cast_le
      G s hs huy Q (hcap u y huy)
  exact EncodeConsecutive56.card_BadClosedWalk56_cast_le G
    (HighCodegreeRelation G s) t D (Q / s) ht
    (div_nonneg hQ (by positivity)) hdeg
    (highCodegreeRelation_symmetric G s) hlocal

lemma repeatedBadClosedWalk56_side_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (t D : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) :
    (Fintype.card
      (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (Conflict56.closedWalkCount G 54 : ℝ) +
          28 * (t b)⁻¹ * (Conflict56.closedWalkCount G 56 : ℝ)) := by
  have hlocal : ∀ u y,
      (((G.neighborFinset y).filter (fun v ↦ u = v)).card : ℝ) ≤ 1 := by
    intro u y
    have hsub : (G.neighborFinset y).filter (fun v ↦ u = v) ⊆ {u} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2.symm
    exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
  simpa only [mul_one, one_mul] using
    (Erdos113Sides56.card_BadClosedWalk56_side_cast_le
      G (fun u v ↦ u = v) side t D (fun _ ↦ 1) ht hD
        (fun _ ↦ by norm_num) hcross hdeg (fun _ _ h ↦ h.symm) hlocal)

lemma highStepBadClosedWalk56_side_cast_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q t D : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (ht : ∀ b, 0 < t b)
    (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y)) :
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
      (HighCodegreeRelation G s)) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (Consecutive56.closedWalkCount G 54 : ℝ) +
          (Q (!b) / s) * (t b)⁻¹ *
            (Consecutive56.closedWalkCount G 56 : ℝ)) := by
  let S : Bool → ℝ := fun b ↦ Q b / s
  have hS : ∀ b, 0 ≤ S b := fun b ↦ div_nonneg (hQ b) (by positivity)
  have hlocal : ∀ u y, G.Adj y u →
      (((G.neighborFinset y).filter (HighCodegreeRelation G s u)).card : ℝ) ≤
        S (side y) := by
    intro u y huy
    have heq : (G.neighborFinset y).filter (HighCodegreeRelation G s u) =
        Erdos113FourCycles.highCodegreeNeighbors G s u y := by
      ext x
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        HighCodegreeRelation, Erdos113FourCycles.mem_highCodegreeNeighbors]
      rfl
    rw [heq]
    exact Erdos113FourCycles.card_highCodegreeNeighbors_cast_le
      G s hs huy (Q (side y)) (hcap u y huy)
  simpa [S] using
    (Erdos113SidesConsecutive56.card_BadClosedWalk56_side_cast_le
      G (HighCodegreeRelation G s) side t D S ht hD hS hcross hdeg
        (highCodegreeRelation_symmetric G s) hlocal)

lemma controlledGenuineCycles_card_lower_of_bad_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (B₀ B₂ : ℝ)
    (hB₀ : (Fintype.card
      (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) : ℝ) ≤ B₀)
    (hB₂ : (Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
      (HighCodegreeRelation G s)) : ℝ) ≤ B₂) :
    (Conflict.closedWalkCount G 56 : ℝ) - B₀ - B₂ ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hcardNat := card_homCycle56_le_controlled_add_bad G s
  have hcard : (Fintype.card (HomCycle56 G) : ℝ) ≤
      (controlledGenuineCycles G s).card +
        Fintype.card (Encode56.BadClosedWalk56 G (fun u v ↦ u = v)) +
        Fintype.card (EncodeConsecutive56.BadClosedWalk56 G
          (HighCodegreeRelation G s)) := by
    exact_mod_cast hcardNat
  have htotal : (Fintype.card (HomCycle56 G) : ℝ) =
      (Conflict.closedWalkCount G 56 : ℝ) := by
    exact_mod_cast Erdos113Cycle56.card_homCycle56_eq_closedWalkCount G
  rw [htotal] at hcard
  linarith

lemma controlledGenuineCycles_card_lower_of_degree_and_c4cap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 0 < s) (Q D t₀ t₂ : ℝ)
    (hQ : 0 ≤ Q) (ht₀ : 0 < t₀) (ht₂ : 0 < t₂)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤ Q) :
    (Conflict.closedWalkCount G 56 : ℝ) -
        56 * (D * t₀ * (Conflict.closedWalkCount G 54 : ℝ) +
          28 * t₀⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) -
        56 * (D * t₂ * (Conflict.closedWalkCount G 54 : ℝ) +
          (Q / s) * t₂⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hrepeat := repeatedBadClosedWalk56_cast_le G t₀ D ht₀ hdeg
  have hhigh := highStepBadClosedWalk56_cast_le G s hs Q t₂ D
    hQ ht₂ hdeg hcap
  apply controlledGenuineCycles_card_lower_of_bad_bounds G s _ _
  · simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
      Conflict56.walkCount, Conflict.walkCount] using hrepeat
  · simpa only [Consecutive56.closedWalkCount, Conflict.closedWalkCount,
      Consecutive56.walkCount, Conflict.walkCount] using hhigh

lemma controlledGenuineCycles_card_lower_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q D t₀ t₂ : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y)) :
    (Conflict.closedWalkCount G 56 : ℝ) -
        56 * ∑ b : Bool,
          (D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) -
        56 * ∑ b : Bool,
          (D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hrepeat := repeatedBadClosedWalk56_side_cast_le
    G side t₀ D ht₀ hD hcross hdeg
  have hhigh := highStepBadClosedWalk56_side_cast_le
    G side s hs Q t₂ D hQ ht₂ hD hcross hdeg hcap
  apply controlledGenuineCycles_card_lower_of_bad_bounds G s _ _
  · simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
      Conflict56.walkCount, Conflict.walkCount] using hrepeat
  · simpa only [Consecutive56.closedWalkCount, Conflict.closedWalkCount,
      Consecutive56.walkCount, Conflict.walkCount] using hhigh

lemma controlledGenuineCycles_half_closedWalkCount_bipartite_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (hs : 0 < s)
    (Q D t₀ t₂ : Bool → ℝ)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y))
    (hclosed : 0 < (Conflict.closedWalkCount G 56 : ℝ))
    (hnumeric :
      56 * ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2) :
    (Conflict.closedWalkCount G 56 : ℝ) / 2 ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hinterp : (Conflict.closedWalkCount G 54 : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
        (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28) := by
    simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
      Conflict56.walkCount, Conflict.walkCount] using
      Erdos113Moments56.closedWalkCount_interpolation_28 G
  have hraw := controlledGenuineCycles_card_lower_bipartite
    G side s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hcross hdeg hcap
  have hreplace₀ : ∀ b,
      D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D b * t₀ b *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    intro b
    exact mul_le_mul_of_nonneg_left hinterp
      (mul_nonneg (hD b) (ht₀ b).le)
  have hreplace₂ : ∀ b,
      D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D b * t₂ b *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    intro b
    exact mul_le_mul_of_nonneg_left hinterp
      (mul_nonneg (hD b) (ht₂ b).le)
  have hsum₀ :
      ∑ b : Bool,
          (D b * t₀ b * (Conflict.closedWalkCount G 54 : ℝ) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
        ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) := by
    exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hreplace₀ b) le_rfl)
  have hsum₂ :
      ∑ b : Bool,
          (D b * t₂ b * (Conflict.closedWalkCount G 54 : ℝ) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) := by
    exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hreplace₂ b) le_rfl)
  linarith

lemma closedWalkCount_54_interpolation_56
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Conflict.closedWalkCount G 54 : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
        (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28) := by
  simpa only [Conflict56.closedWalkCount, Conflict.closedWalkCount,
    Conflict56.walkCount, Conflict.walkCount] using
    Erdos113Moments56.closedWalkCount_interpolation_28 G

lemma closedWalkCount_56_lower_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (hd : 0 ≤ d) (hmin : ∀ x, d ≤ (G.degree x : ℝ)) :
    d ^ 56 ≤ (Conflict.closedWalkCount G 56 : ℝ) := by
  simpa only [show 56 = 2 * 28 by norm_num] using
    Lower.closedWalkCount_lower_of_minDegree G d hd hmin 28

lemma controlledGenuineCycles_half_closedWalkCount_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 0 < s) (Q D t₀ t₂ : ℝ)
    (hQ : 0 ≤ Q) (hD : 0 ≤ D) (ht₀ : 0 < t₀) (ht₂ : 0 < t₂)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤ Q)
    (hnumeric :
      56 * (D * t₀ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        28 * t₀⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
      56 * (D * t₂ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        (Q / s) * t₂⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2) :
    (Conflict.closedWalkCount G 56 : ℝ) / 2 ≤
      ((controlledGenuineCycles G s).card : ℝ) := by
  have hinterp := closedWalkCount_54_interpolation_56 G
  have hraw := controlledGenuineCycles_card_lower_of_degree_and_c4cap
    G s hs Q D t₀ t₂ hQ ht₀ ht₂ hdeg hcap
  have ht₀nonneg : 0 ≤ t₀ := ht₀.le
  have ht₂nonneg : 0 ≤ t₂ := ht₂.le
  have hreplace₀ :
      D * t₀ * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D * t₀ * ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
          (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    gcongr
  have hreplace₂ :
      D * t₂ * (Conflict.closedWalkCount G 54 : ℝ) ≤
        D * t₂ * ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
          (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) := by
    gcongr
  linarith

noncomputable def fewFourCycleGoodFamily_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 0 < s) (β Q D t₀ t₂ : ℝ)
    (hβ : 0 ≤ β) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (ht₀ : 0 < t₀) (ht₂ : 0 < t₂)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤ Q)
    (hbad :
      56 * (D * t₀ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        28 * t₀⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
      56 * (D * t₂ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        (Q / s) * t₂⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2)
    (hpattern : (16 * 7 * s : ℝ) *
        (Fintype.card V * D ^ 53) ≤
      β * ((Conflict.closedWalkCount G 56 : ℝ) / 2)) :
    IsGoodCycleFamily G β (controlledGenuineCycles G s) := by
  apply controlledGenuineCycles_isGood G s hs β D
    ((Conflict.closedWalkCount G 56 : ℝ) / 2) hβ hD hdeg
  · exact controlledGenuineCycles_half_closedWalkCount_of_numerics
      G s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hdeg hcap hbad
  · exact hpattern

/-- Janzer's `β`-nice condition, again for `k = 7`.  In every adjacent-pair
fiber, prescribing either missing coordinate occupies at most a `β`
proportion. -/
structure IsNiceCycleFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (β : ℝ) (C : Finset (CycleTuple V)) : Prop where
  genuine : ∀ x ∈ C, IsGenuineCycleTuple G x
  balanced : ∀ (i : Fin 56) (r : OffPair i → V) (u : V),
    (((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card : ℝ) ≤
      β * (pairFiber C i r).card

lemma fin56_ne_add_one (i : Fin 56) : i ≠ i + 1 := by
  decide +revert

def fillPairLeft {V : Type*} (i : Fin 56) (r : OffPair i → V) (u : V) :
    OffSingle (i + 1) → V := fun j ↦
  if h : (j : Fin 56) = i then u else r ⟨j, h, j.property⟩

def fillPairRight {V : Type*} (i : Fin 56) (r : OffPair i → V) (u : V) :
    OffSingle i → V := fun j ↦
  if h : (j : Fin 56) = i + 1 then u else r ⟨j, j.property, h⟩

lemma pairFiber_filter_left_subset_singleFiber {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V) (u : V) :
    (pairFiber C i r).filter (fun x : CycleTuple V ↦ x i = u) ⊆
      singleFiber C (i + 1) (fillPairLeft i r u) := by
  intro x hx
  have hxpair := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hxleft := (Finset.mem_filter.mp hx).2
  rw [singleFiber, Finset.mem_filter]
  refine ⟨hxpair.1, ?_⟩
  funext j
  simp only [restrictOffSingle, fillPairLeft]
  split_ifs with hj
  · simpa [hj] using hxleft
  · have hrest := congrFun hxpair.2 ⟨j, hj, j.property⟩
    exact hrest

lemma pairFiber_filter_right_subset_singleFiber {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V) (u : V) :
    (pairFiber C i r).filter (fun x : CycleTuple V ↦ x (i + 1) = u) ⊆
      singleFiber C i (fillPairRight i r u) := by
  intro x hx
  have hxpair := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hxright := (Finset.mem_filter.mp hx).2
  rw [singleFiber, Finset.mem_filter]
  refine ⟨hxpair.1, ?_⟩
  funext j
  simp only [restrictOffSingle, fillPairRight]
  split_ifs with hj
  · simpa [hj] using hxright
  · have hrest := congrFun hxpair.2 ⟨j, j.property, hj⟩
    exact hrest

lemma IsGoodCycleFamily.prescribed_pair_card_le {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (i : Fin 56) (r : OffPair i → V) (u : V) :
    ((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card ≤
      2 * hgood.s := by
  let L := (pairFiber C i r).filter (fun x : CycleTuple V ↦ x i = u)
  let R := (pairFiber C i r).filter (fun x : CycleTuple V ↦ x (i + 1) = u)
  have hsubset :
      (pairFiber C i r).filter (fun x : CycleTuple V ↦
        x i = u ∨ x (i + 1) = u) ⊆ L ∪ R := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_union, L, R] at hx ⊢
    exact hx.2.elim (fun h ↦ Or.inl ⟨hx.1, h⟩) (fun h ↦ Or.inr ⟨hx.1, h⟩)
  have hL : L.card ≤ hgood.s :=
    (Finset.card_le_card (pairFiber_filter_left_subset_singleFiber C i r u)).trans
      (hgood.single_card (i + 1) (fillPairLeft i r u))
  have hR : R.card ≤ hgood.s :=
    (Finset.card_le_card (pairFiber_filter_right_subset_singleFiber C i r u)).trans
      (hgood.single_card i (fillPairRight i r u))
  calc
    ((pairFiber C i r).filter fun x : CycleTuple V ↦
      x i = u ∨ x (i + 1) = u).card ≤
        (L ∪ R).card := Finset.card_le_card hsubset
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ 2 * hgood.s := by omega

def relevantPairFibers {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) : Finset (Finset (CycleTuple V)) :=
  Finset.univ.biUnion fun i : Fin 56 ↦
    (pairPatterns C i).image (pairFiber C i)

lemma pairFiber_nonempty_of_mem_pairPatterns {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V)
    (hr : r ∈ pairPatterns C i) : (pairFiber C i r).Nonempty := by
  obtain ⟨x, hxC, hxr⟩ := Finset.mem_image.mp hr
  refine ⟨x, ?_⟩
  simp only [pairFiber, Finset.mem_filter]
  exact ⟨hxC, hxr⟩

lemma pairFiber_mem_relevantPairFibers_of_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (i : Fin 56) (r : OffPair i → V)
    (hr : (pairFiber C i r).Nonempty) :
    pairFiber C i r ∈ relevantPairFibers C := by
  obtain ⟨x, hx⟩ := hr
  have hxdata := Finset.mem_filter.mp hx
  rw [relevantPairFibers, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [Finset.mem_image]
  refine ⟨restrictOffPair i x, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, hxdata.1, rfl⟩
  · exact congrArg (pairFiber C i) hxdata.2

lemma card_relevantPairFibers_le {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) :
    (relevantPairFibers C).card ≤ ∑ i : Fin 56, (pairPatterns C i).card := by
  calc
    (relevantPairFibers C).card ≤
        ∑ i : Fin 56, ((pairPatterns C i).image (pairFiber C i)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin 56, (pairPatterns C i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.card_image_le

lemma IsGoodCycleFamily.relevantPairFibers_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) :
    (16 * 7 * hgood.s : ℝ) * (relevantPairFibers C).card ≤
      56 * (β * C.card) := by
  have hcard : ((relevantPairFibers C).card : ℝ) ≤
      ∑ i : Fin 56, ((pairPatterns C i).card : ℝ) := by
    exact_mod_cast card_relevantPairFibers_le C
  calc
    (16 * 7 * hgood.s : ℝ) * (relevantPairFibers C).card ≤
        (16 * 7 * hgood.s : ℝ) *
          ∑ i : Fin 56, ((pairPatterns C i).card : ℝ) := by
      gcongr
    _ = ∑ i : Fin 56,
          (16 * 7 * hgood.s : ℝ) * (pairPatterns C i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin 56, β * C.card := by
      exact Finset.sum_le_sum fun i _ ↦ hgood.pattern_card i
    _ = 56 * (β * C.card) := by simp

/-- Janzer's pruning lemma (Lemma 2.15), specialized to the 56-coordinate
families used for `H_{7,784}`. -/
theorem IsGoodCycleFamily.exists_nice_subfamily {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (hβ : 0 < β) (hC : C.Nonempty) :
    ∃ C' : Finset (CycleTuple V),
      C' ⊆ C ∧ C'.Nonempty ∧ IsNiceCycleFamily G β C' := by
  let x : ℝ := 2 * hgood.s / β
  let t : ℕ := ⌈x⌉₊
  let fibers := relevantPairFibers C
  have hxpos : 0 < x := by
    dsimp [x]
    have hs : (0 : ℝ) < hgood.s := by exact_mod_cast hgood.s_pos
    positivity
  have htpos : 0 < t := by
    exact Nat.ceil_pos.mpr hxpos
  have htminus : ((t - 1 : ℕ) : ℝ) < x := by
    have htceil := Nat.ceil_lt_add_one hxpos.le
    change (t : ℝ) < x + 1 at htceil
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
    linarith
  have htwo : (2 * hgood.s : ℝ) * (fibers.card : ℝ) ≤ β * C.card := by
    have hrel := hgood.relevantPairFibers_bound
    change (16 * 7 * hgood.s : ℝ) * fibers.card ≤ 56 * (β * C.card) at hrel
    norm_num at hrel ⊢
    nlinarith
  have hratio : (fibers.card : ℝ) * x ≤ C.card := by
    dsimp [x]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hβ).2
    nlinarith
  have hpruneCard : fibers.card * (t - 1) < C.card := by
    by_cases hfibers : fibers.card = 0
    · simp [hfibers, hC.card_pos]
    · have hfibersPos : 0 < (fibers.card : ℝ) := by positivity
      have hstrict : (fibers.card : ℝ) * (t - 1 : ℕ) < (C.card : ℝ) :=
        (mul_lt_mul_of_pos_left htminus hfibersPos).trans_le hratio
      exact_mod_cast hstrict
  obtain ⟨C', hC'subset, hC'card, hC'stable⟩ :=
    exists_pruned_subfamily t C fibers
  have hC'nonempty : C'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, zero_add] at hC'card
    omega
  refine ⟨C', hC'subset, hC'nonempty, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hgood.genuine y (hC'subset hy)
  · intro i r u
    by_cases hpair : (pairFiber C' i r).Nonempty
    · have hpairOriginal : (pairFiber C i r).Nonempty := by
        obtain ⟨y, hy⟩ := hpair
        refine ⟨y, ?_⟩
        have hy' := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hC'subset hy'.1, hy'.2⟩
      have hmem : pairFiber C i r ∈ fibers := by
        exact pairFiber_mem_relevantPairFibers_of_nonempty C i r hpairOriginal
      have hinter : C' ∩ pairFiber C i r = pairFiber C' i r := by
        ext y
        simp only [pairFiber, Finset.mem_inter, Finset.mem_filter]
        constructor
        · exact fun hy ↦ ⟨hy.1, hy.2.2⟩
        · exact fun hy ↦ ⟨hy.1, hC'subset hy.1, hy.2⟩
      have htcard : t ≤ (pairFiber C' i r).card := by
        rw [← hinter]
        exact hC'stable (pairFiber C i r) hmem (by simpa [hinter] using hpair)
      have hxcard : x ≤ ((pairFiber C' i r).card : ℝ) := by
        exact (Nat.le_ceil x).trans (by exact_mod_cast htcard)
      have hdenom : (2 * hgood.s : ℝ) ≤
          β * (pairFiber C' i r).card := by
        have := mul_le_mul_of_nonneg_left hxcard hβ.le
        dsimp [x] at this
        calc
          (2 * hgood.s : ℝ) = β * ((2 * hgood.s : ℝ) / β) := by
            field_simp
          _ ≤ β * (pairFiber C' i r).card := this
      have heventSubset :
          (pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u) ⊆
            (pairFiber C i r).filter (fun y : CycleTuple V ↦
              y i = u ∨ y (i + 1) = u) := by
        intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        have hypair := Finset.mem_filter.mp hy.1
        exact ⟨Finset.mem_filter.mpr ⟨hC'subset hypair.1, hypair.2⟩, hy.2⟩
      have hevent :
          ((pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u)).card ≤
            2 * hgood.s :=
        (Finset.card_le_card heventSubset).trans (hgood.prescribed_pair_card_le i r u)
      have heventReal :
          (((pairFiber C' i r).filter (fun y : CycleTuple V ↦
            y i = u ∨ y (i + 1) = u)).card : ℝ) ≤ (2 * hgood.s : ℝ) := by
        exact_mod_cast hevent
      exact heventReal.trans hdenom
    · have hempty : pairFiber C' i r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpair
      simp [hempty]

/-! ## The explicit Janzer graph -/

/-- There are fourteen matching-pairs of rows in the chosen graph `H_{7,784}`. -/
abbrev Row := Fin 14 × Bool

/-- Splitting a cyclic coordinate of length `1568` into a coordinate modulo `784`
and its parity bit. -/
abbrev Column := ZMod 784 × Bool

/-- The perfect matching between rows `(2i+1,2i+2)`. -/
def matchingRow (r : Row) : Row := (r.1, !r.2)

/-- The row involution used by the nonmatching two-factor.  It fixes the two
boundary rows and pairs every two consecutive interior rows. -/
def turnRow (r : Row) : Row :=
  match r.2 with
  | false => if h : r.1 = 0 then r else (⟨r.1.val - 1, by omega⟩, true)
  | true => if h : r.1 = 13 then r else (⟨r.1.val + 1, by omega⟩, false)

lemma turnRow_involutive (r : Row) : turnRow (turnRow r) = r := by
  decide +revert

/-- Successor on the cyclic coordinate of length `1568`. -/
def nextColumn (c : Column) : Column :=
  match c.2 with
  | false => (c.1, true)
  | true => (c.1 + 1, false)

/-- Predecessor on the cyclic coordinate of length `1568`. -/
def prevColumn (c : Column) : Column :=
  match c.2 with
  | false => (c.1 - 1, true)
  | true => (c.1, false)

/-! ### The 56-cycle interleaving used by the auxiliary graph -/

abbrev SliceTuple (V : Type*) := Row → V

def rowOfFin28 (r : Fin 28) : Row :=
  (⟨r.val / 2, by omega⟩, decide (r.val % 2 = 1))

def interleavingRow (p : Fin 56) : Row :=
  if h : p.val < 28 then rowOfFin28 ⟨p.val, h⟩
  else rowOfFin28 ⟨55 - p.val, by omega⟩

def interleavingUsesLeft (p : Fin 56) : Bool :=
  if p.val < 28 then decide (p.val % 4 < 2)
  else decide ((p.val - 28) % 4 < 2)

def interleavingCoordinate (p : Fin 56) : Bool × Row :=
  (interleavingUsesLeft p, interleavingRow p)

def evalSliceCoordinate {V : Type*} (y z : SliceTuple V) (a : Bool × Row) : V :=
  if a.1 then y a.2 else z a.2

def interleavedCycle {V : Type*} (y z : SliceTuple V) : CycleTuple V :=
  fun p ↦ evalSliceCoordinate y z (interleavingCoordinate p)

lemma interleavingCoordinate_injective : Function.Injective interleavingCoordinate := by
  decide +revert

lemma interleavingCoordinate_bijective : Function.Bijective interleavingCoordinate := by
  apply (Fintype.bijective_iff_injective_and_card interleavingCoordinate).2
  refine ⟨interleavingCoordinate_injective, ?_⟩
  decide

noncomputable def interleavingEquiv : Fin 56 ≃ Bool × Row :=
  Equiv.ofBijective interleavingCoordinate interleavingCoordinate_bijective

noncomputable def sliceOfCycle {V : Type*} (b : Bool) (x : CycleTuple V) :
    SliceTuple V := fun r ↦ x (interleavingEquiv.symm (b, r))

@[simp] lemma interleavingCoordinate_equiv_symm (a : Bool × Row) :
    interleavingCoordinate (interleavingEquiv.symm a) = a :=
  interleavingEquiv.apply_symm_apply a

@[simp] lemma sliceOfCycle_interleavedCycle_left {V : Type*}
    (y z : SliceTuple V) : sliceOfCycle true (interleavedCycle y z) = y := by
  funext r
  simp [sliceOfCycle, interleavedCycle, evalSliceCoordinate]

@[simp] lemma sliceOfCycle_interleavedCycle_right {V : Type*}
    (y z : SliceTuple V) : sliceOfCycle false (interleavedCycle y z) = z := by
  funext r
  simp [sliceOfCycle, interleavedCycle, evalSliceCoordinate]

lemma interleavedCycle_sliceOfCycle {V : Type*} (x : CycleTuple V) :
    interleavedCycle (sliceOfCycle true x) (sliceOfCycle false x) = x := by
  funext p
  have hp : interleavingEquiv.symm (interleavingCoordinate p) = p := by
    apply interleavingCoordinate_injective
    simp
  unfold interleavedCycle evalSliceCoordinate
  split <;> rename_i h
  · change x (interleavingEquiv.symm (true, (interleavingCoordinate p).2)) = x p
    rw [show (true, (interleavingCoordinate p).2) = interleavingCoordinate p by
      ext <;> simp_all, hp]
  · change x (interleavingEquiv.symm (false, (interleavingCoordinate p).2)) = x p
    rw [show (false, (interleavingCoordinate p).2) = interleavingCoordinate p by
      ext <;> simp_all, hp]

def sameSidePairStart (p : Fin 56) : Fin 56 :=
  if interleavingUsesLeft (p + 1) = interleavingUsesLeft p then p else p - 1

lemma sameSidePairStart_spec (p : Fin 56) :
    (sameSidePairStart p = p ∨ sameSidePairStart p + 1 = p) ∧
    interleavingUsesLeft (sameSidePairStart p) = interleavingUsesLeft p ∧
    interleavingUsesLeft (sameSidePairStart p + 1) = interleavingUsesLeft p := by
  decide +revert

@[simp] lemma interleavingUsesLeft_equiv_symm (b : Bool) (r : Row) :
    interleavingUsesLeft (interleavingEquiv.symm (b, r)) = b := by
  have h := congrArg Prod.fst (interleavingCoordinate_equiv_symm (b, r))
  exact h

lemma sliceOfCycle_eq_of_restrictOffPair_eq {V : Type*} (b : Bool)
    (i : Fin 56) {x x' : CycleTuple V}
    (hi : interleavingUsesLeft i ≠ b)
    (hi1 : interleavingUsesLeft (i + 1) ≠ b)
    (hrest : restrictOffPair i x' = restrictOffPair i x) :
    sliceOfCycle b x' = sliceOfCycle b x := by
  funext r
  let p := interleavingEquiv.symm (b, r)
  have hpuse : interleavingUsesLeft p = b := interleavingUsesLeft_equiv_symm b r
  have hpi : p ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact hpuse
  have hpi1 : p ≠ i + 1 := by
    intro h
    apply hi1
    rw [← h]
    exact hpuse
  exact congrFun hrest ⟨p, hpi, hpi1⟩

noncomputable def fixedSliceCycles {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    Finset (CycleTuple V) := C.filter fun x ↦ sliceOfCycle b x = y

lemma fixedSliceCycles_pairFiber_subset {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V)
    (r : Row) (x : CycleTuple V) (hx : x ∈ fixedSliceCycles C b y) :
    pairFiber C (sameSidePairStart (interleavingEquiv.symm (!b, r)))
      (restrictOffPair (sameSidePairStart (interleavingEquiv.symm (!b, r))) x) ⊆
        fixedSliceCycles C b y := by
  intro x' hx'
  let p := interleavingEquiv.symm (!b, r)
  let i := sameSidePairStart p
  have hpuse : interleavingUsesLeft p = !b := interleavingUsesLeft_equiv_symm (!b) r
  have hispec := sameSidePairStart_spec p
  have hiuse : interleavingUsesLeft i = !b := hispec.2.1.trans hpuse
  have hi1use : interleavingUsesLeft (i + 1) = !b := hispec.2.2.trans hpuse
  have hine : interleavingUsesLeft i ≠ b := by
    rw [hiuse]
    cases b <;> decide
  have hi1ne : interleavingUsesLeft (i + 1) ≠ b := by
    rw [hi1use]
    cases b <;> decide
  have hxdata := Finset.mem_filter.mp hx
  have hx'data := Finset.mem_filter.mp hx'
  rw [fixedSliceCycles, Finset.mem_filter]
  refine ⟨hx'data.1, ?_⟩
  calc
    sliceOfCycle b x' = sliceOfCycle b x :=
      sliceOfCycle_eq_of_restrictOffPair_eq b i hine hi1ne hx'data.2
    _ = y := hxdata.2

lemma IsNiceCycleFamily.fixedSliceCycles_coordinate_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (b : Bool) (y : SliceTuple V)
    (r : Row) (u : V) :
    (((fixedSliceCycles C b y).filter fun x : CycleTuple V ↦
      sliceOfCycle (!b) x r = u).card : ℝ) ≤
      β * (fixedSliceCycles C b y).card := by
  let D := fixedSliceCycles C b y
  let p := interleavingEquiv.symm (!b, r)
  let i := sameSidePairStart p
  let key : CycleTuple V → (OffPair i → V) := restrictOffPair i
  let keys := D.image key
  let E := D.filter fun x : CycleTuple V ↦ sliceOfCycle (!b) x r = u
  have hispec := sameSidePairStart_spec p
  have hfiber (q : OffPair i → V) (hq : q ∈ keys) :
      D.filter (fun x ↦ key x = q) = pairFiber C i q := by
    obtain ⟨w, hwD, hwq⟩ := Finset.mem_image.mp hq
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      have hxC := (Finset.mem_filter.mp hx.1).1
      exact Finset.mem_filter.mpr ⟨hxC, hx.2⟩
    · intro hx
      have hxpair := Finset.mem_filter.mp hx
      have hsubset := fixedSliceCycles_pairFiber_subset C b y r w hwD
      have hxD : x ∈ D := hsubset (by
        rw [show restrictOffPair i w = q from hwq]
        exact hx)
      exact ⟨hxD, hxpair.2⟩
  have hlocal (q : OffPair i → V) (hq : q ∈ keys) :
      (((E.filter fun x ↦ key x = q).card : ℕ) : ℝ) ≤
        β * (D.filter fun x ↦ key x = q).card := by
    have hsubset : E.filter (fun x ↦ key x = q) ⊆
        (pairFiber C i q).filter (fun x : CycleTuple V ↦
          x i = u ∨ x (i + 1) = u) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hxE := Finset.mem_filter.mp hx'.1
      have hxpair : x ∈ pairFiber C i q := by
        rw [← hfiber q hq]
        exact Finset.mem_filter.mpr ⟨hxE.1, hx'.2⟩
      refine Finset.mem_filter.mpr ⟨hxpair, ?_⟩
      have hxu : x p = u := by
        simpa [p, sliceOfCycle] using hxE.2
      rcases hispec.1 with hpi | hpi
      · exact Or.inl (by simpa [i, hpi] using hxu)
      · exact Or.inr (by simpa [i, hpi] using hxu)
    calc
      (((E.filter fun x ↦ key x = q).card : ℕ) : ℝ) ≤
          (((pairFiber C i q).filter (fun x : CycleTuple V ↦
            x i = u ∨ x (i + 1) = u)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ β * (pairFiber C i q).card := hnice.balanced i q u
      _ = β * (D.filter fun x ↦ key x = q).card := by rw [hfiber q hq]
  have hEcard : E.card = ∑ q ∈ keys, (E.filter fun x ↦ key x = q).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx ↦ by
      exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have hDcard : D.card = ∑ q ∈ keys, (D.filter fun x ↦ key x = q).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx ↦
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
  change (E.card : ℝ) ≤ β * D.card
  calc
    (E.card : ℝ) = ∑ q ∈ keys, ((E.filter fun x ↦ key x = q).card : ℝ) := by
      exact_mod_cast hEcard
    _ ≤ ∑ q ∈ keys, β * (D.filter fun x ↦ key x = q).card := by
      exact Finset.sum_le_sum fun q hq ↦ hlocal q hq
    _ = β * ∑ q ∈ keys, ((D.filter fun x ↦ key x = q).card : ℝ) := by
      rw [Finset.mul_sum]
    _ = β * D.card := by rw [← Nat.cast_sum, ← hDcard]

def orientedCycle {V : Type*} (b : Bool) (y z : SliceTuple V) : CycleTuple V :=
  if b then interleavedCycle y z else interleavedCycle z y

@[simp] lemma sliceOfCycle_orientedCycle_fixed {V : Type*}
    (b : Bool) (y z : SliceTuple V) : sliceOfCycle b (orientedCycle b y z) = y := by
  cases b <;> simp [orientedCycle]

@[simp] lemma sliceOfCycle_orientedCycle_free {V : Type*}
    (b : Bool) (y z : SliceTuple V) : sliceOfCycle (!b) (orientedCycle b y z) = z := by
  cases b <;> simp [orientedCycle]

lemma orientedCycle_injective {V : Type*} (b : Bool) (y : SliceTuple V) :
    Function.Injective (orientedCycle b y) := by
  intro z z' h
  have := congrArg (sliceOfCycle (!b)) h
  simpa using this

noncomputable def orientedNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    Finset (SliceTuple V) :=
  Finset.univ.filter fun z ↦ orientedCycle b y z ∈ C

lemma orientedNeighbors_image {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    (orientedNeighbors C b y).image (orientedCycle b y) = fixedSliceCycles C b y := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.2, sliceOfCycle_orientedCycle_fixed b y z⟩
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    let z := sliceOfCycle (!b) x
    have hrepr : orientedCycle b y z = x := by
      cases b
      · change interleavedCycle z y = x
        rw [← hx'.2]
        exact interleavedCycle_sliceOfCycle x
      · change interleavedCycle y z = x
        rw [← hx'.2]
        exact interleavedCycle_sliceOfCycle x
    refine Finset.mem_image.mpr ⟨z, ?_, hrepr⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hrepr.symm ▸ hx'.1⟩

lemma card_orientedNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V) :
    (orientedNeighbors C b y).card = (fixedSliceCycles C b y).card := by
  rw [← orientedNeighbors_image C b y, Finset.card_image_iff.mpr]
  exact (orientedCycle_injective b y).injOn

lemma orientedNeighbors_coordinate_card {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (CycleTuple V)) (b : Bool) (y : SliceTuple V)
    (r : Row) (u : V) :
    ((orientedNeighbors C b y).filter fun z ↦ z r = u).card =
      ((fixedSliceCycles C b y).filter fun x ↦ sliceOfCycle (!b) x r = u).card := by
  let S := (orientedNeighbors C b y).filter fun z ↦ z r = u
  have himage : S.image (orientedCycle b y) =
      (fixedSliceCycles C b y).filter fun x ↦ sliceOfCycle (!b) x r = u := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hz' := Finset.mem_filter.mp hz
      have hcycle := Finset.mem_filter.mp hz'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hcycle.2, sliceOfCycle_orientedCycle_fixed b y z⟩,
          by simpa using hz'.2⟩
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      have hxD := Finset.mem_filter.mp hx'.1
      let z := sliceOfCycle (!b) x
      have hrepr : orientedCycle b y z = x := by
        cases b
        · change interleavedCycle z y = x
          rw [← hxD.2]
          exact interleavedCycle_sliceOfCycle x
        · change interleavedCycle y z = x
          rw [← hxD.2]
          exact interleavedCycle_sliceOfCycle x
      refine Finset.mem_image.mpr ⟨z, ?_, hrepr⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hrepr.symm ▸ hxD.1⟩, hx'.2⟩
  rw [← himage, Finset.card_image_iff.mpr]
  exact (orientedCycle_injective b y).injOn

def CyclicallyAdjacentCoordinates (a b : Bool × Row) : Prop :=
  (List.finRange 56).any (fun p ↦ decide
    ((interleavingCoordinate p = a ∧ interleavingCoordinate (p + 1) = b) ∨
    (interleavingCoordinate p = b ∧ interleavingCoordinate (p + 1) = a))) = true

instance instDecidableCyclicallyAdjacentCoordinates (a b : Bool × Row) :
    Decidable (CyclicallyAdjacentCoordinates a b) := by
  unfold CyclicallyAdjacentCoordinates
  infer_instance

lemma interleaving_left_matching (r : Row) :
    CyclicallyAdjacentCoordinates (true, r) (true, matchingRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma interleaving_right_matching (r : Row) :
    CyclicallyAdjacentCoordinates (false, r) (false, matchingRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma interleaving_cross (r : Row) :
    CyclicallyAdjacentCoordinates (true, r) (false, turnRow r) := by
  rcases r with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

lemma adj_evalSliceCoordinate_of_cyclicallyAdjacent {V : Type*}
    (G : SimpleGraph V) (y z : SliceTuple V)
    (hcycle : ∀ p, G.Adj (interleavedCycle y z p) (interleavedCycle y z (p + 1)))
    {a b : Bool × Row} (hab : CyclicallyAdjacentCoordinates a b) :
    G.Adj (evalSliceCoordinate y z a) (evalSliceCoordinate y z b) := by
  rw [CyclicallyAdjacentCoordinates, List.any_iff_exists_prop] at hab
  obtain ⟨p, _hpMem, hp | hp⟩ := hab
  · simpa [interleavedCycle, hp.1, hp.2] using hcycle p
  · simpa [interleavedCycle, hp.1, hp.2] using (hcycle p).symm

/-- The three edge families between two consecutive columns: the matching in
each column and the row-turning edges between the columns. -/
def CompatibleSlices {V : Type*} (G : SimpleGraph V)
    (y z : SliceTuple V) : Prop :=
  (∀ r, G.Adj (y r) (y (matchingRow r))) ∧
  (∀ r, G.Adj (z r) (z (matchingRow r))) ∧
  (∀ r, G.Adj (y r) (z (turnRow r)))

lemma compatibleSlices_of_interleavedCycle {V : Type*} (G : SimpleGraph V)
    (y z : SliceTuple V) (hcycle : IsGenuineCycleTuple G (interleavedCycle y z)) :
    CompatibleSlices G y z := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_left_matching r)
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_right_matching r)
  · intro r
    simpa [evalSliceCoordinate] using
      adj_evalSliceCoordinate_of_cyclicallyAdjacent G y z hcycle.2
        (interleaving_cross r)

lemma CompatibleSlices.symm {V : Type*} {G : SimpleGraph V}
    {y z : SliceTuple V} (h : CompatibleSlices G y z) : CompatibleSlices G z y := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro r
  have hr := h.2.2 (turnRow r)
  rw [turnRow_involutive] at hr
  exact hr.symm

lemma interleavedCycle_self_not_injective {V : Type*} (y : SliceTuple V) :
    ¬ Function.Injective (interleavedCycle y y) := by
  intro hinj
  have heq : interleavedCycle y y (0 : Fin 56) = interleavedCycle y y (55 : Fin 56) := by
    rfl
  have hindex := hinj heq
  have hval := congrArg Fin.val hindex
  norm_num at hval

lemma evalSliceCoordinate_injective_of_interleavedCycle {V : Type*}
    {G : SimpleGraph V} {y z : SliceTuple V}
    (hcycle : IsGenuineCycleTuple G (interleavedCycle y z)) :
    Function.Injective (evalSliceCoordinate y z) := by
  intro a b hab
  obtain ⟨p, hp⟩ := interleavingCoordinate_bijective.2 a
  obtain ⟨q, hq⟩ := interleavingCoordinate_bijective.2 b
  rw [← hp, ← hq] at hab ⊢
  exact congrArg interleavingCoordinate (hcycle.1 hab)

/-- Two auxiliary vertices conflict if some coordinate of one equals some
coordinate of the other. -/
def SlicesConflict {V : Type*} (y z : SliceTuple V) : Prop :=
  ∃ r s : Row, y r = z s

lemma SlicesConflict.symm {V : Type*} {y z : SliceTuple V}
    (h : SlicesConflict y z) : SlicesConflict z y := by
  obtain ⟨r, s, hrs⟩ := h
  exact ⟨s, r, hrs.symm⟩

/-- The auxiliary graph in Janzer's Lemma 2.16: two row-slices are adjacent
when one of the two oriented interleavings belongs to the cycle family. -/
def auxiliaryGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) : SimpleGraph (SliceTuple V) where
  Adj y z := interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C
  symm := ⟨by aesop⟩
  loopless := ⟨by
    intro y hy
    rcases hy with hy | hy
    · exact interleavedCycle_self_not_injective y (hfamily _ hy).1
    · exact interleavedCycle_self_not_injective y (hfamily _ hy).1⟩

instance auxiliaryGraph.instDecidableRel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) :
    DecidableRel (auxiliaryGraph G C hfamily).Adj := fun y z ↦ by
  change Decidable (interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C)
  infer_instance

lemma auxiliaryGraph_neighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) (y : SliceTuple V) :
    (auxiliaryGraph G C hfamily).neighborFinset y =
      orientedNeighbors C true y ∪ orientedNeighbors C false y := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  change (interleavedCycle y z ∈ C ∨ interleavedCycle z y ∈ C) ↔ _
  simp [orientedNeighbors, orientedCycle]

lemma orientedNeighbors_subset_auxiliary_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) (b : Bool) (y : SliceTuple V) :
    orientedNeighbors C b y ⊆ (auxiliaryGraph G C hfamily).neighborFinset y := by
  rw [auxiliaryGraph_neighborFinset G C hfamily y]
  cases b
  · exact Finset.subset_union_right
  · exact Finset.subset_union_left

lemma IsNiceCycleFamily.auxiliary_coordinate_conflict_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β)
    (y : SliceTuple V) (r : Row) (u : V) :
    ((((auxiliaryGraph G C hnice.genuine).neighborFinset y).filter fun z ↦
      z r = u).card : ℝ) ≤
      2 * β * (auxiliaryGraph G C hnice.genuine).degree y := by
  let A := auxiliaryGraph G C hnice.genuine
  let E (b : Bool) := (orientedNeighbors C b y).filter fun z ↦ z r = u
  have hlocal (b : Bool) : (E b).card ≤ β * A.degree y := by
    calc
      ((E b).card : ℝ) =
          (((fixedSliceCycles C b y).filter fun x : CycleTuple V ↦
            sliceOfCycle (!b) x r = u).card : ℝ) := by
        exact_mod_cast orientedNeighbors_coordinate_card C b y r u
      _ ≤ β * (fixedSliceCycles C b y).card :=
        hnice.fixedSliceCycles_coordinate_bound b y r u
      _ = β * (orientedNeighbors C b y).card := by
        rw [card_orientedNeighbors C b y]
      _ ≤ β * A.degree y := by
        apply mul_le_mul_of_nonneg_left _ hβ
        exact_mod_cast Finset.card_le_card
          (orientedNeighbors_subset_auxiliary_neighborFinset G C hnice.genuine b y)
  have hsubset : (A.neighborFinset y).filter (fun z ↦ z r = u) ⊆ E true ∪ E false := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    rw [auxiliaryGraph_neighborFinset G C hnice.genuine y] at hz'
    rcases Finset.mem_union.mp hz'.1 with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hz'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hz'.2⟩)
  calc
    (((A.neighborFinset y).filter (fun z ↦ z r = u)).card : ℝ) ≤
        ((E true ∪ E false).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (E true).card + (E false).card := by
      exact_mod_cast Finset.card_union_le (E true) (E false)
    _ ≤ β * A.degree y + β * A.degree y := add_le_add (hlocal true) (hlocal false)
    _ = 2 * β * A.degree y := by ring

noncomputable instance instDecidableSlicesConflict {V : Type*}
    (x y : SliceTuple V) : Decidable (SlicesConflict x y) :=
  Classical.propDecidable _

noncomputable def conflictingNeighbors {V : Type*} [Fintype V]
    (A : SimpleGraph (SliceTuple V)) [DecidableRel A.Adj]
    (x y : SliceTuple V) : Finset (SliceTuple V) :=
  (A.neighborFinset y).filter (SlicesConflict x)

lemma IsNiceCycleFamily.auxiliary_conflicting_neighbors_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β)
    (x y : SliceTuple V) :
    ((conflictingNeighbors (auxiliaryGraph G C hnice.genuine) x y).card : ℝ) ≤
      1568 * β * (auxiliaryGraph G C hnice.genuine).degree y := by
  let A := auxiliaryGraph G C hnice.genuine
  let E (r s : Row) := (A.neighborFinset y).filter fun z ↦ z s = x r
  let U := Finset.univ.biUnion fun r : Row ↦
    Finset.univ.biUnion fun s : Row ↦ E r s
  have hsubset : conflictingNeighbors A x y ⊆ U := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    obtain ⟨r, s, hrs⟩ := hz'.2
    simp only [U, Finset.mem_biUnion]
    refine ⟨r, Finset.mem_univ r, ?_⟩
    exact ⟨s, Finset.mem_univ s, Finset.mem_filter.mpr ⟨hz'.1, hrs.symm⟩⟩
  have hUcard : (U.card : ℝ) ≤
      ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := by
    calc
      (U.card : ℝ) ≤
          (∑ r : Row, (Finset.univ.biUnion fun s : Row ↦ E r s).card : ℕ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_le_sum
        intro r _
        exact_mod_cast Finset.card_biUnion_le
  calc
    ((conflictingNeighbors A x y).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ r : Row, ∑ s : Row, ((E r s).card : ℝ) := hUcard
    _ ≤ ∑ _r : Row, ∑ _s : Row, 2 * β * A.degree y := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact hnice.auxiliary_coordinate_conflict_bound hβ y s (x r)
    _ = 1568 * β * A.degree y := by
      norm_num [Fintype.card_congr (Equiv.prodComm (Fin 14) Bool)]
      ring

noncomputable def relationNeighbors {W : Type*} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (x y : W) : Finset W :=
  (A.neighborFinset y).filter (R x)

noncomputable def cleanSelectorThreshold (N : ℕ) : ℝ :=
  (2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * (Real.log N) ^ (4 : ℕ) *
    (N : ℝ) ^ ((1 : ℝ) / 784))⁻¹

@[simp] lemma card_Row : Fintype.card Row = 28 := by decide

@[simp] lemma card_sliceTuple_fin (n : ℕ) :
    Fintype.card (SliceTuple (Fin n)) = n ^ 28 := by
  simp [SliceTuple]

lemma log_four_isLittleO_rpow_one_div_twentyEight :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (4 : ℕ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 28)) := by
  have h := (isLittleO_log_rpow_atTop
    (r := (1 : ℝ) / 112) (by norm_num)).pow (by omega : 0 < (4 : ℕ))
  have hn := h.natCast_atTop
  apply hn.congr_right
  intro n
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

lemma eventually_log_pow_scaled_lt_rpow (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K * Real.log (n : ℝ) ^ (4 : ℕ) < (n : ℝ) ^ ((1 : ℝ) / 28) := by
  have h := log_four_isLittleO_rpow_one_div_twentyEight.const_mul_left K
  have hb := h.bound (c := (1 : ℝ) / 2) (by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hrpow : 0 < (n : ℝ) ^ ((1 : ℝ) / 28) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [abs_of_nonneg (mul_nonneg hK.le (pow_nonneg hlog 4)),
    abs_of_pos hrpow] at hn
  nlinarith

/-- The precise analytic inequality needed to apply the selector to a nice
family with `β = n⁻¹ʲ¹⁴`.  The auxiliary vertex set has cardinality
`n²⁸`, while its local conflict factor is `1568β`. -/
lemma eventually_cleanSelectorThreshold :
    ∀ᶠ n : ℕ in atTop,
      1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) := by
  let K : ℝ := 1568 * 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * 28 ^ (4 : ℕ)
  have hK : 0 < K := by positivity
  filter_upwards [eventually_log_pow_scaled_lt_rpow K hK,
    eventually_ge_atTop (2 : ℕ)] with n hgrowth hn
  rw [card_sliceTuple_fin, cleanSelectorThreshold]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnpow : ((n ^ 28 : ℕ) : ℝ) = (n : ℝ) ^ (28 : ℕ) := by norm_cast
  rw [hnpow, Real.log_pow]
  have hrpowpow : (((n : ℝ) ^ (28 : ℕ)) ^ ((1 : ℝ) / 784)) =
      (n : ℝ) ^ ((1 : ℝ) / 28) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnpos.le]
    norm_num
  rw [hrpowpow]
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hrightpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 28) :=
    Real.rpow_pos_of_pos hnpos _
  let D : ℝ :=
      2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
        (28 * Real.log (n : ℝ)) ^ (4 : ℕ) *
          (n : ℝ) ^ ((1 : ℝ) / 28)
  change 1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) < D⁻¹
  have hdenpos : 0 < D := by dsimp [D]; positivity
  rw [← mul_one D⁻¹, lt_inv_mul_iff₀' hdenpos]
  dsimp [D]
  have hneg : (n : ℝ) ^ (-(1 : ℝ) / 14) *
      (n : ℝ) ^ ((1 : ℝ) / 28) =
        (n : ℝ) ^ (-(1 : ℝ) / 28) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [show 1568 * (n : ℝ) ^ (-(1 : ℝ) / 14) *
        (2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          (28 * Real.log (n : ℝ)) ^ (4 : ℕ) *
            (n : ℝ) ^ ((1 : ℝ) / 28)) =
      K * Real.log (n : ℝ) ^ (4 : ℕ) *
        (n : ℝ) ^ (-(1 : ℝ) / 28) by
      rw [mul_pow, ← hneg]
      dsimp [K]
      ring]
  rw [show (-(1 : ℝ) / 28) = -((1 : ℝ) / 28) by ring,
    Real.rpow_neg hnpos.le]
  calc
    K * Real.log (n : ℝ) ^ 4 * ((n : ℝ) ^ ((1 : ℝ) / 28))⁻¹ <
        (n : ℝ) ^ ((1 : ℝ) / 28) *
          ((n : ℝ) ^ ((1 : ℝ) / 28))⁻¹ :=
      mul_lt_mul_of_pos_right hgrowth (inv_pos.mpr hrightpos)
    _ = 1 := mul_inv_cancel₀ hrightpos.ne'

/-! ### Spectral interpolation for the selector

The conflict count uses the number of closed walks of lengths `1566` and
`1568`.  The following is the exact finite-dimensional Schatten-moment
interpolation used in Janzer's Lemma 2.2, proved from the spectral theorem
and Hölder's inequality. -/

lemma trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : ℕ) :
    Matrix.trace (A ^ j) = ∑ i, hA.eigenvalues i ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, Fintype.card {p : A.Walk x x // p.length = m}

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  norm_cast

lemma closedWalkCount_cast_eq_sum_eigenvalues_pow {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) =
      ∑ i, ((A.isHermitian_adjMatrix ℝ).eigenvalues i) ^ m := by
  rw [closedWalkCount_cast_eq_trace]
  exact trace_pow_eq_sum_eigenvalues_pow _ _ _

lemma closedWalkCount_interpolation_784 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] :
    (closedWalkCount A 1566 : ℝ) ≤
      (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) *
        (closedWalkCount A 1568 : ℝ) ^ ((783 : ℝ) / 784) := by
  let hA := A.isHermitian_adjMatrix ℝ
  let lam : W → ℝ := hA.eigenvalues
  have hholder : Real.HolderConjugate (784 : ℝ) ((784 : ℝ) / 783) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun _ : W ↦ (1 : ℝ))
    (g := fun i : W ↦ (lam i ^ 2) ^ (783 : ℕ)) hholder
    (by intro i hi; positivity) (by intro i hi; positivity)
  dsimp [hA, lam] at hh
  have hleft (x : ℝ) : x ^ 1566 = (x ^ 2) ^ 783 := by ring
  have hright (x : ℝ) :
      ((x ^ 2) ^ (783 : ℕ)) ^ ((784 : ℝ) / 783) = x ^ 1568 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg x)]
    norm_num
    ring
  simp_rw [hright] at hh
  simp_rw [← hleft] at hh
  rw [closedWalkCount_cast_eq_sum_eigenvalues_pow,
    closedWalkCount_cast_eq_sum_eigenvalues_pow]
  simp only [one_mul, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  convert hh using 1 <;> norm_num

universe u

def columnLinearIndex (c : Column) : Fin 1568 :=
  ⟨2 * c.1.val + if c.2 then 1 else 0, by
    have hc := ZMod.val_lt c.1
    split <;> omega⟩

def cyclicSucc1568 (i : Fin 1568) : Fin 1568 :=
  ⟨(i.val + 1) % 1568, Nat.mod_lt _ (by omega)⟩

lemma cyclicSucc1568_columnLinearIndex (c : Column) :
    cyclicSucc1568 (columnLinearIndex c) =
      columnLinearIndex (nextColumn c) := by
  rcases c with ⟨j, b⟩
  cases b
  · apply Fin.ext
    change (2 * j.val + 0 + 1) % 1568 = 2 * j.val + 1
    rw [Nat.mod_eq_of_lt]
    have hj := ZMod.val_lt j
    omega
  · apply Fin.ext
    change (2 * j.val + 1 + 1) % 1568 = 2 * (j + 1).val + 0
    rw [ZMod.val_add]
    change (2 * j.val + 1 + 1) % 1568 = 2 * ((j.val + 1) % 784)
    omega

lemma columnLinearIndex_injective : Function.Injective columnLinearIndex := by
  rintro ⟨j, b⟩ ⟨k, d⟩ h
  have hv : 2 * j.val + (if b then 1 else 0) =
      2 * k.val + (if d then 1 else 0) := congrArg Fin.val h
  cases b <;> cases d
  · apply Prod.ext
    · apply ZMod.val_injective 784
      simpa using hv
    · rfl
  · simp at hv
    omega
  · simp at hv
    omega
  · apply Prod.ext
    · apply ZMod.val_injective 784
      simp at hv
      omega
    · rfl

lemma columnLinearIndex_bijective : Function.Bijective columnLinearIndex := by
  apply (Fintype.bijective_iff_injective_and_card columnLinearIndex).2
  exact ⟨columnLinearIndex_injective, by simp [Column]⟩

noncomputable def columnLinearEquiv : Column ≃ Fin 1568 :=
  Equiv.ofBijective columnLinearIndex columnLinearIndex_bijective

@[simp] lemma columnLinearEquiv_apply (c : Column) :
    columnLinearEquiv c = columnLinearIndex c := rfl

/-! Closed walks are a second, counting-friendly representation of the same
homomorphic `1568`-cycles.  Unlike a raw function on `Fin 1568`, Mathlib's
walk type splits canonically into shorter walks, which is what the proof of
the conflict estimate needs. -/

abbrev ClosedWalk1568 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 1568}

lemma card_ClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    Fintype.card (ClosedWalk1568 A) = closedWalkCount A 1568 := by
  simp [ClosedWalk1568, closedWalkCount, Fintype.card_sigma]

def closedWalkVertex1568 {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) : W :=
  P.2.1.getVert i.val

lemma closedWalkVertex1568_adj_succ {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) :
    A.Adj (closedWalkVertex1568 P i)
      (closedWalkVertex1568 P (cyclicSucc1568 i)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 1568
  · simpa [closedWalkVertex1568, cyclicSucc1568,
      Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 1567 := by omega
    have hend : P.2.1.getVert 1568 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [closedWalkVertex1568, cyclicSucc1568, hilast, hend, hstart] using hadj

def HasClosedWalkConflict1568 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (P : ClosedWalk1568 A) : Prop :=
  ∃ i j, i ≠ j ∧
    R (closedWalkVertex1568 P i) (closedWalkVertex1568 P j)

noncomputable def badClosedWalks1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] : Finset (ClosedWalk1568 A) := by
  classical
  exact Finset.univ.filter (HasClosedWalkConflict1568 R)

@[simp] lemma mem_badClosedWalks1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (P : ClosedWalk1568 A) :
    P ∈ badClosedWalks1568 A R ↔ HasClosedWalkConflict1568 R P := by
  classical
  simp [badClosedWalks1568]

lemma exists_pairwise_nonconflicting_column_cycle_of_badClosedWalks_lt
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hcard : (badClosedWalks1568 A R).card < closedWalkCount A 1568) :
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d) := by
  classical
  have htotal : (Finset.univ : Finset (ClosedWalk1568 A)).card =
      closedWalkCount A 1568 := by
    rw [Finset.card_univ, card_ClosedWalk1568]
  have hnsubset : ¬ (Finset.univ : Finset (ClosedWalk1568 A)) ⊆
      badClosedWalks1568 A R := by
    intro hsubset
    have := Finset.card_le_card hsubset
    rw [htotal] at this
    omega
  obtain ⟨P, _hPuniv, hPgood⟩ := Finset.not_subset.mp hnsubset
  let X : Column → W := fun c ↦ closedWalkVertex1568 P (columnLinearIndex c)
  refine ⟨X, ?_, ?_⟩
  · intro c
    simpa only [X, ← cyclicSucc1568_columnLinearIndex] using
      closedWalkVertex1568_adj_succ P (columnLinearIndex c)
  · intro c d hcd hR
    apply hPgood
    rw [mem_badClosedWalks1568]
    refine ⟨columnLinearIndex c, columnLinearIndex d,
      fun h ↦ hcd (columnLinearIndex_injective h), ?_⟩
    exact hR

lemma card_badClosedWalks1568_eq {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    (badClosedWalks1568 A R).card =
      Fintype.card (Encode.BadClosedWalk1568 A R) := by
  classical
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun p ↦ ⟨p.1, by
        have hp := (mem_badClosedWalks1568 A R p.1).mp p.2
        exact hp⟩
      invFun := fun p ↦ ⟨p.1, by
        apply (mem_badClosedWalks1568 A R p.1).mpr
        exact p.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }

lemma badClosedWalks1568_cast_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (t D s : ℝ) (ht : 0 < t) (hs : 0 ≤ s)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    ((badClosedWalks1568 A R).card : ℝ) ≤
      1568 * (D * t * (closedWalkCount A 1566 : ℝ) +
        784 * s * t⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  rw [card_badClosedWalks1568_eq]
  simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
    Conflict.walkCount] using
      Encode.card_BadClosedWalk1568_cast_le A R t D s ht hs hdegree hsymm hlocal

lemma exists_cleanCycle_of_almostRegular
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → R y x)
    (N δ D L α : ℝ)
    (hN : N = Fintype.card W)
    (hδ : 0 < δ) (hD : 0 < D) (hL : 0 < L) (hα : 0 ≤ α)
    (hmin : ∀ x, δ ≤ (A.degree x : ℝ))
    (hmax : ∀ x, (A.degree x : ℝ) ≤ D)
    (hreg : D ≤ L * δ)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ α * D)
    (hsmall : α <
      (2 * 1568 * 784 * 3136 * L ^ 2 * N ^ ((1 : ℝ) / 784))⁻¹) :
    ∃ X : Erdos113.Column → W,
      (∀ c, A.Adj (X c) (X (Erdos113.nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 784)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let t : ℝ := D / (3136 * L ^ 2 * Q)
  have ht : 0 < t := by dsimp [t]; positivity
  let H : ℝ := Erdos113.closedWalkCount A 1568
  let H' : ℝ := Erdos113.closedWalkCount A 1566
  have hHlower : δ ^ 1568 ≤ H := by
    dsimp [H]
    simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
      Conflict.walkCount] using
      Lower.closedWalkCount_lower_of_minDegree A δ hδ.le hmin 784
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < δ ^ 1568) hHlower
  have hinterp : H' ≤ Q * H ^ ((783 : ℝ) / 784) := by
    dsimp [H', Q, H]
    simpa [hN] using Erdos113.closedWalkCount_interpolation_784 A
  have hrootid : H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hδroot : δ ^ 2 ≤ H ^ ((1 : ℝ) / 784) := by
    have := Real.rpow_le_rpow (by positivity : 0 ≤ δ ^ 1568) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 784)
    convert this using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hδ.le]
    norm_num
  have hHp : H' * δ ^ 2 ≤ Q * H := by
    calc
      H' * δ ^ 2 ≤ (Q * H ^ ((783 : ℝ) / 784)) * δ ^ 2 := by
        gcongr
      _ ≤ (Q * H ^ ((783 : ℝ) / 784)) *
          H ^ ((1 : ℝ) / 784) := by
        gcongr
      _ = Q * (H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784)) := by ring
      _ = Q * H := by rw [hrootid]
  have hDsq : D ^ 2 ≤ L ^ 2 * δ ^ 2 := by nlinarith [sq_nonneg (L * δ - D)]
  have hfirst : 1568 * (D * t * H') ≤ H / 2 := by
    have hden : 0 < 3136 * L ^ 2 * Q := by positivity
    have hcore : D ^ 2 * H' ≤ L ^ 2 * Q * H := by
      calc
        D ^ 2 * H' ≤ (L ^ 2 * δ ^ 2) * H' := by
          gcongr
        _ = L ^ 2 * (H' * δ ^ 2) := by ring
        _ ≤ L ^ 2 * (Q * H) := by gcongr
        _ = L ^ 2 * Q * H := by ring
    dsimp [t]
    rw [div_eq_mul_inv]
    have hcalc : 1568 * (D * (D * (3136 * L ^ 2 * Q)⁻¹) * H') =
        (1568 / 3136) * ((D ^ 2 * H') / (L ^ 2 * Q)) := by
      field_simp
      <;> ring
    rw [hcalc]
    have hquot : (D ^ 2 * H') / (L ^ 2 * Q) ≤ H := by
      apply (div_le_iff₀ (by positivity : 0 < L ^ 2 * Q)).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcore
    norm_num
    nlinarith
  have hcoef : 1568 * 784 * (α * D) * t⁻¹ < (1 : ℝ) / 2 := by
    have hbound : α * (2 * 1568 * 784 * 3136 * L ^ 2 * Q) < 1 := by
      have hdenpos : 0 < 2 * 1568 * 784 * 3136 * L ^ 2 * Q := by positivity
      apply (lt_inv_mul_iff₀' hdenpos).mp
      simpa [Q] using hsmall
    have htinv : t⁻¹ = (3136 * L ^ 2 * Q) / D := by
      dsimp [t]
      rw [inv_div]
    rw [htinv]
    field_simp
    nlinarith
  have hsecond : 1568 * (784 * (α * D) * t⁻¹ * H) < H / 2 := by
    nlinarith
  have hbad := Erdos113.badClosedWalks1568_cast_le A R t D (α * D)
    ht (mul_nonneg hα hD.le) hmax hR hlocal
  have hbadlt : ((Erdos113.badClosedWalks1568 A R).card : ℝ) < H := by
    calc
      ((Erdos113.badClosedWalks1568 A R).card : ℝ) ≤
          1568 * (D * t * H' + 784 * (α * D) * t⁻¹ * H) := by
        simpa [H, H'] using hbad
      _ = 1568 * (D * t * H') +
          1568 * (784 * (α * D) * t⁻¹ * H) := by ring
      _ < H / 2 + H / 2 := add_lt_add_of_le_of_lt hfirst hsecond
      _ = H := by ring
  apply Erdos113.exists_pairwise_nonconflicting_column_cycle_of_badClosedWalks_lt
  dsimp [H] at hbadlt
  exact_mod_cast hbadlt

lemma badClosedWalks1568_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    ((badClosedWalks1568 A R).card : ℝ) ≤
      1568 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 1566 : ℝ) +
          784 * s (!b) * (t b)⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  rw [card_badClosedWalks1568_eq]
  simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
    Conflict.walkCount] using
      Erdos113Sides.card_BadClosedWalk1568_side_cast_le
        A R side t D s ht hD hs hcross hdegree hsymm hlocal

lemma exists_cleanCycle_of_bipartiteAlmostRegular
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → R y x)
    (side : W → Bool) (d D : Bool → ℝ) (N L α : ℝ)
    (hN : N = Fintype.card W)
    (hd : ∀ b, 0 < d b) (hD : ∀ b, 0 < D b)
    (hL : 0 < L) (hα : 0 ≤ α)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (A.degree x : ℝ))
    (hmax : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hreg : ∀ b, D b ≤ L * d b)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ α * D (side y))
    (hsmall : α <
      (4 * 1568 * 784 * 6272 * L ^ 2 * N ^ ((1 : ℝ) / 784))⁻¹) :
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c e, c ≠ e → ¬ R (X c) (X e) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 784)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let t : Bool → ℝ := fun b ↦ D (!b) / (6272 * L ^ 2 * Q)
  have ht : ∀ b, 0 < t b := by
    intro b
    dsimp [t]
    exact div_pos (hD (!b)) (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL)) hQ)
  let H : ℝ := Erdos113.closedWalkCount A 1568
  let H' : ℝ := Erdos113.closedWalkCount A 1566
  let p : ℝ := d false * d true
  have hp : 0 < p := by exact mul_pos (hd false) (hd true)
  have hHlower : p ^ 784 ≤ H := by
    dsimp [H, p]
    simpa only [Erdos113.closedWalkCount, Conflict.closedWalkCount,
      Conflict.walkCount] using
      Erdos113LowerBipartite.closedWalkCount_1568_lower_bipartite
        A side d (fun b ↦ (hd b).le) hcross hmin
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < p ^ 784) hHlower
  have hinterp : H' ≤ Q * H ^ ((783 : ℝ) / 784) := by
    dsimp [H', Q, H]
    simpa [hN] using Erdos113.closedWalkCount_interpolation_784 A
  have hrootid : H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hproot : p ≤ H ^ ((1 : ℝ) / 784) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ p ^ 784) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 784)
    convert h using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    norm_num
  have hHp : H' * p ≤ Q * H := by
    calc
      H' * p ≤ (Q * H ^ ((783 : ℝ) / 784)) * p := by gcongr
      _ ≤ (Q * H ^ ((783 : ℝ) / 784)) *
          H ^ ((1 : ℝ) / 784) := by gcongr
      _ = Q * (H ^ ((783 : ℝ) / 784) * H ^ ((1 : ℝ) / 784)) := by ring
      _ = Q * H := by rw [hrootid]
  have hDprod : D false * D true ≤ L ^ 2 * p := by
    calc
      D false * D true ≤ (L * d false) * (L * d true) :=
        mul_le_mul (hreg false) (hreg true) (hD true).le
          (mul_nonneg hL.le (hd false).le)
      _ = L ^ 2 * p := by dsimp [p]; ring
  have hfirst : 1568 *
      (∑ b : Bool, D b * t b * H') ≤ H / 2 := by
    have hden : 0 < 6272 * L ^ 2 * Q := by positivity
    have hcore : D false * D true * H' ≤ L ^ 2 * Q * H := by
      calc
        D false * D true * H' ≤ (L ^ 2 * p) * H' := by
          gcongr
        _ = L ^ 2 * (H' * p) := by ring
        _ ≤ L ^ 2 * (Q * H) := by gcongr
        _ = L ^ 2 * Q * H := by ring
    simp only [Fintype.sum_bool]
    dsimp [t]
    simp only [Bool.not_false, Bool.not_true]
    have hquot : (D false * D true * H') / (L ^ 2 * Q) ≤ H := by
      apply (div_le_iff₀ (by positivity : 0 < L ^ 2 * Q)).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcore
    have heq : 1568 *
        (D false * (D true / (6272 * L ^ 2 * Q)) * H' +
          D true * (D false / (6272 * L ^ 2 * Q)) * H') =
        (1 / 2 : ℝ) * ((D false * D true * H') / (L ^ 2 * Q)) := by
      field_simp
      <;> ring
    rw [show 1568 *
        (D true * (D false / (6272 * L ^ 2 * Q)) * H' +
          D false * (D true / (6272 * L ^ 2 * Q)) * H') =
        (1 / 2 : ℝ) * ((D false * D true * H') / (L ^ 2 * Q)) by
      simpa [add_comm] using heq]
    nlinarith
  have hcoef : 1568 * 784 *
      (∑ b : Bool, (α * D (!b)) * (t b)⁻¹) < (1 : ℝ) / 2 := by
    have hbound : α *
        (4 * 1568 * 784 * 6272 * L ^ 2 * Q) < 1 := by
      have hdenpos : 0 < 4 * 1568 * 784 * 6272 * L ^ 2 * Q := by positivity
      apply (lt_inv_mul_iff₀' hdenpos).mp
      simpa [Q] using hsmall
    simp only [Fintype.sum_bool]
    have htfalse : (t false)⁻¹ = (6272 * L ^ 2 * Q) / D true := by
      dsimp [t]
      rw [Bool.not_false]
      rw [inv_div]
    have httrue : (t true)⁻¹ = (6272 * L ^ 2 * Q) / D false := by
      dsimp [t]
      rw [Bool.not_true]
      rw [inv_div]
    have htermfalse : (α * D true) * (t false)⁻¹ =
        α * (6272 * L ^ 2 * Q) := by
      rw [htfalse]
      field_simp [(hD true).ne']
    have htermtrue : (α * D false) * (t true)⁻¹ =
        α * (6272 * L ^ 2 * Q) := by
      rw [httrue]
      field_simp [(hD false).ne']
    simp only [Bool.not_true, Bool.not_false]
    rw [htermtrue, htermfalse]
    nlinarith
  have hsecond : 1568 *
      (∑ b : Bool, 784 * (α * D (!b)) * (t b)⁻¹ * H) < H / 2 := by
    have heq : 1568 *
        (∑ b : Bool, 784 * (α * D (!b)) * (t b)⁻¹ * H) =
        (1568 * 784 * (∑ b : Bool, (α * D (!b)) * (t b)⁻¹)) * H := by
      simp only [Fintype.sum_bool]
      ring
    rw [heq]
    nlinarith
  have hbad := badClosedWalks1568_side_cast_le A R side t D
    (fun b ↦ α * D b) ht (fun b ↦ (hD b).le)
      (fun b ↦ mul_nonneg hα (hD b).le) hcross hmax hR hlocal
  have hbadlt : ((badClosedWalks1568 A R).card : ℝ) < H := by
    calc
      ((badClosedWalks1568 A R).card : ℝ) ≤
          1568 * ∑ b : Bool,
            (D b * t b * H' +
              784 * (α * D (!b)) * (t b)⁻¹ * H) := by
        simpa [H, H'] using hbad
      _ = 1568 * (∑ b : Bool, D b * t b * H') +
          1568 * (∑ b : Bool,
            784 * (α * D (!b)) * (t b)⁻¹ * H) := by
        simp only [Fintype.sum_bool]
        ring
      _ < H / 2 + H / 2 := add_lt_add_of_le_of_lt hfirst hsecond
      _ = H := by ring
  apply exists_pairwise_nonconflicting_column_cycle_of_badClosedWalks_lt
  dsimp [H] at hbadlt
  exact_mod_cast hbadlt



abbrev BlockedAuxiliaryColumnCycle (W : Type u) := Fin 98 → Fin 16 → W

noncomputable def blockedAuxiliaryColumnCycleEquiv (W : Type u) :
    BlockedAuxiliaryColumnCycle W ≃ (Column → W) :=
  (Equiv.curry (Fin 98) (Fin 16) W).symm.trans <|
    Equiv.arrowCongr (finProdFinEquiv.trans columnLinearEquiv.symm) (Equiv.refl W)

def evalBlockedAuxiliaryColumnCycle {W : Type u}
    (P : BlockedAuxiliaryColumnCycle W) (c : Column) : W :=
  P ⟨(columnLinearIndex c).val / 16, by
      have hc := (columnLinearIndex c).isLt
      omega⟩
    ⟨(columnLinearIndex c).val % 16, Nat.mod_lt _ (by omega)⟩

@[simp] lemma blockedAuxiliaryColumnCycleEquiv_apply {W : Type u}
    (P : BlockedAuxiliaryColumnCycle W) (c : Column) :
    blockedAuxiliaryColumnCycleEquiv W P c = evalBlockedAuxiliaryColumnCycle P c := by
  change Function.uncurry P (finProdFinEquiv.symm (columnLinearIndex c)) = _
  rw [finProdFinEquiv_symm_apply]
  rfl

def IsHomBlockedAuxiliaryColumnCycle {W : Type u}
    (A : SimpleGraph W) (P : BlockedAuxiliaryColumnCycle W) : Prop :=
  ∀ c, A.Adj (evalBlockedAuxiliaryColumnCycle P c)
    (evalBlockedAuxiliaryColumnCycle P (nextColumn c))

def HasBlockedAuxiliaryColumnConflict {W : Type u}
    (R : W → W → Prop) (P : BlockedAuxiliaryColumnCycle W) : Prop :=
  ∃ c d, c ≠ d ∧
    R (evalBlockedAuxiliaryColumnCycle P c) (evalBlockedAuxiliaryColumnCycle P d)

noncomputable def homAuxiliaryColumnCycles {W : Type u} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    Finset (BlockedAuxiliaryColumnCycle W) :=
  by classical exact Finset.univ.filter (IsHomBlockedAuxiliaryColumnCycle A)

noncomputable def badAuxiliaryColumnCycles {W : Type u} [Fintype W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Finset (BlockedAuxiliaryColumnCycle W) :=
  by classical exact
    (homAuxiliaryColumnCycles A).filter (HasBlockedAuxiliaryColumnConflict R)

@[simp] lemma mem_homAuxiliaryColumnCycles {W : Type u} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (P : BlockedAuxiliaryColumnCycle W) :
    P ∈ homAuxiliaryColumnCycles A ↔
      IsHomBlockedAuxiliaryColumnCycle A P := by
  classical
  simp [homAuxiliaryColumnCycles]

@[simp] lemma mem_badAuxiliaryColumnCycles {W : Type u} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : BlockedAuxiliaryColumnCycle W) :
    P ∈ badAuxiliaryColumnCycles A R ↔
      IsHomBlockedAuxiliaryColumnCycle A P ∧
      HasBlockedAuxiliaryColumnConflict R P := by
  classical
  simp [badAuxiliaryColumnCycles]

lemma exists_pairwise_nonconflicting_column_cycle_of_bad_lt_total
    {W : Type u} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hcard : (badAuxiliaryColumnCycles A R).card <
      (homAuxiliaryColumnCycles A).card) :
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d) := by
  classical
  have hnsubset : ¬ homAuxiliaryColumnCycles A ⊆ badAuxiliaryColumnCycles A R :=
    fun hsubset ↦ (Nat.not_le_of_lt hcard) (Finset.card_le_card hsubset)
  obtain ⟨P, hP, hPgood⟩ := Finset.not_subset.mp hnsubset
  have hPhom : IsHomBlockedAuxiliaryColumnCycle A P :=
    (mem_homAuxiliaryColumnCycles A P).mp hP
  refine ⟨evalBlockedAuxiliaryColumnCycle P, hPhom, ?_⟩
  intro c d hcd hR
  apply hPgood
  exact (mem_badAuxiliaryColumnCycles A R P).mpr ⟨hPhom, c, d, hcd, hR⟩

/-- The specialized clean-cycle selector distilled from Janzer's Lemmas
2.3--2.5.  It is kept as a proposition so the analytic counting proof can be
developed independently of the explicit witness and interleaving. -/
def CleanCycleSelector1568 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (α : ℝ),
    (∀ x y, R x y → R y x) →
    (∃ x y, A.Adj x y) →
    (∀ x y, ((relationNeighbors A R x y).card : ℝ) ≤ α * A.degree y) →
    α < cleanSelectorThreshold (Fintype.card W) →
    ∃ X : Column → W,
      (∀ c, A.Adj (X c) (X (nextColumn c))) ∧
      ∀ c d, c ≠ d → ¬ R (X c) (X d)

open Erdos113Regular Erdos113BipartiteGraph Erdos113CellPruning

theorem cleanCycleSelector1568_proof : CleanCycleSelector1568 := by
  intro W instFintype instDecEq A instDecAdj R instDecR α hR hedge hlocal hsmall
  let : Fintype W := instFintype
  let : DecidableEq W := instDecEq
  let : DecidableRel A.Adj := instDecAdj
  let : DecidableRel R := instDecR
  classical
  have hα : 0 ≤ α := by
    obtain ⟨x, y, hxy⟩ := hedge
    have hypos : 0 < A.degree y := by
      apply Finset.card_pos.mpr
      exact ⟨x, (A.mem_neighborFinset y x).mpr hxy.symm⟩
    have hloc := hlocal x y
    have hleft : (0 : ℝ) ≤ ((relationNeighbors A R x y).card : ℝ) := by positivity
    have hprod : 0 ≤ α * (A.degree y : ℝ) := hleft.trans hloc
    exact nonneg_of_mul_nonneg_left hprod (by exact_mod_cast hypos)
  obtain ⟨i, j, E, hEsub, hEne, _hEdense, hleftMin, hrightMin⟩ :=
    exists_pruned_cell A hedge
  let B := retainedGraph E
  let side : LiveLeft E ⊕ LiveRight E → Bool :=
    Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  let proj : LiveLeft E ⊕ LiveRight E → W :=
    Sum.elim (fun x ↦ x.1.1) (fun y ↦ y.1.1)
  let R' : (LiveLeft E ⊕ LiveRight E) →
      (LiveLeft E ⊕ LiveRight E) → Prop := fun x y ↦ R (proj x) (proj y)
  let : DecidableRel B.Adj := inferInstance
  let : DecidableRel R' := fun x y ↦ instDecR (proj x) (proj y)
  let L : ℝ := degreeBinCount (W := W)
  let cap : Bool → ℝ := fun b ↦ if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1)
  let d : Bool → ℝ := fun b ↦ cap b / (16 * L)
  have hLpos : 0 < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hcap : ∀ b, 0 < cap b := by
    intro b
    cases b <;> simp [cap] <;> positivity
  have hprojAdj {x y : LiveLeft E ⊕ LiveRight E} (hxy : B.Adj x y) :
      A.Adj (proj x) (proj y) := by
    rcases x with x | x <;> rcases y with y | y
    · exact False.elim hxy
    · have he : (x.1, y.1) ∈ E := hxy
      exact (mem_cellEdges A i j _).mp (hEsub he)
    · have he : (y.1, x.1) ∈ E := hxy
      exact ((mem_cellEdges A i j _).mp (hEsub he)).symm
    · exact False.elim hxy
  have hprojInjOnNeighbor (y : LiveLeft E ⊕ LiveRight E) :
      Set.InjOn proj (B.neighborSet y) := by
    intro x hx z hz hxz
    rcases y with y | y
    · rcases x with x | x
      · exact False.elim hx
      · rcases z with z | z
        · exact False.elim hz
        · congr 1
          apply Subtype.ext
          apply Subtype.ext
          exact hxz
    · rcases x with x | x
      · rcases z with z | z
        · congr 1
          apply Subtype.ext
          apply Subtype.ext
          exact hxz
        · exact False.elim hz
      · exact False.elim hx
  have hprojDegreeCap (x : LiveLeft E ⊕ LiveRight E) :
      (A.degree (proj x) : ℝ) ≤ cap (side x) := by
    rcases x with x | x
    · have hb := (degree_bounds_of_mem_bin A i x.1.2).2
      dsimp [proj, side, cap]
      exact_mod_cast hb.le
    · have hb := (degree_bounds_of_mem_bin A j x.1.2).2
      dsimp [proj, side, cap]
      exact_mod_cast hb.le
  have hdegreeCap (x : LiveLeft E ⊕ LiveRight E) :
      (B.degree x : ℝ) ≤ cap (side x) := by
    rcases x with x | x
    · rw [Erdos113BipartiteGraph.degree_inl]
      have hf := card_leftFiber_le_degree A i j E hEsub x.1
      have hb := (degree_bounds_of_mem_bin A i x.1.2).2
      dsimp [side, cap]
      exact_mod_cast hf.trans hb.le
    · rw [Erdos113BipartiteGraph.degree_inr]
      have hf := card_rightFiber_le_degree A i j E hEsub x.1
      have hb := (degree_bounds_of_mem_bin A j x.1.2).2
      dsimp [side, cap]
      exact_mod_cast hf.trans hb.le
  have hdegreeMin (x : LiveLeft E ⊕ LiveRight E) :
      d (side x) ≤ (B.degree x : ℝ) := by
    rcases x with x | x
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ leftFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(x.1, y), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_leftFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hleftMin x.1 hinc
      rw [Erdos113BipartiteGraph.degree_inl]
      dsimp [d, cap, side, L]
      have hmR : ((cellThreshold (2 ^ (i.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((leftFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold (cap := 2 ^ (i.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase
      simpa using hbase
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ rightFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(y, x.1), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_rightFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hrightMin x.1 hinc
      rw [Erdos113BipartiteGraph.degree_inr]
      dsimp [d, cap, side, L]
      have hmR : ((cellThreshold (2 ^ (j.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((rightFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold (cap := 2 ^ (j.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase
      simpa using hbase
  have hlocal' (x y : LiveLeft E ⊕ LiveRight E) :
      ((((B.neighborFinset y).filter (R' x)).card : ℕ) : ℝ) ≤
        α * cap (side y) := by
    let S := (B.neighborFinset y).filter (R' x)
    let T := (A.neighborFinset (proj y)).filter (R (proj x))
    have hinj : Set.InjOn proj S := by
      intro z hz w hw hzw
      apply hprojInjOnNeighbor y
      · exact (B.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1
      · exact (B.mem_neighborFinset y w).mp (Finset.mem_filter.mp hw).1
      · exact hzw
    have himage : S.image proj ⊆ T := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw' := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr
        ⟨(A.mem_neighborFinset (proj y) (proj w)).mpr
          (hprojAdj ((B.mem_neighborFinset y w).mp hw'.1)), hw'.2⟩
    calc
      (S.card : ℝ) = ((S.image proj).card : ℝ) := by
        congr 1
        exact (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card himage
      _ ≤ α * A.degree (proj y) := by
        simpa [T, relationNeighbors] using hlocal (proj x) (proj y)
      _ ≤ α * cap (side y) := by
        exact mul_le_mul_of_nonneg_left (hprojDegreeCap y) hα
  have hlocalR : ∀ x y,
      ((((B.neighborFinset y).filter (R' x)).card : ℕ) : ℝ) ≤
        α * cap (side y) := hlocal'
  have hcross : ∀ {x y}, B.Adj x y → side y = !side x := by
    intro x y hxy
    exact Erdos113BipartiteGraph.cross E hxy
  let : Nonempty (LiveLeft E ⊕ LiveRight E) :=
    Erdos113BipartiteGraph.nonempty_of_nonempty E hEne
  let N' : ℝ := Fintype.card (LiveLeft E ⊕ LiveRight E)
  have hcardN : Fintype.card (LiveLeft E ⊕ LiveRight E) ≤ 2 * Fintype.card W := by
    rw [Fintype.card_sum]
    have hleftCard : Fintype.card (LiveLeft E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveLeft E) ≤ Fintype.card (BinVertex A i) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    have hrightCard : Fintype.card (LiveRight E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveRight E) ≤ Fintype.card (BinVertex A j) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    omega
  have hNtwo : 2 ≤ Fintype.card W := by
    obtain ⟨x, y, hxy⟩ := hedge
    have hone : 1 < Fintype.card W :=
      Fintype.one_lt_card_iff.mpr ⟨x, y, hxy.ne⟩
    omega
  have hlogpos : 0 < Real.log (Fintype.card W : ℝ) :=
    Real.log_pos (by exact_mod_cast hNtwo)
  have hLlog : L ≤ 4 * Real.log (Fintype.card W : ℝ) := by
    let k := Nat.log 2 (Fintype.card W)
    have hpow := Nat.pow_log_le_self 2 (show Fintype.card W ≠ 0 by omega)
    have hpowpos : (0 : ℝ) < (2 : ℕ) ^ k := by positivity
    have hnpos : (0 : ℝ) < Fintype.card W := by positivity
    have hlogle := Real.strictMonoOn_log.monotoneOn
      (by exact hpowpos) (by exact hnpos) (by exact_mod_cast hpow)
    rw [Real.log_pow] at hlogle
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 :=
      (by nlinarith [Real.log_two_gt_d9])
    have hk : (0 : ℝ) ≤ k := by positivity
    have hkmul : (k : ℝ) * (1 / 2 : ℝ) ≤ (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlogtwo.le hk
    have hlogmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by
        change (0 : ℝ) < (Fintype.card W : ℝ)
        exact_mod_cast (show 0 < Fintype.card W by omega))
      (by exact_mod_cast hNtwo)
    have hkbound : (k : ℝ) / 2 ≤ Real.log (Fintype.card W : ℝ) := by
      calc
        (k : ℝ) / 2 = (k : ℝ) * (1 / 2) := by ring
        _ ≤ (k : ℝ) * Real.log 2 := hkmul
        _ ≤ Real.log (Fintype.card W : ℝ) := by simpa using hlogle
    have hone : (1 : ℝ) ≤ 2 * Real.log (Fintype.card W : ℝ) := by
      nlinarith
    change ((Nat.log 2 (Fintype.card W) + 1 : ℕ) : ℝ) ≤
      4 * Real.log (Fintype.card W : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    change (k : ℝ) + 1 ≤ 4 * Real.log (Fintype.card W : ℝ)
    nlinarith
  have hNroot : N' ^ ((1 : ℝ) / 784) ≤
      2 * (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
    have hN'nonneg : 0 ≤ N' := by dsimp [N']; positivity
    have hcast : N' ≤ 2 * (Fintype.card W : ℝ) := by
      dsimp [N']
      exact_mod_cast hcardN
    calc
      N' ^ ((1 : ℝ) / 784) ≤
          (2 * (Fintype.card W : ℝ)) ^ ((1 : ℝ) / 784) :=
        Real.rpow_le_rpow hN'nonneg hcast (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 784) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
        rw [Real.mul_rpow] <;> positivity
      _ ≤ 2 * (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hdenom :
      4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
          N' ^ ((1 : ℝ) / 784) ≤
        2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by
    let l := Real.log (Fintype.card W : ℝ)
    let q := (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784)
    have hl : 0 < l := hlogpos
    have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hLsq : L ^ 2 ≤ 16 * l ^ 2 := by
      dsimp [l]
      nlinarith [sq_nonneg (4 * Real.log (Fintype.card W : ℝ) - L)]
    have hlogsq : (1 : ℝ) ≤ 512 * l ^ 2 := by
      have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      have hlogmono := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
        (by
          change (0 : ℝ) < (Fintype.card W : ℝ)
          exact_mod_cast (show 0 < Fintype.card W by omega))
        (by exact_mod_cast hNtwo)
      dsimp [l]
      nlinarith
    calc
      4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
          N' ^ ((1 : ℝ) / 784) =
          2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * L ^ 2 *
            N' ^ ((1 : ℝ) / 784) := by
        norm_num
        left
        ring
      _ ≤ 2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * (16 * l ^ 2) *
          N' ^ ((1 : ℝ) / 784) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hLsq
          positivity
        · exact Real.rpow_nonneg (by dsimp [N']; positivity) _
      _ ≤ 2 ^ (14 : ℕ) * 784 ^ (3 : ℕ) * (16 * l ^ 2) * (2 * q) := by
        apply mul_le_mul_of_nonneg_left hNroot
        positivity
      _ = 2 ^ (19 : ℕ) * 784 ^ (3 : ℕ) * l ^ 2 * q := by
        norm_num
        ring
      _ ≤ (512 * l ^ 2) *
          (2 ^ (19 : ℕ) * 784 ^ (3 : ℕ) * l ^ 2 * q) := by
        have hc : 0 ≤ (2 ^ (19 : ℕ) : ℝ) * 784 ^ (3 : ℕ) * l ^ 2 * q := by
          positivity
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hlogsq hc
      _ = 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) * l ^ (4 : ℕ) * q := by
        norm_num
        ring
      _ = 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
          Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
          (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := rfl
  have hsmall' : α <
      (4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
        N' ^ ((1 : ℝ) / 784))⁻¹ := by
    have hbigpos : 0 < 2 ^ (28 : ℕ) * 784 ^ (3 : ℕ) *
        Real.log (Fintype.card W : ℝ) ^ (4 : ℕ) *
        (Fintype.card W : ℝ) ^ ((1 : ℝ) / 784) := by positivity
    have hsmallpos : 0 < 4 * 1568 * 784 * 6272 * (16 * L) ^ 2 *
        N' ^ ((1 : ℝ) / 784) := by
      have hN'pos : 0 < N' := by dsimp [N']; positivity
      positivity
    apply hsmall.trans_le
    apply (inv_le_inv₀ hbigpos hsmallpos).2
    simpa [cleanSelectorThreshold] using hdenom
  obtain ⟨X, hXadj, hXfree⟩ := exists_cleanCycle_of_bipartiteAlmostRegular
    B R' (fun x y h ↦ hR _ _ h) side d cap N' (16 * L) α rfl
    (fun b ↦ by dsimp [d]; positivity) hcap (by positivity) hα hcross
    hdegreeMin hdegreeCap (fun b ↦ by
      dsimp [d]
      field_simp
      exact le_rfl) hlocalR hsmall'
  refine ⟨fun c ↦ proj (X c), ?_, ?_⟩
  · intro c
    exact hprojAdj (hXadj c)
  · intro c e hce hconf
    exact hXfree c e hce hconf



lemma auxiliaryGraph_adj_compatible {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) {y z : SliceTuple V}
    (h : (auxiliaryGraph G C hfamily).Adj y z) : CompatibleSlices G y z := by
  rcases h with h | h
  · exact compatibleSlices_of_interleavedCycle G y z (hfamily _ h)
  · exact (compatibleSlices_of_interleavedCycle G z y (hfamily _ h)).symm

lemma auxiliaryGraph_adj_left_injective {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x) {y z : SliceTuple V}
    (h : (auxiliaryGraph G C hfamily).Adj y z) : Function.Injective y := by
  rcases h with h | h
  · have hinj := evalSliceCoordinate_injective_of_interleavedCycle (hfamily _ h)
    intro r s hrs
    have hp : (true, r) = (true, s) := hinj (by
      simpa [evalSliceCoordinate] using hrs)
    exact congrArg Prod.snd hp
  · have hinj := evalSliceCoordinate_injective_of_interleavedCycle (hfamily _ h)
    intro r s hrs
    have hp : (false, r) = (false, s) := hinj (by
      simpa [evalSliceCoordinate] using hrs)
    exact congrArg Prod.snd hp

/-- The Erdős--Simonovits assertion from Problem 113. -/
def ErdosSimonovitsConjecture : Prop :=
  ∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
    H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)

/-- Vertex type of Janzer's graph `H_{7,784}`. -/
abbrev Vertex := Row × Column

def matchingVertex (v : Vertex) : Vertex := (matchingRow v.1, v.2)

def nextVertex (v : Vertex) : Vertex := (turnRow v.1, nextColumn v.2)

def prevVertex (v : Vertex) : Vertex := (turnRow v.1, prevColumn v.2)

lemma matchingRow_involutive : Function.Involutive matchingRow := by
  intro r
  cases r with
  | mk i b => cases b <;> rfl

lemma nextColumn_prevColumn (c : Column) : nextColumn (prevColumn c) = c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn, prevColumn]

lemma prevColumn_nextColumn (c : Column) : prevColumn (nextColumn c) = c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn, prevColumn]

lemma matchingVertex_involutive : Function.Involutive matchingVertex := by
  intro v
  simp [matchingVertex, matchingRow_involutive v.1]

lemma nextVertex_prevVertex (v : Vertex) : nextVertex (prevVertex v) = v := by
  change (turnRow (turnRow v.1), nextColumn (prevColumn v.2)) = v
  rw [turnRow_involutive, nextColumn_prevColumn]

lemma prevVertex_nextVertex (v : Vertex) : prevVertex (nextVertex v) = v := by
  change (turnRow (turnRow v.1), prevColumn (nextColumn v.2)) = v
  rw [turnRow_involutive, prevColumn_nextColumn]

lemma matchingVertex_ne (v : Vertex) : matchingVertex v ≠ v := by
  intro h
  have hb := congrArg (fun w : Vertex ↦ w.1.2) h
  cases v.1.2 <;> simp [matchingVertex, matchingRow] at hb

lemma nextColumn_ne (c : Column) : nextColumn c ≠ c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [nextColumn]

lemma prevColumn_ne (c : Column) : prevColumn c ≠ c := by
  rcases c with ⟨j, b⟩
  cases b <;> simp [prevColumn]

lemma nextColumn_ne_prevColumn (c : Column) : nextColumn c ≠ prevColumn c := by
  have hone : (1 : ZMod 784) ≠ 0 := by decide
  rcases c with ⟨j, b⟩
  cases b
  · intro h
    have hj := congrArg Prod.fst h
    simp [nextColumn, prevColumn] at hj
    have hzero : (1 : ZMod 784) = 0 := by
      linear_combination hj
    exact hone hzero
  · intro h
    have hj := congrArg Prod.fst h
    simp [nextColumn, prevColumn] at hj
    exact hone hj

/-
The following three vertex-level nonfixed-point statements are kept separate
because they are also used to compute the degree exactly.
-/
lemma nextVertex_ne (v : Vertex) : nextVertex v ≠ v := by
  exact fun h ↦ nextColumn_ne v.2 (congrArg Prod.snd h)

lemma prevVertex_ne (v : Vertex) : prevVertex v ≠ v := by
  exact fun h ↦ prevColumn_ne v.2 (congrArg Prod.snd h)

/-- Janzer's graph `H_{7,784}`.  Its three neighbors at `v` are the matching
neighbor and the successor and predecessor in the nonmatching two-factor. -/
def janzerGraph : SimpleGraph Vertex where
  Adj v w := w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v
  symm := ⟨by
    intro v w h
    rcases h with h | h | h
    · left
      rw [h, matchingVertex_involutive]
    · right; right
      rw [h, prevVertex_nextVertex]
    · right; left
      rw [h, nextVertex_prevVertex]
    ⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h | h
    · exact matchingVertex_ne v h.symm
    · exact nextVertex_ne v h.symm
    · exact prevVertex_ne v h.symm
    ⟩

instance : DecidableRel janzerGraph.Adj := fun v w ↦ by
  change Decidable (w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v)
  infer_instance

lemma janzerGraph_neighborFinset (v : Vertex) :
    janzerGraph.neighborFinset v = {matchingVertex v, nextVertex v, prevVertex v} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  change (w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]

lemma matchingVertex_ne_nextVertex (v : Vertex) : matchingVertex v ≠ nextVertex v := by
  intro h
  exact nextColumn_ne v.2 (congrArg Prod.snd h).symm

lemma matchingVertex_ne_prevVertex (v : Vertex) : matchingVertex v ≠ prevVertex v := by
  intro h
  exact prevColumn_ne v.2 (congrArg Prod.snd h).symm

lemma nextVertex_ne_prevVertex (v : Vertex) : nextVertex v ≠ prevVertex v := by
  exact fun h ↦ nextColumn_ne_prevColumn v.2 (congrArg Prod.snd h)

theorem janzerGraph_regular : janzerGraph.IsRegularOfDegree 3 := by
  intro v
  rw [← janzerGraph.card_neighborFinset_eq_degree, janzerGraph_neighborFinset]
  simp [matchingVertex_ne_nextVertex v, matchingVertex_ne_prevVertex v,
    nextVertex_ne_prevVertex v]

/-- The row contribution to the bipartite coloring. -/
def rowColor (r : Row) : Bool := decide (r.1.val % 2 = 1) != r.2

/-- The explicit two-coloring of `H_{7,784}`. -/
def vertexColorBool (v : Vertex) : Bool := rowColor v.1 != v.2.2

lemma rowColor_matchingRow (r : Row) : rowColor (matchingRow r) = !rowColor r := by
  decide +revert

lemma rowColor_turnRow (r : Row) : rowColor (turnRow r) = rowColor r := by
  decide +revert

lemma vertexColorBool_matchingVertex (v : Vertex) :
    vertexColorBool (matchingVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, c⟩
  simp only [vertexColorBool, matchingVertex, rowColor_matchingRow]
  cases rowColor r <;> cases c.2 <;> decide

lemma vertexColorBool_nextVertex (v : Vertex) :
    vertexColorBool (nextVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, j, b⟩
  simp only [vertexColorBool, nextVertex, rowColor_turnRow]
  cases rowColor r <;> cases b <;> simp [nextColumn]

lemma vertexColorBool_prevVertex (v : Vertex) :
    vertexColorBool (prevVertex v) = !vertexColorBool v := by
  rcases v with ⟨r, j, b⟩
  simp only [vertexColorBool, prevVertex, rowColor_turnRow]
  cases rowColor r <;> cases b <;> simp [prevColumn]

def vertexColor (v : Vertex) : Fin 2 := if vertexColorBool v then 1 else 0

theorem janzerGraph_bipartite : janzerGraph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk vertexColor ?_⟩
  intro v w h
  rcases h with rfl | rfl | rfl
  · simp only [vertexColor]
    rw [vertexColorBool_matchingVertex]
    cases vertexColorBool v <;> decide
  · simp only [vertexColor]
    rw [vertexColorBool_nextVertex]
    cases vertexColorBool v <;> decide
  · simp only [vertexColor]
    rw [vertexColorBool_prevVertex]
    cases vertexColorBool v <;> decide

theorem janzerGraph_not_twoDegenerate : ¬ IsTwoDegenerate janzerGraph := by
  classical
  intro h
  obtain ⟨v, hv⟩ := h Set.univ Set.univ_nonempty
  have hncard : (janzerGraph.neighborSet (v : Vertex)).ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card']
    change janzerGraph.degree (v : Vertex) = 3
    exact janzerGraph_regular v
  simp only [Set.inter_univ] at hv
  omega

/-! ### From a clean auxiliary cycle to a copy of `H_{7,784}` -/

/-- A conflict-free cyclic traversal of the auxiliary graph.  Conflict-free
means that no two row coordinates selected anywhere on the cycle coincide. -/
structure IsCleanAuxiliaryColumnCycle {V : Type*}
    (A : SimpleGraph (SliceTuple V)) (X : Column → SliceTuple V) : Prop where
  injective : Function.Injective (fun v : Vertex ↦ X v.2 v.1)
  adjacent : ∀ c, A.Adj (X c) (X (nextColumn c))

/-- This is the output format of the clean-cycle selector: consecutive
auxiliary vertices are adjacent and distinct positions share no coordinate. -/
structure IsPairwiseNonconflictingAuxiliaryColumnCycle {V : Type*}
    (A : SimpleGraph (SliceTuple V)) (X : Column → SliceTuple V) : Prop where
  adjacent : ∀ c, A.Adj (X c) (X (nextColumn c))
  nonconflicting : ∀ c d, c ≠ d → ¬ SlicesConflict (X c) (X d)

lemma IsPairwiseNonconflictingAuxiliaryColumnCycle.toClean
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Finset (CycleTuple V)}
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x)
    {X : Column → SliceTuple V}
    (h : IsPairwiseNonconflictingAuxiliaryColumnCycle
      (auxiliaryGraph G C hfamily) X) :
    IsCleanAuxiliaryColumnCycle (auxiliaryGraph G C hfamily) X := by
  refine ⟨?_, h.adjacent⟩
  rintro ⟨r, c⟩ ⟨s, d⟩ hrs
  by_cases hcd : c = d
  · subst d
    have hinj := auxiliaryGraph_adj_left_injective hfamily (h.adjacent c)
    have hrs' : r = s := hinj hrs
    simp [hrs']
  · exact (h.nonconflicting c d hcd ⟨r, s, hrs⟩).elim

/-- A cyclic list of row-slices is clean if consecutive slices generate
members of `C` and all `14 · 2 · 1568` selected host vertices are distinct. -/
structure IsCleanSliceCycle {V : Type*} (G : SimpleGraph V)
    (X : Column → SliceTuple V) : Prop where
  injective : Function.Injective (fun v : Vertex ↦ X v.2 v.1)
  compatible : ∀ c, CompatibleSlices G (X c) (X (nextColumn c))

/-- Janzer's interleaving has exactly the adjacency pattern needed to embed
the explicit graph once a clean auxiliary `1568`-cycle has been selected. -/
theorem copy_of_cleanSliceCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Column → SliceTuple V)
    (hclean : IsCleanSliceCycle G X) :
    janzerGraph ⊑ G := by
  refine ⟨⟨⟨fun v ↦ X v.2 v.1, ?_⟩, hclean.injective⟩⟩
  intro v w hvw
  change w = matchingVertex v ∨ w = nextVertex v ∨ w = prevVertex v at hvw
  rcases hvw with rfl | rfl | rfl
  · exact (hclean.compatible v.2).1 v.1
  · exact (hclean.compatible v.2).2.2 v.1
  · have hp := (hclean.compatible (prevColumn v.2)).2.2 (turnRow v.1)
    rw [nextColumn_prevColumn, turnRow_involutive] at hp
    exact hp.symm

theorem copy_of_cleanAuxiliaryColumnCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (CycleTuple V))
    (hfamily : ∀ x ∈ C, IsGenuineCycleTuple G x)
    (X : Column → SliceTuple V)
    (hclean : IsCleanAuxiliaryColumnCycle (auxiliaryGraph G C hfamily) X) :
    janzerGraph ⊑ G := by
  apply copy_of_cleanSliceCycle G X
  refine ⟨hclean.injective, ?_⟩
  intro c
  exact auxiliaryGraph_adj_compatible hfamily (hclean.adjacent c)

theorem IsNiceCycleFamily.janzerGraph_isContained_of_cleanCycleSelector
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hnice : IsNiceCycleFamily G β C) (hβ : 0 ≤ β) (hC : C.Nonempty)
    (hselector : CleanCycleSelector1568.{u})
    (hsmall : 1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  let A := auxiliaryGraph G C hnice.genuine
  have hedge : ∃ y z, A.Adj y z := by
    obtain ⟨x, hx⟩ := hC
    refine ⟨sliceOfCycle true x, sliceOfCycle false x, ?_⟩
    left
    simpa [A, interleavedCycle_sliceOfCycle] using hx
  have hlocal : ∀ x y,
      ((relationNeighbors A SlicesConflict x y).card : ℝ) ≤
        (1568 * β) * A.degree y := by
    intro x y
    simpa only [A, relationNeighbors, conflictingNeighbors] using
      hnice.auxiliary_conflicting_neighbors_bound hβ x y
  obtain ⟨X, hXadj, hXconflict⟩ :=
    hselector (SliceTuple V) A SlicesConflict (1568 * β)
      (fun _ _ h ↦ h.symm) hedge hlocal hsmall
  apply copy_of_cleanAuxiliaryColumnCycle G C hnice.genuine X
  apply IsPairwiseNonconflictingAuxiliaryColumnCycle.toClean hnice.genuine
  exact ⟨hXadj, hXconflict⟩

theorem IsGoodCycleFamily.janzerGraph_isContained
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {β : ℝ} {C : Finset (CycleTuple V)}
    (hgood : IsGoodCycleFamily G β C) (hβ : 0 < β) (hC : C.Nonempty)
    (hsmall : 1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  obtain ⟨C', hC'sub, hC'nonempty, hnice⟩ :=
    hgood.exists_nice_subfamily hβ hC
  exact hnice.janzerGraph_isContained_of_cleanCycleSelector
    hβ.le hC'nonempty cleanCycleSelector1568_proof hsmall

theorem janzerGraph_isContained_of_fewFourCycle_numerics
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 0 < s) (β Q D t₀ t₂ : ℝ)
    (hβ : 0 < β) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (ht₀ : 0 < t₀) (ht₂ : 0 < t₂)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤ Q)
    (hclosed : 0 < (Conflict.closedWalkCount G 56 : ℝ))
    (hbad :
      56 * (D * t₀ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        28 * t₀⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
      56 * (D * t₂ *
          ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
            (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
        (Q / s) * t₂⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2)
    (hpattern : (16 * 7 * s : ℝ) *
        (Fintype.card V * D ^ 53) ≤
      β * ((Conflict.closedWalkCount G 56 : ℝ) / 2))
    (hsmall : 1568 * β < cleanSelectorThreshold
      (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  let C := controlledGenuineCycles G s
  have hgood : IsGoodCycleFamily G β C :=
    fewFourCycleGoodFamily_of_numerics G s hs β Q D t₀ t₂
      hβ.le hQ hD ht₀ ht₂ hdeg hcap hbad hpattern
  have hcard : 0 < (C.card : ℝ) := by
    have hlower := controlledGenuineCycles_half_closedWalkCount_of_numerics
      G s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hdeg hcap hbad
    linarith
  have hC : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hCempty
    simp [C, hCempty] at hcard
  exact hgood.janzerGraph_isContained hβ hC hsmall

theorem janzerGraph_isContained_of_fewFourCycle_bipartite_numerics
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (s : ℕ) (β : ℝ)
    (Q D t₀ t₂ : Bool → ℝ)
    (hs : 0 < s) (hβ : 0 < β)
    (hQ : ∀ b, 0 ≤ Q b) (hD : ∀ b, 0 ≤ D b)
    (ht₀ : ∀ b, 0 < t₀ b) (ht₂ : ∀ b, 0 < t₂ b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hcap : ∀ u y, G.Adj y u →
      ((Erdos113FourCycles.extensionsThroughEdge G u y).card : ℝ) ≤
        Q (side y))
    (hclosed : 0 < (Conflict.closedWalkCount G 56 : ℝ))
    (hbad :
      56 * ∑ b : Bool,
          (D b * t₀ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * (Conflict.closedWalkCount G 56 : ℝ)) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 28) *
                (Conflict.closedWalkCount G 56 : ℝ) ^ ((27 : ℝ) / 28)) +
            (Q (!b) / s) * (t₂ b)⁻¹ *
              (Conflict.closedWalkCount G 56 : ℝ)) ≤
        (Conflict.closedWalkCount G 56 : ℝ) / 2)
    (hpattern : (16 * 7 * s : ℝ) *
        (2 * G.edgeFinset.card * (D false * D true) ^ 26) ≤
      β * ((Conflict.closedWalkCount G 56 : ℝ) / 2))
    (hsmall : 1568 * β < cleanSelectorThreshold
      (Fintype.card (SliceTuple V))) :
    janzerGraph ⊑ G := by
  let C := controlledGenuineCycles G s
  have hhalf := controlledGenuineCycles_half_closedWalkCount_bipartite_of_numerics
    G side s hs Q D t₀ t₂ hQ hD ht₀ ht₂ hcross hdeg hcap hclosed hbad
  have hgood : IsGoodCycleFamily G β C :=
    controlledGenuineCycles_isGood_bipartite_edges
      G side D hD hcross hdeg s hs β
        ((Conflict.closedWalkCount G 56 : ℝ) / 2) hβ.le hhalf hpattern
  have hC : C.Nonempty := by
    have hcardpos : 0 < (C.card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast hcardpos)
  exact hgood.janzerGraph_isContained hβ hC hsmall

/-! ## Quantitative data from the two dyadic selections -/

open Erdos113FourCycleSelection Erdos113AnchorConstruction

lemma codegree_le_degree_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    Erdos113FourCycles.codegree G u v ≤ G.degree u := by
  rw [Erdos113FourCycles.codegree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

lemma FirstSelection.scale_le_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) :
    2 ^ S.scaleIndex.val ≤ G.maxDegree := by
  obtain ⟨p, hp⟩ := S.triples_nonempty
  have hd := S.data hp
  exact hd.2.2.2.2.2.2.2.1.trans
    ((codegree_le_degree_left G S.anchor p.middle).trans
      (G.degree_le_maxDegree S.anchor))

lemma FirstSelection.SecondSelection.secondScale_lt_twice_firstScale
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    2 ^ R.index.val < 2 * 2 ^ S.scaleIndex.val := by
  obtain ⟨p, hp⟩ := R.bucket_nonempty
  have hb := S.secondDyadicTriples_count_bounds hp
  exact hb.1.trans_lt (by
    simpa [pow_succ, Nat.mul_comm] using
      S.middleCount_lt_scaleCap_at_triple p)

lemma FirstSelection.SecondSelection.auxiliary_edge_card_le_square
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    (S.auxiliaryGraph R.index).edgeFinset.card ≤
      Fintype.card (NeighborVertex G S.anchor) ^ 2 := by
  calc
    (S.auxiliaryGraph R.index).edgeFinset.card ≤
        (Fintype.card (NeighborVertex G S.anchor)).choose 2 :=
      (S.auxiliaryGraph R.index).card_edgeFinset_le_card_choose_two
    _ ≤ Fintype.card (NeighborVertex G S.anchor) ^ 2 := by
      rw [Nat.choose_two_right]
      have hsub : Fintype.card (NeighborVertex G S.anchor) - 1 ≤
          Fintype.card (NeighborVertex G S.anchor) := by omega
      exact (Nat.div_le_self _ _).trans (by
        simpa [pow_two] using Nat.mul_le_mul_left
          (Fintype.card (NeighborVertex G S.anchor)) hsub)

lemma FirstSelection.SecondSelection.selection_count_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}
    (S : FirstSelection G side) (R : S.SecondSelection) :
    (Erdos113Cycles.genuineCycles G 4).card ≤
      32 * Fintype.card V *
        (Nat.log 2 (Fintype.card V) + 1) ^ 2 *
        2 ^ R.index.val *
        (S.auxiliaryGraph R.index).edgeFinset.card := by
  let m := Fintype.card V
  let L := Nat.log 2 m + 1
  let T := S.triples.card
  let f := (S.auxiliaryGraph R.index).edgeFinset.card
  let b := 2 ^ R.index.val
  have hactive :
      (Erdos113FourCycleSelection.activeSideVertices
        G side S.anchorSide).card ≤ m :=
    Finset.card_le_univ _
  have hfirst : (Erdos113Cycles.genuineCycles G 4).card ≤
      4 * m * L * T := by
    calc
      (Erdos113Cycles.genuineCycles G 4).card ≤
          4 * (Erdos113FourCycleSelection.activeSideVertices
            G side S.anchorSide).card * L * T := by
        simpa [m, L, T] using S.many
      _ ≤ 4 * m * L * T := by gcongr
  have hlog :
      Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1 ≤ 2 * L := by
    rw [Nat.log_pow (by omega : 1 < 2)]
    have hi : S.scaleIndex.val + 1 ≤ L := by
      simpa [L, m] using S.scaleIndex.isLt
    have hLpos : 0 < L := by dsimp [L]; omega
    omega
  have hsecond : T ≤ 8 * L * b * f := by
    have hpow : 2 ^ (R.index.val + 2) = 4 * b := by
      dsimp [b]
      ring
    calc
      T ≤ (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
            2 ^ (R.index.val + 2) * f := by
        simpa [T, f] using R.many
      _ ≤ (2 * L) * 2 ^ (R.index.val + 2) * f := by
        gcongr
      _ = (2 * L) * (4 * b) * f := by rw [hpow]
      _ = 8 * L * b * f := by ring
  calc
    (Erdos113Cycles.genuineCycles G 4).card ≤ 4 * m * L * T := hfirst
    _ ≤ 4 * m * L * (8 * L * b * f) := by gcongr
    _ = 32 * m * L ^ 2 * b * f := by ring

lemma cleanSelectorThreshold_slice_mono {n m : ℕ}
    (hn : 2 ≤ n) (hnm : n ≤ m) :
    cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))) ≤
      cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) := by
  rw [card_sliceTuple_fin, card_sliceTuple_fin, cleanSelectorThreshold,
    cleanSelectorThreshold]
  have hpowNat : n ^ 28 ≤ m ^ 28 := pow_le_pow_left' hnm 28
  have hpowReal : ((n ^ 28 : ℕ) : ℝ) ≤ (m ^ 28 : ℕ) := by
    exact_mod_cast hpowNat
  have hnPowPos : (0 : ℝ) < (n ^ 28 : ℕ) := by positivity
  have hlog : Real.log (n ^ 28 : ℕ) ≤ Real.log (m ^ 28 : ℕ) :=
    Real.log_le_log hnPowPos hpowReal
  have hlogn : 0 ≤ Real.log (n ^ 28 : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n ^ 28 by
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  have hlognpos : 0 < Real.log (n ^ 28 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n ^ 28 by
      exact one_lt_pow₀ (by omega : 1 < n) (by norm_num : (28 : ℕ) ≠ 0))
  have hrpow : ((n ^ 28 : ℕ) : ℝ) ^ ((1 : ℝ) / 784) ≤
      ((m ^ 28 : ℕ) : ℝ) ^ ((1 : ℝ) / 784) :=
    Real.rpow_le_rpow (by positivity) hpowReal (by norm_num)
  apply inv_anti₀
  · positivity
  · gcongr

/-! ## The exact host-embedding boundary -/

/-- At order `n`, every host with more than `n^(31/21)` edges contains the
fixed Janzer graph.  Janzer's combinatorial argument proves this eventually. -/
def JanzerHostEmbeddingAt (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ ((31 : ℝ) / 21) < (G.edgeFinset.card : ℝ) →
      janzerGraph ⊑ G

/-- The host-embedding formulation is exactly strong enough to imply the
eventual extremal-number estimate; this is the formal version of the final
sentence in the proof of Janzer's Theorem 1.6. -/
lemma hasExtremalBound_of_eventually_janzerHostEmbedding
    (h : ∀ᶠ n : ℕ in atTop, JanzerHostEmbeddingAt n) :
    HasExtremalBound ((31 : ℝ) / 21) janzerGraph := by
  apply hasExtremalBound_of_eventually_le
  filter_upwards [h] with n hn
  by_contra! hex
  have hnonneg : 0 ≤ (n : ℝ) ^ ((31 : ℝ) / 21) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hex' : (n : ℝ) ^ ((31 : ℝ) / 21) <
      (SimpleGraph.extremalNumber (Fintype.card (Fin n)) janzerGraph : ℝ) := by
    simpa using hex
  have hlt :=
    (SimpleGraph.lt_extremalNumber_iff_of_nonneg
      (V := Fin n) janzerGraph hnonneg).mp hex'
  obtain ⟨G, _, hfree, hedge⟩ := hlt
  exact hfree (hn G hedge)

/-! ## Logical assembly

The sole remaining mathematical input after the explicit construction is
Janzer's extremal estimate.  This lemma records the exact reduction, without
adding the estimate as an assumption to the final theorem. -/

lemma not_erdosSimonovitsConjecture_of_janzer_bound
    (h : HasExtremalBound ((31 : ℝ) / 21) janzerGraph) :
    ¬ ErdosSimonovitsConjecture := by
  intro hconj
  have hiff := hconj Vertex janzerGraph janzerGraph_bipartite
  exact janzerGraph_not_twoDegenerate
    (hiff.mp (hasThreeHalvesExtremalBound_of_thirtyOne_div_twentyOne h))

open scoped BigOperators

open Erdos113AlmostRegular Erdos113HostCell Erdos113HostPruning
  Erdos113HostAsymptotics Erdos113CyclePruning Erdos113FourCycleSelection
  Erdos113Regular Erdos113AnchorConstruction Erdos113Cycles

lemma sparseCore_denseCell_common
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ H : DenseHostCell C.graph,
    let m := C.order
    let L := degreeBinCount (W := C.W)
    let d : ℝ := H.edges.card
    let d₀ := d / (64 * m * L)
    (m : ℝ) ^ ((31 : ℝ) / 21) < 512 * L ^ (2 : ℕ) * d ∧
    (m : ℝ) ^ ((10 : ℝ) / 21) < 32768 * L ^ (3 : ℕ) * d₀ ∧
    (∀ b, (H.sideCap b : ℝ) ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21)) ∧
    (∀ b, d₀ ≤ sideMinimum H b) := by
  let : Fintype C.W := C.fintypeW
  let : DecidableEq C.W := C.decEqW
  let : DecidableRel C.graph.Adj := C.decAdj
  intro H
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let d : ℝ := H.edges.card
  let d₀ := d / (64 * m * L)
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hedgeCore : (m : ℝ) ^ ((31 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d := by
    have hlower := C.edge_lower
    have hdense : (C.graph.edgeFinset.card : ℝ) <
        8 * (L : ℝ) ^ (2 : ℕ) * d := by
      have hdense0 : (C.graph.edgeFinset.card : ℝ) <
          ((8 * L ^ 2 * H.edges.card : ℕ) : ℝ) := by
        exact_mod_cast H.dense
      norm_num [Nat.cast_mul, Nat.cast_pow, d] at hdense0 ⊢
      simpa using hdense0
    calc
      (m : ℝ) ^ ((31 : ℝ) / 21) =
          64 * ((m : ℝ) ^ ((31 : ℝ) / 21) / 64) := by ring
      _ ≤ 64 * C.graph.edgeFinset.card := by
        gcongr
        simpa [m, SparseCore.order] using hlower
      _ < 64 * (8 * (L : ℝ) ^ (2 : ℕ) * d) := by gcongr
      _ = 512 * (L : ℝ) ^ (2 : ℕ) * d := by ring
  have hd₀ : (m : ℝ) ^ ((10 : ℝ) / 21) <
      32768 * (L : ℝ) ^ (3 : ℕ) * d₀ := by
    have hid : (m : ℝ) ^ ((31 : ℝ) / 21) =
        (m : ℝ) ^ ((10 : ℝ) / 21) * m := by
      calc
        (m : ℝ) ^ ((31 : ℝ) / 21) =
            (m : ℝ) ^ ((10 : ℝ) / 21 + 1) := by norm_num
        _ = (m : ℝ) ^ ((10 : ℝ) / 21) * (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_add hmpos _ _
        _ = _ := by rw [Real.rpow_one]
    rw [hid] at hedgeCore
    dsimp [d₀]
    rw [show 32768 * (L : ℝ) ^ (3 : ℕ) *
        (d / (64 * m * L)) = 512 * (L : ℝ) ^ (2 : ℕ) * d / m by
      field_simp
      ring]
    exact (lt_div_iff₀ hmpos).2 (by simpa [mul_comm] using hedgeCore)
  have hcap (b : Bool) : (H.sideCap b : ℝ) ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    have h₁ : H.sideCap b ≤ 2 * C.graph.maxDegree := H.sideCap_le_two_maxDegree b
    have h₂ := C.maxDegree_upper
    have h₁R : (H.sideCap b : ℝ) ≤ 2 * C.graph.maxDegree := by
      exact_mod_cast h₁
    exact h₁R.trans (by
      calc
        (2 : ℝ) * C.graph.maxDegree ≤
            2 * ((regularFactor + 1 : ℕ) *
              (m : ℝ) ^ ((10 : ℝ) / 21)) := by
          gcongr
          simpa [SparseCore.maximumDegree, m] using h₂
        _ = _ := by ring)
  have hd₀min (b : Bool) : d₀ ≤ sideMinimum H b := by
    have hedgeCap : H.edges.card ≤ m * H.sideCap b := by
      simpa [m, SparseCore.order] using H.edge_card_le_card_mul_sideCap b
    have hedgeCapR : d ≤ (m : ℝ) * H.sideCap b := by
      have hedgeCap0 : (H.edges.card : ℝ) ≤
          ((m * H.sideCap b : ℕ) : ℝ) := by exact_mod_cast hedgeCap
      norm_num [Nat.cast_mul, d] at hedgeCap0 ⊢
      simpa using hedgeCap0
    dsimp [d₀, sideMinimum]
    norm_num [Nat.cast_mul]
    change d / (64 * (m : ℝ) * L) ≤
      (H.sideCap b : ℝ) / (64 * (L : ℝ))
    rw [show d / ((64 : ℝ) * m * L) = (d / m) / (64 * L) by
      field_simp]
    apply (div_le_div_iff_of_pos_right (by positivity :
      (0 : ℝ) < 64 * (L : ℝ))).2
    apply (div_le_iff₀ hmpos).2
    simpa [mul_comm] using hedgeCapR
  simpa [m, L, d, d₀] using And.intro hedgeCore
    (And.intro hd₀ (And.intro hcap hd₀min))

lemma low_ready_inputs
    (m n e : ℕ) (d₀ Q : ℝ) (D : Bool → ℝ)
    (hm : 64 ≤ m) (hready : HostPowerReady m)
    (hn : n ≤ m)
    (hDnonneg : ∀ b, 0 ≤ D b)
    (hDcap : ∀ b, D b ≤
      2 * (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21))
    (hedge : ∀ b, (e : ℝ) ≤ (m : ℝ) * D b)
    (hd₀ : (m : ℝ) ^ ((10 : ℝ) / 21) <
      32768 * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ (3 : ℕ) * d₀)
    (hQ : Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4) :
    let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
    let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
    let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
    let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
    (0 < s) ∧
    (∀ b, 896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ)) ∧
    (∀ b, 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ)) ∧
    (∀ b, 896 * 28 * (t₀ b)⁻¹ ≤ 1) ∧
    (∀ b, 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1) ∧
    (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
      β * d₀ ^ (56 : ℕ) := by
  let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
  let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
  let L : ℝ := (Nat.log 2 m + 1 : ℕ)
  let R : ℝ := regularFactor + 1
  have hmpos : (0 : ℝ) < m := by positivity
  have hmone : (1 : ℝ) ≤ m := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hLpos : 0 < L := by dsimp [L]; positivity
  change (m : ℝ) ^ ((10 : ℝ) / 21) <
    32768 * L ^ (3 : ℕ) * d₀ at hd₀
  have hd₀pos : 0 < d₀ := by
    have hright : 0 < 32768 * L ^ (3 : ℕ) * d₀ :=
      (Real.rpow_pos_of_pos hmpos _).trans hd₀
    have hc : 0 < (32768 * L ^ (3 : ℕ) : ℝ) := by positivity
    have hprod : 0 < (32768 * L ^ (3 : ℕ)) * d₀ := by
      simpa only [mul_assoc] using hright
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact (not_lt_of_ge hc.le h.1).elim
  have hsLower : (m : ℝ) ^ ((2 : ℝ) / 7) ≤ s := by
    exact Nat.le_ceil _
  have hsUpper : (s : ℝ) ≤ 2 * (m : ℝ) ^ ((2 : ℝ) / 7) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg hmpos.le ((2 : ℝ) / 7))
    have hone : 1 ≤ (m : ℝ) ^ ((2 : ℝ) / 7) :=
      Real.one_le_rpow hmone (by norm_num)
    dsimp [s]
    linarith
  have hspos : 0 < s := by
    rw [show s = ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊ by rfl,
      Nat.ceil_pos]
    exact Real.rpow_pos_of_pos hmpos _
  have hnroot : (n : ℝ) ^ ((1 : ℝ) / 28) ≤
      (m : ℝ) ^ ((1 : ℝ) / 28) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hn
    · norm_num
  have hpowProduct :
      (m : ℝ) ^ ((10 : ℝ) / 21) *
          (m : ℝ) ^ ((3 : ℝ) / 8) *
          (m : ℝ) ^ ((1 : ℝ) / 28) =
        (m : ℝ) ^ ((149 : ℝ) / 168) := by
    rw [← Real.rpow_add hmpos, ← Real.rpow_add hmpos]
    congr 2
    norm_num
  have hd₀sq : (m : ℝ) ^ ((20 : ℝ) / 21) <
      32768 ^ (2 : ℕ) * L ^ (6 : ℕ) * d₀ ^ (2 : ℕ) := by
    have hsquare := (sq_lt_sq₀
      (Real.rpow_nonneg hmpos.le ((10 : ℝ) / 21))
      (by positivity : 0 ≤ 32768 * L ^ (3 : ℕ) * d₀)).mpr hd₀
    have hbase :
        ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (2 : ℕ) =
          (m : ℝ) ^ ((20 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    rw [hbase] at hsquare
    calc
      (m : ℝ) ^ ((20 : ℝ) / 21) <
          (32768 * L ^ (3 : ℕ) * d₀) ^ (2 : ℕ) := hsquare
      _ = 32768 ^ (2 : ℕ) * L ^ (6 : ℕ) * d₀ ^ (2 : ℕ) := by ring
  rcases hready with ⟨hr₁, hr₂, hr₃, hr₄, _hr₅, _hr₆, _hr₇, _hr₈⟩
  change (1792 * R * 32768 ^ (2 : ℕ)) *
      (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) ≤
        (m : ℝ) ^ ((20 : ℝ) / 21) at hr₁
  change 25088 * (m : ℝ) ^ (0 : ℝ) ≤
      (m : ℝ) ^ ((1 : ℝ) / 4) at hr₂
  change 224 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤
      (m : ℝ) ^ ((3 : ℝ) / 8) at hr₃
  change (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
      32768 ^ (56 : ℕ)) * (m : ℝ) ^ ((557 : ℝ) / 21) *
        L ^ (168 : ℕ) ≤ (m : ℝ) ^ ((1117 : ℝ) / 42) at hr₄
  have hDcapR (b : Bool) : D b ≤
      2 * R * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    simpa [R, Nat.cast_add] using hDcap b
  have hinterp₂ (b : Bool) :
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ) := by
    have hscaled :
        (1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168)) *
            (32768 ^ (2 : ℕ) * L ^ (6 : ℕ)) ≤
          (32768 ^ (2 : ℕ) * L ^ (6 : ℕ)) * d₀ ^ (2 : ℕ) := by
      calc
        _ = (1792 * R * 32768 ^ (2 : ℕ)) *
            (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) := by ring
        _ ≤ (m : ℝ) ^ ((20 : ℝ) / 21) := hr₁
        _ ≤ _ := hd₀sq.le
    have hmain : 1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168) ≤
        d₀ ^ (2 : ℕ) := by
      exact (mul_le_mul_iff_right₀ (by positivity :
        (0 : ℝ) < 32768 ^ (2 : ℕ) * L ^ (6 : ℕ))).mp (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    calc
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤
          896 * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
            (m : ℝ) ^ ((3 : ℝ) / 8) *
              (m : ℝ) ^ ((1 : ℝ) / 28) := by
        dsimp [t₂, R]
        gcongr
        · simpa [R, Nat.cast_add] using hDcap b
      _ = 1792 * R * (m : ℝ) ^ ((149 : ℝ) / 168) := by
        rw [← hpowProduct]
        ring
      _ ≤ _ := hmain
  have ht₀le (b : Bool) : t₀ b ≤ t₂ b := by
    dsimp [t₀, t₂]
    exact Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
  have hinterp₀ (b : Bool) :
      896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d₀ ^ (2 : ℕ) := by
    calc
      _ ≤ 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ht₀le b)
            (mul_nonneg (by norm_num) (hDnonneg b)))
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := hinterp₂ b
  have hinv₀ (b : Bool) : 896 * 28 * (t₀ b)⁻¹ ≤ 1 := by
    have htpos : 0 < t₀ b := by dsimp [t₀]; positivity
    apply (mul_inv_le_iff₀ htpos).2
    dsimp [t₀]
    norm_num [Real.rpow_zero] at hr₂ ⊢
    simpa using hr₂
  have hinv₂ (b : Bool) : 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1 := by
    have htpos : 0 < t₂ b := by dsimp [t₂]; positivity
    apply (mul_inv_le_iff₀ htpos).2
    have hsLowerPos : 0 < (s : ℝ) := by positivity
    have hdiv : Q / s ≤ (m : ℝ) ^ ((1 : ℝ) / 3) / 4 := by
      apply (div_le_iff₀ hsLowerPos).2
      calc
        Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4 := hQ
        _ = ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) *
            (m : ℝ) ^ ((2 : ℝ) / 7) := by
          rw [show (m : ℝ) ^ ((13 : ℝ) / 21) =
            (m : ℝ) ^ ((1 : ℝ) / 3) *
              (m : ℝ) ^ ((2 : ℝ) / 7) by
                rw [← Real.rpow_add hmpos]
                norm_num]
          ring
        _ ≤ ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) * s := by gcongr
    calc
      896 * (Q / s) ≤ 896 * ((m : ℝ) ^ ((1 : ℝ) / 3) / 4) := by gcongr
      _ = 224 * (m : ℝ) ^ ((1 : ℝ) / 3) := by ring
      _ ≤ (m : ℝ) ^ ((3 : ℝ) / 8) := hr₃
      _ = 1 * t₂ b := by simp [t₂]
  have hpattern : (448 * s : ℝ) * e *
      (D false * D true) ^ (26 : ℕ) ≤ β * d₀ ^ (56 : ℕ) := by
    have he : (e : ℝ) ≤
        (m : ℝ) * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) :=
      (hedge false).trans (mul_le_mul_of_nonneg_left
        (hDcapR false) hmpos.le)
    have hDD : D false * D true ≤
        (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
          (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) :=
      mul_le_mul (hDcapR false) (hDcapR true) (hDnonneg true)
        (by positivity)
    have hleft : (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
        (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ)) *
          (m : ℝ) ^ ((557 : ℝ) / 21) := by
      calc
        _ ≤ 448 * (2 * (m : ℝ) ^ ((2 : ℝ) / 7)) *
            ((m : ℝ) * (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21))) *
            ((2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
              (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21))) ^ (26 : ℕ) := by
          gcongr
          all_goals first
            | exact hsUpper
            | exact he
            | exact hDD
            | exact mul_nonneg (hDnonneg false) (hDnonneg true)
            | positivity
        _ = _ := by
          have hm557 : (m : ℝ) ^ ((2 : ℝ) / 7) * m *
              (m : ℝ) ^ ((10 : ℝ) / 21) *
              (((m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((10 : ℝ) / 21)) ^ (26 : ℕ)) =
              (m : ℝ) ^ ((557 : ℝ) / 21) := by
            rw [show (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((10 : ℝ) / 21) =
                (m : ℝ) ^ ((20 : ℝ) / 21) by
                  rw [← Real.rpow_add hmpos]
                  norm_num]
            rw [show ((m : ℝ) ^ ((20 : ℝ) / 21)) ^ (26 : ℕ) =
                (m : ℝ) ^ ((520 : ℝ) / 21) by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
                  norm_num]
            have hA : (m : ℝ) ^ ((2 : ℝ) / 7) * m =
                (m : ℝ) ^ ((9 : ℝ) / 7) := by
              calc
                _ = (m : ℝ) ^ ((2 : ℝ) / 7) * (m : ℝ) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
                _ = (m : ℝ) ^ ((2 : ℝ) / 7 + 1) :=
                  (Real.rpow_add hmpos _ _).symm
                _ = _ := by norm_num
            have hB : (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((520 : ℝ) / 21) =
                (m : ℝ) ^ ((530 : ℝ) / 21) := by
              rw [← Real.rpow_add hmpos]
              norm_num
            rw [show (m : ℝ) ^ ((2 : ℝ) / 7) * m *
                (m : ℝ) ^ ((10 : ℝ) / 21) *
                (m : ℝ) ^ ((520 : ℝ) / 21) =
                ((m : ℝ) ^ ((2 : ℝ) / 7) * m) *
                  ((m : ℝ) ^ ((10 : ℝ) / 21) *
                    (m : ℝ) ^ ((520 : ℝ) / 21)) by ring,
              hA, hB, ← Real.rpow_add hmpos]
            norm_num
          rw [show (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
              (2 * R * (m : ℝ) ^ ((10 : ℝ) / 21)) =
              (4 * R ^ (2 : ℕ)) *
                ((m : ℝ) ^ ((10 : ℝ) / 21) *
                  (m : ℝ) ^ ((10 : ℝ) / 21)) by ring,
            mul_pow, ← hm557]
          ring
    have hd₀pow : (m : ℝ) ^ ((560 : ℝ) / 21) <
        32768 ^ (56 : ℕ) * L ^ (168 : ℕ) * d₀ ^ (56 : ℕ) := by
      have hp := pow_lt_pow_left₀ hd₀
        (Real.rpow_nonneg hmpos.le _) (by omega : (56 : ℕ) ≠ 0)
      have hbase : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (56 : ℕ) =
          (m : ℝ) ^ ((560 : ℝ) / 21) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
        norm_num
      rw [hbase] at hp
      calc
        (m : ℝ) ^ ((560 : ℝ) / 21) <
            (32768 * L ^ (3 : ℕ) * d₀) ^ (56 : ℕ) := hp
        _ = 32768 ^ (56 : ℕ) * L ^ (168 : ℕ) * d₀ ^ (56 : ℕ) := by
          rw [mul_pow, mul_pow, ← pow_mul]
    have hβpow : β * (m : ℝ) ^ ((560 : ℝ) / 21) =
        (m : ℝ) ^ ((1117 : ℝ) / 42) := by
      dsimp [β]
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    have hscaled :
        (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            (m : ℝ) ^ ((557 : ℝ) / 21)) *
            (32768 ^ (56 : ℕ) * L ^ (168 : ℕ)) ≤
          (32768 ^ (56 : ℕ) * L ^ (168 : ℕ)) *
            (β * d₀ ^ (56 : ℕ)) := by
      calc
        _ = (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            32768 ^ (56 : ℕ)) * (m : ℝ) ^ ((557 : ℝ) / 21) *
              L ^ (168 : ℕ) := by ring
        _ ≤ (m : ℝ) ^ ((1117 : ℝ) / 42) := hr₄
        _ = β * (m : ℝ) ^ ((560 : ℝ) / 21) := hβpow.symm
        _ ≤ β * (32768 ^ (56 : ℕ) * L ^ (168 : ℕ) *
              d₀ ^ (56 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hd₀pow.le (by positivity)
        _ = _ := by ring
    have hmain :
        1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) *
            (m : ℝ) ^ ((557 : ℝ) / 21) ≤ β * d₀ ^ (56 : ℕ) := by
      exact (mul_le_mul_iff_right₀ (by positivity :
        (0 : ℝ) < 32768 ^ (56 : ℕ) * L ^ (168 : ℕ))).mp (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    exact hleft.trans hmain
  simpa [s, β, t₀, t₂] using
    And.intro hspos (And.intro hinterp₀ (And.intro hinterp₂
      (And.intro hinv₀ (And.intro hinv₂ hpattern))))

lemma sparseCore_low_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ (H : DenseHostCell C.graph) (K : MinDegreeHostCell H),
      HostPowerReady C.order →
      1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
      (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W)) →
      janzerGraph ⊑ G := by
  let : Fintype C.W := C.fintypeW
  let : DecidableEq C.W := C.decEqW
  let : DecidableRel C.graph.Adj := C.decAdj
  intro H K hready hsmall hlow
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let d : ℝ := H.edges.card
  let d₀ := d / (64 * m * L)
  let P := liveGraph K.edges
  let n := Fintype.card (LiveVertex K.edges)
  let e := P.edgeFinset.card
  let Q : ℝ := H.dynamicCycleCap
  let D : Bool → ℝ := fun b ↦ H.sideCap b
  let s := ⌈(m : ℝ) ^ ((2 : ℝ) / 7)⌉₊
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  let t₀ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((1 : ℝ) / 4)
  let t₂ : Bool → ℝ := fun _ ↦ (m : ℝ) ^ ((3 : ℝ) / 8)
  let W : ℝ := Conflict.closedWalkCount P 56
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by dsimp [L, degreeBinCount]; positivity
  have hdpos : 0 < d := by dsimp [d]; exact_mod_cast H.edges_nonempty.card_pos
  obtain ⟨_hcore, hd₀lower, hDcap, hd₀min⟩ :=
    sparseCore_denseCell_common C H
  change (m : ℝ) ^ ((10 : ℝ) / 21) <
    32768 * (L : ℝ) ^ (3 : ℕ) * d₀ at hd₀lower
  have hd₀pos : 0 < d₀ := by
    have hright : 0 < 32768 * (L : ℝ) ^ (3 : ℕ) * d₀ :=
      (Real.rpow_pos_of_pos hmpos _).trans hd₀lower
    have hc : 0 < (32768 * (L : ℝ) ^ (3 : ℕ) : ℝ) := by positivity
    have hprod : 0 < (32768 * (L : ℝ) ^ (3 : ℕ)) * d₀ := by
      simpa only [mul_assoc] using hright
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact (not_lt_of_ge hc.le h.1).elim
  have hPedge : P.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < P.edgeFinset.card
    rw [show P.edgeFinset.card = K.edges.card by
      simpa [P] using K.liveGraph_edge_card]
    exact K.edges_nonempty.card_pos
  let : Nonempty (LiveVertex K.edges) := by
    obtain ⟨z, hz⟩ := hPedge
    induction z using Sym2.inductionOn with
    | _ x y => exact ⟨x⟩
  have hn : n ≤ m := by
    dsimp [n, m, SparseCore.order]
    exact Fintype.card_subtype_le _
  have hn2 : 2 ≤ n := by
    obtain ⟨z, hz⟩ := hPedge
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hxy : P.Adj x y := P.mem_edgeFinset.mp hz
      have hdegpos : 0 < P.degree x :=
        (P.degree_pos_iff_exists_adj x).2 ⟨y, hxy⟩
      have hdeglt : P.degree x < n := by
        simpa [n] using P.degree_lt_card_verts x
      omega
  have hedge (b : Bool) : (e : ℝ) ≤ (m : ℝ) * D b := by
    have h₁ : e ≤ H.edges.card := by
      rw [show e = K.edges.card by simpa [e, P] using K.liveGraph_edge_card]
      exact Finset.card_le_card K.edges_subset
    have h₂ : H.edges.card ≤ m * H.sideCap b := by
      simpa [m, SparseCore.order] using H.edge_card_le_card_mul_sideCap b
    have hR : (e : ℝ) ≤ ((m * H.sideCap b : ℕ) : ℝ) := by
      exact_mod_cast h₁.trans h₂
    norm_num [Nat.cast_mul, D] at hR ⊢
    simpa [D] using hR
  have hQbound : Q ≤ (m : ℝ) ^ ((13 : ℝ) / 21) / 4 := by
    have hnat : H.dynamicCycleCap * H.edges.card ≤
        64 * L * ((orderedFourCycles H.edges).card + 1) := by
      dsimp [DenseHostCell.dynamicCycleCap]
      exact Nat.div_mul_le_self _ _
    have hreal : Q * d ≤
        64 * (L : ℝ) * (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) := by
      have hR : ((H.dynamicCycleCap * H.edges.card : ℕ) : ℝ) ≤
          ((64 * L * ((orderedFourCycles H.edges).card + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      norm_num [Nat.cast_mul, Q, d] at hR ⊢
      simpa [Q, d] using hR
    have hlow' : (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        d * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * (L : ℝ)) := by
      simpa [m, L, d, Nat.cast_mul] using hlow
    have hprod : Q * d ≤ ((m : ℝ) ^ ((13 : ℝ) / 21) / 4) * d := by
      calc
        Q * d ≤ 64 * (L : ℝ) *
          (d * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L)) := by
          exact hreal.trans (mul_le_mul_of_nonneg_left hlow' (by positivity))
        _ = ((m : ℝ) ^ ((13 : ℝ) / 21) / 4) * d := by
          field_simp
          ring
    exact (mul_le_mul_iff_left₀ hdpos).mp (by
      simpa [mul_comm] using hprod)
  have hDnonneg (b : Bool) : 0 ≤ D b := by dsimp [D]; positivity
  obtain ⟨hspos, hinterp₀, hinterp₂, hinv₀, hinv₂, hpattern⟩ :=
    low_ready_inputs m n e d₀ Q D hm (by simpa [m] using hready) hn
      hDnonneg (by simpa [m, D] using hDcap) hedge
      (by exact hd₀lower) hQbound
  have hWlower : d₀ ^ (56 : ℕ) ≤ W := by
    apply closedWalkCount_56_lower_of_minDegree P d₀ hd₀pos.le
    intro v
    exact (hd₀min (liveSide K.edges H.color v)).trans
      (K.live_degree_lower_real v)
  have hfew := few_branch_numerics n s e W d₀ β Q D t₀ t₂
    hspos hd₀pos (by dsimp [β]; positivity) hDnonneg
    (fun _ ↦ by dsimp [t₀]; positivity) (fun _ ↦ by dsimp [t₂]; positivity)
    (by dsimp [Q]; positivity) hWlower hinterp₀ hinterp₂ hinv₀ hinv₂ hpattern
  have hdeg (v : LiveVertex K.edges) : (P.degree v : ℝ) ≤
      D (liveSide K.edges H.color v) := by
    simpa [P, D] using K.live_degree_upper_real v
  have hcap (u y : LiveVertex K.edges) (huy : P.Adj y u) :
      ((Erdos113FourCycles.extensionsThroughEdge P u y).card : ℝ) ≤
        (fun _ : Bool ↦ Q) (liveSide K.edges H.color y) := by
    have hnat := K.extensionsThroughEdge_le_dynamicCycleCap
      (by simpa [P] using huy)
    have hreal :
        ((Erdos113FourCycles.extensionsThroughEdge
          (liveGraph K.edges) u y).card : ℝ) ≤ (H.dynamicCycleCap : ℝ) := by
      exact_mod_cast hnat
    simpa only [P, Q] using hreal
  have hsmallLive : 1568 * β <
      cleanSelectorThreshold (Fintype.card (SliceTuple (LiveVertex K.edges))) := by
    calc
      1568 * β < cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) := by
        simpa [β, m] using hsmall
      _ = cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))) := by
        congr 2
        simp [SliceTuple, m, SparseCore.order]
      _ ≤ cleanSelectorThreshold (Fintype.card (SliceTuple (Fin n))) :=
        cleanSelectorThreshold_slice_mono hn2 hn
      _ = cleanSelectorThreshold
          (Fintype.card (SliceTuple (LiveVertex K.edges))) := by
        congr 2
        simp [SliceTuple, n]
  have hcopyP : janzerGraph ⊑ P :=
    janzerGraph_isContained_of_fewFourCycle_bipartite_numerics
      P (liveSide K.edges H.color) s β (fun _ ↦ Q) D t₀ t₂ hspos
        (by dsimp [β]; positivity) (fun _ ↦ by dsimp [Q]; positivity)
        hDnonneg (fun _ ↦ by dsimp [t₀]; positivity)
        (fun _ ↦ by dsimp [t₂]; positivity)
        (fun {_ _} h ↦ K.live_cross (by simpa [P] using h)) hdeg hcap
        hfew.1 hfew.2.1 hfew.2.2 hsmallLive
  exact (hcopyP.trans K.liveGraph_isContained_original).trans C.contained

lemma high_ready_inputs
    (m L ℓ N a b f q d : ℕ)
    (hm : 64 ≤ m) (hL : L = Nat.log 2 m + 1)
    (hℓpos : 0 < ℓ) (hℓL : ℓ ≤ L)
    (hready : HostPowerReady m)
    (hcore : (m : ℝ) ^ ((31 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d)
    (hq : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) /
      (512 * L) < q)
    (hNpos : 0 < N) (haN : a ≤ N) (hb : b < 2 * a)
    (hNcap : (N : ℝ) ≤
      (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21))
    (hfcap : f ≤ N ^ 2)
    (hselection : q ≤ 32 * m * L ^ 2 * b * f) :
    3136 * 2 ^ 27 ≤ b ∧
    702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
      (f : ℝ) / (32 * (ℓ : ℝ) ^ 3 * N) ∧
    let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
    ((224 * 1536 * 512 ^ (26 : ℕ)) *
        (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
        m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
      β * q * d ^ (27 : ℕ) := by
  let R : ℝ := regularFactor + 1
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by rw [hL]; omega
    exact_mod_cast this
  have hℓposR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hdpos : (0 : ℝ) < d := by
    have hright : 0 < (512 * (L : ℝ) ^ (2 : ℕ)) * d :=
      (Real.rpow_pos_of_pos hmpos _).trans hcore
    rcases mul_pos_iff.mp hright with h | h
    · exact h.2
    · exact (not_lt_of_ge (by positivity :
        (0 : ℝ) ≤ 512 * L ^ (2 : ℕ)) h.1).elim
  have hNcapR : (N : ℝ) ≤ R * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    simpa [R, Nat.cast_add] using hNcap
  have hqlower : (m : ℝ) ^ ((44 : ℝ) / 21) <
      512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := by
    have hdenpos : (0 : ℝ) < 512 * L := by positivity
    have hqmul : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) <
        (512 * (L : ℝ)) * q := by
      simpa [mul_comm] using (div_lt_iff₀ hdenpos).mp hq
    have hpow : (m : ℝ) ^ ((31 : ℝ) / 21) *
        (m : ℝ) ^ ((13 : ℝ) / 21) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    calc
      (m : ℝ) ^ ((44 : ℝ) / 21) =
          (m : ℝ) ^ ((31 : ℝ) / 21) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := hpow.symm
      _ < (512 * (L : ℝ) ^ (2 : ℕ) * d) *
          (m : ℝ) ^ ((13 : ℝ) / 21) := by gcongr
      _ = (512 * (L : ℝ) ^ (2 : ℕ)) *
          (d * (m : ℝ) ^ ((13 : ℝ) / 21)) := by ring
      _ < (512 * (L : ℝ) ^ (2 : ℕ)) *
          ((512 * L) * q) := by
        exact mul_lt_mul_of_pos_left hqmul (by positivity)
      _ = 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := by ring
  have hselectionR : (q : ℝ) ≤
      32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := by exact_mod_cast hselection
  have hfcapR : (f : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by exact_mod_cast hfcap
  have hNpow : (N : ℝ) ^ (2 : ℕ) ≤
      R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21) := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N) hNcapR
      (2 : ℕ)
    have hm20 : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (2 : ℕ) =
        (m : ℝ) ^ ((20 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    simpa [mul_pow, hm20] using hs
  have hqUpper : (q : ℝ) ≤
      32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
        (m : ℝ) ^ ((41 : ℝ) / 21) := by
    calc
      (q : ℝ) ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := hselectionR
      _ ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b *
          (R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21)) := by
        gcongr
        exact hfcapR.trans hNpow
      _ = _ := by
        have hm41 : (m : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21) =
            (m : ℝ) ^ ((41 : ℝ) / 21) := by
          calc
            _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21) := by
              rw [Real.rpow_one]
            _ = (m : ℝ) ^ (1 + (20 : ℝ) / 21) :=
              (Real.rpow_add hmpos _ _).symm
            _ = _ := by norm_num
        rw [show 32 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * b *
            (R ^ (2 : ℕ) * (m : ℝ) ^ ((20 : ℝ) / 21)) =
            32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
              ((m : ℝ) * (m : ℝ) ^ ((20 : ℝ) / 21)) by ring,
          hm41]
  have hpone : (m : ℝ) ^ ((1 : ℝ) / 7) <
      8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b := by
    have h41pos : 0 < (m : ℝ) ^ ((41 : ℝ) / 21) :=
      Real.rpow_pos_of_pos hmpos _
    have hscaled : (m : ℝ) ^ ((41 : ℝ) / 21) *
        (m : ℝ) ^ ((1 : ℝ) / 7) <
      (m : ℝ) ^ ((41 : ℝ) / 21) *
        (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b) := by
      calc
      (m : ℝ) ^ ((41 : ℝ) / 21) * (m : ℝ) ^ ((1 : ℝ) / 7) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
        rw [← Real.rpow_add hmpos]
        congr 2
        norm_num
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := hqlower
      _ ≤ 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) *
          (32 * R ^ (2 : ℕ) * (L : ℝ) ^ (2 : ℕ) * b *
            (m : ℝ) ^ ((41 : ℝ) / 21)) := by gcongr
      _ = (m : ℝ) ^ ((41 : ℝ) / 21) *
          (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b) := by ring
    exact lt_of_mul_lt_mul_left hscaled h41pos.le
  rcases hready with ⟨_hr₁, _hr₂, _hr₃, _hr₄, _hr₅, hr₆, hr₇, hr₈⟩
  rw [← hL] at hr₆ hr₇ hr₈
  change (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
      (m : ℝ) ^ (0 : ℝ) * (L : ℝ) ^ (5 : ℕ) ≤
        (m : ℝ) ^ ((1 : ℝ) / 7) at hr₆
  have hliftR : (3136 * 2 ^ (27 : ℕ) : ℝ) ≤ b := by
    have hcpos : 0 < 8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) := by positivity
    have hscaled :
        (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) *
            (3136 * 2 ^ (27 : ℕ) : ℝ) ≤
          (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) * b := by
      calc
      (8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ)) *
          (3136 * 2 ^ (27 : ℕ) : ℝ) =
          (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
            (m : ℝ) ^ (0 : ℝ) * (L : ℝ) ^ (5 : ℕ) := by
        rw [Real.rpow_zero]
        ring
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 7) := hr₆
      _ ≤ 8388608 * R ^ (2 : ℕ) * (L : ℝ) ^ (5 : ℕ) * b := hpone.le
      _ = _ := by ring
    exact le_of_mul_le_mul_left hscaled hcpos
  have hlift : 3136 * 2 ^ 27 ≤ b := by exact_mod_cast hliftR
  have hbN : (b : ℝ) < 2 * N := by
    exact_mod_cast hb.trans_le (Nat.mul_le_mul_left 2 haN)
  have hqpos : (0 : ℝ) < q :=
    (div_pos (mul_pos hdpos (Real.rpow_pos_of_pos hmpos _)) (by positivity)).trans hq
  have hqposNat : 0 < q := by exact_mod_cast hqpos
  have hfpos : (0 : ℝ) < f := by
    have : 0 < f := by
      by_contra! hf
      have : f = 0 := by omega
      rw [this] at hselection
      simp at hselection
      omega
    exact_mod_cast this
  have hqUpperF : (q : ℝ) <
      64 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * N * f := by
    calc
      (q : ℝ) ≤ 32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := hselectionR
      _ < 32 * m * (L : ℝ) ^ (2 : ℕ) * (2 * N) * f := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hbN (by positivity)) hfpos
      _ = _ := by ring
  have hfLower : (m : ℝ) ^ ((23 : ℝ) / 21) <
      16777216 * (L : ℝ) ^ (5 : ℕ) * N * f := by
    have hm23pos : 0 < (m : ℝ) := hmpos
    have hscaled : (m : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) <
        (m : ℝ) * (16777216 * (L : ℝ) ^ (5 : ℕ) * N * f) := by
      calc
      (m : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) =
          (m : ℝ) ^ ((44 : ℝ) / 21) := by
        calc
          _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((23 : ℝ) / 21) := by
            rw [Real.rpow_one]
          _ = (m : ℝ) ^ (1 + (23 : ℝ) / 21) :=
            (Real.rpow_add hmpos _ _).symm
          _ = _ := by norm_num
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) * q := hqlower
      _ < 512 ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) *
          (64 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * N * f) := by gcongr
      _ = (m : ℝ) * (16777216 * (L : ℝ) ^ (5 : ℕ) * N * f) := by ring
    exact lt_of_mul_lt_mul_left hscaled hm23pos.le
  change ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) *
      (m : ℝ) ^ ((25 : ℝ) / 49) * (L : ℝ) ^ (9 : ℕ) ≤
        (m : ℝ) ^ ((13 : ℝ) / 21) at hr₇
  have hNroot : (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
      (2 * R) ^ ((1 : ℝ) / 14) *
        (m : ℝ) ^ ((5 : ℝ) / 147) := by
    have hbase : (2 * N : ℝ) ≤
        (2 * R) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
      calc
        (2 : ℝ) * N ≤ 2 * (R * (m : ℝ) ^ ((10 : ℝ) / 21)) := by gcongr
        _ = _ := by ring
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * N)
      hbase (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 14)
    calc
      _ ≤ ((2 * R) * (m : ℝ) ^ ((10 : ℝ) / 21)) ^
          ((1 : ℝ) / 14) := hp
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hmpos.le]
        norm_num
  have hsuperNumerator :
      (702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤ f := by
    have hleft :
        ((702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14)) *
          (16777216 * (L : ℝ) ^ (5 : ℕ) * N) ≤
        (m : ℝ) ^ ((23 : ℝ) / 21) := by
      calc
        _ ≤ ((702464 * 512 : ℝ) * (L : ℝ) ^ (4 : ℕ) *
            (R * (m : ℝ) ^ ((10 : ℝ) / 21)) *
            ((2 * R) ^ ((1 : ℝ) / 14) *
              (m : ℝ) ^ ((5 : ℝ) / 147))) *
            (16777216 * (L : ℝ) ^ (5 : ℕ) *
              (R * (m : ℝ) ^ ((10 : ℝ) / 21))) := by
          gcongr
          all_goals first
            | exact hNcapR
            | exact hNroot
            | exact_mod_cast hℓL
            | positivity
        _ = (((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
              (2 * R) ^ ((1 : ℝ) / 14)) *
              (m : ℝ) ^ ((25 : ℝ) / 49) * (L : ℝ) ^ (9 : ℕ)) *
              (m : ℝ) ^ ((10 : ℝ) / 21) := by
          have hpow25 : (m : ℝ) ^ ((5 : ℝ) / 147) *
              (m : ℝ) ^ ((10 : ℝ) / 21) =
              (m : ℝ) ^ ((25 : ℝ) / 49) := by
            rw [← Real.rpow_add hmpos]
            congr 2
            norm_num
          let K₀ : ℝ := (702464 * 512) * 16777216 * R ^ (2 : ℕ) *
            (2 * R) ^ ((1 : ℝ) / 14) *
              (m : ℝ) ^ ((10 : ℝ) / 21) * (L : ℝ) ^ (9 : ℕ)
          calc
            _ = K₀ * ((m : ℝ) ^ ((5 : ℝ) / 147) *
                (m : ℝ) ^ ((10 : ℝ) / 21)) := by
              dsimp [K₀]
              ring
            _ = K₀ * (m : ℝ) ^ ((25 : ℝ) / 49) := by rw [hpow25]
            _ = _ := by
              dsimp [K₀]
              ring
        _ ≤ (m : ℝ) ^ ((13 : ℝ) / 21) *
            (m : ℝ) ^ ((10 : ℝ) / 21) := by gcongr
        _ = (m : ℝ) ^ ((23 : ℝ) / 21) := by
          rw [← Real.rpow_add hmpos]
          congr 2
          norm_num
    have hdenpos : 0 < 16777216 * (L : ℝ) ^ (5 : ℕ) * N := by positivity
    have hscaled := hleft.trans hfLower.le
    exact (mul_le_mul_iff_right₀ hdenpos).mp (by
      simpa [mul_comm] using hscaled)
  have hsuper :
      702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) ≤
        (f : ℝ) / (32 * (ℓ : ℝ) ^ 3 * N) := by
    apply (le_div_iff₀ (by positivity :
      (0 : ℝ) < 32 * (ℓ : ℝ) ^ 3 * N)).2
    calc
      702464 * (16 * (ℓ : ℝ)) * (2 * N : ℝ) ^ ((1 : ℝ) / 14) *
          (32 * (ℓ : ℝ) ^ 3 * N) =
        (702464 * 512 : ℝ) * (ℓ : ℝ) ^ (4 : ℕ) * N *
          (2 * N : ℝ) ^ ((1 : ℝ) / 14) := by ring
      _ ≤ f := hsuperNumerator
  change (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
      (m : ℝ) ^ ((1756 : ℝ) / 42) * (L : ℝ) ^ (224 : ℕ) ≤
        (m : ℝ) ^ ((1759 : ℝ) / 42) at hr₈
  have hdLower : (m : ℝ) ^ ((31 : ℝ) / 21) <
      (512 * (L : ℝ) ^ (2 : ℕ)) * d := hcore
  have hdPow : (m : ℝ) ^ ((868 : ℝ) / 21) <
      512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (28 : ℕ) := by
    have hp := pow_lt_pow_left₀ hdLower
      (Real.rpow_nonneg hmpos.le _) (by omega : (28 : ℕ) ≠ 0)
    have hbase : ((m : ℝ) ^ ((31 : ℝ) / 21)) ^ (28 : ℕ) =
        (m : ℝ) ^ ((868 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    rw [hbase] at hp
    calc
      _ < ((512 * (L : ℝ) ^ (2 : ℕ)) * d) ^ (28 : ℕ) := hp
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]
  have hN29 : (N : ℝ) ^ (29 : ℕ) ≤
      R ^ (29 : ℕ) * (m : ℝ) ^ ((290 : ℝ) / 21) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N) hNcapR 29
    have hm290 : ((m : ℝ) ^ ((10 : ℝ) / 21)) ^ (29 : ℕ) =
        (m : ℝ) ^ ((290 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
      norm_num
    simpa [mul_pow, hm290] using hp
  have hmaster :
      ((224 * 1536 * 512 ^ (26 : ℕ)) *
          (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
          m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
        β * q * d ^ (27 : ℕ) := by
    let C₀ : ℝ := (224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))
    have hleft : C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
        (N : ℝ) ^ (29 : ℕ) ≤
      C₀ * R ^ (29 : ℕ) * (m : ℝ) ^ ((878 : ℝ) / 21) *
        (L : ℝ) ^ (167 : ℕ) := by
      calc
        _ ≤ C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
            (R ^ (29 : ℕ) * (m : ℝ) ^ ((290 : ℝ) / 21)) := by gcongr
        _ = _ := by
          have hm878 : (m : ℝ) ^ (28 : ℕ) *
              (m : ℝ) ^ ((290 : ℝ) / 21) =
              (m : ℝ) ^ ((878 : ℝ) / 21) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hmpos]
            congr 2
            norm_num
          calc
            _ = C₀ * R ^ (29 : ℕ) *
                ((m : ℝ) ^ (28 : ℕ) *
                  (m : ℝ) ^ ((290 : ℝ) / 21)) *
                  (L : ℝ) ^ (167 : ℕ) := by ring
            _ = _ := by rw [hm878]
    have hd13 : (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) <
        (512 * (L : ℝ)) * q := by
      have hden : (0 : ℝ) < 512 * L := by positivity
      simpa [mul_comm] using (div_lt_iff₀ hden).mp hq
    have hqd : (m : ℝ) ^ ((881 : ℝ) / 21) <
        512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
          ((q : ℝ) * d ^ (27 : ℕ)) := by
      calc
        (m : ℝ) ^ ((881 : ℝ) / 21) =
            (m : ℝ) ^ ((868 : ℝ) / 21) *
              (m : ℝ) ^ ((13 : ℝ) / 21) := by
          rw [← Real.rpow_add hmpos]
          congr 2
          norm_num
        _ < (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (28 : ℕ)) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := by gcongr
        _ = (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (27 : ℕ)) *
            (d * (m : ℝ) ^ ((13 : ℝ) / 21)) := by ring
        _ < (512 ^ (28 : ℕ) * (L : ℝ) ^ (56 : ℕ) * d ^ (27 : ℕ)) *
            ((512 * (L : ℝ)) * q) := by gcongr
        _ = 512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
            ((q : ℝ) * d ^ (27 : ℕ)) := by ring
    have hβ881 : β * (m : ℝ) ^ ((881 : ℝ) / 21) =
        (m : ℝ) ^ ((1759 : ℝ) / 42) := by
      dsimp [β]
      rw [← Real.rpow_add hmpos]
      congr 2
      norm_num
    have hright :
        (m : ℝ) ^ ((1759 : ℝ) / 42) <
          (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
            (β * (q : ℝ) * d ^ (27 : ℕ)) := by
      rw [← hβ881]
      have hβpos : 0 < β := by dsimp [β]; positivity
      calc
        β * (m : ℝ) ^ ((881 : ℝ) / 21) <
            β * (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) *
              ((q : ℝ) * d ^ (27 : ℕ))) :=
          mul_lt_mul_of_pos_left hqd hβpos
        _ = _ := by ac_rfl
    have hdenpos : 0 < 512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ) := by positivity
    apply (mul_le_mul_iff_right₀ hdenpos).mp
    calc
      (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (C₀ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (167 : ℕ) *
            (N : ℝ) ^ (29 : ℕ)) ≤
        (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (C₀ * R ^ (29 : ℕ) * (m : ℝ) ^ ((878 : ℝ) / 21) *
            (L : ℝ) ^ (167 : ℕ)) := by gcongr
      _ = (C₀ * R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
          (m : ℝ) ^ ((1756 : ℝ) / 42) * (L : ℝ) ^ (224 : ℕ) := by
        norm_num [show (878 : ℝ) / 21 = 1756 / 42 by norm_num]
        ring
      _ ≤ (m : ℝ) ^ ((1759 : ℝ) / 42) := by
        simpa [C₀] using hr₈
      _ ≤ (512 ^ (29 : ℕ) * (L : ℝ) ^ (57 : ℕ)) *
          (β * (q : ℝ) * d ^ (27 : ℕ)) := hright.le
  exact ⟨hlift, hsuper, by simpa [β] using hmaster⟩

lemma selectedLiftedCycles_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (S : FirstSelection G side) (R : S.SecondSelection)
    (Q : ℕ)
    (hcycle : ∀ t : NeighborVertex G S.anchor,
      (Erdos113Cycles.cyclesThroughEdge G 4 s(S.anchor, t.1)).card ≤ Q)
    (hlift : 3136 * 2 ^ 27 ≤ 2 ^ R.index.val)
    (hsuper :
      702464 * (16 *
          (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ)) *
          (2 * Fintype.card (NeighborVertex G S.anchor) : ℝ) ^
            ((1 : ℝ) / 14) ≤
        ((S.auxiliaryGraph R.index).edgeFinset.card : ℝ) /
          (32 *
            (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ) ^ 3 *
            Fintype.card (NeighborVertex G S.anchor))) :
    (Erdos113ManyLifts.liftedCycles
      (S.auxiliaryGraph R.index) G
      (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
        S R hcross)).Nonempty := by
  let F := S.auxiliaryGraph R.index
  let L := Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
    S R hcross
  let δ : ℝ := (F.edgeFinset.card : ℝ) /
    (32 * (degreeBinCount (W := NeighborVertex G S.anchor) : ℝ) ^ 3 *
      Fintype.card (NeighborVertex G S.anchor))
  have hFcycles : δ ^ 28 / (2 * (2 : ℝ) ^ 28) ≤
      ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact Erdos113Supersaturation28.genuineCycles28_lower_of_edgeDensity
      F R.auxiliary_edge (by simpa [F, δ] using hsuper)
  obtain ⟨x, y, hxy⟩ := R.auxiliary_edge
  have hfpos : 0 < F.edgeFinset.card := by
    apply Finset.card_pos.mpr
    exact ⟨s(x, y), F.mem_edgeFinset.mpr hxy⟩
  have hNpos : 0 < Fintype.card (NeighborVertex G S.anchor) :=
    Fintype.card_pos_iff.mpr ⟨x⟩
  have hfposR : (0 : ℝ) < F.edgeFinset.card := by exact_mod_cast hfpos
  have hNposR : (0 : ℝ) < Fintype.card (NeighborVertex G S.anchor) := by
    exact_mod_cast hNpos
  have hellposNat : 0 <
      degreeBinCount (W := NeighborVertex G S.anchor) := by
    dsimp [degreeBinCount]
    omega
  have hellposR : (0 : ℝ) <
      degreeBinCount (W := NeighborVertex G S.anchor) := by
    exact_mod_cast hellposNat
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hfposR (by positivity)
  have hcycleposR :
      0 < ((Erdos113Cycles.genuineCycles F 28).card : ℝ) := by
    exact (by positivity : 0 < δ ^ 28 / (2 * (2 : ℝ) ^ 28)).trans_le
      hFcycles
  have hcyclepos : 0 < (Erdos113Cycles.genuineCycles F 28).card := by
    exact_mod_cast hcycleposR
  have hlower : 3136 * 2 ^ 27 ≤ L.lower := by
    change 3136 * 2 ^ 27 ≤ 2 ^ R.index.val
    exact hlift
  have hcount := Erdos113ManyLifts.liftedCycles_card_lower L hlower
  have hleftpos :
      0 < (Erdos113Cycles.genuineCycles F 28).card * L.lower ^ 28 := by
    exact Nat.mul_pos hcyclepos (by positivity)
  have hrightpos :
      0 < 2 * (Erdos113ManyLifts.liftedCycles F G L).card :=
    hleftpos.trans_le hcount
  have hcardpos :
      0 < (Erdos113ManyLifts.liftedCycles F G L).card := by omega
  have hnonempty := Finset.card_pos.mp hcardpos
  simpa [F, L] using hnonempty

lemma sparseCore_high_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    letI : DecidableRel C.graph.Adj := C.decAdj
    ∀ H : DenseHostCell C.graph,
      HostPowerReady C.order →
      1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
      ¬ ((((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W))) →
      janzerGraph ⊑ G := by
  let : Fintype C.W := C.fintypeW
  let : DecidableEq C.W := C.decEqW
  let : DecidableRel C.graph.Adj := C.decAdj
  intro H hready hsmall hhigh
  let m := C.order
  let L := degreeBinCount (W := C.W)
  let P := graphOfEdges H.edges
  let q := (Erdos113Cycles.genuineCycles P 4).card
  let d := H.edges.card
  let β := (m : ℝ) ^ (-(1 : ℝ) / 14)
  have hm : 64 ≤ m := by simpa [m, SparseCore.order] using C.order_large
  have hmpos : (0 : ℝ) < m := by positivity
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hdpos : 0 < d := by dsimp [d]; exact H.edges_nonempty.card_pos
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨hcore, _hd₀lower, _hDcap, _hd₀min⟩ :=
    sparseCore_denseCell_common C H
  change (m : ℝ) ^ ((31 : ℝ) / 21) <
    512 * (L : ℝ) ^ (2 : ℕ) * d at hcore
  have hhigh' :
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L) <
        (((q + 1 : ℕ) : ℝ)) := by
    apply lt_of_not_ge
    simpa [m, L, P, q, d, orderedFourCycles, Nat.cast_mul] using hhigh
  rcases hready with ⟨hr₁, hr₂, hr₃, hr₄, hr₅, hr₆, hr₇, hr₈⟩
  have hm44 : (m : ℝ) ^ ((44 : ℝ) / 21) <
      512 * (L : ℝ) ^ (2 : ℕ) * d *
        (m : ℝ) ^ ((13 : ℝ) / 21) := by
    calc
      (m : ℝ) ^ ((44 : ℝ) / 21) =
          (m : ℝ) ^ ((31 : ℝ) / 21) *
            (m : ℝ) ^ ((13 : ℝ) / 21) := by
        rw [← Real.rpow_add hmpos]
        congr 2
        norm_num
      _ < _ := by gcongr
  have hr₅' : 131072 * (L : ℝ) ^ (3 : ℕ) ≤
      (m : ℝ) ^ ((44 : ℝ) / 21) := by
    rw [Real.rpow_zero, mul_one] at hr₅
    simpa only [L, degreeBinCount, m, SparseCore.order] using hr₅
  have hthresholdMul :
      (512 * (L : ℝ) ^ (2 : ℕ)) * (256 * L) <
        (512 * (L : ℝ) ^ (2 : ℕ)) *
          ((d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21)) := by
    calc
      _ = 131072 * (L : ℝ) ^ (3 : ℕ) := by ring
      _ ≤ (m : ℝ) ^ ((44 : ℝ) / 21) := hr₅'
      _ < 512 * (L : ℝ) ^ (2 : ℕ) * d *
          (m : ℝ) ^ ((13 : ℝ) / 21) := hm44
      _ = _ := by ring
  have hthresholdNumerator :
      256 * (L : ℝ) < (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) :=
    lt_of_mul_lt_mul_left hthresholdMul (by positivity)
  have honeThreshold : (1 : ℝ) <
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L) := by
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 256 * (L : ℝ))).2
      (by simpa using hthresholdNumerator)
  have hqposR : (0 : ℝ) < q := by
    have hqone : (1 : ℝ) < ((q + 1 : ℕ) : ℝ) :=
      honeThreshold.trans hhigh'
    have hqoneNat : 1 < q + 1 := by exact_mod_cast hqone
    exact_mod_cast (show 0 < q by omega)
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqplus : ((q + 1 : ℕ) : ℝ) ≤ 2 * q := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have hqlower :
      (d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (512 * L) < q := by
    calc
      _ = ((d : ℝ) * (m : ℝ) ^ ((13 : ℝ) / 21) / (256 * L)) / 2 := by
        field_simp
        ring
      _ < (((q + 1 : ℕ) : ℝ)) / 2 := by gcongr
      _ ≤ q := by linarith
  have hPcycles : (Erdos113Cycles.genuineCycles P 4).Nonempty :=
    Finset.card_pos.mp (by simpa [q] using hqpos)
  obtain ⟨S⟩ := exists_firstSelection P (sideOfColor H.color) hPcycles
  obtain ⟨R⟩ := S.exists_secondSelection
  let N := Fintype.card (NeighborVertex P S.anchor)
  let a := 2 ^ S.scaleIndex.val
  let b := 2 ^ R.index.val
  let f := (S.auxiliaryGraph R.index).edgeFinset.card
  let ell := degreeBinCount (W := NeighborVertex P S.anchor)
  have hcross : ∀ ⦃x y⦄, P.Adj x y →
      sideOfColor H.color y = !sideOfColor H.color x := by
    intro x y hxy
    exact H.cross hxy
  have hNdegree : N = P.degree S.anchor := by
    simp [N, NeighborVertex, SimpleGraph.card_neighborFinset_eq_degree]
  have hNpos : 0 < N := by
    obtain ⟨p, hp⟩ := S.triples_nonempty
    rw [hNdegree]
    exact (P.degree_pos_iff_exists_adj S.anchor).2 ⟨p.left, (S.data hp).1⟩
  have haN : a ≤ N := by
    obtain ⟨p, hp⟩ := S.triples_nonempty
    calc
      a = 2 ^ S.scaleIndex.val := rfl
      _ ≤ Erdos113FourCycles.codegree P S.anchor p.middle :=
        (S.data hp).2.2.2.2.2.2.2.1
      _ ≤ P.degree S.anchor := codegree_le_degree_left P S.anchor p.middle
      _ = N := hNdegree.symm
  have ha : 2 ≤ a := by
    dsimp [a]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt S.scaleIndex_pos)
  have hb : b < 2 * a := by
    simpa [a, b] using
      Erdos113.FirstSelection.SecondSelection.secondScale_lt_twice_firstScale S R
  have hPcore : P ≤ C.graph := graphOfEdges_le H.edges_subset
  have hNcapNat : N ≤ C.graph.maxDegree := by
    rw [hNdegree]
    exact (SimpleGraph.degree_le_of_le hPcore).trans
      (C.graph.degree_le_maxDegree S.anchor)
  have hNcap : (N : ℝ) ≤
      (regularFactor + 1 : ℕ) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
    calc
      (N : ℝ) ≤ C.graph.maxDegree := by exact_mod_cast hNcapNat
      _ ≤ _ := by simpa [m, SparseCore.maximumDegree] using C.maxDegree_upper
  have hNm : N ≤ m := by
    dsimp [N, m, SparseCore.order]
    exact Fintype.card_subtype_le _
  have hellpos : 0 < ell := by dsimp [ell, degreeBinCount]; omega
  have hellL : ell ≤ L := by
    dsimp [ell, L, degreeBinCount]
    exact Nat.add_le_add_right (Nat.log_mono_right hNm) 1
  have hfcap : f ≤ N ^ 2 := by
    simpa only [f, N] using
      Erdos113.FirstSelection.SecondSelection.auxiliary_edge_card_le_square S R
  have hselection : q ≤ 32 * m * L ^ 2 * b * f := by
    simpa only [q, m, L, b, f, SparseCore.order, degreeBinCount] using
      Erdos113.FirstSelection.SecondSelection.selection_count_bound S R
  obtain ⟨hlift, hsuper, hmaster⟩ := high_ready_inputs
    m L ell N a b f q d hm (by rfl) hellpos hellL
      (by simpa [HostPowerReady, m] using
        And.intro hr₁ (And.intro hr₂ (And.intro hr₃ (And.intro hr₄
          (And.intro hr₅ (And.intro hr₆ (And.intro hr₇ hr₈)))))))
      hcore hqlower hNpos haN hb hNcap hfcap hselection
  have hQd : H.dynamicCycleCap * d ≤ 128 * L * q := by
    have hdiv : H.dynamicCycleCap * H.edges.card ≤
        64 * L * ((orderedFourCycles H.edges).card + 1) := by
      dsimp [DenseHostCell.dynamicCycleCap]
      exact Nat.div_mul_le_self _ _
    have hqplusNat : (orderedFourCycles H.edges).card + 1 ≤ 2 * q := by
      simpa [P, q, orderedFourCycles] using
        (show q + 1 ≤ 2 * q by omega)
    calc
      H.dynamicCycleCap * d = H.dynamicCycleCap * H.edges.card := rfl
      _ ≤ 64 * L * ((orderedFourCycles H.edges).card + 1) := hdiv
      _ ≤ 64 * L * (2 * q) := by gcongr
      _ = 128 * L * q := by ring
  have hcycle : ∀ t : NeighborVertex P S.anchor,
      (Erdos113Cycles.cyclesThroughEdge P 4 s(S.anchor, t.1)).card ≤
        H.dynamicCycleCap := by
    intro t
    exact H.cyclesThroughEdge_le_dynamicCycleCap
      ((P.mem_neighborFinset S.anchor t.1).mp t.2)
  have hnumeric := many_branch_numeric_of_master
    m L N a b f q d H.dynamicCycleCap β hLpos hNpos ha hqpos hdpos
      (by dsimp [β]; positivity) hb hQd hselection hmaster
  have hdeltaMono :
      (f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N) ≤
        (f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N) := by
    apply div_le_div_of_nonneg_left (by positivity)
      (by positivity : (0 : ℝ) < 32 * (ell : ℝ) ^ (3 : ℕ) * N)
    gcongr
  have hdeltaNonneg :
      (0 : ℝ) ≤ (f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N) :=
    div_nonneg (by exact_mod_cast (Nat.zero_le f)) (by positivity)
  have hdeltaPow :
      ((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) ≤
        ((f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) :=
    pow_le_pow_left₀ hdeltaNonneg hdeltaMono 28
  have hYmono :
      ((((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
          (2 * (2 : ℝ) ^ (28 : ℕ))) * (b : ℝ) ^ (28 : ℕ) / 2) ≤
        ((((f : ℝ) / (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
          (2 * (2 : ℝ) ^ (28 : ℕ))) * (b : ℝ) ^ (28 : ℕ) / 2) := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (div_le_div_iff_of_pos_right
      (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ (28 : ℕ))).2 hdeltaPow
  have hnumericEll :
      (112 * (2 * b + 2 * a) : ℝ) *
          (2 * (((N * (H.dynamicCycleCap / (a - 1)) : ℕ) : ℝ)) *
            (((((2 * a) * (H.dynamicCycleCap / (a - 1)) : ℕ) : ℝ)) ^
              (26 : ℕ))) ≤
        β *
          ((((f : ℝ) /
              (32 * (ell : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
                (2 * (2 : ℝ) ^ (28 : ℕ))) *
              (b : ℝ) ^ (28 : ℕ) / 2) := by
    apply hnumeric.trans
    exact mul_le_mul_of_nonneg_left hYmono (by dsimp [β]; positivity)
  have hgood := manyFourCycleGoodFamily_of_numerics
    P (sideOfColor H.color) hcross S R H.dynamicCycleCap hcycle
      hlift hsuper β (by dsimp [β]; positivity) (by
        dsimp only
        simp only [
          Erdos113SelectedLift.FirstSelection.SecondSelection.anchoredLiftSystem,
          Erdos113AnchorConstruction.selectedAnchoredLiftSystem]
        have hbReal : (2 : ℝ) ^ (R.index.val + 1) = 2 * (b : ℝ) := by
          rw [pow_succ]
          norm_num [b]
          ring
        have haReal : (2 : ℝ) ^ (S.scaleIndex.val + 1) = 2 * (a : ℝ) := by
          rw [pow_succ]
          norm_num [a]
          ring
        have haNatR : (((2 ^ (S.scaleIndex.val + 1) : ℕ) : ℝ)) =
            2 * (a : ℝ) := by
          simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, a]
          ring
        rw [hbReal, haReal, haNatR]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hnumericEll ⊢
        simpa only [a, b, N, ell, f] using hnumericEll)
  have hfamily :
      (Erdos113ManyLifts.liftedCycles
        (S.auxiliaryGraph R.index) P
        (Erdos113SelectedLift.FirstSelection.SecondSelection.liftSystem
          S R hcross)).Nonempty :=
    selectedLiftedCycles_nonempty P (sideOfColor H.color) hcross S R
      H.dynamicCycleCap hcycle hlift hsuper
  have hcopyP : janzerGraph ⊑ P :=
    hgood.janzerGraph_isContained (by dsimp [β]; positivity) hfamily (by
      simpa [β, m, P] using hsmall)
  exact (hcopyP.trans (SimpleGraph.IsContained.of_le hPcore)).trans C.contained

theorem SparseCore.janzerGraph_isContained
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : SparseCore G) :
    letI : Fintype C.W := C.fintypeW
    letI : DecidableEq C.W := C.decEqW
    HostPowerReady C.order →
    1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
      cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) →
    janzerGraph ⊑ G := by
  let : Fintype C.W := C.fintypeW
  let : DecidableEq C.W := C.decEqW
  let : DecidableRel C.graph.Adj := C.decAdj
  intro hready hsmall
  obtain ⟨e, he⟩ := C.edges_nonempty
  obtain ⟨x, y, hxy⟩ : ∃ x y, C.graph.Adj x y := by
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, C.graph.mem_edgeFinset.mp he⟩
  obtain ⟨H⟩ := exists_denseHostCell C.graph ⟨x, y, hxy⟩
  by_cases hlow :
      (((orderedFourCycles H.edges).card + 1 : ℕ) : ℝ) ≤
        (H.edges.card : ℝ) *
          (C.order : ℝ) ^ ((13 : ℝ) / 21) /
            (256 * degreeBinCount (W := C.W))
  · obtain ⟨K⟩ :=
      Erdos113HostPruning.DenseHostCell.exists_minDegreeHostCell H
    exact sparseCore_low_branch C H K hready hsmall hlow
  · exact sparseCore_high_branch C H hready hsmall hlow

lemma janzerHostEmbeddingAt_of_core_threshold
    (M n : ℕ)
    (hready : ∀ m, M ≤ m → HostPowerReady m)
    (hsmall : ∀ m, M ≤ m →
      1568 * (m : ℝ) ^ (-(1 : ℝ) / 14) <
        cleanSelectorThreshold (Fintype.card (SliceTuple (Fin m))))
    (hnlarge : max sparseCoreHostThreshold (4 ^ 21 * M ^ 20 + 1) ≤ n) :
    JanzerHostEmbeddingAt n := by
  intro G _inst hdense
  have hhostLarge : sparseCoreHostThreshold ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    exact (Nat.le_max_left _ _).trans hnlarge
  obtain ⟨C⟩ := exists_sparseCore_of_large_host G hhostLarge (by
    simpa using hdense)
  have hnpos : 0 < n := by
    have hthresholdPos : 0 < 4 ^ 21 * M ^ 20 + 1 := by positivity
    exact hthresholdPos.trans_le ((Nat.le_max_right _ _).trans hnlarge)
  have hdensePow : n ^ 31 < G.edgeFinset.card ^ 21 :=
    power_density_of_rpow_density hdense
  have hchain : n ^ 31 < 4 ^ 21 * C.order ^ 20 * n ^ 22 := by
    calc
      n ^ 31 < G.edgeFinset.card ^ 21 := hdensePow
      _ ≤ 4 ^ 21 * C.order ^ 20 * Fintype.card (Fin n) ^ 22 := C.host_growth
      _ = 4 ^ 21 * C.order ^ 20 * n ^ 22 := by simp
  have hcancel : n ^ 9 < 4 ^ 21 * C.order ^ 20 := by
    apply lt_of_mul_lt_mul_right (a := n ^ 22) _ (Nat.zero_le _)
    simpa [← pow_add] using hchain
  have hMcore : M ≤ C.order := by
    by_contra! hm
    have hmPow : C.order ^ 20 ≤ M ^ 20 :=
      pow_le_pow_left' (by omega : C.order ≤ M) 20
    have hcancel' : n ^ 9 < 4 ^ 21 * M ^ 20 :=
      hcancel.trans_le (Nat.mul_le_mul_left _ hmPow)
    have hnlepow : n ≤ n ^ 9 := by
      calc
        n = n ^ 1 := by simp
        _ ≤ n ^ 9 := pow_le_pow_right₀ (by omega : 1 ≤ n) (by omega)
    have hthreshold : 4 ^ 21 * M ^ 20 + 1 ≤ n :=
      (Nat.le_max_right _ _).trans hnlarge
    omega
  let : Fintype C.W := C.fintypeW
  let : DecidableEq C.W := C.decEqW
  have hsmallW : 1568 * (C.order : ℝ) ^ (-(1 : ℝ) / 14) <
      cleanSelectorThreshold (Fintype.card (SliceTuple C.W)) := by
    rw [show Fintype.card (SliceTuple C.W) =
        Fintype.card (SliceTuple (Fin C.order)) by
      calc
        Fintype.card (SliceTuple C.W) = C.order ^ 28 := by
          simp [SliceTuple, SparseCore.order]
        _ = Fintype.card (SliceTuple (Fin C.order)) :=
          (card_sliceTuple_fin C.order).symm]
    exact hsmall C.order hMcore
  exact Erdos113.SparseCore.janzerGraph_isContained C
    (hready C.order hMcore) hsmallW

theorem eventually_janzerHostEmbedding :
    ∀ᶠ n : ℕ in atTop, JanzerHostEmbeddingAt n := by
  have hboth := eventually_hostPowerReady.and eventually_cleanSelectorThreshold
  obtain ⟨M, hM⟩ := eventually_atTop.1 hboth
  filter_upwards [eventually_ge_atTop
    (max sparseCoreHostThreshold (4 ^ 21 * M ^ 20 + 1))] with n hn
  exact janzerHostEmbeddingAt_of_core_threshold M n
    (fun m hm ↦ (hM m hm).1) (fun m hm ↦ (hM m hm).2) hn

theorem janzerGraph_hasExtremalBound :
    HasExtremalBound ((31 : ℝ) / 21) janzerGraph :=
  hasExtremalBound_of_eventually_janzerHostEmbedding
    eventually_janzerHostEmbedding

/-- Janzer's counterexample resolves Erdős Problem 113 negatively. -/
theorem not_erdos_113 :
    ¬ (∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
      H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)) :=
  not_erdosSimonovitsConjecture_of_janzer_bound janzerGraph_hasExtremalBound

end Erdos113

alias _root_.Erdos113.erdos113_resolution := _root_.Erdos113.not_erdos_113
