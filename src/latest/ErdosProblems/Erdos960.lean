/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 960.
https://www.erdosproblems.com/forum/thread/960

Informal authors:
- Boris Alexeev
- Matthew Putterman
- Mehtaab Sawhney
- Mark Sellke
- Gregory Valiant
- OpenAI internal model

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos960.md
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

import ErdosProblems.Erdos735.OrdinaryLineReduction
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.ZMod.Basic

/-!
# Erdős Problem 960

For a finite set `A` of points in the real plane, its ordinary-line graph joins
two points when their joining line contains exactly those two points of `A`.
This file formalizes both the exact forcing threshold and the resolution of the
problem: for fixed `r ≥ 3` and `k ≥ 4` the threshold is bounded below by
`n² / 12 - (10 / 3)n + 1`, and hence is neither `o(n²)` nor `O(n)`.

The lower construction is APSSV's cyclic construction, realized elementarily on
the real nodal cubic `y² = x²(x - 1)`.  The detailed proof and declaration map
are in `tex/960.tex`.

*References:*
- [Erdős Problem 960](https://www.erdosproblems.com/960)
- P. Erdős, *Research problems*, Period. Math. Hungar. 15 (1984), 101--103.
- B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, G. Valiant,
  *Short proofs in combinatorics, probability and number theory II*,
  [arXiv:2604.06609](https://arxiv.org/abs/2604.06609), Section 2.
-/

namespace Erdos960

open scoped BigOperators
open Filter Finset Asymptotics

noncomputable section

abbrev Point := Erdos735.Point

open Erdos735

/-! ## The exact problem and its threshold -/

/-- No `k` points of `A` lie on one affine line. -/
def NoKCollinear (A : Finset Point) (k : ℕ) : Prop :=
  ∀ B : Finset Point, B ⊆ A → B.card = k → ¬ Collinear ℝ (B : Set Point)

/-- An `r`-point subset of `A` whose every joining line is ordinary with respect to `A`. -/
def HasOrdinaryClique (A : Finset Point) (r : ℕ) : Prop :=
  ∃ B : Finset Point, B ⊆ A ∧ B.card = r ∧
    ∀ p ∈ B, ∀ q ∈ B, p ≠ q → OrdinaryPair A p q

/-- `t` ordinary lines force an all-ordinary `r`-set among all `n`-point
configurations with no `k` collinear points. -/
def ForcesOrdinaryClique (r k n t : ℕ) : Prop :=
  ∀ A : Finset Point, A.card = n → NoKCollinear A k →
    t ≤ ordinaryLineCount A → HasOrdinaryClique A r

/-- The least number of ordinary lines which forces an all-ordinary `r`-point subset. -/
noncomputable def f (r k n : ℕ) : ℕ :=
  sInf {t : ℕ | ForcesOrdinaryClique r k n t}

lemma ordinaryLineCount_le_choose (A : Finset Point) :
    ordinaryLineCount A ≤ A.card.choose 2 := by
  classical
  unfold ordinaryLineCount
  simpa using (ordinaryGraph A).card_edgeFinset_le_card_choose_two

lemma forces_choose_succ (r k n : ℕ) :
    ForcesOrdinaryClique r k n (n.choose 2 + 1) := by
  intro A hcard _ hlarge
  have hle := ordinaryLineCount_le_choose A
  rw [hcard] at hle
  omega

lemma forcingSet_nonempty (r k n : ℕ) :
    {t : ℕ | ForcesOrdinaryClique r k n t}.Nonempty :=
  ⟨n.choose 2 + 1, forces_choose_succ r k n⟩

lemma f_forces (r k n : ℕ) : ForcesOrdinaryClique r k n (f r k n) := by
  exact Nat.sInf_mem (forcingSet_nonempty r k n)

lemma counterexample_lower_bound {r k n e : ℕ} {A : Finset Point}
    (hcard : A.card = n) (hnok : NoKCollinear A k)
    (hclique : ¬ HasOrdinaryClique A r) (hedges : e ≤ ordinaryLineCount A) :
    e + 1 ≤ f r k n := by
  by_contra h
  have hfe : f r k n ≤ e := by omega
  exact hclique (f_forces r k n A hcard hnok (hfe.trans hedges))

/-! ## Point-set cliques and graph cliques -/

lemma hasOrdinaryClique_iff_not_cliqueFree (A : Finset Point) (r : ℕ) :
    HasOrdinaryClique A r ↔ ¬ (ordinaryGraph A).CliqueFree r := by
  classical
  constructor
  · rintro ⟨B, hBA, hcard, hpair⟩ hfree
    let e : {p // p ∈ B} ↪ {p // p ∈ A} :=
      ⟨fun p ↦ ⟨p.1, hBA p.2⟩, by
        intro p q h
        apply Subtype.ext
        change p.1 = q.1
        exact congrArg (fun z : {p // p ∈ A} ↦ z.1) h⟩
    let T : Finset {p // p ∈ A} := B.attach.map e
    have hTcard : T.card = r := by simp [T, hcard]
    have hTclique : (ordinaryGraph A).IsClique T := by
      rw [SimpleGraph.isClique_iff]
      intro p hp q hq hpq
      change p ∈ B.attach.map e at hp
      change q ∈ B.attach.map e at hq
      rw [Finset.mem_map] at hp hq
      obtain ⟨p', hp', rfl⟩ := hp
      obtain ⟨q', hq', rfl⟩ := hq
      rw [ordinaryGraph_adj]
      apply hpair p'.1 (by simpa using hp') q'.1 (by simpa using hq')
      intro hpq'
      apply hpq
      exact Subtype.ext hpq'
    exact hfree T ((ordinaryGraph A).isNClique_iff.2 ⟨hTclique, hTcard⟩)
  · intro hfree
    rw [SimpleGraph.CliqueFree] at hfree
    push Not at hfree
    obtain ⟨T, hT⟩ := hfree
    let valEmb : {p // p ∈ A} ↪ Point :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let B : Finset Point := T.map valEmb
    refine ⟨B, ?_, ?_, ?_⟩
    · intro p hp
      simp only [B, Finset.mem_map] at hp
      obtain ⟨p', _, rfl⟩ := hp
      exact p'.2
    · simpa [B] using hT.card_eq
    · intro p hp q hq hpq
      simp only [B, Finset.mem_map] at hp hq
      obtain ⟨p', hp', rfl⟩ := hp
      obtain ⟨q', hq', rfl⟩ := hq
      change OrdinaryPair A p'.1 q'.1
      rw [← ordinaryGraph_adj]
      exact hT.isClique hp' hq' (fun h ↦ hpq (congrArg Subtype.val h))

lemma cliqueFree_of_no_ordinaryClique {A : Finset Point} {r : ℕ}
    (h : ¬ HasOrdinaryClique A r) : (ordinaryGraph A).CliqueFree r := by
  rwa [hasOrdinaryClique_iff_not_cliqueFree, not_not] at h

/-! ## The Turán upper bound -/

/-- The exact finite Turán upper bound for the forcing threshold. -/
theorem f_le_turan (r k n : ℕ) (hr : 2 ≤ r) :
    f r k n ≤ (SimpleGraph.turanGraph n (r - 1)).edgeFinset.card + 1 := by
  classical
  apply Nat.sInf_le
  intro A hcard _ hlarge
  by_contra hclique
  have hfree : (ordinaryGraph A).CliqueFree r := cliqueFree_of_no_ordinaryClique hclique
  have hr' : r = (r - 1) + 1 := by omega
  rw [hr'] at hfree
  have hupper := hfree.card_edgeFinset_le (r := r - 1)
  simp only [Fintype.card_coe, hcard] at hupper
  rw [← SimpleGraph.card_edgeFinset_turanGraph] at hupper
  simp only [ordinaryLineCount] at hlarge
  omega

/-- A denominator-free form of Erdős's displayed Turán estimate. -/
theorem f_turan_mul_bound (r k n : ℕ) (hr : 2 ≤ r) :
    2 * (r - 1) * (f r k n - 1) ≤ (r - 2) * n ^ 2 := by
  have hf := f_le_turan r k n hr
  have ht := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := r - 1)
  have hsub : f r k n - 1 ≤ (SimpleGraph.turanGraph n (r - 1)).edgeFinset.card := by
    omega
  calc
    2 * (r - 1) * (f r k n - 1) ≤
        2 * (r - 1) * (SimpleGraph.turanGraph n (r - 1)).edgeFinset.card := by
          exact Nat.mul_le_mul_left _ hsub
    _ ≤ (r - 2) * n ^ 2 := by simpa [Nat.sub_sub] using ht

/-- Erdős's displayed Turán upper bound, including the `+1` required by
the forcing-threshold convention. -/
theorem erdos960_upper_bound (r k n : ℕ) (hr : 2 ≤ r) :
    (f r k n : ℝ) ≤
      (1 - 1 / ((r - 1 : ℕ) : ℝ)) * (n : ℝ) ^ 2 / 2 + 1 := by
  let e := (SimpleGraph.turanGraph n (r - 1)).edgeFinset.card
  have hf : (f r k n : ℝ) ≤ (e : ℝ) + 1 := by
    exact_mod_cast f_le_turan r k n hr
  have htNat := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := r - 1)
  have ht : 2 * ((r - 1 : ℕ) : ℝ) * (e : ℝ) ≤
      ((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast (show 2 * (r - 1) * e ≤ (r - 2) * n ^ 2 by
      simpa [e, Nat.sub_sub] using htNat)
  have hd : 0 < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
  have he : (e : ℝ) ≤
      (((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ 2) /
        (2 * ((r - 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hd)).2
    nlinarith
  have hsub : ((r - 2 : ℕ) : ℝ) = ((r - 1 : ℕ) : ℝ) - 1 := by
    rw [show r - 2 = (r - 1) - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ r - 1)]
    norm_num
  calc
    (f r k n : ℝ) ≤ (e : ℝ) + 1 := hf
    _ ≤ (((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ 2) /
        (2 * ((r - 1 : ℕ) : ℝ)) + 1 := by linarith
    _ = (1 - 1 / ((r - 1 : ℕ) : ℝ)) * (n : ℝ) ^ 2 / 2 + 1 := by
      rw [hsub]
      field_simp [ne_of_gt hd]

/-! ## An explicit real nodal cubic -/

/-- The standard affine parametrization of `y² = x²(x - 1)`. -/
def nodalPoint (t : ℝ) : Point :=
  WithLp.toLp 2 ![1 + t ^ 2, t * (1 + t ^ 2)]

@[simp] lemma nodalPoint_apply_zero (t : ℝ) : nodalPoint t 0 = 1 + t ^ 2 := by
  simp [nodalPoint]

@[simp] lemma nodalPoint_apply_one (t : ℝ) : nodalPoint t 1 = t * (1 + t ^ 2) := by
  simp [nodalPoint]

/-- The determinant factorization underlying the cyclic construction. -/
lemma orientationDet_nodalPoint (a b c : ℝ) :
    orientationDet (nodalPoint a) (nodalPoint b) (nodalPoint c) =
      -(a - b) * (a - c) * (b - c) * (a * b + a * c + b * c - 1) := by
  simp [orientationDet, nodalPoint]
  ring

lemma nodalPoint_injective : Function.Injective nodalPoint := by
  intro a b hab
  have hx := congrArg (fun p : Point ↦ p 0) hab
  have hy := congrArg (fun p : Point ↦ p 1) hab
  simp only [nodalPoint_apply_zero] at hx
  simp only [nodalPoint_apply_one] at hy
  have ha : 0 < 1 + a ^ 2 := by positivity
  rw [← hx] at hy
  exact mul_right_cancel₀ (ne_of_gt ha) hy

/-- Three distinct nodal parameters give collinear points exactly when the
group-law factor vanishes. -/
lemma collinear3_nodalPoint_iff {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Collinear3 (nodalPoint a) (nodalPoint b) (nodalPoint c) ↔
      a * b + a * c + b * c = 1 := by
  rw [Collinear3, orientationDet_nodalPoint]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · simp only [neg_eq_zero] at h
          exfalso
          exact (sub_ne_zero.mpr hab) h
        · exfalso
          exact (sub_ne_zero.mpr hac) h
      · exfalso
        exact (sub_ne_zero.mpr hbc) h
    · linarith
  · intro h
    rw [show a * b + a * c + b * c - 1 = 0 by linarith, mul_zero]

/-- The elementary three-angle identity in the form used for cotangents. -/
lemma sin_three_add (a b c : ℝ) :
    Real.sin (a + b + c) =
      Real.cos a * Real.cos b * Real.sin c +
      Real.cos a * Real.sin b * Real.cos c +
      Real.sin a * Real.cos b * Real.cos c -
      Real.sin a * Real.sin b * Real.sin c := by
  rw [Real.sin_add, Real.sin_add, Real.cos_add]
  ring

/-- The cotangent group law on the nonsingular real locus of the nodal cubic. -/
lemma cot_pair_sum_eq_one_iff {a b c : ℝ}
    (ha : Real.sin a ≠ 0) (hb : Real.sin b ≠ 0) (hc : Real.sin c ≠ 0) :
    Real.cot a * Real.cot b + Real.cot a * Real.cot c +
        Real.cot b * Real.cot c = 1 ↔
      Real.sin (a + b + c) = 0 := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cot_eq_cos_div_sin]
  rw [sin_three_add]
  field_simp
  constructor <;> intro h <;> linarith

/-! ## The finite cyclic realization -/

/-- The angle representing the nonzero residue `i` modulo `M`. -/
def cyclicAngle (M i : ℕ) : ℝ := (i : ℝ) * Real.pi / M

/-- Vanishing of the sine detects divisibility of the integral numerator. -/
lemma sin_cyclicAngle_eq_zero_iff {M i : ℕ} (hM : 0 < M) :
    Real.sin (cyclicAngle M i) = 0 ↔ M ∣ i := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp h
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hreal : (z : ℝ) * (M : ℝ) = (i : ℝ) := by
      apply mul_right_cancel₀ hpi
      rw [mul_assoc, mul_comm (M : ℝ) Real.pi, ← mul_assoc, hz]
      simp only [cyclicAngle]
      field_simp
    have hzint : z * (M : ℤ) = (i : ℤ) := by exact_mod_cast hreal
    exact_mod_cast (show (M : ℤ) ∣ (i : ℤ) from
      ⟨z, by simpa [mul_comm] using hzint.symm⟩)
  · rintro ⟨d, rfl⟩
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    rw [cyclicAngle, Nat.cast_mul]
    convert Real.sin_nat_mul_pi d using 2 <;> field_simp

lemma cyclicAngle_pos {M i : ℕ} (hM : 0 < M) (hi : 0 < i) : 0 < cyclicAngle M i := by
  simp only [cyclicAngle]
  positivity

lemma cyclicAngle_lt_pi {M i : ℕ} (hiM : i < M) : cyclicAngle M i < Real.pi := by
  simp only [cyclicAngle]
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le i) hiM
  have hiR : (i : ℝ) < M := by exact_mod_cast hiM
  apply (div_lt_iff₀' (show (0 : ℝ) < M by positivity)).2
  nlinarith [Real.pi_pos]

lemma sin_cyclicAngle_ne_zero {M i : ℕ} (hM : 0 < M) (hi : i < M)
    (hi0 : i ≠ 0) : Real.sin (cyclicAngle M i) ≠ 0 := by
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (cyclicAngle_pos hM (Nat.pos_of_ne_zero hi0)) (cyclicAngle_lt_pi hi))

/-- The point indexed by a nonzero cyclic residue. -/
def cyclicPoint (M i : ℕ) : Point := nodalPoint (Real.cot (cyclicAngle M i))

lemma cot_injective_on_Ioo_zero_pi {a b : ℝ}
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (h : Real.cot a = Real.cot b) : a = b := by
  have hsa : Real.sin a ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ha0 haπ)
  have hsb : Real.sin b ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hb0 hbπ)
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin] at h
  have hcross : Real.cos a * Real.sin b = Real.cos b * Real.sin a := by
    field_simp [hsa, hsb] at h
    simpa [mul_comm] using h
  have hsin : Real.sin (b - a) = 0 := by
    rw [Real.sin_sub]
    linarith
  have hba : b - a = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hsin
  linarith

lemma cyclicPoint_injective {M i j : ℕ} (hi0 : i ≠ 0) (hj0 : j ≠ 0)
    (hiM : i < M) (hjM : j < M) (h : cyclicPoint M i = cyclicPoint M j) : i = j := by
  have hcot : Real.cot (cyclicAngle M i) = Real.cot (cyclicAngle M j) :=
    nodalPoint_injective h
  have hMnat : 0 < M := lt_of_lt_of_le (Nat.pos_of_ne_zero hi0) hiM.le
  have hang : cyclicAngle M i = cyclicAngle M j := cot_injective_on_Ioo_zero_pi
    (cyclicAngle_pos hMnat (Nat.pos_of_ne_zero hi0)) (cyclicAngle_lt_pi hiM)
    (cyclicAngle_pos hMnat (Nat.pos_of_ne_zero hj0)) (cyclicAngle_lt_pi hjM) hcot
  simp only [cyclicAngle] at hang
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast hMnat.ne'
  field_simp [hM] at hang
  exact_mod_cast hang

lemma cyclicAngle_add_add (M i j k : ℕ) :
    cyclicAngle M i + cyclicAngle M j + cyclicAngle M k = cyclicAngle M (i + j + k) := by
  simp only [cyclicAngle, Nat.cast_add]
  ring

/-- The incidence law: distinct nonzero cyclic points are collinear exactly
when their three indices sum to zero modulo `M`. -/
lemma collinear3_cyclicPoint_iff {M i j k : ℕ} (hM : 0 < M)
    (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hk0 : k ≠ 0)
    (hiM : i < M) (hjM : j < M) (hkM : k < M)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Collinear3 (cyclicPoint M i) (cyclicPoint M j) (cyclicPoint M k) ↔
      M ∣ i + j + k := by
  let a := Real.cot (cyclicAngle M i)
  let b := Real.cot (cyclicAngle M j)
  let c := Real.cot (cyclicAngle M k)
  have hab : a ≠ b := by
    intro heq
    apply hij
    apply cyclicPoint_injective hi0 hj0 hiM hjM
    exact congrArg nodalPoint heq
  have hac : a ≠ c := by
    intro heq
    apply hik
    apply cyclicPoint_injective hi0 hk0 hiM hkM
    exact congrArg nodalPoint heq
  have hbc : b ≠ c := by
    intro heq
    apply hjk
    apply cyclicPoint_injective hj0 hk0 hjM hkM
    exact congrArg nodalPoint heq
  have hsi := sin_cyclicAngle_ne_zero hM hiM hi0
  have hsj := sin_cyclicAngle_ne_zero hM hjM hj0
  have hsk := sin_cyclicAngle_ne_zero hM hkM hk0
  change Collinear3 (nodalPoint a) (nodalPoint b) (nodalPoint c) ↔ M ∣ i + j + k
  rw [collinear3_nodalPoint_iff hab hac hbc,
    cot_pair_sum_eq_one_iff hsi hsj hsk, cyclicAngle_add_add,
    sin_cyclicAngle_eq_zero_iff hM]

/-- The cyclic realization, now indexed intrinsically by `ZMod M`. -/
def zmodPoint (M : ℕ) (i : ZMod M) : Point := cyclicPoint M i.val

lemma zmodPoint_injective_of_ne_zero {M : ℕ} [NeZero M] {i j : ZMod M}
    (hi : i ≠ 0) (hj : j ≠ 0) (h : zmodPoint M i = zmodPoint M j) : i = j := by
  apply ZMod.val_injective M
  apply cyclicPoint_injective
  · exact (ZMod.val_eq_zero i).not.mpr hi
  · exact (ZMod.val_eq_zero j).not.mpr hj
  · exact ZMod.val_lt i
  · exact ZMod.val_lt j
  · exact h

lemma collinear3_zmodPoint_iff {M : ℕ} [NeZero M] {i j k : ZMod M}
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Collinear3 (zmodPoint M i) (zmodPoint M j) (zmodPoint M k) ↔ i + j + k = 0 := by
  have hM : 0 < M := NeZero.pos M
  rw [zmodPoint, zmodPoint, zmodPoint,
    collinear3_cyclicPoint_iff hM
      ((ZMod.val_eq_zero i).not.mpr hi) ((ZMod.val_eq_zero j).not.mpr hj)
      ((ZMod.val_eq_zero k).not.mpr hk) (ZMod.val_lt i) (ZMod.val_lt j) (ZMod.val_lt k)]
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp
  · exact fun h ↦ hij (ZMod.val_injective M h)
  · exact fun h ↦ hik (ZMod.val_injective M h)
  · exact fun h ↦ hjk (ZMod.val_injective M h)

/-! ## Incidence consequences for finite index sets -/

/-- The planar point set represented by a finite set of nonzero residues. -/
def pointSet (M : ℕ) (I : Finset (ZMod M)) : Finset Point :=
  I.image (zmodPoint M)

lemma mem_pointSet {M : ℕ} {I : Finset (ZMod M)} {p : Point} :
    p ∈ pointSet M I ↔ ∃ i ∈ I, zmodPoint M i = p := by
  simp [pointSet]

lemma card_pointSet {M : ℕ} [NeZero M] {I : Finset (ZMod M)}
    (hI0 : ∀ i ∈ I, i ≠ 0) : (pointSet M I).card = I.card := by
  classical
  rw [pointSet, Finset.card_image_iff]
  intro i hi j hj h
  exact zmodPoint_injective_of_ne_zero (hI0 i hi) (hI0 j hj) h

lemma ordinaryPair_zmodPoint_of_neg_add_not_mem {M : ℕ} [NeZero M]
    {I : Finset (ZMod M)} (hI0 : ∀ x ∈ I, x ≠ 0) {i j : ZMod M}
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) (hthird : -(i + j) ∉ I) :
    OrdinaryPair (pointSet M I) (zmodPoint M i) (zmodPoint M j) := by
  refine ⟨mem_pointSet.2 ⟨i, hi, rfl⟩, mem_pointSet.2 ⟨j, hj, rfl⟩,
    fun h ↦ hij (zmodPoint_injective_of_ne_zero (hI0 i hi) (hI0 j hj) h), ?_⟩
  intro p hp hcol
  obtain ⟨k, hk, rfl⟩ := mem_pointSet.1 hp
  by_cases hki : k = i
  · exact Or.inl (congrArg (zmodPoint M) hki)
  by_cases hkj : k = j
  · exact Or.inr (congrArg (zmodPoint M) hkj)
  have hsum : i + j + k = 0 :=
    (collinear3_zmodPoint_iff (hI0 i hi) (hI0 j hj) (hI0 k hk) hij
      (fun h ↦ hki h.symm) (fun h ↦ hkj h.symm)).mp hcol
  have hkthird : k = -(i + j) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum
  exact (hthird (hkthird ▸ hk)).elim

lemma not_ordinaryPair_zmodPoint_of_neg_add_mem {M : ℕ} [NeZero M]
    {I : Finset (ZMod M)} (hI0 : ∀ x ∈ I, x ≠ 0) {i j : ZMod M}
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (hthird : -(i + j) ∈ I) (hti : -(i + j) ≠ i) (htj : -(i + j) ≠ j) :
    ¬ OrdinaryPair (pointSet M I) (zmodPoint M i) (zmodPoint M j) := by
  intro hord
  let k := -(i + j)
  have hk0 : k ≠ 0 := hI0 k hthird
  have hcol : Collinear3 (zmodPoint M i) (zmodPoint M j) (zmodPoint M k) := by
    apply (collinear3_zmodPoint_iff (hI0 i hi) (hI0 j hj) hk0 hij hti.symm htj.symm).2
    simp [k, add_assoc]
  rcases hord.2.2.2 (zmodPoint M k) (mem_pointSet.2 ⟨k, hthird, rfl⟩) hcol with h | h
  · exact hti (zmodPoint_injective_of_ne_zero hk0 (hI0 i hi) h)
  · exact htj (zmodPoint_injective_of_ne_zero hk0 (hI0 j hj) h)

lemma four_zmodPoints_not_collinear {M : ℕ} [NeZero M] {i j k l : ZMod M}
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) (hl : l ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ¬ Collinear ℝ ({zmodPoint M i, zmodPoint M j, zmodPoint M k, zmodPoint M l} : Set Point) := by
  intro hcol
  have hpq : zmodPoint M i ≠ zmodPoint M j :=
    fun h ↦ hij (zmodPoint_injective_of_ne_zero hi hj h)
  have hkline : zmodPoint M k ∈ line[ℝ, zmodPoint M i, zmodPoint M j] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq
  have hlline : zmodPoint M l ∈ line[ℝ, zmodPoint M i, zmodPoint M j] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq
  have hijk : i + j + k = 0 :=
    (collinear3_zmodPoint_iff hi hj hk hij hik hjk).mp
      ((collinear3_iff_mem_affineSpan_pair hpq).2 hkline)
  have hijl : i + j + l = 0 :=
    (collinear3_zmodPoint_iff hi hj hl hij hil hjl).mp
      ((collinear3_iff_mem_affineSpan_pair hpq).2 hlline)
  apply hkl
  rw [← add_left_cancel_iff (a := i + j)]
  rw [hijk, hijl]

/-- Every line meets a cyclic point set in at most three points. -/
lemma pointSet_no_four_collinear {M : ℕ} [NeZero M] {I : Finset (ZMod M)}
    (hI0 : ∀ x ∈ I, x ≠ 0) : NoKCollinear (pointSet M I) 4 := by
  intro B hBA hcard hcol
  obtain ⟨p, q, r, u, hpq, hpr, hpu, hqr, hqu, hru, rfl⟩ := Finset.card_eq_four.mp hcard
  obtain ⟨i, hi, hip⟩ := mem_pointSet.1 (hBA (by simp : p ∈ ({p, q, r, u} : Finset Point)))
  obtain ⟨j, hj, hjq⟩ := mem_pointSet.1 (hBA (by simp : q ∈ ({p, q, r, u} : Finset Point)))
  obtain ⟨k, hk, hkr⟩ := mem_pointSet.1 (hBA (by simp : r ∈ ({p, q, r, u} : Finset Point)))
  obtain ⟨l, hl, hlu⟩ := mem_pointSet.1 (hBA (by simp : u ∈ ({p, q, r, u} : Finset Point)))
  subst p; subst q; subst r; subst u
  apply four_zmodPoints_not_collinear (hI0 i hi) (hI0 j hj) (hI0 k hk) (hI0 l hl)
  · exact fun h ↦ hpq (congrArg (zmodPoint M) h)
  · exact fun h ↦ hpr (congrArg (zmodPoint M) h)
  · exact fun h ↦ hpu (congrArg (zmodPoint M) h)
  · exact fun h ↦ hqr (congrArg (zmodPoint M) h)
  · exact fun h ↦ hqu (congrArg (zmodPoint M) h)
  · exact fun h ↦ hru (congrArg (zmodPoint M) h)
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using hcol

lemma noKCollinear_of_no_four {A : Finset Point} {k : ℕ} (hk : 4 ≤ k)
    (hfour : NoKCollinear A 4) : NoKCollinear A k := by
  intro B hBA hcard hcol
  obtain ⟨C, hCB, hCcard⟩ := Finset.exists_subset_card_eq (s := B) (n := 4) (by omega)
  apply hfour C (hCB.trans hBA) hCcard
  exact Collinear.subset (by exact_mod_cast hCB) hcol

/-! ## APSSV's six cosets and the five-point size adjustment -/

def modulus (m : ℕ) : ℕ := 7 * m

def baseNat (m : ℕ) (x : Fin 6 × Fin m) : ℕ := x.1.val + 1 + 7 * x.2.val

lemma baseNat_pos (m : ℕ) (x : Fin 6 × Fin m) : 0 < baseNat m x := by
  simp [baseNat]

lemma baseNat_lt_modulus {m : ℕ} (hm : 0 < m) (x : Fin 6 × Fin m) :
    baseNat m x < modulus m := by
  have hc := x.1.isLt
  have ha := x.2.isLt
  simp only [baseNat, modulus]
  omega

lemma baseNat_injective {m : ℕ} (hm : 0 < m) : Function.Injective (baseNat m) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    have hx := x.1.isLt
    have hy := y.1.isLt
    have ha := x.2.isLt
    have hb := y.2.isLt
    simp only [baseNat] at h
    omega
  · apply Fin.ext
    have hx := x.1.isLt
    have hy := y.1.isLt
    have ha := x.2.isLt
    have hb := y.2.isLt
    simp only [baseNat] at h
    omega

def baseEmbedding (m : ℕ) (hm : 0 < m) : Fin 6 × Fin m ↪ ZMod (modulus m) where
  toFun x := (baseNat m x : ZMod (modulus m))
  inj' := by
    intro x y h
    apply baseNat_injective hm
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h |>.eq_of_lt_of_lt
      (baseNat_lt_modulus hm x) (baseNat_lt_modulus hm y)

def baseIndices (m : ℕ) (hm : 0 < m) : Finset (ZMod (modulus m)) :=
  Finset.univ.map (baseEmbedding m hm)

lemma card_baseIndices (m : ℕ) (hm : 0 < m) : (baseIndices m hm).card = 6 * m := by
  simp [baseIndices]

def extraNat (m : ℕ) (a : Fin 5) : ℕ :=
  ![7, 14, modulus m - 21, 21, modulus m - 28] a

lemma extraNat_spec (m : ℕ) :
    extraNat m 0 = 7 ∧ extraNat m 1 = 14 ∧ extraNat m 2 = modulus m - 21 ∧
      extraNat m 3 = 21 ∧ extraNat m 4 = modulus m - 28 := by
  simp [extraNat]

lemma extraNat_pos {m : ℕ} (hm : 12 ≤ m) (a : Fin 5) : 0 < extraNat m a := by
  fin_cases a <;> simp [extraNat, modulus] <;> omega

lemma extraNat_lt_modulus {m : ℕ} (hm : 12 ≤ m) (a : Fin 5) :
    extraNat m a < modulus m := by
  fin_cases a <;> simp [extraNat, modulus] <;> omega

lemma seven_dvd_modulus_sub (m c : ℕ) : 7 ∣ modulus m - 7 * c := by
  rw [modulus, ← Nat.mul_sub_left_distrib]
  exact dvd_mul_right 7 (m - c)

lemma extraNat_dvd_seven {m : ℕ} (a : Fin 5) : 7 ∣ extraNat m a := by
  fin_cases a
  · simp [extraNat]
  · simp [extraNat]
  · simpa [extraNat] using seven_dvd_modulus_sub m 3
  · simp [extraNat]
  · simpa [extraNat] using seven_dvd_modulus_sub m 4

lemma extraNat_injective {m : ℕ} (hm : 12 ≤ m) : Function.Injective (extraNat m) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [extraNat, modulus] at h ⊢ <;> omega

def extraEmbedding (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    Fin s ↪ ZMod (modulus m) where
  toFun a := (extraNat m (Fin.castLE hs a) : ZMod (modulus m))
  inj' := by
    intro a b h
    have hn : extraNat m (Fin.castLE hs a) = extraNat m (Fin.castLE hs b) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp h |>.eq_of_lt_of_lt
        (extraNat_lt_modulus hm _) (extraNat_lt_modulus hm _)
    exact Fin.castLE_injective hs (extraNat_injective hm hn)

def extraIndices (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    Finset (ZMod (modulus m)) := Finset.univ.map (extraEmbedding m s hm hs)

lemma card_extraIndices (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    (extraIndices m s hm hs).card = s := by
  simp [extraIndices]

lemma natCast_ne_zero_of_pos_of_lt {M a : ℕ} (ha0 : 0 < a) (haM : a < M) :
    (a : ZMod M) ≠ 0 := by
  intro h
  have hdvd : M ∣ a := (ZMod.natCast_eq_zero_iff a M).mp h
  exact (not_le_of_gt haM) (Nat.le_of_dvd ha0 hdvd)

lemma baseIndices_ne_zero {m : ℕ} (hm : 0 < m) {z : ZMod (modulus m)}
    (hz : z ∈ baseIndices m hm) : z ≠ 0 := by
  simp only [baseIndices, Finset.mem_map] at hz
  obtain ⟨x, _, rfl⟩ := hz
  exact natCast_ne_zero_of_pos_of_lt (baseNat_pos m x) (baseNat_lt_modulus hm x)

lemma val_baseEmbedding {m : ℕ} (hm : 0 < m) (x : Fin 6 × Fin m) :
    ((baseEmbedding m hm x : ZMod (modulus m))).val = baseNat m x := by
  change ((baseNat m x : ZMod (modulus m))).val = baseNat m x
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (baseNat_lt_modulus hm x)]

lemma mem_baseIndices_iff {m : ℕ} (hm : 0 < m) (z : ZMod (modulus m)) :
    z ∈ baseIndices m hm ↔ ¬ 7 ∣ z.val := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  constructor
  · intro hz hdvd
    simp only [baseIndices, Finset.mem_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    rw [val_baseEmbedding] at hdvd
    obtain ⟨d, hd⟩ := hdvd
    have hc := x.1.isLt
    simp only [baseNat] at hd
    omega
  · intro hn
    have hrem0 : z.val % 7 ≠ 0 := by
      rwa [Nat.dvd_iff_mod_eq_zero] at hn
    have hrempos : 0 < z.val % 7 := Nat.pos_of_ne_zero hrem0
    have hremle : z.val % 7 ≤ 6 := by omega
    have hdivlt : z.val / 7 < m := by
      have hzlt := ZMod.val_lt z
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 7)).2
      simpa only [modulus, mul_comm] using hzlt
    let x : Fin 6 × Fin m :=
      (⟨z.val % 7 - 1, by omega⟩, ⟨z.val / 7, hdivlt⟩)
    rw [baseIndices, Finset.mem_map]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    apply ZMod.val_injective (modulus m)
    rw [val_baseEmbedding]
    simp only [x, baseNat]
    have hdecomp := (Nat.mod_add_div z.val 7).symm
    omega

def residueSeven (m : ℕ) : ZMod (modulus m) →+ ZMod 7 :=
  ZMod.castHom (m := 7) (n := modulus m) (by
    unfold modulus
    exact dvd_mul_right 7 m) (ZMod 7)

lemma residueSeven_apply (m : ℕ) (hm : 0 < m) (z : ZMod (modulus m)) :
    residueSeven m z = (z.val : ZMod 7) := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  change (ZMod.cast z : ZMod 7) = (z.val : ZMod 7)
  exact ZMod.cast_eq_val z

lemma mem_baseIndices_iff_residueSeven_ne_zero {m : ℕ} (hm : 0 < m)
    (z : ZMod (modulus m)) : z ∈ baseIndices m hm ↔ residueSeven m z ≠ 0 := by
  rw [mem_baseIndices_iff hm, residueSeven_apply m hm]
  exact not_congr (ZMod.natCast_eq_zero_iff z.val 7).symm

def leftResidues : Finset (ZMod 7) := {1, 2, 4}

def sameBaseSide (a b : ZMod 7) : Prop :=
  (a.val = 1 ∨ a.val = 2 ∨ a.val = 4) ↔ (b.val = 1 ∨ b.val = 2 ∨ b.val = 4)

lemma zmod_ne_of_val_ne {n : ℕ} {a b : ZMod n} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab ↦ h (congrArg ZMod.val hab)

lemma sameBaseSide_third (a b : ZMod 7) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsame : sameBaseSide a b) :
    -(a + b) ≠ 0 ∧ -(a + b) ≠ a ∧ -(a + b) ≠ b := by
  have table : ∀ i j : Fin 7, i.val ≠ 0 → j.val ≠ 0 →
      ((i.val = 1 ∨ i.val = 2 ∨ i.val = 4) ↔
        (j.val = 1 ∨ j.val = 2 ∨ j.val = 4)) →
      -((i.val : ZMod 7) + j.val) ≠ 0 ∧
        -((i.val : ZMod 7) + j.val) ≠ i.val ∧
        -((i.val : ZMod 7) + j.val) ≠ j.val := by decide
  have ha0 : a.val ≠ 0 := by
    intro h
    apply ha
    apply ZMod.val_injective 7
    simpa [h]
  have hb0 : b.val ≠ 0 := by
    intro h
    apply hb
    apply ZMod.val_injective 7
    simpa [h]
  simpa only [ZMod.natCast_zmod_val] using
    table ⟨a.val, ZMod.val_lt a⟩ ⟨b.val, ZMod.val_lt b⟩ ha0 hb0 hsame

lemma extraIndices_ne_zero {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    {z : ZMod (modulus m)} (hz : z ∈ extraIndices m s hm hs) : z ≠ 0 := by
  simp only [extraIndices, Finset.mem_map] at hz
  obtain ⟨a, _, rfl⟩ := hz
  exact natCast_ne_zero_of_pos_of_lt (extraNat_pos hm _) (extraNat_lt_modulus hm _)

lemma disjoint_base_extra {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Disjoint (baseIndices m (by omega)) (extraIndices m s hm hs) := by
  rw [Finset.disjoint_left]
  intro z hzbase hzextra
  simp only [baseIndices, Finset.mem_map] at hzbase
  simp only [extraIndices, Finset.mem_map] at hzextra
  obtain ⟨x, _, rfl⟩ := hzbase
  obtain ⟨a, _, ha⟩ := hzextra
  have heq : baseNat m x = extraNat m (Fin.castLE hs a) :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp ha |>.eq_of_lt_of_lt
      (extraNat_lt_modulus hm _) (baseNat_lt_modulus (by omega) x)).symm
  have hdvd := extraNat_dvd_seven (m := m) (Fin.castLE hs a)
  simp only [baseNat] at heq
  have hc := x.1.isLt
  obtain ⟨d, hd⟩ := hdvd
  omega

def constructionIndices (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    Finset (ZMod (modulus m)) :=
  baseIndices m (by omega) ∪ extraIndices m s hm hs

lemma card_constructionIndices (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    (constructionIndices m s hm hs).card = 6 * m + s := by
  rw [constructionIndices, Finset.card_union_of_disjoint (disjoint_base_extra hm hs),
    card_baseIndices, card_extraIndices]

lemma constructionIndices_ne_zero {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    ∀ z ∈ constructionIndices m s hm hs, z ≠ 0 := by
  intro z hz
  rw [constructionIndices, Finset.mem_union] at hz
  rcases hz with hz | hz
  · exact baseIndices_ne_zero (by omega) hz
  · exact extraIndices_ne_zero hm hs hz

def construction (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) : Finset Point :=
  pointSet (modulus m) (constructionIndices m s hm hs)

lemma card_construction (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    (construction m s hm hs).card = 6 * m + s := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  rw [construction, card_pointSet (constructionIndices_ne_zero hm hs),
    card_constructionIndices]

/-! ## The bipartition of the ordinary-line graph -/

lemma residueSeven_extra_eq_zero {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    {z : ZMod (modulus m)} (hz : z ∈ extraIndices m s hm hs) :
    residueSeven m z = 0 := by
  simp only [extraIndices, Finset.mem_map] at hz
  obtain ⟨a, _, rfl⟩ := hz
  rw [residueSeven_apply m (by omega)]
  change (((extraNat m (Fin.castLE hs a) : ZMod (modulus m))).val : ZMod 7) = 0
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (extraNat_lt_modulus hm _)]
  exact (ZMod.natCast_eq_zero_iff _ _).2 (extraNat_dvd_seven _)

lemma base_sameSide_third {m : ℕ} (hm : 0 < m) {i j : ZMod (modulus m)}
    (hi : i ∈ baseIndices m hm) (hj : j ∈ baseIndices m hm)
    (hsame : sameBaseSide (residueSeven m i) (residueSeven m j)) :
    -(i + j) ∈ baseIndices m hm ∧ -(i + j) ≠ i ∧ -(i + j) ≠ j := by
  have hi0 := (mem_baseIndices_iff_residueSeven_ne_zero hm i).1 hi
  have hj0 := (mem_baseIndices_iff_residueSeven_ne_zero hm j).1 hj
  have htable := sameBaseSide_third (residueSeven m i) (residueSeven m j) hi0 hj0 hsame
  have hmap : residueSeven m (-(i + j)) = -(residueSeven m i + residueSeven m j) := by
    simp
  refine ⟨(mem_baseIndices_iff_residueSeven_ne_zero hm _).2 ?_, ?_, ?_⟩
  · simpa only [hmap] using htable.1
  · intro h
    apply htable.2.1
    simpa only [hmap] using congrArg (residueSeven m) h
  · intro h
    apply htable.2.2
    simpa only [hmap] using congrArg (residueSeven m) h

lemma neg_nonzero_ne_self_mod_seven (a : ZMod 7) (ha : a ≠ 0) :
    -a ≠ 0 ∧ -a ≠ a := by
  have table : ∀ i : Fin 7, i.val ≠ 0 →
      -(i.val : ZMod 7) ≠ 0 ∧ -(i.val : ZMod 7) ≠ i.val := by decide
  have ha0 : a.val ≠ 0 := by
    intro h
    apply ha
    apply ZMod.val_injective 7
    simpa [h]
  simpa only [ZMod.natCast_zmod_val] using table ⟨a.val, ZMod.val_lt a⟩ ha0

lemma base_extra_third {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    {i j : ZMod (modulus m)} (hi : i ∈ baseIndices m (by omega))
    (hj : j ∈ extraIndices m s hm hs) :
    -(i + j) ∈ baseIndices m (by omega) ∧ -(i + j) ≠ i ∧ -(i + j) ≠ j := by
  have hri := (mem_baseIndices_iff_residueSeven_ne_zero (by omega) i).1 hi
  have hrj := residueSeven_extra_eq_zero hm hs hj
  have hneg := neg_nonzero_ne_self_mod_seven (residueSeven m i) hri
  have hmap : residueSeven m (-(i + j)) = -(residueSeven m i) := by
    simp [hrj]
  refine ⟨(mem_baseIndices_iff_residueSeven_ne_zero (by omega) _).2 ?_, ?_, ?_⟩
  · simpa only [hmap] using hneg.1
  · intro h
    apply hneg.2
    simpa only [hmap] using congrArg (residueSeven m) h
  · intro h
    have := congrArg (residueSeven m) h
    rw [hmap, hrj] at this
    exact hneg.1 this

/-- The color used on the at most five added subgroup points.  For two points
the colors are opposite; for three they are all on one side; from four on,
the first three are on the left and the remaining two are on the right. -/
def extraLeft (s : ℕ) (a : Fin s) : Prop :=
  (s = 2 ∧ a.val = 0) ∨ (s ≠ 2 ∧ s ≤ 3) ∨ (s ≠ 2 ∧ ¬ s ≤ 3 ∧ a.val ≤ 2)

instance instDecidableExtraLeft (s : ℕ) (a : Fin s) : Decidable (extraLeft s a) := by
  unfold extraLeft
  infer_instance

def extraCoeffVal (a : ℕ) : ℤ :=
  if a = 0 then 1 else if a = 1 then 2 else if a = 2 then -3 else if a = 3 then 3 else -4

lemma extraEmbedding_eq_coeff {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (a : Fin s) :
    extraEmbedding m s hm hs a =
      (7 : ZMod (modulus m)) * (extraCoeffVal a.val : ZMod (modulus m)) := by
  have hM21 : 21 ≤ modulus m := by simp [modulus]; omega
  have hM28 : 28 ≤ modulus m := by simp [modulus]; omega
  generalize hc : Fin.castLE hs a = c
  have hav : a.val = c.val := by
    simpa using congrArg Fin.val hc
  fin_cases c
  · simp [extraEmbedding, extraNat, extraCoeffVal, hc, hav]
  · simp [extraEmbedding, extraNat, extraCoeffVal, hc, hav]
    ring
  · simp [extraEmbedding, extraNat, extraCoeffVal, hc, hav]
    rw [Nat.cast_sub hM21]
    simp
    ring
  · simp [extraEmbedding, extraNat, extraCoeffVal, hc, hav]
    ring
  · simp [extraEmbedding, extraNat, extraCoeffVal, hc, hav]
    rw [Nat.cast_sub hM28]
    simp
    ring

lemma extra_sameSide_third {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (a b : Fin s) (hab : a ≠ b) (hsame : extraLeft s a ↔ extraLeft s b) :
    ∃ c : Fin s, c ≠ a ∧ c ≠ b ∧
      -(extraEmbedding m s hm hs a + extraEmbedding m s hm hs b) =
        extraEmbedding m s hm hs c := by
  have hs_cases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Fin.elim0 a
  · fin_cases a
    fin_cases b
    exact (hab rfl).elim
  · have table : ∀ a b : Fin 2, a ≠ b →
        (extraLeft 2 a ↔ extraLeft 2 b) → False := by decide
    exact (table a b hab hsame).elim
  · have table : ∀ a b : Fin 3, a ≠ b →
        (extraLeft 3 a ↔ extraLeft 3 b) →
        ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧
          -(extraCoeffVal a.val + extraCoeffVal b.val) = extraCoeffVal c.val := by decide
    obtain ⟨c, hca, hcb, hc⟩ := table a b hab hsame
    refine ⟨c, hca, hcb, ?_⟩
    simp only [extraEmbedding_eq_coeff]
    have hcz := congrArg (fun z : ℤ ↦ (z : ZMod (modulus m))) hc
    push_cast at hcz
    calc
      -(7 * (extraCoeffVal a.val : ZMod (modulus m)) +
          7 * (extraCoeffVal b.val : ZMod (modulus m))) =
          7 * (-((extraCoeffVal a.val : ZMod (modulus m)) + extraCoeffVal b.val)) := by ring
      _ = 7 * (extraCoeffVal c.val : ZMod (modulus m)) := by rw [hcz]
  · have table : ∀ a b : Fin 4, a ≠ b →
        (extraLeft 4 a ↔ extraLeft 4 b) →
        ∃ c : Fin 4, c ≠ a ∧ c ≠ b ∧
          -(extraCoeffVal a.val + extraCoeffVal b.val) = extraCoeffVal c.val := by decide
    obtain ⟨c, hca, hcb, hc⟩ := table a b hab hsame
    refine ⟨c, hca, hcb, ?_⟩
    simp only [extraEmbedding_eq_coeff]
    have hcz := congrArg (fun z : ℤ ↦ (z : ZMod (modulus m))) hc
    push_cast at hcz
    calc
      -(7 * (extraCoeffVal a.val : ZMod (modulus m)) +
          7 * (extraCoeffVal b.val : ZMod (modulus m))) =
          7 * (-((extraCoeffVal a.val : ZMod (modulus m)) + extraCoeffVal b.val)) := by ring
      _ = 7 * (extraCoeffVal c.val : ZMod (modulus m)) := by rw [hcz]
  · have table : ∀ a b : Fin 5, a ≠ b →
        (extraLeft 5 a ↔ extraLeft 5 b) →
        ∃ c : Fin 5, c ≠ a ∧ c ≠ b ∧
          -(extraCoeffVal a.val + extraCoeffVal b.val) = extraCoeffVal c.val := by decide
    obtain ⟨c, hca, hcb, hc⟩ := table a b hab hsame
    refine ⟨c, hca, hcb, ?_⟩
    simp only [extraEmbedding_eq_coeff]
    have hcz := congrArg (fun z : ℤ ↦ (z : ZMod (modulus m))) hc
    push_cast at hcz
    calc
      -(7 * (extraCoeffVal a.val : ZMod (modulus m)) +
          7 * (extraCoeffVal b.val : ZMod (modulus m))) =
          7 * (-((extraCoeffVal a.val : ZMod (modulus m)) + extraCoeffVal b.val)) := by ring
      _ = 7 * (extraCoeffVal c.val : ZMod (modulus m)) := by rw [hcz]

def indexLeft (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5)
    (z : ZMod (modulus m)) : Prop :=
  (z ∈ baseIndices m (by omega) ∧
    ((residueSeven m z).val = 1 ∨ (residueSeven m z).val = 2 ∨
      (residueSeven m z).val = 4)) ∨
  ∃ a : Fin s, extraEmbedding m s hm hs a = z ∧ extraLeft s a

lemma indexLeft_base_iff {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    {z : ZMod (modulus m)} (hz : z ∈ baseIndices m (by omega)) :
    indexLeft m s hm hs z ↔
      ((residueSeven m z).val = 1 ∨ (residueSeven m z).val = 2 ∨
        (residueSeven m z).val = 4) := by
  constructor
  · rintro (⟨_, h⟩ | ⟨a, ha, _⟩)
    · exact h
    · have hea : extraEmbedding m s hm hs a ∈ extraIndices m s hm hs := by
        simp [extraIndices]
      rw [ha] at hea
      exact (Finset.disjoint_left.1 (disjoint_base_extra hm hs) hz hea).elim
  · exact fun h ↦ Or.inl ⟨hz, h⟩

lemma indexLeft_extra_iff {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (a : Fin s) :
    indexLeft m s hm hs (extraEmbedding m s hm hs a) ↔ extraLeft s a := by
  have hea : extraEmbedding m s hm hs a ∈ extraIndices m s hm hs := by
    simp [extraIndices]
  constructor
  · rintro (⟨hb, _⟩ | ⟨b, hba, hb⟩)
    · exact (Finset.disjoint_left.1 (disjoint_base_extra hm hs) hb hea).elim
    · have : b = a := (extraEmbedding m s hm hs).injective hba
      simpa [this] using hb
  · exact fun h ↦ Or.inr ⟨a, rfl, h⟩

lemma sameIndexSide_not_ordinary {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    {i j : ZMod (modulus m)}
    (hi : i ∈ constructionIndices m s hm hs)
    (hj : j ∈ constructionIndices m s hm hs) (hij : i ≠ j)
    (hsame : indexLeft m s hm hs i ↔ indexLeft m s hm hs j) :
    ¬ OrdinaryPair (construction m s hm hs) (zmodPoint (modulus m) i)
      (zmodPoint (modulus m) j) := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  have hI0 := constructionIndices_ne_zero hm hs
  rw [constructionIndices, Finset.mem_union] at hi hj
  rw [construction]
  rcases hi with hib | hie <;> rcases hj with hjb | hje
  · have hside : sameBaseSide (residueSeven m i) (residueSeven m j) := by
      exact (indexLeft_base_iff hm hs hib).symm.trans
        (hsame.trans (indexLeft_base_iff hm hs hjb))
    obtain ⟨htb, hti, htj⟩ := base_sameSide_third (by omega) hib hjb hside
    apply not_ordinaryPair_zmodPoint_of_neg_add_mem hI0
      (Finset.mem_union_left _ hib) (Finset.mem_union_left _ hjb) hij
      (Finset.mem_union_left _ htb) hti htj
  · obtain ⟨htb, hti, htj⟩ := base_extra_third hm hs hib hje
    apply not_ordinaryPair_zmodPoint_of_neg_add_mem hI0
      (Finset.mem_union_left _ hib) (Finset.mem_union_right _ hje) hij
      (Finset.mem_union_left _ htb) hti htj
  · rw [ordinaryPair_symm]
    obtain ⟨htb, htj, hti⟩ := base_extra_third hm hs hjb hie
    have hthird : -(j + i) ∈ constructionIndices m s hm hs :=
      Finset.mem_union_left _ htb
    apply not_ordinaryPair_zmodPoint_of_neg_add_mem hI0
      (Finset.mem_union_left _ hjb) (Finset.mem_union_right _ hie) hij.symm
      hthird htj hti
  · simp only [extraIndices, Finset.mem_map] at hie hje
    obtain ⟨a, _, ha⟩ := hie
    obtain ⟨b, _, hb⟩ := hje
    have hie' : extraEmbedding m s hm hs a ∈ extraIndices m s hm hs := by
      simp [extraIndices]
    have hje' : extraEmbedding m s hm hs b ∈ extraIndices m s hm hs := by
      simp [extraIndices]
    have hab : a ≠ b := by
      intro h
      apply hij
      rw [← ha, ← hb, h]
    have hside : extraLeft s a ↔ extraLeft s b := by
      rw [← indexLeft_extra_iff hm hs a, ← indexLeft_extra_iff hm hs b]
      simpa only [ha, hb] using hsame
    obtain ⟨c, hca, hcb, hc⟩ := extra_sameSide_third hm hs a b hab hside
    have hce : extraEmbedding m s hm hs c ∈ extraIndices m s hm hs := by
      simp [extraIndices]
    have hthird : -(i + j) ∈ constructionIndices m s hm hs := by
      rw [← ha, ← hb, hc]
      exact Finset.mem_union_right _ hce
    have hti : -(i + j) ≠ i := by
      intro h
      apply hca
      apply (extraEmbedding m s hm hs).injective
      calc
        extraEmbedding m s hm hs c =
            -(extraEmbedding m s hm hs a + extraEmbedding m s hm hs b) := hc.symm
        _ = -(i + j) := by rw [ha, hb]
        _ = i := h
        _ = extraEmbedding m s hm hs a := ha.symm
    have htj : -(i + j) ≠ j := by
      intro h
      apply hcb
      apply (extraEmbedding m s hm hs).injective
      calc
        extraEmbedding m s hm hs c =
            -(extraEmbedding m s hm hs a + extraEmbedding m s hm hs b) := hc.symm
        _ = -(i + j) := by rw [ha, hb]
        _ = j := h
        _ = extraEmbedding m s hm hs b := hb.symm
    apply not_ordinaryPair_zmodPoint_of_neg_add_mem hI0
      (Finset.mem_union_right _ (ha ▸ hie'))
      (Finset.mem_union_right _ (hb ▸ hje')) hij hthird hti htj

noncomputable def constructionIndex {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (p : {p // p ∈ construction m s hm hs}) : ZMod (modulus m) :=
  Classical.choose (mem_pointSet.1 p.2)

lemma constructionIndex_mem {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (p : {p // p ∈ construction m s hm hs}) :
    constructionIndex hm hs p ∈ constructionIndices m s hm hs :=
  (Classical.choose_spec (mem_pointSet.1 p.2)).1

lemma zmodPoint_constructionIndex {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (p : {p // p ∈ construction m s hm hs}) :
    zmodPoint (modulus m) (constructionIndex hm hs p) = p.1 :=
  (Classical.choose_spec (mem_pointSet.1 p.2)).2

def constructionLeftVertices {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Set {p // p ∈ construction m s hm hs} :=
  {p | indexLeft m s hm hs (constructionIndex hm hs p)}

theorem construction_isBipartiteWith {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    (ordinaryGraph (construction m s hm hs)).IsBipartiteWith
      (constructionLeftVertices hm hs) (constructionLeftVertices hm hs)ᶜ := by
  classical
  refine ⟨Set.disjoint_left.2 (by intro x hx hxc; exact hxc hx), ?_⟩
  intro p q hpq
  rw [ordinaryGraph_adj] at hpq
  have hip := constructionIndex_mem hm hs p
  have hiq := constructionIndex_mem hm hs q
  have hij : constructionIndex hm hs p ≠ constructionIndex hm hs q := by
    intro h
    apply hpq.2.2.1
    rw [← zmodPoint_constructionIndex hm hs p,
      ← zmodPoint_constructionIndex hm hs q, h]
  by_cases hp : p ∈ constructionLeftVertices hm hs
  · left
    refine ⟨hp, ?_⟩
    intro hq
    have hnord := sameIndexSide_not_ordinary hm hs hip hiq hij ⟨fun _ ↦ hq, fun _ ↦ hp⟩
    apply hnord
    simpa only [zmodPoint_constructionIndex hm hs p,
      zmodPoint_constructionIndex hm hs q] using hpq
  · right
    refine ⟨hp, ?_⟩
    by_contra hq
    have hnord := sameIndexSide_not_ordinary hm hs hip hiq hij
      ⟨fun hp' ↦ (hp hp').elim, fun hq' ↦ (hq hq').elim⟩
    apply hnord
    simpa only [zmodPoint_constructionIndex hm hs p,
      zmodPoint_constructionIndex hm hs q] using hpq

lemma cliqueFree_three_of_isBipartiteWith_compl {V : Type*} {G : SimpleGraph V}
    {L : Set V} (h : G.IsBipartiteWith L Lᶜ) : G.CliqueFree 3 := by
  classical
  intro T hT
  obtain ⟨a, b, c, hab, hac, hbc, hT_eq⟩ := Finset.card_eq_three.mp hT.card_eq
  rw [hT_eq] at hT
  have hab' : G.Adj a b := hT.isClique (by simp) (by simp) hab
  have hac' : G.Adj a c := hT.isClique (by simp) (by simp) hac
  have hbc' : G.Adj b c := hT.isClique (by simp) (by simp) hbc
  by_cases ha : a ∈ L
  · have hb : b ∈ Lᶜ := h.mem_of_mem_adj ha hab'
    have hc : c ∈ Lᶜ := h.mem_of_mem_adj ha hac'
    have hcL : c ∈ L := h.mem_of_mem_adj' hb hbc'.symm
    exact hc hcL
  · have ha' : a ∈ Lᶜ := ha
    have hb : b ∈ L := h.mem_of_mem_adj' ha' hab'.symm
    have hc : c ∈ L := h.mem_of_mem_adj' ha' hac'.symm
    have hc' : c ∈ Lᶜ := h.mem_of_mem_adj hb hbc'
    exact hc' hc

theorem construction_cliqueFree_three {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    (ordinaryGraph (construction m s hm hs)).CliqueFree 3 :=
  cliqueFree_three_of_isBipartiteWith_compl (construction_isBipartiteWith hm hs)

theorem construction_no_ordinaryClique {m s r : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (hr : 3 ≤ r) : ¬ HasOrdinaryClique (construction m s hm hs) r := by
  rw [hasOrdinaryClique_iff_not_cliqueFree]
  exact not_not_intro ((construction_cliqueFree_three hm hs).mono hr)

theorem construction_noKCollinear {m s k : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (hk : 4 ≤ k) : NoKCollinear (construction m s hm hs) k := by
  apply noKCollinear_of_no_four hk
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  exact pointSet_no_four_collinear (constructionIndices_ne_zero hm hs)

/-! ## Counting the three opposite pairs of cosets -/

def leftCoset : Fin 3 ↪ Fin 6 where
  toFun c := ![0, 1, 3] c
  inj' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp

def rightCoset : Fin 3 ↪ Fin 6 where
  toFun c := ![5, 4, 2] c
  inj' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp

@[simp] lemma leftCoset_apply (c : Fin 3) : leftCoset c = ![0, 1, 3] c := rfl

@[simp] lemma rightCoset_apply (c : Fin 3) : rightCoset c = ![5, 4, 2] c := rfl

lemma leftCoset_ne_rightCoset (c : Fin 3) : leftCoset c ≠ rightCoset c := by
  fin_cases c <;> decide

def leftIndex (m : ℕ) (hm : 0 < m) (x : Fin 3 × Fin m) : ZMod (modulus m) :=
  baseEmbedding m hm (leftCoset x.1, x.2)

def rightIndex (m : ℕ) (hm : 0 < m) (c : Fin 3) (b : Fin m) :
    ZMod (modulus m) :=
  baseEmbedding m hm (rightCoset c, b)

def thirdIndex (m : ℕ) (hm : 0 < m) (x : Fin 3 × Fin m) (b : Fin m) :
    ZMod (modulus m) :=
  -(leftIndex m hm x + rightIndex m hm x.1 b)

lemma residueSeven_baseEmbedding {m : ℕ} (hm : 0 < m) (x : Fin 6 × Fin m) :
    residueSeven m (baseEmbedding m hm x) = (x.1.val + 1 : ZMod 7) := by
  rw [residueSeven_apply m hm, val_baseEmbedding]
  simp [baseNat]
  change (7 : ZMod 7) * (x.2.val : ZMod 7) = 0
  rw [show (7 : ZMod 7) = 0 by decide]
  simp

lemma residueSeven_leftIndex {m : ℕ} (hm : 0 < m) (x : Fin 3 × Fin m) :
    residueSeven m (leftIndex m hm x) = (![1, 2, 4] x.1 : ℕ) := by
  rw [leftIndex, residueSeven_baseEmbedding]
  generalize hc : x.1 = c
  fin_cases c <;> norm_num [hc]

lemma residueSeven_rightIndex {m : ℕ} (hm : 0 < m) (c : Fin 3) (b : Fin m) :
    residueSeven m (rightIndex m hm c b) = (![6, 5, 3] c : ℕ) := by
  rw [rightIndex, residueSeven_baseEmbedding]
  fin_cases c <;> norm_num

lemma residueSeven_thirdIndex_eq_zero {m : ℕ} (hm : 0 < m)
    (x : Fin 3 × Fin m) (b : Fin m) : residueSeven m (thirdIndex m hm x b) = 0 := by
  simp only [thirdIndex, map_neg, map_add, residueSeven_leftIndex,
    residueSeven_rightIndex]
  generalize hc : x.1 = c
  fin_cases c <;> norm_num [hc]
  all_goals exact (by decide)

lemma leftIndex_mem_base {m : ℕ} (hm : 0 < m) (x : Fin 3 × Fin m) :
    leftIndex m hm x ∈ baseIndices m hm := by
  simp [leftIndex, baseIndices]

lemma rightIndex_mem_base {m : ℕ} (hm : 0 < m) (c : Fin 3) (b : Fin m) :
    rightIndex m hm c b ∈ baseIndices m hm := by
  simp [rightIndex, baseIndices]

lemma leftIndex_ne_rightIndex {m : ℕ} (hm : 0 < m) (x : Fin 3 × Fin m) (b : Fin m) :
    leftIndex m hm x ≠ rightIndex m hm x.1 b := by
  intro h
  have hp := (baseEmbedding m hm).injective h
  exact leftCoset_ne_rightCoset x.1 (congrArg Prod.fst hp)

def goodPartners (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun b ↦ thirdIndex m (by omega) x b ∉ extraIndices m s hm hs

lemma thirdIndex_injective {m : ℕ} (hm : 0 < m) (x : Fin 3 × Fin m) :
    Function.Injective (thirdIndex m hm x) := by
  intro a b h
  have hright : rightIndex m hm x.1 a = rightIndex m hm x.1 b := by
    apply add_left_cancel (a := leftIndex m hm x)
    apply neg_injective
    simpa only [thirdIndex] using h
  have hp := (baseEmbedding m hm).injective hright
  exact congrArg Prod.snd hp

lemma card_goodPartners_lower (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) : m - s ≤ (goodPartners m s hm hs x).card := by
  classical
  let bad : Finset (Fin m) :=
    Finset.univ.filter fun b ↦ thirdIndex m (by omega) x b ∈ extraIndices m s hm hs
  let thirdEmb : Fin m ↪ ZMod (modulus m) :=
    ⟨thirdIndex m (by omega) x, thirdIndex_injective (by omega) x⟩
  have hbad : bad.card ≤ s := by
    calc
      bad.card = (bad.map thirdEmb).card := by simp
      _ ≤ (extraIndices m s hm hs).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_map] at hz
        obtain ⟨b, hb, rfl⟩ := hz
        exact (Finset.mem_filter.1 hb).2
      _ = s := card_extraIndices m s hm hs
  have hsplit : bad.card + (goodPartners m s hm hs x).card = m := by
    simpa [bad, goodPartners, add_comm] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun b ↦ thirdIndex m (by omega) x b ∈ extraIndices m s hm hs))
  omega

lemma ordinaryPair_left_right_of_good {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) {b : Fin m} (hb : b ∈ goodPartners m s hm hs x) :
    OrdinaryPair (construction m s hm hs)
      (zmodPoint (modulus m) (leftIndex m (by omega) x))
      (zmodPoint (modulus m) (rightIndex m (by omega) x.1 b)) := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  rw [construction]
  apply ordinaryPair_zmodPoint_of_neg_add_not_mem (constructionIndices_ne_zero hm hs)
  · exact Finset.mem_union_left _ (leftIndex_mem_base (by omega) x)
  · exact Finset.mem_union_left _ (rightIndex_mem_base (by omega) x.1 b)
  · exact leftIndex_ne_rightIndex (by omega) x b
  · rw [constructionIndices, Finset.mem_union]
    push Not
    refine ⟨?_, (Finset.mem_filter.1 hb).2⟩
    intro hbase
    have hne := (mem_baseIndices_iff_residueSeven_ne_zero (by omega) _).1 hbase
    exact hne (residueSeven_thirdIndex_eq_zero (by omega) x b)

def leftVertex {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (x : Fin 3 × Fin m) :
    {p // p ∈ construction m s hm hs} :=
  ⟨zmodPoint (modulus m) (leftIndex m (by omega) x), by
    rw [construction]
    exact mem_pointSet.2 ⟨leftIndex m (by omega) x,
      Finset.mem_union_left _ (leftIndex_mem_base (by omega) x), rfl⟩⟩

def rightVertex {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (c : Fin 3) (b : Fin m) :
    {p // p ∈ construction m s hm hs} :=
  ⟨zmodPoint (modulus m) (rightIndex m (by omega) c b), by
    rw [construction]
    exact mem_pointSet.2 ⟨rightIndex m (by omega) c b,
      Finset.mem_union_left _ (rightIndex_mem_base (by omega) c b), rfl⟩⟩

lemma leftVertex_injective {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Function.Injective (leftVertex hm hs) := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  intro x y h
  have hi : leftIndex m (by omega) x = leftIndex m (by omega) y := by
    apply zmodPoint_injective_of_ne_zero
    · exact baseIndices_ne_zero (by omega) (leftIndex_mem_base (by omega) x)
    · exact baseIndices_ne_zero (by omega) (leftIndex_mem_base (by omega) y)
    · exact congrArg Subtype.val h
  have hp := (baseEmbedding m (by omega)).injective hi
  apply Prod.ext
  · exact leftCoset.injective (congrArg Prod.fst hp)
  · simpa using congrArg Prod.snd hp

lemma rightVertex_injective {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (c : Fin 3) :
    Function.Injective (rightVertex hm hs c) := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  intro a b h
  have hi : rightIndex m (by omega) c a = rightIndex m (by omega) c b := by
    apply zmodPoint_injective_of_ne_zero
    · exact baseIndices_ne_zero (by omega) (rightIndex_mem_base (by omega) c a)
    · exact baseIndices_ne_zero (by omega) (rightIndex_mem_base (by omega) c b)
    · exact congrArg Subtype.val h
  exact congrArg Prod.snd ((baseEmbedding m (by omega)).injective hi)

def leftVertexEmbedding {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Fin 3 × Fin m ↪ {p // p ∈ construction m s hm hs} :=
  ⟨leftVertex hm hs, leftVertex_injective hm hs⟩

def selectedLeftVertices {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Finset {p // p ∈ construction m s hm hs} :=
  Finset.univ.map (leftVertexEmbedding hm hs)

lemma card_selectedLeftVertices {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    (selectedLeftVertices hm hs).card = 3 * m := by
  simp [selectedLeftVertices]

lemma constructionIndex_leftVertex {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) :
    constructionIndex hm hs (leftVertex hm hs x) = leftIndex m (by omega) x := by
  letI : NeZero (modulus m) := ⟨by simp [modulus]; omega⟩
  apply zmodPoint_injective_of_ne_zero
  · exact constructionIndices_ne_zero hm hs _ (constructionIndex_mem hm hs _)
  · exact baseIndices_ne_zero (by omega) (leftIndex_mem_base (by omega) x)
  · rw [zmodPoint_constructionIndex]
    rfl

lemma leftVertex_mem_left {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) : leftVertex hm hs x ∈ constructionLeftVertices hm hs := by
  change indexLeft m s hm hs (constructionIndex hm hs (leftVertex hm hs x))
  rw [constructionIndex_leftVertex, indexLeft_base_iff hm hs (leftIndex_mem_base (by omega) x),
    residueSeven_leftIndex]
  generalize hc : x.1 = c
  fin_cases c <;> norm_num [hc, ZMod.val_natCast]
  all_goals exact (by decide)

noncomputable instance constructionOrdinaryGraphLocallyFinite {m s : ℕ}
    (hm : 12 ≤ m) (hs : s ≤ 5) :
    (ordinaryGraph (construction m s hm hs)).LocallyFinite := by
  classical
  exact fun v ↦ Subtype.fintype (Membership.mem ((ordinaryGraph
    (construction m s hm hs)).neighborSet v))

lemma degree_leftVertex_lower {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5)
    (x : Fin 3 × Fin m) :
    m - s ≤ (ordinaryGraph (construction m s hm hs)).degree (leftVertex hm hs x) := by
  classical
  let G := ordinaryGraph (construction m s hm hs)
  have hcard : (goodPartners m s hm hs x).card ≤ G.degree (leftVertex hm hs x) := by
    unfold SimpleGraph.degree
    apply Finset.card_le_card_of_injOn (fun b ↦ rightVertex hm hs x.1 b)
    · intro b hb
      change rightVertex hm hs x.1 b ∈ G.neighborFinset (leftVertex hm hs x)
      rw [SimpleGraph.mem_neighborFinset, ordinaryGraph_adj]
      exact ordinaryPair_left_right_of_good hm hs x hb
    · exact (rightVertex_injective hm hs x.1).injOn
  exact (card_goodPartners_lower m s hm hs x).trans hcard

noncomputable def constructionLeftFinset {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Finset {p // p ∈ construction m s hm hs} := by
  classical
  exact Finset.univ.filter (fun p ↦ p ∈ constructionLeftVertices hm hs)

lemma selectedLeftVertices_subset_left {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    selectedLeftVertices hm hs ⊆
      constructionLeftFinset hm hs := by
  classical
  intro p hp
  simp only [selectedLeftVertices, Finset.mem_map] at hp
  obtain ⟨x, _, rfl⟩ := hp
  rw [constructionLeftFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, leftVertex_mem_left hm hs x⟩

theorem construction_ordinaryLineCount_lower (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    3 * m * (m - s) ≤ ordinaryLineCount (construction m s hm hs) := by
  classical
  let G := ordinaryGraph (construction m s hm hs)
  let L : Finset {p // p ∈ construction m s hm hs} :=
    constructionLeftFinset hm hs
  have hbip : G.IsBipartiteWith (L : Set _) (Lᶜ : Finset _) := by
    simpa [G, L, constructionLeftFinset] using construction_isBipartiteWith hm hs
  calc
    3 * m * (m - s) = ∑ _x : Fin 3 × Fin m, (m - s) := by simp
    _ ≤ ∑ x : Fin 3 × Fin m, G.degree (leftVertex hm hs x) := by
      exact Finset.sum_le_sum fun _ _ ↦ degree_leftVertex_lower hm hs _
    _ = ∑ p ∈ selectedLeftVertices hm hs, G.degree p := by
      simp [selectedLeftVertices, leftVertexEmbedding]
    _ ≤ ∑ p ∈ L, G.degree p := by
      exact Finset.sum_le_sum_of_subset (selectedLeftVertices_subset_left hm hs)
    _ = ordinaryLineCount (construction m s hm hs) := by
      simpa [G, ordinaryLineCount] using
        SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip

/-! ## The quadratic lower bound and the resolution -/

theorem f_lower_nat {r k n : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n) :
    3 * (n / 6) * (n / 6 - n % 6) + 1 ≤ f r k n := by
  let m := n / 6
  let s := n % 6
  have hm : 12 ≤ m := by
    simp only [m]
    omega
  have hs : s ≤ 5 := by
    simp only [s]
    omega
  apply counterexample_lower_bound
    (A := construction m s hm hs)
    (e := 3 * m * (m - s))
  · rw [card_construction]
    simp only [m, s]
    omega
  · exact construction_noKCollinear hm hs hk
  · exact construction_no_ordinaryClique hm hs hr
  · exact construction_ordinaryLineCount_lower m s hm hs

lemma construction_real_estimate (m s : ℕ) (hm : 12 ≤ m) (hs : s ≤ 5) :
    (((6 * m + s : ℕ) : ℝ) ^ 2) / 12 - (10 / 3 : ℝ) * (6 * m + s) + 1 ≤
      ((3 * m * (m - s) + 1 : ℕ) : ℝ) := by
  have hsm : s ≤ m := by omega
  interval_cases s <;> norm_num [Nat.cast_sub hsm] <;> nlinarith

/-- APSSV's quantitative resolution, translated from their extremal maximum
`F` to Erdős's forcing threshold `f = F + 1`. -/
theorem erdos960_lower_bound {r k n : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n) :
    (n : ℝ) ^ 2 / 12 - (10 / 3 : ℝ) * n + 1 ≤ (f r k n : ℝ) := by
  let m := n / 6
  let s := n % 6
  have hm : 12 ≤ m := by simp only [m]; omega
  have hs : s ≤ 5 := by simp only [s]; omega
  have hdecomp : 6 * m + s = n := by
    simp only [m, s]
    omega
  have hdecompR : (n : ℝ) = 6 * (m : ℝ) + s := by
    exact_mod_cast hdecomp.symm
  calc
    (n : ℝ) ^ 2 / 12 - (10 / 3 : ℝ) * n + 1 =
        ((6 * m + s : ℕ) : ℝ) ^ 2 / 12 -
          (10 / 3 : ℝ) * (6 * m + s) + 1 := by
      rw [hdecompR]
      norm_num
    _ ≤ ((3 * m * (m - s) + 1 : ℕ) : ℝ) := construction_real_estimate m s hm hs
    _ ≤ (f r k n : ℝ) := by
      exact_mod_cast f_lower_nat hr hk hn

lemma quadratic_lower_eventually {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / 24 ≤ (f r k n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨80, ?_⟩
  intro n hn
  have hmain := erdos960_lower_bound hr hk (by omega : 72 ≤ n)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn80' : (80 : ℝ) ≤ n := by exact_mod_cast hn
  have hn80 : 0 ≤ (n : ℝ) - 80 := by linarith
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 80) := mul_nonneg hn0 hn80
  nlinarith

/-- The forcing threshold is not little-oh of `n²`; this answers Erdős's
first asymptotic question negatively. -/
theorem erdos960_not_isLittleO {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ¬ Asymptotics.IsLittleO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  intro hsmall
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 48)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨N, hN⟩ := hbound
  let n := max N 80
  have hnN : N ≤ n := le_max_left _ _
  have hn80 : 80 ≤ n := le_max_right _ _
  have hupper : (f r k n : ℝ) ≤ (n : ℝ) ^ 2 / 48 := by
    have h := hN n hnN
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (f r k n : ℝ) by positivity),
      abs_of_nonneg (sq_nonneg (n : ℝ))] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have hlower' : (n : ℝ) ^ 2 / 24 ≤ (f r k n : ℝ) := by
    exact erdos960_lower_bound hr hk (by omega) |>.trans' (by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn80r' : (80 : ℝ) ≤ n := by exact_mod_cast hn80
      have hn80r : 0 ≤ (n : ℝ) - 80 := by linarith
      have hp := mul_nonneg hn0 hn80r
      nlinarith)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  nlinarith [sq_pos_of_pos hnpos]

/-- In particular the threshold is not `O(n)`, answering Erdős's stronger
linear-growth hope negatively. -/
theorem erdos960_not_isBigO_linear {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ¬ Asymptotics.IsBigO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ)) := by
  intro hbig
  obtain ⟨c, hc⟩ := hbig.bound
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max (N : ℝ) (max 80 (24 * |c|)))
  have hnN : N ≤ n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn).le
  have hn80 : 80 ≤ n := by
    exact_mod_cast (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn).le
  have hnc : 24 * |c| < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hupper : (f r k n : ℝ) ≤ c * n := by
    have h := hN n hnN
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (f r k n : ℝ) by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] at h
    exact h
  have hlower : (n : ℝ) ^ 2 / 24 ≤ (f r k n : ℝ) := by
    have hmain := erdos960_lower_bound hr hk (by omega : 72 ≤ n)
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn80r' : (80 : ℝ) ≤ n := by exact_mod_cast hn80
    have hn80r : 0 ≤ (n : ℝ) - 80 := by linarith
    have hp := mul_nonneg hn0 hn80r
    nlinarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcmul : c * (n : ℝ) ≤ |c| * n :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (Nat.cast_nonneg n)
  have hstrict : 24 * |c| * (n : ℝ) < (n : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hnc hnpos]
  nlinarith

/-- The complete resolution of Erdős Problem 960 in the modern convention
that `NoKCollinear A k` means no `k` points of `A` lie on one line.

The first conjunct records the APSSV quadratic counterexample and Erdős's
Turán upper bound for every `n ≥ 72`; the remaining conjuncts give the two
negative answers to the asymptotic questions posed in the problem. -/
theorem erdos_960 {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    (∀ n : ℕ, 72 ≤ n →
      (n : ℝ) ^ 2 / 12 - (10 / 3 : ℝ) * n + 1 ≤ (f r k n : ℝ) ∧
      (f r k n : ℝ) ≤
        (1 - 1 / ((r - 1 : ℕ) : ℝ)) * (n : ℝ) ^ 2 / 2 + 1) ∧
    ¬ Asymptotics.IsLittleO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ 2) ∧
    ¬ Asymptotics.IsBigO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ)) := by
  refine ⟨?_, erdos960_not_isLittleO hr hk, erdos960_not_isBigO_linear hr hk⟩
  intro n hn
  exact ⟨erdos960_lower_bound hr hk hn, erdos960_upper_bound r k n (by omega)⟩

#print axioms erdos_960

end

end Erdos960

alias _root_.Erdos960.erdos960_resolution := _root_.Erdos960.erdos_960
