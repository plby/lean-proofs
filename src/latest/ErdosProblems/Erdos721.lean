/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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
import ErdosProblems.Erdos123
import ErdosProblems.Erdos88.Probability
import ErdosProblems.Erdos721.Bohr
import ErdosProblems.Erdos721.Fourier
import ErdosProblems.Erdos721.Rudin
import ErdosProblems.Erdos721.Chang
import ErdosProblems.Erdos721.Cardinality
import ErdosProblems.Erdos721.Regularity
import ErdosProblems.Erdos721.AlmostPeriodicity
import ErdosProblems.Erdos721.BoostedAlmostPeriodicity
import ErdosProblems.Erdos721.DensityIncrement
import ErdosProblems.Erdos721.DensityIncrementIteration
import ErdosProblems.Erdos721.RelativeLifting
import ErdosProblems.Erdos721.PositiveDefiniteLifting
import ErdosProblems.Erdos721.LocalUnbalancing
import ErdosProblems.Erdos721.LocalSifting
import ErdosProblems.Erdos721.LocalDensityIncrement
import ErdosProblems.Erdos721.LocalDensityIteration
import ErdosProblems.Erdos721.CyclicRothEndpoint
import ErdosProblems.Erdos721.HunterSpecialization

/-!
# Erdős Problem 721

For the off-diagonal van der Waerden number `W(3,k)`, Hunter proved the
superpolynomial lower bound

`exp (c * (log k)^2 / log (log k))`,

and the quantitative Roth theorem of Bloom--Sisask gives the upper bound

`exp (C * (log k)^9)`.

The detailed mathematical reconstruction and Leanization map are in
`tex/721.tex`.
-/

namespace Erdos721

open Filter
open Classical
open Erdos88.Probability
open scoped BigOperators Topology

/-- A positive-step `l`-term arithmetic progression below `n`, all of whose
terms have the prescribed color.  Colors `0` and `1` represent red and blue.

The coloring is defined on `ℕ`; only values below `n` occur.  This is
equivalent to using a map `Fin n → Fin 2` and makes the arithmetic expression
for a progression independent of proof terms. -/
def HasMonochromaticAP (n l : ℕ) (color : ℕ → Fin 2) (hue : Fin 2) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (l - 1) * d < n ∧
    ∀ i : Fin l, color (a + i.val * d) = hue

/-- Every red/blue coloring of the first `n` natural numbers contains either
a red three-term progression or a blue `k`-term progression. -/
def ForcesW3 (n k : ℕ) : Prop :=
  ∀ color : ℕ → Fin 2,
    HasMonochromaticAP n 3 color 0 ∨
      HasMonochromaticAP n k color 1

/-- The red points of a coloring in the interval below `n`. -/
def redFinset (n : ℕ) (color : ℕ → Fin 2) : Finset ℕ :=
  (Finset.range n).filter fun x ↦ color x = 0

@[simp] lemma mem_redFinset {n : ℕ} {color : ℕ → Fin 2} {x : ℕ} :
    x ∈ redFinset n color ↔ x < n ∧ color x = 0 := by
  simp [redFinset]

/-- If a coloring has no red nonconstant three-term progression, then its red
class is `ThreeAPFree` in Mathlib's additive-combinatorics sense. -/
lemma threeAPFree_redFinset {n : ℕ} {color : ℕ → Fin 2}
    (hred : ¬ HasMonochromaticAP n 3 color 0) :
    ThreeAPFree (redFinset n color : Set ℕ) := by
  rintro a ha b hb c hc habc
  change a ∈ redFinset n color at ha
  change b ∈ redFinset n color at hb
  change c ∈ redFinset n color at hc
  rw [mem_redFinset] at ha hb hc
  by_contra hab
  rcases lt_or_gt_of_ne hab with hablt | habgt
  · apply hred
    refine ⟨a, b - a, by omega, ?_, ?_⟩
    · norm_num
      omega
    · intro i
      fin_cases i
      · simpa using ha.2
      · change color (a + 1 * (b - a)) = 0
        rw [show a + 1 * (b - a) = b by omega]
        exact hb.2
      · change color (a + 2 * (b - a)) = 0
        rw [show a + 2 * (b - a) = c by omega]
        exact hc.2
  · have hcb : c < b := by omega
    apply hred
    refine ⟨c, b - c, by omega, ?_, ?_⟩
    · norm_num
      omega
    · intro i
      fin_cases i
      · simpa using hc.2
      · change color (c + 1 * (b - c)) = 0
        rw [show c + 1 * (b - c) = b by omega]
        exact hb.2
      · change color (c + 2 * (b - c)) = 0
        rw [show c + 2 * (b - c) = a by omega]
        exact ha.2

/-- A red class with no red three-term progression has cardinality at most the
corresponding Roth number. -/
lemma card_redFinset_le_rothNumberNat {n : ℕ} {color : ℕ → Fin 2}
    (hred : ¬ HasMonochromaticAP n 3 color 0) :
    (redFinset n color).card ≤ rothNumberNat n := by
  apply (threeAPFree_redFinset hred).le_rothNumberNat (redFinset n color)
  · intro x hx
    exact (mem_redFinset.mp hx).1
  · rfl

lemma fin_two_eq_one_of_ne_zero {x : Fin 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x <;> simp_all

/-- Every complete consecutive `k`-block contains a red point when there is no
blue `k`-term progression. -/
lemma exists_red_in_block_of_no_blue_AP {n k : ℕ} (hk : 0 < k)
    (color : ℕ → Fin 2) (hblue : ¬ HasMonochromaticAP n k color 1)
    (j : Fin (n / k)) :
    ∃ x ∈ redFinset n color,
      j.val * k ≤ x ∧ x < (j.val + 1) * k := by
  by_contra hex
  apply hblue
  refine ⟨j.val * k, 1, by norm_num, ?_, ?_⟩
  · have hj : (j.val + 1) * k ≤ (n / k) * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr j.isLt)
    have hdiv : (n / k) * k ≤ n := Nat.div_mul_le_self n k
    have hlastBlock : j.val * k + (k - 1) * 1 < (j.val + 1) * k := by
      rw [mul_one, Nat.add_mul]
      omega
    exact hlastBlock.trans_le (hj.trans hdiv)
  · intro i
    let x := j.val * k + i.val
    have hix : i.val < k := i.isLt
    have hxlo : j.val * k ≤ x := by simp [x]
    have hxhi : x < (j.val + 1) * k := by
      dsimp [x]
      rw [Nat.add_mul]
      omega
    have hj : (j.val + 1) * k ≤ (n / k) * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr j.isLt)
    have hdiv : (n / k) * k ≤ n := Nat.div_mul_le_self n k
    have hxn : x < n := hxhi.trans_le (hj.trans hdiv)
    have hx0 : color x ≠ 0 := by
      intro hzero
      apply hex
      exact ⟨x, mem_redFinset.mpr ⟨hxn, hzero⟩, hxlo, hxhi⟩
    simpa [x] using fin_two_eq_one_of_ne_zero hx0

/-- The disjoint consecutive blocks give the exact integral density lower
bound `⌊n/k⌋ ≤ |red|`. -/
lemma div_le_card_redFinset_of_no_blue_AP {n k : ℕ} (hk : 0 < k)
    (color : ℕ → Fin 2) (hblue : ¬ HasMonochromaticAP n k color 1) :
    n / k ≤ (redFinset n color).card := by
  classical
  let witness : Fin (n / k) → ℕ := fun j ↦
    Classical.choose (exists_red_in_block_of_no_blue_AP hk color hblue j)
  have hwitness (j : Fin (n / k)) :
      witness j ∈ redFinset n color ∧
        j.val * k ≤ witness j ∧ witness j < (j.val + 1) * k :=
    Classical.choose_spec (exists_red_in_block_of_no_blue_AP hk color hblue j)
  let f : Fin (n / k) → {x // x ∈ redFinset n color} :=
    fun j ↦ ⟨witness j, (hwitness j).1⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hvalue : witness i = witness j := congrArg Subtype.val hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hblocks : (i.val + 1) * k ≤ j.val * k :=
        Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hijlt)
      have hi := (hwitness i).2.2
      have hj := (hwitness j).2.1
      omega
    · have hblocks : (j.val + 1) * k ≤ i.val * k :=
        Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hjilt)
      have hi := (hwitness i).2.1
      have hj := (hwitness j).2.2
      omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

lemma hasMonochromaticAP_mono_interval {m n l : ℕ} {color : ℕ → Fin 2}
    {hue : Fin 2} (hmn : m ≤ n)
    (h : HasMonochromaticAP m l color hue) :
    HasMonochromaticAP n l color hue := by
  obtain ⟨a, d, hd, hlast, hcolor⟩ := h
  exact ⟨a, d, hd, hlast.trans_le hmn, hcolor⟩

lemma forcesW3_mono_interval {m n k : ℕ} (hmn : m ≤ n)
    (h : ForcesW3 m k) : ForcesW3 n k := by
  intro color
  rcases h color with hred | hblue
  · exact Or.inl (hasMonochromaticAP_mono_interval hmn hred)
  · exact Or.inr (hasMonochromaticAP_mono_interval hmn hblue)

lemma hasMonochromaticAP_prefix {n k l : ℕ} {color : ℕ → Fin 2}
    {hue : Fin 2} (hkl : k ≤ l)
    (h : HasMonochromaticAP n l color hue) :
    HasMonochromaticAP n k color hue := by
  obtain ⟨a, d, hd, hlast, hcolor⟩ := h
  refine ⟨a, d, hd, ?_, ?_⟩
  · calc
      a + (k - 1) * d ≤ a + (l - 1) * d := by
        gcongr
      _ < n := hlast
  · intro i
    exact hcolor ⟨i.val, i.isLt.trans_le hkl⟩

lemma forcesW3_antitone_length {n k l : ℕ} (hkl : k ≤ l)
    (h : ForcesW3 n l) : ForcesW3 n k := by
  intro color
  rcases h color with hred | hblue
  · exact Or.inl hred
  · exact Or.inr (hasMonochromaticAP_prefix hkl hblue)

/-- Finite van der Waerden implies that the set in the definition of `W3` is
nonempty. -/
theorem exists_forcesW3 (k : ℕ) : ∃ n, ForcesW3 n k := by
  let L := max 3 k
  have hL : 1 < L := by
    dsimp [L]
    omega
  obtain ⟨n, hn, hvdw⟩ := Erdos123.finite_van_der_waerden 2 L hL
  refine ⟨n, ?_⟩
  intro color
  obtain ⟨a, d, hd, hlast, hmono⟩ := hvdw color
  have hthree : 3 ≤ L := le_max_left 3 k
  have hk : k ≤ L := le_max_right 3 k
  have hredLast : a + (3 - 1) * d < n := by
    calc
      a + (3 - 1) * d ≤ a + (L - 1) * d := by
        gcongr
      _ < n := hlast
  have hblueLast : a + (k - 1) * d < n := by
    calc
      a + (k - 1) * d ≤ a + (L - 1) * d := by
        gcongr
      _ < n := hlast
  generalize hbase : color a = base
  fin_cases base
  · left
    refine ⟨a, d, hd, hredLast, ?_⟩
    intro i
    exact (hmono ⟨i.val, i.isLt.trans_le hthree⟩).trans hbase
  · right
    refine ⟨a, d, hd, hblueLast, ?_⟩
    intro i
    exact (hmono ⟨i.val, i.isLt.trans_le hk⟩).trans hbase

/-- The exact off-diagonal van der Waerden number `W(3,k)`, using the
zero-based interval `{0, ..., n-1}`. -/
noncomputable def W3 (k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_forcesW3 k)

theorem forcesW3_W3 (k : ℕ) : ForcesW3 (W3 k) k := by
  classical
  exact Nat.find_spec (exists_forcesW3 k)

theorem not_forcesW3_of_lt_W3 {n k : ℕ} (h : n < W3 k) :
    ¬ ForcesW3 n k := by
  classical
  intro hn
  have hle : W3 k ≤ n := Nat.find_min' (exists_forcesW3 k) hn
  omega

theorem W3_le_of_forcesW3 {n k : ℕ} (h : ForcesW3 n k) : W3 k ≤ n := by
  classical
  exact Nat.find_min' (exists_forcesW3 k) h

/-- Conversely, failure of the forcing property puts the interval strictly
below the defining minimum. -/
lemma lt_W3_of_not_forcesW3 {n k : ℕ} (h : ¬ ForcesW3 n k) : n < W3 k := by
  by_contra hn
  exact h (forcesW3_mono_interval (by omega) (forcesW3_W3 k))

theorem W3_mono {k l : ℕ} (hkl : k ≤ l) : W3 k ≤ W3 l := by
  apply W3_le_of_forcesW3
  exact forcesW3_antitone_length hkl (forcesW3_W3 l)

/-- An interval shorter than `k` cannot force a blue `k`-term progression:
the constant-blue coloring is a counterexample. -/
lemma not_forcesW3_of_lt_length {n k : ℕ} (hk : 0 < k) (hnk : n < k) :
    ¬ ForcesW3 n k := by
  intro h
  rcases h (fun _ ↦ (1 : Fin 2)) with hred | hblue
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hred
    have := hcolor (0 : Fin 3)
    norm_num at this
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hblue
    have hmul : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right (k - 1) hd
    omega

/-- The evident lower bound `k ≤ W(3,k)`. -/
theorem le_W3 {k : ℕ} (hk : 0 < k) : k ≤ W3 k := by
  by_contra h
  exact not_forcesW3_of_lt_length hk (by omega) (forcesW3_W3 k)

/-- For `k ≥ 2`, coloring only zero red avoids both alternatives on an
interval of length `k`.  Thus the elementary lower bound is strict. -/
lemma not_forcesW3_self {k : ℕ} (hk : 2 ≤ k) : ¬ ForcesW3 k k := by
  let color : ℕ → Fin 2 := fun x ↦ if x = 0 then 0 else 1
  intro h
  rcases h color with hred | hblue
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hred
    have ha0 : a = 0 := by
      simpa [color] using hcolor (0 : Fin 3)
    have hnext := hcolor (1 : Fin 3)
    simp [color, ha0, hd.ne'] at hnext
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hblue
    have ha_ne : a ≠ 0 := by
      intro ha
      have hfirst := hcolor (⟨0, by omega⟩ : Fin k)
      simp [color, ha] at hfirst
    have hmul : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right (k - 1) hd
    omega

theorem lt_W3 {k : ℕ} (hk : 2 ≤ k) : k < W3 k := by
  exact lt_of_not_ge fun h ↦ not_forcesW3_self hk <|
    forcesW3_mono_interval h (forcesW3_W3 k)

/-- A simple explicit bad coloring: on `[0,2k-2)` color only `k-1` red.
Every `k`-term progression in this interval has step one and hence meets that
red point, while a singleton red class is 3AP-free. -/
lemma not_forcesW3_two_mul_sub_two {k : ℕ} (hk : 3 ≤ k) :
    ¬ ForcesW3 (2 * k - 2) k := by
  let color : ℕ → Fin 2 := fun x ↦ if x = k - 1 then 0 else 1
  intro h
  rcases h color with hred | hblue
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hred
    have ha : a = k - 1 := by
      simpa [color] using hcolor (0 : Fin 3)
    have hnext := hcolor (1 : Fin 3)
    simp [color, ha, hd.ne'] at hnext
  · obtain ⟨a, d, hd, hlast, hcolor⟩ := hblue
    have hdle : d ≤ 1 := by
      by_contra h
      have hd2 : 2 ≤ d := by omega
      have hmul : (k - 1) * 2 ≤ (k - 1) * d := Nat.mul_le_mul_left (k - 1) hd2
      omega
    have hd1 : d = 1 := by omega
    subst d
    have ha : a < k - 1 := by omega
    let i : Fin k := ⟨k - 1 - a, by omega⟩
    have hterm : a + i.val * 1 = k - 1 := by
      dsimp [i]
      omega
    have hcenter := hcolor i
    rw [hterm] at hcenter
    simp [color] at hcenter

/-- An unconditional explicit lower bound, included to make the phrase
"non-trivial lower bound" in the original problem concrete independently of
the much stronger Hunter estimate. -/
theorem two_mul_sub_one_le_W3 {k : ℕ} (hk : 3 ≤ k) : 2 * k - 1 ≤ W3 k := by
  have hlt : 2 * k - 2 < W3 k := by
    by_contra h
    exact not_forcesW3_two_mul_sub_two hk <|
      forcesW3_mono_interval (by omega) (forcesW3_W3 k)
  omega

/-- Below the minimum there is a coloring avoiding both alternatives. -/
lemma exists_bad_coloring_of_lt_W3 {n k : ℕ} (h : n < W3 k) :
    ∃ color : ℕ → Fin 2,
      ¬ HasMonochromaticAP n 3 color 0 ∧
        ¬ HasMonochromaticAP n k color 1 := by
  classical
  simpa only [ForcesW3, not_forall, not_or] using not_forcesW3_of_lt_W3 h

/-- A predicate which is 3-AP-free and meets every `k`-term progression
gives a genuine red/blue coloring witnessing failure of `ForcesW3`. -/
lemma not_forcesW3_of_threeAPFreeBelow_hitsEveryAP {n k : ℕ}
    {red : ℕ → Prop}
    (hfree : HunterColoring.ThreeAPFreeBelow n red)
    (hhit : HunterColoring.HitsEveryAP n k red) :
    ¬ ForcesW3 n k := by
  let color : ℕ → Fin 2 := fun x ↦ if red x then 0 else 1
  intro hforces
  rcases hforces color with hred | hblue
  · obtain ⟨a, d, hd, hbound, hcolor⟩ := hred
    apply hfree a d hd (by norm_num at hbound ⊢; exact hbound)
    constructor
    · have := hcolor (0 : Fin 3)
      simpa [color] using this
    constructor
    · have := hcolor (1 : Fin 3)
      simpa [color] using this
    · have := hcolor (2 : Fin 3)
      simpa [color] using this
  · obtain ⟨a, d, hd, hbound, hcolor⟩ := hblue
    obtain ⟨i, hi⟩ := hhit a d hd hbound
    have hci := hcolor i
    simp [color, hi] at hci

/-- The elementary reduction from a bad coloring to the Roth number: each
consecutive `k`-block contributes a distinct red point, while all red points
form a 3AP-free set. -/
lemma div_le_rothNumberNat_of_not_forcesW3 {n k : ℕ} (hk : 0 < k)
    (h : ¬ ForcesW3 n k) : n / k ≤ rothNumberNat n := by
  classical
  rw [ForcesW3, not_forall] at h
  obtain ⟨color, hcolor⟩ := h
  rw [not_or] at hcolor
  exact (div_le_card_redFinset_of_no_blue_AP hk color hcolor.2).trans
    (card_redFinset_le_rothNumberNat hcolor.1)

lemma two_orbitLength_sub_one_le_progressionLength (t : ℕ) :
    2 * HunterNumerics.orbitLength (HunterParameters.dimension t) - 1 ≤
      HunterParameters.progressionLength (HunterParameters.dimension t) := by
  let D := HunterParameters.dimension t
  have hD : 2 ≤ D := by
    simpa [D] using HunterNumerics.dimension_ge_two t
  have hpow : 2 ≤ D ^ D :=
    hD.trans (Nat.le_pow (HunterParameters.dimension_pos t))
  calc
    2 * HunterNumerics.orbitLength (HunterParameters.dimension t) - 1 ≤
        2 * D ^ (4800 * D) := Nat.sub_le _ _
    _ ≤ D ^ D * D ^ (4800 * D) :=
      Nat.mul_le_mul_right (D ^ (4800 * D)) hpow
    _ = D ^ (4801 * D) := by
      rw [← pow_add]
      rw [show D + 4800 * D = 4801 * D by omega]
    _ = HunterParameters.progressionLength
        (HunterParameters.dimension t) := by
      rfl

/-- The checked finite torus construction gives a bad coloring at every
member of the cofinal integral parameter sequence. -/
theorem not_forcesW3_hunter_sequence (t : ℕ) :
    ¬ ForcesW3
      (HunterParameters.intervalLength (HunterParameters.dimension t))
      (HunterParameters.progressionLength (HunterParameters.dimension t)) := by
  obtain ⟨red, hfree, hhit⟩ :=
    HunterSpecialization.exists_hunter_badSet_dimension t
  have hshort : ¬ ForcesW3
      (HunterParameters.intervalLength (HunterParameters.dimension t))
      (2 * HunterNumerics.orbitLength (HunterParameters.dimension t) - 1) :=
    not_forcesW3_of_threeAPFreeBelow_hitsEveryAP hfree hhit
  intro hlong
  exact hshort (forcesW3_antitone_length
    (two_orbitLength_sub_one_le_progressionLength t) hlong)

/-- The elementary logarithmic comparison which converts two consecutive
members of Hunter's integral parameter sequence into the published exponent.
The deliberately small absolute constant leaves ample room in every estimate. -/
lemma hunter_sequence_exponential_bound {s k : ℕ}
    (hlower : HunterParameters.progressionLength
        (HunterParameters.dimension s) < k)
    (hupper : k ≤ HunterParameters.progressionLength
        (HunterParameters.dimension (s + 1))) :
    Real.exp ((1 / 100000000000 : ℝ) * (Real.log k) ^ 2 /
        Real.log (Real.log k)) ≤
      (HunterParameters.intervalLength (HunterParameters.dimension s) : ℝ) := by
  let D := HunterParameters.dimension s
  let E := HunterParameters.dimension (s + 1)
  let u : ℝ := Real.log D
  let ell : ℝ := Real.log k
  have hDnat : 200 ≤ D := by
    simpa [D] using HunterNumerics.dimension_ge_two_hundred s
  have hDpos : (0 : ℝ) < D := by exact_mod_cast HunterParameters.dimension_pos s
  have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast
    (show 2 ≤ D by omega)
  have hEeq : E = D + 200 := by
    simp only [E, D, HunterParameters.dimension]
    ring
  have hEle : E ≤ 2 * D := by omega
  have hEpos : (0 : ℝ) < E := by
    exact_mod_cast HunterParameters.dimension_pos (s + 1)
  have huone : (1 : ℝ) ≤ u := by
    rw [show u = Real.log (D : ℝ) by rfl,
      Real.le_log_iff_exp_le hDpos]
    have hthree : (3 : ℝ) ≤ D := by exact_mod_cast (show 3 ≤ D by omega)
    exact Real.exp_one_lt_three.le.trans hthree
  have hupos : 0 < u := zero_lt_one.trans_le huone
  have hkposNat : 0 < k :=
    (HunterParameters.progressionLength_pos
      (HunterParameters.dimension_pos s)).trans hlower
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hPpos : (0 : ℝ) <
      HunterParameters.progressionLength D := by
    exact_mod_cast HunterParameters.progressionLength_pos
      (HunterParameters.dimension_pos s)
  have hLowerCast :
      (HunterParameters.progressionLength D : ℝ) < k := by
    exact_mod_cast hlower
  have hUpperCast : (k : ℝ) ≤
      HunterParameters.progressionLength E := by
    exact_mod_cast hupper
  have hlogP : Real.log (HunterParameters.progressionLength D : ℝ) =
      (4801 * D : ℕ) * u := by
    simp only [HunterParameters.progressionLength, Nat.cast_pow]
    rw [Real.log_pow]
  have hlogLower : (4801 * D : ℕ) * u < ell := by
    rw [← hlogP]
    exact Real.log_lt_log hPpos hLowerCast
  have hDleEll : (D : ℝ) ≤ ell := by
    calc
      (D : ℝ) ≤ (4801 * D : ℕ) * u := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        have hcoef : (D : ℝ) ≤ 4801 * D := by
          calc
            (D : ℝ) = 1 * D := by ring
            _ ≤ 4801 * D :=
              mul_le_mul_of_nonneg_right (by norm_num) hDpos.le
        have hmul : (4801 * (D : ℝ)) * 1 ≤
            (4801 * (D : ℝ)) * u :=
          mul_le_mul_of_nonneg_left huone
            (mul_nonneg (by norm_num) hDpos.le)
        exact hcoef.trans (by simpa only [mul_one] using hmul)
      _ ≤ ell := hlogLower.le
  have hellpos : 0 < ell := hDpos.trans_le hDleEll
  have hdenLower : u ≤ Real.log ell := by
    dsimp only [u]
    exact Real.log_le_log hDpos hDleEll
  have hdenpos : 0 < Real.log ell := hupos.trans_le hdenLower
  have hlogE_le : Real.log (E : ℝ) ≤ 2 * u := by
    have hEcast : (E : ℝ) ≤ 2 * D := by exact_mod_cast hEle
    have hlogED : Real.log (E : ℝ) ≤ Real.log (2 * (D : ℝ)) :=
      Real.log_le_log hEpos hEcast
    have hlogMul : Real.log (2 * (D : ℝ)) = Real.log 2 + u := by
      rw [Real.log_mul (by norm_num) hDpos.ne']
    have hlogTwo : Real.log 2 ≤ u := by
      dsimp only [u]
      exact Real.log_le_log (by norm_num) hDtwo
    rw [hlogMul] at hlogED
    linarith
  have hlogEpos : 0 ≤ Real.log (E : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ E by have := HunterParameters.dimension_pos (s + 1); omega))
  have hlogNext :
      Real.log (HunterParameters.progressionLength E : ℝ) =
        (4801 * E : ℕ) * Real.log (E : ℝ) := by
    simp only [HunterParameters.progressionLength, Nat.cast_pow]
    rw [Real.log_pow]
  have hEllUpper0 : ell ≤
      (4801 * E : ℕ) * Real.log (E : ℝ) := by
    rw [← hlogNext]
    exact Real.log_le_log hkpos hUpperCast
  have hEllUpper : ell ≤ 20000 * (D : ℝ) * u := by
    have hEcast : (E : ℝ) ≤ 2 * D := by exact_mod_cast hEle
    have hcoeff : (4801 * E : ℕ) * Real.log (E : ℝ) ≤
        (4801 * (2 * D) : ℝ) * (2 * u) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hcoef : (4801 * (E : ℝ)) ≤ 4801 * (2 * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hEcast (by norm_num)
      exact mul_le_mul
        hcoef hlogE_le hlogEpos
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hDpos.le))
    calc
      ell ≤ (4801 * E : ℕ) * Real.log (E : ℝ) := hEllUpper0
      _ ≤ (4801 * (2 * D) : ℝ) * (2 * u) := hcoeff
      _ ≤ 20000 * (D : ℝ) * u := by
        have hDu : 0 ≤ (D : ℝ) * u := mul_nonneg hDpos.le hupos.le
        calc
          (4801 * (2 * D) : ℝ) * (2 * u) =
              19204 * ((D : ℝ) * u) := by ring
          _ ≤ 20000 * ((D : ℝ) * u) :=
            mul_le_mul_of_nonneg_right (by norm_num) hDu
          _ = 20000 * (D : ℝ) * u := by ring
  have hsq : ell ^ 2 ≤ (20000 * (D : ℝ) * u) ^ 2 :=
    pow_le_pow_left₀ hellpos.le hEllUpper 2
  have hratio : ell ^ 2 / Real.log ell ≤
      400000000 * (D : ℝ) ^ 2 * u := by
    calc
      ell ^ 2 / Real.log ell ≤ ell ^ 2 / u :=
        div_le_div_of_nonneg_left (sq_nonneg ell) hupos hdenLower
      _ ≤ (20000 * (D : ℝ) * u) ^ 2 / u :=
        div_le_div_of_nonneg_right hsq hupos.le
      _ = 400000000 * (D : ℝ) ^ 2 * u := by
        field_simp [hupos.ne']
        ring
  have hscaled : (1 / 100000000000 : ℝ) * ell ^ 2 /
      Real.log ell ≤ (D : ℝ) ^ 2 * u / 200 := by
    calc
      (1 / 100000000000 : ℝ) * ell ^ 2 / Real.log ell =
          (1 / 100000000000 : ℝ) *
            (ell ^ 2 / Real.log ell) := by ring
      _ ≤ (1 / 100000000000 : ℝ) *
          (400000000 * (D : ℝ) ^ 2 * u) := by gcongr
      _ ≤ (D : ℝ) ^ 2 * u / 200 := by
        have hDu : 0 ≤ (D : ℝ) ^ 2 * u :=
          mul_nonneg (sq_nonneg _) hupos.le
        calc
          (1 / 100000000000 : ℝ) *
              (400000000 * (D : ℝ) ^ 2 * u) =
            (1 / 250 : ℝ) * ((D : ℝ) ^ 2 * u) := by ring
          _ ≤ (1 / 200 : ℝ) * ((D : ℝ) ^ 2 * u) :=
            mul_le_mul_of_nonneg_right (by norm_num) hDu
          _ = (D : ℝ) ^ 2 * u / 200 := by ring
  have hexpCast :
      ((D ^ 2 / 200 : ℕ) : ℝ) = (D : ℝ) ^ 2 / 200 := by
    rw [show D ^ 2 / 200 = 200 * (s + 1) ^ 2 by
      simpa [D] using HunterParameters.dimension_sq_div_two_hundred s]
    have hDform : (D : ℝ) = 200 * (s + 1) := by
      dsimp only [D, HunterParameters.dimension]
      push_cast
      ring
    rw [hDform]
    push_cast
    ring
  have hlogN :
      Real.log (HunterParameters.intervalLength D : ℝ) =
        (D : ℝ) ^ 2 * u / 200 := by
    simp only [HunterParameters.intervalLength, Nat.cast_pow]
    rw [Real.log_pow, hexpCast]
    ring
  have hNpos : (0 : ℝ) < HunterParameters.intervalLength D := by
    exact_mod_cast HunterParameters.intervalLength_pos
      (HunterParameters.dimension_pos s)
  rw [show Real.log k = ell by rfl,
    show Real.log (Real.log k) = Real.log ell by rfl]
  rw [← Real.exp_log hNpos, Real.exp_le_exp]
  exact hscaled.trans_eq hlogN.symm

lemma exists_hunter_progression_scale (k : ℕ) :
    ∃ t : ℕ, k ≤ HunterParameters.progressionLength
      (HunterParameters.dimension t) := by
  have h := HunterParameters.tendsto_progressionLength_dimension
  rw [tendsto_atTop_atTop] at h
  obtain ⟨a, ha⟩ := h k
  exact ⟨a, ha a le_rfl⟩

/-- Hunter's superpolynomial lower bound, in an explicit eventual form. -/
def HunterLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop,
      Real.exp (c * (Real.log k) ^ 2 / Real.log (Real.log k)) ≤ (W3 k : ℝ)

/-- Hunter's lower bound, proved unconditionally from the checked finite
torus construction. -/
theorem hunterLowerBound : HunterLowerBound := by
  refine ⟨1 / 100000000000, by norm_num, ?_⟩
  filter_upwards [eventually_gt_atTop
      (HunterParameters.progressionLength (HunterParameters.dimension 0))]
    with k hk
  let hex := exists_hunter_progression_scale k
  let t : ℕ := Nat.find hex
  have htupper : k ≤ HunterParameters.progressionLength
      (HunterParameters.dimension t) := by
    simpa only [t] using Nat.find_spec hex
  have htpos : 0 < t := by
    by_contra ht
    have htzero : t = 0 := Nat.eq_zero_of_not_pos ht
    have hzero : k ≤ HunterParameters.progressionLength
        (HunterParameters.dimension 0) := by
      simpa only [htzero] using htupper
    omega
  let s : ℕ := t - 1
  have hst : s < t := by
    dsimp only [s]
    omega
  have hlower : HunterParameters.progressionLength
      (HunterParameters.dimension s) < k := by
    have hmin : ¬k ≤ HunterParameters.progressionLength
        (HunterParameters.dimension s) :=
      Nat.find_min hex (by simpa only [t] using hst)
    omega
  have hts : t = s + 1 := by
    dsimp only [s]
    omega
  have hupper : k ≤ HunterParameters.progressionLength
      (HunterParameters.dimension (s + 1)) := by
    rw [← hts]
    exact htupper
  have hanalytic := hunter_sequence_exponential_bound hlower hupper
  have hbad : ¬ ForcesW3
      (HunterParameters.intervalLength (HunterParameters.dimension s)) k := by
    intro hforces
    exact not_forcesW3_hunter_sequence s
      (forcesW3_antitone_length hlower.le hforces)
  have hlt : HunterParameters.intervalLength
      (HunterParameters.dimension s) < W3 k :=
    lt_W3_of_not_forcesW3 hbad
  exact hanalytic.trans (by exact_mod_cast hlt.le)

/-- The blue progression length in Hunter's finite coloring theorem. -/
noncomputable def hunterBlueLength (C : ℝ) (N : ℕ) : ℕ :=
  ⌈Real.exp (C * Real.sqrt
    (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))⌉₊

/-- Hunter's source theorem in its construction-facing form: for all large
`N`, there is a coloring with neither a red three-term progression nor a blue
progression of the displayed length.  Writing it as failure of `ForcesW3`
keeps the quantification over the actual coloring exact. -/
def HunterColoringBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ¬ ForcesW3 N (hunterBlueLength C N)

/-- Sample size used to invert Hunter's blue-length threshold. -/
noncomputable def hunterSampleSize (δ : ℝ) (k : ℕ) : ℕ :=
  ⌈Real.exp (δ * (Real.log (k : ℝ)) ^ 2 /
    Real.log (Real.log (k : ℝ)))⌉₊

lemma hunterSampleSize_lower (δ : ℝ) (k : ℕ) :
    Real.exp (δ * (Real.log (k : ℝ)) ^ 2 /
      Real.log (Real.log (k : ℝ))) ≤ (hunterSampleSize δ k : ℝ) := by
  exact Nat.le_ceil _

/-- The exponent defining `hunterSampleSize` tends to infinity. -/
lemma tendsto_hunterExponent {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ ↦ δ * (Real.log (k : ℝ)) ^ 2 /
      Real.log (Real.log (k : ℝ))) atTop atTop := by
  have hL : Tendsto (fun k : ℕ ↦ Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ k : ℕ in atTop,
      0 < Real.log (Real.log (k : ℝ)) ∧
        Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) := by
    filter_upwards
      [(Real.tendsto_log_atTop.comp hL).eventually (eventually_gt_atTop 0),
        hL.eventually (eventually_ge_atTop 0)] with k hell hL0
    exact ⟨hell, Real.log_le_self hL0⟩
  apply tendsto_atTop_mono'
    (f₁ := fun k : ℕ ↦ δ * Real.log (k : ℝ))
    (f₂ := fun k : ℕ ↦ δ * (Real.log (k : ℝ)) ^ 2 /
      Real.log (Real.log (k : ℝ)))
  · filter_upwards [hsmall] with k hk
    rw [le_div_iff₀ hk.1]
    have hL0 : 0 ≤ Real.log (k : ℝ) := (hk.1.trans_le hk.2).le
    simpa [pow_two, mul_assoc] using
      (mul_le_mul_of_nonneg_left hk.2 (mul_nonneg hδ.le hL0))
  · exact hL.const_mul_atTop hδ

lemma tendsto_hunterSampleSize {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (hunterSampleSize δ) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    (Real.tendsto_exp_atTop.comp (tendsto_hunterExponent hδ))

/-- Pointwise quantitative inversion of Hunter's threshold.  The hypotheses
are precisely the elementary eventual inequalities used in the inversion. -/
lemma hunterBlueLength_hunterSampleSize_le {C δ : ℝ} {k : ℕ}
    (_hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hCδ : 6 * C ^ 2 * δ ≤ 1)
    (hL : 1 ≤ Real.log (k : ℝ))
    (hell : 1 ≤ Real.log (Real.log (k : ℝ)))
    (hv : 1 ≤ δ * (Real.log (k : ℝ)) ^ 2 /
      Real.log (Real.log (k : ℝ))) :
    hunterBlueLength C (hunterSampleSize δ k) ≤ k := by
  let L : ℝ := Real.log (k : ℝ)
  let ell : ℝ := Real.log L
  let v : ℝ := δ * L ^ 2 / ell
  let N : ℕ := hunterSampleSize δ k
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hell0 : 0 ≤ ell := le_trans zero_le_one hell
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hv0 : 0 ≤ v := le_trans zero_le_one hv
  have hExpLeN : Real.exp v ≤ (N : ℝ) := by
    simpa [N, hunterSampleSize, v, L, ell] using
      (Nat.le_ceil (Real.exp v))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos v).trans_le hExpLeN
  have hNupper : (N : ℝ) ≤ 2 * Real.exp v := by
    have hceil : (N : ℝ) < Real.exp v + 1 := by
      simpa [N, hunterSampleSize, v, L, ell] using
        (Nat.ceil_lt_add_one (Real.exp_pos v).le)
    have hexpv : 1 ≤ Real.exp v := by
      simpa using (Real.exp_le_exp.mpr hv0)
    linarith
  have hlogNle : Real.log (N : ℝ) ≤ 2 * v := by
    calc
      Real.log (N : ℝ) ≤ Real.log (2 * Real.exp v) :=
        Real.log_le_log hNpos hNupper
      _ = Real.log 2 + v := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos v).ne', Real.log_exp]
      _ ≤ 2 * v := by nlinarith [Real.log_two_lt_d9]
  have hlogNge : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact (Real.exp_le_exp.mpr hv).trans hExpLeN
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hlogNge
  have hloglogN0 : 0 ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_nonneg hlogNge
  have hvle : v ≤ L ^ 2 := by
    dsimp [v]
    rw [div_le_iff₀ hellpos]
    have hδmul : δ * L ^ 2 ≤ 1 * L ^ 2 :=
      mul_le_mul_of_nonneg_right hδ1 (sq_nonneg L)
    nlinarith [mul_le_mul_of_nonneg_left hell hL0]
  have hloglogNle : Real.log (Real.log (N : ℝ)) ≤ 3 * ell := by
    calc
      Real.log (Real.log (N : ℝ)) ≤ Real.log (2 * v) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one hlogNge) hlogNle
      _ ≤ Real.log (2 * L ^ 2) := by
        apply Real.log_le_log (by positivity)
        exact mul_le_mul_of_nonneg_left hvle (by norm_num)
      _ = Real.log 2 + 2 * ell := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        simp [ell]
      _ ≤ 3 * ell := by nlinarith [Real.log_two_lt_d9]
  have hprod :
      Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) ≤
        6 * δ * L ^ 2 := by
    calc
      Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) ≤
          (2 * v) * (3 * ell) :=
        mul_le_mul hlogNle hloglogNle hloglogN0 (by positivity)
      _ = 6 * δ * L ^ 2 := by
        dsimp [v]
        field_simp
        norm_num
  have hsqrt :
      C * Real.sqrt
          (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤ L := by
    have hinside0 : 0 ≤
        Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) :=
      mul_nonneg hlogN0 hloglogN0
    have hsquares :
        (C * Real.sqrt
          (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) ^ 2 ≤ L ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hinside0]
      calc
        C ^ 2 *
            (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤
              C ^ 2 * (6 * δ * L ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (sq_nonneg C)
        _ ≤ L ^ 2 := by
          have := mul_le_mul_of_nonneg_right hCδ (sq_nonneg L)
          nlinarith
    nlinarith [Real.sqrt_nonneg
      (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))]
  rw [hunterBlueLength, Nat.ceil_le]
  change Real.exp (C * Real.sqrt
      (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) ≤ (k : ℝ)
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < L := hLpos
    exact_mod_cast (show 0 < k by
      by_contra hk
      simp_all [L])
  rw [← Real.exp_log hkpos]
  exact Real.exp_le_exp.mpr hsqrt

/-- Hunter's finite coloring theorem implies his stated lower bound for
`W(3,k)`, with every floor/ceiling and logarithmic comparison explicit. -/
theorem hunterLowerBound_of_hunterColoringBound
    (h : HunterColoringBound) : HunterLowerBound := by
  obtain ⟨C, hC, hsource⟩ := h
  let δ : ℝ := 1 / (8 * (C + 1) ^ 2)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg C]
  have hCδ : 6 * C ^ 2 * δ ≤ 1 := by
    dsimp [δ]
    rw [one_div, ← div_eq_mul_inv]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (C + 1), sq_nonneg C]
  refine ⟨δ, hδ0, ?_⟩
  have hsource' : ∀ᶠ k : ℕ in atTop,
      ¬ ForcesW3 (hunterSampleSize δ k)
        (hunterBlueLength C (hunterSampleSize δ k)) :=
    (tendsto_hunterSampleSize hδ0).eventually hsource
  have hlog : Tendsto (fun k : ℕ ↦ Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun k : ℕ ↦ Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hsource', hlog.eventually (eventually_ge_atTop 1),
      hloglog.eventually (eventually_ge_atTop 1),
      (tendsto_hunterExponent hδ0).eventually (eventually_ge_atTop 1)]
    with k hbad hL hell hv
  have hlength : hunterBlueLength C (hunterSampleSize δ k) ≤ k :=
    hunterBlueLength_hunterSampleSize_le hC hδ0 hδ1 hCδ hL hell hv
  have hbadk : ¬ ForcesW3 (hunterSampleSize δ k) k := by
    intro hforces
    exact hbad (forcesW3_antitone_length hlength hforces)
  have hlt : hunterSampleSize δ k < W3 k :=
    lt_W3_of_not_forcesW3 hbadk
  exact (hunterSampleSize_lower δ k).trans (by exact_mod_cast hlt.le)

/-- Hunter's blue-length threshold tends to infinity. -/
lemma tendsto_hunterBlueLength {C : ℝ} (hC : 0 < C) :
    Tendsto (hunterBlueLength C) atTop atTop := by
  have hL : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hell : Tendsto (fun N : ℕ ↦
      Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hprod : Tendsto (fun N : ℕ ↦
      Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    hL.atTop_mul_atTop₀ hell
  exact tendsto_nat_ceil_atTop.comp
    (Real.tendsto_exp_atTop.comp
      ((Real.tendsto_sqrt_atTop.comp hprod).const_mul_atTop hC))

/-- Pointwise estimate for the reverse inversion: at Hunter's forward blue
threshold, the exponent in `HunterLowerBound` is at least `2 log N`, once
the elementary eventual inequalities hold. -/
lemma hunterExponent_at_blueLength_ge {c C : ℝ} {N : ℕ}
    (hc : 0 < c) (hC : 0 < C) (hcoef : 4 ≤ c * C ^ 2)
    (hL : 1 ≤ Real.log (N : ℝ))
    (hell : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hlogC : Real.log (2 * C) ≤ Real.log (Real.log (N : ℝ)))
    (hv : 2 ≤ C * Real.sqrt
      (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) :
    2 * Real.log (N : ℝ) ≤
      c * (Real.log (hunterBlueLength C N : ℝ)) ^ 2 /
        Real.log (Real.log (hunterBlueLength C N : ℝ)) := by
  let L : ℝ := Real.log (N : ℝ)
  let ell : ℝ := Real.log L
  let s : ℝ := Real.sqrt (L * ell)
  let v : ℝ := C * s
  let k : ℕ := hunterBlueLength C N
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hell0 : 0 ≤ ell := zero_le_one.trans hell
  have hellpos : 0 < ell := zero_lt_one.trans_le hell
  have hprod0 : 0 ≤ L * ell := mul_nonneg hL0 hell0
  have hspos : 0 < s := Real.sqrt_pos.mpr (mul_pos hLpos hellpos)
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hExpLeK : Real.exp v ≤ (k : ℝ) := by
    simpa [k, hunterBlueLength, v, s, L, ell] using
      (Nat.le_ceil (Real.exp v))
  have hkpos : 0 < (k : ℝ) := (Real.exp_pos v).trans_le hExpLeK
  have hkupper : (k : ℝ) ≤ 2 * Real.exp v := by
    have hceil : (k : ℝ) < Real.exp v + 1 := by
      simpa [k, hunterBlueLength, v, s, L, ell] using
        (Nat.ceil_lt_add_one (Real.exp_pos v).le)
    have hexpone : 1 ≤ Real.exp v := by
      simpa using (Real.exp_le_exp.mpr hv0)
    linarith
  have hlogkLower : v ≤ Real.log (k : ℝ) := by
    rw [Real.le_log_iff_exp_le hkpos]
    exact hExpLeK
  have hlogkUpper : Real.log (k : ℝ) ≤ 2 * v := by
    calc
      Real.log (k : ℝ) ≤ Real.log (2 * Real.exp v) :=
        Real.log_le_log hkpos hkupper
      _ = Real.log 2 + v := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos v).ne', Real.log_exp]
      _ ≤ 2 * v := by nlinarith [Real.log_two_lt_d9]
  have hlogkOne : 1 ≤ Real.log (k : ℝ) :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (hv.trans hlogkLower)
  have hlogkStrict : 1 < Real.log (k : ℝ) :=
    (by norm_num : (1 : ℝ) < 2).trans_le (hv.trans hlogkLower)
  have hloglogkpos : 0 < Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pos_iff (by positivity)]
    exact hlogkStrict
  have hlogell : Real.log ell ≤ ell := Real.log_le_self hell0
  have hloglogkUpper : Real.log (Real.log (k : ℝ)) ≤ 2 * ell := by
    calc
      Real.log (Real.log (k : ℝ)) ≤ Real.log (2 * v) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one hlogkOne) hlogkUpper
      _ = Real.log (2 * C) + (ell + Real.log ell) / 2 := by
        rw [show 2 * v = (2 * C) * s by simp [v]; ring]
        rw [Real.log_mul (by positivity) hspos.ne', Real.log_sqrt hprod0,
          Real.log_mul hLpos.ne' hellpos.ne']
      _ ≤ 2 * ell := by
        dsimp [ell] at hlogC ⊢
        nlinarith
  have hlogsq : v ^ 2 ≤ (Real.log (k : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hv0 hlogkLower 2
  calc
    2 * L ≤ c * C ^ 2 * L / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hL0]
    _ = c * v ^ 2 / (2 * ell) := by
      dsimp [v, s]
      rw [mul_pow, Real.sq_sqrt hprod0]
      field_simp
    _ ≤ c * (Real.log (k : ℝ)) ^ 2 / (2 * ell) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogsq hc.le) (by positivity)
    _ ≤ c * (Real.log (k : ℝ)) ^ 2 /
        Real.log (Real.log (k : ℝ)) := by
      exact div_le_div_of_nonneg_left (by positivity) hloglogkpos hloglogkUpper

/-- The published Hunter lower bound conversely supplies bad colorings at
Hunter's forward threshold (after changing the absolute constant).  Together
with `hunterLowerBound_of_hunterColoringBound`, this shows that the source
predicate is an equivalent construction-facing formulation. -/
theorem hunterColoringBound_of_hunterLowerBound
    (h : HunterLowerBound) : HunterColoringBound := by
  obtain ⟨c, hc, hlower⟩ := h
  let C : ℝ := 8 * (c⁻¹ + 1)
  have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have hC : 0 < C := by dsimp [C]; positivity
  have hcoef : 4 ≤ c * C ^ 2 := by
    dsimp [C]
    nlinarith [sq_nonneg (c⁻¹ - 1), inv_pos.mpr hc]
  refine ⟨C, hC, ?_⟩
  have hL : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hell : Tendsto (fun N : ℕ ↦
      Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hprod : Tendsto (fun N : ℕ ↦
      Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    hL.atTop_mul_atTop₀ hell
  have hv : Tendsto (fun N : ℕ ↦ C * Real.sqrt
      (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hprod).const_mul_atTop hC
  have hlower' : ∀ᶠ N : ℕ in atTop,
      Real.exp (c *
          (Real.log (hunterBlueLength C N : ℝ)) ^ 2 /
            Real.log (Real.log (hunterBlueLength C N : ℝ))) ≤
        (W3 (hunterBlueLength C N) : ℝ) :=
    (tendsto_hunterBlueLength hC).eventually hlower
  filter_upwards [hlower', hL.eventually (eventually_ge_atTop 1),
      hell.eventually (eventually_ge_atTop 1),
      hell.eventually (eventually_ge_atTop (Real.log (2 * C))),
      hv.eventually (eventually_ge_atTop 2)]
    with N hW hLN hellN hlogC hvN
  let k := hunterBlueLength C N
  let E := c * (Real.log (k : ℝ)) ^ 2 /
    Real.log (Real.log (k : ℝ))
  have hE : 2 * Real.log (N : ℝ) ≤ E := by
    simpa [E, k] using
      hunterExponent_at_blueLength_ge hc hC hcoef hLN hellN hlogC hvN
  have hNpos : 0 < (N : ℝ) := by
    have hNnat : 0 < N := by
      by_contra hN
      have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      norm_num at hLN
    exact_mod_cast hNnat
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans_le hLN
  have hNltExp : (N : ℝ) < Real.exp E := by
    rw [← Real.exp_log hNpos]
    have hloglt : Real.log (N : ℝ) < 2 * Real.log (N : ℝ) := by
      nlinarith
    exact Real.exp_lt_exp.mpr (hloglt.trans_le hE)
  have hW' : Real.exp E ≤ (W3 k : ℝ) := by simpa [E, k] using hW
  have hNk : N < W3 k := by
    exact_mod_cast hNltExp.trans_le hW'
  exact not_forcesW3_of_lt_W3 hNk

/-- The fully explicit elementary lower bound proved above. -/
def ElementaryLowerBound : Prop :=
  ∀ k : ℕ, 3 ≤ k → 2 * k - 1 ≤ W3 k

theorem elementaryLowerBound : ElementaryLowerBound :=
  fun _ hk ↦ two_mul_sub_one_le_W3 hk

/-! ### A genuinely superlinear lower bound by the probabilistic method

Choose every point red with probability `p`.  There are at most `n²`
three-term progressions and at most `n²` progressions of length `k`, so the
expected number of forbidden monochromatic progressions is at most
`n² * (p³ + (1-p)^k)`.  Taking `k=t⁵`, `n=⌊t⁶/8⌋`, and `p=t⁻⁴` gives the
unconditional superlinear family `W(3,t⁵) > t⁶/8` eventually. -/

section ProbabilisticLowerBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator that none of the coordinates in `T` was selected. -/
def antiMonomial (T W : Finset V) : ℝ := if Disjoint T W then 1 else 0

lemma antiMonomial_eq_monomial_compl (T W : Finset V) :
    antiMonomial T W = monomial T Wᶜ := by
  by_cases h : Disjoint T W
  · rw [antiMonomial, if_pos h, monomial, if_pos]
    intro x hxT
    simpa using (Finset.disjoint_left.mp h hxT)
  · rw [antiMonomial, if_neg h, monomial, if_neg]
    intro hsub
    apply h
    rw [Finset.disjoint_left]
    intro x hxT hxW
    exact (by simpa using hsub hxT : x ∉ W) hxW

lemma bernoulliWeight_compl (p : ℝ) (W : Finset V) :
    bernoulliWeight p Wᶜ = bernoulliWeight (1 - p) W := by
  have hcard : W.card ≤ Fintype.card V := Finset.card_le_univ W
  have hsub : Fintype.card V - (Fintype.card V - W.card) = W.card := by omega
  simp [bernoulliWeight, Erdos202.ParkPham.bernoulliMass,
    Finset.card_compl, hsub]
  ring_nf

/-- Complementation is an involution on finite subsets. -/
def finsetComplEquiv : Finset V ≃ Finset V where
  toFun W := Wᶜ
  invFun W := Wᶜ
  left_inv W := by simp
  right_inv W := by simp

/-- In a Bernoulli-`p` subset, a fixed `T` is entirely absent with probability
`(1-p)^|T|`. -/
lemma expectation_antiMonomial {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Finset V) : expectation p (antiMonomial T) = (1 - p) ^ T.card := by
  rw [expectation]
  calc
    (∑ W : Finset V, bernoulliWeight p W * antiMonomial T W) =
        ∑ W : Finset V,
          bernoulliWeight p Wᶜ * antiMonomial T Wᶜ := by
      apply Fintype.sum_equiv (finsetComplEquiv (V := V))
      intro W
      simp [finsetComplEquiv]
    _ = ∑ W : Finset V, bernoulliWeight (1 - p) W * monomial T W := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [bernoulliWeight_compl, antiMonomial_eq_monomial_compl,
        compl_compl]
    _ = expectation (1 - p) (monomial T) := rfl
    _ = (1 - p) ^ T.card := by
      apply expectation_monomial
      · linarith
      · linarith

/-- A positive-step progression encoded by its start and step. -/
def APIndex (n l : ℕ) :=
  {ad : Fin n × Fin n // 0 < ad.2.val ∧ ad.1.val + (l - 1) * ad.2.val < n}
  deriving Fintype, DecidableEq

def apTerm {n l : ℕ} (P : APIndex n l) (i : Fin l) : Fin n :=
  ⟨P.1.1.val + i.val * P.1.2.val, by
    have hi : i.val ≤ l - 1 := by omega
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _) P.2.2⟩

lemma apTerm_injective {n l : ℕ} (P : APIndex n l) :
    Function.Injective (apTerm P) := by
  intro i j hij
  apply Fin.ext
  have hij := congrArg Fin.val hij
  change P.1.1.val + i.val * P.1.2.val =
      P.1.1.val + j.val * P.1.2.val at hij
  have hmul : i.val * P.1.2.val = j.val * P.1.2.val := Nat.add_left_cancel hij
  exact Nat.eq_of_mul_eq_mul_right P.2.1 hmul

def apSupport {n l : ℕ} (P : APIndex n l) : Finset (Fin n) :=
  Finset.univ.image (apTerm P)

lemma card_apSupport {n l : ℕ} (P : APIndex n l) :
    (apSupport P).card = l := by
  rw [apSupport, Finset.card_image_of_injective _ (apTerm_injective P), Finset.card_univ,
    Fintype.card_fin]

/-- Start and step both lie below `n`, giving the coarse `n²` count. -/
lemma card_APIndex_le (n l : ℕ) : Fintype.card (APIndex n l) ≤ n ^ 2 := by
  calc
    Fintype.card (APIndex n l) ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n ^ 2 := by simp [pow_two]

noncomputable def redBadCount (n : ℕ) (W : Finset (Fin n)) : ℝ :=
  ∑ P : APIndex n 3, monomial (apSupport P) W

noncomputable def blueBadCount (n k : ℕ) (W : Finset (Fin n)) : ℝ :=
  ∑ P : APIndex n k, antiMonomial (apSupport P) W

lemma expectation_redBadCount {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    expectation p (redBadCount n) = Fintype.card (APIndex n 3) * p ^ 3 := by
  change expectation p (fun W ↦ ∑ P ∈ (Finset.univ : Finset (APIndex n 3)),
    monomial (apSupport P) W) = _
  rw [expectation_sum p Finset.univ]
  simp_rw [expectation_monomial hp0 hp1, card_apSupport]
  simp [mul_comm]

lemma expectation_blueBadCount {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    expectation p (blueBadCount n k) = Fintype.card (APIndex n k) * (1 - p) ^ k := by
  change expectation p (fun W ↦ ∑ P ∈ (Finset.univ : Finset (APIndex n k)),
    antiMonomial (apSupport P) W) = _
  rw [expectation_sum p Finset.univ]
  simp_rw [expectation_antiMonomial hp0 hp1, card_apSupport]
  simp

lemma redBadCount_eq_card (n : ℕ) (W : Finset (Fin n)) :
    redBadCount n W =
      ((Finset.univ.filter fun P : APIndex n 3 ↦ apSupport P ⊆ W).card : ℝ) := by
  change (∑ P ∈ (Finset.univ : Finset (APIndex n 3)),
    if apSupport P ⊆ W then 1 else 0) = _
  rw [Finset.sum_boole]

lemma blueBadCount_eq_card (n k : ℕ) (W : Finset (Fin n)) :
    blueBadCount n k W =
      ((Finset.univ.filter fun P : APIndex n k ↦ Disjoint (apSupport P) W).card : ℝ) := by
  change (∑ P ∈ (Finset.univ : Finset (APIndex n k)),
    if Disjoint (apSupport P) W then 1 else 0) = _
  rw [Finset.sum_boole]

/-- Finite union bound, proved through an exact expectation. -/
lemma exists_subset_avoiding_APs_of_criterion {n k : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcrit : (n : ℝ) ^ 2 * (p ^ 3 + (1 - p) ^ k) < 1) :
    ∃ W : Finset (Fin n), redBadCount n W = 0 ∧ blueBadCount n k W = 0 := by
  have hmean :
      expectation p (fun W ↦ redBadCount n W + blueBadCount n k W) < 1 := by
    rw [expectation_add, expectation_redBadCount hp0 hp1,
      expectation_blueBadCount hp0 hp1]
    calc
      (Fintype.card (APIndex n 3) : ℝ) * p ^ 3 +
          Fintype.card (APIndex n k) * (1 - p) ^ k ≤
          (n : ℝ) ^ 2 * p ^ 3 + (n : ℝ) ^ 2 * (1 - p) ^ k := by
        gcongr
        · exact_mod_cast card_APIndex_le n 3
        · exact_mod_cast card_APIndex_le n k
      _ = (n : ℝ) ^ 2 * (p ^ 3 + (1 - p) ^ k) := by ring
      _ < 1 := hcrit
  have hex : ∃ W : Finset (Fin n), redBadCount n W + blueBadCount n k W < 1 := by
    by_contra h
    have hall : ∀ W : Finset (Fin n),
        1 ≤ redBadCount n W + blueBadCount n k W := by
      intro W
      exact le_of_not_gt fun hlt ↦ h ⟨W, hlt⟩
    have hge : 1 ≤ expectation p (fun W ↦ redBadCount n W + blueBadCount n k W) := by
      rw [← expectation_const (V := Fin n) p 1]
      unfold expectation
      apply Finset.sum_le_sum
      intro W hW
      exact mul_le_mul_of_nonneg_left (hall W) (bernoulliWeight_nonneg hp0 hp1 W)
    linarith
  obtain ⟨W, hW⟩ := hex
  have hcast :
      (((Finset.univ.filter fun P : APIndex n 3 ↦ apSupport P ⊆ W).card : ℕ) : ℝ) +
          ((Finset.univ.filter fun P : APIndex n k ↦ Disjoint (apSupport P) W).card : ℝ) < 1 := by
    simpa [redBadCount_eq_card, blueBadCount_eq_card] using hW
  have hnat :
      (Finset.univ.filter fun P : APIndex n 3 ↦ apSupport P ⊆ W).card +
          (Finset.univ.filter fun P : APIndex n k ↦ Disjoint (apSupport P) W).card < 1 := by
    exact_mod_cast hcast
  have hr : (Finset.univ.filter fun P : APIndex n 3 ↦ apSupport P ⊆ W).card = 0 := by
    omega
  have hb : (Finset.univ.filter fun P : APIndex n k ↦ Disjoint (apSupport P) W).card = 0 := by
    omega
  refine ⟨W, ?_, ?_⟩
  · rw [redBadCount_eq_card, hr]
    norm_num
  · rw [blueBadCount_eq_card, hb]
    norm_num

def subsetColor (n : ℕ) (W : Finset (Fin n)) (x : ℕ) : Fin 2 :=
  if h : x < n then if (⟨x, h⟩ : Fin n) ∈ W then 0 else 1 else 1

lemma subsetColor_eq_zero_iff {n : ℕ} {W : Finset (Fin n)} {x : ℕ} :
    subsetColor n W x = 0 ↔ ∃ h : x < n, (⟨x, h⟩ : Fin n) ∈ W := by
  by_cases hx : x < n
  · simp only [subsetColor, dif_pos hx]
    constructor
    · intro h
      have hmem : (⟨x, hx⟩ : Fin n) ∈ W := by
        by_contra hnot
        simp [hnot] at h
      exact ⟨hx, hmem⟩
    · rintro ⟨h, hmem⟩
      have hmem' : (⟨x, hx⟩ : Fin n) ∈ W := by simpa using hmem
      simp [hmem']
  · simp [subsetColor, hx]

lemma no_red_AP_of_redBadCount_eq_zero {n : ℕ} {W : Finset (Fin n)}
    (hzero : redBadCount n W = 0) :
    ¬ HasMonochromaticAP n 3 (subsetColor n W) 0 := by
  rintro ⟨a, d, hd, hlast, hcolor⟩
  have ha : a < n := by omega
  have hdn : d < n := by omega
  let P : APIndex n 3 := ⟨(⟨a, ha⟩, ⟨d, hdn⟩), hd, by simpa using hlast⟩
  have hsupp : apSupport P ⊆ W := by
    intro x hx
    rw [apSupport, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have hc := hcolor i
    rw [subsetColor_eq_zero_iff] at hc
    obtain ⟨_, hc⟩ := hc
    exact hc
  have hmem : P ∈ Finset.univ.filter (fun Q : APIndex n 3 ↦ apSupport Q ⊆ W) := by
    simp [hsupp]
  have hpos := Finset.card_pos.mpr ⟨P, hmem⟩
  rw [redBadCount_eq_card] at hzero
  have hpos' : (0 : ℝ) <
      (Finset.univ.filter (fun Q : APIndex n 3 ↦ apSupport Q ⊆ W)).card := by
    exact_mod_cast hpos
  have heqcard :
      ((Finset.univ.filter (fun Q : APIndex n 3 ↦ apSupport Q ⊆ W)).card : ℝ) = 0 := by
    exact hzero
  linarith

lemma no_blue_AP_of_blueBadCount_eq_zero {n k : ℕ} {W : Finset (Fin n)}
    (hk : 2 ≤ k) (hzero : blueBadCount n k W = 0) :
    ¬ HasMonochromaticAP n k (subsetColor n W) 1 := by
  rintro ⟨a, d, hd, hlast, hcolor⟩
  have ha : a < n := by omega
  have hdmul : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d (by omega)
  have hdn : d < n := by omega
  let P : APIndex n k := ⟨(⟨a, ha⟩, ⟨d, hdn⟩), hd, hlast⟩
  have hdisj : Disjoint (apSupport P) W := by
    rw [Finset.disjoint_left]
    intro x hx hxin
    rw [apSupport, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have hc := hcolor i
    simp [subsetColor] at hc
    exact hc (apTerm P i).isLt (by simpa [apTerm, P] using hxin)
  have hmem : P ∈ Finset.univ.filter
      (fun Q : APIndex n k ↦ Disjoint (apSupport Q) W) := by
    simp [hdisj]
  have hpos := Finset.card_pos.mpr ⟨P, hmem⟩
  rw [blueBadCount_eq_card] at hzero
  have hpos' : (0 : ℝ) <
      (Finset.univ.filter
        (fun Q : APIndex n k ↦ Disjoint (apSupport Q) W)).card := by
    exact_mod_cast hpos
  have heqcard :
      ((Finset.univ.filter
        (fun Q : APIndex n k ↦ Disjoint (apSupport Q) W)).card : ℝ) = 0 := by
    exact hzero
  linarith

/-- If the elementary union-bound expression is below one, an honest bad
coloring exists. -/
theorem not_forcesW3_of_probabilistic_criterion {n k : ℕ} {p : ℝ}
    (hk : 2 ≤ k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcrit : (n : ℝ) ^ 2 * (p ^ 3 + (1 - p) ^ k) < 1) :
    ¬ ForcesW3 n k := by
  obtain ⟨W, hred, hblue⟩ := exists_subset_avoiding_APs_of_criterion hp0 hp1 hcrit
  intro h
  rcases h (subsetColor n W) with hr | hb
  · exact no_red_AP_of_redBadCount_eq_zero hred hr
  · exact no_blue_AP_of_blueBadCount_eq_zero hk hblue hb

lemma one_sub_inv_fourth_pow_fifth_le_exp_neg {t : ℕ} (ht : 1 ≤ t) :
    (1 - 1 / (t : ℝ) ^ 4) ^ (t ^ 5) ≤ Real.exp (-(t : ℝ)) := by
  have htle : (t : ℝ) ≤ ((t ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pow (a := t) (b := 5) (by norm_num)
  have h := Real.one_sub_div_pow_le_exp_neg (n := t ^ 5) (t := (t : ℝ)) htle
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  convert h using 1
  · congr 2
    push_cast
    field_simp

/-- A fully formal, unconditional, genuinely superlinear lower-bound family:
along fifth powers, `W(3,k)` is at least a constant times `k^(6/5)`. -/
theorem eventually_superlinear_lower_on_fifth_powers :
    ∀ᶠ t : ℕ in atTop, t ^ 6 / 8 < W3 (t ^ 5) := by
  have hdecayReal :
      ∀ᶠ x : ℝ in atTop, x ^ 12 * Real.exp (-x) < 1 :=
    (tendsto_order.mp (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12)).2 1 zero_lt_one
  have hdecayNat :
      ∀ᶠ t : ℕ in atTop, (t : ℝ) ^ 12 * Real.exp (-(t : ℝ)) < 1 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hdecayReal
  filter_upwards [hdecayNat, eventually_ge_atTop 2] with t hdecay ht
  let n : ℕ := t ^ 6 / 8
  let k : ℕ := t ^ 5
  let p : ℝ := 1 / (t : ℝ) ^ 4
  have htR : (0 : ℝ) < t := by positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by exact_mod_cast (show 1 ≤ t by omega)))
  have hncast : (n : ℝ) ≤ (t : ℝ) ^ 6 / 8 := by
    dsimp [n]
    simpa using (Nat.cast_div_le (m := t ^ 6) (n := 8) :
      ((t ^ 6 / 8 : ℕ) : ℝ) ≤ ((t ^ 6 : ℕ) : ℝ) / (8 : ℝ))
  have hblue : (1 - p) ^ k ≤ Real.exp (-(t : ℝ)) := by
    simpa [p, k] using one_sub_inv_fourth_pow_fifth_le_exp_neg (show 1 ≤ t by omega)
  have hred : p ^ 3 = 1 / (t : ℝ) ^ 12 := by
    dsimp [p]
    field_simp
  have hcrit : (n : ℝ) ^ 2 * (p ^ 3 + (1 - p) ^ k) < 1 := by
    calc
      (n : ℝ) ^ 2 * (p ^ 3 + (1 - p) ^ k) ≤
          ((t : ℝ) ^ 6 / 8) ^ 2 *
            (1 / (t : ℝ) ^ 12 + Real.exp (-(t : ℝ))) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity) hncast 2
        · exact add_le_add hred.le hblue
        · positivity
        · positivity
      _ = 1 / 64 + ((t : ℝ) ^ 12 * Real.exp (-(t : ℝ))) / 64 := by
        field_simp
        ring
      _ < 1 := by linarith
  have hnot : ¬ ForcesW3 n k :=
    not_forcesW3_of_probabilistic_criterion (by
      dsimp [k]
      exact (show 2 ≤ 2 ^ 5 by norm_num).trans (Nat.pow_le_pow_left ht 5)) hp0 hp1 hcrit
  dsimp [n, k] at hnot ⊢
  by_contra hle
  exact hnot (forcesW3_mono_interval (by omega) (forcesW3_W3 (t ^ 5)))

end ProbabilisticLowerBound

/-- Number of ordered pairs `(a,b) ∈ A²` for which the uniquely determined
third point `b+b-a` also lies in `A`.  Equivalently, this counts ordered
solutions `a+c=b+b` in `A`, including the trivial ones. -/
def threeAPPairCount {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) : ℕ :=
  ((A ×ˢ A).filter fun p ↦ p.2 + p.2 - p.1 ∈ A).card

/-- A three-AP-free set has exactly its diagonal, trivial progressions. -/
lemma threeAPPairCount_eq_card_of_threeAPFree {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hA : ThreeAPFree (A : Set G)) :
    threeAPPairCount A = A.card := by
  have hiff : ∀ a ∈ A, ∀ b ∈ A,
      b + b - a ∈ A ↔ a = b := by
    intro a ha b hb
    constructor
    · intro hz
      apply hA ha hb hz
      abel
    · rintro rfl
      simpa
  unfold threeAPPairCount
  let f : G → G × G := fun a ↦ (a, a)
  symm
  apply Finset.card_bij (fun a _ ↦ f a)
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, ha⟩, ?_⟩
    convert ha using 1
    simp [f]
  · intro a₁ ha₁ a₂ ha₂ heq
    exact congrArg Prod.fst heq
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    have hab := (hiff a hp.1.1 b hp.1.2).mp hp.2
    subst b
    exact ⟨a, hp.1.1, by simp [f]⟩

/-- The diagonal pairs inject into the three-progression pairs. -/
lemma card_le_threeAPPairCount {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] (A : Finset G) :
    A.card ≤ threeAPPairCount A := by
  let e : G ↪ G × G :=
    ⟨fun a ↦ (a, a), fun _ _ h ↦ congrArg Prod.fst h⟩
  have hsubset : A.map e ⊆
      (A ×ˢ A).filter (fun p ↦ p.2 + p.2 - p.1 ∈ A) := by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, ha⟩, ?_⟩
    change a + a - a ∈ A
    simpa
  rw [threeAPPairCount, ← Finset.card_map e]
  exact Finset.card_le_card hsubset

/-- Conversely, if there are no more than the diagonal pairs, the set is
three-AP-free.  Any nontrivial progression would add one more pair to the
embedded diagonal. -/
lemma threeAPFree_of_threeAPPairCount_le_card {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hcount : threeAPPairCount A ≤ A.card) :
    ThreeAPFree (A : Set G) := by
  intro a ha b hb c hc habc
  by_contra hab
  let e : G ↪ G × G :=
    ⟨fun x ↦ (x, x), fun _ _ h ↦ congrArg Prod.fst h⟩
  let T : Finset (G × G) :=
    (A ×ˢ A).filter (fun p ↦ p.2 + p.2 - p.1 ∈ A)
  have hp : (a, b) ∈ T := by
    dsimp only [T]
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, hb⟩, ?_⟩
    have heq : b + b - a = c := by
      apply add_left_cancel (a := a)
      calc
        a + (b + b - a) = b + b := by abel
        _ = a + c := habc.symm
    simpa [heq] using hc
  have hpnot : (a, b) ∉ A.map e := by
    rw [Finset.mem_map]
    rintro ⟨x, hx, heq⟩
    exact hab (by
      have hfst := congrArg Prod.fst heq
      have hsnd := congrArg Prod.snd heq
      simpa [e] using hfst.symm.trans hsnd)
  have hdiag : A.map e ⊆ T := by
    intro p hp'
    rw [Finset.mem_map] at hp'
    obtain ⟨x, hx, rfl⟩ := hp'
    dsimp only [T]
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hx⟩, ?_⟩
    change x + x - x ∈ A
    simpa
  have hinsert : insert (a, b) (A.map e) ⊆ T :=
    Finset.insert_subset hp hdiag
  have htooMany : A.card + 1 ≤ threeAPPairCount A := by
    calc
      A.card + 1 = (insert (a, b) (A.map e)).card := by
        rw [Finset.card_insert_of_notMem hpnot, Finset.card_map]
      _ ≤ T.card := Finset.card_le_card hinsert
      _ = threeAPPairCount A := rfl
  omega

lemma threeAPFree_iff_threeAPPairCount_eq_card {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] {A : Finset G} :
    ThreeAPFree (A : Set G) ↔ threeAPPairCount A = A.card := by
  refine ⟨threeAPPairCount_eq_card_of_threeAPFree, fun h ↦
    threeAPFree_of_threeAPPairCount_le_card h.le⟩

/-- The normalized cyclic Fourier progression functional on an indicator is
exactly the finite ordered-pair count divided by the square of the group
order.  This connects the analytic density-increment argument to the
combinatorial supersaturation endpoint below. -/
lemma CyclicFourier.threeAPCount_indicator_eq_threeAPPairCount
    {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    CyclicFourier.threeAPCount (CyclicFourier.indicator A)
        (CyclicFourier.indicator A) (CyclicFourier.indicator A) =
      ((threeAPPairCount A : ℝ) / (N : ℝ) ^ 2 : ℂ) := by
  rw [CyclicFourier.threeAPCount_eq_equationCount]
  unfold CyclicFourier.threeAPEquationCount CyclicFourier.average
    threeAPPairCount CyclicFourier.indicator
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsum :
      ∑ a : ZMod N, ∑ b : ZMod N,
        (if a ∈ A then (1 : ℂ) else 0) * (if b ∈ A then 1 else 0) *
          (if b + b - a ∈ A then 1 else 0) =
        (((A ×ˢ A).filter fun p ↦ p.2 + p.2 - p.1 ∈ A).card : ℂ) := by
    rw [← Fintype.sum_prod_type (fun p : ZMod N × ZMod N ↦
      (if p.1 ∈ A then 1 else 0) * (if p.2 ∈ A then 1 else 0) *
        (if p.2 + p.2 - p.1 ∈ A then 1 else 0))]
    calc
      (∑ p : ZMod N × ZMod N,
          (if p.1 ∈ A then 1 else 0) * (if p.2 ∈ A then 1 else 0) *
            (if p.2 + p.2 - p.1 ∈ A then 1 else 0)) =
          ∑ p : ZMod N × ZMod N,
            if p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 + p.2 - p.1 ∈ A then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p _hp
        by_cases hpa : p.1 ∈ A <;> by_cases hpb : p.2 ∈ A <;>
          by_cases hpc : p.2 + p.2 - p.1 ∈ A <;> simp [hpa, hpb, hpc]
      _ = ∑ p ∈ (Finset.univ : Finset (ZMod N × ZMod N)).filter
            (fun p ↦ p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 + p.2 - p.1 ∈ A), (1 : ℂ) := by
        rw [Finset.sum_filter]
      _ = ∑ _p ∈ ((A ×ˢ A).filter fun p ↦ p.2 + p.2 - p.1 ∈ A), (1 : ℂ) := by
        congr 1
        ext p
        simp [and_assoc]
      _ = ((A ×ˢ A).filter fun p ↦ p.2 + p.2 - p.1 ∈ A).card := by simp
  simp only [← Finset.mul_sum]
  rw [hsum]
  push_cast
  field_simp

/-- Quantitative supersaturation endpoint of the cyclic Bohr-set argument:
above the Bloom--Sisask density threshold, a set has a nontrivial ordered
three-term progression. -/
def CyclicThreeAPSupersaturation : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset (Fin (2 * N + 1)),
        ((2 * N + 1 : ℕ) : ℝ) *
            Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) <
          (A.card : ℝ) →
        A.card < threeAPPairCount A

/-- The checked cyclic density-increment endpoint, transported across the
canonical ring equivalence `Fin (2N+1) ≃+* ZMod (2N+1)`, gives the exact
supersaturation statement used by the interval reduction. -/
theorem cyclicThreeAPSupersaturation : CyclicThreeAPSupersaturation := by
  obtain ⟨c, hc, hsaturation⟩ :=
    CyclicRothEndpoint.cyclicZModSupersaturation
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsaturation] with N hN
  intro A hlarge
  rw [← not_le]
  intro hcount
  have hfreeFin : ThreeAPFree (A : Set (Fin (2 * N + 1))) :=
    threeAPFree_of_threeAPPairCount_le_card hcount
  let e : Fin (2 * N + 1) ↪ ZMod (2 * N + 1) :=
    (ZMod.finEquiv (2 * N + 1)).toEmbedding
  let AZ : Finset (ZMod (2 * N + 1)) := A.map e
  have hfreeZMod : ThreeAPFree (AZ : Set (ZMod (2 * N + 1))) := by
    intro a ha b hb z hz habz
    simp only [AZ, Finset.mem_coe, Finset.mem_map] at ha hb hz
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨w, hw, rfl⟩ := hz
    have hxyw : x + w = y + y := by
      apply (ZMod.finEquiv (2 * N + 1)).injective
      have habz' :
          (ZMod.finEquiv (2 * N + 1)) x +
                (ZMod.finEquiv (2 * N + 1)) w =
            (ZMod.finEquiv (2 * N + 1)) y +
                (ZMod.finEquiv (2 * N + 1)) y := by
        change e x + e w = e y + e y
        exact habz
      simpa only [map_add] using habz'
    exact congrArg (ZMod.finEquiv (2 * N + 1))
      (hfreeFin hx hy hw hxyw)
  apply hN AZ
  · simpa only [AZ, Finset.card_map] using hlarge
  · exact hfreeZMod

/-- The interval `[0,N)` embeds into the odd cyclic group of order `2N+1`
without introducing a wraparound solution to `x + z = 2y`.  Mathlib's
identification of the initial interval in `Fin (2N+1)` with
`rothNumberNat N` therefore gives this monotonicity statement. -/
lemma rothNumberNat_le_cyclic (N : ℕ) :
    rothNumberNat N ≤
      addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) := by
  let k : Fin (2 * N + 1) := ⟨N, by omega⟩
  calc
    rothNumberNat N = rothNumberNat k := rfl
    _ = addRothNumber (Finset.Iio k) :=
      (Fin.addRothNumber_eq_rothNumberNat (by
        change 2 * N ≤ 2 * N
        exact le_rfl)).symm
    _ ≤ addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) :=
      addRothNumber.mono (Finset.subset_univ _)

/-- A cyclic-group form of the quantitative Bloom--Sisask estimate.  This is
the natural endpoint of the Bohr-set density-increment argument: the ambient
group has odd order, so division by two is available and nontrivial cyclic
three-term progressions have their usual meaning. -/
def CyclicBloomSisaskRothBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop,
      (addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) : ℝ) ≤
        (2 * N + 1 : ℕ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ))

/-- Quantitative supersaturation gives the cyclic Roth bound: apply it to a
maximal three-AP-free subset and use that only its diagonal progressions
remain. -/
theorem cyclicBloomSisaskRothBound_of_supersaturation
    (h : CyclicThreeAPSupersaturation) : CyclicBloomSisaskRothBound := by
  obtain ⟨c, hc, hsaturation⟩ := h
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsaturation] with N hN
  obtain ⟨A, hAuniv, hAcard, hAfree⟩ :=
    addRothNumber_spec (Finset.univ : Finset (Fin (2 * N + 1)))
  by_contra hbound
  rw [not_le] at hbound
  have hlarge :
      ((2 * N + 1 : ℕ) : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) <
        (A.card : ℝ) := by
    simpa [hAcard] using hbound
  have hmore := hN A hlarge
  rw [threeAPPairCount_eq_card_of_threeAPFree hAfree] at hmore
  omega

/-- The Roth bound also gives the stated supersaturation formulation.  Thus
the source boundary is quantitatively equivalent to the desired cyclic
Bloom--Sisask estimate, rather than a strengthened assumption. -/
theorem supersaturation_of_cyclicBloomSisaskRothBound
    (h : CyclicBloomSisaskRothBound) : CyclicThreeAPSupersaturation := by
  obtain ⟨c, hc, hroth⟩ := h
  refine ⟨c, hc, ?_⟩
  filter_upwards [hroth] with N hN
  intro A hlarge
  rw [← not_le]
  intro hcount
  have hfree : ThreeAPFree (A : Set (Fin (2 * N + 1))) :=
    threeAPFree_of_threeAPPairCount_le_card hcount
  have hcard : A.card ≤
      addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) :=
    hfree.le_addRothNumber (Finset.subset_univ A)
  have hcast : (A.card : ℝ) ≤
      (addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) : ℝ) := by
    exact_mod_cast hcard
  exact (not_lt_of_ge (hcast.trans hN)) hlarge

/-- The quantitative Roth estimate proved by Bloom and Sisask, in the exact
form needed for the coloring reduction. -/
def BloomSisaskRothBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      (rothNumberNat n : ℝ) ≤
        (n : ℝ) * Real.exp (-c * (Real.log (n : ℝ)) ^ (1 / 9 : ℝ))

/-- The cyclic quantitative estimate implies the integer estimate.  The
factor `2N+1 ≤ 3N` is absorbed by halving the positive exponential constant. -/
theorem bloomSisaskRothBound_of_cyclic
    (h : CyclicBloomSisaskRothBound) : BloomSisaskRothBound := by
  obtain ⟨c, hc, hcyc⟩ := h
  let c' := c / 2
  have hc' : 0 < c' := by dsimp [c']; positivity
  refine ⟨c', hc', ?_⟩
  have htend : Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ)) ^ (1 / 9 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have habsorb : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 3 / c ≤ (Real.log (N : ℝ)) ^ (1 / 9 : ℝ) :=
    htend.eventually (eventually_ge_atTop (2 * Real.log 3 / c))
  filter_upwards [hcyc, habsorb, eventually_ge_atTop 1] with N hN hlarge hN1
  have htransfer : (rothNumberNat N : ℝ) ≤
      (addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) : ℝ) := by
    exact_mod_cast rothNumberNat_le_cyclic N
  have hcast : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
    exact_mod_cast (show 2 * N + 1 ≤ 3 * N by omega)
  have habsorb' :
      Real.log 3 ≤ c' * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ) := by
    have hmul := (div_le_iff₀ hc).mp hlarge
    dsimp [c']
    nlinarith
  have hexp :
      3 * Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) ≤
        Real.exp (-c' * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [c'] at habsorb' ⊢
    nlinarith
  calc
    (rothNumberNat N : ℝ) ≤
        (addRothNumber (Finset.univ : Finset (Fin (2 * N + 1))) : ℝ) := htransfer
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) := hN
    _ ≤ 3 * (N : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) := by
      gcongr
    _ ≤ (N : ℝ) *
          Real.exp (-c' * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) := by
      calc
        3 * (N : ℝ) *
            Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) =
              (N : ℝ) *
                (3 * Real.exp (-c *
                  (Real.log (N : ℝ)) ^ (1 / 9 : ℝ))) := by ring
        _ ≤ (N : ℝ) *
              Real.exp (-c' * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The quasipolynomial upper bound obtained from the quantitative Roth
theorem of Bloom--Sisask. -/
def QuasipolynomialUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k : ℕ in atTop,
      (W3 k : ℝ) ≤ Real.exp (C * (Real.log k) ^ 9)

/-- Removing the floor in the block count costs at most a factor two. -/
lemma half_div_le_natDiv_cast {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (n : ℝ) / (2 * (k : ℝ)) ≤ (n / k : ℕ) := by
  have hq : 0 < n / k := (Nat.div_pos hkn hk)
  have hrem : n % k < k := Nat.mod_lt n hk
  have hdecomp : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hkq : k ≤ k * (n / k) := Nat.le_mul_of_pos_right k hq
  have hnat : n ≤ 2 * (k * (n / k)) := by omega
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast (by simpa [mul_assoc, mul_left_comm, mul_comm] using hnat)

/-- Taking fifth roots tends to infinity.  This transfers the probabilistic
lower bound proved on the subsequence `k = t^5` to all sufficiently large
blue progression lengths. -/
lemma tendsto_nthRoot_five_atTop :
    Tendsto (Nat.nthRoot 5) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ 5, fun k hk ↦ ?_⟩
  rw [Nat.le_nthRoot_iff (by norm_num : (5 : ℕ) ≠ 0)]
  exact hk

/-- An unconditional all-`k` polynomial lower bound, expressed without
fractional powers.  The inequality

`k^6 < C * W(3,k)^5`

is quantitatively equivalent to `W(3,k) ≫ k^(6/5)` and is therefore a
genuinely superlinear lower bound. -/
def SuperlinearPolynomialLowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k : ℕ in atTop,
      (k : ℝ) ^ 6 < C * (W3 k : ℝ) ^ 5

/-- The sparse probabilistic family `W(3,t^5) > t^6/8`, monotonicity of
`W3`, and the defining inequalities for `Nat.nthRoot` give an unconditional
superlinear lower bound for every sufficiently large `k`. -/
theorem superlinearPolynomialLowerBound : SuperlinearPolynomialLowerBound := by
  let C : ℝ := (2 : ℝ) ^ 30 * 16 ^ 5
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hfamily := tendsto_nthRoot_five_atTop.eventually
    eventually_superlinear_lower_on_fifth_powers
  have hroot2 : ∀ᶠ k : ℕ in atTop, 2 ≤ Nat.nthRoot 5 k :=
    tendsto_nthRoot_five_atTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hfamily, hroot2] with k hfamily hkroot
  let t := Nat.nthRoot 5 k
  have ht2 : 2 ≤ t := by simpa [t] using hkroot
  have ht5 : t ^ 5 ≤ k := by
    exact Nat.pow_nthRoot_le (.inl (by norm_num : (5 : ℕ) ≠ 0))
  have hklt : k < (t + 1) ^ 5 := by
    simpa [t] using Nat.lt_pow_nthRoot_add_one (by norm_num : (5 : ℕ) ≠ 0) k
  have hfamily' : t ^ 6 / 8 < W3 (t ^ 5) := by simpa [t] using hfamily
  have hfloorW : t ^ 6 / 8 < W3 k :=
    hfamily'.trans_le (W3_mono ht5)
  have hhalf : (t : ℝ) ^ 6 / 16 ≤ ((t ^ 6 / 8 : ℕ) : ℝ) := by
    convert half_div_le_natDiv_cast (n := t ^ 6) (k := 8) (by norm_num) (by
      have : 2 ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left ht2 3
      nlinarith [Nat.zero_le (t ^ 3)]) using 1 <;> norm_num
  have htw : (t : ℝ) ^ 6 / 16 < (W3 k : ℝ) := by
    exact hhalf.trans_lt (by exact_mod_cast hfloorW)
  have hkcast : (k : ℝ) < (2 * (t : ℝ)) ^ 5 := by
    exact_mod_cast hklt.trans_le (Nat.pow_le_pow_left (by omega : t + 1 ≤ 2 * t) 5)
  have hkpow : (k : ℝ) ^ 6 < ((2 * (t : ℝ)) ^ 5) ^ 6 :=
    pow_lt_pow_left₀ hkcast (by positivity) (by norm_num)
  have hwpow : ((t : ℝ) ^ 6 / 16) ^ 5 < (W3 k : ℝ) ^ 5 :=
    pow_lt_pow_left₀ htw (by positivity) (by norm_num)
  calc
    (k : ℝ) ^ 6 < ((2 * (t : ℝ)) ^ 5) ^ 6 := hkpow
    _ = C * ((t : ℝ) ^ 6 / 16) ^ 5 := by dsimp [C]; ring
    _ < C * (W3 k : ℝ) ^ 5 := mul_lt_mul_of_pos_left hwpow hC

/-- Numerical heart of the coloring-to-Roth reduction.  A quantitative Roth
estimate at `m`, together with a bad coloring of `[0,m)`, bounds `log m` by a
ninth power of `log k`. -/
lemma log_le_of_roth_estimate {c : ℝ} {m k : ℕ} (hc : 0 < c) (hk : 2 ≤ k)
    (hkm : k ≤ m) (hbad : ¬ ForcesW3 m k)
    (hroth : (rothNumberNat m : ℝ) ≤
      (m : ℝ) * Real.exp (-c * (Real.log (m : ℝ)) ^ (1 / 9 : ℝ))) :
    Real.log (m : ℝ) ≤ (2 / c) ^ 9 * (Real.log (k : ℝ)) ^ 9 := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hblocksNat : m / k ≤ rothNumberNat m :=
    div_le_rothNumberNat_of_not_forcesW3 (by omega) hbad
  have hblocks : (m / k : ℕ) ≤ (rothNumberNat m : ℝ) := by exact_mod_cast hblocksNat
  have hchain :
      (m : ℝ) / (2 * (k : ℝ)) ≤
        (m : ℝ) * Real.exp (-c * (Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) :=
    (half_div_le_natDiv_cast (by omega) hkm).trans (hblocks.trans hroth)
  have hcancel :
      1 / (2 * (k : ℝ)) ≤
        Real.exp (-c * (Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) := by
    apply (mul_le_mul_iff_of_pos_left hmpos).mp
    calc
      (m : ℝ) * (1 / (2 * (k : ℝ))) = (m : ℝ) / (2 * (k : ℝ)) := by ring
      _ ≤ (m : ℝ) * Real.exp
          (-c * (Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) := hchain
  have hlogineq := Real.log_le_log (by positivity) hcancel
  rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hkpos.ne', Real.log_exp] at hlogineq
  have hroot :
      c * (Real.log (m : ℝ)) ^ (1 / 9 : ℝ) ≤
        Real.log (2 * (k : ℝ)) := by
    rw [Real.log_mul (by norm_num) hkpos.ne']
    linarith
  have hrootle :
      (Real.log (m : ℝ)) ^ (1 / 9 : ℝ) ≤ Real.log (2 * (k : ℝ)) / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hroot)
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hlogtwoK : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk])
  have hpow :
      ((Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) ^ 9 ≤
        (Real.log (2 * (k : ℝ)) / c) ^ 9 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hlogm _) hrootle 9
  have hrootpow :
      ((Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) ^ 9 = Real.log (m : ℝ) := by
    convert Real.rpow_inv_natCast_pow hlogm (by norm_num : (9 : ℕ) ≠ 0) using 1
    all_goals norm_num
  have hlogtwo_le : Real.log (2 * (k : ℝ)) ≤ 2 * Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num) hkpos.ne']
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_cast : (2 : ℝ) ≤ k)
    linarith
  calc
    Real.log (m : ℝ) = ((Real.log (m : ℝ)) ^ (1 / 9 : ℝ)) ^ 9 := hrootpow.symm
    _ ≤ (Real.log (2 * (k : ℝ)) / c) ^ 9 := hpow
    _ ≤ ((2 * Real.log (k : ℝ)) / c) ^ 9 := by
      gcongr
    _ = (2 / c) ^ 9 * (Real.log (k : ℝ)) ^ 9 := by ring

/-- The quantitative Roth estimate gives the current quasipolynomial upper
bound for the off-diagonal van der Waerden number. -/
theorem quasipolynomialUpperBound_of_bloomSisaskRothBound
    (h : BloomSisaskRothBound) : QuasipolynomialUpperBound := by
  obtain ⟨c, hc, hroth⟩ := h
  rw [eventually_atTop] at hroth
  obtain ⟨N, hN⟩ := hroth
  let C : ℝ := (2 / c) ^ 9 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (max 3 N)] with k hklarge
  have hk3 : 3 ≤ k := (le_max_left 3 N).trans hklarge
  have hNk : N ≤ k := (le_max_right 3 N).trans hklarge
  have hk2 : 2 ≤ k := by omega
  let w := W3 k
  let m := w - 1
  have hkw : k < w := by simpa [w] using lt_W3 hk2
  have hwpos : 0 < (w : ℝ) := by
    exact_mod_cast (show 0 < w by omega)
  have hmposNat : 0 < m := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  have hNm : N ≤ m := hNk.trans hkm
  have hm_lt : m < W3 k := by dsimp [m, w]; omega
  have hbad : ¬ ForcesW3 m k := not_forcesW3_of_lt_W3 hm_lt
  have hlogm :
      Real.log (m : ℝ) ≤ (2 / c) ^ 9 * (Real.log (k : ℝ)) ^ 9 :=
    log_le_of_roth_estimate hc hk2 hkm hbad (hN m hNm)
  have hwmNat : w ≤ 2 * m := by dsimp [m]; omega
  have hwm : (w : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hwmNat
  have hlogw : Real.log (w : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log hwpos hwm
  have hlogkpos : 0 < (k : ℝ) := by positivity
  have hlogtwo_le : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
  have hlogk_one : 1 ≤ Real.log (k : ℝ) := by
    rw [Real.le_log_iff_exp_le hlogkpos]
    have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    exact Real.exp_one_lt_d9.le.trans <|
      (show (2.7182818286 : ℝ) ≤ (3 : ℝ) by norm_num).trans hk3r
  have hlogk_pow : Real.log (k : ℝ) ≤ (Real.log (k : ℝ)) ^ 9 :=
    le_self_pow₀ hlogk_one (by norm_num)
  have hlogw_final : Real.log (w : ℝ) ≤ C * (Real.log (k : ℝ)) ^ 9 := by
    calc
      Real.log (w : ℝ) ≤ Real.log (2 * (m : ℝ)) := hlogw
      _ = Real.log 2 + Real.log (m : ℝ) := by
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hmposNat.ne')]
      _ ≤ Real.log (k : ℝ) +
          (2 / c) ^ 9 * (Real.log (k : ℝ)) ^ 9 :=
        add_le_add hlogtwo_le hlogm
      _ ≤ (Real.log (k : ℝ)) ^ 9 +
          (2 / c) ^ 9 * (Real.log (k : ℝ)) ^ 9 :=
        by gcongr
      _ = C * (Real.log (k : ℝ)) ^ 9 := by simp [C]; ring
  change (w : ℝ) ≤ Real.exp (C * (Real.log (k : ℝ)) ^ 9)
  rw [← Real.exp_log hwpos]
  exact Real.exp_le_exp.mpr hlogw_final

/-- The subexponential upper bound explicitly requested in Problem 721. -/
def SubexponentialUpperBound : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
    ∀ᶠ k : ℕ in atTop,
      (W3 k : ℝ) < Real.exp ((k : ℝ) ^ γ)

/-- A fixed multiple of a ninth power of a logarithm is eventually smaller
than a square root.  This is the analytic comparison which turns the current
quasipolynomial estimate into the subexponential estimate asked for by
Erdős. -/
lemma eventually_const_mul_log_pow_lt_sqrt_rpow {C : ℝ} (hC : 0 < C) :
    ∀ᶠ k : ℕ in atTop,
      C * (Real.log (k : ℝ)) ^ 9 < (k : ℝ) ^ (1 / 2 : ℝ) := by
  have heps : 0 < (1 / (2 * C) : ℝ) := by positivity
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop (9 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound heps
  filter_upwards [hbound, eventually_ge_atTop 2] with k hkbound hk
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hleft : 0 ≤ (Real.log (k : ℝ)) ^ (9 : ℝ) := Real.rpow_nonneg hlog _
  have hright : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hkbound' :
      (Real.log (k : ℝ)) ^ (9 : ℝ) ≤
        (1 / (2 * C) : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright.le] using hkbound
  have hkboundNat :
      (Real.log (k : ℝ)) ^ (9 : ℕ) ≤
        (1 / (2 * C) : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (Real.log (k : ℝ)) 9]
    exact hkbound'
  calc
    C * (Real.log (k : ℝ)) ^ 9 ≤
        C * ((1 / (2 * C) : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hkboundNat hC.le
    _ = (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by field_simp
    _ < (k : ℝ) ^ (1 / 2 : ℝ) := by nlinarith

/-- The Bloom--Sisask quasipolynomial estimate is stronger than the
subexponential estimate in the question (we may take `γ = 1/2`). -/
theorem subexponentialUpperBound_of_quasipolynomialUpperBound
    (h : QuasipolynomialUpperBound) : SubexponentialUpperBound := by
  obtain ⟨C, hC, hupper⟩ := h
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hupper, eventually_const_mul_log_pow_lt_sqrt_rpow hC] with k hk hdom
  exact hk.trans_lt (Real.exp_lt_exp.mpr hdom)

/-- The exact asymptotic resolution recorded on the Erdős Problems page:
Hunter's lower bound, the current Bloom--Sisask quasipolynomial upper bound,
and the requested subexponential corollary. -/
def Erdos721Resolution : Prop :=
  HunterLowerBound ∧ QuasipolynomialUpperBound ∧ SubexponentialUpperBound

/-- Assembly of the final resolution from the two construction-level source
theorems.  All combinatorial transfers and analytic inversions occur in the
preceding checked lemmas. -/
theorem erdos721Resolution_of_sourceTheorems
    (hHunter : HunterColoringBound)
    (hBloomSisask : CyclicThreeAPSupersaturation) :
    Erdos721Resolution := by
  have hlower : HunterLowerBound :=
    hunterLowerBound_of_hunterColoringBound hHunter
  have hcyclic : CyclicBloomSisaskRothBound :=
    cyclicBloomSisaskRothBound_of_supersaturation hBloomSisask
  have hroth : BloomSisaskRothBound :=
    bloomSisaskRothBound_of_cyclic hcyclic
  have hquasi : QuasipolynomialUpperBound :=
    quasipolynomialUpperBound_of_bloomSisaskRothBound hroth
  exact ⟨hlower, hquasi,
    subexponentialUpperBound_of_quasipolynomialUpperBound hquasi⟩

/-- Unconditional resolution of Erdős Problem 721.  The Hunter source
predicate follows from the finite torus construction formalized above, and
the cyclic Bloom--Sisask endpoint is proved in `CyclicRothEndpoint`. -/
theorem erdos_721 : ((∃ c : ℝ, 0 < c ∧
  ∀ᶠ k : ℕ in Filter.atTop,
    Real.exp (c * (Real.log k) ^ 2 / Real.log (Real.log k)) ≤ (Erdos721.W3 k : ℝ)) ∧ (∃ C : ℝ, 0 < C ∧
  ∀ᶠ k : ℕ in Filter.atTop,
    (Erdos721.W3 k : ℝ) ≤ Real.exp (C * (Real.log k) ^ 9)) ∧ (∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
  ∀ᶠ k : ℕ in Filter.atTop,
    (Erdos721.W3 k : ℝ) < Real.exp ((k : ℝ) ^ γ))) := by
  exact erdos721Resolution_of_sourceTheorems
    (hunterColoringBound_of_hunterLowerBound hunterLowerBound)
    cyclicThreeAPSupersaturation

end Erdos721

alias _root_.Erdos721.erdos721Resolution := _root_.Erdos721.erdos_721
