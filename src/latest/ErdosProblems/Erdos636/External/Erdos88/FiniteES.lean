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
import ErdosProblems.Erdos636.External.Erdos88.Foundations
import Util.Ramsey

/-!
# The finite Erdős--Szemerédi density argument

This file contains the finite graph-combinatorial core of the 1972
Erdős--Szemerédi density theorem.  The proof follows the explicit
neighbourhood-pattern argument recorded in `tex/88.tex`.
-/

open scoped BigOperators
open Filter Finset SimpleGraph

noncomputable section

namespace Erdos88.FiniteES

/-- The edge count, packaged noncomputably so downstream theorem statements
do not carry implementation-level decidability instances. -/
noncomputable def edgeCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- The degree of a vertex, similarly packaged without exposing the
decidability instance for its neighbor set. -/
noncomputable def vertexDegree {α : Type*} [Fintype α]
    (G : SimpleGraph α) (v : α) : ℕ :=
  Nat.card (G.neighborSet v)

lemma vertexDegree_eq_degree {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    vertexDegree G v = G.degree v := by
  rw [vertexDegree, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

/-- A homogeneous set of order `r` means an `r`-clique or an
`r`-vertex independent set. -/
def HasHomogeneousSet (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ¬ (G.CliqueFree r ∧ G.IndepSetFree r)

/-- The target order in the explicit finite Erdős--Szemerédi lemma. -/
noncomputable def esTarget (k n : ℕ) : ℕ :=
  ⌊(k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k)⌋₊

/-- The family of subsets of `L` having at most `s` elements. -/
def smallSubsets (L : Finset α) (s : ℕ) : Finset (Finset α) :=
  L.powerset.filter fun Y ↦ Y.card ≤ s

@[simp] lemma mem_smallSubsets {Y L : Finset α} {s : ℕ} :
    Y ∈ smallSubsets L s ↔ Y ⊆ L ∧ Y.card ≤ s := by
  simp [smallSubsets]

/-- The weighted-powerset estimate used in the neighborhood-pattern
argument.  It is the integral, division-free consequence of
`x^s P ≤ (1+x)^l ≤ exp(s)` with `x=s/l`: if `s ≤ l` and
`16l ≤ ks`, then the number of subsets of an `l`-set of size at most
`s` is at most `k^s`. -/
lemma card_smallSubsets_le_pow {L : Finset α} {s k : ℕ}
    (hspos : 0 < s) (hsl : s ≤ L.card)
    (hscale : 16 * L.card ≤ k * s) :
    ((smallSubsets L s).card : ℝ) ≤ (k : ℝ) ^ s := by
  classical
  let x : ℝ := (s : ℝ) / L.card
  have hlpos : 0 < L.card := hspos.trans_le hsl
  have hxpos : 0 < x := by
    exact div_pos (by exact_mod_cast hspos) (by exact_mod_cast hlpos)
  have hxle : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one (by exact_mod_cast hlpos)]
    exact_mod_cast hsl
  have hweighted :
      ((smallSubsets L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := by
    calc
      ((smallSubsets L s).card : ℝ) * x ^ s =
          ∑ Y ∈ smallSubsets L s, x ^ s := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ Y ∈ smallSubsets L s, x ^ Y.card := by
        apply Finset.sum_le_sum
        intro Y hY
        exact pow_le_pow_of_le_one hxpos.le hxle (mem_smallSubsets.mp hY).2
      _ ≤ ∑ Y ∈ L.powerset, x ^ Y.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro Y hY
          exact Finset.mem_powerset.mpr (mem_smallSubsets.mp hY).1
        · intro Y _hYL _hYsmall
          positivity
      _ = (x + 1) ^ L.card := by
        simpa using Finset.sum_pow_mul_eq_add_pow x 1 L
  have hexp : (x + 1) ^ L.card ≤ Real.exp 1 ^ s := by
    calc
      (x + 1) ^ L.card ≤ Real.exp x ^ L.card := by
        exact pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp x) _
      _ = Real.exp ((L.card : ℝ) * x) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (s : ℝ) := by
        congr 1
        dsimp [x]
        field_simp
      _ = Real.exp 1 ^ s := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hbase : Real.exp 1 ≤ (k : ℝ) * x := by
    have hscaleReal : (16 : ℝ) * L.card ≤ (k : ℝ) * s := by
      exact_mod_cast hscale
    have hsixteen : (16 : ℝ) ≤ (k : ℝ) * x := by
      dsimp [x]
      calc
        (16 : ℝ) ≤ ((k : ℝ) * s) / L.card := by
          apply (le_div_iff₀ (by exact_mod_cast hlpos)).2
          simpa [mul_comm, mul_left_comm] using hscaleReal
        _ = (k : ℝ) * ((s : ℝ) / L.card) := by ring
    exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 16).trans hsixteen)
  have hupper :
      ((smallSubsets L s).card : ℝ) * x ^ s ≤
        (k : ℝ) ^ s * x ^ s := by
    calc
      ((smallSubsets L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := hweighted
      _ ≤ Real.exp 1 ^ s := hexp
      _ ≤ ((k : ℝ) * x) ^ s := pow_le_pow_left₀ (Real.exp_pos 1).le hbase _
      _ = (k : ℝ) ^ s * x ^ s := by rw [mul_pow]
  exact le_of_mul_le_mul_right hupper (pow_pos hxpos s)

/-- The same weighted-powerset estimate bounds the asymmetric Ramsey
number.  The deliberately cross-multiplied hypothesis is the exact fact
needed about the auxiliary parameter `t`. -/
lemma ramseyNumber_le_pow_of_scale {h t k : ℕ}
    (hhpos : 0 < h) (htpos : 0 < t)
    (hscale : 16 * (h + t - 1) ≤ k * t) :
    (Ramsey.ramseyNumber h (t + 1) : ℝ) ≤ (k : ℝ) ^ t := by
  let N := h + t - 1
  have hramsey : Ramsey.ramseyNumber h (t + 1) ≤ Nat.choose N t := by
    have hraw := Ramsey.ramseyNumber_le_choose (h - 1) (t + 1)
    have hfirst : h - 1 + 1 = h := by omega
    have hindex : h - 1 + (t + 1) - 1 = N := by omega
    have hsum : N = (h - 1) + t := by omega
    calc
      Ramsey.ramseyNumber h (t + 1) =
          Ramsey.ramseyNumber (h - 1 + 1) (t + 1) := by rw [hfirst]
      _ ≤ Nat.choose (h - 1 + (t + 1) - 1) (h - 1) := hraw
      _ = Nat.choose N (h - 1) := by rw [hindex]
      _ = Nat.choose N t := by rw [hsum, Nat.choose_symm_add]
  have htN : t ≤ N := by simp [N]; omega
  let L : Finset (Fin N) := Finset.univ
  have hchoose : Nat.choose N t ≤ (smallSubsets L t).card := by
    calc
      Nat.choose N t = (L.powersetCard t).card := by simp [L]
      _ ≤ (smallSubsets L t).card := by
        apply Finset.card_le_card
        intro Y hY
        exact mem_smallSubsets.mpr ⟨(Finset.mem_powersetCard.mp hY).1,
          (Finset.mem_powersetCard.mp hY).2.le⟩
  have hsmall : ((smallSubsets L t).card : ℝ) ≤ (k : ℝ) ^ t := by
    apply card_smallSubsets_le_pow htpos
    · simpa [L] using htN
    · simpa [L, N] using hscale
  exact (by exact_mod_cast hramsey.trans hchoose :
    (Ramsey.ramseyNumber h (t + 1) : ℝ) ≤ (smallSubsets L t).card).trans hsmall

/-- The two binomial estimates in the explicit finite proof, with only the
final comparison of a power of `k` with `n` left as a hypothesis.  This is
the useful purely-natural interface for the later logarithmic calculation. -/
lemma pattern_bound_of_power {n k h : ℕ} (L : Finset (Fin n))
    (hk : 64 ≤ k) (hkh : k < 16 * h)
    (hLh : L.card < h) (hscaleL : k ≤ 16 * L.card)
    (hpower :
      let s := (16 * L.card) ⌈/⌉ k
      let t := (32 * h) ⌈/⌉ k
      8 * k ^ (s + t) ≤ n) :
    let s := (16 * L.card) ⌈/⌉ k
    8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n := by
  have hkpos : 0 < k := by omega
  let s := (16 * L.card) ⌈/⌉ k
  let t := (32 * h) ⌈/⌉ k
  have hLpos : 0 < L.card := by nlinarith
  have hspos : 0 < s := by
    have hsLower : 16 * L.card ≤ k * s := by
      exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
    nlinarith
  have htpos : 0 < t := by
    have htLower : 32 * h ≤ k * t := by
      exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
    have hhpos : 0 < h := by omega
    nlinarith
  have hsUpper : k * s ≤ 32 * L.card := by
    have hdiv := Nat.div_mul_le_self (16 * L.card + k - 1) k
    have hraw : s * k ≤ 16 * L.card + k - 1 := by
      simpa [s, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : s * k ≤ 16 * L.card + k :=
      hraw.trans (Nat.sub_le _ _)
    nlinarith
  have htLower : 32 * h ≤ k * t := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have htUpper : k * t ≤ 64 * h := by
    have hdiv := Nat.div_mul_le_self (32 * h + k - 1) k
    have hraw : t * k ≤ 32 * h + k - 1 := by
      simpa [t, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : t * k ≤ 32 * h + k :=
      hraw.trans (Nat.sub_le _ _)
    nlinarith
  have hst : s ≤ t := by
    nlinarith
  have hsl : s ≤ L.card := by
    nlinarith
  have hsScale : 16 * L.card ≤ k * s := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have hramseyScale : 16 * (h + t - 1) ≤ k * t := by
    have hkt : 32 * t ≤ k * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hsmall := card_smallSubsets_le_pow hspos hsl hsScale
  have hramseyT := ramseyNumber_le_pow_of_scale (by omega) htpos hramseyScale
  have hramseyMono :
      (Ramsey.ramseyNumber h (s + 1) : ℝ) ≤
        Ramsey.ramseyNumber h (t + 1) := by
    have hmonoNat : Ramsey.ramseyNumber h (s + 1) ≤
        Ramsey.ramseyNumber h (t + 1) := by
      apply Ramsey.ramseyNumber_le_of_property
      intro G hbad
      have htprop := Ramsey.ramseyNumber_spec h (t + 1)
      apply htprop G
      refine ⟨hbad.1, ?_⟩
      rw [← SimpleGraph.cliqueFree_compl] at hbad ⊢
      exact hbad.2.mono (Nat.add_le_add_right hst 1)
    exact_mod_cast hmonoNat
  have hproduct :
      (((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) : ℕ) : ℝ) ≤
        (k : ℝ) ^ (s + t) := by
    rw [Nat.cast_mul, pow_add]
    exact mul_le_mul hsmall (hramseyMono.trans hramseyT) (Nat.cast_nonneg _) (by positivity)
  have hpowerReal : (8 : ℝ) * (k : ℝ) ^ (s + t) ≤ n := by
    exact_mod_cast hpower
  have hresultReal :
      (((8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1))) : ℕ) : ℝ) ≤ n := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hproduct (by norm_num)).trans hpowerReal
  exact_mod_cast hresultReal

/-- The logarithmic calculation behind the final power comparison in the
finite Erdős--Szemerédi lemma. -/
lemma eight_mul_pow_le_of_log_scale {n k h r : ℕ}
    (hn : 16 ≤ n) (hk : 64 ≤ k) (hr : k * r ≤ 96 * h)
    (hhlog : (512 : ℝ) * h * Real.log k ≤ (k : ℝ) * Real.log n) :
    8 * k ^ r ≤ n := by
  have hkReal : (0 : ℝ) < k := by positivity
  have hnReal : (0 : ℝ) < n := by positivity
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hrReal : (k : ℝ) * r ≤ 96 * h := by exact_mod_cast hr
  have hscaled :
      ((512 : ℝ) * h * Real.log k) / k ≤ Real.log n := by
    exact (div_le_iff₀ hkReal).2 (by simpa [mul_comm, mul_left_comm] using hhlog)
  have hrlog : (r : ℝ) * Real.log k ≤ (3 / 16 : ℝ) * Real.log n := by
    calc
      (r : ℝ) * Real.log k =
          ((k : ℝ) * r) * (Real.log k / k) := by field_simp
      _ ≤ ((96 : ℝ) * h) * (Real.log k / k) := by
        exact mul_le_mul_of_nonneg_right hrReal (div_nonneg hlogk hkReal.le)
      _ = (3 / 16 : ℝ) * (((512 : ℝ) * h * Real.log k) / k) := by ring
      _ ≤ (3 / 16 : ℝ) * Real.log n := by gcongr
  have hlogEight : Real.log (8 : ℝ) ≤ (3 / 4 : ℝ) * Real.log n := by
    have hlogMono : Real.log (16 : ℝ) ≤ Real.log n := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      calc
        Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
        _ = (3 : ℝ) * Real.log 2 := Real.log_pow 2 3
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      calc
        Real.log (16 : ℝ) = Real.log ((2 : ℝ) ^ 4) := by norm_num
        _ = (4 : ℝ) * Real.log 2 := Real.log_pow 2 4
    rw [h8]
    nlinarith [hlogMono, h16]
  have htotal :
      Real.log ((8 : ℝ) * (k : ℝ) ^ r) ≤ Real.log n := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by positivity)), Real.log_pow]
    nlinarith
  have hreal : (8 : ℝ) * (k : ℝ) ^ r ≤ n :=
    (Real.log_le_log_iff (by positivity) hnReal).mp htotal
  exact_mod_cast hreal

/-- The complete numerical pattern estimate from the logarithmic upper
bound on `h`.  This packages (2.2)--(2.5) of the writeup. -/
lemma pattern_bound_of_log_scale {n k h : ℕ} (L : Finset (Fin n))
    (hn : 16 ≤ n) (hk : 64 ≤ k) (hkh : k < 16 * h)
    (hhlog : (512 : ℝ) * h * Real.log k ≤ (k : ℝ) * Real.log n)
    (hLh : L.card < h) (hscaleL : k ≤ 16 * L.card) :
    let s := (16 * L.card) ⌈/⌉ k
    8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n := by
  apply pattern_bound_of_power L hk hkh hLh hscaleL
  let s := (16 * L.card) ⌈/⌉ k
  let t := (32 * h) ⌈/⌉ k
  have hkpos : 0 < k := by omega
  have hsUpper : k * s ≤ 32 * L.card := by
    have hdiv := Nat.div_mul_le_self (16 * L.card + k - 1) k
    have hraw : s * k ≤ 16 * L.card + k - 1 := by
      simpa [s, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : s * k ≤ 16 * L.card + k := hraw.trans (Nat.sub_le _ _)
    calc
      k * s = s * k := Nat.mul_comm _ _
      _ ≤ 16 * L.card + k := hraw'
      _ ≤ 32 * L.card := by omega
  have htUpper : k * t ≤ 64 * h := by
    have hdiv := Nat.div_mul_le_self (32 * h + k - 1) k
    have hraw : t * k ≤ 32 * h + k - 1 := by
      simpa [t, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    have hraw' : t * k ≤ 32 * h + k := hraw.trans (Nat.sub_le _ _)
    calc
      k * t = t * k := Nat.mul_comm _ _
      _ ≤ 32 * h + k := hraw'
      _ ≤ 64 * h := by omega
  apply eight_mul_pow_le_of_log_scale hn hk
  · rw [mul_add]
    calc
      k * s + k * t ≤ 32 * L.card + 64 * h := Nat.add_le_add hsUpper htUpper
      _ ≤ 96 * h := by omega
  · exact hhlog

/-- The floor defining `esTarget` satisfies exactly the cross-multiplied
logarithmic upper bound used by the finite argument. -/
lemma esTarget_log_scale {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (512 : ℝ) * esTarget k n * Real.log k ≤
      (k : ℝ) * Real.log n := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have hlogbn : 0 ≤ Real.logb 2 (n : ℝ) :=
    div_nonneg hlogn hlogTwo.le
  have hlogbk : 0 < Real.logb 2 (k : ℝ) :=
    div_pos hlogk hlogTwo
  have harg : 0 ≤
      (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) := by positivity
  have hfloor : (esTarget k n : ℝ) ≤
      (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) := by
    exact Nat.floor_le harg
  have hmul : (esTarget k n : ℝ) * (512 * Real.logb 2 k) ≤
      (k : ℝ) * Real.logb 2 n :=
    (le_div_iff₀ (mul_pos (by norm_num) hlogbk)).mp hfloor
  have hquot :
      ((512 : ℝ) * esTarget k n * Real.log k) / Real.log 2 ≤
        ((k : ℝ) * Real.log n) / Real.log 2 := by
    rw [Real.logb, Real.logb] at hmul
    convert hmul using 1 <;> ring
  exact (div_le_div_iff_of_pos_right hlogTwo).mp hquot

/-- For every positive Ramsey constant one can choose the fixed density
parameter `k` so that the coefficient in `esTarget` is at least `2C`.
This is the only parameter-selection use of `log x = o(x)`. -/
lemma exists_density_parameter (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 64 ≤ k ∧
      2 * C ≤ (k : ℝ) / (512 * Real.logb 2 k) := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let K : ℝ := 1024 * C / Real.log 2
  have hK : 0 < K := by dsimp [K]; positivity
  have heps : 0 < K⁻¹ := inv_pos.mpr hK
  have hreal := Real.isLittleO_log_id_atTop.bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨k, hkBound, hk⟩ := (hnat.and (eventually_ge_atTop 64)).exists
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg k), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)] at hkBound
  have hKlog : K * Real.log (k : ℝ) ≤ k := by
    calc
      K * Real.log (k : ℝ) ≤ K * (K⁻¹ * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hkBound hK.le
      _ = (k : ℝ) := by field_simp
  have hkpos : (0 : ℝ) < k := by positivity
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogbk : 0 < Real.logb 2 (k : ℝ) := div_pos hlogk hlogTwo
  refine ⟨k, hk, ?_⟩
  rw [le_div_iff₀ (mul_pos (by norm_num) hlogbk)]
  dsimp [K] at hKlog
  rw [Real.logb]
  calc
    2 * C * (512 * (Real.log k / Real.log 2)) =
        (1024 * C / Real.log 2) * Real.log k := by ring
    _ ≤ k := hKlog

/-- Eventual side conditions for the explicit finite lemma. -/
lemma exists_density_side_conditions (C : ℝ) (hC : 0 < C) :
    ∃ k N : ℕ, 64 ≤ k ∧ ∀ n : ℕ, N ≤ n →
      let h := esTarget k n
      16 ≤ n ∧ k < 16 * h ∧ 8 * h ≤ n ∧
        C * Real.logb 2 n ≤ (h : ℝ) := by
  obtain ⟨k, hk, hcoeff⟩ := exists_density_parameter C hC
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  let a : ℝ := (k : ℝ) / (512 * Real.log k)
  let c : ℝ := C / Real.log 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoeffNat : 2 * c ≤ a := by
    dsimp [a, c]
    rw [Real.logb] at hcoeff
    field_simp at hcoeff ⊢
    nlinarith
  have hlogTendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      max c⁻¹ (((k : ℝ) / 16 + 1) / a) ≤ Real.log n :=
    hlogTendsto.eventually (eventually_ge_atTop _)
  have heps : 0 < (8 * a)⁻¹ := by positivity
  have hsmallReal := Real.isLittleO_log_id_atTop.bound heps
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have heventually : ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧
      let h := esTarget k n
      k < 16 * h ∧ 8 * h ≤ n ∧ C * Real.logb 2 n ≤ (h : ℝ) := by
    filter_upwards [eventually_ge_atTop 16, hlarge, hsmallNat] with n hn hnlarge hnsmall
    have hnpos : (0 : ℝ) < n := by positivity
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hlogn, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n)] at hnsmall
    have hsmall : 8 * a * Real.log (n : ℝ) ≤ n := by
      calc
        8 * a * Real.log (n : ℝ) ≤
            8 * a * ((8 * a)⁻¹ * (n : ℝ)) := by gcongr
        _ = (n : ℝ) := by field_simp
    have hcLarge : 1 ≤ c * Real.log (n : ℝ) := by
      have := le_trans (le_max_left c⁻¹ (((k : ℝ) / 16 + 1) / a)) hnlarge
      calc
        (1 : ℝ) = c * c⁻¹ := by field_simp
        _ ≤ c * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left this hc.le
    have haLarge : (k : ℝ) / 16 + 1 ≤ a * Real.log (n : ℝ) := by
      have := le_trans (le_max_right c⁻¹ (((k : ℝ) / 16 + 1) / a)) hnlarge
      calc
        (k : ℝ) / 16 + 1 = a * (((k : ℝ) / 16 + 1) / a) := by field_simp
        _ ≤ a * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left this ha.le
    have hargEq :
        (k : ℝ) * Real.logb 2 n / (512 * Real.logb 2 k) =
          a * Real.log n := by
      dsimp [a]
      rw [Real.logb, Real.logb]
      field_simp
    have hargNonneg : 0 ≤ a * Real.log (n : ℝ) := mul_nonneg ha.le hlogn
    let h := esTarget k n
    have hfloorUpper : (h : ℝ) ≤ a * Real.log (n : ℝ) := by
      dsimp [h, esTarget]
      rw [hargEq]
      exact Nat.floor_le hargNonneg
    have hfloorLower : a * Real.log (n : ℝ) < (h : ℝ) + 1 := by
      dsimp [h, esTarget]
      rw [hargEq]
      exact Nat.lt_floor_add_one _
    have hthreshold : C * Real.logb 2 n ≤ (h : ℝ) := by
      have hx : C * Real.logb 2 n = c * Real.log n := by
        dsimp [c]
        rw [Real.logb]
        ring
      rw [hx]
      have htwice : 2 * (c * Real.log (n : ℝ)) ≤
          a * Real.log (n : ℝ) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeffNat hlogn
      nlinarith
    have hkh : k < 16 * h := by
      exact_mod_cast (show (k : ℝ) < 16 * h by nlinarith)
    have hhn : 8 * h ≤ n := by
      exact_mod_cast (show (8 : ℝ) * h ≤ n by nlinarith)
    exact ⟨hn, hkh, hhn, hthreshold⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  refine ⟨k, N, hk, ?_⟩
  intro n hn
  exact hN n hn

/-- Vertices whose degree is strictly below `4n/k`, written without
division so that all subsequent double counting is over natural numbers. -/
noncomputable def lowDegreeSet {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v ↦ k * vertexDegree G v < 4 * n

@[simp] lemma mem_lowDegreeSet {n k : ℕ} {G : SimpleGraph (Fin n)}
    {v : Fin n} :
    v ∈ lowDegreeSet G k ↔ k * vertexDegree G v < 4 * n := by
  classical
  simp [lowDegreeSet]

/-- More than half the vertices have degree below `4n/k` when
`e(G) < n²/k`.  Both inequalities are cross-multiplied over `ℕ`. -/
lemma card_lowDegreeSet_gt_half {n k : ℕ} (G : SimpleGraph (Fin n))
    (hedges : k * edgeCount G < n ^ 2) :
    n < 2 * (lowDegreeSet G k).card := by
  classical
  let D := lowDegreeSet G k
  let E := Finset.univ \ D
  have hDE : D.card + E.card = n := by
    change D.card + (Finset.univ \ D).card = n
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    have hDn : D.card ≤ n := by
      simpa [D] using Finset.card_le_card (Finset.subset_univ D)
    rw [show (Finset.univ : Finset (Fin n)).card = n by simp]
    exact Nat.add_sub_of_le hDn
  have hdeg : ∀ v ∈ E, 4 * n ≤ k * vertexDegree G v := by
    intro v hv
    have hv' : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hv'' : ¬ k * vertexDegree G v < 4 * n := by
      intro h
      exact hv' (by simpa [D, lowDegreeSet] using h)
    exact Nat.le_of_not_gt hv''
  have hsumLower : E.card * (4 * n) ≤ ∑ v ∈ E, k * vertexDegree G v := by
    simpa [Finset.sum_const_nat] using Finset.sum_le_sum hdeg
  have hsumSubset : (∑ v ∈ E, vertexDegree G v) ≤ ∑ v, vertexDegree G v := by
    exact Finset.sum_le_sum_of_subset (by simp [E])
  have hhandshake : ∑ v, vertexDegree G v = 2 * edgeCount G := by
    calc
      ∑ v, vertexDegree G v = ∑ v, G.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact vertexDegree_eq_degree G v
      _ = 2 * edgeCount G := by
        simpa [edgeCount] using G.sum_degrees_eq_twice_card_edges
  by_contra hhalf
  change ¬ n < 2 * D.card at hhalf
  have hcard : n ≤ 2 * E.card := by omega
  have hquad : 2 * n ^ 2 ≤ E.card * (4 * n) := by nlinarith
  have hupper : (∑ v ∈ E, k * vertexDegree G v) ≤ k * (2 * edgeCount G) := by
    rw [← Finset.mul_sum, ← hhandshake]
    exact Nat.mul_le_mul_left k hsumSubset
  have hle : 2 * n ^ 2 ≤ k * (2 * edgeCount G) :=
    hquad.trans (hsumLower.trans hupper)
  have hlt : k * (2 * edgeCount G) < 2 * n ^ 2 := by
    calc
      k * (2 * edgeCount G) = 2 * (k * edgeCount G) := by ring
      _ < 2 * n ^ 2 := Nat.mul_lt_mul_of_pos_left hedges (by omega)
  omega

/-- Every neighborhood trace on `L` is a subset of `L`. -/
lemma neighborTrace_subset [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (L : Finset α) :
    G.neighborFinset v ∩ L ⊆ L :=
  inter_subset_right

/-- If all neighborhood traces have size at most `s`, their image is
contained in `smallSubsets L s`. -/
lemma neighborTrace_mem_smallSubsets [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {B L : Finset α} {s : ℕ}
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s) :
    ∀ v ∈ B, G.neighborFinset v ∩ L ∈ smallSubsets L s := by
  intro v hv
  exact mem_smallSubsets.mpr ⟨inter_subset_right, hsmall v hv⟩

/-- Pigeonholing bounded neighborhood traces. -/
theorem exists_uniform_neighborTrace
    {n s q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {B L : Finset (Fin n)}
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s)
    (hmul : (smallSubsets L s).card * q < B.card) :
    ∃ Y Z : Finset (Fin n),
      Y ∈ smallSubsets L s ∧ Z ⊆ B ∧ q < Z.card ∧
        ∀ z ∈ Z, G.neighborFinset z ∩ L = Y := by
  classical
  obtain ⟨Y, hY, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := B) (t := smallSubsets L s)
      (f := fun v ↦ G.neighborFinset v ∩ L)
      (neighborTrace_mem_smallSubsets G hsmall) hmul
  let Z := B.filter fun v ↦ G.neighborFinset v ∩ L = Y
  refine ⟨Y, Z, hY, ?_, ?_, ?_⟩
  · exact filter_subset _ _
  · simpa [Z] using hfiber
  · intro z hz
    exact (mem_filter.mp hz).2

/-- Off-diagonal Ramsey numbers are monotone in the independent-set
parameter. -/
lemma ramseyNumber_mono_right {r p s : ℕ} (hps : p ≤ s) :
    Ramsey.ramseyNumber r p ≤ Ramsey.ramseyNumber r s := by
  apply Ramsey.ramseyNumber_le_of_property
  intro G hbad
  have hsprop := Ramsey.ramseyNumber_spec r s
  apply hsprop G
  refine ⟨hbad.1, ?_⟩
  rw [← SimpleGraph.cliqueFree_compl] at hbad ⊢
  exact hbad.2.mono hps

/-- Every finite vertex set has an independent subset of maximum
cardinality (maximum only among subsets of the given set). -/
theorem exists_maximum_independent_subset
    {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) :
    ∃ L : Finset (Fin n),
      L ⊆ D ∧ G.IsIndepSet L ∧
        ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card := by
  classical
  let A : Finset (Finset (Fin n)) :=
    D.powerset.filter fun I : Finset (Fin n) ↦ G.IsIndepSet (I : Set (Fin n))
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [A, SimpleGraph.isIndepSet_iff]
  let cards := A.image fun I ↦ I.card
  have hcards : cards.Nonempty := hA.image _
  let m := cards.max' hcards
  have hm : m ∈ cards := Finset.max'_mem cards hcards
  obtain ⟨L, hLA, hLm⟩ := Finset.mem_image.mp hm
  have hL := Finset.mem_filter.mp hLA
  refine ⟨L, Finset.mem_powerset.mp hL.1, hL.2, ?_⟩
  intro I hID hI
  have hIA : I ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hID, hI⟩
  have hIcard : I.card ∈ cards := Finset.mem_image.mpr ⟨I, hIA, rfl⟩
  rw [hLm]
  exact Finset.le_max' cards I.card hIcard

/-- Maximality consequence: every vertex of `D \ L` has a neighbor in a
maximum independent subset `L`. -/
lemma exists_neighbor_in_maximum_independent_subset
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    {v : Fin n} (hv : v ∈ D \ L) :
    ∃ x ∈ L, G.Adj x v := by
  classical
  by_contra hnone
  push_neg at hnone
  have hvD : v ∈ D := (Finset.mem_sdiff.mp hv).1
  have hvL : v ∉ L := (Finset.mem_sdiff.mp hv).2
  have hindep : G.IsIndepSet (↑(insert v L) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply Set.Pairwise.insert hL
    intro x hx _hvx
    have hnxv := hnone x (by simpa using hx)
    exact ⟨by simpa [G.adj_comm] using hnxv, hnxv⟩
  have hsub : insert v L ⊆ D := insert_subset hvD hLD
  have hle := hmax (insert v L) hsub (by
    show G.IsIndepSet (↑(insert v L) : Set (Fin n))
    exact hindep)
  rw [card_insert_of_notMem hvL] at hle
  omega

/-- The vertices outside a maximum independent subset are covered by the
neighborhoods of its vertices. -/
lemma card_sdiff_le_sum_vertexDegree
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card) :
    (D \ L).card ≤ ∑ x ∈ L, vertexDegree G x := by
  have hcover : D \ L ⊆ L.biUnion fun x ↦ G.neighborFinset x := by
    intro v hv
    obtain ⟨x, hxL, hxv⟩ :=
      exists_neighbor_in_maximum_independent_subset hLD hL hmax hv
    exact Finset.mem_biUnion.mpr ⟨x, hxL, by simpa using hxv⟩
  calc
    (D \ L).card ≤ (L.biUnion fun x ↦ G.neighborFinset x).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ L, (G.neighborFinset x).card := Finset.card_biUnion_le
    _ = ∑ x ∈ L, vertexDegree G x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [G.card_neighborFinset_eq_degree, ← vertexDegree_eq_degree]

/-- Double-counting the adjacencies between two finite vertex sets. -/
lemma sum_card_neighborFinset_inter_comm
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) :
    (∑ a ∈ A, #(G.neighborFinset a ∩ B)) =
      ∑ b ∈ B, #(G.neighborFinset b ∩ A) := by
  classical
  calc
    (∑ a ∈ A, #(G.neighborFinset a ∩ B)) =
        ∑ a ∈ A, #(B.bipartiteAbove G.Adj a) := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 1
          ext b
          simp [and_comm, G.adj_comm]
    _ = ∑ b ∈ B, #(A.bipartiteBelow G.Adj b) :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
    _ = ∑ b ∈ B, #(G.neighborFinset b ∩ A) := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext a
      simp [and_comm, G.adj_comm]

/-- Vertices outside `L` whose trace on `L` has at least `s` elements. -/
def highTraceSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D L : Finset (Fin n)) (s : ℕ) : Finset (Fin n) := by
  exact (D \ L).filter fun v ↦ s ≤ #(G.neighborFinset v ∩ L)

@[simp] lemma mem_highTraceSet
    {n s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} {v : Fin n} :
    v ∈ highTraceSet G D L s ↔
      v ∈ D \ L ∧ s ≤ #(G.neighborFinset v ∩ L) := by
  simp only [highTraceSet, Finset.mem_filter]

/-- The high-trace set has fewer than `n/4` vertices.  This is the second
double-counting step in the finite Erdős--Szemerédi proof. -/
lemma four_mul_card_highTraceSet_lt
    {n k s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)}
    (hD : D = lowDegreeSet G k) (hLD : L ⊆ D) (hLpos : 0 < L.card)
    (hscale : 16 * L.card ≤ k * s) :
    4 * (highTraceSet G D L s).card < n := by
  let T := highTraceSet G D L s
  have hTDL : T ⊆ D \ L := by
    intro v hv
    exact ((mem_highTraceSet (G := G)).mp hv).1
  have hlower : T.card * s ≤ ∑ v ∈ T, #(G.neighborFinset v ∩ L) := by
    have hconst : (∑ _v ∈ T, s) = T.card * s := by simp
    rw [← hconst]
    apply Finset.sum_le_sum
    intro v hv
    exact ((mem_highTraceSet (G := G) (D := D) (L := L) (s := s)).mp hv).2
  have hsumMono :
      (∑ v ∈ T, #(G.neighborFinset v ∩ L)) ≤
        ∑ v ∈ D \ L, #(G.neighborFinset v ∩ L) :=
    Finset.sum_le_sum_of_subset hTDL
  have hdouble :
      (∑ v ∈ D \ L, #(G.neighborFinset v ∩ L)) =
        ∑ x ∈ L, #(G.neighborFinset x ∩ (D \ L)) :=
    sum_card_neighborFinset_inter_comm G (D \ L) L
  have htoDegree :
      (∑ x ∈ L, #(G.neighborFinset x ∩ (D \ L))) ≤
        ∑ x ∈ L, vertexDegree G x := by
    apply Finset.sum_le_sum
    intro x hx
    calc
      #(G.neighborFinset x ∩ (D \ L)) ≤ #(G.neighborFinset x) :=
        Finset.card_le_card Finset.inter_subset_left
      _ = vertexDegree G x := by
        rw [G.card_neighborFinset_eq_degree, vertexDegree_eq_degree]
  have hincidence : T.card * s ≤ ∑ x ∈ L, vertexDegree G x := by
    exact hlower.trans (hsumMono.trans (hdouble.le.trans htoDegree))
  have hdegreeSmall :
      k * (∑ x ∈ L, vertexDegree G x) < L.card * (4 * n) := by
    rw [Finset.mul_sum]
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hLpos)
      (fun x hx ↦ (mem_lowDegreeSet.mp (by rw [← hD]; exact hLD hx)))
    simpa [Finset.sum_const_nat] using hlt
  by_contra hbad
  change ¬4 * T.card < n at hbad
  have hquarter : n ≤ 4 * T.card := Nat.le_of_not_gt hbad
  nlinarith

/-- The residual low-trace class after removing `L` and the high-trace
vertices. -/
def residualSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D L : Finset (Fin n)) (s : ℕ) : Finset (Fin n) :=
  (D \ L) \ highTraceSet G D L s

@[simp] lemma mem_residualSet
    {n s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)} {v : Fin n} :
    v ∈ residualSet G D L s ↔
      v ∈ D \ L ∧ #(G.neighborFinset v ∩ L) < s := by
  simp only [residualSet, Finset.mem_sdiff, mem_highTraceSet]
  constructor
  · rintro ⟨hvDL, hvT⟩
    exact ⟨hvDL, Nat.lt_of_not_ge (fun hs ↦ hvT ⟨hvDL, hs⟩)⟩
  · rintro ⟨hvDL, hsmall⟩
    exact ⟨hvDL, fun hvT ↦ (Nat.not_le_of_lt hsmall) hvT.2⟩

/-- Under the three cardinal estimates in the finite proof, the residual
set has more than `n/8` vertices. -/
lemma card_residualSet_gt_eighth
    {n h s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)}
    (hLD : L ⊆ D) (hDhalf : n < 2 * D.card)
    (hLh : L.card < h) (hhn : 8 * h ≤ n)
    (hT : 4 * (highTraceSet G D L s).card < n) :
    n < 8 * (residualSet G D L s).card := by
  classical
  have hTsub : highTraceSet G D L s ⊆ D \ L := by
    intro v hv
    exact (mem_highTraceSet.mp hv).1
  have hDsplit : L.card + (D \ L).card = D.card := by
    rw [Finset.card_sdiff_of_subset hLD]
    omega
  have hBsplit :
      (highTraceSet G D L s).card + (residualSet G D L s).card =
        (D \ L).card := by
    rw [residualSet, Finset.card_sdiff_of_subset hTsub]
    omega
  omega

/-- The first numerical consequence in the finite proof: a maximum
independent subset of the low-degree set has size at least `k/16`, in the
cross-multiplied form `k ≤ 16 * |L|`. -/
lemma sixteen_mul_card_maximum_independent_ge
    {n k h : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L : Finset (Fin n)}
    (hD : D = lowDegreeSet G k) (hk : 64 ≤ k)
    (hkh : k < 16 * h) (hhn : 8 * h ≤ n)
    (hDhalf : n < 2 * D.card)
    (hLD : L ⊆ D) (hL : G.IsIndepSet L)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hLh : L.card < h) :
    k ≤ 16 * L.card := by
  classical
  have hnpos : 0 < n := by omega
  have hDnonempty : D.Nonempty := by rw [← card_pos]; omega
  obtain ⟨v, hvD⟩ := hDnonempty
  have hsingleton : G.IsIndepSet ({v} : Finset (Fin n)) := by
    simp [SimpleGraph.isIndepSet_iff]
  have hLpos : 0 < L.card := by
    have := hmax {v} (by simpa using hvD) hsingleton
    simpa using this
  have hdiff := card_sdiff_le_sum_vertexDegree hLD hL hmax
  have hLDcard : L.card ≤ D.card := Finset.card_le_card hLD
  have hDsplit : L.card + (D \ L).card = D.card := by
    rw [Finset.card_sdiff_of_subset hLD]
    omega
  have hdiffLarge : n < 4 * (D \ L).card := by omega
  have hsumSmall :
      k * (∑ x ∈ L, vertexDegree G x) < L.card * (4 * n) := by
    rw [Finset.mul_sum]
    have := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hLpos)
      (fun x hx ↦ (mem_lowDegreeSet.mp (by rw [← hD]; exact hLD hx)))
    simpa [Finset.sum_const_nat] using this
  by_contra hbad
  have hbad' : 16 * L.card < k := Nat.lt_of_not_ge hbad
  nlinarith

/-- Ramsey's theorem applied to an induced graph.  If `B` has at least
`R(r,q)` vertices, then `B` contains an `r`-clique or a `q`-independent set
of the ambient graph. -/
theorem clique_or_independent_subset_of_ramseyNumber_le
    {n r q : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (hcard : Ramsey.ramseyNumber r q ≤ B.card) :
    (∃ K : Finset (Fin n), K ⊆ B ∧ G.IsNClique r K) ∨
      (∃ I : Finset (Fin n), I ⊆ B ∧ G.IsNIndepSet q I) := by
  classical
  let H : SimpleGraph (B : Set (Fin n)) := G.induce (B : Set (Fin n))
  have hprop : Ramsey.RamseyProperty r q B.card :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hcard
  have hnot : ¬ (H.CliqueFree r ∧ H.IndepSetFree q) :=
    Ramsey.ramseyProperty_of_card (by simp) hprop H
  simp only [not_and_or] at hnot
  rcases hnot with hclique | hindep
  · left
    simp only [SimpleGraph.CliqueFree, not_forall] at hclique
    obtain ⟨K, hK⟩ := hclique
    have hK' : H.IsNClique r K := by simpa using hK
    let K' : Finset (Fin n) := K.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨K', ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hK'.isClique hx' hy' (by simpa using hxy)
      · simpa [K'] using hK'.card_eq
  · right
    simp only [SimpleGraph.IndepSetFree, not_forall] at hindep
    obtain ⟨I, hI⟩ := hindep
    have hI' : H.IsNIndepSet q I := by simpa using hI
    let I' : Finset (Fin n) := I.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨I', ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hI'.isIndepSet hx' hy' (by simpa using hxy)
      · simpa [I'] using hI'.card_eq

/-- The Ramsey endpoint of the finite Erdős--Szemerédi argument.

If every independent set in `Z` has at most `p` vertices and `Z` has at
least `R(h,p+1)` vertices, then a graph with no `h`-clique is impossible. -/
theorem not_cliqueFree_of_large_set_indep_card_le
    {n h p : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
    (hZ : Ramsey.ramseyNumber h (p + 1) ≤ Z.card)
    (hindep : ∀ I : Finset (Fin n), I ⊆ Z → G.IsIndepSet I → I.card ≤ p) :
    ¬ G.CliqueFree h := by
  intro hfree
  rcases clique_or_independent_subset_of_ramseyNumber_le G Z hZ with hK | hI
  · obtain ⟨K, -, hKr⟩ := hK
    exact hfree K hKr
  · obtain ⟨I, hIZ, hIr⟩ := hI
    have := hindep I hIZ hIr.isIndepSet
    rw [hIr.card_eq] at this
    omega

/-- Uniform neighborhood traces turn an independent set in `Z` into a
larger independent set by replacing its common neighborhood in `L`.
This is the key exchange step in the finite Erdős--Szemerédi proof. -/
lemma card_indep_le_of_uniform_trace
    {n : ℕ} {G : SimpleGraph (Fin n)} {D L Y Z : Finset (Fin n)}
    [DecidableRel G.Adj]
    (hL : G.IsIndepSet L) (hLD : L ⊆ D) (hYL : Y ⊆ L)
    (hZD : Z ⊆ D)
    (hZL : Disjoint Z L)
    (htrace : ∀ z ∈ Z, G.neighborFinset z ∩ L = Y)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    {I : Finset (Fin n)} (hIZ : I ⊆ Z) (hI : G.IsIndepSet I) :
    I.card ≤ Y.card := by
  classical
  let J := (L \ Y) ∪ I
  have hdisj : Disjoint (L \ Y) I := by
    exact (Finset.disjoint_of_subset_left sdiff_subset
      (Finset.disjoint_of_subset_right hIZ hZL.symm))
  have hJ : G.IsIndepSet J := by
    intro x hx y hy hxy
    change x ∈ (L \ Y) ∪ I at hx
    change y ∈ (L \ Y) ∪ I at hy
    rw [mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hL (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
    · have hxL : x ∈ L := (Finset.mem_sdiff.mp hx).1
      have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
      have hyZ : y ∈ Z := hIZ hy
      intro hadj
      have hxyN : x ∈ G.neighborFinset y := by
        simpa [G.adj_comm] using hadj
      apply hxY
      rw [← htrace y hyZ]
      exact mem_inter.mpr ⟨hxyN, hxL⟩
    · have hyL : y ∈ L := (Finset.mem_sdiff.mp hy).1
      have hyY : y ∉ Y := (Finset.mem_sdiff.mp hy).2
      have hxZ : x ∈ Z := hIZ hx
      intro hadj
      have hxyN : y ∈ G.neighborFinset x := by simpa using hadj
      apply hyY
      rw [← htrace x hxZ]
      exact mem_inter.mpr ⟨hxyN, hyL⟩
    · exact hI hx hy hxy
  have hJD : J ⊆ D := union_subset (sdiff_subset.trans hLD) (hIZ.trans hZD)
  have hcardJ := hmax J hJD hJ
  have hYLcard : Y.card ≤ L.card := card_le_card hYL
  change ((L \ Y) ∪ I).card ≤ L.card at hcardJ
  rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hYL] at hcardJ
  omega

/-- A uniform neighborhood-trace class of Ramsey size forces an `h`-clique,
provided `L` is a maximum independent set and the class is disjoint from
`L`. -/
theorem not_cliqueFree_of_uniform_trace
    {n h p : ℕ} {G : SimpleGraph (Fin n)} {D L Y Z : Finset (Fin n)}
    [DecidableRel G.Adj]
    (hL : G.IsIndepSet L) (hLD : L ⊆ D) (hYL : Y ⊆ L) (hp : Y.card = p)
    (hZD : Z ⊆ D)
    (hZL : Disjoint Z L)
    (htrace : ∀ z ∈ Z, G.neighborFinset z ∩ L = Y)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hlarge : Ramsey.ramseyNumber h (p + 1) ≤ Z.card) :
    ¬ G.CliqueFree h := by
  apply not_cliqueFree_of_large_set_indep_card_le hlarge
  intro I hIZ hI
  simpa [hp] using
    card_indep_le_of_uniform_trace hL hLD hYL hZD hZL htrace hmax hIZ hI

/-- The complete neighborhood-pattern core of the finite
Erdős--Szemerédi lemma.  The remaining hypotheses in the explicit theorem
are purely numerical estimates ensuring `hmul`. -/
theorem finiteES_pattern_core
    {n h s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D L B : Finset (Fin n)}
    (hL : G.IsIndepSet L) (hLD : L ⊆ D)
    (hmax : ∀ I : Finset (Fin n), I ⊆ D → G.IsIndepSet I → I.card ≤ L.card)
    (hBD : B ⊆ D) (hBL : Disjoint B L)
    (hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s)
    (hmul : (smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) < B.card) :
    ¬ G.CliqueFree h := by
  classical
  obtain ⟨Y, Z, hY, hZB, hZlarge, htrace⟩ :=
    exists_uniform_neighborTrace G hsmall hmul
  have hYL : Y ⊆ L := (mem_smallSubsets.mp hY).1
  have hYs : Y.card ≤ s := (mem_smallSubsets.mp hY).2
  have hramsey : Ramsey.ramseyNumber h (Y.card + 1) ≤ Z.card := by
    exact (ramseyNumber_mono_right (Nat.add_le_add_right hYs 1)).trans hZlarge.le
  exact not_cliqueFree_of_uniform_trace hL hLD hYL rfl
    (hZB.trans hBD) (hBL.mono_left hZB) htrace hmax hramsey

/-- The explicit finite Erdős--Szemerédi argument with its final binomial
and Ramsey estimates isolated as a single, purely numerical hypothesis.

The hypothesis `hpattern` is exactly the estimate proved in (2.2)--(2.5)
of `tex/88.tex`; all graph-theoretic and double-counting steps are proved
here. -/
theorem finite_erdos_szemeredi_of_pattern_bound
    {n k h : ℕ} (G : SimpleGraph (Fin n))
    (hk : 64 ≤ k) (hkh : k < 16 * h) (hhn : 8 * h ≤ n)
    (hedges : k * edgeCount G < n ^ 2)
    (hpattern : ∀ L : Finset (Fin n), L.card < h → k ≤ 16 * L.card →
      let s := (16 * L.card) ⌈/⌉ k
      8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n) :
    HasHomogeneousSet G h := by
  classical
  intro hfree
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let D := lowDegreeSet G k
  have hDhalf : n < 2 * D.card := card_lowDegreeSet_gt_half G hedges
  obtain ⟨L, hLD, hL, hmax⟩ := exists_maximum_independent_subset G D
  have hLh : L.card < h := by
    by_contra hnot
    have hhL : h ≤ L.card := Nat.le_of_not_gt hnot
    obtain ⟨I, hIL, hIcard⟩ := Finset.exists_subset_card_eq hhL
    exact hfree.2 I ⟨hL.mono (by exact_mod_cast hIL), hIcard⟩
  have hscaleL : k ≤ 16 * L.card :=
    sixteen_mul_card_maximum_independent_ge rfl hk hkh hhn hDhalf
      hLD hL hmax hLh
  let s := (16 * L.card) ⌈/⌉ k
  have hkpos : 0 < k := by omega
  have hscaleS : 16 * L.card ≤ k * s := by
    exact (ceilDiv_le_iff_le_mul hkpos).mp le_rfl
  have hLpos : 0 < L.card := by nlinarith
  have hT : 4 * (highTraceSet G D L s).card < n :=
    four_mul_card_highTraceSet_lt rfl hLD hLpos hscaleS
  let B := residualSet G D L s
  have hBlarge : n < 8 * B.card :=
    card_residualSet_gt_eighth hLD hDhalf hLh hhn hT
  have hBD : B ⊆ D := by
    intro v hv
    exact (Finset.mem_sdiff.mp (mem_residualSet.mp hv).1).1
  have hBL : Disjoint B L := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvL
    exact (Finset.mem_sdiff.mp (mem_residualSet.mp hvB).1).2 hvL
  have hsmall : ∀ v ∈ B, #(G.neighborFinset v ∩ L) ≤ s := by
    intro v hv
    exact (mem_residualSet.mp hv).2.le
  have hnumeric := hpattern L hLh hscaleL
  change 8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n at hnumeric
  have hmul :
      (smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1) < B.card := by
    nlinarith
  exact finiteES_pattern_core hL hLD hmax hBD hBL hsmall hmul hfree.1

/-- Explicit finite Erdős--Szemerédi lemma, with the constants and floor
exactly as in `tex/88.tex`. -/
theorem finite_erdos_szemeredi {n k : ℕ} (G : SimpleGraph (Fin n))
    (hn : 16 ≤ n) (hk : 64 ≤ k) :
    let h := esTarget k n
    k < 16 * h → 8 * h ≤ n → k * edgeCount G < n ^ 2 →
      HasHomogeneousSet G h := by
  dsimp only
  intro hkh hhn hedges
  apply finite_erdos_szemeredi_of_pattern_bound G hk hkh hhn hedges
  intro L hLh hscaleL
  exact pattern_bound_of_log_scale L hn hk hkh
    (esTarget_log_scale (by omega) (by omega)) hLh hscaleL

/-- The remaining purely numerical certificate needed to turn the explicit
finite lemma into the eventual Erdős--Szemerédi density theorem. -/
def DensityCertificate (C : ℝ) : Prop :=
  ∃ k N : ℕ, 64 ≤ k ∧ ∀ n : ℕ, N ≤ n →
    let h := esTarget k n
    k < 16 * h ∧ 8 * h ≤ n ∧ C * Real.logb 2 n ≤ (h : ℝ) ∧
      ∀ L : Finset (Fin n), L.card < h → k ≤ 16 * L.card →
        let s := (16 * L.card) ⌈/⌉ k
        8 * ((smallSubsets L s).card * Ramsey.ramseyNumber h (s + 1)) ≤ n

/-- A Ramsey-free graph is both clique-free and independent-set-free at
every integer order at least its real homogeneous-set threshold. -/
lemma cliqueFree_and_indepSetFree_of_ramseyFree
    {n h : ℕ} {C : ℝ} {G : SimpleGraph (Fin n)}
    (hG : RamseyFree C G) (hthreshold : C * Real.logb 2 n ≤ (h : ℝ)) :
    G.CliqueFree h ∧ G.IndepSetFree h := by
  constructor
  · intro S hS
    have hlt := hG S (Or.inl hS.isClique)
    rw [hS.card_eq] at hlt
    exact (not_lt_of_ge hthreshold) hlt
  · intro S hS
    have hlt := hG S (Or.inr hS.isIndepSet)
    rw [hS.card_eq] at hlt
    exact (not_lt_of_ge hthreshold) hlt

/-- The eventual quadratic edge-density consequence of any proved
`DensityCertificate`.  The separate numerical theorem below is the only
ingredient needed to remove the certificate hypothesis. -/
theorem ramseyFree_edgeCount_density_lower_of_certificate
    (C : ℝ) (hC : 0 < C) (hcert : DensityCertificate C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        a * (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) := by
  obtain ⟨k, N, hk, hcert⟩ := hcert
  have hkpos : 0 < k := by omega
  refine ⟨(k : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hkpos), N, ?_⟩
  intro n hn G hG
  obtain ⟨hkh, hhn, hthreshold, hpattern⟩ := hcert n hn
  let h := esTarget k n
  have hfree : G.CliqueFree h ∧ G.IndepSetFree h :=
    cliqueFree_and_indepSetFree_of_ramseyFree hG hthreshold
  have hedgesNat : n ^ 2 ≤ k * edgeCount G := by
    by_contra hnot
    have hsparse : k * edgeCount G < n ^ 2 := Nat.lt_of_not_ge hnot
    exact (finite_erdos_szemeredi_of_pattern_bound G hk hkh hhn hsparse hpattern) hfree
  have hedgesReal : (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) * k := by
    exact_mod_cast (show n ^ 2 ≤ edgeCount G * k by simpa [mul_comm] using hedgesNat)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (by exact_mod_cast hkpos)).2 (by simpa [mul_comm] using hedgesReal)

/-- Erdős--Szemerédi: an exact `C`-Ramsey graph has eventual positive
constant edge density. -/
theorem ramseyFree_edgeCount_density_lower (C : ℝ) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        a * (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) := by
  obtain ⟨k, N, hk, hside⟩ := exists_density_side_conditions C hC
  have hkpos : 0 < k := by omega
  refine ⟨(k : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hkpos), N, ?_⟩
  intro n hn G hG
  obtain ⟨hn16, hkh, hhn, hthreshold⟩ := hside n hn
  let h := esTarget k n
  have hfree : G.CliqueFree h ∧ G.IndepSetFree h :=
    cliqueFree_and_indepSetFree_of_ramseyFree hG hthreshold
  have hedgesNat : n ^ 2 ≤ k * edgeCount G := by
    by_contra hnot
    have hsparse : k * edgeCount G < n ^ 2 := Nat.lt_of_not_ge hnot
    exact (finite_erdos_szemeredi G hn16 hk hkh hhn hsparse) hfree
  have hedgesReal : (n : ℝ) ^ 2 ≤ (edgeCount G : ℝ) * k := by
    exact_mod_cast (show n ^ 2 ≤ edgeCount G * k by simpa [mul_comm] using hedgesNat)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (by exact_mod_cast hkpos)).2 (by simpa [mul_comm] using hedgesReal)

end Erdos88.FiniteES
