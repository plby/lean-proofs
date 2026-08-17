/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.Lenz
import ErdosProblems.Erdos223.Obstruction
import ErdosProblems.Erdos223.Turan

/-!
# The asymptotic part of Erdős Problem 223

For `d ≥ 4`, put `p = ⌊d / 2⌋`.  The Lenz construction contains the
balanced `p`-partite Turán graph, while the geometric obstruction excludes a
balanced complete `(p + 1)`-partite graph with three vertices per part.
Erdős–Stone therefore squeezes the normalized number of diameter pairs to
`(p - 1) / (2p)`.
-/

open Filter Metric
open scoped SimpleGraph

namespace Erdos223

/-- The Turán density coefficient occurring in dimension `d`. -/
noncomputable def asymptoticCoefficient (d : ℕ) : ℝ :=
  (((d / 2 : ℕ) : ℝ) - 1) / (2 * (d / 2 : ℕ))

/-- A crude lower estimate for the balanced Turán graph.  Its error is a
constant depending only on the number of parts, which is all that is needed
for the normalized limit. -/
theorem turanGraph_edge_count_lower_bound (n p : ℕ) (hp : 0 < p) :
    (((p : ℝ) - 1) / (2 * p)) * (n : ℝ) ^ 2 - ((p : ℝ) ^ 2 + 1) ≤
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) := by
  let r := n % p
  let a := (n ^ 2 - r ^ 2) * (p - 1)
  let q := 2 * p
  have hq : 0 < q := by simp only [q]; omega
  have hfloorNat : a ≤ q * (a / q + 1) :=
    (Nat.lt_mul_div_succ a hq).le
  have hfloorCast : (a : ℝ) ≤ (q : ℝ) * ((a / q : ℕ) + 1) := by
    exact_mod_cast hfloorNat
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hfloor : (a : ℝ) / (q : ℝ) - 1 ≤ (a / q : ℕ) := by
    have hdiv : (a : ℝ) / (q : ℝ) ≤ (a / q : ℕ) + 1 := by
      apply (div_le_iff₀ hqReal).2
      simpa [mul_comm] using hfloorCast
    linarith
  have hrlt : r < p := by simpa only [r] using Nat.mod_lt n hp
  have hrsq : r ^ 2 ≤ n ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.mod_le n p) 2
  have hrsqP : (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast (Nat.pow_le_pow_left hrlt.le 2)
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hpMinus : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have haCast : (a : ℝ) = ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((p : ℝ) - 1) := by
    rw [show a = (n ^ 2 - r ^ 2) * (p - 1) by rfl, Nat.cast_mul,
      Nat.cast_sub hrsq, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  rw [Nat.cast_add]
  change _ ≤ ((a / q : ℕ) : ℝ) + ((r.choose 2 : ℕ) : ℝ)
  have hchoose : (0 : ℝ) ≤ ((r.choose 2 : ℕ) : ℝ) := by positivity
  calc
    (((p : ℝ) - 1) / (2 * p)) * (n : ℝ) ^ 2 - ((p : ℝ) ^ 2 + 1)
        ≤ (a : ℝ) / (q : ℝ) - 1 := by
          rw [haCast]
          dsimp [q]
          have herr :
              (((p : ℝ) - 1) / (2 * p)) * (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
            have hcoeff : ((p : ℝ) - 1) / (2 * p) ≤ 1 := by
              apply (div_le_one (by positivity : (0 : ℝ) < 2 * p)).2
              linarith
            calc
              ((p : ℝ) - 1) / (2 * p) * (r : ℝ) ^ 2
                  ≤ 1 * (r : ℝ) ^ 2 :=
                    mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (r : ℝ))
              _ = (r : ℝ) ^ 2 := one_mul _
              _ ≤ (p : ℝ) ^ 2 := hrsqP
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
          have hid :
              (((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((p : ℝ) - 1)) / (2 * p) =
                (((p : ℝ) - 1) / (2 * p)) * (n : ℝ) ^ 2 -
                  (((p : ℝ) - 1) / (2 * p)) * (r : ℝ) ^ 2 := by
            field_simp
          rw [hid]
          linarith
    _ ≤ ((a / q : ℕ) : ℝ) := hfloor
    _ ≤ ((a / q : ℕ) : ℝ) + ((r.choose 2 : ℕ) : ℝ) := by linarith

/-- The normalized balanced Turán edge count tends to its classical density. -/
theorem turanGraph_edge_count_ratio_tendsto (p : ℕ) (hp : 0 < p) :
    Tendsto
      (fun n : ℕ ↦ ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (((p : ℝ) - 1) / (2 * p))) := by
  let c : ℝ := ((p : ℝ) - 1) / (2 * p)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hconst : 0 ≤ (p : ℝ) ^ 2 + 1 := by positivity
  have herror : Tendsto (fun n : ℕ ↦ ((p : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hevent := herror.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hnerror := hN n ((le_max_left N 1).trans hn)
  have hn : 1 ≤ n := (le_max_right N 1).trans hn
  have hnReal : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnReal 2
  have hlowerRaw := turanGraph_edge_count_lower_bound n p hp
  have hlower : c - ((p : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2 ≤
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2 := by
    calc
      c - ((p : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2 =
          (c * (n : ℝ) ^ 2 - ((p : ℝ) ^ 2 + 1)) / (n : ℝ) ^ 2 := by
            field_simp
      _ ≤ ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by simpa [c] using hlowerRaw) hnSq.le
  have hupperNat := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := p)
  have hupperCast :
      (2 * p : ℝ) * ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) ≤
        ((p - 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hupperNat
  have hpCastSub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have hupper :
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2 ≤ c := by
    rw [hpCastSub] at hupperCast
    apply (div_le_iff₀ hnSq).2
    calc
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ)
          ≤ (((p : ℝ) - 1) * (n : ℝ) ^ 2) / (2 * p) :=
            (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * p)).2 (by
              simpa [mul_comm] using hupperCast)
      _ = c * (n : ℝ) ^ 2 := by
        dsimp [c]
        ring
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · dsimp [c] at hlower ⊢
    linarith
  · dsimp [c] at hupper ⊢
    linarith

/-- Erdős–Stone supplies the asymptotic upper bound for `f`. -/
theorem eventually_f_le_asymptoticCoefficient_add
    (d : ℕ) (hd : 4 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (f d n : ℝ) ≤ (asymptoticCoefficient d + ε) * (n : ℝ) ^ 2 := by
  have hp : 2 ≤ d / 2 := by omega
  filter_upwards
      [Turan.eventually_card_edgeFinset_le_completeEquipartite (d / 2) 3 hp hε,
        eventually_ge_atTop 2]
      with n hbound hn
  obtain ⟨A, hAcard, hA, hcount⟩ :=
    exists_diameterPairCount_eq_f d n (by omega) (by omega)
  have hgraph := hbound {x // x ∈ A} (by simpa using hAcard) (diameterGraph A)
    (diameterGraph_completeEquipartiteGraph_free hd A)
  rw [← hcount, diameterPairCount]
  simpa [asymptoticCoefficient] using hgraph

/-- Resolution of the asymptotic part of Erdős Problem 223. -/
theorem f_ratio_tendsto (d : ℕ) (hd : 4 ≤ d) :
    Tendsto (fun n : ℕ ↦ (f d n : ℝ) / (n : ℝ) ^ 2) atTop
      (nhds ((((d / 2 : ℕ) : ℝ) - 1) / (2 * (d / 2 : ℕ)))) := by
  let p := d / 2
  let c : ℝ := ((p : ℝ) - 1) / (2 * p)
  have hp : 0 < p := by dsimp [p]; omega
  have hTuran := turanGraph_edge_count_ratio_tendsto p hp
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hTuranEvent := hTuran.eventually (Metric.ball_mem_nhds _ hε)
  apply eventually_atTop.mp
  filter_upwards [hTuranEvent,
      eventually_f_le_asymptoticCoefficient_add d hd (half_pos hε),
      eventually_ge_atTop 2] with n hTuranClose hupper hn
  have hnReal : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnReal 2
  have hlenzNat := Lenz.turanNumber_le_f (d := d) (n := n) hd (by omega)
  have hlenz :
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2 ≤
        (f d n : ℝ) / (n : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hlenzNat) hnSq.le
  have hlower : c - ε < (f d n : ℝ) / (n : ℝ) ^ 2 := by
    rw [Real.dist_eq] at hTuranClose
    have habs := (abs_lt.mp hTuranClose).1
    have hTuranLower :
        c - ε < ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) / (n : ℝ) ^ 2 := by
      dsimp [c]
      linarith
    exact hTuranLower.trans_le hlenz
  have hupperRatio : (f d n : ℝ) / (n : ℝ) ^ 2 ≤ c + ε / 2 := by
    apply (div_le_iff₀ hnSq).2
    simpa [asymptoticCoefficient, p, c] using hupper
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> dsimp [c, p] at * <;> linarith

#print axioms f_ratio_tendsto

end Erdos223
