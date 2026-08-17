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

/-!
# Exact global bucket parameters for Janzer--Sudakov Theorem 5.3

The exponent intervals are divided into dyadic phases.  In phase `i` there
are `10*r` equal slots, each of width `2^i * ell`, where
`ell = log₂(log₂ Delta) + 1`.
-/

namespace Erdos182
namespace JSGlobalParameters

def ell (Delta : ℕ) : ℕ := Nat.log 2 (Nat.log 2 Delta) + 1
def slots (r : ℕ) : ℕ := 10 * r
def slotWidth (Delta i : ℕ) : ℕ := 2 ^ i * ell Delta
def lowerExponent (r Delta i q : ℕ) : ℕ :=
  (slots r + q) * slotWidth Delta i
def upperExponent (r Delta i q : ℕ) : ℕ :=
  (slots r + q + 1) * slotWidth Delta i
def iterationExponent (r Delta i q : ℕ) : ℕ :=
  upperExponent r Delta i q - upperExponent r Delta i q / (6 * r)
def indices (r Delta : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (ell Delta)).product (Finset.range (slots r))
def lowDegree (r Delta : ℕ) : ℕ := 10 * r ^ 2 * ell Delta
def coreDegree (r Delta : ℕ) : ℕ := 20 * r ^ 2 * ell Delta
def incidenceLoss (k r Delta : ℕ) : ℕ :=
  Nat.clog 2 (400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2) + 2

open Filter

private theorem eight_mul_add_seven_le_pow_two {m : ℕ} (hm : 8 ≤ m) :
    8 * m + 7 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm hpow =>
      rw [pow_succ]
      omega

private theorem clog_two_le_div_eight {n : ℕ} (hn : 64 ≤ n) :
    Nat.clog 2 n ≤ n / 8 := by
  apply Nat.clog_le_of_le_pow
  have hm : 8 ≤ n / 8 := by omega
  calc
    n = 8 * (n / 8) + n % 8 := by omega
    _ ≤ 8 * (n / 8) + 7 := by omega
    _ ≤ 2 ^ (n / 8) := eight_mul_add_seven_le_pow_two hm

private theorem incidence_clog_bound (k r Delta : ℕ) :
    Nat.clog 2
          (400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2) ≤
      Nat.clog 2 (400 * (4 * (k + 1) ^ 2) * r ^ 2) +
        2 * Nat.clog 2 (ell Delta) := by
  let A := 400 * (4 * (k + 1) ^ 2) * r ^ 2
  let L := ell Delta
  let a := Nat.clog 2 A
  let l := Nat.clog 2 L
  apply Nat.clog_le_of_le_pow
  calc
    400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2 = A * L ^ 2 := by rfl
    _ ≤ 2 ^ a * (2 ^ l) ^ 2 := by
      gcongr
      · exact Nat.le_pow_clog (by omega) A
      · exact Nat.le_pow_clog (by omega) L
    _ = 2 ^ (a + 2 * l) := by ring

/-- A completely explicit sufficient condition for the global incidence loss
to fit into half of the iterated-logarithm budget. -/
theorem incidenceLoss_le_half_of_ell_ge (k r Delta : ℕ)
    (hell64 : 64 ≤ ell Delta)
    (hellC :
      4 * (Nat.clog 2 (400 * (4 * (k + 1) ^ 2) * r ^ 2) + 2) ≤ ell Delta) :
    incidenceLoss k r Delta ≤ ell Delta / 2 := by
  let L := ell Delta
  let c := Nat.clog 2 (400 * (4 * (k + 1) ^ 2) * r ^ 2)
  have hlog : Nat.clog 2 L ≤ L / 8 := clog_two_le_div_eight hell64
  have hc : c + 2 ≤ L / 4 := by omega
  have hcore := incidence_clog_bound k r Delta
  dsimp [incidenceLoss]
  change Nat.clog 2
      (400 * (4 * (k + 1) ^ 2) * r ^ 2 * L ^ 2) + 2 ≤ L / 2
  change 4 * (c + 2) ≤ L at hellC
  change Nat.clog 2
      (400 * (4 * (k + 1) ^ 2) * r ^ 2 * L ^ 2) ≤
        c + 2 * Nat.clog 2 L at hcore
  omega

private theorem ell_ge_of_two_pow_two_pow_le {B Delta : ℕ}
    (hDelta : 2 ^ (2 ^ B) ≤ Delta) : B ≤ ell Delta := by
  have hinner : 2 ^ B ≤ Nat.log 2 Delta := by
    calc
      2 ^ B = Nat.log 2 (2 ^ (2 ^ B)) := by
        rw [Nat.log_pow (by omega : 1 < 2)]
      _ ≤ Nat.log 2 Delta := Nat.log_mono_right hDelta
  have houter : B ≤ Nat.log 2 (Nat.log 2 Delta) := by
    calc
      B = Nat.log 2 (2 ^ B) := by
        rw [Nat.log_pow (by omega : 1 < 2)]
      _ ≤ Nat.log 2 (Nat.log 2 Delta) := Nat.log_mono_right hinner
  simp only [ell]
  omega

/-- For fixed k and r, the integer incidence loss is eventually at most half
of ell Delta.  This is the exact eventual hypothesis consumed by the global
parameter package. -/
theorem eventually_incidenceLoss_le_half (k r : ℕ) :
    ∀ᶠ Delta : ℕ in atTop,
      incidenceLoss k r Delta ≤ ell Delta / 2 := by
  let B := max 64
    (4 * (Nat.clog 2 (400 * (4 * (k + 1) ^ 2) * r ^ 2) + 2))
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ B))] with Delta hDelta
  have hell : B ≤ ell Delta := ell_ge_of_two_pow_two_pow_le hDelta
  apply incidenceLoss_le_half_of_ell_ge k r Delta
  · exact (le_max_left _ _).trans hell
  · exact (le_max_right _ _).trans hell

lemma ell_pos (Delta : ℕ) : 0 < ell Delta := by simp [ell]

lemma slots_pos {r : ℕ} (hr : 0 < r) : 0 < slots r := by
  simp [slots, hr]

lemma slotWidth_pos (Delta i : ℕ) : 0 < slotWidth Delta i := by
  simp [slotWidth, ell_pos]

@[simp] theorem card_indices (r Delta : ℕ) :
    (indices r Delta).card = ell Delta * slots r := by
  simp [indices]

theorem lowDegree_add_bucket_budget (r Delta : ℕ) :
    lowDegree r Delta + (indices r Delta).card * r = coreDegree r Delta := by
  simp [lowDegree, coreDegree, card_indices, slots]
  ring

private theorem exists_slot {m W x : ℕ} (hW : 0 < W)
    (hx : 0 < x) (hxle : x ≤ m * W) :
    ∃ q < m, q * W < x ∧ x ≤ (q + 1) * W := by
  let q := (x - 1) / W
  have hxsub : x - 1 < m * W := by omega
  have hq : q < m := by
    apply (Nat.div_lt_iff_lt_mul hW).2
    simpa [q] using hxsub
  have hqlo : q * W ≤ x - 1 := by
    simpa [q, mul_comm] using Nat.div_mul_le_self (x - 1) W
  have hqhi : x - 1 < (q + 1) * W := by
    have := Nat.lt_mul_div_succ (x - 1) hW
    simpa [q, mul_comm] using this
  exact ⟨q, hq, by omega, by omega⟩

private theorem exists_phase_slot {m W L e : ℕ} (hW : 0 < W)
    (hlo : m * W < e) (hhi : e ≤ m * W * 2 ^ (L + 1)) :
    ∃ i ≤ L, ∃ q < m,
      (m + q) * (2 ^ i * W) < e ∧
        e ≤ (m + q + 1) * (2 ^ i * W) := by
  induction L generalizing e with
  | zero =>
      have hx : 0 < e - m * W := by omega
      have hxle : e - m * W ≤ m * W := by
        have hhi' : e ≤ m * W + m * W := by
          calc
            e ≤ m * W * 2 := by simpa [pow_succ] using hhi
            _ = m * W + m * W := by ring
        omega
      obtain ⟨q, hqm, hqlo, hqhi⟩ := exists_slot hW hx hxle
      refine ⟨0, le_rfl, q, hqm, ?_, ?_⟩
      · simp only [pow_zero, one_mul]
        calc
          (m + q) * W = m * W + q * W := by ring
          _ < m * W + (e - m * W) := Nat.add_lt_add_left hqlo _
          _ = e := Nat.add_sub_of_le hlo.le
      · simp only [pow_zero, one_mul]
        calc
          e = m * W + (e - m * W) := (Nat.add_sub_of_le hlo.le).symm
          _ ≤ m * W + (q + 1) * W := Nat.add_le_add_left hqhi _
          _ = (m + q + 1) * W := by ring
  | succ L ih =>
      by_cases hfirst : e ≤ m * W * 2 ^ (L + 1)
      · obtain ⟨i, hi, q, hq, hlo', hhi'⟩ := ih hlo hfirst
        exact ⟨i, hi.trans (Nat.le_succ L), q, hq, hlo', hhi'⟩
      · let W' := 2 ^ (L + 1) * W
        have hW' : 0 < W' := by positivity
        have hlo' : m * W' < e := by
          dsimp [W']
          simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.lt_of_not_ge hfirst
        have hhi' : e ≤ 2 * (m * W') := by
          dsimp [W']
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi
        have hx : 0 < e - m * W' := by omega
        have hxle : e - m * W' ≤ m * W' := by omega
        obtain ⟨q, hqm, hqlo, hqhi⟩ := exists_slot hW' hx hxle
        refine ⟨L + 1, le_rfl, q, hqm, ?_, ?_⟩
        · calc
            (m + q) * (2 ^ (L + 1) * W) = m * W' + q * W' := by
              dsimp [W']; ring
            _ < m * W' + (e - m * W') := Nat.add_lt_add_left hqlo _
            _ = e := Nat.add_sub_of_le hlo'.le
        · calc
            e = m * W' + (e - m * W') := (Nat.add_sub_of_le hlo'.le).symm
            _ ≤ m * W' + (q + 1) * W' := Nat.add_le_add_left hqhi _
            _ = (m + q + 1) * (2 ^ (L + 1) * W) := by
              dsimp [W']; ring

theorem exponent_covered {r Delta e : ℕ}
    (hlo : slots r * ell Delta < e)
    (hhi : e ≤ slots r * ell Delta * 2 ^ ell Delta) :
    ∃ z ∈ indices r Delta,
      lowerExponent r Delta z.1 z.2 < e ∧
        e ≤ upperExponent r Delta z.1 z.2 := by
  have hell : ell Delta - 1 + 1 = ell Delta := Nat.sub_add_cancel (ell_pos Delta)
  obtain ⟨i, hi, q, hq, hlo', hhi'⟩ :=
    exists_phase_slot (L := ell Delta - 1) (ell_pos Delta) hlo (by
      simpa [hell] using hhi)
  have hi' : i < ell Delta := by omega
  refine ⟨(i, q), ?_, ?_, ?_⟩
  · simp [indices, hi', hq]
  · simpa [lowerExponent, slotWidth, mul_assoc, mul_left_comm, mul_comm] using hlo'
  · simpa [upperExponent, slotWidth, mul_assoc, mul_left_comm, mul_comm] using hhi'

theorem clog_le_finalExponent {r Delta : ℕ} (hr : 0 < r) :
    Nat.clog 2 Delta ≤ slots r * ell Delta * 2 ^ ell Delta := by
  have hlog : Nat.log 2 Delta < 2 ^ ell Delta := by
    simpa [ell] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) (Nat.log 2 Delta)
  have hclog : Nat.clog 2 Delta ≤ Nat.log 2 Delta + 1 := by
    apply Nat.clog_le_of_le_pow
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) Delta).le
  have hclogpow : Nat.clog 2 Delta ≤ 2 ^ ell Delta := by omega
  have hfactor : 1 ≤ slots r * ell Delta := by
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt (slots_pos hr))
      (ne_of_gt (ell_pos Delta)))
  calc
    Nat.clog 2 Delta ≤ 2 ^ ell Delta := hclogpow
    _ ≤ slots r * ell Delta * 2 ^ ell Delta := by
      nlinarith [pow_pos (by omega : 0 < 2) (ell Delta)]

theorem degree_covered {r Delta d : ℕ} (hr : 0 < r) (hd : d ≤ Delta)
    (hlow : 2 ^ (slots r * ell Delta) < d) :
    ∃ z ∈ indices r Delta,
      2 ^ lowerExponent r Delta z.1 z.2 < d ∧
        d ≤ 2 ^ upperExponent r Delta z.1 z.2 := by
  let e := Nat.clog 2 d
  have hde : d ≤ 2 ^ e := Nat.le_pow_clog (by omega) d
  have helow : slots r * ell Delta < e := by
    by_contra h
    have he : e ≤ slots r * ell Delta := Nat.le_of_not_gt h
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) he
    omega
  have heDelta : e ≤ Nat.clog 2 Delta := Nat.clog_mono_right 2 hd
  have hehi : e ≤ slots r * ell Delta * 2 ^ ell Delta :=
    heDelta.trans (clog_le_finalExponent (r := r) (Delta := Delta) hr)
  obtain ⟨z, hz, hlo, hhi⟩ := exponent_covered helow hehi
  refine ⟨z, hz, ?_, hde.trans (Nat.pow_le_pow_right (by omega) hhi)⟩
  exact Nat.pow_lt_of_lt_clog hlo

theorem iteration_gap {r Delta i q : ℕ} (hr : 0 < r) :
    6 * r * (upperExponent r Delta i q - iterationExponent r Delta i q) ≤
        upperExponent r Delta i q ∧
      ell Delta / 2 + iterationExponent r Delta i q ≤
        lowerExponent r Delta i q := by
  let W := slotWidth Delta i
  let P := lowerExponent r Delta i q
  let T := upperExponent r Delta i q
  let S := iterationExponent r Delta i q
  have hden : 0 < 6 * r := by positivity
  have hdiv : T / (6 * r) ≤ T := Nat.div_le_self _ _
  have hsub : T - S = T / (6 * r) := by
    dsimp [S, iterationExponent]
    change T - (T - T / (6 * r)) = T / (6 * r)
    exact Nat.sub_sub_self hdiv
  have hclose : 6 * r * (T - S) ≤ T := by
    rw [hsub]
    simpa [mul_comm] using Nat.mul_div_le T (6 * r)
  have hellW : ell Delta ≤ W := by
    dsimp [W, slotWidth]
    simpa using Nat.mul_le_mul_right (ell Delta) (Nat.one_le_two_pow : 1 ≤ 2 ^ i)
  have hhalf : 2 * (ell Delta / 2) ≤ ell Delta := by
    simpa [mul_comm] using Nat.mul_div_le (ell Delta) 2
  have hbudget : 6 * r * (W + ell Delta / 2) ≤ T := by
    calc
      6 * r * (W + ell Delta / 2) =
          6 * r * W + 3 * r * (2 * (ell Delta / 2)) := by ring
      _ ≤ 6 * r * W + 3 * r * ell Delta := by gcongr
      _ ≤ 6 * r * W + 3 * r * W := by gcongr
      _ ≤ 10 * r * W := by
        nlinarith [slotWidth_pos Delta i]
      _ ≤ T := by
        dsimp [T, upperExponent, slots]
        nlinarith [slotWidth_pos Delta i]
  have hdivBudget : W + ell Delta / 2 ≤ T / (6 * r) :=
    (Nat.le_div_iff_mul_le hden).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget)
  have hTP : T = P + W := by
    dsimp [T, P, upperExponent, lowerExponent]
    ring
  have hSadd : S + T / (6 * r) = T := by
    dsimp [S, iterationExponent]
    change (T - T / (6 * r)) + T / (6 * r) = T
    exact Nat.sub_add_cancel hdiv
  have hreserve : S + (W + ell Delta / 2) ≤ T := by
    calc
      S + (W + ell Delta / 2) ≤ S + T / (6 * r) := by gcongr
      _ = T := hSadd
  have hgap : ell Delta / 2 + S ≤ P := by
    rw [hTP] at hreserve
    omega
  exact ⟨by simpa [T, S] using hclose, by simpa [P, S] using hgap⟩

theorem iterationExponent_lt_upper {r Delta i q : ℕ} (hr : 0 < r) :
    iterationExponent r Delta i q < upperExponent r Delta i q := by
  let W := slotWidth Delta i
  let T := upperExponent r Delta i q
  have hden : 0 < 6 * r := by positivity
  have hW : 0 < W := slotWidth_pos Delta i
  have hdenle : 6 * r ≤ T := by
    calc
      6 * r ≤ 10 * r * W := by nlinarith
      _ ≤ T := by
        dsimp [T, upperExponent, slots]
        nlinarith
  have hdiv : 0 < T / (6 * r) := Nat.div_pos hdenle hden
  have hT : 0 < T := hden.trans_le hdenle
  simpa [iterationExponent, T] using Nat.sub_lt hT hdiv

theorem case2_integer_slack {k r Delta i q : ℕ} (hr : 0 < r)
    (hloss : incidenceLoss k r Delta ≤ ell Delta / 2) :
    incidenceLoss k r Delta + iterationExponent r Delta i q ≤
        lowerExponent r Delta i q ∧
      6 * r *
          (upperExponent r Delta i q - iterationExponent r Delta i q) ≤
        upperExponent r Delta i q := by
  have hgap := iteration_gap (Delta := Delta) (i := i) (q := q) hr
  exact ⟨(Nat.add_le_add_right hloss _).trans hgap.2, hgap.1⟩

/-- The exponent slack implies the literal power inequality needed after
the Case-2 double count. -/
theorem case2_density_power {k r Delta i q : ℕ} (hr : 0 < r)
    (hloss : incidenceLoss k r Delta ≤ ell Delta / 2) :
    400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2 *
          2 ^ iterationExponent r Delta i q ≤
      2 ^ lowerExponent r Delta i q := by
  let F := 400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2
  let S := iterationExponent r Delta i q
  let P := lowerExponent r Delta i q
  have hFP : incidenceLoss k r Delta + S ≤ P :=
    (case2_integer_slack hr hloss).1
  have hF : F ≤ 2 ^ incidenceLoss k r Delta := by
    calc
      F ≤ 2 ^ Nat.clog 2 F := Nat.le_pow_clog (by omega) F
      _ ≤ 2 ^ incidenceLoss k r Delta := by
        apply Nat.pow_le_pow_right (by omega)
        simp [incidenceLoss, F]
  calc
    400 * (4 * (k + 1) ^ 2) * r ^ 2 * (ell Delta) ^ 2 * 2 ^ S =
        F * 2 ^ S := by rfl
    _ ≤ 2 ^ incidenceLoss k r Delta * 2 ^ S := by gcongr
    _ = 2 ^ (incidenceLoss k r Delta + S) := (pow_add _ _ _).symm
    _ ≤ 2 ^ P := Nat.pow_le_pow_right (by omega) hFP

theorem exact_parameter_package (k r Delta : ℕ) (hr : 0 < r)
    (hloss : incidenceLoss k r Delta ≤ ell Delta / 2) :
    (indices r Delta).card = ell Delta * slots r ∧
      lowDegree r Delta + (indices r Delta).card * r = coreDegree r Delta ∧
      (∀ d ≤ Delta, 2 ^ (slots r * ell Delta) < d →
        ∃ z ∈ indices r Delta,
          2 ^ lowerExponent r Delta z.1 z.2 < d ∧
            d ≤ 2 ^ upperExponent r Delta z.1 z.2) ∧
      (∀ z ∈ indices r Delta,
        incidenceLoss k r Delta + iterationExponent r Delta z.1 z.2 ≤
            lowerExponent r Delta z.1 z.2 ∧
          6 * r *
              (upperExponent r Delta z.1 z.2 -
                iterationExponent r Delta z.1 z.2) ≤
            upperExponent r Delta z.1 z.2) := by
  refine ⟨card_indices r Delta, lowDegree_add_bucket_budget r Delta, ?_, ?_⟩
  · intro d hd hlow
    exact degree_covered hr hd hlow
  · intro z _hz
    exact case2_integer_slack hr hloss

/-- For fixed positive r, the complete exact bucket package is available for
all sufficiently large maximum degrees. -/
theorem eventually_exact_parameter_package (k r : ℕ) (hr : 0 < r) :
    ∀ᶠ Delta : ℕ in atTop,
      (indices r Delta).card = ell Delta * slots r ∧
        lowDegree r Delta + (indices r Delta).card * r = coreDegree r Delta ∧
        (∀ d ≤ Delta, 2 ^ (slots r * ell Delta) < d →
          ∃ z ∈ indices r Delta,
            2 ^ lowerExponent r Delta z.1 z.2 < d ∧
              d ≤ 2 ^ upperExponent r Delta z.1 z.2) ∧
        (∀ z ∈ indices r Delta,
          incidenceLoss k r Delta + iterationExponent r Delta z.1 z.2 ≤
              lowerExponent r Delta z.1 z.2 ∧
            6 * r *
                (upperExponent r Delta z.1 z.2 -
                  iterationExponent r Delta z.1 z.2) ≤
              upperExponent r Delta z.1 z.2) := by
  filter_upwards [eventually_incidenceLoss_le_half k r] with Delta hloss
  exact exact_parameter_package k r Delta hr hloss

end JSGlobalParameters
end Erdos182
