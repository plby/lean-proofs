/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Padding

/-!
# Erdős Problem 284: from Croot intervals to every cardinality

This file contains the asymptotic reindexing and padding argument.  Given
Croot witnesses in `(N, X(N)]`, with `X(N) / N → e`, choose
`N = ⌊c(k+1)⌋`.  If

`1/2 < c < 1 / (e - 1)`,

then eventually the witness has at most `k+1` terms and its one-shot padding
has enough room to reach exactly `k+1` terms while retaining the lower bound
on every denominator.
-/

open Filter
open scoped Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The natural cutoff used to turn Croot's parameter `N` into an exact
number `k+1` of summands. -/
def lowerCutoff (c : ℝ) (k : ℕ) : ℕ :=
  ⌊c * (k + 1 : ℕ)⌋₊

theorem lowerCutoff_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (lowerCutoff c) atTop atTop := by
  exact (tendsto_nat_floor_mul_atTop c hc).comp (tendsto_add_atTop_nat 1)

theorem lowerCutoff_ratio_tendsto {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ ↦ (lowerCutoff c k : ℝ) / (k + 1 : ℕ))
      atTop (nhds c) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  convert h using 1
  funext k
  norm_num [lowerCutoff]

/-- Croot's variable-cardinality witnesses imply exact-cardinality
representations whose smallest denominator is asymptotically at least any
constant strictly between `1/2` and `1/(e-1)`. -/
theorem eventually_exact_card_above_of_croot
    (hCroot : HasCrootShortIntervals) {c : ℝ}
    (hcpos : 0 < c) (hchalf : (1 : ℝ) / 2 < c)
    (hctarget : c < 1 / (Real.exp 1 - 1)) :
    ∀ᶠ k : ℕ in atTop, ∃ E : Finset ℕ,
      FinsetRepresentation (k + 1) E ∧
        ∀ a ∈ E, lowerCutoff c k < a := by
  rcases hCroot with ⟨X, hXratio, hXwitness⟩
  let N : ℕ → ℕ := lowerCutoff c
  have hNtop : Tendsto N atTop atTop := lowerCutoff_tendsto_atTop hcpos
  have hNratio :
      Tendsto (fun k : ℕ ↦ (N k : ℝ) / (k + 1 : ℕ))
        atTop (nhds c) := lowerCutoff_ratio_tendsto hcpos.le
  have hXNratio :
      Tendsto (fun k : ℕ ↦ (X (N k) : ℝ) / (N k : ℝ))
        atTop (nhds (Real.exp 1)) := hXratio.comp hNtop
  have hNpos : ∀ᶠ k : ℕ in atTop, 0 < N k :=
    hNtop.eventually (eventually_gt_atTop 0)
  have hXoverK :
      Tendsto (fun k : ℕ ↦ (X (N k) : ℝ) / (k + 1 : ℕ))
        atTop (nhds (Real.exp 1 * c)) := by
    have hprod := hXNratio.mul hNratio
    refine hprod.congr' ?_
    filter_upwards [hNpos] with k hk
    have hkN : (N k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hkK : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hgap :
      Tendsto
        (fun k : ℕ ↦
          (X (N k) : ℝ) / (k + 1 : ℕ) -
            (N k : ℝ) / (k + 1 : ℕ))
        atTop (nhds (Real.exp 1 * c - c)) := hXoverK.sub hNratio
  have hexpm1 : 0 < Real.exp 1 - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hlimit_lt : Real.exp 1 * c - c < 1 := by
    have hc := (lt_div_iff₀ hexpm1).mp hctarget
    calc
      Real.exp 1 * c - c = c * (Real.exp 1 - 1) := by ring
      _ < 1 := by simpa using hc
  have hgap_lt : ∀ᶠ k : ℕ in atTop,
      (X (N k) : ℝ) / (k + 1 : ℕ) -
          (N k : ℝ) / (k + 1 : ℕ) < 1 :=
    (tendsto_order.1 hgap).2 1 hlimit_lt
  have hhalf : ∀ᶠ k : ℕ in atTop,
      (1 : ℝ) / 2 < (N k : ℝ) / (k + 1 : ℕ) :=
    (tendsto_order.1 hNratio).1 ((1 : ℝ) / 2) hchalf
  have hwitness : ∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ, ShortIntervalWitness (N k) (X (N k)) A :=
    hNtop.eventually hXwitness
  filter_upwards [hwitness, hgap_lt, hhalf] with k hw hgapk hhalfk
  rcases hw with ⟨A, hA⟩
  have hAne : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le
    (Nat.zero_lt_succ (N k)) hA.succ_le_card)
  have hNX : N k ≤ X (N k) := by
    obtain ⟨a, ha⟩ := hAne
    exact (hA.interval a ha).1.le.trans (hA.interval a ha).2
  have hsubratio :
      (((X (N k) - N k : ℕ) : ℝ) / (k + 1 : ℕ)) =
        (X (N k) : ℝ) / (k + 1 : ℕ) -
          (N k : ℝ) / (k + 1 : ℕ) := by
    rw [Nat.cast_sub hNX]
    ring
  have hsub_lt : X (N k) - N k < k + 1 := by
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hr : (((X (N k) - N k : ℕ) : ℝ) / (k + 1 : ℕ)) < 1 := by
      rw [hsubratio]
      exact hgapk
    have := (div_lt_one hkpos).mp hr
    exact_mod_cast this
  have hcard : A.card ≤ k + 1 := hA.card_le_sub.trans (Nat.le_of_lt hsub_lt)
  have htwice : k + 1 < 2 * (N k + 1) := by
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hh := (lt_div_iff₀ hkpos).mp hhalfk
    have hreal : ((k + 1 : ℕ) : ℝ) < 2 * (N k : ℝ) := by
      nlinarith
    have hnat : k + 1 < 2 * N k := by exact_mod_cast hreal
    omega
  simpa only [N] using
    (padShortIntervalWitnessToCard_of_lt_two_mul hA hcard htwice)

end

end Erdos284

#print axioms Erdos284.lowerCutoff_tendsto_atTop
#print axioms Erdos284.lowerCutoff_ratio_tendsto
#print axioms Erdos284.eventually_exact_card_above_of_croot
