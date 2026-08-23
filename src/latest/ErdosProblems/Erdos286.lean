/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 286.
https://www.erdosproblems.com/forum/thread/286

Informal authors:
- Ernest S. Croot III
- Greg Martin

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos286.md
-/
/-
This is a Lean formalization of the affirmative resolution of Erdős Problem 286.

Informal authors:
- Ernest S. Croot III
- Greg Martin

Formalization:
- OpenAI Codex

Primary references:
- https://doi.org/10.4064/aa99-2-1
- https://doi.org/10.4064/aa-95-3-231-260
- https://www.erdosproblems.com/286
-/
import ErdosProblems.Erdos285.MartinUpperFinal
import ErdosProblems.Erdos285.Basic

/-!
# Erdős Problem 286

The supplied statement asks for, asymptotically in the number k of terms,
k distinct positive integers in a real interval of width
(exp 1 - 1 + o(1)) * k whose unit fractions sum to one.

The local formalization of Martin's theorem supplies, for every sufficiently
large k, an exact k-term representation whose largest denominator is
(exp 1 / (exp 1 - 1) + o(1)) * k.  The elementary strict inequality

exp 1 / (exp 1 - 1) < exp 1 - 1

therefore lets us enlarge the containing interval to the width requested here.
-/

namespace Erdos286

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- A literal ordered k-term representation of one by positive natural
denominators lying in the real interval [a, b]. -/
def IntervalRepresentation (k : ℕ) (a b : ℝ) : Prop :=
  ∃ n : Fin k → ℕ,
    StrictMono n ∧
    0 ∉ Set.range n ∧
    1 = ∑ i, (1 : ℝ) / n i ∧
    ∀ i, (n i : ℝ) ∈ Set.Icc a b

/-- Increasing enumeration of an arbitrary finite set with prescribed
cardinality. -/
def enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k) : Fin k → ℕ :=
  A.orderEmbOfFin hA

lemma enumerate_strictMono {k : ℕ} (A : Finset ℕ) (hA : A.card = k) :
    StrictMono (enumerate A hA) :=
  (A.orderEmbOfFin hA).strictMono

lemma enumerate_mem {k : ℕ} (A : Finset ℕ) (hA : A.card = k) (i : Fin k) :
    enumerate A hA i ∈ A :=
  A.orderEmbOfFin_mem hA i

lemma range_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k) :
    Set.range (enumerate A hA) = A :=
  A.range_orderEmbOfFin hA

lemma sum_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k) :
    (∑ i, (1 : ℝ) / enumerate A hA i) = Erdos285.reciprocalSum A := by
  rw [Erdos285.reciprocalSum]
  change (∑ i : Fin k, (1 : ℝ) / A.orderEmbOfFin hA i) =
    ∑ n ∈ A, (1 : ℝ) / n
  calc
    (∑ i : Fin k, (1 : ℝ) / A.orderEmbOfFin hA i) =
        ∑ n ∈ Finset.image (A.orderEmbOfFin hA) Finset.univ,
          (1 : ℝ) / n := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => (A.orderEmbOfFin hA).injective hij
    _ = ∑ n ∈ A, (1 : ℝ) / n := by
      rw [A.image_orderEmbOfFin_univ hA]

/-- The constant in Martin's largest-denominator theorem is strictly smaller
than the width coefficient requested in Problem 286. -/
lemma densityConstant_lt_exp_sub_one :
    Erdos285.Analytic.densityConstant < Real.exp 1 - 1 := by
  rw [Erdos285.Analytic.densityConstant]
  have hden : 0 < Real.exp 1 - 1 :=
    Erdos285.Analytic.exp_one_sub_one_pos
  rw [div_lt_iff₀ hden]
  have he : (2.7 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  nlinarith [sq_nonneg (Real.exp 1 - 2.7)]

/-- Martin's witnesses, reindexed by their actual number of terms. -/
lemma eventually_upperWitness_by_card :
    ∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ,
        Erdos285.UpperWitness 1 k
          (Erdos285.MartinUpperFinal.martinCutoff (k - 1)) A := by
  have h :=
    (tendsto_sub_atTop_nat 1).eventually
      Erdos285.MartinUpperFinal.eventually_martinUpperWitness
  filter_upwards [h, eventually_gt_atTop 0] with k hk hkpos
  simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hkpos.ne')]
    using hk

/-- The reindexed cutoff divided by the actual number of terms has Martin's
limit. -/
lemma cutoffByCard_ratio_tendsto :
    Tendsto
      (fun k : ℕ ↦
        (Erdos285.MartinUpperFinal.martinCutoff (k - 1) : ℝ) / (k : ℝ))
      atTop (nhds Erdos285.Analytic.densityConstant) := by
  have h :=
    Erdos285.MartinUpperFinal.martinCutoff_ratio_tendsto.comp
      (tendsto_sub_atTop_nat 1)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk1 : k - 1 + 1 = k :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')
  simp only [Function.comp_apply, hk1]

/-- Eventually Martin's natural cutoff lies strictly below
(exp 1 - 1) * k. -/
lemma eventually_cutoff_lt_width :
    ∀ᶠ k : ℕ in atTop,
      (Erdos285.MartinUpperFinal.martinCutoff (k - 1) : ℝ) <
        (Real.exp 1 - 1) * k := by
  have hratio :
      ∀ᶠ k : ℕ in atTop,
        (Erdos285.MartinUpperFinal.martinCutoff (k - 1) : ℝ) / (k : ℝ) <
          Real.exp 1 - 1 :=
    cutoffByCard_ratio_tendsto.eventually
      (Iio_mem_nhds densityConstant_lt_exp_sub_one)
  filter_upwards [hratio, eventually_gt_atTop 0] with k hk hkpos
  exact (div_lt_iff₀ (by exact_mod_cast hkpos)).mp hk

/-- Erdős Problem 286.

There is an o(1) error function such that every sufficiently large k
admits k strictly increasing positive integer denominators in a real
interval of width (e - 1 + o(1)) k, and their reciprocals sum to one.

We choose the error identically zero and the interval
[1, 1 + (e - 1)k]; Martin's stronger eventual upper bound puts every
denominator inside it. -/
theorem erdos_286 :
    ∃ o : ℕ → ℝ,
      o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ k : ℕ in atTop,
        2 ≤ k ∧
          ∃ a b : ℝ,
            b - a = (Real.exp 1 - 1 + o k) * k ∧
            IntervalRepresentation k a b := by
  refine ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _, ?_⟩
  filter_upwards
    [eventually_ge_atTop 2, eventually_upperWitness_by_card,
      eventually_cutoff_lt_width]
      with k hk2 hk hcut
  refine ⟨hk2, ?_⟩
  rcases hk with ⟨A, hA⟩
  let n : Fin k → ℕ := enumerate A hA.card_eq
  refine ⟨1, 1 + (Real.exp 1 - 1) * k, by simp, n, ?_, ?_, ?_, ?_⟩
  · exact enumerate_strictMono A hA.card_eq
  · rw [range_enumerate A hA.card_eq]
    exact hA.zero_not_mem
  · rw [sum_enumerate A hA.card_eq, hA.sum_eq]
  · intro i
    have hmem : n i ∈ A := enumerate_mem A hA.card_eq i
    have hn0 : n i ≠ 0 := by
      intro hn
      exact hA.zero_not_mem (hn ▸ hmem)
    have hnle : n i ≤ Erdos285.MartinUpperFinal.martinCutoff (k - 1) :=
      hA.le_cutoff (n i) hmem
    constructor
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    · have hnleR :
          (n i : ℝ) ≤
            (Erdos285.MartinUpperFinal.martinCutoff (k - 1) : ℝ) := by
        exact_mod_cast hnle
      linarith

end

end Erdos286

#print axioms Erdos286.erdos_286
