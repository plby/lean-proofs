import ErdosProblems.Erdos260.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sequence/support bridges for the Erdős 260 endpoint

This module contains the analytic reindexing facts used after the positive
dyadic-density theorem.  It is independent of the carry/window argument.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260

/-- The positive-integer sequence summand, placed below `Completion` so the
support reindexing lemmas do not introduce an import cycle. -/
def natSequenceTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) / (2 : ℝ) ^ a n

theorem summable_nat_weight :
    Summable (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) := by
  apply summable_of_ratio_norm_eventually_le (r := (3 : ℝ) / 4) (by norm_num)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hterm : 0 ≤ (n : ℝ) / (2 : ℝ) ^ n := by positivity
  have htermSucc :
      0 ≤ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by positivity
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg htermSucc, abs_of_nonneg hterm]
  rw [pow_succ]
  field_simp
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith

theorem summable_weightedSupportTerm (S : Set ℕ) :
    Summable (weightedSupportTerm S) := by
  apply summable_nat_weight.of_norm_bounded
  intro n
  have hbase : 0 ≤ (n : ℝ) / (2 : ℝ) ^ n := by positivity
  by_cases hn : n ∈ S
  · simp [weightedSupportTerm, hn]
  · simp [weightedSupportTerm, hn, hbase]

theorem natSequenceTerm_eq_weightedSupport_comp (a : ℕ → ℕ)
    (n : ℕ) :
    natSequenceTerm a n = weightedSupportTerm (Set.range a) (a n) := by
  simp [natSequenceTerm, weightedSupportTerm]

theorem hasSum_range_weightedSupport (a : ℕ → ℕ) (ha : StrictMono a) :
    HasSum (weightedSupportTerm (Set.range a))
      (∑' n : ℕ, natSequenceTerm a n) := by
  let f := weightedSupportTerm (Set.range a)
  have hzero : ∀ x ∉ Set.range a, f x = 0 := by
    intro x hx
    simp [f, weightedSupportTerm, hx]
  have hcomp :
      (fun n => natSequenceTerm a n) = f ∘ a := by
    funext n
    exact natSequenceTerm_eq_weightedSupport_comp a n
  have hsummableF : Summable f := summable_weightedSupportTerm (Set.range a)
  have hsummableComp : Summable (f ∘ a) :=
    (ha.injective.summable_iff hzero).2 hsummableF
  have hsum : HasSum (f ∘ a) (∑' n : ℕ, natSequenceTerm a n) := by
    have hs : Summable (fun n => natSequenceTerm a n) := by
      rw [hcomp]
      exact hsummableComp
    exact hs.hasSum.congr_fun fun n => (congrFun hcomp n).symm
  exact (ha.injective.hasSum_iff hzero).1 hsum

theorem range_infinite_of_strictMono (a : ℕ → ℕ) (ha : StrictMono a) :
    (Set.range a).Infinite := by
  exact Set.infinite_range_of_injective ha.injective

/-- Superlinear growth forces the range to occupy less than any prescribed
positive proportion of every sufficiently large dyadic block. -/
theorem eventually_dyadicBlockCount_lt_of_growth (a : ℕ → ℕ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℕ in atTop,
      (dyadicBlockCount (Set.range a) (dyadicScale L) : ℝ) <
        c * dyadicScale L := by
  classical
  let M : ℝ := 8 / c
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (hgrowth.eventually_gt_atTop M)
  have hscale :
      Tendsto (fun L : ℕ => ((dyadicScale L : ℕ) : ℝ)) atTop atTop := by
    simpa [dyadicScale] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  filter_upwards
      [hscale.eventually_gt_atTop (2 * (N + 1) / c)] with L hL
  let X := dyadicScale L
  let K := N + Nat.ceil (c * X / 4)
  have hsubset :
      ((Finset.Ioc X (2 * X)).filter fun x => x ∈ Set.range a) ⊆
        (Finset.range K).image a := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    rcases hx.2 with ⟨n, rfl⟩
    have hnK : n < K := by
      by_contra hnot
      have hKn : K ≤ n := le_of_not_gt hnot
      have hNn : N ≤ n := le_trans (Nat.le_add_right N _) hKn
      have hceiln : Nat.ceil (c * X / 4) ≤ n := by
        dsimp [K] at hKn
        omega
      have hratio := hN n hNn
      have hnreal : c * X / 4 ≤ (n : ℝ) := by
        exact (Nat.le_ceil (c * X / 4)).trans (by exact_mod_cast hceiln)
      have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hmul : M * ((n : ℝ) + 1) < (a n : ℝ) :=
        (lt_div_iff₀ hn1pos).mp (by simpa [Nat.cast_add, Nat.cast_one] using hratio)
      have h2X : (2 : ℝ) * X < a n := by
        dsimp [M] at hmul
        have hXnonneg : (0 : ℝ) ≤ X := by positivity
        field_simp [hc.ne'] at hmul ⊢
        nlinarith
      have hupper : (a n : ℝ) ≤ 2 * X := by exact_mod_cast hx.1.2
      linarith
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨n, hnK, rfl⟩
  have hcardNat : dyadicBlockCount (Set.range a) X ≤ K := by
    calc
      dyadicBlockCount (Set.range a) X ≤
          ((Finset.range K).image a).card := Finset.card_le_card hsubset
      _ ≤ (Finset.range K).card := Finset.card_image_le
      _ = K := Finset.card_range K
  have hcardReal :
      (dyadicBlockCount (Set.range a) X : ℝ) ≤ K := by
    exact_mod_cast hcardNat
  have hceil :
      (Nat.ceil (c * X / 4) : ℝ) < c * X / 4 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hlarge : (N : ℝ) + 1 < c * X / 2 := by
    dsimp [X] at hL ⊢
    have hcross := (div_lt_iff₀ hc).mp hL
    nlinarith
  dsimp [K] at hcardReal
  push_cast at hcardReal
  dsimp [X] at hcardReal hceil hlarge ⊢
  nlinarith

end Erdos260
