/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. -/
import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Sigma
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Erdős Problem 37

An essential component is a set whose addition strictly increases the
Schnirelmann density of every set of density strictly between zero and one.
Erdős asked whether a uniformly lacunary set can be an essential component.
Ruzsa proved that the answer is no.

The definition of lacunarity below enumerates the positive part of the set.
Thus a possible zero, which is relevant to ordinary pointwise sumsets but not
to the counting function or to lacunarity, is handled correctly.
-/

open scoped ENNReal NNReal Pointwise Real
open Finset Set Filter

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Erdos37

/-- The number of members of `A` in `{1, ..., N}`. -/
def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  #{a ∈ Finset.Ioc 0 N | a ∈ A}

/-- A division-free characterization of lower asymptotic density.  The first
clause gives every strict eventual lower bound; the second gives arbitrarily
late upper witnesses for every strict upper bound. -/
def HasLowerDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  (∀ α : ℝ, α < δ →
    ∀ᶠ N : ℕ in atTop, α * (N : ℝ) ≤ (countIn A N : ℝ)) ∧
  (∀ β : ℝ, δ < β → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
    (countIn A N : ℝ) ≤ β * (N : ℝ))

namespace HasLowerDensity

lemma eventually_lower {A : Set ℕ} {δ α : ℝ}
    (h : HasLowerDensity A δ) (hα : α < δ) :
    ∀ᶠ N : ℕ in atTop, α * (N : ℝ) ≤ (countIn A N : ℝ) :=
  h.1 α hα

lemma exists_upper {A : Set ℕ} {δ β : ℝ}
    (h : HasLowerDensity A δ) (hβ : δ < β) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (countIn A N : ℝ) ≤ β * (N : ℝ) :=
  h.2 β hβ M

end HasLowerDensity

/-- The positive part of a set of natural numbers. -/
def positivePart (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ n ∈ A}

/-- Mathlib's Schnirelmann density with classical membership decisions fixed
once and for all.  The value is independent of that decision procedure. -/
noncomputable abbrev sd (A : Set ℕ) : ℝ :=
  @schnirelmannDensity A (fun n => Classical.propDecidable (n ∈ A))

/-- Essential component for Mathlib's Schnirelmann density and ordinary
pointwise addition of sets of nonnegative integers. -/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ,
    0 < sd B →
    sd B < 1 →
    sd B < sd (A + B)

/-- A set is lacunary when its positive part is infinite and consecutive
members of its canonical increasing enumeration grow by one fixed real ratio
strictly greater than one. -/
def IsLacunary (A : Set ℕ) : Prop :=
  (positivePart A).Infinite ∧
    ∃ q : ℝ, 1 < q ∧
      ∀ i : ℕ,
        q * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
          (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ)

/-- The noncomputable density does not depend on which membership decision
procedure is supplied. -/
lemma schnirelmannDensity_decidable_irrel (A : Set ℕ)
    (i j : DecidablePred (· ∈ A)) :
    @schnirelmannDensity A i = @schnirelmannDensity A j := by
  unfold schnirelmannDensity
  refine iInf_congr fun n => ?_
  refine congrArg (fun k : ℕ => (k : ℝ) / (n : ℕ)) ?_
  apply congrArg Finset.card
  ext a
  simp

lemma schnirelmannDensity_odd_with (d : DecidablePred (· ∈ Set.ofPred Odd)) :
    @schnirelmannDensity (Set.ofPred Odd) d = (2 : ℝ)⁻¹ := by
  calc
    @schnirelmannDensity (Set.ofPred Odd) d =
        @schnirelmannDensity (Set.ofPred Odd) (fun a => Nat.instDecidablePredOdd a) :=
      schnirelmannDensity_decidable_irrel _ _ _
    _ = (2 : ℝ)⁻¹ := schnirelmannDensity_setOfPred_Odd

lemma zero_mem_of_essential {A : Set ℕ} (hA : IsEssentialComponent A) : 0 ∈ A := by
  by_contra hzero
  have hB : sd (Set.ofPred Odd) = (2 : ℝ)⁻¹ :=
    schnirelmannDensity_odd_with _
  have hone : 1 ∉ A + Set.ofPred Odd := by
    intro h
    simp only [Set.mem_add] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have ha_le : a ≤ 1 := by omega
    have hb_le : b ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> simp_all [Odd]
  have hsum : sd (A + Set.ofPred Odd) = 0 :=
    schnirelmannDensity_eq_zero_of_one_notMem hone
  have hstrict := hA (Set.ofPred Odd) (by rw [hB]; norm_num) (by rw [hB]; norm_num)
  rw [hB, hsum] at hstrict
  norm_num at hstrict

lemma one_mem_of_essential {A : Set ℕ} (hA : IsEssentialComponent A) : 1 ∈ A := by
  by_contra hone
  have hB : sd (Set.ofPred Odd) = (2 : ℝ)⁻¹ :=
    schnirelmannDensity_odd_with _
  have htwo : 2 ∉ A + Set.ofPred Odd := by
    intro h
    simp only [Set.mem_add] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> simp_all [Odd]
  have hupper : sd (A + Set.ofPred Odd) ≤ (2 : ℝ)⁻¹ := by
    calc
      sd (A + Set.ofPred Odd) = schnirelmannDensity (A + Set.ofPred Odd) :=
        schnirelmannDensity_decidable_irrel _ _ _
      _ ≤ (2 : ℝ)⁻¹ := by
        have := schnirelmannDensity_le_of_notMem htwo
        norm_num at this ⊢
        exact this
  have hstrict := hA (Set.ofPred Odd) (by rw [hB]; norm_num) (by rw [hB]; norm_num)
  rw [hB] at hstrict
  exact (not_lt_of_ge hupper) hstrict

lemma countIn_eq_count_positivePart (A : Set ℕ) (N : ℕ) :
    countIn A N = Nat.count (· ∈ positivePart A) (N + 1) := by
  rw [countIn, Nat.count_eq_card_filter_range]
  congr 1
  ext n
  constructor
  · intro hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hn.1.2, by simpa [positivePart] using ⟨hn.1.1, hn.2⟩⟩
  · intro hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have hp : 0 < n ∧ n ∈ A := by simpa [positivePart] using hn.2
    exact ⟨⟨hp.1, Nat.le_of_lt_succ hn.1⟩, hp.2⟩

lemma nth_positivePart_pos {A : Set ℕ} (hA : (positivePart A).Infinite) (i : ℕ) :
    0 < Nat.nth (· ∈ positivePart A) i := by
  exact (Nat.nth_mem_of_infinite hA i).1

lemma nth_positivePart_mem {A : Set ℕ} (hA : (positivePart A).Infinite) (i : ℕ) :
    Nat.nth (· ∈ positivePart A) i ∈ A := by
  exact (Nat.nth_mem_of_infinite hA i).2

/-- Iteration of the one-step lacunarity inequality. -/
lemma lacunary_nth_lower {A : Set ℕ} {q : ℝ} (hq : 1 < q)
    (hstep : ∀ i : ℕ,
      q * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
        (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ)) (i : ℕ) :
    q ^ i * (Nat.nth (· ∈ positivePart A) 0 : ℝ) ≤
      (Nat.nth (· ∈ positivePart A) i : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc
        q ^ (i + 1) * (Nat.nth (· ∈ positivePart A) 0 : ℝ) =
            q * (q ^ i * (Nat.nth (· ∈ positivePart A) 0 : ℝ)) := by ring
        _ ≤ q * (Nat.nth (· ∈ positivePart A) i : ℝ) :=
          mul_le_mul_of_nonneg_left ih (le_of_lt (zero_lt_one.trans hq))
        _ ≤ (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ) := hstep i

/-- If `m` positive members of `A` occur at most `N`, the member with index
`m - 1` occurs at most `N`. -/
lemma nth_countIn_pred_le {A : Set ℕ} {N : ℕ} (hcount : 0 < countIn A N) :
    Nat.nth (· ∈ positivePart A) (countIn A N - 1) ≤ N := by
  have hltCount : countIn A N - 1 < Nat.count (· ∈ positivePart A) (N + 1) := by
    rw [← countIn_eq_count_positivePart]
    omega
  have hlt := Nat.nth_lt_of_lt_count hltCount
  omega

/-- The basic division-free counting estimate for a lacunary set. -/
lemma pow_countIn_pred_le {A : Set ℕ} (hA : IsLacunary A) {N : ℕ}
    (hcount : 0 < countIn A N) :
    ∃ q : ℝ, 1 < q ∧ q ^ (countIn A N - 1) ≤ (N : ℝ) := by
  obtain ⟨hInf, q, hq, hstep⟩ := hA
  refine ⟨q, hq, ?_⟩
  have hfirst : (1 : ℝ) ≤ (Nat.nth (· ∈ positivePart A) 0 : ℕ) := by
    exact_mod_cast nth_positivePart_pos hInf 0
  calc
    q ^ (countIn A N - 1) = q ^ (countIn A N - 1) * 1 := by simp
    _ ≤ q ^ (countIn A N - 1) *
        (Nat.nth (· ∈ positivePart A) 0 : ℝ) := by
      gcongr
    _ ≤ (Nat.nth (· ∈ positivePart A) (countIn A N - 1) : ℝ) :=
      lacunary_nth_lower hq hstep _
    _ ≤ (N : ℝ) := by
      exact_mod_cast nth_countIn_pred_le hcount

/-- A uniformly lacunary set has at most logarithmically many positive
members up to `N`, with one constant independent of `N`. -/
lemma lacunary_countIn_eventually_le_log {A : Set ℕ} (hA : IsLacunary A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop, (countIn A N : ℝ) ≤ C * Real.log N := by
  obtain ⟨hInf, q, hq, hstep⟩ := hA
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hpow : ∀ {N : ℕ}, 0 < countIn A N →
      q ^ (countIn A N - 1) ≤ (N : ℝ) := by
    intro N hcount
    have hfirst : (1 : ℝ) ≤ (Nat.nth (· ∈ positivePart A) 0 : ℕ) := by
      exact_mod_cast nth_positivePart_pos hInf 0
    calc
      q ^ (countIn A N - 1) =
          q ^ (countIn A N - 1) * 1 := by simp
      _ ≤ q ^ (countIn A N - 1) *
          (Nat.nth (· ∈ positivePart A) 0 : ℝ) := by
        gcongr
      _ ≤ (Nat.nth (· ∈ positivePart A) (countIn A N - 1) : ℝ) :=
        lacunary_nth_lower hq hstep _
      _ ≤ (N : ℝ) := by
        exact_mod_cast nth_countIn_pred_le hcount
  let C : ℝ := 1 + (Real.log q)⁻¹
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with N hlogN
  change 1 ≤ Real.log (N : ℝ) at hlogN
  by_cases hcount0 : countIn A N = 0
  · rw [hcount0]
    norm_num
    exact mul_nonneg hC.le (zero_le_one.trans hlogN)
  · have hcount : 0 < countIn A N := Nat.pos_of_ne_zero hcount0
    have hpowN := hpow hcount
    have hlog := Real.log_le_log (pow_pos hq0 _) hpowN
    rw [Real.log_pow] at hlog
    have hpred : ((countIn A N - 1 : ℕ) : ℝ) ≤
        Real.log N / Real.log q := by
      rw [le_div_iff₀ hlogq]
      exact hlog
    have hcast : (countIn A N : ℝ) =
        ((countIn A N - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hcount0)]
      norm_num
    rw [hcast]
    dsimp [C]
    calc
      ((countIn A N - 1 : ℕ) : ℝ) + 1 ≤
          Real.log N / Real.log q + 1 := by
        simpa [add_comm] using add_le_add_right hpred 1
      _ ≤ (1 + (Real.log q)⁻¹) * Real.log N := by
        rw [add_mul, one_mul, inv_mul_eq_div]
        linarith

private lemma lacunary_nth_lower_from {A : Set ℕ} {q : ℝ} (hq : 1 < q)
    (hstep : ∀ i : ℕ,
      q * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
        (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ)) (i k : ℕ) :
    q ^ k * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
      (Nat.nth (· ∈ positivePart A) (i + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        q ^ (k + 1) * (Nat.nth (· ∈ positivePart A) i : ℝ) =
            q * (q ^ k * (Nat.nth (· ∈ positivePart A) i : ℝ)) := by ring
        _ ≤ q * (Nat.nth (· ∈ positivePart A) (i + k) : ℝ) :=
          mul_le_mul_of_nonneg_left ih (le_of_lt (zero_lt_one.trans hq))
        _ ≤ (Nat.nth (· ∈ positivePart A) (i + k + 1) : ℝ) := hstep (i + k)
        _ = (Nat.nth (· ∈ positivePart A) (i + (k + 1)) : ℝ) := by
          rw [Nat.add_assoc]

/-- A uniformly lacunary set has only linearly many members in a dyadic shell.
The constant is independent of `P`, `N`, and the number `j` of doublings. -/
lemma lacunary_shell_card_le {A : Set ℕ} (hA : IsLacunary A) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ ⦃P N j : ℕ⦄, 1 ≤ P → N ≤ 2 ^ j * P →
        #{a ∈ Finset.Ioc P N | a ∈ A} ≤ K * j + 1 := by
  obtain ⟨hInf, q, hq, hstep⟩ := hA
  have hevPow : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ≤ q ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hq).eventually_ge_atTop 2
  have hevK : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
  obtain ⟨K, hK, hKpow⟩ : ∃ K : ℕ, 1 ≤ K ∧ (2 : ℝ) ≤ q ^ K := by
    exact (hevK.and hevPow).exists
  refine ⟨K, hK, ?_⟩
  intro P N j hP hN
  by_cases hPN : P ≤ N
  · let sP := (Finset.Ioc 0 P).filter (· ∈ A)
    let sN := (Finset.Ioc 0 N).filter (· ∈ A)
    let s := (Finset.Ioc P N).filter (· ∈ A)
    have hsPsub : sP ⊆ sN := by
      intro a ha
      simp only [sP, sN, Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
      exact ⟨⟨ha.1.1, ha.1.2.trans hPN⟩, ha.2⟩
    have hsEq : s = sN \ sP := by
      ext a
      simp only [s, sN, sP, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
      by_cases ha : a ∈ A <;> simp [ha] <;> omega
    have hcard : s.card + countIn A P = countIn A N := by
      rw [countIn, countIn, hsEq]
      exact Finset.card_sdiff_add_card_eq_card hsPsub
    by_contra hle
    have hlarge : K * j + 1 < s.card := Nat.lt_of_not_ge hle
    have hidx : countIn A P + K * j < countIn A N := by omega
    have hfirst : P < Nat.nth (· ∈ positivePart A) (countIn A P) := by
      have h := Nat.le_nth_count hInf (P + 1)
      have hcount : Nat.count (fun n => 0 < n ∧ n ∈ A) (P + 1) =
          countIn A P := by
        rw [Nat.count_eq_card_filter_range, countIn]
        congr 1
        ext a
        by_cases ha : a ∈ A <;> simp [ha] <;> omega
      rw [hcount] at h
      exact Nat.lt_of_succ_le (by simpa [positivePart] using h)
    have hlast : Nat.nth (· ∈ positivePart A) (countIn A P + K * j) ≤ N := by
      have hlt : countIn A P + K * j <
          Nat.count (· ∈ positivePart A) (N + 1) := by
        rwa [← countIn_eq_count_positivePart]
      exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hlt)
    have hpow : (2 : ℝ) ^ j ≤ q ^ (K * j) := by
      calc
        (2 : ℝ) ^ j ≤ (q ^ K) ^ j := by gcongr
        _ = q ^ (K * j) := by rw [pow_mul]
    have hstrict : (2 : ℝ) ^ j * (P : ℝ) <
        q ^ (K * j) *
          (Nat.nth (· ∈ positivePart A) (countIn A P) : ℝ) := by
      calc
        (2 : ℝ) ^ j * (P : ℝ) <
            (2 : ℝ) ^ j *
              (Nat.nth (· ∈ positivePart A) (countIn A P) : ℝ) := by
          apply mul_lt_mul_of_pos_left _ (pow_pos (by norm_num) _)
          exact_mod_cast hfirst
        _ ≤ q ^ (K * j) *
              (Nat.nth (· ∈ positivePart A) (countIn A P) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    have hiter := lacunary_nth_lower_from hq hstep (countIn A P) (K * j)
    have hlastR :
        (Nat.nth (· ∈ positivePart A) (countIn A P + K * j) : ℝ) ≤ N := by
      exact_mod_cast hlast
    have hNR : (N : ℝ) ≤ (2 : ℝ) ^ j * (P : ℝ) := by
      exact_mod_cast hN
    linarith
  · have hNP : N ≤ P := by omega
    rw [Finset.Ioc_eq_empty_of_le hNP]
    simp

/-- Fattening a lacunary set by `[0,P]` has a polynomial-times-shell cardinal
bound inside `[1,N]`. -/
lemma lacunary_fattening_ncard_le {A : Set ℕ} {K P N j : ℕ}
    (hshell : #{a ∈ Finset.Ioc P N | a ∈ A} ≤ K * j + 1) :
    ((A + Set.Icc 0 P) ∩ Set.Icc 1 N).ncard ≤
      2 * P + 1 + (K * j + 1) * (P + 1) := by
  let sSmall := Finset.Icc 0 (2 * P)
  let sShell := (Finset.Ioc P N).filter (· ∈ A)
  let sB := Finset.Icc 0 P
  have hsub : (A + Set.Icc 0 P) ∩ Set.Icc 1 N ⊆
      (sSmall ∪ Finset.image₂ (· + ·) sShell sB : Finset ℕ) := by
    rintro x ⟨hx, hxN⟩
    rw [Set.mem_add] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    simp only [Set.mem_Icc] at hb hxN
    rw [Finset.mem_coe, Finset.mem_union]
    by_cases haP : a ≤ P
    · left
      simp only [sSmall, Finset.mem_Icc]
      omega
    · right
      rw [Finset.mem_image₂]
      refine ⟨a, ?_, b, ?_, hab⟩
      · simp only [sShell, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨Nat.lt_of_not_ge haP, ?_⟩, ha⟩
        omega
      · simpa [sB] using hb
  calc
    ((A + Set.Icc 0 P) ∩ Set.Icc 1 N).ncard ≤
        ((sSmall ∪ Finset.image₂ (· + ·) sShell sB : Finset ℕ) : Set ℕ).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (sSmall ∪ Finset.image₂ (· + ·) sShell sB).card :=
      Set.ncard_coe_finset _
    _ ≤ sSmall.card + (Finset.image₂ (· + ·) sShell sB).card :=
      Finset.card_union_le _ _
    _ ≤ sSmall.card + sShell.card * sB.card := by
      gcongr
      exact Finset.card_image₂_le _ _ _
    _ ≤ (2 * P + 1) + (K * j + 1) * (P + 1) := by
      gcongr
      · simp [sSmall]
      · simp [sB]

/-- One lacunarity-dependent integer controls both dyadic shells and their
fattening by `[0,P]`. -/
lemma lacunary_shell_and_fattening_bounds {A : Set ℕ} (hA : IsLacunary A) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ ⦃P N j : ℕ⦄, 1 ≤ P → N ≤ 2 ^ j * P →
        #{a ∈ Finset.Ioc P N | a ∈ A} ≤ K * j + 1 ∧
        ((A + Set.Icc 0 P) ∩ Set.Icc 1 N).ncard ≤
          2 * P + 1 + (K * j + 1) * (P + 1) := by
  obtain ⟨K, hK, hshell⟩ := lacunary_shell_card_le hA
  refine ⟨K, hK, ?_⟩
  intro P N j hP hN
  have hs := hshell hP hN
  exact ⟨hs, lacunary_fattening_ncard_le hs⟩

/-- A cofinal lower bound for a monotone counting function yields a translate
whose every nonempty increment has the prescribed smaller density.  This is
the abstract form of the density-tail lemma used in the block gluing
argument. -/
lemma exists_shift_increment_lower_bound_of_eventually
    (c : ℕ → ℕ) (hc : Monotone c) (hc0 : c 0 = 0)
    {α β : ℝ} (hαβ : α < β)
    (hβ : ∀ᶠ n : ℕ in atTop, β * (n : ℝ) ≤ (c n : ℝ)) :
    ∃ t : ℕ, ∀ m : ℕ, 0 < m →
      α * (m : ℝ) ≤ ((c (t + m) - c t : ℕ) : ℝ) := by
  by_contra hgood
  push Not at hgood
  choose gap hgap_pos hgap_bad using hgood
  let endpoint : ℕ → ℕ := fun k ↦
    Nat.rec 0 (fun _ t ↦ t + gap t) k
  have endpoint_zero : endpoint 0 = 0 := by
    simp [endpoint]
  have endpoint_succ (k : ℕ) :
      endpoint (k + 1) = endpoint k + gap (endpoint k) := by
    simp [endpoint]
  have endpoint_strict (k : ℕ) : endpoint k < endpoint (k + 1) := by
    rw [endpoint_succ]
    exact Nat.lt_add_of_pos_right (hgap_pos (endpoint k))
  have index_le_endpoint (k : ℕ) : k ≤ endpoint k := by
    induction k with
    | zero => simp [endpoint_zero]
    | succ k ih =>
        have hstep := endpoint_strict k
        omega
  have count_endpoint_le (k : ℕ) :
      (c (endpoint k) : ℝ) ≤ α * Nat.cast (endpoint k) := by
    induction k with
    | zero => simp [endpoint_zero, hc0]
    | succ k ih =>
        have hmono : c (endpoint k) ≤ c (endpoint (k + 1)) :=
          hc (Nat.le_of_lt (endpoint_strict k))
        calc
          (c (endpoint (k + 1)) : ℝ) =
              (c (endpoint k) : ℝ) +
                ((c (endpoint (k + 1)) - c (endpoint k) : ℕ) : ℝ) := by
            rw [← Nat.cast_add, Nat.add_sub_of_le hmono]
          _ ≤ α * Nat.cast (endpoint k) +
                α * (gap (endpoint k) : ℝ) := by
            exact add_le_add ih (le_of_lt (by
              simpa [endpoint_succ] using hgap_bad (endpoint k)))
          _ = α * (endpoint (k + 1) : ℝ) := by
            rw [endpoint_succ]
            push_cast
            ring
  obtain ⟨N, hN⟩ := eventually_atTop.1 hβ
  let k := N + 1
  have hkN : N ≤ endpoint k := le_trans (by omega) (index_le_endpoint k)
  have hkpos : 0 < endpoint k := lt_of_lt_of_le (by omega) (index_le_endpoint k)
  have hlower := hN (endpoint k) hkN
  have hupper := count_endpoint_le k
  have hcastpos : (0 : ℝ) < Nat.cast (endpoint k) := by exact_mod_cast hkpos
  nlinarith

/-- The positive counting function is monotone in its endpoint. -/
lemma countIn_monotone (D : Set ℕ) : Monotone (countIn D) := by
  intro m n hmn
  unfold countIn
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
  exact ⟨⟨ha.1.1, ha.1.2.trans hmn⟩, ha.2⟩

/-- The abstract density-tail lemma specialized to the counting function of
a set of positive integers. -/
lemma exists_shift_countIn_increment_lower_bound_of_eventually
    (D : Set ℕ) {α β : ℝ} (hαβ : α < β)
    (hβ : ∀ᶠ n : ℕ in atTop, β * (n : ℝ) ≤ (countIn D n : ℝ)) :
    ∃ t : ℕ, ∀ m : ℕ, 0 < m →
      α * (m : ℝ) ≤
        ((countIn D (t + m) - countIn D t : ℕ) : ℝ) := by
  exact exists_shift_increment_lower_bound_of_eventually
    (countIn D) (countIn_monotone D) (by simp [countIn]) hαβ hβ

/-- Translate the part of `D` strictly after `t` back to the origin. -/
def translatedTail (D : Set ℕ) (t : ℕ) : Set ℕ :=
  {m | t + m ∈ D}

/-- Translation identifies the positive prefix of a translated tail with
the corresponding half-open interval of the original set. -/
lemma countIn_translatedTail_eq_card_Ioc (D : Set ℕ) (t m : ℕ) :
    countIn (translatedTail D t) m =
      #{a ∈ Finset.Ioc t (t + m) | a ∈ D} := by
  unfold countIn
  apply Finset.card_bij (fun a _ ↦ t + a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
    exact ⟨⟨Nat.lt_add_of_pos_right ha.1.1,
      Nat.add_le_add_left ha.1.2 t⟩, ha.2⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hb
    refine ⟨b - t, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hsubpos : 0 < b - t := Nat.sub_pos_of_lt hb.1.1
      have hsuble : b - t ≤ m := by omega
      have hadd : t + (b - t) = b := Nat.add_sub_of_le (Nat.le_of_lt hb.1.1)
      refine ⟨Finset.mem_Ioc.mpr ⟨hsubpos, hsuble⟩, ?_⟩
      change t + (b - t) ∈ D
      simpa [hadd] using hb.2
    · exact Nat.add_sub_of_le (Nat.le_of_lt hb.1.1)

/-- The interval count is the difference of the two prefix counts. -/
lemma card_filter_Ioc_eq_countIn_sub (D : Set ℕ) (t m : ℕ) :
    #{a ∈ Finset.Ioc t (t + m) | a ∈ D} =
      countIn D (t + m) - countIn D t := by
  let low := (Finset.Ioc 0 t).filter (· ∈ D)
  let step := (Finset.Ioc t (t + m)).filter (· ∈ D)
  let high := (Finset.Ioc 0 (t + m)).filter (· ∈ D)
  have hunion : low ∪ step = high := by
    ext a
    simp only [low, step, high, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨ha0, hat⟩, haD⟩ | ⟨⟨hat, hatm⟩, haD⟩)
      · exact ⟨⟨ha0, hat.trans (Nat.le_add_right t m)⟩, haD⟩
      · exact ⟨⟨lt_of_le_of_lt (Nat.zero_le t) hat, hatm⟩, haD⟩
    · rintro ⟨⟨ha0, hatm⟩, haD⟩
      by_cases hat : a ≤ t
      · exact Or.inl ⟨⟨ha0, hat⟩, haD⟩
      · exact Or.inr ⟨⟨Nat.lt_of_not_ge hat, hatm⟩, haD⟩
  have hdisjoint : Disjoint low step := by
    rw [Finset.disjoint_left]
    intro a halow hastep
    simp only [low, step, Finset.mem_filter, Finset.mem_Ioc] at halow hastep
    omega
  have hcard : high.card = low.card + step.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisjoint]
  change step.card = high.card - low.card
  omega

/-- Counting a translated tail is exactly a difference of prefix counts. -/
lemma countIn_translatedTail (D : Set ℕ) (t m : ℕ) :
    countIn (translatedTail D t) m =
      countIn D (t + m) - countIn D t := by
  rw [countIn_translatedTail_eq_card_Ioc, card_filter_Ioc_eq_countIn_sub]

/-- Translating a tail back into `D` injects every bounded element of its
sumset with `A` into a slightly longer prefix of `A + D`. -/
lemma countIn_add_translatedTail_le (A D : Set ℕ) (t n : ℕ) :
    countIn (A + translatedTail D t) n ≤ countIn (A + D) (t + n) := by
  unfold countIn
  apply Finset.card_le_card_of_injOn (fun x : ℕ ↦ t + x)
  · intro x hx
    change x ∈ (Finset.Ioc 0 n).filter (· ∈ A + translatedTail D t) at hx
    change t + x ∈ (Finset.Ioc 0 (t + n)).filter (· ∈ A + D)
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    refine ⟨⟨Nat.add_pos_right t hx.1.1, Nat.add_le_add_left hx.1.2 t⟩, ?_⟩
    simp only [Set.mem_add] at hx ⊢
    obtain ⟨a, ha, e, he, hae⟩ := hx.2
    refine ⟨a, ha, t + e, ?_, ?_⟩
    · simpa [translatedTail] using he
    · omega
  · intro x hx y hy hxy
    exact Nat.add_left_cancel hxy

/-- Density-tail lemma in the form used by block gluing: after a suitable
translation, every positive prefix has density at least `α`. -/
lemma exists_translatedTail_schnirelmann_lower_bound_of_eventually
    (D : Set ℕ) {α β : ℝ} (hαβ : α < β)
    (hβ : ∀ᶠ n : ℕ in atTop, β * (n : ℝ) ≤ (countIn D n : ℝ)) :
    ∃ t : ℕ, ∀ m : ℕ, 0 < m →
      α * (m : ℝ) ≤ (countIn (translatedTail D t) m : ℝ) := by
  obtain ⟨t, ht⟩ :=
    exists_shift_countIn_increment_lower_bound_of_eventually D hαβ hβ
  refine ⟨t, fun m hm ↦ ?_⟩
  simpa [countIn_translatedTail] using ht m hm

/-- A set of lower density `δ` has a translated tail whose every positive
prefix has any prescribed density strictly below `δ`. -/
lemma exists_translatedTail_prefix_lower_of_hasLowerDensity
    (D : Set ℕ) {α δ : ℝ} (hD : HasLowerDensity D δ) (hαδ : α < δ) :
    ∃ t : ℕ, ∀ m : ℕ, 0 < m →
      α * (m : ℝ) ≤ (countIn (translatedTail D t) m : ℝ) := by
  let β := (α + δ) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβδ : β < δ := by dsimp [β]; linarith
  exact exists_translatedTail_schnirelmann_lower_bound_of_eventually
    D hαβ (hD.eventually_lower hβδ)

/-! ### Simultaneous Dirichlet approximation -/

private def dirichletBox {E : Type*} (α : E → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (m : ℕ) (e : E) : Fin Q :=
  ⟨⌊Int.fract ((m : ℝ) * α e) * Q⌋₊, by
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _))]
    have hfract := Int.fract_lt_one ((m : ℝ) * α e)
    have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    nlinarith⟩

private lemma abs_fract_sub_le_inv_of_box_eq {E : Type*} (α : E → ℝ)
    (Q : ℕ) (hQ : 0 < Q) {a b : ℕ} {e : E}
    (hbox : dirichletBox α Q hQ a e = dirichletBox α Q hQ b e) :
    |Int.fract ((b : ℝ) * α e) - Int.fract ((a : ℝ) * α e)| ≤ (1 : ℝ) / Q := by
  have hfloor :
      ⌊Int.fract ((a : ℝ) * α e) * Q⌋₊ =
        ⌊Int.fract ((b : ℝ) * α e) * Q⌋₊ := by
    exact congrArg Fin.val hbox
  have ha0 : 0 ≤ Int.fract ((a : ℝ) * α e) * (Q : ℝ) :=
    mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _)
  have hb0 : 0 ≤ Int.fract ((b : ℝ) * α e) * (Q : ℝ) :=
    mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _)
  have haL :
      (⌊Int.fract ((a : ℝ) * α e) * Q⌋₊ : ℝ) ≤
        Int.fract ((a : ℝ) * α e) * Q :=
    Nat.floor_le ha0
  have hbL :
      (⌊Int.fract ((b : ℝ) * α e) * Q⌋₊ : ℝ) ≤
        Int.fract ((b : ℝ) * α e) * Q :=
    Nat.floor_le hb0
  have haU :
      Int.fract ((a : ℝ) * α e) * Q <
        (⌊Int.fract ((a : ℝ) * α e) * Q⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((a : ℝ) * α e) * Q)
  have hbU :
      Int.fract ((b : ℝ) * α e) * Q <
        (⌊Int.fract ((b : ℝ) * α e) * Q⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((b : ℝ) * α e) * Q)
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hab :
      Int.fract ((a : ℝ) * α e) - Int.fract ((b : ℝ) * α e) ≤ (1 : ℝ) / Q := by
    apply (le_div_iff₀ hQr).2
    rw [← hfloor] at hbL hbU
    nlinarith
  have hba :
      Int.fract ((b : ℝ) * α e) - Int.fract ((a : ℝ) * α e) ≤ (1 : ℝ) / Q := by
    apply (le_div_iff₀ hQr).2
    rw [hfloor] at haL haU
    nlinarith
  exact abs_le.mpr ⟨by linarith, hba⟩

/-- Simultaneous Dirichlet approximation for finitely many real frequencies.

For a positive integer `Q` and a finite family `α`, there is a positive integer
`u ≤ Q ^ |E|` such that every `u * α e` lies within `1 / Q` of an integer. -/
theorem simultaneous_dirichlet {E : Type*} [Fintype E] (α : E → ℝ)
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ Q ^ Fintype.card E ∧
      ∀ e, ∃ z : ℤ, |(u : ℝ) * α e - z| ≤ (1 : ℝ) / Q := by
  classical
  let f : Fin (Q ^ Fintype.card E + 1) → (E → Fin Q) :=
    fun m e ↦ dirichletBox α Q hQ m e
  have hcard :
      Fintype.card (E → Fin Q) < Fintype.card (Fin (Q ^ Fintype.card E + 1)) := by
    simp [Fintype.card_pi, Finset.prod_const]
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · refine ⟨y - x, Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hxy_lt), ?_, ?_⟩
    · exact (Nat.sub_le y x).trans (Nat.le_of_lt_succ y.isLt)
    · intro e
      let z : ℤ := ⌊(y : ℝ) * α e⌋ - ⌊(x : ℝ) * α e⌋
      refine ⟨z, ?_⟩
      have hbox : dirichletBox α Q hQ x e = dirichletBox α Q hQ y e :=
        congrFun hf e
      have hfract := abs_fract_sub_le_inv_of_box_eq α Q hQ hbox
      have hxdecomp := Int.fract_add_floor ((x : ℝ) * α e)
      have hydecomp := Int.fract_add_floor ((y : ℝ) * α e)
      dsimp [z]
      have heq :
          ((y - x : ℕ) : ℝ) * α e -
              (↑(⌊(y : ℝ) * α e⌋ - ⌊(x : ℝ) * α e⌋) : ℝ) =
            Int.fract ((y : ℝ) * α e) - Int.fract ((x : ℝ) * α e) := by
        rw [Nat.cast_sub hxy_lt.le]
        push_cast
        linarith
      rw [heq]
      exact hfract
  · refine ⟨x - y, Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hyx_lt), ?_, ?_⟩
    · exact (Nat.sub_le x y).trans (Nat.le_of_lt_succ x.isLt)
    · intro e
      let z : ℤ := ⌊(x : ℝ) * α e⌋ - ⌊(y : ℝ) * α e⌋
      refine ⟨z, ?_⟩
      have hbox : dirichletBox α Q hQ y e = dirichletBox α Q hQ x e :=
        (congrFun hf e).symm
      have hfract := abs_fract_sub_le_inv_of_box_eq α Q hQ hbox
      have hxdecomp := Int.fract_add_floor ((x : ℝ) * α e)
      have hydecomp := Int.fract_add_floor ((y : ℝ) * α e)
      dsimp [z]
      have heq :
          ((x - y : ℕ) : ℝ) * α e -
              (↑(⌊(x : ℝ) * α e⌋ - ⌊(y : ℝ) * α e⌋) : ℝ) =
            Int.fract ((x : ℝ) * α e) - Int.fract ((y : ℝ) * α e) := by
        rw [Nat.cast_sub hyx_lt.le]
        push_cast
        linarith
      rw [heq]
      exact hfract

/-! ### Fourth moment of the standard Gaussian -/

/-- The standard centered real Gaussian has fourth moment equal to three. -/
lemma standardGaussian_fourthMoment :
    ∫ x : ℝ, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1 = 3 := by
  change ∫ x : ℝ, ((fun x : ℝ ↦ x) ^ 4) x
      ∂ProbabilityTheory.gaussianReal 0 1 = 3
  rw [← ProbabilityTheory.iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x)
    (by simp : 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun x : ℝ ↦ x) (ProbabilityTheory.gaussianReal 0 1))) 4]
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  have h₁ : deriv (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t ↦ t * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_div_const, deriv_fun_pow (by fun_prop) 2, deriv_id'']
    ring
  rw [h₁]
  have h₂ : deriv (fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
    rw [deriv_id'', deriv_div_const, deriv_fun_pow (by fun_prop) 2, deriv_id'']
    ring
  rw [h₂]
  have h₃ : deriv (fun t : ℝ ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const,
      deriv_fun_pow (by fun_prop) 2, deriv_id'', deriv_div_const,
      deriv_fun_pow (by fun_prop) 2, deriv_id'']
    ring
  rw [h₃]
  have h₄ : deriv (fun t : ℝ ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop),
      deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const, deriv_id'',
      deriv_fun_pow (by fun_prop) 3, deriv_id'', deriv_div_const,
      deriv_fun_pow (by fun_prop) 2, deriv_id'']
    ring
  rw [h₄]
  norm_num

/-- The standard centered real Gaussian has second moment one. -/
lemma standardGaussian_secondMoment :
    ∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 1 := by
  have h := ProbabilityTheory.variance_fun_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable,
    ProbabilityTheory.integral_id_gaussianReal] at h
  simpa using h

/-- The first absolute moment of the standard centered real Gaussian is at most one. -/
lemma standardGaussian_absMoment_le_one :
    ∫ x : ℝ, |x| ∂ProbabilityTheory.gaussianReal 0 1 ≤ 1 := by
  have habs : MeasureTheory.Integrable (fun x : ℝ ↦ |x|)
      (ProbabilityTheory.gaussianReal 0 1) := by
    exact (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ))
      (v := (1 : ℝ≥0)) 1).integrable (by norm_num) |>.abs
  have hquad : MeasureTheory.Integrable (fun x : ℝ ↦ (x ^ 2 + 1) / 2)
      (ProbabilityTheory.gaussianReal 0 1) := by
    exact ((ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ))
      (v := (1 : ℝ≥0)) 2).integrable_sq |>.add
        (MeasureTheory.integrable_const 1)).div_const 2
  calc
    ∫ x : ℝ, |x| ∂ProbabilityTheory.gaussianReal 0 1
        ≤ ∫ x : ℝ, (x ^ 2 + 1) / 2 ∂ProbabilityTheory.gaussianReal 0 1 := by
          refine MeasureTheory.integral_mono habs hquad ?_
          intro x
          nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    _ = 1 := by
      rw [MeasureTheory.integral_div, MeasureTheory.integral_add,
        standardGaussian_secondMoment]
      · simp
      · exact (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ))
          (v := (1 : ℝ≥0)) 2).integrable_sq
      · exact MeasureTheory.integrable_const 1

/-! ### Coordinate caps for a finite standard Gaussian vector -/

namespace GaussianCoordinateCap

open MeasureTheory ProbabilityTheory

variable {I : Type*} [Fintype I]

/-- Every coordinate of a finite-dimensional standard Gaussian vector is a standard real
Gaussian. -/
lemma map_eval (i : I) :
    (stdGaussian (EuclideanSpace ℝ I)).map (fun x ↦ x i) = gaussianReal 0 1 := by
  classical
  have h := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ I)) (S := (1 : Matrix I I ℝ)) Matrix.PosSemidef.one
    (i := i)
  simpa [multivariateGaussian_zero_one] using h.map_eq

/-- The fourth power of every coordinate is integrable. -/
lemma integrable_pow_four_eval (i : I) :
    Integrable (fun x : EuclideanSpace ℝ I ↦ (x i) ^ 4)
      (stdGaussian (EuclideanSpace ℝ I)) := by
  have hreal : Integrable (fun y : ℝ ↦ y ^ 4) (gaussianReal 0 1) := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ))
      (v := (1 : ℝ≥0)) 4).integrable_norm_pow (by norm_num)
    refine h.congr ?_
    filter_upwards [] with y
    simp only [id_eq, Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hmap : Integrable (fun y : ℝ ↦ y ^ 4)
      ((stdGaussian (EuclideanSpace ℝ I)).map (fun x ↦ x i)) := by
    rwa [map_eval]
  simpa [Function.comp_def] using hmap.comp_aemeasurable (by fun_prop)

/-- Each coordinate of a finite-dimensional standard Gaussian vector has fourth moment three. -/
lemma fourthMoment_eval (i : I) :
    ∫ x : EuclideanSpace ℝ I, (x i) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ I)) = 3 := by
  calc
    ∫ x : EuclideanSpace ℝ I, (x i) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ I)) =
        ∫ y : ℝ, y ^ 4
          ∂((stdGaussian (EuclideanSpace ℝ I)).map (fun x ↦ x i)) := by
            rw [integral_map] <;> fun_prop
    _ = 3 := by rw [map_eval, standardGaussian_fourthMoment]

/-- Markov's fourth-moment bound, stated for real-valued random variables. -/
lemma fourthMoment_tail {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] (Y : X → ℝ) (hY4 : Integrable (fun x ↦ (Y x) ^ 4) P)
    (t : ℝ) (ht : 0 < t) :
    P.real {x | t < |Y x|} ≤ (∫ x, (Y x) ^ 4 ∂P) / t ^ 4 := by
  let F : X → ℝ := fun x ↦ (Y x) ^ 4 / t ^ 4
  have hF : Integrable F P := hY4.div_const _
  have hF_nonneg : 0 ≤ᵐ[P] F := by
    filter_upwards [] with x
    exact div_nonneg (by positivity) (by positivity)
  have hmeasure : P {x | t < |Y x|} ≤ ENNReal.ofReal (∫ x, F x ∂P) := by
    refine hF.measure_le_integral hF_nonneg ?_
    intro x hx
    have hpow : t ^ 4 < (Y x) ^ 4 := calc
      t ^ 4 < |Y x| ^ 4 := pow_lt_pow_left₀ hx ht.le (by norm_num)
      _ = (Y x) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    dsimp [F]
    rw [one_le_div (by positivity)]
    exact hpow.le
  have hreal : (P {x | t < |Y x|}).toReal ≤
      (ENNReal.ofReal (∫ x, F x ∂P)).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top P _) (by simp)).2 hmeasure
  have hFint_nonneg : 0 ≤ ∫ x, F x ∂P := integral_nonneg_of_ae hF_nonneg
  rw [ENNReal.toReal_ofReal hFint_nonneg] at hreal
  change (P {x | t < |Y x|}).toReal ≤ (∫ x, (Y x) ^ 4 ∂P) / t ^ 4
  simpa [F, integral_div] using hreal

/-- A union bound over all coordinates of a finite standard Gaussian vector. -/
lemma coordinateCap (M : ℝ) (hM : 0 < M) :
    (stdGaussian (EuclideanSpace ℝ I)).real
        {x | ∃ i : I, M < |x i|} ≤
      3 * Fintype.card I / M ^ 4 := by
  let P := stdGaussian (EuclideanSpace ℝ I)
  have hcoord (i : I) : P.real {x | M < |x i|} ≤ 3 / M ^ 4 := by
    calc
      P.real {x | M < |x i|} ≤ (∫ x, (x i) ^ 4 ∂P) / M ^ 4 :=
        fourthMoment_tail P (fun x ↦ x i) (integrable_pow_four_eval i) M hM
      _ = 3 / M ^ 4 := by rw [fourthMoment_eval i]
  rw [show {x : EuclideanSpace ℝ I | ∃ i : I, M < |x i|} =
      ⋃ i : I, {x | M < |x i|} by ext x; simp]
  calc
    P.real (⋃ i : I, {x | M < |x i|})
        ≤ ∑ i : I, P.real {x | M < |x i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : I, 3 / M ^ 4 := Finset.sum_le_sum fun i _hi ↦ hcoord i
    _ = 3 * Fintype.card I / M ^ 4 := by
      simp [mul_div_assoc, mul_comm]

/-- With two blocks of `m^6` Gaussian coordinates, the chance that any coordinate has
absolute value exceeding `m^2` is at most `6 / m^2`. -/
lemma coordinateCap_finSum (m : ℕ) (hm : 0 < m) :
    (stdGaussian (EuclideanSpace ℝ (Fin (m ^ 6) ⊕ Fin (m ^ 6)))).real
        {x | ∃ i : Fin (m ^ 6) ⊕ Fin (m ^ 6), (m : ℝ) ^ 2 < |x i|} ≤
      6 / (m : ℝ) ^ 2 := by
  calc
    _ ≤ 3 * Fintype.card (Fin (m ^ 6) ⊕ Fin (m ^ 6)) / ((m : ℝ) ^ 2) ^ 4 :=
      coordinateCap ((m : ℝ) ^ 2) (by positivity)
    _ = 6 / (m : ℝ) ^ 2 := by
      simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_pow]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring

end GaussianCoordinateCap

/-! ### Finite cyclic cosine orthogonality -/

/-- A primitive `N`-th root of unity. -/
def omegaPrim37 (N : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- The sum of the nontrivial powers of a primitive root vanishes. -/
lemma root_sum_zero37 (N : ℕ) (hN : 2 ≤ N) (a : ℕ) (ha0 : 0 < a) (haN : a < N) :
    ∑ d ∈ range N, omegaPrim37 N ^ (a * d) = 0 := by
  norm_num [pow_mul]
  rw [geom_sum_eq] <;> norm_num [omegaPrim37]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm,
      div_mul_cancel₀] <;>
      norm_num [show N ≠ 0 by positivity]
  · rw [← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff]
    norm_num [Complex.ext_iff, div_mul_eq_mul_div]
    intro x hx
    rw [div_eq_iff (by positivity)] at hx
    exact False.elim <|
      absurd hx <| by
        exact fun hx' => by
          exact absurd
            (Int.le_of_dvd (by positivity) <|
              show (N : ℤ) ∣ a from
                ⟨x, by
                  rw [← @Int.cast_inj ℝ]
                  push_cast
                  nlinarith [Real.pi_pos]⟩)
            (by
              norm_cast
              linarith)

/-- Full orthogonality for the finite cyclic character grid. -/
lemma root_orthogonality37 (N : ℕ) (hN : 0 < N) (a : ℤ) :
    ∑ d ∈ range N, omegaPrim37 N ^ (a * (d : ℤ)) =
      if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    norm_num [zpow_mul, omegaPrim37]
    norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hN.ne']
  · obtain ⟨q, s, hs⟩ : ∃ q s : ℤ, 0 < s ∧ s < N ∧ a = N * q + s := by
      exact
        ⟨a / N, a % N,
          lt_of_le_of_ne (Int.emod_nonneg _ (by positivity)) (Ne.symm (by aesop)),
          Int.emod_lt_of_pos _ (by positivity),
          by rw [Int.mul_ediv_add_emod]⟩
    have h_exp : ∀ d : ℕ, omegaPrim37 N ^ (a * d) = omegaPrim37 N ^ (s * d) := by
      intro d
      simp [hs, omegaPrim37]
      norm_num [zpow_add₀ (Complex.exp_ne_zero _), zpow_mul]
      norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hN.ne']
    convert root_sum_zero37 N (by linarith) s.natAbs (by omega) (by omega) using 1
    cases s <;> aesop

/-- The normalized cosine sum attached to the integer frequencies `r`. -/
def cosineCoefficient (N k : ℕ) (r : Fin k → ℤ) (d : ℕ) : ℝ :=
  (1 / (k : ℝ)) *
    ∑ j : Fin k, Real.cos (2 * Real.pi * (r j : ℝ) * (d : ℝ) / (N : ℝ))

lemma root_re_eq_cos (N : ℕ) (r : ℤ) (d : ℕ) :
    ((omegaPrim37 N) ^ (r * (d : ℤ))).re =
      Real.cos (2 * Real.pi * (r : ℝ) * (d : ℝ) / (N : ℝ)) := by
  rw [omegaPrim37]
  rw [← Complex.exp_int_mul]
  rw [Complex.exp_re]
  simp [omegaPrim37]
  ring_nf

lemma sum_cos_eq_zero (N : ℕ) (hN : 0 < N) (r : ℤ)
    (hr : ¬ (N : ℤ) ∣ r) :
    ∑ d ∈ range N,
      Real.cos (2 * Real.pi * (r : ℝ) * (d : ℝ) / (N : ℝ)) = 0 := by
  have h := root_orthogonality37 N hN r
  rw [if_neg hr] at h
  have hre :
      ∑ d ∈ range N, ((omegaPrim37 N) ^ (r * (d : ℤ))).re = 0 := by
    simpa only [map_sum, Complex.reCLM_apply, Complex.zero_re] using
      congrArg (fun z : ℂ => Complex.reCLM z) h
  simpa only [root_re_eq_cos] using hre

lemma two_mul_cos_mul_cos (x y : ℝ) :
    2 * Real.cos x * Real.cos y = Real.cos (x + y) + Real.cos (x - y) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Exact second moment of a normalized cosine sum. The first condition says
the frequencies are distinct modulo `N`; the second rules out every opposite
pair modulo `N`, including a self-opposite frequency. -/
theorem cosineCoefficient_sq_sum
    (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (r : Fin k → ℤ)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    ∑ d ∈ range N, cosineCoefficient N k r d ^ 2 =
      (N : ℝ) / (2 * (k : ℝ)) := by
  let angle (i : Fin k) (d : ℕ) : ℝ :=
    2 * Real.pi * (r i : ℝ) * (d : ℝ) / (N : ℝ)
  have hpair (i j : Fin k) :
      ∑ d ∈ range N, Real.cos (angle i d) * Real.cos (angle j d) =
        if i = j then (N : ℝ) / 2 else 0 := by
    have hprod (d : ℕ) :
        2 * Real.cos (angle i d) * Real.cos (angle j d) =
          Real.cos (2 * Real.pi * ((r i + r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) +
          Real.cos (2 * Real.pi * ((r i - r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) := by
      convert two_mul_cos_mul_cos (angle i d) (angle j d) using 1 <;>
        simp only [angle] <;> push_cast <;> ring
    have hplus :
        ∑ d ∈ range N,
          Real.cos (2 * Real.pi * ((r i + r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) = 0 :=
      sum_cos_eq_zero N hN (r i + r j) (hadd i j)
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have htwice :
          2 * (∑ d ∈ range N, Real.cos (angle i d) * Real.cos (angle i d)) =
            (N : ℝ) := by
        calc
          2 * (∑ d ∈ range N, Real.cos (angle i d) * Real.cos (angle i d)) =
              ∑ d ∈ range N,
                (2 * Real.cos (angle i d) * Real.cos (angle i d)) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun d _ => by ring
          _ = ∑ d ∈ range N,
                (Real.cos
                    (2 * Real.pi * ((r i + r i : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) +
                 Real.cos
                    (2 * Real.pi * ((r i - r i : ℤ) : ℝ) * (d : ℝ) / (N : ℝ))) := by
                  exact Finset.sum_congr rfl fun d _ => hprod d
          _ = (N : ℝ) := by
                  rw [Finset.sum_add_distrib, hplus]
                  simp
      linarith
    · rw [if_neg hij]
      have hminus : ¬ (N : ℤ) ∣ r i - r j := by
        intro hdiv
        exact hij ((hsub i j).mp hdiv)
      have hminus_sum :
          ∑ d ∈ range N,
            Real.cos (2 * Real.pi * ((r i - r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) = 0 :=
        sum_cos_eq_zero N hN (r i - r j) hminus
      have htwice :
          2 * (∑ d ∈ range N, Real.cos (angle i d) * Real.cos (angle j d)) = 0 := by
        calc
          2 * (∑ d ∈ range N, Real.cos (angle i d) * Real.cos (angle j d)) =
              ∑ d ∈ range N,
                (2 * Real.cos (angle i d) * Real.cos (angle j d)) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun d _ => by ring
          _ = ∑ d ∈ range N,
                (Real.cos
                    (2 * Real.pi * ((r i + r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ)) +
                 Real.cos
                    (2 * Real.pi * ((r i - r j : ℤ) : ℝ) * (d : ℝ) / (N : ℝ))) := by
                  exact Finset.sum_congr rfl fun d _ => hprod d
          _ = 0 := by rw [Finset.sum_add_distrib, hplus, hminus_sum, add_zero]
      linarith
  have hsq (d : ℕ) :
      (∑ i : Fin k, Real.cos (angle i d)) ^ 2 =
        ∑ i : Fin k, ∑ j : Fin k,
          Real.cos (angle i d) * Real.cos (angle j d) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  unfold cosineCoefficient
  change
    ∑ d ∈ range N,
      ((1 / (k : ℝ)) * ∑ j : Fin k, Real.cos (angle j d)) ^ 2 = _
  calc
    ∑ d ∈ range N,
        ((1 / (k : ℝ)) * ∑ j : Fin k, Real.cos (angle j d)) ^ 2 =
        (1 / (k : ℝ)) ^ 2 *
          ∑ d ∈ range N, ∑ i : Fin k, ∑ j : Fin k,
            Real.cos (angle i d) * Real.cos (angle j d) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun d _ => by rw [mul_pow, hsq]
    _ = (1 / (k : ℝ)) ^ 2 *
          ∑ i : Fin k, ∑ j : Fin k, ∑ d ∈ range N,
            Real.cos (angle i d) * Real.cos (angle j d) := by
              congr 1
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = (1 / (k : ℝ)) ^ 2 *
          ∑ i : Fin k, ∑ j : Fin k,
            (if i = j then (N : ℝ) / 2 else 0) := by
              congr 1
              exact Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun j _ => hpair i j
    _ = (N : ℝ) / (2 * (k : ℝ)) := by
      simp
      field_simp

theorem cosineCoefficient_sq_average
    (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (r : Fin k → ℤ)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    (∑ d ∈ range N, cosineCoefficient N k r d ^ 2) / (N : ℝ) =
      1 / (2 * (k : ℝ)) := by
  rw [cosineCoefficient_sq_sum N k hN hk r hsub hadd]
  field_simp

/-- At most `2N/k` residues have normalized cosine sum above `1/2`. -/
theorem cosineCoefficient_gt_half_card
    (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (r : Fin k → ℤ)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    (((range N).filter
      (fun d => (1 / 2 : ℝ) < cosineCoefficient N k r d)).card : ℝ) ≤
      2 * (N : ℝ) / (k : ℝ) := by
  let S := (range N).filter
    (fun d => (1 / 2 : ℝ) < cosineCoefficient N k r d)
  have hquarter :
      ((S.card : ℝ) / 4) ≤ ∑ d ∈ S, cosineCoefficient N k r d ^ 2 := by
    calc
      (S.card : ℝ) / 4 = ∑ _d ∈ S, (1 / 4 : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ d ∈ S, cosineCoefficient N k r d ^ 2 := by
        exact Finset.sum_le_sum fun d hd => by
          have hd' : (1 / 2 : ℝ) < cosineCoefficient N k r d := by
            exact Finset.mem_filter.mp hd |>.2
          nlinarith
  have hsubset : S ⊆ range N := by
    intro d hd
    exact Finset.mem_filter.mp hd |>.1
  have htotal :
      ∑ d ∈ S, cosineCoefficient N k r d ^ 2 ≤
        ∑ d ∈ range N, cosineCoefficient N k r d ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => sq_nonneg _
  rw [cosineCoefficient_sq_sum N k hN hk r hsub hadd] at htotal
  change (S.card : ℝ) ≤ 2 * (N : ℝ) / (k : ℝ)
  calc
    (S.card : ℝ) = 4 * ((S.card : ℝ) / 4) := by ring
    _ ≤ 4 * ((N : ℝ) / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left (hquarter.trans htotal) (by norm_num)
    _ = 2 * (N : ℝ) / (k : ℝ) := by ring

/-! ### Euclidean score vectors -/

namespace ScoreVector

/-- The coefficient space for the `k` cosine/sine pairs in the trigonometric score. -/
abbrev ScoreSpace (k : ℕ) := EuclideanSpace ℝ (Fin k × Fin 2)

/-- The real phase at the residue represented by `x`. -/
def intPhase (N : ℕ) (r : ℤ) (x : ℕ) : ℝ :=
  2 * Real.pi * (r : ℝ) * (x : ℝ) / (N : ℝ)

/-- The vector consisting of the cosine and sine coordinates for every frequency. -/
def scoreVector (N k : ℕ) (r : Fin k → ℤ) (x : ZMod N) : ScoreSpace k :=
  WithLp.toLp 2 fun p =>
    if p.2 = 0 then Real.cos (intPhase N (r p.1) x.val)
    else Real.sin (intPhase N (r p.1) x.val)

/-- The deterministic trigonometric score obtained by pairing a coefficient vector
with `scoreVector`. -/
def trigScore (N k : ℕ) (r : Fin k → ℤ) (w : ScoreSpace k)
    (x : ZMod N) : ℝ :=
  ∑ j : Fin k,
    (w (j, 0) * Real.cos (intPhase N (r j) x.val) +
      w (j, 1) * Real.sin (intPhase N (r j) x.val))

@[simp] lemma scoreVector_apply_zero (N k : ℕ) (r : Fin k → ℤ) (x : ZMod N)
    (j : Fin k) :
    scoreVector N k r x (j, 0) = Real.cos (intPhase N (r j) x.val) := by
  simp [scoreVector]

@[simp] lemma scoreVector_apply_one (N k : ℕ) (r : Fin k → ℤ) (x : ZMod N)
    (j : Fin k) :
    scoreVector N k r x (j, 1) = Real.sin (intPhase N (r j) x.val) := by
  simp [scoreVector]

/-- Pairing with the score vector is exactly the deterministic trigonometric score. -/
theorem inner_scoreVector (N k : ℕ) (r : Fin k → ℤ) (w : ScoreSpace k)
    (x : ZMod N) :
    inner ℝ w (scoreVector N k r x) = trigScore N k r w x := by
  rw [PiLp.inner_apply]
  rw [Fintype.sum_prod_type]
  simp [trigScore, Fin.sum_univ_two, mul_comm]

/-- Reducing the residue difference modulo `N` does not change its phase cosine. -/
lemma cos_intPhase_zmod_sub (N : ℕ) [NeZero N] (r : ℤ) (x y : ZMod N) :
    Real.cos (intPhase N r y.val - intPhase N r x.val) =
      Real.cos (intPhase N r (y - x).val) := by
  have hcast :
      ((((y.val : ℤ) - (x.val : ℤ) : ℤ) : ZMod N)) =
        ((((y - x).val : ℕ) : ℤ) : ZMod N) := by
    simp
  have hdiv :
      (N : ℤ) ∣ ((y - x).val : ℤ) - ((y.val : ℤ) - (x.val : ℤ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hcast
  obtain ⟨z, hz⟩ := hdiv
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hzR :
      ((y - x).val : ℝ) - ((y.val : ℝ) - (x.val : ℝ)) = (N : ℝ) * (z : ℝ) := by
    exact_mod_cast hz
  have hdR :
      ((y - x).val : ℝ) = (y.val : ℝ) - (x.val : ℝ) + (N : ℝ) * (z : ℝ) := by
    linarith
  have hphase :
      intPhase N r (y - x).val =
        (intPhase N r y.val - intPhase N r x.val) +
          ((r * z : ℤ) : ℝ) * (2 * Real.pi) := by
    dsimp [intPhase]
    push_cast
    field_simp
    rw [hdR]
  rw [hphase, Real.cos_add_int_mul_two_pi]

lemma cos_sin_sub_sq_add (a b : ℝ) :
    (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2 =
      2 - 2 * Real.cos (a - b) := by
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

/-- The squared Euclidean separation is the variance factor used by the Gaussian score. -/
theorem norm_scoreVector_sub_sq (N k : ℕ) [NeZero N]
    (r : Fin k → ℤ) (x y : ZMod N) :
    ‖scoreVector N k r y - scoreVector N k r x‖ ^ 2 =
      2 * (k : ℝ) * (1 - cosineCoefficient N k r (y - x).val) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, scoreVector_apply_zero,
    scoreVector_apply_one]
  simp_rw [cos_sin_sub_sq_add]
  simp_rw [cos_intPhase_zmod_sub]
  unfold cosineCoefficient
  change
    (∑ j : Fin k, (2 - 2 * Real.cos (intPhase N (r j) (y - x).val))) =
      2 * (k : ℝ) *
        (1 - (1 / (k : ℝ)) *
          ∑ j : Fin k, Real.cos (intPhase N (r j) (y - x).val))
  by_cases hk : k = 0
  · subst k
    simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp

lemma cos_intPhase_one_zmod_sub_lt_one (N : ℕ) [NeZero N]
    {x y : ZMod N} (hxy : x ≠ y) :
    Real.cos (intPhase N 1 (y - x).val) < 1 := by
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hdne : (y - x).val ≠ 0 := by
    exact fun h => hsub ((ZMod.val_eq_zero (y - x)).mp h)
  have hdpos : 0 < (y - x).val := Nat.pos_of_ne_zero hdne
  have hdlt : (y - x).val < N := ZMod.val_lt _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hanglepos : 0 < intPhase N 1 (y - x).val := by
    dsimp [intPhase]
    positivity
  have hanglelt : intPhase N 1 (y - x).val < 2 * Real.pi := by
    have hdltR : ((y - x).val : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hdlt
    calc
      intPhase N 1 (y - x).val =
          (2 * Real.pi) * (((y - x).val : ℝ) / (N : ℝ)) := by
            simp [intPhase]
            ring
      _ < (2 * Real.pi) * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one hNpos).2 hdltR)
          (mul_pos (by norm_num) Real.pi_pos)
      _ = 2 * Real.pi := by ring
  have hne : Real.cos (intPhase N 1 (y - x).val) ≠ 1 := by
    intro h
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hanglelt).mp h
    exact (ne_of_gt hanglepos) hz
  exact lt_of_le_of_ne (Real.cos_le_one _) hne

/-- The first frequency `1` separates distinct cyclic residues. -/
theorem scoreVector_ne_of_first_eq_one (N k : ℕ) [NeZero N] [NeZero k]
    (r : Fin k → ℤ) (hfirst : r 0 = 1) {x y : ZMod N} (hxy : x ≠ y) :
    scoreVector N k r x ≠ scoreVector N k r y := by
  intro h
  have hc := congrArg (fun v : ScoreSpace k => v ((0 : Fin k), (0 : Fin 2))) h
  have hs := congrArg (fun v : ScoreSpace k => v ((0 : Fin k), (1 : Fin 2))) h
  simp only [scoreVector_apply_zero] at hc
  simp only [scoreVector_apply_one] at hs
  have htrig := cos_sin_sub_sq_add
    (intPhase N (r 0) y.val) (intPhase N (r 0) x.val)
  rw [cos_intPhase_zmod_sub] at htrig
  rw [hfirst] at htrig hc hs
  have hlt := cos_intPhase_one_zmod_sub_lt_one N hxy
  rw [hc, hs] at htrig
  norm_num at htrig
  linarith

theorem scoreVector_sub_ne_zero_of_first_eq_one (N k : ℕ) [NeZero N] [NeZero k]
    (r : Fin k → ℤ) (hfirst : r 0 = 1) {x y : ZMod N} (hxy : x ≠ y) :
    scoreVector N k r y - scoreVector N k r x ≠ 0 := by
  rw [sub_ne_zero]
  exact (scoreVector_ne_of_first_eq_one N k r hfirst hxy).symm

end ScoreVector

/-! ### A Gaussian interval estimate -/

/-- The density of a centered real Gaussian is bounded above by its value at the center. -/
lemma centeredGaussianPDF_le_peak (v : ℝ≥0) (x : ℝ) :
    ProbabilityTheory.gaussianPDF 0 v x ≤
      ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ := by
  rw [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal]
  apply ENNReal.ofReal_le_ofReal
  let c : ℝ := (√(2 * π * (v : ℝ)))⁻¹
  change c * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) ≤ c
  calc
    c * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) ≤ c * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
            (mul_nonneg (by norm_num) v.coe_nonneg)))
        (by dsimp [c]; positivity)
    _ = c := mul_one c

/-- The mass of a nonempty-variance centered real Gaussian on an interval of
length `W` is at most `W / √(2πv)`. -/
lemma centeredGaussian_Ioc_le {v : ℝ≥0} (hv : v ≠ 0) (a W : ℝ) (hW : 0 ≤ W) :
    ProbabilityTheory.gaussianReal 0 v (Set.Ioc a (a + W))
      ≤ ENNReal.ofReal (W / √(2 * π * (v : ℝ))) := by
  rw [ProbabilityTheory.gaussianReal_apply 0 hv]
  calc
    ∫⁻ x in Set.Ioc a (a + W), ProbabilityTheory.gaussianPDF 0 v x
        ≤ ∫⁻ _x in Set.Ioc a (a + W),
            ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ :=
      MeasureTheory.setLIntegral_mono measurable_const
        (fun x _hx ↦ centeredGaussianPDF_le_peak v x)
    _ = ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ * ENNReal.ofReal W := by
      simp [Real.volume_Ioc, hW]
    _ = ENNReal.ofReal (W / √(2 * π * (v : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (√(2 * π * (v : ℝ)))⁻¹)]
      congr 1
      ring

/-! ### Gaussian linear scores -/

namespace GaussianLinear

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {I : Type*} [Fintype I]

/-- A linear score against a standard Gaussian vector is a centered real Gaussian,
with variance the squared norm of the deterministic score vector. -/
lemma stdGaussian_map_inner (v : EuclideanSpace ℝ I) :
    (stdGaussian (EuclideanSpace ℝ I)).map (innerSL ℝ v) =
      gaussianReal 0 ⟨‖v‖ ^ 2, sq_nonneg ‖v‖⟩ := by
  rw [IsGaussian.map_eq_gaussianReal]
  change gaussianReal ((stdGaussian (EuclideanSpace ℝ I))[innerSL ℝ v])
      (Var[innerSL ℝ v; stdGaussian (EuclideanSpace ℝ I)]).toNNReal = _
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm]
  simp [Real.toNNReal_of_nonneg (sq_nonneg ‖v‖)]
  congr

/-- The probability that a standard Gaussian linear score belongs to an interval of
length `W` has the usual density-peak upper bound. -/
lemma stdGaussian_inner_Ioc_le (v : EuclideanSpace ℝ I) (hv : v ≠ 0)
    (a W : ℝ) (hW : 0 ≤ W) :
    stdGaussian (EuclideanSpace ℝ I)
        {w | ⟪v, w⟫ ∈ Set.Ioc a (a + W)} ≤
      ENNReal.ofReal (W / √(2 * π * ‖v‖ ^ 2)) := by
  let sigma2 : ℝ≥0 := ⟨‖v‖ ^ 2, sq_nonneg ‖v‖⟩
  have hsigma2 : sigma2 ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    change ‖v‖ ^ 2 ≠ 0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  change stdGaussian (EuclideanSpace ℝ I)
      ((innerSL ℝ v) ⁻¹' Set.Ioc a (a + W)) ≤ _
  rw [← Measure.map_apply (by fun_prop) measurableSet_Ioc, stdGaussian_map_inner]
  have hbound := Erdos37.centeredGaussian_Ioc_le hsigma2 a W hW
  dsimp only [sigma2] at hbound
  exact hbound

/-- A nonconstant standard Gaussian linear score hits any prescribed value with
probability zero. -/
lemma stdGaussian_inner_eq_zero (v : EuclideanSpace ℝ I) (hv : v ≠ 0) (a : ℝ) :
    stdGaussian (EuclideanSpace ℝ I) {w | ⟪v, w⟫ = a} = 0 := by
  let sigma2 : ℝ≥0 := ⟨‖v‖ ^ 2, sq_nonneg ‖v‖⟩
  have hsigma2 : sigma2 ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    change ‖v‖ ^ 2 ≠ 0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  change stdGaussian (EuclideanSpace ℝ I) ((innerSL ℝ v) ⁻¹' {a}) = 0
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton a),
    stdGaussian_map_inner]
  letI : NullSingletonClass (gaussianReal 0 sigma2) :=
    nullSingletonClass_gaussianReal hsigma2
  exact measure_singleton a

/-- Equality of two Gaussian linear scores is a zero-mass hyperplane whenever
their deterministic difference vector is nonzero. -/
lemma stdGaussian_two_scores_eq_zero (u v : EuclideanSpace ℝ I)
    (huv : u - v ≠ 0) :
    stdGaussian (EuclideanSpace ℝ I) {w | ⟪u, w⟫ = ⟪v, w⟫} = 0 := by
  have hzero := stdGaussian_inner_eq_zero (u - v) huv 0
  rw [show {w | ⟪u, w⟫ = ⟪v, w⟫} = {w | ⟪u - v, w⟫ = 0} by
    ext w
    simp only [Set.mem_setOf_eq, inner_sub_left]
    constructor
    · intro h
      rw [h, sub_self]
    · exact sub_eq_zero.mp]
  exact hzero

/-- If every off-diagonal difference in a finite family of deterministic score
vectors is nonzero, a standard Gaussian coefficient vector gives all their
linear scores distinct almost surely. -/
lemma stdGaussian_finite_score_ties_null {J : Type*} [Fintype J]
    (v : J → EuclideanSpace ℝ I)
    (hdiff : ∀ i j, i ≠ j → v i - v j ≠ 0) :
    stdGaussian (EuclideanSpace ℝ I)
        {w | ∃ i j, i ≠ j ∧ ⟪v i, w⟫ = ⟪v j, w⟫} = 0 := by
  let P := {p : J × J // p.1 ≠ p.2}
  let H : P → Set (EuclideanSpace ℝ I) := fun p ↦
    {w | ⟪v p.val.1, w⟫ = ⟪v p.val.2, w⟫}
  have hH (p : P) : stdGaussian (EuclideanSpace ℝ I) (H p) = 0 := by
    simpa [H] using stdGaussian_two_scores_eq_zero (v p.val.1) (v p.val.2)
      (hdiff p.val.1 p.val.2 p.property)
  refine measure_mono_null ?_ (measure_iUnion_null hH)
  intro w hw
  rcases hw with ⟨i, j, hij, hscore⟩
  exact Set.mem_iUnion_of_mem (⟨(i, j), hij⟩ : P) (by simpa [H] using hscore)

/-- Pairwise distinct vectors satisfy the difference-vector hypothesis in the
preceding finite-union lemma. -/
lemma stdGaussian_finite_pairwise_score_ties_null {J : Type*} [Fintype J]
    (v : J → EuclideanSpace ℝ I)
    (hv : ∀ i j, i ≠ j → v i ≠ v j) :
    stdGaussian (EuclideanSpace ℝ I)
        {w | ∃ i j, i ≠ j ∧ ⟪v i, w⟫ = ⟪v j, w⟫} = 0 := by
  exact stdGaussian_finite_score_ties_null v fun i j hij ↦
    sub_ne_zero.mpr (hv i j hij)

end GaussianLinear

/-! ## Abstract gluing bridge -/

/-- The number of elements of `C` in the half-open integer interval `(a,b]`. -/
def segmentCount (C : Set ℕ) (a b : ℕ) : ℕ :=
  #{x ∈ Finset.Ioc a b | x ∈ C}

lemma segmentCount_zero (C : Set ℕ) (n : ℕ) :
    segmentCount C 0 n = countIn C n := by
  rfl

/-- Splitting a prefix at an intermediate cutoff. -/
lemma countIn_add_segmentCount (C : Set ℕ) {a n : ℕ} (han : a ≤ n) :
    countIn C n = countIn C a + segmentCount C a n := by
  unfold countIn segmentCount
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) han, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  exact (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (d := n) le_rfl).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Splitting one finite stage at the end of its filled buffer. -/
lemma segmentCount_add_segmentCount (C : Set ℕ) {a b n : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) :
    segmentCount C a n = segmentCount C a b + segmentCount C b n := by
  unfold segmentCount
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbn, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  exact (Finset.Ioc_disjoint_Ioc_of_le (a := a) (d := n) le_rfl).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- A completely filled integer interval has its full interval cardinality. -/
lemma segmentCount_eq_sub_of_filled (C : Set ℕ) {a b : ℕ}
    (hfilled : ∀ x ∈ Finset.Ioc a b, x ∈ C) :
    segmentCount C a b = b - a := by
  unfold segmentCount
  rw [Finset.filter_true_of_mem hfilled, Nat.card_Ioc]

/-- A concrete finite-stage constructor used in the gluing argument.

The interval `(s,p]` is a completely filled buffer.  After `p`, a finite word
is only `α`-prefix-balanced, where `α ≤ δ`.  The buffer's surplus
`(1-δ)(p-s)` pays for the total possible word deficit
`(δ-α)(t-p)`.  Consequently the whole stage `(s,t]` is
`δ`-prefix-balanced at every intermediate cutoff. -/
lemma buffer_then_word_stage_balanced (C : Set ℕ) {α δ : ℝ} {s p t : ℕ}
    (hsp : s ≤ p) (_hpt : p ≤ t) (hδ : δ ≤ 1) (hαδ : α ≤ δ)
    (hbuffer : ∀ x ∈ Finset.Ioc s p, x ∈ C)
    (hword : ∀ n : ℕ, p ≤ n → n ≤ t →
      α * ((n - p : ℕ) : ℝ) ≤ (segmentCount C p n : ℝ))
    (hcomp : (δ - α) * ((t - p : ℕ) : ℝ) ≤
      (1 - δ) * ((p - s : ℕ) : ℝ)) :
    ∀ n : ℕ, s ≤ n → n ≤ t →
      δ * ((n - s : ℕ) : ℝ) ≤ (segmentCount C s n : ℝ) := by
  intro n hsn hnt
  by_cases hnp : n ≤ p
  · have hfilled : ∀ x ∈ Finset.Ioc s n, x ∈ C := by
      intro x hx
      have hx' : s < x ∧ x ≤ n := Finset.mem_Ioc.mp hx
      exact hbuffer x (Finset.mem_Ioc.mpr ⟨hx'.1, hx'.2.trans hnp⟩)
    rw [segmentCount_eq_sub_of_filled C hfilled]
    have hlen : 0 ≤ (((n - s : ℕ) : ℝ)) := by positivity
    nlinarith
  · have hpn : p ≤ n := Nat.le_of_not_ge hnp
    have hbuf : segmentCount C s p = p - s :=
      segmentCount_eq_sub_of_filled C hbuffer
    have hwordn := hword n hpn hnt
    have hcoef : 0 ≤ δ - α := sub_nonneg.mpr hαδ
    have hlength : ((n - p : ℕ) : ℝ) ≤ ((t - p : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hnt p
    have hcompn : (δ - α) * ((n - p : ℕ) : ℝ) ≤
        (1 - δ) * ((p - s : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_left hlength hcoef).trans hcomp
    have hdecomp : n - s = (p - s) + (n - p) := by omega
    rw [segmentCount_add_segmentCount C hsp hpn, hbuf, Nat.cast_add, hdecomp,
      Nat.cast_add]
    linarith

/-- A cutoff sequence whose consecutive pieces form an infinite concatenation
and whose every finite piece is prefix-balanced at level `δ`.

The stage condition only refers to a finite interval.  Thus a finite
construction may establish it separately at every stage (including a filled
buffer followed by a translated finite word). -/
structure PrefixGluingCertificate (C : Set ℕ) (δ : ℝ) where
  cut : ℕ → ℕ
  cut_zero : cut 0 = 0
  cut_strict : StrictMono cut
  stage_balanced : ∀ j n : ℕ, cut j ≤ n → n ≤ cut (j + 1) →
    δ * ((n - cut j : ℕ) : ℝ) ≤ (segmentCount C (cut j) n : ℝ)

/-- Assemble an infinite prefix-gluing certificate from a sequence of concrete
filled-buffer/finite-word stages.  This is the direct interface for a
subsequence of finite cyclic witnesses whose densities approach `δ` from
below. -/
def prefixGluingCertificate_of_bufferedWords (C : Set ℕ) (δ : ℝ)
    (cut pivot : ℕ → ℕ) (α : ℕ → ℝ)
    (hzero : cut 0 = 0) (hstrict : StrictMono cut) (hδ : δ ≤ 1)
    (hleft : ∀ j, cut j ≤ pivot j)
    (hright : ∀ j, pivot j ≤ cut (j + 1))
    (hαδ : ∀ j, α j ≤ δ)
    (hbuffer : ∀ j x, x ∈ Finset.Ioc (cut j) (pivot j) → x ∈ C)
    (hword : ∀ j n, pivot j ≤ n → n ≤ cut (j + 1) →
      α j * ((n - pivot j : ℕ) : ℝ) ≤
        (segmentCount C (pivot j) n : ℝ))
    (hcomp : ∀ j,
      (δ - α j) * ((cut (j + 1) - pivot j : ℕ) : ℝ) ≤
        (1 - δ) * ((pivot j - cut j : ℕ) : ℝ)) :
    PrefixGluingCertificate C δ where
  cut := cut
  cut_zero := hzero
  cut_strict := hstrict
  stage_balanced j n hjn hnend :=
    buffer_then_word_stage_balanced C (hleft j) (hright j) hδ (hαδ j)
      (hbuffer j) (hword j) (hcomp j) n hjn hnend

namespace PrefixGluingCertificate

variable {C : Set ℕ} {δ : ℝ} (g : PrefixGluingCertificate C δ)

lemma id_le_cut (j : ℕ) : j ≤ g.cut j := by
  induction j with
  | zero => simp [g.cut_zero]
  | succ j ih =>
      exact (Nat.succ_le_succ ih).trans (g.cut_strict (Nat.lt_succ_self j))

lemma exists_cut_ge (n : ℕ) : ∃ j : ℕ, n ≤ g.cut j := by
  exact ⟨n, g.id_le_cut n⟩

/-- Every completed stage has at least the target proportion. -/
lemma endpoint_lower (j : ℕ) :
    δ * (g.cut j : ℝ) ≤ (countIn C (g.cut j) : ℝ) := by
  induction j with
  | zero => simp [g.cut_zero, countIn]
  | succ j ih =>
      have hle : g.cut j ≤ g.cut (j + 1) := (g.cut_strict (Nat.lt_succ_self j)).le
      rw [countIn_add_segmentCount C hle, Nat.cast_add]
      have hstage := g.stage_balanced j (g.cut (j + 1)) hle le_rfl
      rw [Nat.cast_sub hle] at hstage
      linarith

include g
/-- Infinite concatenation lemma: prefix balance of every finite stage implies
prefix balance of the resulting infinite set at every positive cutoff. -/
lemma all_prefixes_lower (n : ℕ) :
    δ * (n : ℝ) ≤ (countIn C n : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [countIn]
  · let hex : ∃ k : ℕ, n ≤ g.cut k := g.exists_cut_ge n
    let k := Nat.find hex
    have hk : n ≤ g.cut k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro hkzero
      rw [hkzero, g.cut_zero] at hk
      omega
    obtain ⟨j, hkj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjn : g.cut j ≤ n := by
      by_contra h
      have hnle : n ≤ g.cut j := Nat.le_of_not_ge h
      have hmin' : Nat.find hex ≤ j := Nat.find_min' hex hnle
      have hmin : k ≤ j := by simpa [k] using hmin'
      omega
    have hk' : n ≤ g.cut (j + 1) := by simpa [hkj] using hk
    rw [countIn_add_segmentCount C hjn, Nat.cast_add]
    have hend := g.endpoint_lower j
    have hstage := g.stage_balanced j n hjn hk'
    rw [Nat.cast_sub hjn] at hstage
    linarith

end PrefixGluingCertificate

/-- Abstract endpoint input.  In the application, the finite witness bounds
the new translated word, and lacunarity bounds the old-prefix fattening; the
sum of those two bounds gives this property. -/
def HasControlledSumsetEndpoints (A C : Set ℕ) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧
    (countIn (A + C) n : ℝ) / (n : ℝ) < δ + ε

/-- Quantitative endpoint data before passing to the epsilon formulation.
`error` is exactly where the lacunary old-prefix fattening estimate is placed:
the finite word contributes the main `δ` term, while all buffer and old-prefix
effects are absorbed into an error tending to zero. -/
structure EndpointFatteningCertificate (A C : Set ℕ) (δ : ℝ) where
  endpoint : ℕ → ℕ
  endpoint_pos : ∀ j, 0 < endpoint j
  error : ℕ → ℝ
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  sumset_upper : ∀ j,
    (countIn (A + C) (endpoint j) : ℝ) / (endpoint j : ℝ) ≤ δ + error j

namespace EndpointFatteningCertificate

variable {A C : Set ℕ} {δ : ℝ} (e : EndpointFatteningCertificate A C δ)

include e
lemma hasControlledSumsetEndpoints : HasControlledSumsetEndpoints A C δ := by
  intro ε hε
  obtain ⟨j, hj⟩ := ((e.error_tendsto_zero).eventually_lt_const hε).exists
  refine ⟨e.endpoint j, e.endpoint_pos j, (e.sumset_upper j).trans_lt ?_⟩
  linarith

end EndpointFatteningCertificate

/-- Exact Schnirelmann pinning from global prefix balance and arbitrarily
accurate controlled sumset endpoints. -/
theorem schnirelmann_pinning {A C : Set ℕ} {δ : ℝ}
    (hzero : 0 ∈ A)
    (hlower : ∀ n : ℕ, δ * (n : ℝ) ≤ (countIn C n : ℝ))
    (hupper : HasControlledSumsetEndpoints A C δ) :
    sd C = δ ∧ sd (A + C) = δ := by
  have hsubset : C ⊆ A + C := by
    intro c hc
    exact ⟨0, hzero, c, hc, zero_add c⟩
  have hC_lower : δ ≤ sd C := by
    rw [le_schnirelmannDensity_iff]
    intro n hn
    rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
    exact hlower n
  have hmono : sd C ≤ sd (A + C) :=
    schnirelmannDensity_le_of_subset hsubset
  have hsum_upper : sd (A + C) ≤ δ := by
    rw [schnirelmannDensity_le_iff_forall]
    intro ε hε
    exact hupper ε hε
  constructor <;> linarith

/-- The reusable bridge used by the concatenation argument.  All infinitary
bookkeeping below the hard finite witness is discharged here: finite
prefix-balanced stages yield a genuine Schnirelmann-density witness, and the
old-prefix endpoint estimate yields equality after addition by `A`. -/
theorem schnirelmann_bridge_of_prefix_gluing {A C : Set ℕ} {δ : ℝ}
    (hzero : 0 ∈ A) (g : PrefixGluingCertificate C δ)
    (hupper : HasControlledSumsetEndpoints A C δ) :
    sd C = δ ∧ sd (A + C) = δ :=
  schnirelmann_pinning hzero (PrefixGluingCertificate.all_prefixes_lower g) hupper

/-- Version in which the lacunary fattening error is supplied as an explicit
null sequence. -/
theorem schnirelmann_bridge_of_fattening_certificate {A C : Set ℕ} {δ : ℝ}
    (hzero : 0 ∈ A) (g : PrefixGluingCertificate C δ)
    (e : EndpointFatteningCertificate A C δ) :
    sd C = δ ∧ sd (A + C) = δ :=
  schnirelmann_bridge_of_prefix_gluing hzero g
    (EndpointFatteningCertificate.hasControlledSumsetEndpoints e)

/-! ## Cyclic prefix pinning -/

namespace CyclicPrefixPinning

/-- A finite integer word of total sum zero has a cyclic rotation all of
whose prefix sums are nonnegative. -/
lemma exists_rotate_prefix_sum_nonneg (l : List ℤ) (hsum : l.sum = 0) :
    ∃ t ≤ l.length, ∀ m ≤ l.length, 0 ≤ ((l.rotate t).take m).sum := by
  let P : ℕ → ℤ := fun m => (l.take m).sum
  obtain ⟨t, htmem, hmin⟩ :=
    Finset.exists_min_image (Finset.range (l.length + 1)) P (by simp)
  have ht : t ≤ l.length := by
    simpa [Finset.mem_range] using htmem
  refine ⟨t, ht, ?_⟩
  intro m hm
  rw [List.rotate_eq_drop_append_take ht]
  by_cases hnowrap : t + m ≤ l.length
  · have hmDrop : m ≤ (l.drop t).length := by
      simp only [List.length_drop]
      omega
    rw [List.take_append_of_le_length hmDrop]
    have htmMem : t + m ∈ Finset.range (l.length + 1) := by
      simp only [Finset.mem_range]
      omega
    have h := hmin (t + m) htmMem
    change (l.take t).sum ≤ (l.take (t + m)).sum at h
    rw [List.take_add, List.sum_append] at h
    omega
  · have hmDrop : (l.drop t).length ≤ m := by
      simp only [List.length_drop]
      omega
    have hk : m - (l.length - t) ≤ t := by omega
    have hkMem : m - (l.length - t) ∈ Finset.range (l.length + 1) := by
      simp only [Finset.mem_range]
      omega
    have h := hmin (m - (l.length - t)) hkMem
    change (l.take t).sum ≤ (l.take (m - (l.length - t))).sum at h
    rw [List.take_append, List.take_of_length_le hmDrop, List.length_drop,
      List.take_take, Nat.min_eq_left hk, List.sum_append]
    have hsplit := List.sum_take_add_sum_drop l t
    rw [hsum] at hsplit
    omega

/-- Number of ones in the first `m` positions after cyclically rotating the
binary membership word of `B` by `t` positions. -/
def rotatedPrefixCount {N : ℕ} (B : Finset (Fin N)) (t m : ℕ) : ℕ :=
  ((List.finRange N).rotate t).take m |>.countP fun i => decide (i ∈ B)

private lemma countP_finRange {N : ℕ} (B : Finset (Fin N)) :
    (List.finRange N).countP (fun i => decide (i ∈ B)) = B.card := by
  classical
  rw [List.countP_eq_length_filter]
  have hnodup :
      ((List.finRange N).filter fun i => decide (i ∈ B)).Nodup :=
    (List.nodup_finRange N).filter _
  have hset :
      ((List.finRange N).filter fun i => decide (i ∈ B)).toFinset = B := by
    rw [List.toFinset_filter, List.toFinset_finRange]
    ext i
    simp
  rw [← List.toFinset_card_of_nodup hnodup, hset]

private lemma sum_membership_weights {N b : ℕ} (B : Finset (Fin N))
    (l : List (Fin N)) :
    (List.map (fun i => if i ∈ B then (N : ℤ) - (b : ℤ) else -(b : ℤ)) l).sum =
      (N : ℤ) * (l.countP (fun i => decide (i ∈ B)) : ℕ) -
        (b : ℤ) * l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
      by_cases hi : i ∈ B
      · simp [hi, ih]
        ring
      · simp [hi, ih]
        ring

/-- Cyclic prefix pinning: some rotation of any finite set's binary word has
at least its global density in every prefix. -/
theorem exists_rotation_prefix_density {N : ℕ} (B : Finset (Fin N)) :
    ∃ t ≤ N, ∀ m ≤ N,
      B.card * m ≤ N * rotatedPrefixCount B t m := by
  let l : List ℤ :=
    List.map (fun i => if i ∈ B then (N : ℤ) - (B.card : ℤ)
      else -(B.card : ℤ)) (List.finRange N)
  have hlen : l.length = N := by simp [l]
  have hsum : l.sum = 0 := by
    change (List.map (fun i => if i ∈ B then (N : ℤ) - (B.card : ℤ)
      else -(B.card : ℤ)) (List.finRange N)).sum = 0
    rw [sum_membership_weights, countP_finRange]
    simp only [List.length_finRange]
    ring
  obtain ⟨t, ht, hprefix⟩ := exists_rotate_prefix_sum_nonneg l hsum
  refine ⟨t, by simpa [hlen] using ht, ?_⟩
  intro m hm
  have h := hprefix m (by simpa [hlen] using hm)
  have hrewrite : ((l.rotate t).take m).sum =
      (N : ℤ) * (rotatedPrefixCount B t m : ℤ) - (B.card : ℤ) * m := by
    change ((List.map (fun i => if i ∈ B then (N : ℤ) - (B.card : ℤ)
      else -(B.card : ℤ)) (List.finRange N)).rotate t |>.take m).sum = _
    rw [← List.map_rotate, ← List.map_take, sum_membership_weights]
    have htakeLen : ((List.finRange N).rotate t |>.take m).length = m := by
      simp [hm]
    rw [htakeLen]
    rfl
  rw [hrewrite] at h
  change 0 ≤ (N : ℤ) * (rotatedPrefixCount B t m : ℤ) -
    (B.card : ℤ) * m at h
  omega

private def positionFinset {α : Type*} (l : List α) (p : α → Bool) :
    Finset (Fin l.length) :=
  Finset.univ.filter fun i => p (l.get i)

private lemma card_positionFinset {α : Type*} (l : List α) (p : α → Bool) :
    (positionFinset l p).card = l.countP p := by
  classical
  rw [positionFinset, Finset.card_filter]
  have hindicator : (l.map fun x => if p x then 1 else 0).sum = l.countP p := by
    induction l with
    | nil => simp
    | cons x l ih =>
        cases hpx : p x <;> simp [hpx, ih, Nat.add_comm]
  rw [Fin.sum_univ_def]
  have hmap :
      (List.finRange l.length).map (fun i => if p (l.get i) then 1 else 0) =
        l.map (fun x => if p x then 1 else 0) := by
    calc
      _ = List.map (fun x => if p x then 1 else 0)
          (List.map l.get (List.finRange l.length)) := by
            rw [List.map_map]
            rfl
      _ = _ := congrArg (List.map fun x => if p x then 1 else 0)
        (List.map_get_finRange l)
  rw [hmap]
  exact hindicator

private lemma card_positionFinset_prefix {α : Type*} (l : List α) (p : α → Bool)
    {m : ℕ} (hm : m ≤ l.length) :
    ((positionFinset l p).filter fun i => i.val < m).card = (l.take m).countP p := by
  classical
  let S := (positionFinset l p).filter fun i => i.val < m
  let T := positionFinset (l.take m) p
  have hcard : S.card = T.card := by
    apply Finset.card_bij
      (fun i hi => (⟨i.val, by simp [hm, (Finset.mem_filter.mp hi).2]⟩ :
        Fin (l.take m).length))
    · intro i hi
      simp only [T, positionFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      have hip := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      simpa using hip
    · intro i hi j hj hij
      have hv : i.val = j.val := by
        exact congrArg (fun x : Fin (l.take m).length => x.val) hij
      exact Fin.ext hv
    · intro j hj
      let i : Fin l.length := ⟨j.val, by
        have hjlt : j.val < m := by simpa [hm] using j.isLt
        exact hjlt.trans_le hm⟩
      have hiS : i ∈ S := by
        simp only [S, positionFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        have hjp := (Finset.mem_filter.mp hj).2
        constructor
        · simpa [i] using hjp
        · simpa [i, hm] using j.isLt
      exact ⟨i, hiS, Fin.ext rfl⟩
  rw [show ((positionFinset l p).filter fun i => i.val < m) = S from rfl,
    hcard, show T = positionFinset (l.take m) p from rfl, card_positionFinset]

/-- Natural-number positions at which the rotated canonical word belongs to `B`. -/
def rotatedNatFinset {N : ℕ} (B : Finset (Fin N)) (t : ℕ) : Finset ℕ :=
  (positionFinset ((List.finRange N).rotate t) (fun i => decide (i ∈ B))).image Fin.val

lemma rotatedNatFinset_subset_range {N : ℕ} (B : Finset (Fin N)) (t : ℕ) :
    rotatedNatFinset B t ⊆ Finset.range N := by
  intro x hx
  rw [rotatedNatFinset, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rw [Finset.mem_range]
  simpa using i.isLt

lemma card_rotatedNatFinset_prefix {N : ℕ} (B : Finset (Fin N)) (t : ℕ)
    {m : ℕ} (hm : m ≤ N) :
    ((rotatedNatFinset B t).filter fun x => x < m).card =
      rotatedPrefixCount B t m := by
  classical
  let l := (List.finRange N).rotate t
  let p : Fin N → Bool := fun i => decide (i ∈ B)
  have hfilter :
      ((positionFinset l p).image Fin.val).filter (fun x => x < m) =
        ((positionFinset l p).filter fun i => i.val < m).image Fin.val := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, him⟩
      exact ⟨i, ⟨hi, him⟩, rfl⟩
    · rintro ⟨i, ⟨hi, him⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, him⟩
  rw [rotatedNatFinset, show (List.finRange N).rotate t = l from rfl,
    show (fun i => decide (i ∈ B)) = p from rfl, hfilter,
    Finset.card_image_of_injective _ Fin.val_injective]
  calc
    ((positionFinset l p).filter fun i => i.val < m).card =
        (l.take m).countP p :=
      card_positionFinset_prefix l p (by simpa [l] using hm)
    _ = rotatedPrefixCount B t m := rfl

@[simp] lemma mem_rotatedNatFinset {N : ℕ} [NeZero N]
    (B : Finset (Fin N)) (t x : ℕ) :
    x ∈ rotatedNatFinset B t ↔
      x < N ∧ (⟨(x + t) % N, Nat.mod_lt _ (NeZero.pos N)⟩ : Fin N) ∈ B := by
  classical
  rw [rotatedNatFinset, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hip := (Finset.mem_filter.mp hi).2
    refine ⟨by simpa using i.isLt, ?_⟩
    simpa [List.get_rotate] using hip
  · rintro ⟨hx, hxB⟩
    let i : Fin ((List.finRange N).rotate t).length := ⟨x, by simpa using hx⟩
    refine ⟨i, ?_, by simp [i]⟩
    rw [positionFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [i, List.get_rotate] using hxB

lemma card_rotatedNatFinset {N : ℕ} (B : Finset (Fin N)) (t : ℕ) :
    (rotatedNatFinset B t).card = B.card := by
  classical
  rw [rotatedNatFinset, Finset.card_image_of_injective _ Fin.val_injective,
    card_positionFinset]
  rw [(List.rotate_perm (List.finRange N) t).countP_eq]
  exact countP_finRange B

/-- The cycle lemma returned as a genuine subset of `[0,N)`, with its
cardinality and every ordinary prefix count exposed. -/
theorem exists_rotatedNatFinset_prefix_density {N : ℕ} (B : Finset (Fin N)) :
    ∃ t ≤ N,
      (rotatedNatFinset B t).card = B.card ∧
      rotatedNatFinset B t ⊆ Finset.range N ∧
      ∀ m ≤ N, B.card * m ≤
        N * ((rotatedNatFinset B t).filter fun x => x < m).card := by
  obtain ⟨t, ht, hpref⟩ := exists_rotation_prefix_density B
  refine ⟨t, ht, card_rotatedNatFinset B t,
    rotatedNatFinset_subset_range B t, ?_⟩
  intro m hm
  rw [card_rotatedNatFinset_prefix B t hm]
  exact hpref m hm

end CyclicPrefixPinning

/-! ## Finite approximate-character recursion -/

namespace CharacterRecursion

/-- The integer frequency `r` approximates the additive character at `h`,
with denominator `N`, to accuracy `rho`. -/
def ApproxGood (N : ℕ) (rho : ℝ) (r h : ℕ) : Prop :=
  ∃ z : ℤ, |((r * h : ℕ) : ℝ) / (N : ℝ) - (z : ℝ)| ≤ rho

/-- Multiplying a good frequency by `t` multiplies the approximation error
by at most `t`. -/
lemma approxGood_mul {N u h : ℕ} {eps : ℝ} (t : ℕ)
    (hu : ApproxGood N eps u h) :
    ApproxGood N ((t : ℝ) * eps) (t * u) h := by
  rw [ApproxGood] at hu ⊢
  obtain ⟨z, hz⟩ := hu
  refine ⟨(t : ℤ) * z, ?_⟩
  push_cast
  push_cast at hz
  rw [show ((t : ℝ) * (u : ℝ)) * (h : ℝ) / (N : ℝ) -
          (t : ℝ) * (z : ℝ) =
        (t : ℝ) * ((u : ℝ) * (h : ℝ) / (N : ℝ) - (z : ℝ)) by ring]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)]
  exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg t)

lemma approxGood_mono {N r h : ℕ} {eps rho : ℝ}
    (hgood : ApproxGood N eps r h) (her : eps ≤ rho) :
    ApproxGood N rho r h := by
  obtain ⟨z, hz⟩ := hgood
  exact ⟨z, hz.trans her⟩

/-- Simultaneous Dirichlet approximation, specialized to the finite set `E`
and rewritten in the `ApproxGood` normalization. -/
lemma exists_dirichlet_approxGood (E : Finset ℕ) (N Q : ℕ) (hQ : 0 < Q) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ Q ^ E.card ∧
      ∀ h ∈ E, ApproxGood N ((1 : ℝ) / (Q : ℝ)) u h := by
  let α : (↥E) → ℝ := fun h => (h.1 : ℝ) / (N : ℝ)
  obtain ⟨u, hu1, huQ, hu⟩ := simultaneous_dirichlet α Q hQ
  refine ⟨u, hu1, ?_, ?_⟩
  · simpa using huQ
  · intro h hh
    let e : ↥E := ⟨h, hh⟩
    obtain ⟨z, hz⟩ := hu e
    refine ⟨z, ?_⟩
    convert hz using 1 <;> push_cast <;> dsimp [α, e] <;> ring

/-- Among the first `k` positive multiples of a nonzero natural `u`, one is
outside any set having fewer than `k` members. -/
lemma exists_unused_multiple {S : Finset ℕ} {k u : ℕ}
    (hS : S.card < k) (hu : 0 < u) :
    ∃ t ∈ Finset.Icc 1 k, t * u ∉ S := by
  let T := (Finset.Icc 1 k).image (fun t : ℕ => t * u)
  have hinj : Function.Injective (fun t : ℕ => t * u) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hu hab
  have hcardT : T.card = k := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  obtain ⟨x, hxT, hxS⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := T) (by simpa [hcardT])
  rw [Finset.mem_image] at hxT
  obtain ⟨t, ht, rfl⟩ := hxT
  exact ⟨t, ht, hxS⟩

/-- In a finite family of frequencies, a point is bad at most once. -/
def BadAtMostOnce (F R : Finset ℕ) (Good : ℕ → ℕ → Prop) : Prop :=
  ∀ h ∈ F, ∀ r ∈ R, ∀ s ∈ R, ¬ Good r h → ¬ Good s h → r = s

/-- A shell cardinality estimate bounds the already-bad set as soon as every
already-bad point lies in that shell. -/
lemma badSet_card_le_of_shell
    {A : Set ℕ} {F R : Finset ℕ} {Good : ℕ → ℕ → Prop}
    {P N K j : ℕ}
    (hF : ∀ h ∈ F, h ∈ A ∧ h ≤ N)
    (habove : ∀ h ∈ F, (∃ r ∈ R, ¬ Good r h) → P < h)
    (hshell : #{h ∈ Finset.Ioc P N | h ∈ A} ≤ K * j + 1) :
    (F.filter fun h => ∃ r ∈ R, ¬ Good r h).card ≤ K * j + 1 := by
  refine (Finset.card_le_card ?_).trans hshell
  intro h hh
  have hh' := Finset.mem_filter.mp hh
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ioc.mpr ⟨habove h hh'.1 hh'.2, (hF h hh'.1).2⟩,
    (hF h hh'.1).1⟩

/-- If the new frequency is good at every point that was already bad, then
the at-most-one-bad invariant is preserved. -/
lemma badAtMostOnce_insert {F R : Finset ℕ} {Good : ℕ → ℕ → Prop}
    {r : ℕ} (hR : BadAtMostOnce F R Good)
    (hnew : ∀ h ∈ F, (∃ s ∈ R, ¬ Good s h) → Good r h) :
    BadAtMostOnce F (insert r R) Good := by
  intro h hh x hx y hy hxbad hybad
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hxR
  · rcases hy with rfl | hyR
    · rfl
    · exact False.elim (hxbad (hnew h hh ⟨y, hyR, hybad⟩))
  · rcases hy with rfl | hyR
    · exact False.elim (hybad (hnew h hh ⟨x, hxR, hxbad⟩))
    · exact hR h hh x hxR y hyR hxbad hybad

/-- Finite approximate-character recursion.

`Rbound n` bounds all frequencies through stage `n`, and `Ebound n` bounds
the number of points already bad at stage `n`.  The hypotheses `hbadcard`
and `hDir` are respectively the lacunary shell estimate and simultaneous
Dirichlet approximation. -/
theorem construct_approximate_characters
    (F : Finset ℕ) (N k Q : ℕ) (rho : ℝ)
    (Ebound Rbound : ℕ → ℕ)
    (hk : 0 < k) (hQ : 1 ≤ Q)
    (hscale : (k : ℝ) / (Q : ℝ) ≤ rho)
    (hbase : 1 ≤ Rbound 1)
    (hmono : Monotone Rbound)
    (hnext : ∀ n < k, k * Q ^ Ebound n ≤ Rbound (n + 1))
    (hbadcard : ∀ (n : ℕ) (R : Finset ℕ),
      1 ≤ n → n < k → R.card = n →
      (∀ r ∈ R, r ≤ Rbound n) →
      (F.filter fun h => ∃ r ∈ R, ¬ ApproxGood N rho r h).card ≤ Ebound n)
    (hDir : ∀ E : Finset ℕ, E ⊆ F →
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ Q ^ E.card ∧
        ∀ h ∈ E, ApproxGood N ((1 : ℝ) / (Q : ℝ)) u h) :
    ∃ R : Finset ℕ,
      R.card = k ∧ 1 ∈ R ∧
      (∀ r ∈ R, 0 < r) ∧
      (∀ r ∈ R, r ≤ Rbound k) ∧
      BadAtMostOnce F R (ApproxGood N rho) := by
  have hstage : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      ∃ R : Finset ℕ,
        R.card = n ∧ 1 ∈ R ∧
        (∀ r ∈ R, 0 < r) ∧
        (∀ r ∈ R, r ≤ Rbound n) ∧
        BadAtMostOnce F R (ApproxGood N rho) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hnpos hnle
      by_cases hn0 : n = 0
      · subst n
        refine ⟨{1}, by simp, by simp, ?_, ?_, ?_⟩
        · simp
        · intro r hr
          simp only [Finset.mem_singleton] at hr
          subst r
          exact hbase
        · intro h hh r hr s hs
          simp only [Finset.mem_singleton] at hr hs
          subst r
          subst s
          simp
      · have hnpos' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hnle' : n ≤ k := by omega
        obtain ⟨R, hRcard, honeR, hRpos, hRbound, hRbad⟩ := ih hnpos' hnle'
        have hnk : n < k := by omega
        let E := F.filter fun h => ∃ r ∈ R, ¬ ApproxGood N rho r h
        have hEsub : E ⊆ F := by
          intro h hh
          exact (Finset.mem_filter.mp hh).1
        have hEcard : E.card ≤ Ebound n := by
          exact hbadcard n R hnpos' hnk hRcard hRbound
        obtain ⟨u, hu1, huQ, huGood⟩ := hDir E hEsub
        obtain ⟨t, ht, htuR⟩ :=
          exists_unused_multiple (S := R) (k := k) (u := u) (by omega) (by omega)
        have htpos : 0 < t := (Finset.mem_Icc.mp ht).1
        have htk : t ≤ k := (Finset.mem_Icc.mp ht).2
        have hnewPos : 0 < t * u := Nat.mul_pos htpos (by omega)
        have hnewGood : ∀ h ∈ F, (∃ r ∈ R, ¬ ApproxGood N rho r h) →
            ApproxGood N rho (t * u) h := by
          intro h hhF hhold
          have hhE : h ∈ E := Finset.mem_filter.mpr ⟨hhF, hhold⟩
          have hmul := approxGood_mul t (huGood h hhE)
          refine approxGood_mono hmul ?_
          calc
            (t : ℝ) * ((1 : ℝ) / (Q : ℝ)) = (t : ℝ) / (Q : ℝ) := by ring
            _ ≤ (k : ℝ) / (Q : ℝ) := by
              gcongr
            _ ≤ rho := hscale
        have hnewBound : t * u ≤ Rbound (n + 1) := by
          calc
            t * u ≤ k * Q ^ E.card := Nat.mul_le_mul htk huQ
            _ ≤ k * Q ^ Ebound n := by
              gcongr
            _ ≤ Rbound (n + 1) := hnext n hnk
        refine ⟨insert (t * u) R, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem htuR, hRcard]
        · exact Finset.mem_insert_of_mem honeR
        · intro r hr
          simp only [Finset.mem_insert] at hr
          rcases hr with rfl | hr
          · exact hnewPos
          · exact hRpos r hr
        · intro r hr
          simp only [Finset.mem_insert] at hr
          rcases hr with rfl | hr
          · exact hnewBound
          · exact (hRbound r hr).trans (hmono (by omega))
        · exact badAtMostOnce_insert hRbad hnewGood
  obtain ⟨R, hRcard, honeR, hRpos, hRbound, hRbad⟩ :=
    hstage k (by omega) le_rfl
  exact ⟨R, hRcard, honeR, hRpos, hRbound, hRbad⟩

/-! ### Lacunary instantiation of the approximate-character recursion -/

private lemma two_mul_le_two_pow_succ (D : ℕ) :
    2 * D ≤ 2 ^ (D + 1) := by
  have hD : D ≤ 2 ^ D := by
    induction D with
    | zero => simp
    | succ D ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ D := Nat.one_le_pow D 2 (by omega)
        omega
  rw [pow_succ]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hD

theorem exists_bounded_character_family_of_shell_bound
    {A : Set ℕ} (K : ℕ) (_hK : 1 ≤ K)
    (hshell : ∀ ⦃P N j : ℕ⦄, 1 ≤ P → N ≤ 2 ^ j * P →
      #{a ∈ Finset.Ioc P N | a ∈ A} ≤ K * j + 1)
    (k Q : ℕ) (rho : ℝ)
    (hk : 0 < k) (hQ : 1 ≤ Q)
    (hrho : 0 < rho)
    (hscale : (k : ℝ) / (Q : ℝ) ≤ rho) :
    ∃ Rmax N0 : ℕ, 0 < Rmax ∧ 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        ∃ R : Finset ℕ,
          R.card = k ∧ 1 ∈ R ∧
          (∀ r ∈ R, 0 < r ∧ r ≤ Rmax ∧ r < N / 2) ∧
          BadAtMostOnce
            ((Finset.Icc 1 N).filter (· ∈ A)) R (ApproxGood N rho) := by
  obtain ⟨L0, hLrho⟩ := exists_nat_one_div_lt hrho
  let L := L0 + 1
  have hL : 1 ≤ L := by simp [L]
  have hLrho' : (1 : ℝ) / (L : ℝ) ≤ rho := by
    simpa [L] using hLrho.le
  let Rbound : ℕ → ℕ := fun n => Nat.rec 1
    (fun _ r => r + k * Q ^ (K * (L * r + 1) + 1)) n
  let Ebound : ℕ → ℕ := fun n => K * (L * Rbound n + 1) + 1
  have hRbase : Rbound 0 = 1 := by simp [Rbound]
  have hRstep (n : ℕ) :
      Rbound (n + 1) =
        Rbound n + k * Q ^ (K * (L * Rbound n + 1) + 1) := by
    simp [Rbound]
  have hRmono : Monotone Rbound := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hRstep]
    omega
  have hRpos (n : ℕ) : 1 ≤ Rbound n := by
    have h := hRmono (Nat.zero_le n)
    simpa [hRbase] using h
  let Rmax := Rbound k
  let Dmax := L * Rmax
  let N0 := max (2 * (Rmax + 1)) (2 * Dmax)
  have hRmax : 0 < Rmax := hRpos k
  have hDmax : 0 < Dmax := Nat.mul_pos (by omega) hRmax
  have hN0 : 0 < N0 := by
    dsimp [N0]
    omega
  refine ⟨Rmax, N0, hRmax, hN0, ?_⟩
  intro N hN
  have hNfreq : 2 * (Rmax + 1) ≤ N :=
    (le_max_left _ _).trans hN
  have hNDmax : 2 * Dmax ≤ N :=
    (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hnext : ∀ n < k, k * Q ^ Ebound n ≤ Rbound (n + 1) := by
    intro n hn
    rw [hRstep]
    dsimp [Ebound]
    omega
  have hbadcard : ∀ (n : ℕ) (R : Finset ℕ),
      1 ≤ n → n < k → R.card = n →
      (∀ r ∈ R, r ≤ Rbound n) →
      (((Finset.Icc 1 N).filter (· ∈ A)).filter fun h =>
        ∃ r ∈ R, ¬ ApproxGood N rho r h).card ≤ Ebound n := by
    intro n R hn hnk hRcard hRbound
    let D := L * Rbound n
    let P := N / D
    let j := D + 1
    have hnle : n ≤ k := by omega
    have hRn : Rbound n ≤ Rmax := hRmono hnle
    have hDpos : 0 < D := Nat.mul_pos (by omega) (hRpos n)
    have hDle : D ≤ Dmax := by
      dsimp [D, Dmax, Rmax]
      exact Nat.mul_le_mul_left L hRn
    have htwoD : 2 * D ≤ N := by omega
    have hP : 1 ≤ P := by
      dsimp [P]
      exact (Nat.one_le_div_iff hDpos).2 (by omega)
    have hDP : D * P ≤ N := by
      dsimp [P]
      exact Nat.mul_div_le N D
    have hNlt : N < D * (P + 1) := by
      dsimp [P]
      exact Nat.lt_mul_div_succ N hDpos
    have hNtwoDP : N ≤ 2 * D * P := by
      have hPpos : 0 < P := by omega
      have haux : D * (P + 1) ≤ 2 * D * P := by nlinarith
      omega
    have hpowD : 2 * D ≤ 2 ^ j := by
      dsimp [j]
      exact two_mul_le_two_pow_succ D
    have hNshell : N ≤ 2 ^ j * P := by
      calc
        N ≤ 2 * D * P := hNtwoDP
        _ ≤ 2 ^ j * P := Nat.mul_le_mul_right P hpowD
    have hshell' :
        #{a ∈ Finset.Ioc P N | a ∈ A} ≤ K * j + 1 :=
      hshell hP hNshell
    apply badSet_card_le_of_shell
      (P := P) (N := N) (K := K) (j := j)
      (A := A) (F := (Finset.Icc 1 N).filter (· ∈ A))
      (R := R) (Good := ApproxGood N rho)
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh
      exact ⟨hh.2, hh.1.2⟩
    · intro h hhF hbad
      by_contra hnot
      have hhP : h ≤ P := by omega
      obtain ⟨r, hrR, hrbad⟩ := hbad
      have hr : r ≤ Rbound n := hRbound r hrR
      have hDh : D * h ≤ N := by
        calc
          D * h ≤ D * P := Nat.mul_le_mul_left D hhP
          _ ≤ N := hDP
      have hrhL : r * h * L ≤ N := by
        calc
          r * h * L ≤ Rbound n * h * L := by
            exact Nat.mul_le_mul_right L (Nat.mul_le_mul_right h hr)
          _ = D * h := by simp [D, Nat.mul_left_comm, Nat.mul_comm]
          _ ≤ N := hDh
      have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
      have hfrac :
          ((r * h : ℕ) : ℝ) / (N : ℝ) ≤ (1 : ℝ) / (L : ℝ) := by
        rw [div_le_div_iff₀ hNreal hLreal]
        norm_num
        exact_mod_cast hrhL
      apply hrbad
      refine ⟨0, ?_⟩
      norm_num only [Int.cast_zero, sub_zero]
      rw [abs_of_nonneg (by positivity)]
      exact hfrac.trans hLrho'
    · simpa [Ebound, D, j] using hshell'
  have hDir : ∀ E : Finset ℕ,
      E ⊆ (Finset.Icc 1 N).filter (· ∈ A) →
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ Q ^ E.card ∧
        ∀ h ∈ E, ApproxGood N ((1 : ℝ) / (Q : ℝ)) u h := by
    intro E hE
    exact exists_dirichlet_approxGood E N Q (by omega)
  obtain ⟨R, hRcard, hone, hRpos, hRbound, hbad⟩ :=
    construct_approximate_characters
      ((Finset.Icc 1 N).filter (· ∈ A)) N k Q rho Ebound Rbound
      hk hQ hscale (by simp [Rbound]) hRmono hnext hbadcard hDir
  refine ⟨R, hRcard, hone, ?_, hbad⟩
  intro r hr
  have hrpos : 0 < r := hRpos r hr
  have hrmax : r ≤ Rmax := hRbound r hr
  refine ⟨hrpos, hrmax, ?_⟩
  have hhalf : Rmax + 1 ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    simpa [Nat.mul_comm] using hNfreq
  omega

theorem exists_bounded_character_family_of_lacunary
    {A : Set ℕ} (hA : _root_.Erdos37.IsLacunary A)
    (k Q : ℕ) (rho : ℝ)
    (hk : 0 < k) (hQ : 1 ≤ Q)
    (hrho : 0 < rho)
    (hscale : (k : ℝ) / (Q : ℝ) ≤ rho) :
    ∃ Rmax N0 : ℕ, 0 < Rmax ∧ 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        ∃ R : Finset ℕ,
          R.card = k ∧ 1 ∈ R ∧
          (∀ r ∈ R, 0 < r ∧ r ≤ Rmax ∧ r < N / 2) ∧
          BadAtMostOnce
            ((Finset.Icc 1 N).filter (· ∈ A)) R (ApproxGood N rho) := by
  obtain ⟨K, hK, hshell⟩ := _root_.Erdos37.lacunary_shell_card_le hA
  exact exists_bounded_character_family_of_shell_bound K hK hshell
    k Q rho hk hQ hrho hscale

/-- Positive frequencies below half the modulus have exactly the integer
orthogonality relations needed for the finite cyclic character calculation. -/
lemma integer_orthogonality_of_positive_lt_half
    {ι : Type*} {N : ℕ} (r : ι → ℕ)
    (hrinj : Function.Injective r)
    (hrange : ∀ i, 0 < r i ∧ r i < N / 2) :
    (∀ i j, (N : ℤ) ∣ (r i : ℤ) - (r j : ℤ) ↔ i = j) ∧
    (∀ i j, ¬(N : ℤ) ∣ (r i : ℤ) + (r j : ℤ)) := by
  constructor
  · intro i j
    constructor
    · intro hdvd
      have hirN : r i < N := by
        have := (hrange i).2
        omega
      have hjrN : r j < N := by
        have := (hrange j).2
        omega
      have habs : |(r i : ℤ) - (r j : ℤ)| < (N : ℤ) := by
        exact Int.abs_sub_lt_of_lt_lt hjrN hirN
      have hzero : (r i : ℤ) - (r j : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd habs
      apply hrinj
      exact_mod_cast (Int.sub_eq_zero.mp hzero)
    · rintro rfl
      simp
  · intro i j hdvd
    have hpos : (0 : ℤ) < (r i : ℤ) + (r j : ℤ) := by
      exact_mod_cast Nat.add_pos_left (hrange i).1 (r j)
    have hlt : (r i : ℤ) + (r j : ℤ) < (N : ℤ) := by
      have hi := (hrange i).2
      have hj := (hrange j).2
      exact_mod_cast (show r i + r j < N from by omega)
    have hzero : (r i : ℤ) + (r j : ℤ) = 0 :=
      Int.eq_zero_of_dvd_of_nonneg_of_lt hpos.le hlt hdvd
    omega

/-- Indexed form of the lacunary approximate-character family.  The
frequencies are enumerated increasingly, so the distinguished frequency
`1` is the zeroth one. -/
theorem exists_indexed_character_family_of_lacunary
    {A : Set ℕ} (hA : IsLacunary A)
    (k Q : ℕ) (rho : ℝ)
    (hk : 0 < k) (hQ : 1 ≤ Q)
    (hrho : 0 < rho)
    (hscale : (k : ℝ) / (Q : ℝ) ≤ rho) :
    ∃ Rmax N0 : ℕ, 0 < Rmax ∧ 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        ∃ r : Fin k → ℕ,
          r ⟨0, hk⟩ = 1 ∧
          Function.Injective r ∧
          (∀ i, 0 < r i ∧ r i ≤ Rmax ∧ r i < N / 2) ∧
          (∀ h ∈ (Finset.Icc 1 N).filter (· ∈ A),
            (Finset.univ.filter fun i => ¬ ApproxGood N rho (r i) h).card ≤ 1) ∧
          (∀ i j, (N : ℤ) ∣ (r i : ℤ) - (r j : ℤ) ↔ i = j) ∧
          (∀ i j, ¬(N : ℤ) ∣ (r i : ℤ) + (r j : ℤ)) := by
  obtain ⟨Rmax, N0, hRmax, hN0, hfamily⟩ :=
    exists_bounded_character_family_of_lacunary hA k Q rho hk hQ hrho hscale
  refine ⟨Rmax, N0, hRmax, hN0, ?_⟩
  intro N hN
  obtain ⟨R, hRcard, hone, hRrange, hbad⟩ := hfamily N hN
  let r : Fin k → ℕ := R.orderEmbOfFin hRcard
  have hrmem (i : Fin k) : r i ∈ R := by
    exact Finset.orderEmbOfFin_mem R hRcard i
  have hrange (i : Fin k) : 0 < r i ∧ r i ≤ Rmax ∧ r i < N / 2 :=
    hRrange (r i) (hrmem i)
  have hrinj : Function.Injective r := (R.orderEmbOfFin hRcard).injective
  have hRnonempty : R.Nonempty := ⟨1, hone⟩
  have hrzero : r ⟨0, hk⟩ = 1 := by
    change R.orderEmbOfFin hRcard ⟨0, hk⟩ = 1
    rw [Finset.orderEmbOfFin_zero hRcard hk]
    apply le_antisymm
    · exact R.min'_le 1 hone
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt ((hRrange (R.min' hRnonempty) (R.min'_mem hRnonempty)).1))
  have hbadcard : ∀ h ∈ (Finset.Icc 1 N).filter (· ∈ A),
      (Finset.univ.filter fun i => ¬ ApproxGood N rho (r i) h).card ≤ 1 := by
    intro h hh
    refine Finset.card_le_one.2 ?_
    intro i hi j hj
    rw [Finset.mem_filter] at hi hj
    apply hrinj
    exact hbad h hh (r i) (hrmem i) (r j) (hrmem j) hi.2 hj.2
  obtain ⟨hdiff, hsum⟩ := integer_orthogonality_of_positive_lt_half
    r hrinj (fun i => ⟨(hrange i).1, (hrange i).2.2⟩)
  exact ⟨r, hrzero, hrinj, hrange, hbadcard, hdiff, hsum⟩

end CharacterRecursion

/-! ## Deterministic trigonometric score bounds -/

namespace DeterministicScore

open CharacterRecursion

/-- The real phase attached to the frequency `r` at the integer point `x`. -/
noncomputable def natPhase (N r x : ℕ) : ℝ :=
  2 * Real.pi * (((r * x : ℕ) : ℝ) / (N : ℝ))

/-- The niveau score with prescribed cosine and sine coefficients. -/
noncomputable def natScore {ι : Type*} [Fintype ι]
    (N : ℕ) (r : ι → ℕ) (U V : ι → ℝ) (x : ℕ) : ℝ :=
  ∑ j, (U j * Real.cos (natPhase N (r j) x) +
    V j * Real.sin (natPhase N (r j) x))

/-- `ApproxGood` says exactly that the phase increment differs from an
integer multiple of `2π` by at most `2πρ`. -/
lemma abs_natPhase_add_sub_period_le
    (N r h x : ℕ) [NeZero N] (rho : ℝ)
    (hgood : ApproxGood N rho r h) :
    ∃ z : ℤ,
      |natPhase N r (x + h) -
        (natPhase N r x + (z : ℝ) * (2 * Real.pi))| ≤ 2 * Real.pi * rho := by
  obtain ⟨z, hz⟩ := hgood
  refine ⟨z, ?_⟩
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have heq :
      natPhase N r (x + h) -
          (natPhase N r x + (z : ℝ) * (2 * Real.pi)) =
        (2 * Real.pi) * ((((r * h : ℕ) : ℝ) / (N : ℝ)) - (z : ℝ)) := by
    simp only [natPhase, Nat.cast_mul, Nat.cast_add]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left hz (by positivity)

/-- A good phase changes every cosine coordinate by at most `2πρ`. -/
lemma abs_cos_natPhase_add_sub_le
    (N r h x : ℕ) [NeZero N] (rho : ℝ)
    (hgood : ApproxGood N rho r h) :
    |Real.cos (natPhase N r (x + h)) - Real.cos (natPhase N r x)| ≤
      2 * Real.pi * rho := by
  obtain ⟨z, hz⟩ := abs_natPhase_add_sub_period_le N r h x rho hgood
  rw [← Real.cos_add_int_mul_two_pi (natPhase N r x) z]
  exact (Real.abs_cos_sub_cos_le _ _).trans hz

/-- A good phase changes every sine coordinate by at most `2πρ`. -/
lemma abs_sin_natPhase_add_sub_le
    (N r h x : ℕ) [NeZero N] (rho : ℝ)
    (hgood : ApproxGood N rho r h) :
    |Real.sin (natPhase N r (x + h)) - Real.sin (natPhase N r x)| ≤
      2 * Real.pi * rho := by
  obtain ⟨z, hz⟩ := abs_natPhase_add_sub_period_le N r h x rho hgood
  rw [← Real.sin_add_int_mul_two_pi (natPhase N r x) z]
  exact (Real.abs_sin_sub_sin_le _ _).trans hz

private lemma abs_cos_sub_le_two (u v : ℝ) :
    |Real.cos u - Real.cos v| ≤ 2 := by
  calc
    |Real.cos u - Real.cos v| ≤ |Real.cos u| + |Real.cos v| := by
      simpa [sub_eq_add_neg] using abs_add_le (Real.cos u) (-Real.cos v)
    _ ≤ 2 := by linarith [Real.abs_cos_le_one u, Real.abs_cos_le_one v]

private lemma abs_sin_sub_le_two (u v : ℝ) :
    |Real.sin u - Real.sin v| ≤ 2 := by
  calc
    |Real.sin u - Real.sin v| ≤ |Real.sin u| + |Real.sin v| := by
      simpa [sub_eq_add_neg] using abs_add_le (Real.sin u) (-Real.sin v)
    _ ≤ 2 := by linarith [Real.abs_sin_le_one u, Real.abs_sin_le_one v]

/-- Coordinate control using `2πρ` at a good frequency and the universal
bound `2` at a bad frequency. -/
lemma natPhase_coordinate_change_le
    (N r h x : ℕ) [NeZero N] (rho : ℝ) :
    |Real.cos (natPhase N r (x + h)) - Real.cos (natPhase N r x)| ≤
        (if ApproxGood N rho r h then 2 * Real.pi * rho else 2) ∧
      |Real.sin (natPhase N r (x + h)) - Real.sin (natPhase N r x)| ≤
        (if ApproxGood N rho r h then 2 * Real.pi * rho else 2) := by
  by_cases hg : ApproxGood N rho r h
  · simp only [hg, if_true]
    exact ⟨abs_cos_natPhase_add_sub_le N r h x rho hg,
      abs_sin_natPhase_add_sub_le N r h x rho hg⟩
  · simp only [hg, if_false]
    exact ⟨abs_cos_sub_le_two _ _, abs_sin_sub_le_two _ _⟩

/-- The score-change estimate under an explicit weighted good/bad budget. -/
theorem abs_natScore_add_sub_le {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ)
    (rho W : ℝ) (h x : ℕ)
    (hrho : 0 ≤ rho)
    (hbudget :
      (∑ j, (|U j| + |V j|) *
        (if ApproxGood N rho (r j) h then 2 * Real.pi * rho else 2)) ≤ W) :
    |natScore N r U V (x + h) - natScore N r U V x| ≤ W := by
  rw [natScore, natScore, ← Finset.sum_sub_distrib]
  calc
    |∑ j, ((U j * Real.cos (natPhase N (r j) (x + h)) +
          V j * Real.sin (natPhase N (r j) (x + h))) -
        (U j * Real.cos (natPhase N (r j) x) +
          V j * Real.sin (natPhase N (r j) x)))|
        ≤ ∑ j, |((U j * Real.cos (natPhase N (r j) (x + h)) +
          V j * Real.sin (natPhase N (r j) (x + h))) -
        (U j * Real.cos (natPhase N (r j) x) +
          V j * Real.sin (natPhase N (r j) x)))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (|U j| + |V j|) *
          (if ApproxGood N rho (r j) h then 2 * Real.pi * rho else 2) := by
      gcongr with j
      have hc := (natPhase_coordinate_change_le N (r j) h x rho).1
      have hs := (natPhase_coordinate_change_le N (r j) h x rho).2
      have heta : 0 ≤ (if ApproxGood N rho (r j) h then
          2 * Real.pi * rho else 2) := by
        split_ifs <;> positivity
      calc
        |(U j * Real.cos (natPhase N (r j) (x + h)) +
              V j * Real.sin (natPhase N (r j) (x + h))) -
            (U j * Real.cos (natPhase N (r j) x) +
              V j * Real.sin (natPhase N (r j) x))|
            = |U j * (Real.cos (natPhase N (r j) (x + h)) -
                  Real.cos (natPhase N (r j) x)) +
                V j * (Real.sin (natPhase N (r j) (x + h)) -
                  Real.sin (natPhase N (r j) x))| := by ring_nf
        _ ≤ |U j| * |Real.cos (natPhase N (r j) (x + h)) -
                Real.cos (natPhase N (r j) x)| +
              |V j| * |Real.sin (natPhase N (r j) (x + h)) -
                Real.sin (natPhase N (r j) x)| := by
              simpa [abs_mul] using abs_add_le
                (U j * (Real.cos (natPhase N (r j) (x + h)) -
                  Real.cos (natPhase N (r j) x)))
                (V j * (Real.sin (natPhase N (r j) (x + h)) -
                  Real.sin (natPhase N (r j) x)))
        _ ≤ |U j| * (if ApproxGood N rho (r j) h then
                2 * Real.pi * rho else 2) +
              |V j| * (if ApproxGood N rho (r j) h then
                2 * Real.pi * rho else 2) := by
              gcongr
        _ = (|U j| + |V j|) *
              (if ApproxGood N rho (r j) h then
                2 * Real.pi * rho else 2) := by ring
    _ ≤ W := hbudget

/-- Arithmetic budget for a family in which at most one phase is bad. -/
lemma weighted_phase_budget_le_of_bad_card_le_one
    {ι : Type*} [Fintype ι]
    (A : ι → ℝ) (P : ι → Prop) (g b C S : ℝ)
    (hA0 : ∀ j, 0 ≤ A j)
    (hA : ∀ j, A j ≤ C)
    (hC0 : 0 ≤ C) (hg0 : 0 ≤ g) (hb0 : 0 ≤ b)
    (hsum : (∑ j, A j) ≤ S)
    (hbad : (Finset.univ.filter fun j => ¬ P j).card ≤ 1) :
    (∑ j, A j * (if P j then g else b)) ≤ C * b + S * g := by
  let good : Finset ι := Finset.univ.filter P
  let bad : Finset ι := Finset.univ.filter fun j => ¬ P j
  have hgoodA : (∑ j ∈ good, A j) ≤ S := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) ?_) hsum
    intro j hj _
    exact hA0 j
  have hbadA_card : (∑ j ∈ bad, A j) ≤ bad.card • C := by
    exact Finset.sum_le_card_nsmul bad A C (fun j _ => hA j)
  have hbad_card : bad.card ≤ 1 := by simpa [bad] using hbad
  have hbadA : (∑ j ∈ bad, A j) ≤ C := by
    calc
      (∑ j ∈ bad, A j) ≤ bad.card • C := hbadA_card
      _ ≤ 1 • C := nsmul_le_nsmul_left hC0 hbad_card
      _ = C := one_nsmul C
  calc
    (∑ j, A j * (if P j then g else b)) =
        (∑ j ∈ good, A j * g) + (∑ j ∈ bad, A j * b) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P
        (fun j => A j * (if P j then g else b))]
      dsimp only [good, bad]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        have hjP : P j := (Finset.mem_filter.mp hj).2
        simp [hjP]
      · apply Finset.sum_congr rfl
        intro j hj
        have hjP : ¬ P j := (Finset.mem_filter.mp hj).2
        simp [hjP]
    _ = (∑ j ∈ good, A j) * g + (∑ j ∈ bad, A j) * b := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ S * g + C * b := add_le_add
      (mul_le_mul_of_nonneg_right hgoodA hg0)
      (mul_le_mul_of_nonneg_right hbadA hb0)
    _ = C * b + S * g := add_comm _ _

/-- With `|U_j|,|V_j| ≤ M`, one bad coordinate contributes at most `4M`;
the good coordinates contribute at most `2πρ` times the total amplitude. -/
lemma niveau_weighted_budget_le {ι : Type*} [Fintype ι]
    (N h : ℕ) (r : ι → ℕ) (U V : ι → ℝ) (rho M S : ℝ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hU : ∀ j, |U j| ≤ M) (hV : ∀ j, |V j| ≤ M)
    (hsum : (∑ j, (|U j| + |V j|)) ≤ S)
    (hbad : (Finset.univ.filter fun j =>
      ¬ ApproxGood N rho (r j) h).card ≤ 1) :
    (∑ j, (|U j| + |V j|) *
      (if ApproxGood N rho (r j) h then 2 * Real.pi * rho else 2)) ≤
        4 * M + S * (2 * Real.pi * rho) := by
  have h := weighted_phase_budget_le_of_bad_card_le_one
    (A := fun j => |U j| + |V j|)
    (P := fun j => ApproxGood N rho (r j) h)
    (g := 2 * Real.pi * rho) (b := 2) (C := 2 * M) (S := S)
    (fun j => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun j => by linarith [hU j, hV j]) (by positivity) (by positivity)
    (by norm_num) hsum hbad
  nlinarith

/-- End-to-end deterministic niveau-score bound. -/
theorem abs_natScore_add_sub_le_of_bad_card_le_one
    {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ)
    (rho M S : ℝ) (h x : ℕ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hU : ∀ j, |U j| ≤ M) (hV : ∀ j, |V j| ≤ M)
    (hsum : (∑ j, (|U j| + |V j|)) ≤ S)
    (hbad : (Finset.univ.filter fun j =>
      ¬ ApproxGood N rho (r j) h).card ≤ 1) :
    |natScore N r U V (x + h) - natScore N r U V x| ≤
      4 * M + S * (2 * Real.pi * rho) := by
  exact abs_natScore_add_sub_le N r U V rho _ h x hrho
    (niveau_weighted_budget_le N h r U V rho M S hrho hM hU hV hsum hbad)

/-- Splitting `x` into its residue and quotient changes the phase by an
integer multiple of `2π`. -/
lemma natPhase_eq_mod_add_period (N r x : ℕ) [NeZero N] :
    natPhase N r x = natPhase N r (x % N) +
      ((r * (x / N) : ℕ) : ℝ) * (2 * Real.pi) := by
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have hx : x % N + N * (x / N) = x := Nat.mod_add_div x N
  have hxR : (x : ℝ) = ((x % N : ℕ) : ℝ) +
      (N : ℝ) * ((x / N : ℕ) : ℝ) := by
    exact_mod_cast hx.symm
  simp only [natPhase, Nat.cast_mul]
  rw [hxR]
  field_simp

lemma cos_natPhase_mod (N r x : ℕ) [NeZero N] :
    Real.cos (natPhase N r (x % N)) = Real.cos (natPhase N r x) := by
  rw [natPhase_eq_mod_add_period N r x, Real.cos_add_nat_mul_two_pi]

lemma sin_natPhase_mod (N r x : ℕ) [NeZero N] :
    Real.sin (natPhase N r (x % N)) = Real.sin (natPhase N r x) := by
  rw [natPhase_eq_mod_add_period N r x, Real.sin_add_nat_mul_two_pi]

/-- The niveau score is periodic modulo its denominator. -/
theorem natScore_mod {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ) (x : ℕ) :
    natScore N r U V (x % N) = natScore N r U V x := by
  simp only [natScore, cos_natPhase_mod, sin_natPhase_mod]

/-- The score band inside the finite interval `[0,L)`. -/
noncomputable def natBandFinset {ι : Type*} [Fintype ι]
    (L N : ℕ) (r : ι → ℕ) (U V : ι → ℝ) (a b : ℝ) : Finset ℕ :=
  (Finset.range L).filter fun x => a ≤ natScore N r U V x ∧ natScore N r U V x ≤ b

@[simp] lemma mem_natBandFinset {ι : Type*} [Fintype ι]
    {L N : ℕ} {r : ι → ℕ} {U V : ι → ℝ} {a b : ℝ} {x : ℕ} :
    x ∈ natBandFinset L N r U V a b ↔
      x < L ∧ a ≤ natScore N r U V x ∧ natScore N r U V x ≤ b := by
  simp [natBandFinset, and_assoc]

/-- Adding good shifts to a score band can only reach the band expanded by
the deterministic translation bound.  The interval doubles because both
summands lie in `[0,N)`. -/
theorem natBandFinset_add_subset_expanded {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ)
    (rho M S a b : ℝ) (F : Finset ℕ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hU : ∀ j, |U j| ≤ M) (hV : ∀ j, |V j| ≤ M)
    (hsum : (∑ j, (|U j| + |V j|)) ≤ S)
    (hF : F ⊆ Finset.range N)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j =>
      ¬ ApproxGood N rho (r j) h).card ≤ 1) :
    natBandFinset N N r U V a b + F ⊆
      natBandFinset (2 * N) N r U V
        (a - (4 * M + S * (2 * Real.pi * rho)))
        (b + (4 * M + S * (2 * Real.pi * rho))) := by
  intro y hy
  rw [Finset.mem_add] at hy
  obtain ⟨x, hx, h, hh, rfl⟩ := hy
  rw [mem_natBandFinset] at hx ⊢
  have hhN : h < N := Finset.mem_range.mp (hF hh)
  have hchange := abs_natScore_add_sub_le_of_bad_card_le_one
    N r U V rho M S h x hrho hM hU hV hsum (hbad h hh)
  rw [abs_le] at hchange
  exact ⟨by omega, by linarith [hx.2.1, hchange.1],
    by linarith [hx.2.2, hchange.2]⟩

/-- Cardinality form of `natBandFinset_add_subset_expanded`. -/
theorem card_natBandFinset_add_le_expanded {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ)
    (rho M S a b : ℝ) (F : Finset ℕ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hU : ∀ j, |U j| ≤ M) (hV : ∀ j, |V j| ≤ M)
    (hsum : (∑ j, (|U j| + |V j|)) ≤ S)
    (hF : F ⊆ Finset.range N)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j =>
      ¬ ApproxGood N rho (r j) h).card ≤ 1) :
    (natBandFinset N N r U V a b + F).card ≤
      (natBandFinset (2 * N) N r U V
        (a - (4 * M + S * (2 * Real.pi * rho)))
        (b + (4 * M + S * (2 * Real.pi * rho)))).card :=
  Finset.card_le_card (natBandFinset_add_subset_expanded
    N r U V rho M S a b F hrho hM hU hV hsum hF hbad)

/-- The superlevel set of the score inside `[0,L)`. -/
noncomputable def natSuperlevelFinset {ι : Type*} [Fintype ι]
    (L N : ℕ) (r : ι → ℕ) (U V : ι → ℝ) (a : ℝ) : Finset ℕ :=
  (Finset.range L).filter fun x => a ≤ natScore N r U V x

@[simp] lemma mem_natSuperlevelFinset {ι : Type*} [Fintype ι]
    {L N : ℕ} {r : ι → ℕ} {U V : ι → ℝ} {a : ℝ} {x : ℕ} :
    x ∈ natSuperlevelFinset L N r U V a ↔
      x < L ∧ a ≤ natScore N r U V x := by
  simp [natSuperlevelFinset]

/-- The ordinary sumset followed by reduction modulo `N`. -/
def cyclicImageSumset (N : ℕ) (B F : Finset ℕ) : Finset ℕ :=
  (B + F).image fun x => x % N

private def zmodImage {N : ℕ} (S : Finset ℕ) : Finset (ZMod N) :=
  S.image fun x : ℕ => (x : ZMod N)

private def finZmodImage {N : ℕ} (B : Finset (Fin N)) : Finset (ZMod N) :=
  B.image fun b : Fin N => (b.val : ZMod N)

private lemma zmodImage_rotatedNatFinset {N : ℕ} [NeZero N]
    (B : Finset (Fin N)) (t : ℕ) :
    zmodImage (CyclicPrefixPinning.rotatedNatFinset B t) =
      finZmodImage B + ({-(t : ZMod N)} : Finset (ZMod N)) := by
  classical
  ext q
  simp only [zmodImage, finZmodImage, Finset.mem_image, Finset.mem_add,
    Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxB := (CyclicPrefixPinning.mem_rotatedNatFinset B t x).mp hx
    let b : Fin N := ⟨(x + t) % N, Nat.mod_lt _ (NeZero.pos N)⟩
    refine ⟨(b.val : ZMod N), ⟨b, hxB.2, rfl⟩, -(t : ZMod N), rfl, ?_⟩
    have hb : (b.val : ZMod N) = (x : ZMod N) + (t : ZMod N) := by
      change (((x + t) % N : ℕ) : ZMod N) = _
      rw [ZMod.natCast_mod]
      push_cast
      rfl
    rw [hb]
    abel
  · rintro ⟨qb, ⟨b, hb, rfl⟩, qt, rfl, rfl⟩
    let q : ZMod N := (b.val : ZMod N) + -(t : ZMod N)
    let x : ℕ := q.val
    have hxmem : x ∈ CyclicPrefixPinning.rotatedNatFinset B t := by
      apply (CyclicPrefixPinning.mem_rotatedNatFinset B t x).mpr
      refine ⟨by simpa [x] using q.val_lt, ?_⟩
      have hqt : q + (t : ZMod N) = (b.val : ZMod N) := by
        dsimp [q]
        abel
      have hv := congrArg ZMod.val hqt
      have hfin :
          (⟨(x + t) % N, Nat.mod_lt _ (NeZero.pos N)⟩ : Fin N) = b := by
        apply Fin.ext
        simpa [x, ZMod.val_add, ZMod.val_natCast, Nat.add_mod,
          Nat.mod_eq_of_lt b.isLt] using hv
      simpa [hfin] using hb
    refine ⟨x, hxmem, ?_⟩
    change (q.val : ZMod N) = (b.val : ZMod N) + -(t : ZMod N)
    rw [ZMod.natCast_zmod_val]

private def zmodCyclicSumset (N : ℕ) (B F : Finset ℕ) : Finset (ZMod N) :=
  zmodImage B + zmodImage F

private lemma cyclicImageSumset_eq_image_val {N : ℕ} [NeZero N]
    (B F : Finset ℕ) :
    cyclicImageSumset N B F =
      (zmodCyclicSumset N B F).image ZMod.val := by
  classical
  ext y
  simp only [cyclicImageSumset, zmodCyclicSumset, zmodImage, Finset.mem_image,
    Finset.mem_add]
  constructor
  · rintro ⟨z, ⟨b, hb, f, hf, rfl⟩, rfl⟩
    let q : ZMod N := (b : ZMod N) + (f : ZMod N)
    refine ⟨q, ⟨(b : ZMod N), ⟨b, hb, rfl⟩,
      (f : ZMod N), ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
    simp [q, ZMod.val_add, ZMod.val_natCast, Nat.add_mod]
  · rintro ⟨q, ⟨qb, ⟨b, hb, rfl⟩, qf, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    refine ⟨b + f, ⟨b, hb, f, hf, rfl⟩, ?_⟩
    simp [ZMod.val_add, ZMod.val_natCast, Nat.add_mod]

private lemma card_cyclicImageSumset_eq_zmod {N : ℕ} [NeZero N]
    (B F : Finset ℕ) :
    (cyclicImageSumset N B F).card = (zmodCyclicSumset N B F).card := by
  rw [cyclicImageSumset_eq_image_val,
    Finset.card_image_of_injective _ (ZMod.val_injective N)]

private lemma card_add_singleton_eq {G : Type*} [AddGroup G] [DecidableEq G]
    (S : Finset G) (a : G) : (S + {a}).card = S.card := by
  have hset : S + {a} = S.image fun x => x + a := by
    ext x
    simp only [Finset.mem_add, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, _, rfl, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, a, rfl, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (add_left_injective a)]

/-- Cyclic sumset size is invariant under the rotation used to pin prefixes. -/
theorem card_cyclicImageSumset_rotated {N : ℕ} [NeZero N]
    (B : Finset (Fin N)) (F : Finset ℕ) (t : ℕ) :
    (cyclicImageSumset N (CyclicPrefixPinning.rotatedNatFinset B t) F).card =
      (cyclicImageSumset N (B.image Fin.val) F).card := by
  rw [card_cyclicImageSumset_eq_zmod, card_cyclicImageSumset_eq_zmod]
  change ((zmodImage (N := N) (CyclicPrefixPinning.rotatedNatFinset B t) +
      zmodImage (N := N) F : Finset (ZMod N))).card =
    ((zmodImage (N := N) (B.image Fin.val) + zmodImage (N := N) F :
      Finset (ZMod N))).card
  rw [zmodImage_rotatedNatFinset]
  have hbase : zmodImage (B.image Fin.val) = finZmodImage B := by
    ext q
    simp [zmodImage, finZmodImage]
  rw [hbase]
  have hassoc :
      (finZmodImage B + {-(t : ZMod N)}) + zmodImage F =
        (finZmodImage B + zmodImage F) + {-(t : ZMod N)} := by
    ac_rfl
  rw [hassoc, card_add_singleton_eq]

/-- Generic cyclic superlevel containment under the deterministic score
translation estimate. -/
theorem cyclicImageSumset_superlevel_subset {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (r : ι → ℕ) (U V : ι → ℝ)
    (rho M S a : ℝ) (F : Finset ℕ)
    (hrho : 0 ≤ rho) (hM : 0 ≤ M)
    (hU : ∀ j, |U j| ≤ M) (hV : ∀ j, |V j| ≤ M)
    (hsum : (∑ j, (|U j| + |V j|)) ≤ S)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j =>
      ¬ ApproxGood N rho (r j) h).card ≤ 1) :
    cyclicImageSumset N (natSuperlevelFinset N N r U V a) F ⊆
      natSuperlevelFinset N N r U V
        (a - (4 * M + S * (2 * Real.pi * rho))) := by
  intro y hy
  rw [cyclicImageSumset, Finset.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, h, hh, rfl⟩ := hz
  rw [mem_natSuperlevelFinset] at hx ⊢
  have hchange := abs_natScore_add_sub_le_of_bad_card_le_one
    N r U V rho M S h x hrho hM hU hV hsum (hbad h hh)
  rw [abs_le] at hchange
  rw [natScore_mod]
  exact ⟨Nat.mod_lt _ (NeZero.pos N), by linarith [hx.2, hchange.1]⟩

/-- Under the coordinate cap `m²`, the total coefficient amplitude is at
most `2 k m²`. -/
lemma amplitude_sum_le_two_mul_card_mul_sq
    {k m : ℕ} (U V : Fin k → ℝ)
    (hU : ∀ j, |U j| ≤ (m : ℝ) ^ 2)
    (hV : ∀ j, |V j| ≤ (m : ℝ) ^ 2) :
    (∑ j, (|U j| + |V j|)) ≤ 2 * (k : ℝ) * (m : ℝ) ^ 2 := by
  calc
    (∑ j, (|U j| + |V j|)) ≤ ∑ _j : Fin k, (2 * (m : ℝ) ^ 2) := by
      gcongr with j
      linarith [hU j, hV j]
    _ = 2 * (k : ℝ) * (m : ℝ) ^ 2 := by simp; ring

/-- With `rho = 1/(256k)` and coefficient cap `m²`, the deterministic score
translation bound is at most `5m²`. -/
theorem abs_natScore_add_sub_le_five_sq
    (N k m : ℕ) [NeZero N] (hk : 0 < k)
    (r : Fin k → ℕ) (U V : Fin k → ℝ) (h x : ℕ)
    (hU : ∀ j, |U j| ≤ (m : ℝ) ^ 2)
    (hV : ∀ j, |V j| ≤ (m : ℝ) ^ 2)
    (hbad : (Finset.univ.filter fun j =>
      ¬ ApproxGood N ((1 : ℝ) / (256 * (k : ℝ))) (r j) h).card ≤ 1) :
    |natScore N r U V (x + h) - natScore N r U V x| ≤
      5 * (m : ℝ) ^ 2 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hraw := abs_natScore_add_sub_le_of_bad_card_le_one
    N r U V ((1 : ℝ) / (256 * (k : ℝ))) ((m : ℝ) ^ 2)
      (2 * (k : ℝ) * (m : ℝ) ^ 2) h x
      (by positivity) (sq_nonneg _) hU hV
      (amplitude_sum_le_two_mul_card_mul_sq U V hU hV) hbad
  have heq :
      (2 * (k : ℝ) * (m : ℝ) ^ 2) *
          (2 * Real.pi * ((1 : ℝ) / (256 * (k : ℝ)))) =
        (Real.pi / 64) * (m : ℝ) ^ 2 := by
    field_simp
    ring
  rw [heq] at hraw
  calc
    |natScore N r U V (x + h) - natScore N r U V x| ≤
        4 * (m : ℝ) ^ 2 + (Real.pi / 64) * (m : ℝ) ^ 2 := hraw
    _ ≤ 5 * (m : ℝ) ^ 2 := by
      have hpi := Real.pi_le_four
      nlinarith [sq_nonneg (m : ℝ)]

/-- Exact finite-witness containment with the simplified `5m²` width. -/
theorem cyclicImageSumset_superlevel_subset_five_sq
    (N k m : ℕ) [NeZero N] (hk : 0 < k)
    (r : Fin k → ℕ) (U V : Fin k → ℝ) (a : ℝ) (F : Finset ℕ)
    (hU : ∀ j, |U j| ≤ (m : ℝ) ^ 2)
    (hV : ∀ j, |V j| ≤ (m : ℝ) ^ 2)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j =>
      ¬ ApproxGood N ((1 : ℝ) / (256 * (k : ℝ))) (r j) h).card ≤ 1) :
    cyclicImageSumset N (natSuperlevelFinset N N r U V a) F ⊆
      natSuperlevelFinset N N r U V (a - 5 * (m : ℝ) ^ 2) := by
  intro y hy
  rw [cyclicImageSumset, Finset.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, h, hh, rfl⟩ := hz
  rw [mem_natSuperlevelFinset] at hx ⊢
  have hchange := abs_natScore_add_sub_le_five_sq
    N k m hk r U V h x hU hV (hbad h hh)
  rw [abs_le] at hchange
  rw [natScore_mod]
  exact ⟨Nat.mod_lt _ (NeZero.pos N), by linarith [hx.2, hchange.1]⟩

/-- Cardinality consequence of the cyclic finite-witness containment. -/
theorem card_cyclicImageSumset_superlevel_le_five_sq
    (N k m : ℕ) [NeZero N] (hk : 0 < k)
    (r : Fin k → ℕ) (U V : Fin k → ℝ) (a : ℝ) (F : Finset ℕ)
    (hU : ∀ j, |U j| ≤ (m : ℝ) ^ 2)
    (hV : ∀ j, |V j| ≤ (m : ℝ) ^ 2)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j =>
      ¬ ApproxGood N ((1 : ℝ) / (256 * (k : ℝ))) (r j) h).card ≤ 1) :
    (cyclicImageSumset N (natSuperlevelFinset N N r U V a) F).card ≤
      (natSuperlevelFinset N N r U V (a - 5 * (m : ℝ) ^ 2)).card :=
  Finset.card_le_card (cyclicImageSumset_superlevel_subset_five_sq
    N k m hk r U V a F hU hV hbad)

end DeterministicScore

section FiniteEventCount

open MeasureTheory

/-- The real-valued number of events in a finite family that occur at `ω`. -/
def finiteEventCount {J Ω : Type*} [Fintype J] (R : J → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ j, ({ω | R j ω}.indicator fun _ => (1 : ℝ)) ω

lemma finiteEventCount_nonneg {J Ω : Type*} [Fintype J]
    (R : J → Ω → Prop) (ω : Ω) :
    0 ≤ finiteEventCount R ω := by
  unfold finiteEventCount
  apply Finset.sum_nonneg
  intro j _
  by_cases hj : R j ω <;> simp [hj]

lemma measurable_finiteEventCount {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    {R : J → Ω → Prop} (hR : ∀ j, MeasurableSet {ω | R j ω}) :
    Measurable (finiteEventCount R) := by
  unfold finiteEventCount
  exact Finset.measurable_sum _ fun j _ => measurable_const.indicator (hR j)

lemma integrable_finiteEventCount {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {R : J → Ω → Prop}
    (hR : ∀ j, MeasurableSet {ω | R j ω}) :
    Integrable (finiteEventCount R) μ := by
  unfold finiteEventCount
  exact integrable_finsetSum Finset.univ fun j _ =>
    (integrable_const 1).indicator (hR j)

lemma integral_finiteEventCount {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {R : J → Ω → Prop}
    (hR : ∀ j, MeasurableSet {ω | R j ω}) :
    ∫ ω, finiteEventCount R ω ∂μ = ∑ j, μ.real {ω | R j ω} := by
  unfold finiteEventCount
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun j _ => integral_indicator_one (hR j)
  · exact fun j _ => (integrable_const 1).indicator (hR j)

/-- Expected finite event count bounded by the sum of per-event probability bounds. -/
lemma integral_finiteEventCount_le_sum {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {R : J → Ω → Prop} (p : J → ℝ)
    (hR : ∀ j, MeasurableSet {ω | R j ω})
    (hp : ∀ j, μ.real {ω | R j ω} ≤ p j) :
    ∫ ω, finiteEventCount R ω ∂μ ≤ ∑ j, p j := by
  rw [integral_finiteEventCount μ hR]
  exact Finset.sum_le_sum fun j _ => hp j

/-- An exceptional-family version: good events cost `p`, while exceptional events cost one. -/
lemma integral_finiteEventCount_le_card_add
    {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {R : J → Ω → Prop}
    (bad : Finset J) (p : ℝ) (hp0 : 0 ≤ p)
    (hR : ∀ j, MeasurableSet {ω | R j ω})
    (hgood : ∀ j, j ∉ bad → μ.real {ω | R j ω} ≤ p) :
    ∫ ω, finiteEventCount R ω ∂μ ≤ (bad.card : ℝ) + Fintype.card J * p := by
  rw [integral_finiteEventCount μ hR]
  calc
    ∑ j : J, μ.real {ω | R j ω}
        ≤ ∑ j : J, if j ∈ bad then (1 : ℝ) else p := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs with hj
          · exact measureReal_le_one
          · exact hgood j hj
    _ ≤ (bad.card : ℝ) + Fintype.card J * p := by
      calc
        (∑ j : J, if j ∈ bad then (1 : ℝ) else p)
            ≤ ∑ j : J, ((if j ∈ bad then (1 : ℝ) else 0) + p) := by
              apply Finset.sum_le_sum
              intro j _
              split_ifs <;> simp [hp0]
        _ = (bad.card : ℝ) + Fintype.card J * p := by
              rw [Finset.sum_add_distrib]
              simp

/-- Markov's inequality packaged as a high-probability event at eight times
an expectation bound. -/
lemma measureReal_compl_eventCount_le_eight
    {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {R : J → Ω → Prop}
    (B : ℝ) (hB : 0 < B) (hR : ∀ j, MeasurableSet {ω | R j ω})
    (hmean : ∫ ω, finiteEventCount R ω ∂μ ≤ B) :
    μ.real {ω | finiteEventCount R ω ≤ 8 * B}ᶜ ≤ 1 / 8 := by
  have hint := integrable_finiteEventCount μ hR
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := finiteEventCount R)
    (ae_of_all μ (finiteEventCount_nonneg R)) hint (8 * B)
  have hsubset : {ω | finiteEventCount R ω ≤ 8 * B}ᶜ ⊆
      {ω | 8 * B ≤ finiteEventCount R ω} := by
    intro ω hω
    have hlt : 8 * B < finiteEventCount R ω := by simpa using hω
    exact hlt.le
  have hmono : μ.real {ω | finiteEventCount R ω ≤ 8 * B}ᶜ ≤
      μ.real {ω | 8 * B ≤ finiteEventCount R ω} :=
    measureReal_mono hsubset (by finiteness)
  nlinarith

end FiniteEventCount

section ProbabilisticRealization

open MeasureTheory

/-- A union-bound realization lemma.  The fourth event is stated as conull,
so the first three events need no measurability hypotheses. -/
lemma exists_mem_four_events_of_compl_bounds
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {E F G T : Set Ω} {a b c : ℝ}
    (hE : μ.real Eᶜ ≤ a) (hF : μ.real Fᶜ ≤ b) (hG : μ.real Gᶜ ≤ c)
    (hT : μ.real Tᶜ = 0) (habc : a + b + c < 1) :
    ∃ ω, ω ∈ E ∧ ω ∈ F ∧ ω ∈ G ∧ ω ∈ T := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set Ω) ⊆ Eᶜ ∪ Fᶜ ∪ Gᶜ ∪ Tᶜ := by
    intro ω _
    by_cases hEω : ω ∈ E
    · by_cases hFω : ω ∈ F
      · by_cases hGω : ω ∈ G
        · exact Or.inr (by simpa using h ω hEω hFω hGω)
        · exact Or.inl (Or.inr (by simpa using hGω))
      · exact Or.inl (Or.inl (Or.inr (by simpa using hFω)))
    · exact Or.inl (Or.inl (Or.inl (by simpa using hEω)))
  have hone : (1 : ℝ) ≤ a + b + c := calc
    1 = μ.real Set.univ := probReal_univ.symm
    _ ≤ μ.real (Eᶜ ∪ Fᶜ ∪ Gᶜ ∪ Tᶜ) :=
      measureReal_mono hsub (by finiteness)
    _ ≤ μ.real Eᶜ + μ.real Fᶜ + μ.real Gᶜ + μ.real Tᶜ := by
      calc
        μ.real (Eᶜ ∪ Fᶜ ∪ Gᶜ ∪ Tᶜ)
            ≤ μ.real (Eᶜ ∪ Fᶜ ∪ Gᶜ) + μ.real Tᶜ :=
              measureReal_union_le _ _
        _ ≤ (μ.real (Eᶜ ∪ Fᶜ) + μ.real Gᶜ) + μ.real Tᶜ := by
              gcongr
              exact measureReal_union_le _ _
        _ ≤ (μ.real Eᶜ + μ.real Fᶜ + μ.real Gᶜ) + μ.real Tᶜ := by
              gcongr
              exact measureReal_union_le _ _
    _ ≤ a + b + c := by linarith
  linarith

/-- The same realization lemma with the fourth event presented as a
measurable full-measure event. -/
lemma exists_mem_four_events_of_bounds_of_measureReal_eq_one
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {E F G T : Set Ω} {a b c : ℝ}
    (hE : μ.real Eᶜ ≤ a) (hF : μ.real Fᶜ ≤ b) (hG : μ.real Gᶜ ≤ c)
    (hTm : MeasurableSet T) (hT : μ.real T = 1) (habc : a + b + c < 1) :
    ∃ ω, ω ∈ E ∧ ω ∈ F ∧ ω ∈ G ∧ ω ∈ T := by
  apply exists_mem_four_events_of_compl_bounds μ hE hF hG _ habc
  rw [probReal_compl_eq_one_sub hTm, hT]
  norm_num

end ProbabilisticRealization

section CentralRankSelection

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Number of scores at least as large as the score of `y`. -/
def upperScoreCount (s : X → ℝ) (y : X) : ℕ :=
  #{x ∈ Finset.univ | s y ≤ s x}

/-- Anchors whose upper rank lies between the first and third quartiles. -/
def centralAnchors (s : X → ℝ) : Finset X :=
  Finset.univ.filter fun y =>
    Fintype.card X / 4 ≤ upperScoreCount s y ∧
      upperScoreCount s y ≤ 3 * Fintype.card X / 4

/-- Scores lying below `s y` but within distance `W` of it. -/
def lowerScoreBand (s : X → ℝ) (W : ℝ) (y : X) : Finset X :=
  Finset.univ.filter fun x => s y - W ≤ s x ∧ s x < s y

/-- All ordered increasing score-pairs separated by at most `W`. -/
def closeScorePairs (s : X → ℝ) (W : ℝ) : Finset (X × X) :=
  (Finset.univ.product Finset.univ).filter fun p =>
    0 < s p.2 - s p.1 ∧ s p.2 - s p.1 ≤ W

private lemma upperScoreCount_lt_of_score_lt (s : X → ℝ) {a b : X}
    (hab : s a < s b) : upperScoreCount s b < upperScoreCount s a := by
  let aboveA := Finset.univ.filter fun x => s a ≤ s x
  let aboveB := Finset.univ.filter fun x => s b ≤ s x
  have hsub : insert a aboveB ⊆ aboveA := by
    intro x hx
    simp only [Finset.mem_insert, aboveA, aboveB, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | hx
    · exact le_rfl
    · exact hab.le.trans hx
  have hnot : a ∉ aboveB := by
    simp only [aboveB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le_of_gt hab
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  change aboveB.card < aboveA.card
  omega

lemma upperScoreCount_injective (s : X → ℝ) (hs : Function.Injective s) :
    Function.Injective (upperScoreCount s) := by
  intro a b hab
  rcases lt_trichotomy (s a) (s b) with hlt | heq | hgt
  · exact False.elim ((upperScoreCount_lt_of_score_lt s hlt).ne hab.symm)
  · exact hs heq
  · exact False.elim ((upperScoreCount_lt_of_score_lt s hgt).ne hab)

omit [DecidableEq X] in
lemma upperScoreCount_pos (s : X → ℝ) (y : X) : 0 < upperScoreCount s y := by
  rw [upperScoreCount, Finset.card_pos]
  exact ⟨y, by simp⟩

omit [DecidableEq X] in
lemma upperScoreCount_le_card (s : X → ℝ) (y : X) :
    upperScoreCount s y ≤ Fintype.card X := by
  rw [upperScoreCount, ← Finset.card_univ]
  exact Finset.card_filter_le _ _

/-- At least one quarter of the finite type consists of central anchors. -/
lemma card_le_four_mul_card_centralAnchors (s : X → ℝ)
    (hs : Function.Injective s) (hcard : 8 ≤ Fintype.card X) :
    Fintype.card X ≤ 4 * (centralAnchors s).card := by
  let N := Fintype.card X
  let low := Finset.univ.filter fun y => upperScoreCount s y < N / 4
  let high := Finset.univ.filter fun y => 3 * N / 4 < upperScoreCount s y
  let central := centralAnchors s
  have hinj := upperScoreCount_injective s hs
  have hlow : low.card ≤ N / 4 := by
    calc
      low.card = (low.image (upperScoreCount s)).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
      _ ≤ (Finset.range (N / 4)).card := by
        apply Finset.card_le_card
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨y, hy, rfl⟩
        simpa [low] using hy
      _ = N / 4 := Finset.card_range _
  have hhigh : high.card ≤ N - 3 * N / 4 := by
    calc
      high.card = (high.image (upperScoreCount s)).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
      _ ≤ (Finset.Ioc (3 * N / 4) N).card := by
        apply Finset.card_le_card
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨y, hy, rfl⟩
        simp only [high, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact Finset.mem_Ioc.mpr ⟨hy, upperScoreCount_le_card s y⟩
      _ = N - 3 * N / 4 := by simp
  have hcover : Finset.univ ⊆ (central ∪ low) ∪ high := by
    intro y hy
    simp only [central, centralAnchors, low, high, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcoverCard : N ≤ central.card + low.card + high.card := by
    calc
      N = Finset.univ.card := by simp [N]
      _ ≤ ((central ∪ low) ∪ high).card := Finset.card_le_card hcover
      _ ≤ (central ∪ low).card + high.card := Finset.card_union_le _ _
      _ ≤ central.card + low.card + high.card := by
        have h := Finset.card_union_le central low
        omega
  change N ≤ 4 * central.card
  omega

private lemma card_sigma_lowerScoreBand_le_closeScorePairs
    (s : X → ℝ) (W : ℝ) (C : Finset X) :
    (C.sigma fun y => lowerScoreBand s W y).card ≤ (closeScorePairs s W).card := by
  let swapSigma : (Σ _ : X, X) ↪ (X × X) :=
    ⟨fun p => (p.2, p.1), by
      intro a b h
      cases a with
      | mk a₁ a₂ =>
          cases b with
          | mk b₁ b₂ =>
              simp only [Prod.mk.injEq] at h
              cases h.2
              cases h.1
              rfl⟩
  rw [← Finset.card_map swapSigma]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rw [Finset.mem_sigma] at hz
  simp only [lowerScoreBand, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  rw [closeScorePairs, Finset.mem_filter]
  constructor
  · simp
  · change 0 < s z.1 - s z.2 ∧ s z.1 - s z.2 ≤ W
    constructor
    · exact sub_pos.mpr hz.2.2
    · linarith [hz.2.1]

/-- A central anchor whose lower `W`-band is no larger than four times the
global close-pair count after clearing the factor `|X|`. -/
lemma exists_central_anchor_card_mul_band_le (s : X → ℝ)
    (hs : Function.Injective s) (W : ℝ) (hcard : 8 ≤ Fintype.card X) :
    ∃ y : X,
      Fintype.card X / 4 ≤ upperScoreCount s y ∧
      upperScoreCount s y ≤ 3 * Fintype.card X / 4 ∧
      Fintype.card X * (lowerScoreBand s W y).card ≤
        4 * (closeScorePairs s W).card := by
  let C := centralAnchors s
  have hCcard : Fintype.card X ≤ 4 * C.card :=
    card_le_four_mul_card_centralAnchors s hs hcard
  have hC : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    rw [hEmpty, Finset.card_empty, mul_zero] at hCcard
    omega
  obtain ⟨y, hyC, hymin⟩ :=
    Finset.exists_min_image C (fun z => (lowerScoreBand s W z).card) hC
  have havg : C.card * (lowerScoreBand s W y).card ≤
      ∑ z ∈ C, (lowerScoreBand s W z).card := by
    calc
      C.card * (lowerScoreBand s W y).card =
          ∑ _z ∈ C, (lowerScoreBand s W y).card := by simp
      _ ≤ ∑ z ∈ C, (lowerScoreBand s W z).card := by
        exact Finset.sum_le_sum fun z hz => hymin z hz
  have hsum : (∑ z ∈ C, (lowerScoreBand s W z).card) ≤
      (closeScorePairs s W).card := by
    rw [← Finset.card_sigma]
    exact card_sigma_lowerScoreBand_le_closeScorePairs s W C
  have hycentral : Fintype.card X / 4 ≤ upperScoreCount s y ∧
      upperScoreCount s y ≤ 3 * Fintype.card X / 4 := by
    simpa [C, centralAnchors] using hyC
  refine ⟨y, hycentral.1, hycentral.2, ?_⟩
  calc
    Fintype.card X * (lowerScoreBand s W y).card ≤
        (4 * C.card) * (lowerScoreBand s W y).card :=
      Nat.mul_le_mul_right _ hCcard
    _ = 4 * (C.card * (lowerScoreBand s W y).card) := by
      rw [Nat.mul_assoc]
    _ ≤ 4 * (closeScorePairs s W).card := by
      exact Nat.mul_le_mul_left 4 (havg.trans hsum)

end CentralRankSelection

section DifferencePairCounting

/-- Ordered pairs in `ZMod N` whose difference representative satisfies `P`. -/
def badDifferencePairs (N : ℕ) [NeZero N] (P : ℕ → Prop)
    [DecidablePred P] : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => P (p.2 - p.1).val

/-- Each possible difference occurs exactly `N` times among ordered pairs in
`ZMod N`. -/
theorem card_badDifferencePairs_eq (N : ℕ) [NeZero N] (P : ℕ → Prop)
    [DecidablePred P] :
    (badDifferencePairs N P).card =
      N * ((Finset.range N).filter P).card := by
  classical
  let T := (Finset.univ : Finset (ZMod N)).product ((Finset.range N).filter P)
  have hcardT : T.card = N * ((Finset.range N).filter P).card := by
    simp [T]
  rw [← hcardT]
  refine Finset.card_bij'
    (fun p _ => (p.1, (p.2 - p.1).val))
    (fun q _ => (q.1, q.1 + (q.2 : ZMod N))) ?_ ?_ ?_ ?_
  · intro p hp
    have hpP : P (p.2 - p.1).val := (Finset.mem_filter.mp hp).2
    have hmem : p.1 ∈ (Finset.univ : Finset (ZMod N)) ∧
        (p.2 - p.1).val ∈ (Finset.range N).filter P :=
      ⟨Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (ZMod.val_lt _), hpP⟩⟩
    dsimp [T]
    rw [Finset.mem_product]
    exact hmem
  · intro q hq
    have hq' := Finset.mem_product.mp hq
    have hn : q.2 < N := Finset.mem_range.mp (Finset.mem_filter.mp hq'.2).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [ZMod.val_natCast_of_lt hn] using (Finset.mem_filter.mp hq'.2).2
  · intro p hp
    apply Prod.ext
    · rfl
    · simp
  · intro q hq
    have hq' := Finset.mem_product.mp hq
    have hn : q.2 < N := Finset.mem_range.mp (Finset.mem_filter.mp hq'.2).1
    apply Prod.ext
    · rfl
    · simp [ZMod.val_natCast_of_lt hn]

end DifferencePairCounting

section CloseScoreEventBridge

/-- The close-score event attached to one ordered pair. -/
def closeScoreEvent {X Ω : Type*} (score : Ω → X → ℝ) (W : ℝ)
    (p : X × X) (ω : Ω) : Prop :=
  0 < score ω p.2 - score ω p.1 ∧ score ω p.2 - score ω p.1 ≤ W

/-- The probabilistic finite-event counter is exactly the real cast of the
deterministic close-pair cardinality. -/
lemma finiteEventCount_closeScoreEvent_eq_card
    {X Ω : Type*} [Fintype X] (score : Ω → X → ℝ) (W : ℝ) (ω : Ω) :
    finiteEventCount (closeScoreEvent score W) ω =
      ((closeScorePairs (score ω) W).card : ℝ) := by
  classical
  unfold finiteEventCount closeScoreEvent closeScorePairs
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.univ_product_univ]
  simpa using
    (Finset.sum_boole (R := ℝ)
      (fun p : X × X ↦
        0 < score ω p.2 - score ω p.1 ∧ score ω p.2 - score ω p.1 ≤ W)
      (Finset.univ : Finset (X × X)))

end CloseScoreEventBridge

/-! ### Gaussian close-pair realization -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianLinear

/-- Real-valued form of the Gaussian interval estimate. -/
lemma stdGaussian_inner_Ioc_real_le {I : Type*} [Fintype I]
    (v : EuclideanSpace ℝ I) (hv : v ≠ 0) (a W : ℝ) (hW : 0 ≤ W) :
    (stdGaussian (EuclideanSpace ℝ I)).real
        {w | ⟪v, w⟫ ∈ Set.Ioc a (a + W)} ≤
      W / √(2 * Real.pi * ‖v‖ ^ 2) := by
  have h := stdGaussian_inner_Ioc_le v hv a W hW
  calc
    (stdGaussian (EuclideanSpace ℝ I)).real
          {w | ⟪v, w⟫ ∈ Set.Ioc a (a + W)} =
        ((stdGaussian (EuclideanSpace ℝ I))
          {w | ⟪v, w⟫ ∈ Set.Ioc a (a + W)}).toReal := rfl
    _ ≤ (ENNReal.ofReal (W / √(2 * Real.pi * ‖v‖ ^ 2))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = W / √(2 * Real.pi * ‖v‖ ^ 2) := by
      rw [ENNReal.toReal_ofReal]
      positivity

/-- A lower bound on squared norm gives a uniform real-valued Gaussian interval bound. -/
lemma stdGaussian_inner_Ioc_real_le_of_sq_norm {I : Type*} [Fintype I]
    (v : EuclideanSpace ℝ I) (W K : ℝ) (hW : 0 ≤ W) (hK : 0 < K)
    (hnorm : K ≤ ‖v‖ ^ 2) :
    (stdGaussian (EuclideanSpace ℝ I)).real
        {w | ⟪v, w⟫ ∈ Set.Ioc 0 W} ≤
      W / √(2 * Real.pi * K) := by
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp at hnorm
    linarith
  have hbase := stdGaussian_inner_Ioc_real_le v hv 0 W hW
  rw [zero_add] at hbase
  refine hbase.trans ?_
  apply div_le_div_of_nonneg_left hW
  · positivity
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hnorm (by positivity)

end GaussianLinear

/-- Simultaneously realize a coordinate cap, a Markov close-pair bound, and
pairwise distinct Gaussian linear scores. -/
lemma exists_capped_gaussian_closePairs
    {I X : Type*} [Fintype I] [Fintype X]
    (v : X → EuclideanSpace ℝ I) (M W B a : ℝ)
    (hB : 0 < B)
    (hdiff : ∀ x y, x ≠ y → v y - v x ≠ 0)
    (hcap : (stdGaussian (EuclideanSpace ℝ I)).real
      {w | ∃ i, M < |w i|} ≤ a)
    (hR : ∀ p : X × X, MeasurableSet
      {w | closeScoreEvent (fun w x ↦ ⟪v x, w⟫) W p w})
    (hmean : ∫ w, finiteEventCount
        (closeScoreEvent (fun w x ↦ ⟪v x, w⟫) W) w
        ∂(stdGaussian (EuclideanSpace ℝ I)) ≤ B)
    (hfail : a + 1 / 8 + 0 < 1) :
    ∃ w : EuclideanSpace ℝ I,
      (∀ i, |w i| ≤ M) ∧
      ((closeScorePairs (fun x ↦ ⟪v x, w⟫) W).card : ℝ) ≤ 8 * B ∧
      Function.Injective (fun x ↦ ⟪v x, w⟫) := by
  let μ := stdGaussian (EuclideanSpace ℝ I)
  let score : EuclideanSpace ℝ I → X → ℝ := fun w x ↦ ⟪v x, w⟫
  let E : Set (EuclideanSpace ℝ I) := {w | ∀ i, |w i| ≤ M}
  let F : Set (EuclideanSpace ℝ I) :=
    {w | finiteEventCount (closeScoreEvent score W) w ≤ 8 * B}
  let T : Set (EuclideanSpace ℝ I) :=
    {w | Function.Injective (fun x ↦ score w x)}
  have hEc : μ.real Eᶜ ≤ a := by
    have hset : Eᶜ = {w | ∃ i, M < |w i|} := by
      ext w
      simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq]
      push Not
      rfl
    rw [hset]
    exact hcap
  have hFc : μ.real Fᶜ ≤ 1 / 8 := by
    exact measureReal_compl_eventCount_le_eight μ B hB hR hmean
  have hTc : μ.real Tᶜ = 0 := by
    rw [measureReal_eq_zero_iff]
    have hnull := GaussianLinear.stdGaussian_finite_score_ties_null v
      (fun i j hij ↦ hdiff j i hij.symm)
    rw [show Tᶜ = {w | ∃ x y, x ≠ y ∧ ⟪v x, w⟫ = ⟪v y, w⟫} by
      ext w
      simp [T, score, Function.Injective, and_comm]]
    exact hnull
  obtain ⟨w, hwE, hwF, _hwU, hwT⟩ :=
    exists_mem_four_events_of_compl_bounds μ hEc hFc
      (E := E) (F := F) (G := Set.univ) (T := T)
      (by simp) hTc hfail
  refine ⟨w, ?_, ?_, ?_⟩
  · exact hwE
  · change finiteEventCount (closeScoreEvent score W) w ≤ 8 * B at hwF
    simpa [score, finiteEventCount_closeScoreEvent_eq_card] using hwF
  · exact hwT

/-! ### Cyclic close-pair expectation -/

section CyclicClosePairMean

open ScoreVector

/-- Residue differences for which cyclic orthogonality does not give the
uniform Gaussian interval estimate. -/
def badScoreDifferences (N k : ℕ) (r : Fin k → ℤ) : Finset ℕ :=
  (Finset.range N).filter fun d ↦
    (1 / 2 : ℝ) < cosineCoefficient N k r d

/-- Ordered cyclic pairs having an exceptional score difference. -/
def badScorePairs (N k : ℕ) [NeZero N]
    (r : Fin k → ℤ) : Finset (ZMod N × ZMod N) :=
  badDifferencePairs N fun d ↦
    (1 / 2 : ℝ) < cosineCoefficient N k r d

/-- The orthogonality estimate lifted from exceptional differences to
ordered cyclic pairs. -/
lemma card_badScorePairs_real_le
    (N k : ℕ) [NeZero N] (hk : 0 < k) (r : Fin k → ℤ)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    ((badScorePairs N k r).card : ℝ) ≤
      2 * (N : ℝ) ^ 2 / (k : ℝ) := by
  have hN : 0 < N := NeZero.pos N
  have hpair := card_badDifferencePairs_eq N
    (fun d ↦ (1 / 2 : ℝ) < cosineCoefficient N k r d)
  have hdiff := cosineCoefficient_gt_half_card N k hN hk r hsub hadd
  have hNR : (0 : ℝ) ≤ N := by positivity
  calc
    ((badScorePairs N k r).card : ℝ) =
        (N : ℝ) * ((badScoreDifferences N k r).card : ℝ) := by
      exact_mod_cast hpair
    _ ≤ (N : ℝ) * (2 * (N : ℝ) / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [badScoreDifferences] using hdiff) hNR
    _ = 2 * (N : ℝ) ^ 2 / (k : ℝ) := by ring

/-- The close-pair events for cyclic trigonometric scores are measurable. -/
lemma measurable_closeScoreEvent_scoreVector
    (N k : ℕ) [NeZero N] (r : Fin k → ℤ) (W : ℝ)
    (p : ZMod N × ZMod N) :
    MeasurableSet {w : ScoreSpace k |
      closeScoreEvent
        (fun w x ↦ inner ℝ (scoreVector N k r x) w) W p w} := by
  have hmeas : Measurable (fun w : ScoreSpace k ↦
      inner ℝ (scoreVector N k r p.2) w - inner ℝ (scoreVector N k r p.1) w) := by
    fun_prop
  have hpos : MeasurableSet {w : ScoreSpace k | (0 : ℝ) <
      inner ℝ (scoreVector N k r p.2) w - inner ℝ (scoreVector N k r p.1) w} :=
    measurableSet_lt measurable_const hmeas
  have hle : MeasurableSet {w : ScoreSpace k |
      inner ℝ (scoreVector N k r p.2) w - inner ℝ (scoreVector N k r p.1) w ≤ W} :=
    measurableSet_le hmeas measurable_const
  exact hpos.inter hle

/-- Outside the exceptional difference set, a close score pair has the
uniform one-dimensional Gaussian interval bound. -/
lemma measureReal_closeScoreEvent_le
    (N k : ℕ) [NeZero N] (hk : 0 < k) (r : Fin k → ℤ)
    (W : ℝ) (hW : 0 ≤ W) (p : ZMod N × ZMod N)
    (hp : p ∉ badScorePairs N k r) :
    (stdGaussian (ScoreSpace k)).real {w |
      closeScoreEvent
        (fun w x ↦ inner ℝ (scoreVector N k r x) w) W p w} ≤
      W / √(2 * Real.pi * (k : ℝ)) := by
  let v := scoreVector N k r p.2 - scoreVector N k r p.1
  have hc : cosineCoefficient N k r (p.2 - p.1).val ≤ (1 / 2 : ℝ) := by
    simpa [badScorePairs, badDifferencePairs] using hp
  have hnorm : (k : ℝ) ≤ ‖v‖ ^ 2 := by
    rw [show ‖v‖ ^ 2 = 2 * (k : ℝ) *
        (1 - cosineCoefficient N k r (p.2 - p.1).val) by
      simpa [v] using ScoreVector.norm_scoreVector_sub_sq N k r p.1 p.2]
    have hkR : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hprob := GaussianLinear.stdGaussian_inner_Ioc_real_le_of_sq_norm
    v W (k : ℝ) hW (by exact_mod_cast hk) hnorm
  simpa only [v, closeScoreEvent, Set.mem_ofPred_eq, Set.mem_Ioc,
    inner_sub_left, zero_add] using hprob

/-- Expected number of close cyclic score pairs, with exceptional differences
charged at probability one. -/
lemma integral_closeScoreCount_le
    (N k : ℕ) [NeZero N] (hk : 0 < k) (r : Fin k → ℤ)
    (W : ℝ) (hW : 0 ≤ W)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    ∫ w, finiteEventCount
        (closeScoreEvent
          (fun w x ↦ inner ℝ (scoreVector N k r x) w) W) w
        ∂(stdGaussian (ScoreSpace k)) ≤
      2 * (N : ℝ) ^ 2 / (k : ℝ) +
        (N : ℝ) ^ 2 * (W / √(2 * Real.pi * (k : ℝ))) := by
  let p : ℝ := W / √(2 * Real.pi * (k : ℝ))
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hraw := integral_finiteEventCount_le_card_add
    (stdGaussian (ScoreSpace k)) (badScorePairs N k r) p hp0
    (measurable_closeScoreEvent_scoreVector N k r W)
    (fun j hj ↦ measureReal_closeScoreEvent_le N k hk r W hW j hj)
  have hbad := card_badScorePairs_real_le N k hk r hsub hadd
  calc
    ∫ w, finiteEventCount
          (closeScoreEvent
            (fun w x ↦ inner ℝ (scoreVector N k r x) w) W) w
          ∂(stdGaussian (ScoreSpace k))
        ≤ ((badScorePairs N k r).card : ℝ) +
          Fintype.card (ZMod N × ZMod N) * p := hraw
    _ ≤ (2 * (N : ℝ) ^ 2 / (k : ℝ)) +
          (N : ℝ) ^ 2 * p := by
      gcongr
      simp [ZMod.card, pow_two]
    _ = 2 * (N : ℝ) ^ 2 / (k : ℝ) +
          (N : ℝ) ^ 2 * (W / √(2 * Real.pi * (k : ℝ))) := rfl

/-- Coordinate cap specialized to the cosine/sine coefficient space. -/
lemma coordinateCap_scoreSpace (m : ℕ) (hm : 0 < m) :
    (stdGaussian (ScoreSpace (m ^ 6))).real
        {w | ∃ i, (m : ℝ) ^ 2 < |w i|} ≤
      6 / (m : ℝ) ^ 2 := by
  calc
    _ ≤ 3 * Fintype.card (Fin (m ^ 6) × Fin 2) / (((m : ℝ) ^ 2) ^ 4) :=
      GaussianCoordinateCap.coordinateCap ((m : ℝ) ^ 2) (by positivity)
    _ = 6 / (m : ℝ) ^ 2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- The exact expected close-pair estimate is bounded by the rational
envelope `(7/m) N²` used in the finite witness. -/
lemma integral_closeScoreCount_le_seven_div
    (N m : ℕ) [NeZero N] (hm : 0 < m)
    (r : Fin (m ^ 6) → ℤ)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    ∫ w, finiteEventCount
        (closeScoreEvent
          (fun w x ↦ inner ℝ (scoreVector N (m ^ 6) r x) w)
          (5 * (m : ℝ) ^ 2)) w
        ∂(stdGaussian (ScoreSpace (m ^ 6))) ≤
      (7 / (m : ℝ)) * (N : ℝ) ^ 2 := by
  have hk : 0 < m ^ 6 := pow_pos hm 6
  have hraw := integral_closeScoreCount_le N (m ^ 6) hk r
    (5 * (m : ℝ) ^ 2) (by positivity) hsub hadd
  have hraw' :
      ∫ w, finiteEventCount
          (closeScoreEvent
            (fun w x ↦ inner ℝ (scoreVector N (m ^ 6) r x) w)
            (5 * (m : ℝ) ^ 2)) w
          ∂(stdGaussian (ScoreSpace (m ^ 6))) ≤
        2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 6 +
          (N : ℝ) ^ 2 *
            ((5 * (m : ℝ) ^ 2) /
              √(2 * Real.pi * (m : ℝ) ^ 6)) := by
    simpa only [Nat.cast_pow] using hraw
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.two_le_pi]
  have hsquare : ((m : ℝ) ^ 3) ^ 2 ≤
      2 * Real.pi * (m : ℝ) ^ 6 := by
    have hm6 : 0 ≤ (m : ℝ) ^ 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpi hm6]
  have hsqrt : (m : ℝ) ^ 3 ≤
      √(2 * Real.pi * (m : ℝ) ^ 6) := by
    exact (Real.le_sqrt (by positivity) (by positivity)).2 hsquare
  have hinter :
      (5 * (m : ℝ) ^ 2) /
          √(2 * Real.pi * (m : ℝ) ^ 6) ≤
        5 / (m : ℝ) := by
    calc
      (5 * (m : ℝ) ^ 2) /
            √(2 * Real.pi * (m : ℝ) ^ 6) ≤
          (5 * (m : ℝ) ^ 2) / ((m : ℝ) ^ 3) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
      _ = 5 / (m : ℝ) := by field_simp
  have hm1 : 1 ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hmle : (m : ℝ) ≤ (m : ℝ) ^ 6 := by
    calc
      (m : ℝ) = (m : ℝ) * 1 := by ring
      _ ≤ (m : ℝ) * (m : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hm1) hmR.le
      _ = (m : ℝ) ^ 6 := by ring
  have hbad : 2 / (m : ℝ) ^ 6 ≤ 2 / (m : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) hmR
    exact hmle
  calc
    _ ≤ 2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 6 +
        (N : ℝ) ^ 2 *
          ((5 * (m : ℝ) ^ 2) /
            √(2 * Real.pi * (m : ℝ) ^ 6)) := hraw'
    _ = (2 / (m : ℝ) ^ 6) * (N : ℝ) ^ 2 +
        (N : ℝ) ^ 2 *
          ((5 * (m : ℝ) ^ 2) /
            √(2 * Real.pi * (m : ℝ) ^ 6)) := by ring
    _ ≤ (2 / (m : ℝ)) * (N : ℝ) ^ 2 +
        (N : ℝ) ^ 2 * (5 / (m : ℝ)) := by gcongr
    _ = (7 / (m : ℝ)) * (N : ℝ) ^ 2 := by ring

/-- A deterministic realization of the Gaussian niveau score with capped
coordinates, few close ordered pairs, and no score ties. -/
theorem exists_niveau_score_realization
    (N m : ℕ) [NeZero N] (hm : 4 ≤ m)
    (r : Fin (m ^ 6) → ℤ)
    (hfirst : ∀ hk : 0 < m ^ 6, r ⟨0, hk⟩ = 1)
    (hsub : ∀ i j, (N : ℤ) ∣ r i - r j ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ r i + r j) :
    ∃ w : ScoreSpace (m ^ 6),
      (∀ i, |w i| ≤ (m : ℝ) ^ 2) ∧
      ((closeScorePairs
        (fun x : ZMod N ↦ inner ℝ (scoreVector N (m ^ 6) r x) w)
        (5 * (m : ℝ) ^ 2)).card : ℝ) ≤
          (56 / (m : ℝ)) * (N : ℝ) ^ 2 ∧
      Function.Injective
        (fun x : ZMod N ↦ inner ℝ (scoreVector N (m ^ 6) r x) w) := by
  have hmpos : 0 < m := by omega
  have hkpos : 0 < m ^ 6 := pow_pos hmpos 6
  letI : NeZero (m ^ 6) := ⟨hkpos.ne'⟩
  let B : ℝ := (7 / (m : ℝ)) * (N : ℝ) ^ 2
  have hB : 0 < B := by
    dsimp [B]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    exact mul_pos (div_pos (by norm_num) hmR) (sq_pos_of_pos hNR)
  have hfail : 6 / (m : ℝ) ^ 2 + 1 / 8 + 0 < 1 := by
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm2 : (16 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hfrac : 6 / (m : ℝ) ^ 2 ≤ (3 / 8 : ℝ) := by
      calc
        6 / (m : ℝ) ^ 2 ≤ 6 / 16 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm2
        _ = 3 / 8 := by norm_num
    linarith
  have hmean := integral_closeScoreCount_le_seven_div N m hmpos r hsub hadd
  obtain ⟨w, hwcap, hwclose, hwinj⟩ := exists_capped_gaussian_closePairs
    (v := scoreVector N (m ^ 6) r)
    ((m : ℝ) ^ 2) (5 * (m : ℝ) ^ 2) B (6 / (m : ℝ) ^ 2)
    hB
    (fun x y hxy ↦
      ScoreVector.scoreVector_sub_ne_zero_of_first_eq_one N (m ^ 6) r
        (by simpa using hfirst hkpos) hxy)
    (coordinateCap_scoreSpace m hmpos)
    (measurable_closeScoreEvent_scoreVector N (m ^ 6) r
      (5 * (m : ℝ) ^ 2))
    hmean hfail
  refine ⟨w, hwcap, ?_, hwinj⟩
  calc
    ((closeScorePairs
        (fun x : ZMod N ↦ inner ℝ (scoreVector N (m ^ 6) r x) w)
        (5 * (m : ℝ) ^ 2)).card : ℝ) ≤ 8 * B := hwclose
    _ = (56 / (m : ℝ)) * (N : ℝ) ^ 2 := by
      dsimp [B]
      ring

end CyclicClosePairMean

/-! ### Finite niveau witnesses -/

open ScoreVector DeterministicScore

/-- The Euclidean score-vector pairing agrees with the natural-number
trigonometric score on the canonical representative of a residue. -/
lemma inner_scoreVector_eq_natScore
    (N k : ℕ) [NeZero N] (r : Fin k → ℕ)
    (w : ScoreSpace k) (x : ZMod N) :
    inner ℝ (scoreVector N k (fun j ↦ (r j : ℤ)) x) w =
      natScore N r (fun j ↦ w (j, 0)) (fun j ↦ w (j, 1)) x.val := by
  rw [real_inner_comm, inner_scoreVector]
  unfold trigScore natScore
  apply Finset.sum_congr rfl
  intro j _
  congr 1 <;> congr 1 <;>
    simp only [intPhase, natPhase, Int.cast_natCast, Nat.cast_mul] <;> ring

/-- The natural superlevel set is the image under `ZMod.val` of the cyclic
superlevel set. -/
lemma natSuperlevelFinset_eq_image_val
    (N k : ℕ) [NeZero N] (r : Fin k → ℕ)
    (w : ScoreSpace k) (a : ℝ) :
    natSuperlevelFinset N N r (fun j ↦ w (j, 0)) (fun j ↦ w (j, 1)) a =
      (Finset.univ.filter fun x : ZMod N ↦
        a ≤ inner ℝ (scoreVector N k (fun j ↦ (r j : ℤ)) x) w).image
          ZMod.val := by
  classical
  ext n
  simp only [mem_natSuperlevelFinset, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hn
    let x : ZMod N := (n : ZMod N)
    have hxval : x.val = n := ZMod.val_natCast_of_lt hn.1
    refine ⟨x, ?_, hxval⟩
    rw [inner_scoreVector_eq_natScore, hxval]
    exact hn.2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [inner_scoreVector_eq_natScore] at hx
    exact hx

/-- The natural lower score band is the image under `ZMod.val` of the
corresponding cyclic lower band. -/
lemma natLowerBand_eq_image_val
    (N k : ℕ) [NeZero N] (r : Fin k → ℕ)
    (w : ScoreSpace k) (a W : ℝ) :
    ((Finset.range N).filter fun n ↦
      a - W ≤ natScore N r (fun j ↦ w (j, 0)) (fun j ↦ w (j, 1)) n ∧
      natScore N r (fun j ↦ w (j, 0)) (fun j ↦ w (j, 1)) n < a) =
      (Finset.univ.filter fun x : ZMod N ↦
        a - W ≤ inner ℝ (scoreVector N k (fun j ↦ (r j : ℤ)) x) w ∧
        inner ℝ (scoreVector N k (fun j ↦ (r j : ℤ)) x) w < a).image
          ZMod.val := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro hn
    let x : ZMod N := (n : ZMod N)
    have hxval : x.val = n := ZMod.val_natCast_of_lt hn.1
    refine ⟨x, ?_, hxval⟩
    simpa [inner_scoreVector_eq_natScore, hxval] using hn.2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨ZMod.val_lt x, ?_⟩
    simpa [inner_scoreVector_eq_natScore] using hx

/-- An unrotated finite niveau word obtained from a pointed family of
approximate characters. The shift set is augmented by zero so that the
cyclic sumset already contains the word itself. -/
theorem exists_unrotated_finiteNiveauWitness
    (N m : ℕ) [NeZero N] (hm : 4 ≤ m) (hN : 8 ≤ N)
    (r : Fin (m ^ 6) → ℕ)
    (hfirst : ∀ hk : 0 < m ^ 6, r ⟨0, hk⟩ = 1)
    (hsub : ∀ i j, (N : ℤ) ∣ (r i : ℤ) - (r j : ℤ) ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ (r i : ℤ) + (r j : ℤ))
    (F : Finset ℕ)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j ↦
      ¬ CharacterRecursion.ApproxGood N
        ((1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ))) (r j) h).card ≤ 1) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.range N ∧
      N / 4 ≤ B.card ∧ B.card ≤ 3 * N / 4 ∧
      ((cyclicImageSumset N B (insert 0 F)).card : ℝ) ≤
        (B.card : ℝ) + (224 / (m : ℝ)) * (N : ℝ) := by
  let rz : Fin (m ^ 6) → ℤ := fun j ↦ (r j : ℤ)
  obtain ⟨w, hwcap, hwclose, hwinj⟩ :=
    exists_niveau_score_realization N m hm rz
      (fun hk ↦ by
        simpa [rz] using congrArg (fun n : ℕ ↦ (n : ℤ)) (hfirst hk)) hsub hadd
  let U : Fin (m ^ 6) → ℝ := fun j ↦ w (j, 0)
  let V : Fin (m ^ 6) → ℝ := fun j ↦ w (j, 1)
  let W : ℝ := 5 * (m : ℝ) ^ 2
  let s : ZMod N → ℝ := fun x ↦ inner ℝ (scoreVector N (m ^ 6) rz x) w
  obtain ⟨y, hylo, hyhi, hyband⟩ :=
    exists_central_anchor_card_mul_band_le s hwinj W (by simpa [ZMod.card] using hN)
  let a : ℝ := s y
  let B : Finset ℕ := natSuperlevelFinset N N r U V a
  let L : Finset ℕ := (Finset.range N).filter fun n ↦
    a - W ≤ natScore N r U V n ∧ natScore N r U V n < a
  have hBimage : B =
      (Finset.univ.filter fun x : ZMod N ↦ a ≤ s x).image ZMod.val := by
    simpa [B, U, V, a, s, rz] using
      natSuperlevelFinset_eq_image_val N (m ^ 6) r w (s y)
  have hLimage : L =
      (Finset.univ.filter fun x : ZMod N ↦
        a - W ≤ s x ∧ s x < a).image ZMod.val := by
    simpa [L, U, V, a, s, rz] using
      natLowerBand_eq_image_val N (m ^ 6) r w (s y) W
  have hBcard : B.card = upperScoreCount s y := by
    rw [hBimage, Finset.card_image_of_injective _ (ZMod.val_injective N)]
    rfl
  have hLcard : L.card = (lowerScoreBand s W y).card := by
    rw [hLimage, Finset.card_image_of_injective _ (ZMod.val_injective N)]
    rfl
  have hbandR : (L.card : ℝ) ≤ (224 / (m : ℝ)) * (N : ℝ) := by
    have hybandR : (N : ℝ) * (L.card : ℝ) ≤
        4 * ((closeScorePairs s W).card : ℝ) := by
      exact_mod_cast (by simpa [hLcard, ZMod.card] using hyband)
    have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    calc
      (L.card : ℝ) = ((N : ℝ) * (L.card : ℝ)) / (N : ℝ) := by
        field_simp
      _ ≤ (4 * ((closeScorePairs s W).card : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hybandR hNR.le
      _ ≤ (4 * ((56 / (m : ℝ)) * (N : ℝ) ^ 2)) / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ hNR.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa [s, W] using hwclose
      _ = (224 / (m : ℝ)) * (N : ℝ) := by
        field_simp
        ring
  have hU : ∀ j, |U j| ≤ (m : ℝ) ^ 2 := fun j ↦ hwcap (j, 0)
  have hV : ∀ j, |V j| ≤ (m : ℝ) ^ 2 := fun j ↦ hwcap (j, 1)
  have hbad0 : ∀ h ∈ insert 0 F, (Finset.univ.filter fun j ↦
      ¬ CharacterRecursion.ApproxGood N
        ((1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ))) (r j) h).card ≤ 1 := by
    intro h hh
    rcases Finset.mem_insert.mp hh with rfl | hhF
    · have hgood0 (j : Fin (m ^ 6)) :
          CharacterRecursion.ApproxGood N
            ((1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ))) (r j) 0 := by
        refine ⟨0, ?_⟩
        simpa using (show (0 : ℝ) ≤
          (1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ)) by positivity)
      have hempty : (Finset.univ.filter fun j ↦
          ¬ CharacterRecursion.ApproxGood N
            ((1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ))) (r j) 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _
        simpa [div_eq_mul_inv, mul_inv, mul_comm] using hgood0 j
      rw [hempty]
      simp
    · exact hbad h hhF
  have hcont := cyclicImageSumset_superlevel_subset_five_sq
    N (m ^ 6) m (pow_pos (by omega : 0 < m) 6) r U V a (insert 0 F)
    hU hV hbad0
  have hsubset : cyclicImageSumset N B (insert 0 F) ⊆ B ∪ L := by
    intro n hn
    have hn' := hcont (by simpa [B] using hn)
    rw [mem_natSuperlevelFinset] at hn'
    by_cases hna : a ≤ natScore N r U V n
    · exact Finset.mem_union_left L (by simpa [B, mem_natSuperlevelFinset] using ⟨hn'.1, hna⟩)
    · apply Finset.mem_union_right B
      simp only [L, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn'.1, hn'.2, lt_of_not_ge hna⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact Finset.mem_range.mpr ((mem_natSuperlevelFinset.mp hn).1)
  · simpa [hBcard] using hylo
  · simpa [hBcard] using hyhi
  · calc
      ((cyclicImageSumset N B (insert 0 F)).card : ℝ) ≤ ((B ∪ L).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ (B.card : ℝ) + (L.card : ℝ) := by
        exact_mod_cast Finset.card_union_le B L
      _ ≤ (B.card : ℝ) + (224 / (m : ℝ)) * (N : ℝ) := by
        gcongr

/-- Rotating the finite niveau word pins every prefix at its global density,
without changing its cyclic sumset.  Divisibility by four turns the central
rank bounds into exact quarter-density inequalities. -/
theorem exists_rotated_finiteNiveauWitness
    (N m : ℕ) [NeZero N] (hm : 4 ≤ m) (hN : 8 ≤ N) (hN4 : 4 ∣ N)
    (r : Fin (m ^ 6) → ℕ)
    (hfirst : ∀ hk : 0 < m ^ 6, r ⟨0, hk⟩ = 1)
    (hsub : ∀ i j, (N : ℤ) ∣ (r i : ℤ) - (r j : ℤ) ↔ i = j)
    (hadd : ∀ i j, ¬ (N : ℤ) ∣ (r i : ℤ) + (r j : ℤ))
    (F : Finset ℕ)
    (hbad : ∀ h ∈ F, (Finset.univ.filter fun j ↦
      ¬ CharacterRecursion.ApproxGood N
        ((1 : ℝ) / (256 * ((m ^ 6 : ℕ) : ℝ))) (r j) h).card ≤ 1) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.range N ∧
      N ≤ 4 * B.card ∧ 4 * B.card ≤ 3 * N ∧
      (∀ t ≤ N, B.card * t ≤
        N * (B.filter fun x ↦ x < t).card) ∧
      ((cyclicImageSumset N B (insert 0 F)).card : ℝ) ≤
        (B.card : ℝ) + (224 / (m : ℝ)) * (N : ℝ) := by
  obtain ⟨B, hBrange, hBlo, hBhi, hBexp⟩ :=
    exists_unrotated_finiteNiveauWitness N m hm hN r hfirst hsub hadd F hbad
  let Bfin : Finset (Fin N) := Finset.univ.filter fun i ↦ i.val ∈ B
  have hBfinImage : Bfin.image Fin.val = B := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hn
      have hnN : n < N := Finset.mem_range.mp (hBrange hn)
      let i : Fin N := ⟨n, hnN⟩
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
  have hBfinCard : Bfin.card = B.card := by
    calc
      Bfin.card = (Bfin.image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ = B.card := congrArg Finset.card hBfinImage
  obtain ⟨t, ht, hrotCard, hrotRange, hprefix⟩ :=
    CyclicPrefixPinning.exists_rotatedNatFinset_prefix_density Bfin
  let B' : Finset ℕ := CyclicPrefixPinning.rotatedNatFinset Bfin t
  have hB'card : B'.card = B.card := hrotCard.trans hBfinCard
  have hB'exp :
      ((cyclicImageSumset N B' (insert 0 F)).card : ℝ) ≤
        (B'.card : ℝ) + (224 / (m : ℝ)) * (N : ℝ) := by
    have hcard := DeterministicScore.card_cyclicImageSumset_rotated
      Bfin (insert 0 F) t
    rw [show (cyclicImageSumset N B' (insert 0 F)).card =
        (cyclicImageSumset N B (insert 0 F)).card by
      simpa [B', hBfinImage] using hcard]
    simpa [hB'card] using hBexp
  refine ⟨B', ?_, ?_, ?_, ?_, hB'exp⟩
  · exact hrotRange
  · rw [hB'card]
    omega
  · rw [hB'card]
    omega
  · intro q hq
    calc
      B'.card * q = Bfin.card * q := by rw [hrotCard]
      _ ≤ N * (B'.filter fun x ↦ x < q).card := hprefix q hq

/-- Every sufficiently large cyclic length divisible by four admits a pinned
niveau word for the positive truncation of a lacunary set. -/
theorem exists_eventually_rotated_finiteNiveauWitness_of_lacunary
    {A : Set ℕ} (hA : IsLacunary A) (m : ℕ) (hm : 4 ≤ m) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → 4 ∣ N →
      ∃ B : Finset ℕ,
        B ⊆ Finset.range N ∧
        N ≤ 4 * B.card ∧ 4 * B.card ≤ 3 * N ∧
        (∀ t ≤ N, B.card * t ≤
          N * (B.filter fun x ↦ x < t).card) ∧
        ((cyclicImageSumset N B
          (insert 0 ((Finset.Icc 1 N).filter fun h ↦ h ∈ A))).card : ℝ) ≤
          (B.card : ℝ) + (224 / (m : ℝ)) * (N : ℝ) := by
  let k : ℕ := m ^ 6
  let Q : ℕ := 256 * k ^ 2
  let rho : ℝ := (1 : ℝ) / (256 * (k : ℝ))
  have hmpos : 0 < m := by omega
  have hk : 0 < k := by simpa [k] using pow_pos hmpos 6
  have hQ : 1 ≤ Q := by
    have hQpos : 0 < Q := by
      dsimp [Q]
      positivity
    omega
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hscale : (k : ℝ) / (Q : ℝ) ≤ rho := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    dsimp [Q, rho]
    push_cast
    field_simp
    norm_num
  obtain ⟨Rmax, Nchar, hRmax, hNchar, hfamily⟩ :=
    CharacterRecursion.exists_indexed_character_family_of_lacunary
      hA k Q rho hk hQ hrho hscale
  refine ⟨max Nchar 8, by omega, ?_⟩
  intro N hN hN4
  have hNcharN : Nchar ≤ N := by omega
  have hN8 : 8 ≤ N := by omega
  have hNpos : 0 < N := by omega
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  obtain ⟨r, hfirst, hrinj, hrange, hbad, hsub, hadd⟩ := hfamily N hNcharN
  refine exists_rotated_finiteNiveauWitness N m hm hN8 hN4 r
    ?_ hsub hadd ((Finset.Icc 1 N).filter fun h ↦ h ∈ A) ?_
  · intro hk'
    convert hfirst using 1
  · intro h hh
    simpa [rho, k] using hbad h hh

/-- A real sequence that stays in `[1/4, 3/4]` has a convergent strictly
increasing subsequence whose limit lies in the same interval. -/
lemma exists_strictMono_subsequence_tendsto_Icc
    (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    ∃ δ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (α ∘ φ) atTop (nhds δ) := by
  exact isCompact_Icc.tendsto_subseq hα

/-- Epsilon form of convergence for a real subsequence, expressed as an
eventual two-sided inequality. -/
lemma eventually_sub_lt_and_lt_add_of_tendsto
    {α : ℕ → ℝ} {φ : ℕ → ℕ} {δ ε : ℝ}
    (hlim : Tendsto (α ∘ φ) atTop (nhds δ)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      δ - ε < α (φ n) ∧ α (φ n) < δ + ε := by
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  have hdist := hN n hn
  rw [Real.dist_eq, abs_lt] at hdist
  change -ε < α (φ n) - δ ∧ α (φ n) - δ < ε at hdist
  exact ⟨by linarith [hdist.1], by linarith [hdist.2]⟩

/-- Combined compact-subsequence selection and its eventual epsilon bounds. -/
lemma exists_strictMono_subsequence_with_eventual_bounds
    (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    ∃ δ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (α ∘ φ) atTop (nhds δ) ∧
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            δ - ε < α (φ n) ∧ α (φ n) < δ + ε := by
  obtain ⟨δ, hδ, φ, hφ, hlim⟩ :=
    exists_strictMono_subsequence_tendsto_Icc α hα
  exact ⟨δ, hδ, φ, hφ, hlim,
    fun ε hε ↦ eventually_sub_lt_and_lt_add_of_tendsto hlim hε⟩

/-- A bounded real sequence has a convergent subsequence whose convergence is
accelerated to a geometric rate.  The selected indices themselves dominate
the identity. -/
lemma exists_strictMono_subsequence_with_geometric_bound
    (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    ∃ δ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (α ∘ φ) atTop (nhds δ) ∧
        (∀ j, j ≤ φ j) ∧
        ∀ j, |α (φ j) - δ| ≤ (1 - δ) / (2 : ℝ) ^ (j + 2) := by
  obtain ⟨δ, hδ, φ₀, hφ₀, hlim⟩ :=
    exists_strictMono_subsequence_tendsto_Icc α hα
  let ε : ℕ → ℝ := fun j ↦ (1 - δ) / (2 : ℝ) ^ (j + 2)
  have hδlt : δ < 1 := hδ.2.trans_lt (by norm_num)
  have hεpos : ∀ j, 0 < ε j := by
    intro j
    dsimp [ε]
    positivity
  have hlim₀ := hlim
  rw [Metric.tendsto_atTop] at hlim
  choose u hu using fun j ↦ hlim (ε j) (hεpos j)
  let ψ : ℕ → ℕ := fun j ↦ ∑ k ∈ Finset.range (j + 1), (u k + 1)
  have hψstep : ∀ j, ψ j < ψ (j + 1) := by
    intro j
    simp only [ψ, Nat.add_assoc, Finset.sum_range_succ]
    omega
  have hψ : StrictMono ψ := strictMono_nat_of_lt_succ hψstep
  have huψ : ∀ j, u j ≤ ψ j := by
    intro j
    have hterm : u j + 1 ≤ ψ j := by
      dsimp [ψ]
      refine Finset.single_le_sum (fun i hi ↦ Nat.zero_le (u i + 1)) ?_
      simp
    omega
  let φ : ℕ → ℕ := φ₀ ∘ ψ
  have hφ : StrictMono φ := hφ₀.comp hψ
  have hfast : ∀ j, |α (φ j) - δ| ≤ ε j := by
    intro j
    have hj := hu j (ψ j) (huψ j)
    rw [Real.dist_eq] at hj
    exact hj.le
  refine ⟨δ, hδ, φ, hφ, ?_, fun j ↦ hφ.id_le j, ?_⟩
  · simpa [φ, Function.comp_def] using hlim₀.comp hψ.tendsto_atTop
  · simpa [ε] using hfast

/-! ## Deterministic infinite assembly of cyclic witnesses -/

namespace InfiniteAssembly

/-! ### Canonical vanishing buffers -/

/-- The least integer buffer whose surplus at density `1` compensates the
density deficit of a block of length `N j`. -/
def densityBufferLength (δ : ℝ) (α : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.ceil (((δ - min (α j) δ) * (N j : ℝ)) / (1 - δ))

/-- The ceiling defining the buffer provides the required compensation. -/
lemma densityBufferLength_compensates
    {δ : ℝ} (hδ : δ < 1) (α : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) :
    (δ - min (α j) δ) * (N j : ℝ) ≤
      (1 - δ) * (densityBufferLength δ α N j : ℝ) := by
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  have hceil := Nat.le_ceil
    (((δ - min (α j) δ) * (N j : ℝ)) / (1 - δ))
  rw [div_le_iff₀ hden] at hceil
  simpa [densityBufferLength, mul_comm] using hceil

/-- No buffer is needed when the block density is already at least `δ`. -/
lemma densityBufferLength_eq_zero_of_ge
    {δ : ℝ} {α : ℕ → ℝ} {N : ℕ → ℕ} {j : ℕ} (h : δ ≤ α j) :
    densityBufferLength δ α N j = 0 := by
  simp [densityBufferLength, min_eq_right h]

/-- A ceiling buffer is bounded by the normalized deficit plus one inverse
block length.  This is the explicit endpoint-error estimate used in the
infinite assembly. -/
lemma densityBufferLength_div_le
    {δ : ℝ} (hδ : δ < 1) (α : ℕ → ℝ) (N : ℕ → ℕ)
    (hNpos : ∀ j, 0 < N j) (j : ℕ) :
    (densityBufferLength δ α N j : ℝ) / (N j : ℝ) ≤
      (δ - min (α j) δ) / (1 - δ) + 1 / (N j : ℝ) := by
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  have hdef : 0 ≤ δ - min (α j) δ := sub_nonneg.mpr (min_le_right _ _)
  have hNreal : (0 : ℝ) < N j := by exact_mod_cast hNpos j
  have hx : 0 ≤ ((δ - min (α j) δ) * (N j : ℝ)) / (1 - δ) :=
    div_nonneg (mul_nonneg hdef (Nat.cast_nonneg _)) hden.le
  have hceil := Nat.ceil_lt_add_one hx
  rw [div_le_iff₀ hNreal]
  apply le_of_lt
  calc
    (densityBufferLength δ α N j : ℝ) <
        ((δ - min (α j) δ) * (N j : ℝ)) / (1 - δ) + 1 := by
      simpa [densityBufferLength] using hceil
    _ = ((δ - min (α j) δ) / (1 - δ) + 1 / (N j : ℝ)) *
          (N j : ℝ) := by
      field_simp

/-- If the block densities converge to `δ` and block lengths tend to
infinity, then the relative buffer length tends to zero. -/
lemma densityBufferLength_div_tendsto_zero
    {δ : ℝ} (hδ : δ < 1) {α : ℕ → ℝ} {N : ℕ → ℕ}
    (hα : Tendsto α atTop (nhds δ))
    (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j) :
    Tendsto (fun j ↦ (densityBufferLength δ α N j : ℝ) / (N j : ℝ))
      atTop (nhds 0) := by
  have hmin : Tendsto (fun j ↦ min (α j) δ) atTop (nhds δ) := by
    have hconst : Tendsto (fun _ : ℕ ↦ δ) atTop (nhds δ) := tendsto_const_nhds
    simpa using hα.min hconst
  have hdef : Tendsto (fun j ↦ δ - min (α j) δ) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hmin using 1
    all_goals norm_num
  have hdefdiv :
      Tendsto (fun j ↦ (δ - min (α j) δ) / (1 - δ)) atTop (nhds 0) := by
    convert hdef.div_const (1 - δ) using 1
    all_goals norm_num
  have hNreal : Tendsto (fun j ↦ (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun j ↦ 1 / (N j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hNreal
  have hupper : Tendsto
      (fun j ↦ (δ - min (α j) δ) / (1 - δ) + 1 / (N j : ℝ))
      atTop (nhds 0) := by
    convert hdefdiv.add hinv using 1
    all_goals norm_num
  exact squeeze_zero
    (fun j ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun j ↦ densityBufferLength_div_le hδ α N hNpos j)
    hupper

/-- Number of letters of a finite word among positions `1,...,m`. -/
def wordPrefixCount (W : Finset ℕ) (m : ℕ) : ℕ :=
  #(W.filter fun w ↦ w ≤ m)

/-- Endpoints of successive buffer-plus-word stages. -/
def cut (L N : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cut L N j + L j + N j

/-- End of the filled buffer and beginning of the finite word at stage `j`. -/
def pivot (L N : ℕ → ℕ) (j : ℕ) : ℕ :=
  cut L N j + L j

@[simp] lemma cut_zero (L N : ℕ → ℕ) : cut L N 0 = 0 := rfl

@[simp] lemma cut_succ (L N : ℕ → ℕ) (j : ℕ) :
    cut L N (j + 1) = pivot L N j + N j := by
  rfl

lemma cut_le_pivot (L N : ℕ → ℕ) (j : ℕ) :
    cut L N j ≤ pivot L N j := by
  simp [pivot]

lemma pivot_le_cut_succ (L N : ℕ → ℕ) (j : ℕ) :
    pivot L N j ≤ cut L N (j + 1) := by
  simp

lemma cut_strictMono (L N : ℕ → ℕ) (hN : ∀ j, 0 < N j) :
    StrictMono (cut L N) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [cut_succ]
  dsimp [pivot]
  have := hN j
  omega

/-- The global concatenation: at each stage fill `(cut j,pivot j]`, then append
the translated finite word `W j`. -/
def globalSet (W : ℕ → Finset ℕ) (L N : ℕ → ℕ) : Set ℕ :=
  {x | ∃ j : ℕ,
    x ∈ Finset.Ioc (cut L N j) (pivot L N j) ∨
      ∃ w ∈ W j, x = pivot L N j + w}

lemma buffer_mem_globalSet (W : ℕ → Finset ℕ) (L N : ℕ → ℕ)
    (j x : ℕ) (hx : x ∈ Finset.Ioc (cut L N j) (pivot L N j)) :
    x ∈ globalSet W L N := by
  exact ⟨j, Or.inl hx⟩

lemma translated_word_mem_globalSet (W : ℕ → Finset ℕ) (L N : ℕ → ℕ)
    (j w : ℕ) (hw : w ∈ W j) :
    pivot L N j + w ∈ globalSet W L N := by
  exact ⟨j, Or.inr ⟨w, hw, rfl⟩⟩

/-- Translating a word prefix into its stage cannot decrease its cardinality
inside the corresponding global interval. -/
lemma wordPrefixCount_le_segmentCount
    (W : ℕ → Finset ℕ) (L N : ℕ → ℕ)
    (hsupport : ∀ j, W j ⊆ Finset.Ioc 0 (N j)) (j m : ℕ) :
    wordPrefixCount (W j) m ≤
      segmentCount (globalSet W L N) (pivot L N j) (pivot L N j + m) := by
  let S := (W j).filter fun w ↦ w ≤ m
  let T := (Finset.Ioc (pivot L N j) (pivot L N j + m)).filter
    fun x ↦ x ∈ globalSet W L N
  have hsub : S.map (addLeftEmbedding (pivot L N j)) ⊆ T := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' := Finset.mem_filter.mp hw
    have hwsupport := Finset.mem_Ioc.mp (hsupport j hw'.1)
    rw [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · exact ⟨Nat.add_lt_add_left hwsupport.1 _, Nat.add_le_add_left hw'.2 _⟩
    · exact translated_word_mem_globalSet W L N j w hw'.1
  have hcard := Finset.card_le_card hsub
  simpa [S, T, wordPrefixCount, segmentCount] using hcard

/-- A sequence of already-rotated finite cyclic witnesses.  `prefixPinned`
is the output of the cyclic rotation lemma; `expansionError` records the finite
sumset error before old-prefix fattening. -/
structure PinnedCyclicWords (δ : ℝ) where
  length : ℕ → ℕ
  word : ℕ → Finset ℕ
  density : ℕ → ℝ
  expansionError : ℕ → ℝ
  length_pos : ∀ j, 0 < length j
  support : ∀ j, word j ⊆ Finset.Ioc 0 (length j)
  card_eq : ∀ j, ((word j).card : ℝ) = density j * (length j : ℝ)
  density_mem : ∀ j, density j ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)
  prefixPinned : ∀ j m, m ≤ length j →
    density j * (m : ℝ) ≤ (wordPrefixCount (word j) m : ℝ)
  density_tendsto : Tendsto density atTop (nhds δ)
  expansionError_tendsto : Tendsto expansionError atTop (nhds 0)

/-- Buffer lengths and the one application-specific endpoint estimate.

`endpoint_upper` is deliberately the only place where the old-prefix
lacunary fattening argument enters.  A finite witness supplies
`density j + expansionError j`; `oldError j` absorbs the buffer, all earlier
stages, and truncating the lacunary summand set. -/
structure FatteningBounds (A : Set ℕ) {δ : ℝ} (w : PinnedCyclicWords δ) where
  bufferLength : ℕ → ℕ
  compensation : ∀ j,
    (δ - min (w.density j) δ) * (w.length j : ℝ) ≤
      (1 - δ) * (bufferLength j : ℝ)
  oldError : ℕ → ℝ
  oldError_tendsto : Tendsto oldError atTop (nhds 0)
  endpoint_upper : ∀ j,
    let C := globalSet w.word bufferLength w.length
    (countIn (A + C) (cut bufferLength w.length (j + 1)) : ℝ) /
        (cut bufferLength w.length (j + 1) : ℝ) ≤
      w.density j + w.expansionError j + oldError j

variable {A : Set ℕ} {δ : ℝ} (w : PinnedCyclicWords δ)
  (b : FatteningBounds A w)

private lemma beta_prefixPinned (j n : ℕ)
    (hleft : pivot b.bufferLength w.length j ≤ n)
    (hright : n ≤ cut b.bufferLength w.length (j + 1)) :
    min (w.density j) δ * ((n - pivot b.bufferLength w.length j : ℕ) : ℝ) ≤
      (segmentCount
        (globalSet w.word b.bufferLength w.length)
        (pivot b.bufferLength w.length j) n : ℝ) := by
  let m := n - pivot b.bufferLength w.length j
  have hm : m ≤ w.length j := by
    dsimp [m]
    rw [cut_succ] at hright
    omega
  have hpin := w.prefixPinned j m hm
  have hmin : min (w.density j) δ * (m : ℝ) ≤ w.density j * (m : ℝ) := by
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg m)
  have hcount := wordPrefixCount_le_segmentCount w.word b.bufferLength w.length
    w.support j m
  have hadd : pivot b.bufferLength w.length j + m = n := by
    dsimp [m]
    omega
  rw [hadd] at hcount
  exact hmin.trans (hpin.trans (by exact_mod_cast hcount))

/-- The deterministic infinite assembly produces both certificates needed by
`schnirelmann_bridge_of_fattening_certificate`. -/
def certificates (δ_le_one : δ ≤ 1) :
    let C := globalSet w.word b.bufferLength w.length
    PrefixGluingCertificate C δ × EndpointFatteningCertificate A C δ := by
  let C := globalSet w.word b.bufferLength w.length
  let cuts := cut b.bufferLength w.length
  let pivots := pivot b.bufferLength w.length
  let beta := fun j ↦ min (w.density j) δ
  have hprefix : PrefixGluingCertificate C δ :=
    prefixGluingCertificate_of_bufferedWords C δ cuts pivots beta
      (by simp [cuts])
      (by simpa [cuts] using cut_strictMono b.bufferLength w.length w.length_pos)
      δ_le_one
      (by intro j; exact cut_le_pivot _ _ _)
      (by intro j; exact pivot_le_cut_succ _ _ _)
      (by intro j; exact min_le_right _ _)
      (by
        intro j x hx
        exact buffer_mem_globalSet w.word b.bufferLength w.length j x hx)
      (by
        intro j n hleft hright
        exact beta_prefixPinned w b j n hleft hright)
      (by
        intro j
        simpa [cuts, pivots, beta, cut_succ, pivot] using b.compensation j)
  have herr : Tendsto
      (fun j ↦ |w.density j - δ| + w.expansionError j + b.oldError j)
      atTop (nhds 0) := by
    have hdiff : Tendsto (fun j ↦ |w.density j - δ|) atTop (nhds 0) := by
      simpa using (w.density_tendsto.sub_const δ).abs
    simpa using (hdiff.add w.expansionError_tendsto).add b.oldError_tendsto
  let hendpoint : EndpointFatteningCertificate A C δ := {
    endpoint := fun j ↦ cuts (j + 1)
    endpoint_pos := by
      intro j
      dsimp [cuts]
      rw [cut_succ]
      have := w.length_pos j
      omega
    error := fun j ↦ |w.density j - δ| + w.expansionError j + b.oldError j
    error_tendsto_zero := herr
    sumset_upper := by
      intro j
      have hu := b.endpoint_upper j
      dsimp [C, cuts] at hu ⊢
      calc
        (countIn
              (A + globalSet w.word b.bufferLength w.length)
              (cut b.bufferLength w.length (j + 1)) : ℝ) /
            (cut b.bufferLength w.length (j + 1) : ℝ)
            ≤ w.density j + w.expansionError j + b.oldError j := hu
        _ ≤ δ +
            (|w.density j - δ| + w.expansionError j + b.oldError j) := by
          have habs : w.density j - δ ≤ |w.density j - δ| := le_abs_self _
          linarith }
  simpa [C] using (hprefix, hendpoint)

/-- Final density conclusion of the abstract infinite assembly. -/
theorem schnirelmann_eq (δ_le_one : δ ≤ 1) (hzero : 0 ∈ A) :
    let C := globalSet w.word b.bufferLength w.length
    sd C = δ ∧ sd (A + C) = δ := by
  obtain ⟨hp, he⟩ := certificates w b δ_le_one
  exact schnirelmann_bridge_of_fattening_certificate hzero hp he

end InfiniteAssembly

/-! ## Concrete lacunary endpoint bounds for the infinite assembly -/

namespace InfiniteAssembly.ConcreteFattening

/-- Truncation of `A` to the residues `0,...,N`. -/
def truncatedA (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 0 N).filter (fun a ↦ a ∈ A)

/-- Ordinary (not reduced modulo `N`) current-word sums that stay in `(0,N]`. -/
def currentWindow (A : Set ℕ) (W : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (W + truncatedA A N).filter (fun y ↦ y ∈ Finset.Ioc 0 N)

lemma globalSet_le_endpoint_classify
    (W : ℕ → Finset ℕ) (L N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (hsupport : ∀ k, W k ⊆ Finset.Ioc 0 (N k))
    (j c : ℕ) (hc : c ∈ globalSet W L N)
    (hcT : c ≤ cut L N (j + 1)) :
    c ≤ pivot L N j ∨ ∃ u ∈ W j, c = pivot L N j + u := by
  obtain ⟨k, hkbuf | ⟨u, hu, rfl⟩⟩ := hc
  · by_cases hkj : k ≤ j
    · rcases hkj.eq_or_lt with rfl | hkjlt
      · exact Or.inl (Finset.mem_Ioc.mp hkbuf).2
      · left
        have hupper : c ≤ cut L N (k + 1) := by
          exact (Finset.mem_Ioc.mp hkbuf).2.trans (pivot_le_cut_succ L N k)
        exact hupper.trans ((cut_strictMono L N hN).monotone (Nat.succ_le_iff.mpr hkjlt))
          |>.trans (cut_le_pivot L N j)
    · have hjk : j < k := Nat.lt_of_not_ge hkj
      have hlower : cut L N k < c :=
        (Finset.mem_Ioc.mp hkbuf).1
      have hcut : cut L N (j + 1) ≤ cut L N k :=
        (cut_strictMono L N hN).monotone (Nat.succ_le_iff.mpr hjk)
      omega
  · by_cases hkj : k ≤ j
    · rcases hkj.eq_or_lt with rfl | hkjlt
      · exact Or.inr ⟨u, hu, rfl⟩
      · left
        have huN : u ≤ N k := (Finset.mem_Ioc.mp (hsupport k hu)).2
        have hupper : pivot L N k + u ≤ cut L N (k + 1) := by
          rw [cut_succ]
          omega
        exact hupper.trans ((cut_strictMono L N hN).monotone
          (Nat.succ_le_iff.mpr hkjlt)) |>.trans (cut_le_pivot L N j)
    · have hjk : j < k := Nat.lt_of_not_ge hkj
      have hu0 : 0 < u := (Finset.mem_Ioc.mp (hsupport k hu)).1
      have hlower : cut L N k < pivot L N k + u := by
        dsimp [pivot]
        omega
      have hcut : cut L N (j + 1) ≤ cut L N k :=
        (cut_strictMono L N hN).monotone (Nat.succ_le_iff.mpr hjk)
      omega

/-- At a completed stage, every sum is covered either by fattening `A` with
the whole old prefix `[0,P]`, or by the current finite word window. -/
lemma countIn_endpoint_le_old_add_current
    (A : Set ℕ) (W : ℕ → Finset ℕ) (L N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (hsupport : ∀ k, W k ⊆ Finset.Ioc 0 (N k))
    (j : ℕ) :
    countIn (A + globalSet W L N) (cut L N (j + 1)) ≤
      ((A + Set.Icc 0 (pivot L N j)) ∩ Set.Icc 1 (cut L N (j + 1))).ncard +
        (currentWindow A (W j) (N j)).card := by
  let P := pivot L N j
  let T := cut L N (j + 1)
  let target := (Finset.Ioc 0 T).filter (fun x ↦ x ∈ A + globalSet W L N)
  let old := (Finset.Icc 1 T).filter (fun x ↦ x ∈ A + Set.Icc 0 P)
  let current := (currentWindow A (W j) (N j)).map (addLeftEmbedding P)
  have hsub : target ⊆ old ∪ current := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxI := Finset.mem_Ioc.mp hx'.1
    have hxsum := hx'.2
    rw [Set.mem_add] at hxsum
    obtain ⟨a, ha, c, hc, hac⟩ := hxsum
    have hcT : c ≤ T := by omega
    have hclass := globalSet_le_endpoint_classify W L N hN hsupport j c hc hcT
    rw [Finset.mem_union]
    rcases hclass with hcP | ⟨u, hu, hcu⟩
    · left
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hxI.1, hxI.2⟩, ?_⟩
      rw [Set.mem_add]
      exact ⟨a, ha, c, ⟨Nat.zero_le _, hcP⟩, hac⟩
    · right
      let y := a + u
      have hT : T = P + N j := by simp [T, P]
      have hxy : x = P + y := by
        dsimp [y]
        omega
      have hyN : y ≤ N j := by omega
      have hu0 : 0 < u := (Finset.mem_Ioc.mp (hsupport j hu)).1
      have hy0 : 0 < y := by dsimp [y]; omega
      have haN : a ≤ N j := by dsimp [y] at hyN; omega
      have haTrunc : a ∈ truncatedA A (N j) := by
        simp [truncatedA, ha, haN]
      have hySum : y ∈ W j + truncatedA A (N j) := by
        rw [Finset.mem_add]
        exact ⟨u, hu, a, haTrunc, by simp [y, add_comm]⟩
      have hyWindow : y ∈ currentWindow A (W j) (N j) := by
        rw [currentWindow, Finset.mem_filter]
        exact ⟨hySum, Finset.mem_Ioc.mpr ⟨hy0, hyN⟩⟩
      dsimp [current]
      rw [Finset.mem_map]
      exact ⟨y, hyWindow, by simpa [hxy]⟩
  have hcard := Finset.card_le_card hsub
  have holdSet : (old : Set ℕ) =
      (A + Set.Icc 0 P) ∩ Set.Icc 1 T := by
    ext x
    simp [old, and_comm]
  calc
    countIn (A + globalSet W L N) (cut L N (j + 1)) = target.card := rfl
    _ ≤ (old ∪ current).card := hcard
    _ ≤ old.card + current.card := Finset.card_union_le _ _
    _ = ((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard +
        (currentWindow A (W j) (N j)).card := by
      rw [← holdSet, Set.ncard_coe_finset]
      simp [current]
    _ = ((A + Set.Icc 0 (pivot L N j)) ∩ Set.Icc 1 (cut L N (j + 1))).ncard +
        (currentWindow A (W j) (N j)).card := rfl

/-- The ordinary current window injects into the cyclic image sumset by
reduction modulo `N`. -/
lemma currentWindow_card_le_cyclicImageSumset
    (A : Set ℕ) (W : Finset ℕ) (N : ℕ) (hN : 0 < N) :
    (currentWindow A W N).card ≤
      (DeterministicScore.cyclicImageSumset N W (truncatedA A N)).card := by
  have hinj : Set.InjOn (fun x : ℕ ↦ x % N) (currentWindow A W N : Set ℕ) := by
    intro x hx y hy hxy
    have hxI : x ∈ Finset.Ioc 0 N :=
      (Finset.mem_filter.mp hx).2
    have hyI : y ∈ Finset.Ioc 0 N :=
      (Finset.mem_filter.mp hy).2
    have hxpos : 0 < x := (Finset.mem_Ioc.mp hxI).1
    have hypos : 0 < y := (Finset.mem_Ioc.mp hyI).1
    have hxle : x ≤ N := (Finset.mem_Ioc.mp hxI).2
    have hyle : y ≤ N := (Finset.mem_Ioc.mp hyI).2
    rcases hxle.eq_or_lt with rfl | hxlt
    · rcases hyle.eq_or_lt with rfl | hylt
      · rfl
      · change x % x = y % x at hxy
        rw [Nat.mod_self, Nat.mod_eq_of_lt hylt] at hxy
        omega
    · rcases hyle.eq_or_lt with rfl | hylt
      · change x % y = y % y at hxy
        rw [Nat.mod_self, Nat.mod_eq_of_lt hxlt] at hxy
        omega
      · simpa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hxy
  calc
    (currentWindow A W N).card =
        ((currentWindow A W N).image fun x ↦ x % N).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ ≤ (DeterministicScore.cyclicImageSumset N W (truncatedA A N)).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_image] at hr
      rw [DeterministicScore.cyclicImageSumset, Finset.mem_image]
      obtain ⟨x, hx, rfl⟩ := hr
      exact ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩

/-- Explicit numerator in the lacunary old-prefix fattening estimate. -/
def oldBound (K : ℕ) (d L N : ℕ → ℕ) (j : ℕ) : ℕ :=
  let P := pivot L N j
  2 * P + 1 + (K * d j + 1) * (P + 1)

/-- A concrete `FatteningBounds` constructor.  The only remaining inputs are:

* a dyadic exponent placing the endpoint in a lacunary shell;
* a scale-growth limit making the explicit old-prefix numerator negligible;
* the finite cyclic image-sumset bound.
-/
noncomputable def boundsOfLacunary
    (A : Set ℕ) {δ : ℝ} (w : PinnedCyclicWords δ) (hA : IsLacunary A)
    (L d : ℕ → ℕ)
    (hcomp : ∀ j,
      (δ - min (w.density j) δ) * (w.length j : ℝ) ≤
        (1 - δ) * (L j : ℝ))
    (hP : ∀ j, 1 ≤ pivot L w.length j)
    (hdyadic : ∀ j,
      cut L w.length (j + 1) ≤ 2 ^ d j * pivot L w.length j)
    (hscale : ∀ K : ℕ, 1 ≤ K →
      Tendsto (fun j ↦
        (oldBound K d L w.length j : ℝ) /
          (cut L w.length (j + 1) : ℝ)) atTop (nhds 0))
    (hexp_nonneg : ∀ j, 0 ≤ w.density j + w.expansionError j)
    (hcyclic : ∀ j,
      ((DeterministicScore.cyclicImageSumset (w.length j) (w.word j)
        (truncatedA A (w.length j))).card : ℝ) ≤
          (w.density j + w.expansionError j) * (w.length j : ℝ)) :
    FatteningBounds A w := by
  let hex := lacunary_shell_and_fattening_bounds hA
  let K := Classical.choose hex
  have hK : 1 ≤ K := (Classical.choose_spec hex).1
  have hshell := (Classical.choose_spec hex).2
  refine
    { bufferLength := L
      compensation := hcomp
      oldError := fun j ↦
        (oldBound K d L w.length j : ℝ) /
          (cut L w.length (j + 1) : ℝ)
      oldError_tendsto := hscale K hK
      endpoint_upper := ?_ }
  intro j
  let P := pivot L w.length j
  let T := cut L w.length (j + 1)
  let q := w.density j + w.expansionError j
  have hTformula : T = P + w.length j := by simp [T, P]
  have hTpos : (0 : ℝ) < T := by
    have hTnat : 0 < T := by
      rw [hTformula]
      exact Nat.add_pos_right P (w.length_pos j)
    exact_mod_cast hTnat
  have hNT : w.length j ≤ T := by rw [hTformula]; omega
  have hold := (hshell (hP j) (hdyadic j)).2
  have hold' :
      (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) ≤
        (oldBound K d L w.length j : ℝ) := by
    exact_mod_cast hold
  have hdecomp := countIn_endpoint_le_old_add_current A w.word L w.length
    w.length_pos w.support j
  have hcurrentNat := currentWindow_card_le_cyclicImageSumset
    A (w.word j) (w.length j) (w.length_pos j)
  have hcurrent : ((currentWindow A (w.word j) (w.length j)).card : ℝ) ≤
      q * (w.length j : ℝ) := by
    have hcurrentCast : ((currentWindow A (w.word j) (w.length j)).card : ℝ) ≤
        ((DeterministicScore.cyclicImageSumset (w.length j) (w.word j)
          (truncatedA A (w.length j))).card : ℝ) := by
      exact_mod_cast hcurrentNat
    exact hcurrentCast.trans (hcyclic j)
  have hcount : (countIn (A + globalSet w.word L w.length) T : ℝ) ≤
      (oldBound K d L w.length j : ℝ) + q * (w.length j : ℝ) := by
    have hdecompCast : (countIn (A + globalSet w.word L w.length) T : ℝ) ≤
        (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) +
          ((currentWindow A (w.word j) (w.length j)).card : ℝ) := by
      exact_mod_cast hdecomp
    exact hdecompCast.trans (add_le_add hold' hcurrent)
  have hq : 0 ≤ q := hexp_nonneg j
  have hqNT : q * (w.length j : ℝ) ≤ q * T := by
    apply mul_le_mul_of_nonneg_left _ hq
    exact_mod_cast hNT
  have hcancel :
      ((oldBound K d L w.length j : ℝ) / T) * T =
        (oldBound K d L w.length j : ℝ) := by
    field_simp
  change (countIn (A + globalSet w.word L w.length) T : ℝ) / T ≤
    q + (oldBound K d L w.length j : ℝ) / T
  rw [div_le_iff₀ hTpos]
  nlinarith

end InfiniteAssembly.ConcreteFattening

/-! ### Turning cyclic residue witnesses into positive finite words -/

namespace InfiniteAssembly

open Filter Topology
open ConcreteFattening

/-- A buffer equal to the ceiling of a `2^(j+1)`-fraction of the current
word. -/
noncomputable def dyadicBufferLength (N : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.ceil ((N j : ℝ) / ((2 ^ (j + 1) : ℕ) : ℝ))

lemma dyadicBufferLength_pos (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) (j : ℕ) :
    0 < dyadicBufferLength N j := by
  rw [dyadicBufferLength, Nat.ceil_pos]
  apply div_pos
  · exact_mod_cast hN j
  · exact_mod_cast (show 0 < 2 ^ (j + 1) by positivity)

lemma length_le_pow_mul_dyadicBufferLength
    (N : ℕ → ℕ) (j : ℕ) :
    N j ≤ 2 ^ (j + 1) * dyadicBufferLength N j := by
  have hpNat : 0 < 2 ^ (j + 1) := by positivity
  have hp : (0 : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hpNat
  have hc := Nat.le_ceil
    ((N j : ℝ) / ((2 ^ (j + 1) : ℕ) : ℝ))
  rw [div_le_iff₀ hp] at hc
  simpa [dyadicBufferLength, mul_comm] using (show
    N j ≤ dyadicBufferLength N j * 2 ^ (j + 1) by exact_mod_cast hc)

lemma one_le_pivot_dyadicBufferLength
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) (j : ℕ) :
    1 ≤ pivot (dyadicBufferLength N) N j := by
  have hL := dyadicBufferLength_pos N hN j
  simp only [pivot]
  omega

lemma cut_succ_le_dyadic_mul_pivot
    (N : ℕ → ℕ) (j : ℕ) :
    cut (dyadicBufferLength N) N (j + 1) ≤
      2 ^ (j + 2) * pivot (dyadicBufferLength N) N j := by
  let P := pivot (dyadicBufferLength N) N j
  let s := 2 ^ (j + 1)
  have hNP : N j ≤ s * P := by
    have hNL := length_le_pow_mul_dyadicBufferLength N j
    have hLP : dyadicBufferLength N j ≤ P := by
      dsimp [P]
      simp [pivot]
    exact hNL.trans (Nat.mul_le_mul_left s hLP)
  have hspos : 0 < s := by dsimp [s]; positivity
  have hs : 1 ≤ s := by omega
  have hPP : P ≤ s * P := by
    simpa [one_mul] using Nat.mul_le_mul_right P hs
  have hsum : P + N j ≤ (s * P) + (s * P) :=
    Nat.add_le_add hPP hNP
  rw [cut_succ]
  change P + N j ≤ 2 ^ (j + 2) * P
  calc
    P + N j ≤ s * P + s * P := hsum
    _ = 2 ^ (j + 2) * P := by
      dsimp [s]
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring

/-- Weighted reciprocal lengths vanish as soon as the preceding cut is at
least one and its weighted ratio to the new word vanishes. -/
lemma weighted_inv_length_tendsto_zero
    (L N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (hcut : Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) * (cut L N j : ℝ)) / (N j : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun j ↦ ((j + 2 : ℕ) : ℝ) / (N j : ℝ))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hcut ?_ ?_
  · exact Filter.Eventually.of_forall fun j ↦ by positivity
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hcutpos : 0 < cut L N j := by
      have hmono := cut_strictMono L N hN
      exact (show cut L N 0 < cut L N j from hmono hj)
    have hcutone : (1 : ℝ) ≤ (cut L N j : ℝ) := by exact_mod_cast hcutpos
    have hr : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by positivity
    have hnum : ((j + 2 : ℕ) : ℝ) ≤
        ((j + 2 : ℕ) : ℝ) * (cut L N j : ℝ) := by
      nlinarith
    exact div_le_div_of_nonneg_right hnum (by positivity)

/-- The elementary shifted exponential estimate used for ceiling buffers. -/
lemma tendsto_nat_add_two_div_two_pow_succ :
    Tendsto (fun j : ℕ ↦
      ((j + 2 : ℕ) : ℝ) / (((2 ^ (j + 1) : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < 2 by norm_num)).comp (Filter.tendsto_add_atTop_nat 2)
  have h' := h.const_mul (2 : ℝ)
  convert h' using 1
  · funext j
    norm_num [pow_succ]
    ring
  · norm_num

/-- The weighted relative size of the dyadic ceiling buffer tends to zero,
provided the weighted old-cut/new-word ratio does. -/
lemma weighted_dyadicBufferLength_div_tendsto_zero
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (hcut : Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) *
        (cut (dyadicBufferLength N) N j : ℝ)) / (N j : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) * (dyadicBufferLength N j : ℝ)) /
        (N j : ℝ)) atTop (nhds 0) := by
  have hinv := weighted_inv_length_tendsto_zero
    (dyadicBufferLength N) N hN hcut
  have hu := tendsto_nat_add_two_div_two_pow_succ.add hinv
  apply squeeze_zero
  · intro j
    positivity
  · intro j
    let r : ℝ := ((j + 2 : ℕ) : ℝ)
    let n : ℝ := (N j : ℝ)
    let s : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
    have hn : 0 < n := by dsimp [n]; exact_mod_cast hN j
    have hs : 0 < s := by dsimp [s]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hx : 0 ≤ n / s := div_nonneg hn.le hs.le
    have hceil := (Nat.ceil_lt_add_one hx).le
    have hL : (dyadicBufferLength N j : ℝ) ≤ n / s + 1 := by
      simpa [dyadicBufferLength, n, s] using hceil
    calc
      r * (dyadicBufferLength N j : ℝ) / n ≤
          r * (n / s + 1) / n := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL hr) hn.le
      _ = r / s + r / n := by field_simp
  · simpa using hu

lemma weighted_pivot_div_length_tendsto_zero
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (hcut : Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) *
        (cut (dyadicBufferLength N) N j : ℝ)) / (N j : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) *
        (pivot (dyadicBufferLength N) N j : ℝ)) / (N j : ℝ))
      atTop (nhds 0) := by
  have hL := weighted_dyadicBufferLength_div_tendsto_zero N hN hcut
  have hsum := hcut.add hL
  convert hsum using 1
  · funext j
    simp only [pivot, Nat.cast_add]
    ring
  · norm_num

/-- The explicit lacunary old-prefix error tends to zero for exponent
`d j = j+2` under the (necessary) weighted cut-growth hypothesis. -/
lemma oldBound_dyadicBufferLength_div_tendsto_zero
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) (K : ℕ)
    (hcut : Tendsto (fun j ↦
      (((j + 2 : ℕ) : ℝ) *
        (cut (dyadicBufferLength N) N j : ℝ)) / (N j : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun j ↦
      (oldBound K (fun i ↦ i + 2) (dyadicBufferLength N) N j : ℝ) /
        (cut (dyadicBufferLength N) N (j + 1) : ℝ))
      atTop (nhds 0) := by
  let L := dyadicBufferLength N
  have hpiv := weighted_pivot_div_length_tendsto_zero N hN hcut
  have hinv := weighted_inv_length_tendsto_zero L N hN hcut
  have hu := (hpiv.add hinv).const_mul ((K : ℝ) + 3)
  apply squeeze_zero
  · intro j
    positivity
  · intro j
    let r : ℝ := ((j + 2 : ℕ) : ℝ)
    let k : ℝ := (K : ℝ)
    let P : ℝ := (pivot L N j : ℝ)
    let n : ℝ := (N j : ℝ)
    let T : ℝ := (cut L N (j + 1) : ℝ)
    have hn : 0 < n := by dsimp [n]; exact_mod_cast hN j
    have hr : 2 ≤ r := by dsimp [r]; norm_num
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hT : T = P + n := by
      dsimp [T, P, n, L]
      rw [cut_succ]
      norm_num
    have hnT : n ≤ T := by rw [hT]; linarith
    have hnum :
        (oldBound K (fun i ↦ i + 2) L N j : ℝ) ≤
          (k + 3) * r * (P + 1) := by
      simp only [oldBound]
      dsimp [r, k, P]
      push_cast
      nlinarith
    have hquot :
        (oldBound K (fun i ↦ i + 2) L N j : ℝ) / T ≤
          ((k + 3) * r * (P + 1)) / n := by
      exact div_le_div₀ (by positivity) hnum hn hnT
    calc
      (oldBound K (fun i ↦ i + 2) L N j : ℝ) /
          (cut L N (j + 1) : ℝ) ≤
          ((k + 3) * r * (P + 1)) / n := by simpa [T] using hquot
      _ = (k + 3) * (r * P / n + r / n) := by field_simp
  · simpa [L] using hu


/-! ### Explicit positive geometric buffers for the final diagonal construction -/

namespace EndpointLimits

open InfiniteAssembly.ConcreteFattening

/-- The explicit positive buffer used in the final diagonal construction. -/
noncomputable def geometricBufferLength (N : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.ceil ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ)) + 1

/-- The dyadic shell exponent used at the `j`th endpoint. -/
def geometricDyadicExponent (j : ℕ) : ℕ := j + 3

lemma geometricBufferLength_pos (N : ℕ → ℕ) (j : ℕ) :
    0 < geometricBufferLength N j := by
  simp [geometricBufferLength]

lemma one_le_pivot_geometricBufferLength (N : ℕ → ℕ) (j : ℕ) :
    1 ≤ pivot (geometricBufferLength N) N j := by
  have hL := geometricBufferLength_pos N j
  simp only [pivot]
  omega

/-- The ceiling buffer is at most `N/2^(j+2) + 2`. -/
lemma geometricBufferLength_cast_le (N : ℕ → ℕ) (j : ℕ) :
    (geometricBufferLength N j : ℝ) ≤
      (N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ) + 2 := by
  have hx : 0 ≤ (N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  simp only [geometricBufferLength, Nat.cast_add, Nat.cast_one]
  linarith

/-- The block length is absorbed by `2^(j+2)` copies of its buffer. -/
lemma length_le_pow_mul_geometricBufferLength (N : ℕ → ℕ) (j : ℕ) :
    N j ≤ 2 ^ (j + 2) * geometricBufferLength N j := by
  have hq : (0 : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by positivity
  have hc := Nat.le_ceil
    ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ))
  rw [div_le_iff₀ hq] at hc
  have hc' : N j ≤ 2 ^ (j + 2) *
      (Nat.ceil ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ))) := by
    have hc' : (N j : ℝ) ≤
        ((2 ^ (j + 2) : ℕ) : ℝ) *
          (Nat.ceil ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ)) : ℝ) := by
      simpa [mul_comm] using hc
    exact_mod_cast hc'
  exact hc'.trans (Nat.mul_le_mul_left _ (by simp [geometricBufferLength]))

/-- The endpoint fits in the announced dyadic shell. -/
lemma cut_succ_le_geometricDyadicExponent_mul_pivot
    (N : ℕ → ℕ) (j : ℕ) :
    cut (geometricBufferLength N) N (j + 1) ≤
      2 ^ geometricDyadicExponent j * pivot (geometricBufferLength N) N j := by
  let P := pivot (geometricBufferLength N) N j
  let q := 2 ^ (j + 2)
  have hNP : N j ≤ q * P := by
    have hNL := length_le_pow_mul_geometricBufferLength N j
    have hLP : geometricBufferLength N j ≤ P := by
      dsimp [P]
      simp [pivot]
    exact hNL.trans (Nat.mul_le_mul_left q hLP)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hPP : P ≤ q * P := by
    nlinarith
  rw [cut_succ]
  change P + N j ≤ 2 ^ (j + 3) * P
  calc
    P + N j ≤ q * P + q * P := Nat.add_le_add hPP hNP
    _ = 2 ^ (j + 3) * P := by
      dsimp [q]
      rw [show j + 3 = (j + 2) + 1 by omega, pow_succ]
      ring

/-- Rapid convergence of the block densities makes the explicit positive
buffer compensate every possible deficit below `δ`. -/
lemma geometricBufferLength_compensates
    {δ : ℝ} (hδ : δ ≤ 3 / 4) (α : ℕ → ℝ) (N : ℕ → ℕ)
    (hfast : ∀ j, |α j - δ| ≤ (1 - δ) / ((2 ^ (j + 2) : ℕ) : ℝ))
    (j : ℕ) :
    (δ - min (α j) δ) * (N j : ℝ) ≤
      (1 - δ) * (geometricBufferLength N j : ℝ) := by
  have hδone : 0 ≤ 1 - δ := by linarith
  have hdef : δ - min (α j) δ ≤ |α j - δ| := by
    by_cases h : α j ≤ δ
    · rw [min_eq_left h]
      simpa [abs_sub_comm] using (le_abs_self (δ - α j))
    · have h' : δ ≤ α j := le_of_not_ge h
      rw [min_eq_right h']
      have habs : (0 : ℝ) ≤ |α j - δ| := abs_nonneg _
      linarith
  have hdef' : δ - min (α j) δ ≤
      (1 - δ) / ((2 ^ (j + 2) : ℕ) : ℝ) :=
    hdef.trans (hfast j)
  have hceil : (N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ) ≤
      (geometricBufferLength N j : ℝ) := by
    have hc := Nat.le_ceil
      ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ))
    have hstep : (Nat.ceil
        ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ)) : ℝ) ≤
        (geometricBufferLength N j : ℝ) := by
      simp [geometricBufferLength]
    exact hc.trans hstep
  calc
    (δ - min (α j) δ) * (N j : ℝ) ≤
        ((1 - δ) / ((2 ^ (j + 2) : ℕ) : ℝ)) * (N j : ℝ) :=
      mul_le_mul_of_nonneg_right hdef' (Nat.cast_nonneg _)
    _ = (1 - δ) *
        ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ)) := by ring
    _ ≤ (1 - δ) * (geometricBufferLength N j : ℝ) :=
      mul_le_mul_of_nonneg_left hceil hδone

lemma small_pow_le_large_pow (j : ℕ) :
    2 ^ (j + 2) ≤ 2 ^ (j + 10) := by
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) (by omega)

/-- Even at stage zero, positivity of the block length gives a uniform
comparison between the small dyadic scale and the block length. -/
lemma small_pow_le_four_mul_length
    (N : ℕ → ℕ) (hNpos : ∀ j, 0 < N j)
    (hdom : ∀ j, 2 ^ (j + 10) * cut (geometricBufferLength N) N j ≤ N j)
    (j : ℕ) :
    2 ^ (j + 2) ≤ 4 * N j := by
  cases j with
  | zero =>
      have := hNpos 0
      norm_num
      exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt this)
  | succ j =>
      have hcut : 1 ≤ cut (geometricBufferLength N) N (j + 1) := by
        rw [cut_succ]
        have := hNpos j
        omega
      have hbig : 2 ^ ((j + 1) + 10) ≤ N (j + 1) := by
        calc
          2 ^ ((j + 1) + 10) ≤
              2 ^ ((j + 1) + 10) * cut (geometricBufferLength N) N (j + 1) := by
            exact Nat.le_mul_of_pos_right _ hcut
          _ ≤ N (j + 1) := hdom (j + 1)
      have hsmall : 2 ^ ((j + 1) + 2) ≤ N (j + 1) :=
        (small_pow_le_large_pow (j + 1)).trans hbig
      omega

/-- The old-prefix numerator is controlled by a linear coefficient times
`pivot + 1`. -/
lemma oldBound_le_linear_mul_pivot_add_one
    (K : ℕ) (d L N : ℕ → ℕ) (j : ℕ) :
    oldBound K d L N j ≤
      (K * d j + 3) * (pivot L N j + 1) := by
  simp only [oldBound]
  nlinarith

/-- The scale assumptions force `pivot + 1` to occupy only an exponentially
small fraction of the endpoint. -/
lemma pow_mul_pivot_add_one_le_fourteen_mul_cut_succ
    (N : ℕ → ℕ) (hNpos : ∀ j, 0 < N j)
    (hdom : ∀ j, 2 ^ (j + 10) * cut (geometricBufferLength N) N j ≤ N j)
    (j : ℕ) :
    2 ^ (j + 2) * (pivot (geometricBufferLength N) N j + 1) ≤
      14 * cut (geometricBufferLength N) N (j + 1) := by
  let q : ℕ := 2 ^ (j + 2)
  let P : ℕ := pivot (geometricBufferLength N) N j
  let T : ℕ := cut (geometricBufferLength N) N (j + 1)
  have hqpos : (0 : ℝ) < q := by dsimp [q]; positivity
  have hqbig : q ≤ 2 ^ (j + 10) := small_pow_le_large_pow j
  have hqcutNat : q * cut (geometricBufferLength N) N j ≤ N j := by
    calc
      q * cut (geometricBufferLength N) N j ≤
          2 ^ (j + 10) * cut (geometricBufferLength N) N j :=
        Nat.mul_le_mul_right _ hqbig
      _ ≤ N j := hdom j
  have hqNnat : q ≤ 4 * N j := small_pow_le_four_mul_length N hNpos hdom j
  have hL := geometricBufferLength_cast_le N j
  have hqcut : (q : ℝ) * (cut (geometricBufferLength N) N j : ℝ) ≤
      (N j : ℝ) := by exact_mod_cast hqcutNat
  have hqN : (q : ℝ) ≤ 4 * (N j : ℝ) := by exact_mod_cast hqNnat
  have hqL : (q : ℝ) * (geometricBufferLength N j : ℝ) ≤
      (N j : ℝ) + 2 * q := by
    have := mul_le_mul_of_nonneg_left hL hqpos.le
    dsimp [q] at this ⊢
    rw [mul_add] at this
    have hqne : (((2 ^ (j + 2) : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hqne] at this ⊢
    linarith
  have hqP : (q : ℝ) * ((P + 1 : ℕ) : ℝ) ≤
      14 * (N j : ℝ) := by
    dsimp [P, pivot]
    push_cast
    nlinarith
  have hNT : N j ≤ T := by
    dsimp [T]
    rw [cut_succ]
    omega
  have hqPT : (q : ℝ) * ((P + 1 : ℕ) : ℝ) ≤
      14 * (T : ℝ) :=
    hqP.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hNT) (by norm_num))
  exact_mod_cast hqPT

/-- A linear polynomial divided by `2^(j+2)` tends to zero. -/
lemma tendsto_fourteen_mul_linear_div_pow (K : ℕ) :
    Tendsto (fun j : ℕ ↦
      14 * ((K * (j + 3) + 3 : ℕ) : ℝ) /
        ((2 ^ (j + 2) : ℕ) : ℝ)) atTop (nhds 0) := by
  have hj : Tendsto (fun j : ℕ ↦ (j : ℝ) * (1 / 2 : ℝ) ^ j)
      atTop (nhds 0) :=
    by simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).tendsto_atTop_zero
  have hg : Tendsto (fun j : ℕ ↦ (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsum := (hj.const_mul (14 * (K : ℝ) / 4)).add
    (hg.const_mul (14 * (3 * (K : ℝ) + 3) / 4))
  convert hsum using 1
  · funext j
    push_cast
    rw [show j + 2 = j + 2 by rfl, pow_add]
    simp only [div_pow, one_pow]
    norm_num
    ring
  · norm_num

/-- The complete old-prefix error tends to zero under rapid stage growth. -/
lemma oldBound_div_cut_tendsto_zero
    (N : ℕ → ℕ) (hNpos : ∀ j, 0 < N j)
    (hdom : ∀ j, 2 ^ (j + 10) * cut (geometricBufferLength N) N j ≤ N j)
    (K : ℕ) :
    Tendsto (fun j ↦
      (oldBound K geometricDyadicExponent (geometricBufferLength N) N j : ℝ) /
        (cut (geometricBufferLength N) N (j + 1) : ℝ)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro j
    positivity
  · intro j
    let q : ℕ := 2 ^ (j + 2)
    let P : ℕ := pivot (geometricBufferLength N) N j
    let T : ℕ := cut (geometricBufferLength N) N (j + 1)
    have hqpos : (0 : ℝ) < q := by dsimp [q]; positivity
    have hTpos : (0 : ℝ) < T := by
      dsimp [T]
      rw [cut_succ]
      exact_mod_cast Nat.add_pos_right P (hNpos j)
    have holdNat := oldBound_le_linear_mul_pivot_add_one
      K geometricDyadicExponent (geometricBufferLength N) N j
    have hold : (oldBound K geometricDyadicExponent
        (geometricBufferLength N) N j : ℝ) ≤
        ((K * geometricDyadicExponent j + 3 : ℕ) : ℝ) * ((P + 1 : ℕ) : ℝ) := by
      exact_mod_cast holdNat
    have hpNat := pow_mul_pivot_add_one_le_fourteen_mul_cut_succ N hNpos hdom j
    have hp : ((P + 1 : ℕ) : ℝ) / (T : ℝ) ≤ 14 / (q : ℝ) := by
      rw [div_le_div_iff₀ hTpos hqpos]
      have hp' : ((q * (pivot (geometricBufferLength N) N j + 1) : ℕ) : ℝ) ≤
          ((14 * cut (geometricBufferLength N) N (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast hpNat
      simpa [P, T, q, mul_comm] using hp'
    calc
      (oldBound K geometricDyadicExponent (geometricBufferLength N) N j : ℝ) /
          (cut (geometricBufferLength N) N (j + 1) : ℝ) ≤
          (((K * geometricDyadicExponent j + 3 : ℕ) : ℝ) *
            ((P + 1 : ℕ) : ℝ)) / (T : ℝ) := by
        simpa [T] using div_le_div_of_nonneg_right hold hTpos.le
      _ = ((K * geometricDyadicExponent j + 3 : ℕ) : ℝ) *
          (((P + 1 : ℕ) : ℝ) / (T : ℝ)) := by ring
      _ ≤ ((K * geometricDyadicExponent j + 3 : ℕ) : ℝ) *
          (14 / (q : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
      _ = 14 * ((K * (j + 3) + 3 : ℕ) : ℝ) /
          ((2 ^ (j + 2) : ℕ) : ℝ) := by
        simp [geometricDyadicExponent, q]
        ring
  · exact tendsto_fourteen_mul_linear_div_pow K

end EndpointLimits


/-- Shift a cyclic residue word from `[0,N)` to positive positions `[1,N]`. -/
def shiftedResidueWord (B : Finset ℕ) : Finset ℕ :=
  B.image fun x ↦ x + 1

lemma shiftedResidueWord_support {B : Finset ℕ} {N : ℕ}
    (hB : B ⊆ Finset.range N) :
    shiftedResidueWord B ⊆ Finset.Ioc 0 N := by
  intro y hy
  rw [shiftedResidueWord, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxN := Finset.mem_range.mp (hB hx)
  simp only [Finset.mem_Ioc]
  omega

@[simp] lemma card_shiftedResidueWord (B : Finset ℕ) :
    (shiftedResidueWord B).card = B.card := by
  rw [shiftedResidueWord, Finset.card_image_of_injective]
  intro x y hxy
  change x + 1 = y + 1 at hxy
  exact Nat.add_right_cancel hxy

lemma wordPrefixCount_shiftedResidueWord (B : Finset ℕ) (t : ℕ) :
    wordPrefixCount (shiftedResidueWord B) t =
      (B.filter fun x ↦ x < t).card := by
  classical
  unfold wordPrefixCount shiftedResidueWord
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective]
  · congr 1
  · intro x y hxy
    change x + 1 = y + 1 at hxy
    exact Nat.add_right_cancel hxy

open ConcreteFattening DeterministicScore

/-- Reducing a positive current-window sum by one identifies it with the
cyclic sum of the original residue and the corresponding element of `A`.
This is the bridge from cyclic niveau witnesses to positive concatenation
words. -/
lemma currentWindow_shiftedResidueWord_card_le
    (A : Set ℕ) (B : Finset ℕ) (N : ℕ) (_hN : 0 < N) :
    (currentWindow A (shiftedResidueWord B) N).card ≤
      (cyclicImageSumset N B
        (insert 0 ((Finset.Icc 1 N).filter fun a ↦ a ∈ A))).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun y : ℕ ↦ y - 1)
  · intro y hy
    have hyWindow := Finset.mem_filter.mp hy
    have hyI := Finset.mem_Ioc.mp hyWindow.2
    rw [Finset.mem_add] at hyWindow
    obtain ⟨w, hw, a, ha, hwa⟩ := hyWindow.1
    rw [shiftedResidueWord, Finset.mem_image] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    change y - 1 ∈ cyclicImageSumset N B
      (insert 0 ((Finset.Icc 1 N).filter fun a ↦ a ∈ A))
    rw [cyclicImageSumset, Finset.mem_image]
    refine ⟨b + a, ?_, ?_⟩
    · rw [Finset.mem_add]
      refine ⟨b, hb, a, ?_, rfl⟩
      have haTrunc := Finset.mem_filter.mp ha
      have haIcc := Finset.mem_Icc.mp haTrunc.1
      by_cases ha0 : a = 0
      · subst a
        simp
      · rw [Finset.mem_insert]
        right
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, haIcc.2⟩, haTrunc.2⟩
    · have heq : y = b + a + 1 := by omega
      have hlt : b + a < N := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
  · intro x hx y hy hxy
    have hxI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).2
    have hyI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).2
    change x - 1 = y - 1 at hxy
    omega

/-- One cyclic witness chosen at raw index `n`, with enough length to dominate
the accumulated budget `q`. -/
structure RapidFiniteStage (A : Set ℕ) (n q : ℕ) where
  length : ℕ
  residues : Finset ℕ
  length_pos : 0 < length
  support : residues ⊆ Finset.range length
  lower_card : length ≤ 4 * residues.card
  upper_card : 4 * residues.card ≤ 3 * length
  prefixPinned : ∀ t ≤ length,
    residues.card * t ≤ length * (residues.filter fun x ↦ x < t).card
  cyclic_upper :
    ((cyclicImageSumset length residues
      (insert 0 ((Finset.Icc 1 length).filter fun a ↦ a ∈ A))).card : ℝ) ≤
      (residues.card : ℝ) +
        (224 / ((n + 4 : ℕ) : ℝ)) * (length : ℝ)
  growth : 2 ^ (n + 10) * (q + 1) ≤ length

lemma exists_rapidFiniteStage {A : Set ℕ} (hA : IsLacunary A) (n q : ℕ) :
    Nonempty (RapidFiniteStage A n q) := by
  obtain ⟨N₀, hN₀0, hN₀⟩ :=
    exists_eventually_rotated_finiteNiveauWitness_of_lacunary hA (n + 4) (by omega)
  let N := 4 * max N₀ (2 ^ (n + 10) * (q + 1))
  have hNpos : 0 < N := by
    dsimp [N]
    have : 0 < max N₀ (2 ^ (n + 10) * (q + 1)) := by omega
    omega
  have hN₀N : N₀ ≤ N := by
    dsimp [N]
    omega
  have hN4 : 4 ∣ N := by exact dvd_mul_right 4 _
  obtain ⟨B, hB, hlo, hhi, hprefix, hexp⟩ := hN₀ N hN₀N hN4
  exact ⟨⟨N, B, hNpos, hB, hlo, hhi, hprefix, hexp, by
    dsimp [N]
    omega⟩⟩

noncomputable def rapidFiniteStage {A : Set ℕ} (hA : IsLacunary A)
    (n q : ℕ) : RapidFiniteStage A n q :=
  Classical.choice (exists_rapidFiniteStage hA n q)

/-- Raw cumulative budget.  It dominates a word and its later positive
geometric buffer by charging `2N+1` per raw stage. -/
noncomputable def rapidBudget {A : Set ℕ} (hA : IsLacunary A) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let s := rapidFiniteStage hA n (rapidBudget hA n)
      rapidBudget hA n + (2 * s.length + 1)

noncomputable def rawRapidStage {A : Set ℕ} (hA : IsLacunary A) (n : ℕ) :
    RapidFiniteStage A n (rapidBudget hA n) :=
  rapidFiniteStage hA n (rapidBudget hA n)

@[simp] lemma rapidBudget_zero {A : Set ℕ} (hA : IsLacunary A) :
    rapidBudget hA 0 = 0 := rfl

lemma rapidBudget_succ {A : Set ℕ} (hA : IsLacunary A) (n : ℕ) :
    rapidBudget hA (n + 1) = rapidBudget hA n +
      (2 * (rawRapidStage hA n).length + 1) := by
  rfl

lemma rapidBudget_eq_sum {A : Set ℕ} (hA : IsLacunary A) (n : ℕ) :
    rapidBudget hA n =
      ∑ i ∈ Finset.range n, (2 * (rawRapidStage hA i).length + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        rapidBudget hA (n + 1) = rapidBudget hA n +
            (2 * (rawRapidStage hA n).length + 1) := rapidBudget_succ hA n
        _ = (∑ i ∈ Finset.range n,
              (2 * (rawRapidStage hA i).length + 1)) +
            (2 * (rawRapidStage hA n).length + 1) :=
          congrArg (fun z ↦ z + (2 * (rawRapidStage hA n).length + 1)) ih
        _ = ∑ i ∈ Finset.range (n + 1),
              (2 * (rawRapidStage hA i).length + 1) := by
          rw [Finset.sum_range_succ]

def geometricBuffer (N : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.ceil ((N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ)) + 1

lemma geometricBuffer_pos (N : ℕ → ℕ) (j : ℕ) :
    0 < geometricBuffer N j := by
  simp [geometricBuffer]

lemma geometricBuffer_le_add_one (N : ℕ → ℕ) (j : ℕ) :
    geometricBuffer N j ≤ N j + 1 := by
  have hpow : (1 : ℝ) ≤ ((2 ^ (j + 2) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow (j + 2) 2 (by norm_num))
  have hN : (0 : ℝ) ≤ N j := by positivity
  have hdiv : (N j : ℝ) / ((2 ^ (j + 2) : ℕ) : ℝ) ≤ N j := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ))).2
      (by nlinarith)
  have hceil : Nat.ceil ((N j : ℝ) /
      ((2 ^ (j + 2) : ℕ) : ℝ)) ≤ N j :=
    Nat.ceil_le.mpr (by exact_mod_cast hdiv)
  simpa [geometricBuffer] using Nat.add_le_add_right hceil 1

lemma length_le_pow_mul_geometricBuffer (N : ℕ → ℕ) (j : ℕ) :
    N j ≤ 2 ^ (j + 2) * geometricBuffer N j := by
  let q : ℕ := 2 ^ (j + 2)
  have hq : 0 < q := by positivity
  have hceil := Nat.le_ceil ((N j : ℝ) / (q : ℝ))
  have hmul : (N j : ℝ) ≤
      (q : ℝ) * (Nat.ceil ((N j : ℝ) / (q : ℝ)) : ℝ) := by
    rw [div_le_iff₀ (by exact_mod_cast hq)] at hceil
    simpa [mul_comm] using hceil
  have hnat : N j ≤ q * Nat.ceil ((N j : ℝ) / (q : ℝ)) := by
    exact_mod_cast hmul
  dsimp [q] at hnat
  exact hnat.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

lemma cut_eq_sum (L N : ℕ → ℕ) (j : ℕ) :
    cut L N j = ∑ i ∈ Finset.range j, (L i + N i) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [cut_succ, pivot, ih, Finset.sum_range_succ]
      omega

lemma cut_selected_le_rapidBudget {A : Set ℕ} (hA : IsLacunary A)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (N : ℕ → ℕ) (hN : ∀ j, N j = (rawRapidStage hA (φ j)).length)
    (L : ℕ → ℕ) (hL : ∀ j, L j ≤ N j + 1) (j : ℕ) :
    cut L N j ≤ rapidBudget hA (φ j) := by
  rw [cut_eq_sum, rapidBudget_eq_sum]
  calc
    (∑ i ∈ Finset.range j, (L i + N i)) ≤
        ∑ i ∈ Finset.range j,
          (2 * (rawRapidStage hA (φ i)).length + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiL := hL i
      rw [hN i] at hiL ⊢
      omega
    _ = ∑ k ∈ (Finset.range j).image φ,
          (2 * (rawRapidStage hA k).length + 1) := by
      rw [Finset.sum_image]
      exact hφ.injective.injOn
    _ ≤ ∑ k ∈ Finset.range (φ j),
          (2 * (rawRapidStage hA k).length + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi ⊢
        exact hφ hi
      · intro i hi hnot
        positivity

lemma pow_mul_cut_le_selected_length {A : Set ℕ} (hA : IsLacunary A)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφge : ∀ j, j ≤ φ j)
    (N : ℕ → ℕ) (hN : ∀ j, N j = (rawRapidStage hA (φ j)).length)
    (L : ℕ → ℕ) (hL : ∀ j, L j ≤ N j + 1) (j : ℕ) :
    2 ^ (j + 10) * cut L N j ≤ N j := by
  have hcut := cut_selected_le_rapidBudget hA φ hφ N hN L hL j
  have hgrowth := (rawRapidStage hA (φ j)).growth
  have hpow : 2 ^ (j + 10) ≤ 2 ^ (φ j + 10) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right (hφge j) 10)
  rw [hN j]
  calc
    2 ^ (j + 10) * cut L N j ≤
        2 ^ (φ j + 10) * rapidBudget hA (φ j) := by
      exact Nat.mul_le_mul hpow hcut
    _ ≤ 2 ^ (φ j + 10) * (rapidBudget hA (φ j) + 1) := by
      exact Nat.mul_le_mul_left _ (Nat.le_add_right _ 1)
    _ ≤ (rawRapidStage hA (φ j)).length := hgrowth

/-- The density of the raw cyclic residue word. -/
noncomputable def rawRapidDensity {A : Set ℕ} (hA : IsLacunary A)
    (n : ℕ) : ℝ :=
  ((rawRapidStage hA n).residues.card : ℝ) /
    ((rawRapidStage hA n).length : ℝ)

lemma rawRapidDensity_mem_Icc {A : Set ℕ} (hA : IsLacunary A) (n : ℕ) :
    rawRapidDensity hA n ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hpos := (rawRapidStage hA n).length_pos
  have hden : (0 : ℝ) < (rawRapidStage hA n).length := by exact_mod_cast hpos
  have hlo := (rawRapidStage hA n).lower_card
  have hhi := (rawRapidStage hA n).upper_card
  constructor
  · rw [rawRapidDensity, le_div_iff₀ hden]
    have hloR : ((rawRapidStage hA n).length : ℝ) ≤
        4 * ((rawRapidStage hA n).residues.card : ℝ) := by
      exact_mod_cast hlo
    nlinarith
  · rw [rawRapidDensity, div_le_iff₀ hden]
    have hhiR : 4 * ((rawRapidStage hA n).residues.card : ℝ) ≤
        3 * ((rawRapidStage hA n).length : ℝ) := by
      exact_mod_cast hhi
    nlinarith

/-- A rapidly separated subsequence of finite niveau witnesses, assembled as
positive word positions.  Besides the `PinnedCyclicWords` interface, this
packages the geometric density rate, a scale estimate valid for every small
buffer, and the direct current-window estimate needed by lacunary fattening. -/
theorem exists_rapidPinnedCyclicWords {A : Set ℕ} (hA : IsLacunary A) :
    ∃ δ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      ∃ w : PinnedCyclicWords δ,
        (∀ j, |w.density j - δ| ≤ (1 - δ) / (2 : ℝ) ^ (j + 2)) ∧
        (∀ L : ℕ → ℕ, (∀ j, L j ≤ w.length j + 1) →
          ∀ j, 2 ^ (j + 10) * cut L w.length j ≤ w.length j) ∧
        ∀ j,
          ((currentWindow A (w.word j) (w.length j)).card : ℝ) ≤
            (w.density j + w.expansionError j) * (w.length j : ℝ) := by
  obtain ⟨δ, hδ, φ, hφ, hlim, hφge, hfast⟩ :=
    exists_strictMono_subsequence_with_geometric_bound
      (rawRapidDensity hA) (rawRapidDensity_mem_Icc hA)
  let N : ℕ → ℕ := fun j ↦ (rawRapidStage hA (φ j)).length
  let B : ℕ → Finset ℕ := fun j ↦ (rawRapidStage hA (φ j)).residues
  let W : ℕ → Finset ℕ := fun j ↦ shiftedResidueWord (B j)
  let α : ℕ → ℝ := fun j ↦ rawRapidDensity hA (φ j)
  let η : ℕ → ℝ := fun j ↦ 224 / (((φ j + 4 : ℕ) : ℝ))
  have hNpos : ∀ j, 0 < N j := fun j ↦ (rawRapidStage hA (φ j)).length_pos
  have hηlim : Tendsto η atTop (nhds 0) := by
    have hnat : Tendsto (fun j ↦ φ j + 4) atTop atTop :=
      (Filter.tendsto_add_atTop_nat 4).comp hφ.tendsto_atTop
    have hreal : Tendsto (fun j ↦ (((φ j + 4 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hnat
    simpa [η] using (tendsto_const_nhds.div_atTop hreal :
      Tendsto (fun j ↦ (224 : ℝ) / (((φ j + 4 : ℕ) : ℝ))) atTop (nhds 0))
  let w : PinnedCyclicWords δ :=
    { length := N
      word := W
      density := α
      expansionError := η
      length_pos := hNpos
      support := by
        intro j
        exact shiftedResidueWord_support (rawRapidStage hA (φ j)).support
      card_eq := by
        intro j
        have hn : (0 : ℝ) < N j := by exact_mod_cast hNpos j
        simp only [W, card_shiftedResidueWord, α, rawRapidDensity, N, B]
        exact (div_mul_cancel₀ _ (ne_of_gt hn)).symm
      density_mem := by
        intro j
        exact rawRapidDensity_mem_Icc hA (φ j)
      prefixPinned := by
        intro j t ht
        have hp := (rawRapidStage hA (φ j)).prefixPinned t ht
        have hn : (0 : ℝ) < N j := by exact_mod_cast hNpos j
        simp only [W, wordPrefixCount_shiftedResidueWord]
        change rawRapidDensity hA (φ j) * (t : ℝ) ≤ _
        rw [rawRapidDensity, div_mul_eq_mul_div, div_le_iff₀ hn]
        have hpR :
            ((rawRapidStage hA (φ j)).residues.card : ℝ) * (t : ℝ) ≤
              ((rawRapidStage hA (φ j)).length : ℝ) *
                (((rawRapidStage hA (φ j)).residues.filter fun x ↦ x < t).card : ℝ) := by
          exact_mod_cast hp
        simpa [N, B, mul_comm] using hpR
      density_tendsto := by
        simpa [α, Function.comp_def] using hlim
      expansionError_tendsto := hηlim }
  refine ⟨δ, hδ, w, ?_, ?_, ?_⟩
  · intro j
    exact hfast j
  · intro L hL j
    exact pow_mul_cut_le_selected_length hA φ hφ hφge N
      (fun i ↦ rfl) L (by simpa [w] using hL) j
  · intro j
    have hcur := currentWindow_shiftedResidueWord_card_le A
      (B j) (N j) (hNpos j)
    have hcurR : ((currentWindow A (W j) (N j)).card : ℝ) ≤
        ((cyclicImageSumset (N j) (B j)
          (insert 0 ((Finset.Icc 1 (N j)).filter fun a ↦ a ∈ A))).card : ℝ) := by
      exact_mod_cast hcur
    have hexp := (rawRapidStage hA (φ j)).cyclic_upper
    have hn : (0 : ℝ) < N j := by exact_mod_cast hNpos j
    change ((currentWindow A (w.word j) (w.length j)).card : ℝ) ≤
      (w.density j + w.expansionError j) * (w.length j : ℝ)
    dsimp [w]
    exact hcurR.trans (hexp.trans_eq (by
      simp only [α, η, rawRapidDensity, N]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hn)]))

namespace ConcreteFattening

/-- Variant of `boundsOfLacunary` for positive shifted words: the application
supplies the ordinary current-window bound directly. -/
noncomputable def boundsOfLacunaryCurrent
    (A : Set ℕ) {δ : ℝ} (w : PinnedCyclicWords δ) (hA : IsLacunary A)
    (L d : ℕ → ℕ)
    (hcomp : ∀ j,
      (δ - min (w.density j) δ) * (w.length j : ℝ) ≤
        (1 - δ) * (L j : ℝ))
    (hP : ∀ j, 1 ≤ pivot L w.length j)
    (hdyadic : ∀ j,
      cut L w.length (j + 1) ≤ 2 ^ d j * pivot L w.length j)
    (hscale : ∀ K : ℕ, 1 ≤ K →
      Tendsto (fun j ↦
        (oldBound K d L w.length j : ℝ) /
          (cut L w.length (j + 1) : ℝ)) atTop (nhds 0))
    (hexp_nonneg : ∀ j, 0 ≤ w.density j + w.expansionError j)
    (hcurrent : ∀ j,
      ((currentWindow A (w.word j) (w.length j)).card : ℝ) ≤
        (w.density j + w.expansionError j) * (w.length j : ℝ)) :
    FatteningBounds A w := by
  let hex := lacunary_shell_and_fattening_bounds hA
  let K := Classical.choose hex
  have hK : 1 ≤ K := (Classical.choose_spec hex).1
  have hshell := (Classical.choose_spec hex).2
  refine
    { bufferLength := L
      compensation := hcomp
      oldError := fun j ↦
        (oldBound K d L w.length j : ℝ) /
          (cut L w.length (j + 1) : ℝ)
      oldError_tendsto := hscale K hK
      endpoint_upper := ?_ }
  intro j
  let P := pivot L w.length j
  let T := cut L w.length (j + 1)
  let q := w.density j + w.expansionError j
  have hTformula : T = P + w.length j := by simp [T, P]
  have hTpos : (0 : ℝ) < T := by
    have hTnat : 0 < T := by
      rw [hTformula]
      exact Nat.add_pos_right P (w.length_pos j)
    exact_mod_cast hTnat
  have hNT : w.length j ≤ T := by rw [hTformula]; omega
  have hold := (hshell (hP j) (hdyadic j)).2
  have hold' :
      (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) ≤
        (oldBound K d L w.length j : ℝ) := by
    exact_mod_cast hold
  have hdecomp := countIn_endpoint_le_old_add_current A w.word L w.length
    w.length_pos w.support j
  have hcount : (countIn (A + globalSet w.word L w.length) T : ℝ) ≤
      (oldBound K d L w.length j : ℝ) + q * (w.length j : ℝ) := by
    have hdecompCast : (countIn (A + globalSet w.word L w.length) T : ℝ) ≤
        (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) +
          ((currentWindow A (w.word j) (w.length j)).card : ℝ) := by
      exact_mod_cast hdecomp
    exact hdecompCast.trans (add_le_add hold' (hcurrent j))
  have hq : 0 ≤ q := hexp_nonneg j
  have hqNT : q * (w.length j : ℝ) ≤ q * T := by
    apply mul_le_mul_of_nonneg_left _ hq
    exact_mod_cast hNT
  have hcancel :
      ((oldBound K d L w.length j : ℝ) / T) * T =
        (oldBound K d L w.length j : ℝ) := by
    field_simp
  change (countIn (A + globalSet w.word L w.length) T : ℝ) / T ≤
    q + (oldBound K d L w.length j : ℝ) / T
  rw [div_le_iff₀ hTpos]
  nlinarith

end ConcreteFattening

/-- A lacunary set containing zero has a witness on which addition preserves
Schnirelmann density.  The witness density is uniformly separated from both
zero and one. -/
theorem exists_equal_schnirelmannDensity_of_lacunary
    {A : Set ℕ} (hA : IsLacunary A) (hzero : 0 ∈ A) :
    ∃ δ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ), ∃ C : Set ℕ,
      sd C = δ ∧ sd (A + C) = δ := by
  obtain ⟨δ, hδ, w, hfast, hgrowth, hcurrent⟩ :=
    exists_rapidPinnedCyclicWords hA
  let L : ℕ → ℕ := EndpointLimits.geometricBufferLength w.length
  let d : ℕ → ℕ := EndpointLimits.geometricDyadicExponent
  have hL : ∀ j, L j ≤ w.length j + 1 := by
    intro j
    simpa [L, EndpointLimits.geometricBufferLength, geometricBuffer] using
      geometricBuffer_le_add_one w.length j
  have hdom : ∀ j, 2 ^ (j + 10) * cut L w.length j ≤ w.length j :=
    hgrowth L hL
  have hcomp : ∀ j,
      (δ - min (w.density j) δ) * (w.length j : ℝ) ≤
        (1 - δ) * (L j : ℝ) := by
    intro j
    apply EndpointLimits.geometricBufferLength_compensates hδ.2
    intro i
    simpa using hfast i
  have hP : ∀ j, 1 ≤ pivot L w.length j := by
    intro j
    exact EndpointLimits.one_le_pivot_geometricBufferLength w.length j
  have hdyadic : ∀ j,
      cut L w.length (j + 1) ≤ 2 ^ d j * pivot L w.length j := by
    intro j
    exact EndpointLimits.cut_succ_le_geometricDyadicExponent_mul_pivot
      w.length j
  have hscale : ∀ K : ℕ, 1 ≤ K →
      Tendsto (fun j ↦
        (ConcreteFattening.oldBound K d L w.length j : ℝ) /
          (cut L w.length (j + 1) : ℝ)) atTop (nhds 0) := by
    intro K hK
    exact EndpointLimits.oldBound_div_cut_tendsto_zero
      w.length w.length_pos (by simpa [L] using hdom) K
  have hnonneg : ∀ j, 0 ≤ w.density j + w.expansionError j := by
    intro j
    have hc := hcurrent j
    have hlen : (0 : ℝ) < w.length j := by exact_mod_cast w.length_pos j
    have hcard : (0 : ℝ) ≤
        ((ConcreteFattening.currentWindow A (w.word j) (w.length j)).card : ℝ) := by
      positivity
    nlinarith
  let b : FatteningBounds A w :=
    ConcreteFattening.boundsOfLacunaryCurrent A w hA L d hcomp hP hdyadic
      hscale hnonneg hcurrent
  let C : Set ℕ := globalSet w.word L w.length
  have heq := schnirelmann_eq w b (by linarith [hδ.2]) hzero
  have hbL : b.bufferLength = L := by
    rfl
  rw [hbL] at heq
  exact ⟨δ, hδ, C, by simpa [C] using heq⟩

end InfiniteAssembly

/-! ## No-buffer concatenation for lower asymptotic density -/

namespace InfiniteAssembly.NoBuffer

/-- The identically-zero buffer sequence. -/
def zeroBuffer : ℕ → ℕ := fun _ ↦ 0

/-- Stage endpoints for the unbuffered concatenation. -/
def stageCut {δ : ℝ} (w : PinnedCyclicWords δ) : ℕ → ℕ :=
  cut zeroBuffer w.length

/-- The direct concatenation of the finite words, with no filled buffers. -/
def concatenation {δ : ℝ} (w : PinnedCyclicWords δ) : Set ℕ :=
  globalSet w.word zeroBuffer w.length

@[simp] lemma pivot_zeroBuffer (N : ℕ → ℕ) (j : ℕ) :
    pivot zeroBuffer N j = cut zeroBuffer N j := by
  simp [pivot, zeroBuffer]

@[simp] lemma stageCut_zero {δ : ℝ} (w : PinnedCyclicWords δ) :
    stageCut w 0 = 0 := by
  simp [stageCut]

@[simp] lemma stageCut_succ {δ : ℝ} (w : PinnedCyclicWords δ) (j : ℕ) :
    stageCut w (j + 1) = stageCut w j + w.length j := by
  simp [stageCut, cut_succ]

lemma stageCut_strict {δ : ℝ} (w : PinnedCyclicWords δ) :
    StrictMono (stageCut w) := by
  simpa [stageCut] using cut_strictMono zeroBuffer w.length w.length_pos

lemma index_le_stageCut {δ : ℝ} (w : PinnedCyclicWords δ) (j : ℕ) :
    j ≤ stageCut w j := by
  induction j with
  | zero => simp
  | succ j ih =>
      exact (Nat.succ_le_succ ih).trans
        ((stageCut_strict w) (Nat.lt_succ_self j))

/-- Prefix pinning of one finite word is exactly the lower bound for the
corresponding portion of the unbuffered global concatenation. -/
lemma stage_lower {δ : ℝ} (w : PinnedCyclicWords δ) (j n : ℕ)
    (hleft : stageCut w j ≤ n) (hright : n ≤ stageCut w (j + 1)) :
    w.density j * ((n - stageCut w j : ℕ) : ℝ) ≤
      (segmentCount (concatenation w) (stageCut w j) n : ℝ) := by
  let m := n - stageCut w j
  have hm : m ≤ w.length j := by
    dsimp [m]
    rw [stageCut_succ] at hright
    omega
  have hpin := w.prefixPinned j m hm
  have hcount := wordPrefixCount_le_segmentCount
    w.word zeroBuffer w.length w.support j m
  have hpivot : pivot zeroBuffer w.length j = stageCut w j := by
    simp [stageCut]
  have hadd : stageCut w j + m = n := by
    dsimp [m]
    omega
  rw [hpivot, hadd] at hcount
  have hcount' : (wordPrefixCount (w.word j) m : ℝ) ≤
      (segmentCount (concatenation w) (stageCut w j) n : ℝ) := by
    exact_mod_cast hcount
  exact hpin.trans hcount'

/-- If all words from stage `J` onward have density at least `γ`, then every
completed tail from `J` has density at least `γ`. -/
lemma tail_endpoint_lower {δ γ : ℝ} (w : PinnedCyclicWords δ) (J k : ℕ)
    (hJk : J ≤ k) (hγ : ∀ j, J ≤ j → γ ≤ w.density j) :
    γ * ((stageCut w k - stageCut w J : ℕ) : ℝ) ≤
      (segmentCount (concatenation w) (stageCut w J) (stageCut w k) : ℝ) := by
  induction k, hJk using Nat.le_induction with
  | base => simp [segmentCount]
  | succ k hJk ih =>
      have hcutJk : stageCut w J ≤ stageCut w k :=
        (stageCut_strict w).monotone hJk
      have hcutknext : stageCut w k ≤ stageCut w (k + 1) :=
        (stageCut_strict w).monotone (Nat.le_succ k)
      have hstage := stage_lower w k (stageCut w (k + 1)) hcutknext le_rfl
      have hcoef : 0 ≤ ((stageCut w (k + 1) - stageCut w k : ℕ) : ℝ) :=
        by positivity
      have hγstage :
          γ * ((stageCut w (k + 1) - stageCut w k : ℕ) : ℝ) ≤
            (segmentCount (concatenation w) (stageCut w k)
              (stageCut w (k + 1)) : ℝ) := by
        exact (mul_le_mul_of_nonneg_right (hγ k hJk) hcoef).trans hstage
      have hdecomp : stageCut w (k + 1) - stageCut w J =
          (stageCut w k - stageCut w J) +
            (stageCut w (k + 1) - stageCut w k) := by
        omega
      rw [segmentCount_add_segmentCount (concatenation w) hcutJk hcutknext]
      rw [Nat.cast_add, hdecomp, Nat.cast_add]
      exact mul_add γ _ _ ▸ add_le_add ih hγstage

/-- The preceding completed-tail estimate also holds at every intermediate
cutoff of the concatenation. -/
lemma tail_lower {δ γ : ℝ} (w : PinnedCyclicWords δ) (J n : ℕ)
    (hJn : stageCut w J ≤ n) (hγ : ∀ j, J ≤ j → γ ≤ w.density j) :
    γ * ((n - stageCut w J : ℕ) : ℝ) ≤
      (segmentCount (concatenation w) (stageCut w J) n : ℝ) := by
  rcases hJn.eq_or_lt with rfl | hJnlt
  · simp [segmentCount]
  · let hex : ∃ r : ℕ, n ≤ stageCut w r :=
      ⟨n, (index_le_stageCut w n)⟩
    let r := Nat.find hex
    have hr : n ≤ stageCut w r := Nat.find_spec hex
    have hr0 : r ≠ 0 := by
      intro hrzero
      rw [hrzero, stageCut_zero] at hr
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    rw [hj] at hr
    have hjn : stageCut w j ≤ n := by
      by_contra h
      have hnle : n ≤ stageCut w j := Nat.le_of_not_ge h
      have hmin : Nat.find hex ≤ j := Nat.find_min' hex hnle
      dsimp [r] at hj
      omega
    have hJj : J ≤ j := by
      have hnot : ¬ j + 1 ≤ J := by
        intro hjJ
        have hu := (stageCut_strict w).monotone hjJ
        exact (not_le_of_gt hJnlt) (hr.trans hu)
      omega
    have hcutJj : stageCut w J ≤ stageCut w j :=
      (stageCut_strict w).monotone hJj
    have hend := tail_endpoint_lower w J j hJj hγ
    have hstage := stage_lower w j n hjn hr
    have hcoef : 0 ≤ ((n - stageCut w j : ℕ) : ℝ) := by positivity
    have hγstage : γ * ((n - stageCut w j : ℕ) : ℝ) ≤
        (segmentCount (concatenation w) (stageCut w j) n : ℝ) :=
      (mul_le_mul_of_nonneg_right (hγ j hJj) hcoef).trans hstage
    have hdecomp : n - stageCut w J =
        (stageCut w j - stageCut w J) + (n - stageCut w j) := by
      omega
    rw [segmentCount_add_segmentCount (concatenation w) hcutJj hjn]
    rw [Nat.cast_add, hdecomp, Nat.cast_add]
    exact mul_add γ _ _ ▸ add_le_add hend hγstage

/-- Application-specific upper endpoint data for an unbuffered concatenation.
The finite cyclic witness supplies `density + expansionError`, and `oldError`
is the normalized lacunary fattening of all earlier blocks. -/
structure EndpointBounds (A : Set ℕ) {δ : ℝ} (w : PinnedCyclicWords δ) where
  oldError : ℕ → ℝ
  oldError_tendsto : Tendsto oldError atTop (nhds 0)
  upper : ∀ j,
    (countIn (A + concatenation w) (stageCut w (j + 1)) : ℝ) /
        (stageCut w (j + 1) : ℝ) ≤
      w.density j + w.expansionError j + oldError j

lemma countIn_le_of_subset {C D : Set ℕ} (hCD : C ⊆ D) (n : ℕ) :
    countIn C n ≤ countIn D n := by
  unfold countIn
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hCD hx.2⟩

/-- No-buffer concatenation theorem for lower density.  Convergence of the
local densities gives the lower bound throughout every sufficiently late
stage, while the lacunary/cyclic endpoint estimate supplies arbitrarily late
upper witnesses for both `C` and `A + C`. -/
theorem hasLowerDensity
    (A : Set ℕ) {δ : ℝ} (w : PinnedCyclicWords δ)
    (b : EndpointBounds A w) (hzero : 0 ∈ A) :
    HasLowerDensity (concatenation w) δ ∧
      HasLowerDensity (A + concatenation w) δ := by
  let C := concatenation w
  have hsubset : C ⊆ A + C := by
    intro c hc
    exact ⟨0, hzero, c, hc, zero_add c⟩
  have hClower : ∀ α : ℝ, α < δ →
      ∀ᶠ n : ℕ in atTop, α * (n : ℝ) ≤ (countIn C n : ℝ) := by
    intro α hαδ
    let γ := (α + δ) / 2
    have hαγ : α < γ := by dsimp [γ]; linarith
    have hγδ : γ < δ := by dsimp [γ]; linarith
    obtain ⟨J, hJ⟩ := eventually_atTop.1
      (w.density_tendsto.eventually_const_lt hγδ)
    have hγtail : ∀ j, J ≤ j → γ ≤ w.density j := by
      intro j hj
      exact (hJ j hj).le
    have hlin : Tendsto (fun n : ℕ ↦ (γ - α) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hαγ)
    have hloss : ∀ᶠ n : ℕ in atTop,
        γ * (stageCut w J : ℝ) ≤ (γ - α) * (n : ℝ) :=
      hlin.eventually_ge_atTop (γ * (stageCut w J : ℝ))
    filter_upwards [eventually_ge_atTop (stageCut w J), hloss] with n hn hlossn
    have htail := tail_lower w J n hn hγtail
    have hsplit := countIn_add_segmentCount C hn
    have hsegNat : segmentCount C (stageCut w J) n ≤ countIn C n := by
      omega
    have hseg : (segmentCount C (stageCut w J) n : ℝ) ≤
        (countIn C n : ℝ) := by exact_mod_cast hsegNat
    rw [Nat.cast_sub hn] at htail
    dsimp [C] at htail hseg ⊢
    linarith
  have hsumLower : ∀ α : ℝ, α < δ →
      ∀ᶠ n : ℕ in atTop,
        α * (n : ℝ) ≤ (countIn (A + C) n : ℝ) := by
    intro α hαδ
    filter_upwards [hClower α hαδ] with n hn
    have hmono : countIn C n ≤ countIn (A + C) n :=
      countIn_le_of_subset hsubset n
    exact hn.trans (by exact_mod_cast hmono)
  have hq : Tendsto
      (fun j ↦ w.density j + w.expansionError j + b.oldError j)
      atTop (nhds δ) := by
    convert (w.density_tendsto.add w.expansionError_tendsto).add
      b.oldError_tendsto using 1
    all_goals norm_num
  have hupperSum : ∀ β : ℝ, δ < β → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (countIn (A + C) N : ℝ) ≤ β * (N : ℝ) := by
    intro β hδβ M
    have hqev := hq.eventually_lt_const hδβ
    obtain ⟨j, hjM, hjq⟩ : ∃ j : ℕ, M ≤ j ∧
        w.density j + w.expansionError j + b.oldError j < β := by
      exact (eventually_atTop.2 ⟨M, fun j hj ↦ hj⟩).and hqev |>.exists
    let T := stageCut w (j + 1)
    have hMT : M ≤ T := hjM.trans ((Nat.le_succ j).trans (index_le_stageCut w (j + 1)))
    have hTposNat : 0 < T := by
      dsimp [T]
      rw [stageCut_succ]
      exact Nat.add_pos_right _ (w.length_pos j)
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hTposNat
    have hu := b.upper j
    dsimp [C, T] at hu ⊢
    rw [div_le_iff₀ hTpos] at hu
    refine ⟨stageCut w (j + 1), hMT, hu.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hjq.le hTpos.le
  have hupperC : ∀ β : ℝ, δ < β → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (countIn C N : ℝ) ≤ β * (N : ℝ) := by
    intro β hδβ M
    obtain ⟨N, hMN, hsum⟩ := hupperSum β hδβ M
    refine ⟨N, hMN, ?_⟩
    have hmono : countIn C N ≤ countIn (A + C) N :=
      countIn_le_of_subset hsubset N
    have hmonoR : (countIn C N : ℝ) ≤ (countIn (A + C) N : ℝ) := by
      exact_mod_cast hmono
    exact hmonoR.trans hsum
  exact ⟨⟨hClower, hupperC⟩, ⟨hsumLower, hupperSum⟩⟩

end InfiniteAssembly.NoBuffer

/-! ## Direct special bridge from translated lower-density tails -/

namespace DirectSpecialBridge

open InfiniteAssembly
open InfiniteAssembly.ConcreteFattening

/-- The finite word cut from a translated tail. -/
def tailWord (D : Set ℕ) (t N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (· ∈ translatedTail D t)

lemma tailWord_support (D : Set ℕ) (t N : ℕ) :
    tailWord D t N ⊆ Finset.Ioc 0 N := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Up to a cutoff below its length, a tail word has exactly the same count
as the underlying translated tail. -/
lemma wordPrefixCount_tailWord_eq_countIn (D : Set ℕ) (t N m : ℕ)
    (hm : m ≤ N) :
    wordPrefixCount (tailWord D t N) m =
      countIn (translatedTail D t) m := by
  unfold wordPrefixCount tailWord countIn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hx0, hxN⟩, hxD⟩, hxm⟩
    exact ⟨⟨hx0, hxm⟩, hxD⟩
  · rintro ⟨⟨hx0, hxm⟩, hxD⟩
    exact ⟨⟨⟨hx0, hxm.trans hm⟩, hxD⟩, hxm⟩

/-- The ordinary current window of a tail word injects into the corresponding
prefix of the full translated-tail sumset. -/
lemma currentWindow_tailWord_card_le_countIn
    (A D : Set ℕ) (t N : ℕ) :
    (currentWindow A (tailWord D t N) N).card ≤
      countIn (A + translatedTail D t) N := by
  apply Finset.card_le_card
  intro y hy
  rw [currentWindow, Finset.mem_filter] at hy
  change y ∈ (Finset.Ioc 0 N).filter (· ∈ A + translatedTail D t)
  rw [Finset.mem_filter]
  refine ⟨hy.2, ?_⟩
  rw [Finset.mem_add] at hy
  obtain ⟨w, hw, a, ha, rfl⟩ := hy.1
  rw [Set.mem_add]
  refine ⟨a, ?_, w, ?_, by omega⟩
  · exact (Finset.mem_filter.mp ha).2
  · exact (Finset.mem_filter.mp hw).2

/-- Upper-density witnesses survive translating a tail, after increasing the
cutoff enough to absorb the fixed translation. -/
lemma exists_translatedTail_add_upper_of_hasLowerDensity
    (A D : Set ℕ) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hAD : HasLowerDensity (A + D) δ) (t M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 0 < N ∧
      (countIn (A + translatedTail D t) N : ℝ) ≤
        (δ + η) * (N : ℝ) := by
  let β := δ + η / 2
  have hδβ : δ < β := by dsimp [β]; linarith
  have hβ0 : 0 ≤ β := by dsimp [β]; linarith
  let Q := Nat.ceil ((2 * β * (t : ℝ)) / η)
  have hQabsorb : β * (t : ℝ) ≤ (η / 2) * (Q : ℝ) := by
    have hceil := Nat.le_ceil ((2 * β * (t : ℝ)) / η)
    have hmul := (div_le_iff₀ hη).mp hceil
    dsimp [Q]
    nlinarith
  obtain ⟨X, hXlarge, hXupper⟩ :=
    hAD.exists_upper hδβ (t + max (max M Q) 1)
  let N := X - t
  have htX : t ≤ X := by omega
  have htN : t + N = X := by simp [N, Nat.add_sub_of_le htX]
  have hMN : M ≤ N := by
    dsimp [N]
    omega
  have hQN : Q ≤ N := by
    dsimp [N]
    omega
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hcountNat := countIn_add_translatedTail_le A D t N
  have hcount : (countIn (A + translatedTail D t) N : ℝ) ≤
      (countIn (A + D) X : ℝ) := by
    rw [← htN]
    exact_mod_cast hcountNat
  have hNcast : (Q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hQN
  refine ⟨N, hMN, hNpos, hcount.trans (hXupper.trans ?_)⟩
  rw [← htN, Nat.cast_add]
  dsimp [β]
  have habsorb : β * (t : ℝ) ≤ (η / 2) * (N : ℝ) :=
    hQabsorb.trans (mul_le_mul_of_nonneg_left hNcast (by linarith))
  dsimp [β] at habsorb
  nlinarith

/-- One direct finite stage selected from equality of the two lower
densities. -/
lemma exists_tail_stage
    (A D : Set ℕ) {α δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hαδ : α < δ) (hD : HasLowerDensity D δ)
    (hAD : HasLowerDensity (A + D) δ) (M : ℕ) :
    ∃ t N : ℕ, M ≤ N ∧ 0 < N ∧
      (∀ m : ℕ, 0 < m →
        α * (m : ℝ) ≤ (countIn (translatedTail D t) m : ℝ)) ∧
      ((currentWindow A (tailWord D t N) N).card : ℝ) ≤
        (δ + η) * (N : ℝ) := by
  obtain ⟨t, htail⟩ :=
    exists_translatedTail_prefix_lower_of_hasLowerDensity D hD hαδ
  obtain ⟨N, hMN, hNpos, hupper⟩ :=
    exists_translatedTail_add_upper_of_hasLowerDensity A D hδ.le hη hAD t M
  refine ⟨t, N, hMN, hNpos, htail, ?_⟩
  have hcard := currentWindow_tailWord_card_le_countIn A D t N
  have hcardR : ((currentWindow A (tailWord D t N) N).card : ℝ) ≤
      (countIn (A + translatedTail D t) N : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans hupper

/-- End-to-end deterministic bridge from a sequence of translated-tail
stages.  The stage-selection theorem only has to supply lengths, shifts, and
the displayed current-window and growth estimates. -/
theorem schnirelmann_eq_of_tail_stages
    (A D : Set ℕ) {δ : ℝ} (hzero : 0 ∈ A) (hδ : δ < 1)
    (α expansion : ℕ → ℝ) (t N d : ℕ → ℕ)
    (hαlt : ∀ j, α j < δ)
    (hαlim : Tendsto α atTop (nhds δ))
    (hexplim : Tendsto expansion atTop (nhds 0))
    (hNpos : ∀ j, 0 < N j)
    (htail : ∀ (j m : ℕ), 0 < m →
      α j * (m : ℝ) ≤ (countIn (translatedTail D (t j)) m : ℝ))
    (hcurrent_nonneg : ∀ j, 0 ≤ α j + expansion j)
    (hcurrent : ∀ j,
      ((currentWindow A (tailWord D (t j) (N j)) (N j)).card : ℝ) ≤
        (α j + expansion j) * (N j : ℝ))
    (hA : IsLacunary A)
    (hP : ∀ j, 1 ≤ pivot (densityBufferLength δ α N) N j)
    (hdyadic : ∀ j,
      cut (densityBufferLength δ α N) N (j + 1) ≤
        2 ^ d j * pivot (densityBufferLength δ α N) N j)
    (hscale : ∀ K : ℕ, 1 ≤ K →
      Tendsto (fun j ↦
        (oldBound K d (densityBufferLength δ α N) N j : ℝ) /
          (cut (densityBufferLength δ α N) N (j + 1) : ℝ))
        atTop (nhds 0)) :
    ∃ C : Set ℕ, sd C = δ ∧ sd (A + C) = δ := by
  let W : ℕ → Finset ℕ := fun j ↦ tailWord D (t j) (N j)
  let L : ℕ → ℕ := densityBufferLength δ α N
  let C : Set ℕ := globalSet W L N
  have hsupport : ∀ j, W j ⊆ Finset.Ioc 0 (N j) := by
    intro j
    exact tailWord_support D (t j) (N j)
  have hwordPrefix : ∀ j m, m ≤ N j →
      α j * (m : ℝ) ≤ (wordPrefixCount (W j) m : ℝ) := by
    intro j m hm
    rcases m.eq_zero_or_pos with rfl | hmpos
    · simp [wordPrefixCount]
    · dsimp [W]
      rw [wordPrefixCount_tailWord_eq_countIn D (t j) (N j) m hm]
      exact htail j m hmpos
  have hprefix : PrefixGluingCertificate C δ :=
    prefixGluingCertificate_of_bufferedWords C δ (cut L N) (pivot L N) α
      (by simp)
      (cut_strictMono L N hNpos)
      hδ.le
      (fun j ↦ cut_le_pivot L N j)
      (fun j ↦ pivot_le_cut_succ L N j)
      (fun j ↦ (hαlt j).le)
      (by
        intro j x hx
        exact buffer_mem_globalSet W L N j x hx)
      (by
        intro j n hnleft hnright
        let m := n - pivot L N j
        have hm : m ≤ N j := by
          dsimp [m]
          rw [cut_succ] at hnright
          omega
        have hpref := hwordPrefix j m hm
        have hcount := wordPrefixCount_le_segmentCount W L N hsupport j m
        have hadd : pivot L N j + m = n := by
          dsimp [m]
          omega
        rw [hadd] at hcount
        exact hpref.trans (by exact_mod_cast hcount))
      (by
        intro j
        have hc := densityBufferLength_compensates hδ α N j
        have hmin : min (α j) δ = α j := min_eq_left (hαlt j).le
        simpa [L, cut_succ, pivot, hmin] using hc)
  obtain ⟨K, hK, hshell⟩ := lacunary_shell_and_fattening_bounds hA
  let oldError : ℕ → ℝ := fun j ↦
    (oldBound K d L N j : ℝ) / (cut L N (j + 1) : ℝ)
  have holdlim : Tendsto oldError atTop (nhds 0) := by
    simpa [oldError, L] using hscale K hK
  have herr : Tendsto
      (fun j ↦ |α j - δ| + expansion j + oldError j) atTop (nhds 0) := by
    have hdiff : Tendsto (fun j ↦ |α j - δ|) atTop (nhds 0) := by
      simpa using (hαlim.sub_const δ).abs
    simpa using (hdiff.add hexplim).add holdlim
  have hendpoint : EndpointFatteningCertificate A C δ := {
    endpoint := fun j ↦ cut L N (j + 1)
    endpoint_pos := by
      intro j
      rw [cut_succ]
      exact Nat.add_pos_right _ (hNpos j)
    error := fun j ↦ |α j - δ| + expansion j + oldError j
    error_tendsto_zero := herr
    sumset_upper := by
      intro j
      let P := pivot L N j
      let T := cut L N (j + 1)
      let q := α j + expansion j
      have hTformula : T = P + N j := by simp [T, P]
      have hTpos : (0 : ℝ) < T := by
        have hTnat : 0 < T := by
          rw [hTformula]
          exact Nat.add_pos_right P (hNpos j)
        exact_mod_cast hTnat
      have hNT : N j ≤ T := by rw [hTformula]; omega
      have hold := (hshell (hP j) (hdyadic j)).2
      have hold' :
          (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) ≤
            (oldBound K d L N j : ℝ) := by
        exact_mod_cast hold
      have hdecomp := countIn_endpoint_le_old_add_current A W L N
        hNpos hsupport j
      have hcur : ((currentWindow A (W j) (N j)).card : ℝ) ≤
          q * (N j : ℝ) := by
        simpa [W, q] using hcurrent j
      have hcount : (countIn (A + C) T : ℝ) ≤
          (oldBound K d L N j : ℝ) + q * (N j : ℝ) := by
        have hdecompCast : (countIn (A + C) T : ℝ) ≤
            (((A + Set.Icc 0 P) ∩ Set.Icc 1 T).ncard : ℝ) +
              ((currentWindow A (W j) (N j)).card : ℝ) := by
          simpa [C, T, P] using (show
            (countIn (A + globalSet W L N) (cut L N (j + 1)) : ℝ) ≤
              (((A + Set.Icc 0 (pivot L N j)) ∩
                Set.Icc 1 (cut L N (j + 1))).ncard : ℝ) +
              ((currentWindow A (W j) (N j)).card : ℝ) by
                exact_mod_cast hdecomp)
        exact hdecompCast.trans (add_le_add hold' hcur)
      have hqNT : q * (N j : ℝ) ≤ q * T := by
        apply mul_le_mul_of_nonneg_left _ (hcurrent_nonneg j)
        exact_mod_cast hNT
      have hcancel : ((oldBound K d L N j : ℝ) / T) * T =
          (oldBound K d L N j : ℝ) := by
        field_simp
      have hraw : (countIn (A + C) T : ℝ) / T ≤
          q + (oldBound K d L N j : ℝ) / T := by
        rw [div_le_iff₀ hTpos]
        nlinarith
      change (countIn (A + C) (cut L N (j + 1)) : ℝ) /
          (cut L N (j + 1) : ℝ) ≤
        δ + (|α j - δ| + expansion j + oldError j)
      have habs : α j - δ ≤ |α j - δ| := le_abs_self _
      dsimp [oldError]
      exact hraw.trans (by dsimp [q] at hraw ⊢; linarith) }
  refine ⟨C, ?_⟩
  exact schnirelmann_bridge_of_fattening_certificate hzero hprefix hendpoint

end DirectSpecialBridge

end Erdos37

open scoped ENNReal NNReal Pointwise Real
open Finset Set Filter

namespace Erdos37.DirectSpecialBridge.StageSelection

open Erdos37
open DirectSpecialBridge
open InfiniteAssembly
open InfiniteAssembly.ConcreteFattening

attribute [local instance] Classical.propDecidable

/-- The geometric density deficit used at stage `j`. -/
noncomputable def deficit (δ : ℝ) (j : ℕ) : ℝ :=
  (1 - δ) / (2 ^ (j + 2) : ℝ)

noncomputable def stageAlpha (δ : ℝ) (j : ℕ) : ℝ := δ - deficit δ j

noncomputable def stageExpansion (δ : ℝ) (j : ℕ) : ℝ := 2 * deficit δ j

def growthFactor (j : ℕ) : ℕ := 2 ^ (j + 2)

lemma growthFactor_pos (j : ℕ) : 0 < growthFactor j := by
  simp [growthFactor]

lemma deficit_pos {δ : ℝ} (hδ : δ < 1) (j : ℕ) : 0 < deficit δ j := by
  apply div_pos (sub_pos.mpr hδ)
  positivity

lemma stageAlpha_lt {δ : ℝ} (hδ : δ < 1) (j : ℕ) : stageAlpha δ j < δ := by
  dsimp [stageAlpha]
  linarith [deficit_pos hδ j]

lemma stageAlpha_add_expansion (δ : ℝ) (j : ℕ) :
    stageAlpha δ j + stageExpansion δ j = δ + deficit δ j := by
  simp [stageAlpha, stageExpansion]
  ring

structure RawState where
  prior : ℕ
  shift : ℕ
  length : ℕ

def ValidStage (A D : Set ℕ) (δ : ℝ) (j : ℕ) (s : RawState) : Prop :=
  growthFactor j * (s.prior + 1) ≤ s.length ∧
  0 < s.length ∧
  (∀ m : ℕ, 0 < m →
    stageAlpha δ j * (m : ℝ) ≤
      (countIn (translatedTail D s.shift) m : ℝ)) ∧
  ((currentWindow A (tailWord D s.shift s.length) s.length).card : ℝ) ≤
    (stageAlpha δ j + stageExpansion δ j) * (s.length : ℝ)

lemma exists_validStage
    (A D : Set ℕ) {δ : ℝ} (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (j R : ℕ) : ∃ s : RawState, s.prior = R ∧ ValidStage A D δ j s := by
  obtain ⟨t, N, hMN, hNpos, htail, hcur⟩ :=
    exists_tail_stage A D hδpos (deficit_pos hδ j)
      (stageAlpha_lt hδ j) hD hAD (growthFactor j * (R + 1))
  refine ⟨⟨R, t, N⟩, rfl, hMN, hNpos, htail, ?_⟩
  simpa [stageAlpha_add_expansion] using hcur

noncomputable def selectStage
    (A D : Set ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (j R : ℕ) : RawState :=
  Classical.choose (exists_validStage A D hδpos hδ hD hAD j R)

lemma selectStage_valid
    (A D : Set ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (j R : ℕ) :
    ValidStage A D δ j (selectStage A D δ hδpos hδ hD hAD j R) :=
  (Classical.choose_spec (exists_validStage A D hδpos hδ hD hAD j R)).2

lemma selectStage_prior
    (A D : Set ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (j R : ℕ) :
    (selectStage A D δ hδpos hδ hD hAD j R).prior = R :=
  (Classical.choose_spec (exists_validStage A D hδpos hδ hD hAD j R)).1

noncomputable def bufferFor (δ : ℝ) (j N : ℕ) : ℕ :=
  densityBufferLength δ (stageAlpha δ) (fun _ ↦ N) j

/-- Recursive states.  `prior` is the cut immediately before this stage. -/
noncomputable def states
    (A D : Set ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ) :
    ℕ → RawState
  | 0 => selectStage A D δ hδpos hδ hD hAD 0 0
  | j + 1 =>
      let s := states A D δ hδpos hδ hD hAD j
      let nextPrior := s.prior +
        bufferFor δ j s.length + s.length
      selectStage A D δ hδpos hδ hD hAD (j + 1) nextPrior

variable (A D : Set ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδ : δ < 1)
  (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)

local notation "S" => states A D δ hδpos hδ hD hAD

noncomputable def priorSeq (j : ℕ) : ℕ := (S j).prior
noncomputable def shiftSeq (j : ℕ) : ℕ := (S j).shift
noncomputable def lengthSeq (j : ℕ) : ℕ := (S j).length

lemma states_valid (j : ℕ) :
    ValidStage A D δ j (S j) := by
  cases j with
  | zero =>
      simpa [states] using
        selectStage_valid A D δ hδpos hδ hD hAD 0 0
  | succ j =>
      let R := (S j).prior +
        bufferFor δ j (S j).length +
          (S j).length
      have hv := selectStage_valid A D δ hδpos hδ hD hAD (j + 1) R
      simpa [states, R] using hv

lemma priorSeq_succ (j : ℕ) :
    priorSeq A D δ hδpos hδ hD hAD (j + 1) =
      priorSeq A D δ hδpos hδ hD hAD j +
        densityBufferLength δ (stageAlpha δ)
          (lengthSeq A D δ hδpos hδ hD hAD) j +
        lengthSeq A D δ hδpos hδ hD hAD j := by
  have hp := selectStage_prior A D δ hδpos hδ hD hAD (j + 1)
    ((S j).prior + bufferFor δ j (S j).length + (S j).length)
  simpa [states, priorSeq, lengthSeq, bufferFor, densityBufferLength] using hp

lemma priorSeq_zero : priorSeq A D δ hδpos hδ hD hAD 0 = 0 := by
  have hp := selectStage_prior A D δ hδpos hδ hD hAD 0 0
  simpa [states, priorSeq] using hp

lemma priorSeq_eq_cut (j : ℕ) :
    priorSeq A D δ hδpos hδ hD hAD j =
      cut (densityBufferLength δ (stageAlpha δ)
        (lengthSeq A D δ hδpos hδ hD hAD))
        (lengthSeq A D δ hδpos hδ hD hAD) j := by
  induction j with
  | zero => simp [priorSeq_zero]
  | succ j ih =>
      rw [priorSeq_succ, cut_succ]
      simp only [pivot]
      rw [ih]

lemma lengthSeq_pos (j : ℕ) :
    0 < lengthSeq A D δ hδpos hδ hD hAD j :=
  (states_valid A D δ hδpos hδ hD hAD j).2.1

lemma stage_growth (j : ℕ) :
    growthFactor j * (priorSeq A D δ hδpos hδ hD hAD j + 1) ≤
      lengthSeq A D δ hδpos hδ hD hAD j :=
  (states_valid A D δ hδpos hδ hD hAD j).1

lemma stage_tail_lower (j m : ℕ) (hm : 0 < m) :
    stageAlpha δ j * (m : ℝ) ≤
      (countIn (translatedTail D (shiftSeq A D δ hδpos hδ hD hAD j)) m : ℝ) :=
  (states_valid A D δ hδpos hδ hD hAD j).2.2.1 m hm

lemma stage_current_upper (j : ℕ) :
    ((currentWindow A
      (tailWord D (shiftSeq A D δ hδpos hδ hD hAD j)
        (lengthSeq A D δ hδpos hδ hD hAD j))
      (lengthSeq A D δ hδpos hδ hD hAD j)).card : ℝ) ≤
      (stageAlpha δ j + stageExpansion δ j) *
        (lengthSeq A D δ hδpos hδ hD hAD j : ℝ) :=
  (states_valid A D δ hδpos hδ hD hAD j).2.2.2

/-- The canonical buffer occupies at most one geometric share of its word,
up to the single rounding point. -/
lemma buffer_div_bound (j : ℕ) :
    (densityBufferLength δ (stageAlpha δ)
        (lengthSeq A D δ hδpos hδ hD hAD) j : ℝ) /
        (lengthSeq A D δ hδpos hδ hD hAD j : ℝ) ≤
      1 / (growthFactor j : ℝ) +
        1 / (lengthSeq A D δ hδpos hδ hD hAD j : ℝ) := by
  have hb := densityBufferLength_div_le hδ (stageAlpha δ)
    (lengthSeq A D δ hδpos hδ hD hAD)
    (lengthSeq_pos A D δ hδpos hδ hD hAD) j
  have hmin : min (stageAlpha δ j) δ = stageAlpha δ j :=
    min_eq_left (stageAlpha_lt hδ j).le
  have hden : (1 : ℝ) - δ ≠ 0 := (sub_pos.mpr hδ).ne'
  rw [hmin] at hb
  convert hb using 1 <;>
    simp only [stageAlpha, deficit, growthFactor, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

/-- The selected word is at least `2^(j+1)` times longer than the pivot
preceding it.  This estimate is insensitive to how far the upper-density
witness overshoots the requested cutoff. -/
lemma pivot_mul_pow_le_length (j : ℕ) :
    pivot
        (densityBufferLength δ (stageAlpha δ)
          (lengthSeq A D δ hδpos hδ hD hAD))
        (lengthSeq A D δ hδpos hδ hD hAD) j * 2 ^ (j + 1) ≤
      lengthSeq A D δ hδpos hδ hD hAD j := by
  let N := lengthSeq A D δ hδpos hδ hD hAD j
  let R := priorSeq A D δ hδpos hδ hD hAD j
  let L := densityBufferLength δ (stageAlpha δ)
    (lengthSeq A D δ hδpos hδ hD hAD) j
  let H : ℕ := 2 ^ (j + 1)
  let Q : ℕ := growthFactor j
  have hNposNat : 0 < N := lengthSeq_pos A D δ hδpos hδ hD hAD j
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hQposNat : 0 < Q := growthFactor_pos j
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQposNat
  have hQ : Q = 2 * H := by
    simp [Q, H, growthFactor, pow_succ']
  have hgNat : Q * (R + 1) ≤ N := by
    simpa [Q, R, N] using stage_growth A D δ hδpos hδ hD hAD j
  have hg : (Q : ℝ) * ((R : ℝ) + 1) ≤ (N : ℝ) := by
    exact_mod_cast hgNat
  have hR : (R : ℝ) + 1 ≤ (N : ℝ) / (Q : ℝ) := by
    rw [le_div_iff₀ hQpos]
    simpa [mul_comm] using hg
  have hb := buffer_div_bound A D δ hδpos hδ hD hAD j
  have hL : (L : ℝ) ≤ (N : ℝ) / (Q : ℝ) + 1 := by
    have hb' : (L : ℝ) ≤
        (1 / (Q : ℝ) + 1 / (N : ℝ)) * (N : ℝ) := by
      rw [← div_le_iff₀ hNpos]
      simpa [L, N, Q] using hb
    calc
      (L : ℝ) ≤ (1 / (Q : ℝ) + 1 / (N : ℝ)) * (N : ℝ) := hb'
      _ = (N : ℝ) / (Q : ℝ) + 1 := by field_simp
  have hP' : (R : ℝ) + (L : ℝ) ≤ 2 * ((N : ℝ) / (Q : ℝ)) := by
    linarith
  have hP : (R : ℝ) + (L : ℝ) ≤ 2 * (N : ℝ) / (Q : ℝ) := by
    convert hP' using 1 <;> ring
  have hPH : ((R + L) * H : ℕ) ≤ N := by
    have hH : (H : ℝ) = (Q : ℝ) / 2 := by
      rw [hQ]
      norm_num
    have : ((R + L : ℕ) : ℝ) * (H : ℝ) ≤ (N : ℝ) := by
      rw [Nat.cast_add, hH]
      calc
        ((R : ℝ) + (L : ℝ)) * ((Q : ℝ) / 2) ≤
            (2 * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
        _ = (N : ℝ) := by field_simp
    exact_mod_cast this
  simpa [pivot, ← priorSeq_eq_cut A D δ hδpos hδ hD hAD j,
    R, L, H, N] using hPH

noncomputable def stagePivot (j : ℕ) : ℕ :=
  pivot
    (densityBufferLength δ (stageAlpha δ)
      (lengthSeq A D δ hδpos hδ hD hAD))
    (lengthSeq A D δ hδpos hδ hD hAD) j

noncomputable def stageEnd (j : ℕ) : ℕ :=
  cut
    (densityBufferLength δ (stageAlpha δ)
      (lengthSeq A D δ hδpos hδ hD hAD))
    (lengthSeq A D δ hδpos hδ hD hAD) (j + 1)

noncomputable def quotientSeq (j : ℕ) : ℕ :=
  stageEnd A D δ hδpos hδ hD hAD j /
    stagePivot A D δ hδpos hδ hD hAD j

noncomputable def exponentSeq (j : ℕ) : ℕ :=
  Nat.log 2 (quotientSeq A D δ hδpos hδ hD hAD j + 1) + 1

lemma buffer_pos (j : ℕ) :
    0 < densityBufferLength δ (stageAlpha δ)
      (lengthSeq A D δ hδpos hδ hD hAD) j := by
  have hc := densityBufferLength_compensates hδ (stageAlpha δ)
    (lengthSeq A D δ hδpos hδ hD hAD) j
  have hdef : 0 < δ - min (stageAlpha δ j) δ := by
    rw [min_eq_left (stageAlpha_lt hδ j).le]
    simpa [stageAlpha] using deficit_pos hδ j
  have hN : (0 : ℝ) < lengthSeq A D δ hδpos hδ hD hAD j := by
    exact_mod_cast lengthSeq_pos A D δ hδpos hδ hD hAD j
  have hleft : 0 <
      (δ - min (stageAlpha δ j) δ) *
        (lengthSeq A D δ hδpos hδ hD hAD j : ℝ) :=
    mul_pos hdef hN
  have hcast : (0 : ℝ) < densityBufferLength δ (stageAlpha δ)
      (lengthSeq A D δ hδpos hδ hD hAD) j := by
    have hden := sub_pos.mpr hδ
    nlinarith
  exact_mod_cast hcast

lemma stagePivot_pos (j : ℕ) :
    0 < stagePivot A D δ hδpos hδ hD hAD j := by
  dsimp [stagePivot, pivot]
  exact Nat.add_pos_right _ (buffer_pos A D δ hδpos hδ hD hAD j)

lemma stageEnd_eq (j : ℕ) :
    stageEnd A D δ hδpos hδ hD hAD j =
      stagePivot A D δ hδpos hδ hD hAD j +
        lengthSeq A D δ hδpos hδ hD hAD j := by
  simp [stageEnd, stagePivot]

lemma quotient_ge_pow (j : ℕ) :
    2 ^ (j + 1) + 1 ≤ quotientSeq A D δ hδpos hδ hD hAD j := by
  let P := stagePivot A D δ hδpos hδ hD hAD j
  let T := stageEnd A D δ hδpos hδ hD hAD j
  let N := lengthSeq A D δ hδpos hδ hD hAD j
  let H : ℕ := 2 ^ (j + 1)
  have hP : 0 < P := stagePivot_pos A D δ hδpos hδ hD hAD j
  have hPN : P * H ≤ N := by
    simpa [P, N, H, stagePivot] using
      pivot_mul_pow_le_length A D δ hδpos hδ hD hAD j
  have hmul : (H + 1) * P ≤ T := by
    change (H + 1) * P ≤ P + N
    nlinarith
  change H + 1 ≤ T / P
  rw [Nat.le_div_iff_mul_le hP]
  simpa [mul_comm] using hmul

lemma quotient_tendsto_atTop :
    Tendsto (quotientSeq A D δ hδpos hδ hD hAD) atTop atTop := by
  have hbase : Tendsto (fun j : ℕ ↦ 2 ^ (j + 1) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
        (tendsto_add_atTop_nat 1))
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall (quotient_ge_pow A D δ hδpos hδ hD hAD)) hbase

lemma dyadic_shell (j : ℕ) :
    stageEnd A D δ hδpos hδ hD hAD j ≤
      2 ^ exponentSeq A D δ hδpos hδ hD hAD j *
        stagePivot A D δ hδpos hδ hD hAD j := by
  let P := stagePivot A D δ hδpos hδ hD hAD j
  let T := stageEnd A D δ hδpos hδ hD hAD j
  let q := quotientSeq A D δ hδpos hδ hD hAD j
  let d := exponentSeq A D δ hδpos hδ hD hAD j
  have hP : 0 < P := stagePivot_pos A D δ hδpos hδ hD hAD j
  have hT : T < (q + 1) * P := by
    have hquot : T / P < q + 1 := by simp [q, quotientSeq, T, P]
    exact (Nat.div_lt_iff_lt_mul hP).mp hquot
  have hlog : q + 1 < 2 ^ d := by
    simpa [d, exponentSeq, q] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (q + 1))
  have hmul : (q + 1) * P < 2 ^ d * P :=
    Nat.mul_lt_mul_of_pos_right hlog hP
  exact (hT.trans hmul).le

/-- The natural base-two logarithm is negligible compared with its
argument. -/
lemma natLog_two_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.logb 2 x / x) atTop (nhds 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero
  have hrealNat : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := hreal.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    have hn : (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      Real.natLog_le_logb n 2
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)
  · exact hrealNat

lemma exponent_div_succ_quotient_tendsto_zero :
    Tendsto (fun j ↦
      (exponentSeq A D δ hδpos hδ hD hAD j : ℝ) /
        (quotientSeq A D δ hδpos hδ hD hAD j + 1 : ℕ))
      atTop (nhds 0) := by
  let q := quotientSeq A D δ hδpos hδ hD hAD
  have hq : Tendsto (fun j ↦ q j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (quotient_tendsto_atTop A D δ hδpos hδ hD hAD)
  have hlog := natLog_two_div_tendsto_zero.comp hq
  have hinv : Tendsto (fun j ↦ 1 / ((q j + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    have hcast : Tendsto (fun j ↦ ((q j + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hq
    convert hcast.inv_tendsto_atTop using 1
    ext j
    simp [Function.comp_def, one_div]
  convert hlog.add hinv using 1
  · ext j
    simp only [exponentSeq, q, Nat.cast_add, Nat.cast_one, add_div,
      Function.comp_apply]
  · norm_num

lemma quotient_pos (j : ℕ) :
    0 < quotientSeq A D δ hδpos hδ hD hAD j := by
  have h := quotient_ge_pow A D δ hδpos hδ hD hAD j
  exact (by positivity : 0 < 2 ^ (j + 1) + 1).trans_le h

lemma quotient_mul_pivot_le_end (j : ℕ) :
    quotientSeq A D δ hδpos hδ hD hAD j *
        stagePivot A D δ hδpos hδ hD hAD j ≤
      stageEnd A D δ hδpos hδ hD hAD j := by
  simpa [quotientSeq, mul_comm] using
    Nat.mul_div_le (stageEnd A D δ hδpos hδ hD hAD j)
      (stagePivot A D δ hδpos hδ hD hAD j)

lemma oldBound_ratio_le (K j : ℕ) :
    (oldBound K (exponentSeq A D δ hδpos hδ hD hAD)
        (densityBufferLength δ (stageAlpha δ)
          (lengthSeq A D δ hδpos hδ hD hAD))
        (lengthSeq A D δ hδpos hδ hD hAD) j : ℝ) /
        (stageEnd A D δ hδpos hδ hD hAD j : ℝ) ≤
      5 * (1 / (quotientSeq A D δ hδpos hδ hD hAD j : ℝ)) +
        4 * (K : ℝ) *
          ((exponentSeq A D δ hδpos hδ hD hAD j : ℝ) /
            (quotientSeq A D δ hδpos hδ hD hAD j + 1 : ℕ)) := by
  let P := stagePivot A D δ hδpos hδ hD hAD j
  let T := stageEnd A D δ hδpos hδ hD hAD j
  let q := quotientSeq A D δ hδpos hδ hD hAD j
  let d := exponentSeq A D δ hδpos hδ hD hAD j
  have hPnat : 0 < P := stagePivot_pos A D δ hδpos hδ hD hAD j
  have hTnat : 0 < T := by
    have heq : T = P + lengthSeq A D δ hδpos hδ hD hAD j :=
      stageEnd_eq A D δ hδpos hδ hD hAD j
    omega
  have hqnat : 0 < q := quotient_pos A D δ hδpos hδ hD hAD j
  have hqPnat : q * P ≤ T :=
    quotient_mul_pivot_le_end A D δ hδpos hδ hD hAD j
  have hP : (0 : ℝ) < P := by exact_mod_cast hPnat
  have hT : (0 : ℝ) < T := by exact_mod_cast hTnat
  have hq : (0 : ℝ) < q := by exact_mod_cast hqnat
  have hqP : (q : ℝ) * (P : ℝ) ≤ (T : ℝ) := by exact_mod_cast hqPnat
  have hq_le_qP : q ≤ q * P := by
    calc
      q = q * 1 := by simp
      _ ≤ q * P := Nat.mul_le_mul_left q (Nat.one_le_iff_ne_zero.mpr hPnat.ne')
  have hqTnat : q ≤ T := hq_le_qP.trans hqPnat
  have hqT : (q : ℝ) ≤ (T : ℝ) := by exact_mod_cast hqTnat
  have hPdiv : (P : ℝ) / (T : ℝ) ≤ 1 / (q : ℝ) := by
    rw [div_le_div_iff₀ hT hq]
    simpa [mul_comm] using hqP
  have honeDiv : 1 / (T : ℝ) ≤ 1 / (q : ℝ) := by
    exact one_div_le_one_div_of_le hq hqT
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  have hdPdiv : (d : ℝ) * (P : ℝ) / (T : ℝ) ≤
      (d : ℝ) / (q : ℝ) := by
    calc
      (d : ℝ) * (P : ℝ) / (T : ℝ) =
          (d : ℝ) * ((P : ℝ) / (T : ℝ)) := by ring
      _ ≤ (d : ℝ) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hPdiv hdnonneg
      _ = (d : ℝ) / (q : ℝ) := by ring
  have hqrel : (d : ℝ) / (q : ℝ) ≤
      2 * ((d : ℝ) / ((q : ℝ) + 1)) := by
    have hdleqNat : d ≤ d * q := by
      calc
        d = d * 1 := by simp
        _ ≤ d * q := Nat.mul_le_mul_left d (Nat.one_le_iff_ne_zero.mpr hqnat.ne')
    have hdleq : (d : ℝ) ≤ (d : ℝ) * (q : ℝ) := by exact_mod_cast hdleqNat
    have hcross : (d : ℝ) / (q : ℝ) ≤
        (2 * (d : ℝ)) / ((q : ℝ) + 1) := by
      rw [div_le_div_iff₀ hq (by positivity : (0 : ℝ) < (q : ℝ) + 1)]
      nlinarith
    convert hcross using 1 <;> ring
  have hdPfinal : (d : ℝ) * (P : ℝ) / (T : ℝ) ≤
      2 * ((d : ℝ) / ((q : ℝ) + 1)) := hdPdiv.trans hqrel
  have hnum :
      ((2 * P + 1 + (K * d + 1) * (P + 1) : ℕ) : ℝ) /
          (T : ℝ) ≤
        3 * ((P : ℝ) / (T : ℝ)) + 2 * (1 / (T : ℝ)) +
          2 * (K : ℝ) * ((d : ℝ) * (P : ℝ) / (T : ℝ)) := by
    have hK : (0 : ℝ) ≤ K := by positivity
    have hdle : (d : ℝ) ≤ (d : ℝ) * (P : ℝ) := by
      have hdleNat : d ≤ d * P := by
        calc
          d = d * 1 := by simp
          _ ≤ d * P := Nat.mul_le_mul_left d (Nat.one_le_iff_ne_zero.mpr hPnat.ne')
      exact_mod_cast hdleNat
    have hKdle : (K : ℝ) * (d : ℝ) ≤
        (K : ℝ) * ((d : ℝ) * (P : ℝ)) :=
      mul_le_mul_of_nonneg_left hdle hK
    have hraw : ((2 * P + 1 + (K * d + 1) * (P + 1) : ℕ) : ℝ) ≤
        3 * (P : ℝ) + 2 + 2 * (K : ℝ) * (d : ℝ) * (P : ℝ) := by
      push_cast
      nlinarith
    calc
      ((2 * P + 1 + (K * d + 1) * (P + 1) : ℕ) : ℝ) / (T : ℝ) ≤
          (3 * (P : ℝ) + 2 + 2 * (K : ℝ) * (d : ℝ) * (P : ℝ)) /
            (T : ℝ) := div_le_div_of_nonneg_right hraw hT.le
      _ = 3 * ((P : ℝ) / (T : ℝ)) + 2 * (1 / (T : ℝ)) +
            2 * (K : ℝ) * ((d : ℝ) * (P : ℝ) / (T : ℝ)) := by
        field_simp
  change ((2 * P + 1 + (K * d + 1) * (P + 1) : ℕ) : ℝ) / (T : ℝ) ≤ _
  calc
    ((2 * P + 1 + (K * d + 1) * (P + 1) : ℕ) : ℝ) / (T : ℝ) ≤
        3 * ((P : ℝ) / (T : ℝ)) + 2 * (1 / (T : ℝ)) +
          2 * (K : ℝ) * ((d : ℝ) * (P : ℝ) / (T : ℝ)) := hnum
    _ ≤ 3 * (1 / (q : ℝ)) + 2 * (1 / (q : ℝ)) +
          2 * (K : ℝ) * (2 * ((d : ℝ) / ((q : ℝ) + 1))) := by
      gcongr
    _ = 5 * (1 / (q : ℝ)) + 4 * (K : ℝ) *
          ((d : ℝ) / (q + 1 : ℕ)) := by
      push_cast
      ring

lemma oldBound_ratio_tendsto_zero (K : ℕ) :
    Tendsto (fun j ↦
      (oldBound K (exponentSeq A D δ hδpos hδ hD hAD)
          (densityBufferLength δ (stageAlpha δ)
            (lengthSeq A D δ hδpos hδ hD hAD))
          (lengthSeq A D δ hδpos hδ hD hAD) j : ℝ) /
        (stageEnd A D δ hδpos hδ hD hAD j : ℝ))
      atTop (nhds 0) := by
  let q := quotientSeq A D δ hδpos hδ hD hAD
  let d := exponentSeq A D δ hδpos hδ hD hAD
  have hqcast : Tendsto (fun j ↦ (q j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (quotient_tendsto_atTop A D δ hδpos hδ hD hAD)
  have hqinv : Tendsto (fun j ↦ 1 / (q j : ℝ)) atTop (nhds 0) := by
    convert hqcast.inv_tendsto_atTop using 1
    ext j
    simp [one_div]
  have hd := exponent_div_succ_quotient_tendsto_zero
    A D δ hδpos hδ hD hAD
  have hupper : Tendsto (fun j ↦
      5 * (1 / (q j : ℝ)) +
        4 * (K : ℝ) * ((d j : ℝ) / (q j + 1 : ℕ)))
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hqinv).add
      ((tendsto_const_nhds.mul tendsto_const_nhds).mul hd) using 1 <;>
      norm_num
  apply squeeze_zero
  · intro j
    positivity
  · intro j
    exact oldBound_ratio_le A D δ hδpos hδ hD hAD K j
  · exact hupper

lemma deficit_tendsto_zero :
    Tendsto (deficit δ) atTop (nhds 0) := by
  have hp : Tendsto (fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 2)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 2)
  have hmul : Tendsto (fun j : ℕ ↦
      (1 - δ) * (1 / 2 : ℝ) ^ (j + 2)) atTop (nhds 0) :=
    by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 - δ : ℝ)) atTop
        (nhds (1 - δ))).mul hp using 1 <;> norm_num
  convert hmul using 1
  ext j
  simp [deficit, div_eq_mul_inv, Nat.cast_pow]

lemma stageAlpha_tendsto :
    Tendsto (stageAlpha δ) atTop (nhds δ) := by
  change Tendsto (fun j ↦ δ - deficit δ j) atTop (nhds δ)
  convert tendsto_const_nhds.sub (deficit_tendsto_zero δ) using 1 <;> norm_num

lemma stageExpansion_tendsto :
    Tendsto (stageExpansion δ) atTop (nhds 0) := by
  change Tendsto (fun j ↦ 2 * deficit δ j) atTop (nhds 0)
  convert (deficit_tendsto_zero δ).const_mul 2 using 1 <;> norm_num

lemma stage_current_nonneg {δ : ℝ} (hδpos : 0 < δ) (hδ : δ < 1) (j : ℕ) :
    0 ≤ stageAlpha δ j + stageExpansion δ j := by
  rw [stageAlpha_add_expansion]
  exact add_nonneg hδpos.le (deficit_pos hδ j).le

/-- Equality of lower asymptotic densities can be upgraded to an exact
Schnirelmann-density witness.  The recursive construction requests each new
translated-tail stage beyond a geometric multiple of all preceding stages;
the post-selected logarithmic exponent handles arbitrary overshoot of the
upper-density witness. -/
theorem exists_schnirelmann_eq
    (A D : Set ℕ) {δ : ℝ} (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (hzero : 0 ∈ A) (hA : IsLacunary A) :
    ∃ C : Set ℕ, sd C = δ ∧ sd (A + C) = δ := by
  let t := shiftSeq A D δ hδpos hδ hD hAD
  let N := lengthSeq A D δ hδpos hδ hD hAD
  let d := exponentSeq A D δ hδpos hδ hD hAD
  refine schnirelmann_eq_of_tail_stages A D hzero hδ
    (stageAlpha δ) (stageExpansion δ) t N d
    (stageAlpha_lt hδ) (stageAlpha_tendsto δ)
    (stageExpansion_tendsto δ) ?_ ?_ (stage_current_nonneg hδpos hδ)
    ?_ hA ?_ ?_ ?_
  · intro j
    exact lengthSeq_pos A D δ hδpos hδ hD hAD j
  · intro j m hm
    exact stage_tail_lower A D δ hδpos hδ hD hAD j m hm
  · intro j
    exact stage_current_upper A D δ hδpos hδ hD hAD j
  · intro j
    exact stagePivot_pos A D δ hδpos hδ hD hAD j
  · intro j
    exact dyadic_shell A D δ hδpos hδ hD hAD j
  · intro K _hK
    simpa [stageEnd, N, d] using
      oldBound_ratio_tendsto_zero A D δ hδpos hδ hD hAD K


end Erdos37.DirectSpecialBridge.StageSelection

namespace Erdos37.DirectSpecialBridge

/-- Direct bridge from equality of two lower asymptotic densities to the
Schnirelmann witness needed to refute essentiality. -/
theorem exists_schnirelmann_eq_of_hasLowerDensity
    (A D : Set ℕ) {δ : ℝ} (hzero : 0 ∈ A)
    (hδpos : 0 < δ) (hδ : δ < 1)
    (hD : HasLowerDensity D δ) (hAD : HasLowerDensity (A + D) δ)
    (hA : IsLacunary A) :
    ∃ C : Set ℕ, sd C = δ ∧ sd (A + C) = δ :=
  StageSelection.exists_schnirelmann_eq A D (δ := δ)
    hδpos hδ hD hAD hzero hA

end Erdos37.DirectSpecialBridge

namespace Erdos37

/-- **Erdős Problem 37.** No uniformly lacunary subset of the natural
numbers is an essential component for Schnirelmann density. -/
theorem erdos_37 :
    ∀ A : Set ℕ, IsLacunary A → ¬ IsEssentialComponent A := by
  intro A hL hE
  have hzero : 0 ∈ A := zero_mem_of_essential hE
  obtain ⟨δ, hδ, C, hC, hAC⟩ :=
    InfiniteAssembly.exists_equal_schnirelmannDensity_of_lacunary hL hzero
  have hδpos : 0 < δ := lt_of_lt_of_le (by norm_num) hδ.1
  have hδone : δ < 1 := hδ.2.trans_lt (by norm_num)
  have hstrict : sd C < sd (A + C) := hE C
    (by simpa [hC] using hδpos)
    (by simpa [hC] using hδone)
  rw [hC, hAC] at hstrict
  exact (lt_irrefl δ) hstrict

#print axioms erdos_37

end Erdos37
