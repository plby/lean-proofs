/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.FiniteDefect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Erdős Problem 163: finite dependent random choice

The probability space is represented by a literal finite average over tuples
sampled with replacement.  This keeps every use of the probabilistic method
as an equality or inequality between finite sums.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace DRC

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

noncomputable def indicator (P : Prop) : ℝ :=
  @ite ℝ P (Classical.propDecidable P) 1 0

@[simp] theorem indicator_true {P : Prop} (h : P) : indicator P = 1 := by
  simp [indicator, h]

@[simp] theorem indicator_false {P : Prop} (h : ¬P) : indicator P = 0 := by
  simp [indicator, h]

theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

theorem sum_indicator_eq_card_filter (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ∑ x ∈ s, indicator (p x) = ((s.filter p).card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [sum_insert ha, ih, filter_insert]
      by_cases hp : p a
      · rw [indicator_true hp]
        simp [ha, hp]
        <;> ring
      · rw [indicator_false hp]
        simp [ha, hp]

theorem card_commonNeighbors_eq_sum_indicator
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (B : Finset α) :
    ((FiniteDefect.commonNeighbors G q B).card : ℝ) =
      ∑ y ∈ B, indicator (∀ i, G.Adj (q i) y) := by
  classical
  rw [sum_indicator_eq_card_filter]
  rfl

theorem expect_all_adjacent
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A : Finset α) (t : ℕ) (y : α) :
    𝔼 x ∈ FiniteDefect.samples t A,
        indicator (∀ i, G.Adj (x i) y) =
      (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  have hsingle :
      𝔼 z ∈ A, indicator (G.Adj z y) =
        ((A.filter fun z => G.Adj z y).card : ℝ) / A.card := by
    rw [Finset.expect_eq_sum_div_card]
    rw [sum_indicator_eq_card_filter]
  calc
    𝔼 x ∈ FiniteDefect.samples t A,
        indicator (∀ i, G.Adj (x i) y) =
        𝔼 x ∈ FiniteDefect.samples t A,
          ∏ i, indicator (G.Adj (x i) y) := by
            apply Finset.expect_congr rfl
            intro x hx
            by_cases h : ∀ i, G.Adj (x i) y
            · rw [indicator_true h]
              exact (Finset.prod_eq_one fun i _ => indicator_true (h i)).symm
            · rw [indicator_false h]
              push Not at h
              obtain ⟨i, hi⟩ := h
              exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_false hi)).symm
    _ = (𝔼 z ∈ A, indicator (G.Adj z y)) ^ t := by
      symm
      simpa [FiniteDefect.samples] using
        (Finset.expect_pow A (fun z => indicator (G.Adj z y)) t)
    _ = (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
      rw [hsingle]

theorem expect_all_predicate (A : Finset α) (t : ℕ) (p : α → Prop)
    [DecidablePred p] :
    𝔼 x ∈ FiniteDefect.samples t A, indicator (∀ i, p (x i)) =
      (((A.filter p).card : ℝ) / A.card) ^ t := by
  classical
  have hsingle :
      𝔼 z ∈ A, indicator (p z) = ((A.filter p).card : ℝ) / A.card := by
    rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter]
  calc
    𝔼 x ∈ FiniteDefect.samples t A, indicator (∀ i, p (x i)) =
        𝔼 x ∈ FiniteDefect.samples t A, ∏ i, indicator (p (x i)) := by
          apply Finset.expect_congr rfl
          intro x hx
          by_cases h : ∀ i, p (x i)
          · rw [indicator_true h]
            exact (Finset.prod_eq_one fun i _ => indicator_true (h i)).symm
          · rw [indicator_false h]
            push Not at h
            obtain ⟨i, hi⟩ := h
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_false hi)).symm
    _ = (𝔼 z ∈ A, indicator (p z)) ^ t := by
      symm
      simpa [FiniteDefect.samples] using
        (Finset.expect_pow A (fun z => indicator (p z)) t)
    _ = (((A.filter p).card : ℝ) / A.card) ^ t := by rw [hsingle]

/-- Mean size of the common neighborhood of a sample tuple. -/
theorem expect_card_commonNeighbors
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B : Finset α) (t : ℕ) :
    𝔼 x ∈ FiniteDefect.samples t A,
        ((FiniteDefect.commonNeighbors G x B).card : ℝ) =
      ∑ y ∈ B, (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  simp_rw [card_commonNeighbors_eq_sum_indicator]
  rw [Finset.expect_sum_comm]
  congr 1
  funext y
  exact expect_all_adjacent G A t y

/-- Sum of degrees from `B` into `A`, counted with orientation from `B`. -/
def edgeMass (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B : Finset α) : ℕ :=
  ∑ y ∈ B, (A.filter fun z => G.Adj z y).card

theorem sum_degree_ratios
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B : Finset α) :
    ∑ y ∈ B, ((A.filter fun z => G.Adj z y).card : ℝ) / A.card =
      edgeMass G A B / A.card := by
  classical
  simp only [edgeMass, Nat.cast_sum]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]

/-- Jensen's inequality for a finite uniform average of nonnegative reals. -/
theorem pow_expect_le_expect_pow {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (f : ι → ℝ) (hf : ∀ x ∈ S, 0 ≤ f x) (t : ℕ) :
    (𝔼 x ∈ S, f x) ^ t ≤ 𝔼 x ∈ S, (f x) ^ t := by
  classical
  let w : ι → ℝ := fun _ => (S.card : ℝ)⁻¹
  have hw : ∀ x ∈ S, 0 ≤ w x := fun _ _ => by positivity
  have hw_sum : ∑ x ∈ S, w x = 1 := by
    simp [w, hS.card_ne_zero]
  have hJ := Real.pow_arith_mean_le_arith_mean_pow S w f hw hw_sum hf t
  simpa [Finset.expect, NNRat.smul_def, w, div_eq_inv_mul, ← Finset.mul_sum] using hJ

theorem samples_nonempty (t : ℕ) {A : Finset α} (hA : A.Nonempty) :
    (FiniteDefect.samples t A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨fun _ => a, ?_⟩
  simp [FiniteDefect.samples, ha]

/-- First Jensen estimate in dependent random choice. -/
theorem expect_card_commonNeighbors_lower
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (t : ℕ) :
    (ρ ^ t) * B.card ≤
      𝔼 x ∈ FiniteDefect.samples t A,
        ((FiniteDefect.commonNeighbors G x B).card : ℝ) := by
  classical
  let f : α → ℝ := fun y =>
    ((A.filter fun z => G.Adj z y).card : ℝ) / A.card
  have hf : ∀ y ∈ B, 0 ≤ f y := fun _ _ => by positivity
  have hmean : ρ ≤ 𝔼 y ∈ B, f y := by
    rw [Finset.expect_eq_sum_div_card, show (∑ y ∈ B, f y) =
      edgeMass G A B / A.card by exact sum_degree_ratios G A B]
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hApos hBpos)).2
    simpa [mul_assoc] using hdensity
  have hjensen := pow_expect_le_expect_pow B hB f hf t
  have hpow : ρ ^ t ≤ 𝔼 y ∈ B, (f y) ^ t := by
    exact (pow_le_pow_left₀ hρ hmean t).trans hjensen
  rw [expect_card_commonNeighbors G A B t]
  rw [Finset.expect_eq_sum_div_card] at hpow
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  apply (le_div_iff₀ (by exact_mod_cast hB.card_pos)).mp at hpow
  simpa [f, mul_comm] using hpow

/-- The `D`-th moment form used by defect DRC. -/
theorem expect_card_commonNeighbors_pow_lower
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (t D : ℕ) :
    (ρ ^ (D * t)) * (B.card : ℝ) ^ D ≤
      𝔼 x ∈ FiniteDefect.samples t A,
        ((FiniteDefect.commonNeighbors G x B).card : ℝ) ^ D := by
  classical
  let Ω := FiniteDefect.samples t A
  let f : (Fin t → α) → ℝ := fun x =>
    (FiniteDefect.commonNeighbors G x B).card
  have hΩ : Ω.Nonempty := samples_nonempty t hA
  have hf : ∀ x ∈ Ω, 0 ≤ f x := fun _ _ => by positivity
  have hjensen := pow_expect_le_expect_pow Ω hΩ f hf D
  have hfirst := expect_card_commonNeighbors_lower G hA hB hρ hdensity t
  have hpow : ((ρ ^ t) * B.card) ^ D ≤ (𝔼 x ∈ Ω, f x) ^ D :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hρ _) (by positivity)) hfirst D
  calc
    (ρ ^ (D * t)) * (B.card : ℝ) ^ D = ((ρ ^ t) * B.card) ^ D := by
      rw [mul_pow, ← pow_mul]
      simp [Nat.mul_comm]
    _ ≤ (𝔼 x ∈ Ω, f x) ^ D := hpow
    _ ≤ 𝔼 x ∈ Ω, (f x) ^ D := hjensen

/-- Unnormalized defect sum over `D`-tuples from one set. -/
noncomputable def rawMoment (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D : ℕ) (U T : Finset α) : ℝ :=
  ∑ q ∈ FiniteDefect.tuples (fun _ : Fin D => U),
    FiniteDefect.defectPower G θ q T s

theorem rawMoment_as_ambient (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D : ℕ) {U B T : Finset α} (hUB : U ⊆ B) :
    rawMoment G θ s D U T =
      ∑ q ∈ FiniteDefect.tuples (fun _ : Fin D => B),
        indicator (∀ i, q i ∈ U) * FiniteDefect.defectPower G θ q T s := by
  classical
  have htuples :
      FiniteDefect.tuples (fun _ : Fin D => U) =
        (FiniteDefect.tuples (fun _ : Fin D => B)).filter fun q => ∀ i, q i ∈ U := by
    ext q
    simp only [FiniteDefect.mem_tuples, mem_filter]
    constructor
    · intro h
      exact ⟨fun i => hUB (h i), h⟩
    · exact fun h => h.2
  rw [rawMoment, htuples, sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : ∀ i, q i ∈ U
  · simp [h, indicator_true]
  · simp [h, indicator_false]

/-- Exact expectation of the unnormalized defect sum after a DRC sample. -/
theorem expect_rawMoment
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B : Finset α) (θ s D t : ℕ) :
    𝔼 x ∈ FiniteDefect.samples t A,
        rawMoment G θ s D (FiniteDefect.commonNeighbors G x B) A =
      ∑ q ∈ FiniteDefect.tuples (fun _ : Fin D => B),
        FiniteDefect.defectPower G θ q A s *
          (((FiniteDefect.commonNeighbors G q A).card : ℝ) / A.card) ^ t := by
  classical
  have hsub : ∀ x : Fin t → α, FiniteDefect.commonNeighbors G x B ⊆ B := by
    intro x y hy
    exact (Defect.commonNeighbors_subset_target G x B) hy
  simp_rw [rawMoment_as_ambient G θ s D (hsub _)]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.expect_mul]
  rw [mul_comm (FiniteDefect.defectPower G θ q A s)]
  congr 1
  calc
    𝔼 x ∈ FiniteDefect.samples t A,
        indicator (∀ i, q i ∈ FiniteDefect.commonNeighbors G x B) =
        𝔼 x ∈ FiniteDefect.samples t A,
          indicator (∀ j, x j ∈ FiniteDefect.commonNeighbors G q A) := by
            apply Finset.expect_congr rfl
            intro x hx
            apply congrArg indicator
            have hxA : ∀ j, x j ∈ A := (FiniteDefect.mem_samples t A x).mp hx
            have hqB : ∀ i, q i ∈ B :=
              (FiniteDefect.mem_tuples (fun _ : Fin D => B) q).mp hq
            simp only [FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
            apply propext
            constructor
            · intro h j
              exact ⟨hxA j, fun i => (h i).2 j |>.symm⟩
            · intro h i
              exact ⟨hqB i, fun j => (h j).2 i |>.symm⟩
    _ = (((FiniteDefect.commonNeighbors G q A).card : ℝ) / A.card) ^ t := by
      have hfilter :
          A.filter (fun z => z ∈ FiniteDefect.commonNeighbors G q A) =
            FiniteDefect.commonNeighbors G q A := by
        ext z
        simp [FiniteDefect.commonNeighbors, Defect.commonNeighbors]
      have hpred := expect_all_predicate A t
        (fun z => z ∈ FiniteDefect.commonNeighbors G q A)
      rw [hfilter] at hpred
      exact hpred

/-- Pointwise estimate behind the defect part of dependent random choice. -/
theorem defectPower_mul_ratio_pow_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A : Finset α} (hA : A.Nonempty) {θ s D t : ℕ}
    (ht : 0 < t) (hst : s ≤ t) {η ρ : ℝ} (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hθ : (θ : ℝ) ≤ η * ρ ^ D * A.card)
    (q : Fin D → α) :
    FiniteDefect.defectPower G θ q A s *
        (((FiniteDefect.commonNeighbors G q A).card : ℝ) / A.card) ^ t ≤
      η ^ t * ρ ^ (D * t) := by
  classical
  let k : ℕ := (FiniteDefect.commonNeighbors G q A).card
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  by_cases hlarge : θ ≤ k
  · have hzero : FiniteDefect.defect G θ q A = 0 :=
      FiniteDefect.defect_eq_zero_of_threshold_le G hlarge
    simp only [FiniteDefect.defectPower, hzero, if_pos, zero_mul]
    exact mul_nonneg (pow_nonneg hη _) (pow_nonneg hρ _)
  · have hklt : k < θ := Nat.lt_of_not_ge hlarge
    by_cases hkzero : k = 0
    · have ht0 : t ≠ 0 := Nat.ne_of_gt ht
      have hkcard : (FiniteDefect.commonNeighbors G q A).card = 0 := hkzero
      simp only [hkcard, Nat.cast_zero, zero_div, zero_pow ht0, mul_zero]
      exact mul_nonneg (pow_nonneg hη _) (pow_nonneg hρ _)
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
      have hθpos : 0 < θ := hkpos.trans hklt
      have hdef : FiniteDefect.defect G θ q A = (θ : ℝ) / k := by
        exact FiniteDefect.defect_eq_div_of_pos_card_lt G hkpos hklt
      have hdef0 : FiniteDefect.defect G θ q A ≠ 0 := by
        rw [hdef]
        positivity
      rw [FiniteDefect.defectPower, if_neg hdef0, hdef]
      let r : ℝ := (k : ℝ) / A.card
      let w : ℝ := (θ : ℝ) / k
      let a : ℝ := η * ρ ^ D
      have hr : 0 ≤ r := by dsimp [r]; positivity
      have hw : 1 ≤ w := by
        dsimp [w]
        exact (one_le_div₀ (by positivity)).2 (by exact_mod_cast hklt.le)
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hrw : r * w = (θ : ℝ) / A.card := by
        dsimp [r, w]
        field_simp
      have hθdiv : (θ : ℝ) / A.card ≤ a := by
        apply (div_le_iff₀ hApos).2
        simpa [a, mul_assoc] using hθ
      have hrw_le : r * w ≤ a := hrw.trans_le hθdiv
      have hr_le : r ≤ a := (le_mul_of_one_le_right hr hw).trans hrw_le
      have hmain : w ^ s * r ^ t ≤ a ^ t := by
        have ht_split : t = s + (t - s) := (Nat.add_sub_of_le hst).symm
        rw [ht_split, pow_add]
        calc
          w ^ s * (r ^ s * r ^ (t - s)) = (r * w) ^ s * r ^ (t - s) := by
            rw [mul_pow]
            ring
          _ ≤ a ^ s * a ^ (t - s) := by
            apply mul_le_mul
            · exact pow_le_pow_left₀ (mul_nonneg hr (zero_le_one.trans hw)) hrw_le s
            · exact pow_le_pow_left₀ hr hr_le (t - s)
            · exact pow_nonneg hr _
            · exact pow_nonneg ha _
          _ = a ^ (s + (t - s)) := (pow_add a s (t - s)).symm
      have hrewrite :
          ((θ : ℝ) / k) ^ s * ((k : ℝ) / A.card) ^ t = w ^ s * r ^ t := rfl
      rw [hrewrite]
      calc
        w ^ s * r ^ t ≤ a ^ t := hmain
        _ = η ^ t * ρ ^ (D * t) := by
          dsimp [a]
          rw [mul_pow, pow_mul]

theorem expect_rawMoment_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) {θ s D t : ℕ}
    (ht : 0 < t) (hst : s ≤ t) {η ρ : ℝ} (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hθ : (θ : ℝ) ≤ η * ρ ^ D * A.card) :
    𝔼 x ∈ FiniteDefect.samples t A,
        rawMoment G θ s D (FiniteDefect.commonNeighbors G x B) A ≤
      (B.card : ℝ) ^ D * η ^ t * ρ ^ (D * t) := by
  classical
  rw [expect_rawMoment G A B θ s D t]
  calc
    (∑ q ∈ FiniteDefect.tuples (fun _ : Fin D => B),
        FiniteDefect.defectPower G θ q A s *
          (((FiniteDefect.commonNeighbors G q A).card : ℝ) / A.card) ^ t) ≤
        ∑ _q ∈ FiniteDefect.tuples (fun _ : Fin D => B),
          η ^ t * ρ ^ (D * t) := by
            apply Finset.sum_le_sum
            intro q hq
            exact defectPower_mul_ratio_pow_le G hA ht hst hη hρ hθ q
    _ = (B.card : ℝ) ^ D * η ^ t * ρ ^ (D * t) := by
      rw [sum_const, nsmul_eq_mul]
      simp [FiniteDefect.card_tuples, mul_assoc]

/-- Raw defect sum and normalized moment differ by the number of tuples. -/
theorem rawMoment_eq_card_pow_mul_moment
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D : ℕ) (U T : Finset α) :
    rawMoment G θ s D U T = (U.card : ℝ) ^ D *
      FiniteDefect.moment G θ s (fun _ : Fin D => U) T := by
  classical
  unfold rawMoment FiniteDefect.moment
  rw [Finset.expect_eq_sum_div_card]
  have hcard : (FiniteDefect.tuples (fun _ : Fin D => U)).card = U.card ^ D := by
    simp [FiniteDefect.card_tuples]
  rw [hcard]
  by_cases hU : U.card ^ D = 0
  · have htuples : FiniteDefect.tuples (fun _ : Fin D => U) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [FiniteDefect.card_tuples] using hU
    simp [htuples, hU]
  · have hcast : ((U.card ^ D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hU
    field_simp [hcast]
    rw [Nat.cast_pow]

/-- The objective-function selection step in defect DRC. -/
theorem exists_drc_power_and_moment
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty)
    {θ s D t : ℕ} (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (hθ : (θ : ℝ) ≤ η * ρ ^ D * A.card) :
    ∃ x ∈ FiniteDefect.samples t A,
      let U := FiniteDefect.commonNeighbors G x B
      ((ρ ^ t) * B.card) ^ D / 2 ≤ (U.card : ℝ) ^ D ∧
      FiniteDefect.moment G θ s (fun _ : Fin D => U) A ≤ 2 * η ^ t := by
  classical
  let Ω := FiniteDefect.samples t A
  let X : (Fin t → α) → ℝ := fun x =>
    ((FiniteDefect.commonNeighbors G x B).card : ℝ) ^ D
  let Z : (Fin t → α) → ℝ := fun x =>
    rawMoment G θ s D (FiniteDefect.commonNeighbors G x B) A
  let L : ℝ := ((ρ ^ t) * B.card) ^ D
  let c : ℝ := 2 * η ^ t
  have hΩ : Ω.Nonempty := samples_nonempty t hA
  have hc : 0 < c := by dsimp [c]; positivity
  have hX : L ≤ 𝔼 x ∈ Ω, X x := by
    dsimp [L, X, Ω]
    have h := expect_card_commonNeighbors_pow_lower G hA hB hρ.le hdensity t D
    calc
      ((ρ ^ t) * B.card) ^ D = ρ ^ (D * t) * (B.card : ℝ) ^ D := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm t D]
      _ ≤ 𝔼 x ∈ FiniteDefect.samples t A,
          ((FiniteDefect.commonNeighbors G x B).card : ℝ) ^ D := h
  have hZ : 𝔼 x ∈ Ω, Z x ≤ (η ^ t) * L := by
    dsimp [Z, Ω]
    have h := expect_rawMoment_le G hA ht hst hη.le hρ.le hθ (B := B)
    dsimp [L]
    calc
      𝔼 x ∈ FiniteDefect.samples t A,
          rawMoment G θ s D (FiniteDefect.commonNeighbors G x B) A ≤
          (B.card : ℝ) ^ D * η ^ t * ρ ^ (D * t) := h
      _ = η ^ t * ((ρ ^ t) * B.card) ^ D := by
        rw [mul_pow, pow_mul]
        ring
  have hobj : L / 2 ≤ 𝔼 x ∈ Ω, (X x - Z x / c) := by
    rw [Finset.expect_sub_distrib, ← Finset.expect_div]
    have hzdiv : (𝔼 x ∈ Ω, Z x) / c ≤ L / 2 := by
      calc
        (𝔼 x ∈ Ω, Z x) / c ≤ (η ^ t * L) / c :=
          div_le_div_of_nonneg_right hZ hc.le
        _ = L / 2 := by
          dsimp [c]
          have hηpow : η ^ t ≠ 0 := pow_ne_zero _ (ne_of_gt hη)
          field_simp
    linarith
  obtain ⟨x, hxΩ, hxobj⟩ := Finset.exists_le_of_le_expect hΩ hobj
  refine ⟨x, hxΩ, ?_⟩
  dsimp [X, Z, L, c] at hxobj ⊢
  let U := FiniteDefect.commonNeighbors G x B
  have hZnonneg : 0 ≤ rawMoment G θ s D U A := by
    unfold rawMoment
    exact Finset.sum_nonneg fun q _ => FiniteDefect.defectPower_nonneg G θ q A s
  have hpower : ((ρ ^ t) * B.card) ^ D / 2 ≤ (U.card : ℝ) ^ D := by
    have : 0 ≤ rawMoment G θ s D U A / (2 * η ^ t) := div_nonneg hZnonneg hc.le
    linarith
  refine ⟨hpower, ?_⟩
  have hbase : 0 < ((ρ ^ t) * B.card : ℝ) := by
    exact mul_pos (pow_pos hρ _) (by exact_mod_cast hB.card_pos)
  have hLhalf : 0 < ((ρ ^ t) * B.card : ℝ) ^ D / 2 := by
    exact div_pos (pow_pos hbase _) (by norm_num)
  have hUposPow : 0 < (U.card : ℝ) ^ D :=
    lt_of_lt_of_le hLhalf hpower
  have hUcard : (U.card : ℝ) ^ D ≠ 0 := ne_of_gt hUposPow
  have hraw : rawMoment G θ s D U A ≤ (2 * η ^ t) * (U.card : ℝ) ^ D := by
    have hdiv : rawMoment G θ s D U A / (2 * η ^ t) ≤ (U.card : ℝ) ^ D := by
      have hLnonneg : 0 ≤ ((ρ ^ t) * B.card : ℝ) ^ D / 2 := by positivity
      linarith
    have := (div_le_iff₀ hc).mp hdiv
    dsimp [c] at this
    simpa [mul_comm] using this
  rw [rawMoment_eq_card_pow_mul_moment G θ s D U A] at hraw
  apply (le_of_mul_le_mul_left ?_ hUposPow)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

/-- DRC with a caller-supplied integral lower bound for the selected set. -/
theorem exists_drc
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty)
    {θ s D t τ : ℕ} (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (hθ : (θ : ℝ) ≤ η * ρ ^ D * A.card)
    (hτ : (τ : ℝ) ^ D ≤ ((ρ ^ t) * B.card) ^ D / 2) :
    ∃ x ∈ FiniteDefect.samples t A,
      let U := FiniteDefect.commonNeighbors G x B
      τ ≤ U.card ∧
      FiniteDefect.moment G θ s (fun _ : Fin D => U) A ≤ 2 * η ^ t := by
  obtain ⟨x, hx, hpow, hmom⟩ :=
    exists_drc_power_and_moment G hA hB hD ht hst hη hρ hdensity hθ
  refine ⟨x, hx, ?_, hmom⟩
  apply_mod_cast (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ τ)
    (by positivity : (0 : ℝ) ≤ (FiniteDefect.commonNeighbors G x B).card)
    (Nat.ne_of_gt hD)).mp (hτ.trans hpow)

end DRC
end Erdos163
