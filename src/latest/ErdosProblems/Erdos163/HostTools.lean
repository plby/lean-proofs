/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.DRC
import ErdosProblems.Erdos163.ProductAverage

/-!
# Finite averaging tools for the host-preparation argument

This file collects the normalization and simultaneous-selection facts used
in the dependent-random-choice construction of the monochromatic host.
They are stated for literal finite averages, so every later probabilistic
choice is reduced to a deterministic element of a finite set.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace HostTools

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem expect_const_mul {Ω : Type v} [DecidableEq Ω]
    (S : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    (𝔼 x ∈ S, c * f x) = c * (𝔼 x ∈ S, f x) := by
  simp only [Finset.expect_eq_sum_div_card, ← Finset.mul_sum]
  ring

/-- If the expected sum of finitely many nonnegative normalized costs is
strictly below one, one outcome makes every individual cost smaller than its
normalizing bound. -/
theorem exists_simultaneously_lt
    {Ω : Type u} {κ : Type v} [DecidableEq Ω]
    (S : Finset Ω) (hS : S.Nonempty) (I : Finset κ)
    (F : κ → Ω → ℝ) (a : κ → ℝ)
    (hF : ∀ i ∈ I, ∀ x ∈ S, 0 ≤ F i x)
    (ha : ∀ i ∈ I, 0 < a i)
    (hmean : ∑ i ∈ I, (𝔼 x ∈ S, F i x) / a i < 1) :
    ∃ x ∈ S, ∀ i ∈ I, F i x < a i := by
  classical
  have hswap :
      (𝔼 x ∈ S, ∑ i ∈ I, F i x / a i) =
        ∑ i ∈ I, (𝔼 x ∈ S, F i x) / a i := by
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.expect_div]
  have havg : (𝔼 x ∈ S, ∑ i ∈ I, F i x / a i) < 1 := by
    rw [hswap]
    exact hmean
  obtain ⟨x, hx, hcost⟩ := Finset.exists_lt_of_expect_lt hS havg
  refine ⟨x, hx, ?_⟩
  intro i hi
  have hterm : F i x / a i ≤ ∑ j ∈ I, F j x / a j := by
    exact Finset.single_le_sum
      (fun j hj => div_nonneg (hF j hj x hx) (ha j hj).le) hi
  have hratio : F i x / a i < 1 := hterm.trans_lt hcost
  exact (div_lt_one (ha i hi)).mp hratio

/-- The raw sum underlying `FiniteDefect.moment`. -/
noncomputable def rawFamilyMoment
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (A : ι → Finset α) (T : Finset α) : ℝ :=
  ∑ q ∈ FiniteDefect.familyTuples A,
    FiniteDefect.defectPower G θ q T s

theorem rawFamilyMoment_nonneg
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (A : ι → Finset α) (T : Finset α) :
    0 ≤ rawFamilyMoment G θ s A T := by
  unfold rawFamilyMoment
  exact Finset.sum_nonneg fun q _ =>
    FiniteDefect.defectPower_nonneg G θ q T s

/-- Exact conversion between a raw defect sum and the normalized family
moment.  The formula also covers empty products and empty coordinate sets. -/
theorem rawFamilyMoment_eq_card_mul_moment
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (A : ι → Finset α) (T : Finset α) :
    rawFamilyMoment G θ s A T =
      ((FiniteDefect.familyTuples A).card : ℝ) *
        FiniteDefect.familyMoment G θ s A T := by
  classical
  unfold rawFamilyMoment FiniteDefect.familyMoment
  rw [Finset.expect_eq_sum_div_card]
  by_cases hcard : (FiniteDefect.familyTuples A).card = 0
  · have hempty : FiniteDefect.familyTuples A = ∅ := Finset.card_eq_zero.mp hcard
    simp [hempty]
  · have hcast : ((FiniteDefect.familyTuples A).card : ℝ) ≠ 0 := by
      exact_mod_cast hcard
    field_simp

/-- Restricting coordinate sets can only decrease the unnormalized defect
sum. -/
theorem rawFamilyMoment_mono_coordinates
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) {A B : ι → Finset α}
    (hAB : ∀ i, A i ⊆ B i) (T : Finset α) :
    rawFamilyMoment G θ s A T ≤ rawFamilyMoment G θ s B T := by
  classical
  unfold rawFamilyMoment
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rw [FiniteDefect.mem_familyTuples] at hq ⊢
    exact fun i => hAB i (hq i)
  · intro q hq hnot
    exact FiniteDefect.defectPower_nonneg G θ q T s

/-- A normalized coordinate-restriction estimate.  It is deliberately
written with the literal product cardinalities; later applications discharge
the denominator bounds separately. -/
theorem familyMoment_le_of_coordinate_subset
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) {A B : ι → Finset α}
    (hAB : ∀ i, A i ⊆ B i)
    (hA : (FiniteDefect.familyTuples A).Nonempty)
    (T : Finset α) :
    FiniteDefect.familyMoment G θ s A T ≤
      ((FiniteDefect.familyTuples B).card : ℝ) /
          (FiniteDefect.familyTuples A).card *
        FiniteDefect.familyMoment G θ s B T := by
  classical
  have hAcard : (0 : ℝ) < (FiniteDefect.familyTuples A).card := by
    exact_mod_cast hA.card_pos
  have hraw := rawFamilyMoment_mono_coordinates G θ s hAB T
  rw [rawFamilyMoment_eq_card_mul_moment,
    rawFamilyMoment_eq_card_mul_moment] at hraw
  rw [show
    ((FiniteDefect.familyTuples B).card : ℝ) /
          (FiniteDefect.familyTuples A).card *
        FiniteDefect.familyMoment G θ s B T =
      (((FiniteDefect.familyTuples B).card : ℝ) *
        FiniteDefect.familyMoment G θ s B T) /
          (FiniteDefect.familyTuples A).card by ring]
  apply (le_div_iff₀ hAcard).2
  calc
    FiniteDefect.familyMoment G θ s A T *
          (FiniteDefect.familyTuples A).card =
        ((FiniteDefect.familyTuples A).card : ℝ) *
          FiniteDefect.familyMoment G θ s A T := by ring
    _ ≤ ((FiniteDefect.familyTuples B).card : ℝ) *
          FiniteDefect.familyMoment G θ s B T := hraw
    _ = ((FiniteDefect.familyTuples B).card : ℝ) *
          FiniteDefect.familyMoment G θ s B T := rfl

/-- Uniform specialization of coordinate restriction.  If the ambient
coordinate set is at most `K` times as large as the restricted set, the
normalization loss in `D` coordinates is at most `K^D`. -/
theorem moment_le_pow_mul_of_subset
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D K : ℕ) {U B : Finset α} (hU : U.Nonempty)
    (hUB : U ⊆ B) (hcard : B.card ≤ K * U.card) (T : Finset α) :
    FiniteDefect.moment G θ s (fun _ : Fin D => U) T ≤
      (K : ℝ) ^ D *
        FiniteDefect.moment G θ s (fun _ : Fin D => B) T := by
  classical
  have htuples : (FiniteDefect.familyTuples
      (fun _ : Fin D => U)).Nonempty := by
    obtain ⟨u, hu⟩ := hU
    refine ⟨fun _ => u, ?_⟩
    simpa using fun _ => hu
  have hbase := familyMoment_le_of_coordinate_subset G θ s
    (A := fun _ : Fin D => U) (B := fun _ : Fin D => B)
    (fun _ => hUB) htuples T
  rw [FiniteDefect.familyMoment_fin, FiniteDefect.familyMoment_fin] at hbase
  simp only [FiniteDefect.card_familyTuples, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat] at hbase
  have hUpow : (0 : ℝ) < (U.card : ℝ) ^ D := by
    exact pow_pos (by exact_mod_cast hU.card_pos) D
  have hpowNat : B.card ^ D ≤ (K * U.card) ^ D :=
    Nat.pow_le_pow_left hcard D
  have hpowCast : (B.card : ℝ) ^ D ≤
      ((K * U.card : ℕ) : ℝ) ^ D := by
    exact_mod_cast hpowNat
  have hpow : (B.card : ℝ) ^ D ≤
      (K : ℝ) ^ D * (U.card : ℝ) ^ D := by
    simpa [Nat.cast_mul, mul_pow] using hpowCast
  have hratio : (B.card : ℝ) ^ D / (U.card : ℝ) ^ D ≤ (K : ℝ) ^ D := by
    exact (div_le_iff₀ hUpow).2 (by simpa [mul_comm] using hpow)
  exact hbase.trans (mul_le_mul_of_nonneg_right hratio
    (FiniteDefect.moment_nonneg G θ s (fun _ : Fin D => B) T))

/-- Coordinatewise version of `moment_le_pow_mul_of_subset` for a product
indexed by an arbitrary finite type. -/
theorem familyMoment_le_pow_mul_of_subset
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s K : ℕ) {A B : ι → Finset α}
    (hA : ∀ i, (A i).Nonempty) (hAB : ∀ i, A i ⊆ B i)
    (hcard : ∀ i, (B i).card ≤ K * (A i).card) (T : Finset α) :
    FiniteDefect.familyMoment G θ s A T ≤
      (K : ℝ) ^ Fintype.card ι *
        FiniteDefect.familyMoment G θ s B T := by
  classical
  have htuples : (FiniteDefect.familyTuples A).Nonempty := by
    refine ⟨fun i => (hA i).choose, ?_⟩
    rw [FiniteDefect.mem_familyTuples]
    intro i
    exact (hA i).choose_spec
  have hbase := familyMoment_le_of_coordinate_subset G θ s hAB htuples T
  have hprodNat : (∏ i, (B i).card) ≤
      ∏ i, (K * (A i).card) := Finset.prod_le_prod' fun i _ => hcard i
  have hprodRight : (∏ i, (K * (A i).card)) =
      K ^ Fintype.card ι * ∏ i, (A i).card := by
    simp [Finset.prod_mul_distrib]
  rw [hprodRight] at hprodNat
  have hAprod : (0 : ℝ) < (∏ i, (A i).card : ℕ) := by
    exact_mod_cast Finset.prod_pos fun i _ => (hA i).card_pos
  have hprodCast : ((∏ i, (B i).card : ℕ) : ℝ) ≤
      ((K ^ Fintype.card ι * ∏ i, (A i).card : ℕ) : ℝ) := by
    exact_mod_cast hprodNat
  have hprod : ((∏ i, (B i).card : ℕ) : ℝ) ≤
      (K : ℝ) ^ Fintype.card ι * ((∏ i, (A i).card : ℕ) : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hprodCast
  have hratio : ((∏ i, (B i).card : ℕ) : ℝ) /
      ((∏ i, (A i).card : ℕ) : ℝ) ≤ (K : ℝ) ^ Fintype.card ι := by
    exact (div_le_iff₀ hAprod).2 (by simpa [mul_comm] using hprod)
  rw [FiniteDefect.card_familyTuples, FiniteDefect.card_familyTuples] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right hratio
    (FiniteDefect.familyMoment_nonneg G θ s B T))

/-- Increasing the target set can only decrease each finite defect and hence
the whole family moment. -/
theorem familyMoment_mono_target
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ s : ℕ) (A : ι → Finset α) {T U : Finset α} (hTU : T ⊆ U) :
    FiniteDefect.familyMoment G θ s A U ≤
      FiniteDefect.familyMoment G θ s A T := by
  classical
  unfold FiniteDefect.familyMoment Finset.expect
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro q hq
  exact FiniteDefect.defectPower_mono_coordinates_target G q q id rfl hTU

/-! ## Adding an independently sampled block of coordinates -/

def appendTupleSets {D t : ℕ} (B A : Finset α) :
    Fin (D + t) → Finset α :=
  Fin.append (fun _ : Fin D => B) (fun _ : Fin t => A)

def appendEquiv (D t : ℕ) :
    (Fin D → α) × (Fin t → α) ≃ (Fin (D + t) → α) where
  toFun p := Fin.append p.1 p.2
  invFun z := (λ i => z (Fin.castAdd t i), λ j => z (Fin.natAdd D j))
  left_inv p := by
    ext i
    · simp
    · simp
  right_inv z := by
    funext i
    refine Fin.addCases (λ j => ?_) (λ j => ?_) i <;> simp

theorem commonNeighbors_commonNeighbors_eq_append
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {D t : ℕ} (q : Fin D → α) (x : Fin t → α) (T : Finset α) :
    FiniteDefect.commonNeighbors G q
        (FiniteDefect.commonNeighbors G x T) =
      FiniteDefect.commonNeighbors G (Fin.append q x) T := by
  classical
  ext z
  simp only [FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
  constructor
  · rintro ⟨⟨hzT, hx⟩, hq⟩
    refine ⟨hzT, ?_⟩
    intro i
    refine Fin.addCases (λ j => ?_) (λ j => ?_) i
    · simpa using hq j
    · simpa using hx j
  · rintro ⟨hzT, hall⟩
    refine ⟨⟨hzT, ?_⟩, ?_⟩
    · intro j
      simpa using hall (Fin.natAdd D j)
    · intro j
      simpa using hall (Fin.castAdd t j)

/-- Proposition 5.2 in the finite notation used here: averaging a defect
moment after intersecting the target with the common neighborhood of an
independent sample is exactly the moment obtained by appending that sample
to the defect tuple. -/
theorem expect_moment_commonNeighbors
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B T : Finset α) (D t θ s : ℕ) :
    (𝔼 x ∈ FiniteDefect.samples t A,
        FiniteDefect.moment G θ s (fun _ : Fin D => B)
          (FiniteDefect.commonNeighbors G x T)) =
      FiniteDefect.moment G θ s (appendTupleSets (D := D) (t := t) B A) T := by
  classical
  unfold FiniteDefect.moment FiniteDefect.samples FiniteDefect.tuples
  rw [Finset.expect_comm]
  let e : (Fin D → α) × (Fin t → α) ≃ (Fin (D + t) → α) :=
    appendEquiv D t
  calc
    (𝔼 q ∈ Fintype.piFinset (fun _ : Fin D => B),
        𝔼 x ∈ Fintype.piFinset (fun _ : Fin t => A),
          FiniteDefect.defectPower G θ q
            (FiniteDefect.commonNeighbors G x T) s) =
        𝔼 p ∈ (Fintype.piFinset (fun _ : Fin D => B)) ×ˢ
            (Fintype.piFinset (fun _ : Fin t => A)),
          FiniteDefect.defectPower G θ p.1
            (FiniteDefect.commonNeighbors G p.2 T) s := by
              rw [Finset.expect_product]
    _ = 𝔼 z ∈ Fintype.piFinset (appendTupleSets (D := D) (t := t) B A),
          FiniteDefect.defectPower G θ z T s := by
      apply Finset.expect_equiv e
      · intro p
        simp only [Finset.mem_product, Fintype.mem_piFinset]
        constructor
        · rintro ⟨hp, hx⟩ i
          refine Fin.addCases (λ j => ?_) (λ j => ?_) i
          · rw [show e p = Fin.append p.1 p.2 from rfl,
              Fin.append_left]
            simpa [appendTupleSets] using hp j
          · rw [show e p = Fin.append p.1 p.2 from rfl,
              Fin.append_right]
            simpa [appendTupleSets] using hx j
        · intro hall
          constructor
          · intro j
            have h := hall (Fin.castAdd t j)
            rw [show e p = Fin.append p.1 p.2 from rfl,
              Fin.append_left] at h
            simpa [appendTupleSets] using h
          · intro j
            have h := hall (Fin.natAdd D j)
            rw [show e p = Fin.append p.1 p.2 from rfl,
              Fin.append_right] at h
            simpa [appendTupleSets] using h
      · intro p hp
        have hcn := commonNeighbors_commonNeighbors_eq_append G p.1 p.2 T
        unfold FiniteDefect.defectPower FiniteDefect.defect
        simp only
        rw [hcn]
        rfl

theorem defectPower_zero_eq_indicator_lt
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → α) (T : Finset α) (θ : ℕ) :
    FiniteDefect.defectPower G θ q T 0 =
      DRC.indicator ((FiniteDefect.commonNeighbors G q T).card < θ) := by
  classical
  by_cases hsmall : (FiniteDefect.commonNeighbors G q T).card < θ
  · rw [DRC.indicator_true hsmall]
    have hdef : FiniteDefect.defect G θ q T ≠ 0 := by
      intro hzero
      have hnonneg := FiniteDefect.defect_nonneg G θ q T
      unfold FiniteDefect.defect at hzero
      simp only [Nat.not_le_of_lt hsmall, if_false] at hzero
      by_cases hcard : (FiniteDefect.commonNeighbors G q T).card = 0
      · simp [hcard, Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hsmall)] at hzero
        have : (0 : ℝ) < Fintype.card α + 1 := by positivity
        linarith
      · have hθ : 0 < θ := (Nat.pos_of_ne_zero hcard).trans hsmall
        have : (0 : ℝ) < (θ : ℝ) /
            (FiniteDefect.commonNeighbors G q T).card := by positivity
        simp [hcard] at hzero
        linarith
    simp [FiniteDefect.defectPower, hdef]
  · have hlarge : θ ≤ (FiniteDefect.commonNeighbors G q T).card :=
      Nat.le_of_not_gt hsmall
    rw [DRC.indicator_false hsmall,
      FiniteDefect.defectPower,
      if_pos (FiniteDefect.defect_eq_zero_of_threshold_le G hlarge)]

theorem moment_zero_eq_expect_indicator
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (A T : Finset α) (D θ : ℕ) :
    FiniteDefect.moment G θ 0 (fun _ : Fin D => A) T =
      𝔼 q ∈ FiniteDefect.samples D A,
        DRC.indicator ((FiniteDefect.commonNeighbors G q T).card < θ) := by
  classical
  unfold FiniteDefect.moment FiniteDefect.samples FiniteDefect.tuples
  apply Finset.expect_congr rfl
  intro q hq
  exact defectPower_zero_eq_indicator_lt G q T θ

/-- Adding independent coordinates can only increase a defect moment on
average. -/
theorem moment_mono_dimension
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A : Finset α} (hA : A.Nonempty) (T : Finset α)
    (θ s : ℕ) {d e : ℕ} (hde : d ≤ e) :
    FiniteDefect.moment G θ s (fun _ : Fin d => A) T ≤
      FiniteDefect.moment G θ s (fun _ : Fin e => A) T := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  have hsamples : (FiniteDefect.samples k A).Nonempty := DRC.samples_nonempty k hA
  have hpoint : ∀ x ∈ FiniteDefect.samples k A,
      FiniteDefect.moment G θ s (fun _ : Fin d => A) T ≤
        FiniteDefect.moment G θ s (fun _ : Fin d => A)
          (FiniteDefect.commonNeighbors G x T) := by
    intro x hx
    rw [← FiniteDefect.familyMoment_fin, ← FiniteDefect.familyMoment_fin]
    exact familyMoment_mono_target G θ s (fun _ : Fin d => A)
      (Defect.commonNeighbors_subset_target G x T)
  have havg : FiniteDefect.moment G θ s (fun _ : Fin d => A) T ≤
      𝔼 x ∈ FiniteDefect.samples k A,
        FiniteDefect.moment G θ s (fun _ : Fin d => A)
          (FiniteDefect.commonNeighbors G x T) :=
    Finset.le_expect hsamples hpoint
  rw [expect_moment_commonNeighbors G A A T d k θ s] at havg
  have hsets : appendTupleSets (D := d) (t := k) A A =
      (fun _ : Fin (d + k) => A) := by
    funext i
    refine Fin.addCases (λ j => ?_) (λ j => ?_) i <;>
      simp [appendTupleSets]
  rw [hsets] at havg
  exact havg

/-- Simultaneously restricting the sampling set and dropping coordinates
costs at most the corresponding cardinality-ratio power. -/
theorem moment_subsample_dimension_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {A B : Finset α} (hA : A.Nonempty) (hAB : A ⊆ B)
    (θ s K : ℕ) {d e : ℕ} (hde : d ≤ e)
    (hcard : B.card ≤ K * A.card) (T : Finset α) :
    FiniteDefect.moment G θ s (fun _ : Fin d => A) T ≤
      (K : ℝ) ^ d *
        FiniteDefect.moment G θ s (fun _ : Fin e => B) T := by
  exact (moment_le_pow_mul_of_subset G θ s d K hA hAB hcard T).trans
    (mul_le_mul_of_nonneg_left
      (moment_mono_dimension G (hA.mono hAB) T θ s hde)
      (pow_nonneg (by positivity) d))

/-- Convert a strict raw-sum estimate into a normalized moment estimate once
the selected coordinate set meets its cardinal reserve. -/
theorem moment_lt_of_raw_lt_reserve
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D reserve : ℕ) {U T : Finset α} {a : ℝ}
    (hreserve : 0 < reserve) (hcard : reserve ≤ U.card) (ha : 0 ≤ a)
    (hraw : DRC.rawMoment G θ s D U T < (reserve : ℝ) ^ D * a) :
    FiniteDefect.moment G θ s (fun _ : Fin D => U) T < a := by
  rw [DRC.rawMoment_eq_card_pow_mul_moment] at hraw
  have hUpow : (0 : ℝ) < (U.card : ℝ) ^ D := by
    exact pow_pos (by exact_mod_cast hreserve.trans_le hcard) D
  have hpow : (reserve : ℝ) ^ D ≤ (U.card : ℝ) ^ D := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) D
  have hscaled : (reserve : ℝ) ^ D * a ≤ (U.card : ℝ) ^ D * a :=
    mul_le_mul_of_nonneg_right hpow ha
  exact (lt_of_mul_lt_mul_left (hraw.trans_le hscaled) hUpow.le)

theorem rawMoment_mono_coordinates
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (θ s D : ℕ) {U B : Finset α} (hUB : U ⊆ B) (T : Finset α) :
    DRC.rawMoment G θ s D U T ≤ DRC.rawMoment G θ s D B T := by
  classical
  unfold DRC.rawMoment
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rw [FiniteDefect.mem_tuples] at hq ⊢
    exact fun i => hUB (hq i)
  · intro q hq hnot
    exact FiniteDefect.defectPower_nonneg G θ q T s

end HostTools
end Erdos163
