/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.PrimeReciprocal

/-!
# Bilinear reciprocal sums for Erdős 378

This file isolates the two finite Cauchy--Schwarz expansions used for the
balanced terms in Vaughan's identity.  No asymptotic statement occurs here:
all sums are over explicit finsets, and the matrix correlation on the right
is the exact place where the reciprocal derivative estimates enter.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace BilinearReciprocal

noncomputable section

open PrimeReciprocal

/-- Finite complex Cauchy--Schwarz in squared norm form. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm :
      ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
        simp_rw [Complex.norm_mul]
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
        (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))).mpr hnorm
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖a i‖) (fun i ↦ ‖b i‖)

private theorem complex_norm_sq_cast (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

/-- The squared `ℓ²` mass of a finite matrix transform is bounded by the
coefficient-weighted norms of its column correlations. -/
theorem sum_norm_sq_matrix_le_correlation
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (b : κ → ℂ) (w : ι → κ → ℂ) :
    (∑ m ∈ s, ‖∑ k ∈ t, b k * w m k‖ ^ 2) ≤
      ∑ k₁ ∈ t, ∑ k₂ ∈ t,
        ‖b k₁‖ * ‖b k₂‖ *
          ‖∑ m ∈ s, w m k₂ * conj (w m k₁)‖ := by
  let F : ι → ℂ := fun m ↦ ∑ k ∈ t, b k * w m k
  let R : ℂ := ∑ k₁ ∈ t, ∑ k₂ ∈ t,
    (b k₂ * conj (b k₁)) *
      ∑ m ∈ s, w m k₂ * conj (w m k₁)
  have hcast :
      (((∑ m ∈ s, ‖F m‖ ^ 2 : ℝ) : ℂ)) =
        ∑ m ∈ s, conj (F m) * F m := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact complex_norm_sq_cast (F m)
  have hexpand : (∑ m ∈ s, conj (F m) * F m) = R := by
    dsimp only [F, R]
    calc
      (∑ m ∈ s, conj (∑ k ∈ t, b k * w m k) *
          ∑ k ∈ t, b k * w m k) =
        ∑ m ∈ s, ∑ k₁ ∈ t, ∑ k₂ ∈ t,
          (conj (b k₁) * conj (w m k₁)) * (b k₂ * w m k₂) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [map_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k₁ hk₁
            rw [Finset.mul_sum, map_mul]
      _ = ∑ k₁ ∈ t, ∑ m ∈ s, ∑ k₂ ∈ t,
          (conj (b k₁) * conj (w m k₁)) * (b k₂ * w m k₂) := by
            rw [Finset.sum_comm]
      _ = ∑ k₁ ∈ t, ∑ k₂ ∈ t, ∑ m ∈ s,
          (conj (b k₁) * conj (w m k₁)) * (b k₂ * w m k₂) := by
            apply Finset.sum_congr rfl
            intro k₁ hk₁
            rw [Finset.sum_comm]
      _ = ∑ k₁ ∈ t, ∑ k₂ ∈ t,
          (b k₂ * conj (b k₁)) *
            ∑ m ∈ s, w m k₂ * conj (w m k₁) := by
            apply Finset.sum_congr rfl
            intro k₁ hk₁
            apply Finset.sum_congr rfl
            intro k₂ hk₂
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
  have hreal :
      (∑ m ∈ s, ‖F m‖ ^ 2) = R.re := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
      congrArg Complex.re (hcast.trans hexpand)
  calc
    (∑ m ∈ s, ‖∑ k ∈ t, b k * w m k‖ ^ 2) =
        ∑ m ∈ s, ‖F m‖ ^ 2 := by rfl
    _ = R.re := hreal
    _ ≤ ‖R‖ := Complex.re_le_norm R
    _ ≤ ∑ k₁ ∈ t, ∑ k₂ ∈ t,
        ‖(b k₂ * conj (b k₁)) *
          ∑ m ∈ s, w m k₂ * conj (w m k₁)‖ := by
      dsimp only [R]
      exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun k₁ hk₁ ↦
        norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k₁ hk₁
      apply Finset.sum_congr rfl
      intro k₂ hk₂
      simp only [Complex.norm_mul, Complex.norm_conj]
      ring

/-- Cauchy--Schwarz in the outer variable followed by the exact matrix
correlation expansion in the inner variable. -/
theorem norm_bilinear_sum_sq_le_correlation
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (w : ι → κ → ℂ) :
    ‖∑ m ∈ s, a m * ∑ k ∈ t, b k * w m k‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ k₁ ∈ t, ∑ k₂ ∈ t,
          ‖b k₁‖ * ‖b k₂‖ *
            ‖∑ m ∈ s, w m k₂ * conj (w m k₁)‖ := by
  have houter := norm_sum_mul_sq_le s a
    (fun m ↦ ∑ k ∈ t, b k * w m k)
  have hmatrix := sum_norm_sq_matrix_le_correlation s t b w
  exact houter.trans <| mul_le_mul_of_nonneg_left hmatrix
    (Finset.sum_nonneg fun m hm ↦ sq_nonneg _)

/-! ## Product cutoffs and their correlation intervals -/

/-- Reciprocal phase restricted to one half-open product interval. -/
def reciprocalCutoffWeight (X : ℝ) (x y m k : ℕ) : ℂ :=
  if x < m * k ∧ m * k ≤ y then reciprocalWeight X (m * k) else 0

/-- The common interval in the first factor on which two product cutoffs are
simultaneously active. -/
def commonProductInterval
    (x y m₀ m₁ k₁ k₂ : ℕ) : Finset ℕ :=
  Finset.Ioc (max m₀ (max (x / k₁) (x / k₂)))
    (min m₁ (min (y / k₁) (y / k₂)))

theorem mem_commonProductInterval_iff
    {x y m₀ m₁ k₁ k₂ m : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    m ∈ commonProductInterval x y m₀ m₁ k₁ k₂ ↔
      m ∈ Finset.Ioc m₀ m₁ ∧
        (x < m * k₁ ∧ m * k₁ ≤ y) ∧
        (x < m * k₂ ∧ m * k₂ ≤ y) := by
  rw [commonProductInterval, Finset.mem_Ioc]
  constructor
  · intro hm
    have hm₀ : m₀ < m := lt_of_le_of_lt (Nat.le_max_left _ _) hm.1
    have hxk₁div : x / k₁ < m :=
      lt_of_le_of_lt (le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right m₀ _)) hm.1
    have hxk₂div : x / k₂ < m :=
      lt_of_le_of_lt (le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right m₀ _)) hm.1
    have hmm₁ : m ≤ m₁ := hm.2.trans (Nat.min_le_left _ _)
    have hmy₁div : m ≤ y / k₁ := hm.2.trans <|
      (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    have hmy₂div : m ≤ y / k₂ := hm.2.trans <|
      (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
    exact ⟨Finset.mem_Ioc.mpr ⟨hm₀, hmm₁⟩,
      ⟨(Nat.div_lt_iff_lt_mul hk₁).mp hxk₁div,
        (Nat.le_div_iff_mul_le hk₁).mp hmy₁div⟩,
      ⟨(Nat.div_lt_iff_lt_mul hk₂).mp hxk₂div,
        (Nat.le_div_iff_mul_le hk₂).mp hmy₂div⟩⟩
  · rintro ⟨hmIoc, hx₁, hx₂⟩
    have hmIoc' := Finset.mem_Ioc.mp hmIoc
    have hxk₁div : x / k₁ < m := (Nat.div_lt_iff_lt_mul hk₁).mpr hx₁.1
    have hxk₂div : x / k₂ < m := (Nat.div_lt_iff_lt_mul hk₂).mpr hx₂.1
    have hmy₁div : m ≤ y / k₁ := (Nat.le_div_iff_mul_le hk₁).mpr hx₁.2
    have hmy₂div : m ≤ y / k₂ := (Nat.le_div_iff_mul_le hk₂).mpr hx₂.2
    exact ⟨max_lt hmIoc'.1 (max_lt hxk₁div hxk₂div),
      le_min hmIoc'.2 (le_min hmy₁div hmy₂div)⟩

/-- A cutoff correlation is supported exactly on the common product
interval. -/
theorem sum_reciprocalCutoffWeight_correlation_eq_common
    (X : ℝ) {x y m₀ m₁ k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)) =
      ∑ m ∈ commonProductInterval x y m₀ m₁ k₁ k₂,
        reciprocalWeight X (m * k₁) * conj (reciprocalWeight X (m * k₂)) := by
  let P : ℕ → Prop := fun m ↦
    (x < m * k₁ ∧ m * k₁ ≤ y) ∧ (x < m * k₂ ∧ m * k₂ ≤ y)
  let f : ℕ → ℂ := fun m ↦
    reciprocalWeight X (m * k₁) * conj (reciprocalWeight X (m * k₂))
  have hterm : ∀ m,
      reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂) =
        if P m then f m else 0 := by
    intro m
    by_cases h₁ : x < m * k₁ ∧ m * k₁ ≤ y
    · by_cases h₂ : x < m * k₂ ∧ m * k₂ ≤ y
      · simp [reciprocalCutoffWeight, P, f, h₁, h₂]
      · simp [reciprocalCutoffWeight, P, f, h₁, h₂]
    · simp [reciprocalCutoffWeight, P, f, h₁]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter]
    rw [mem_commonProductInterval_iff hk₁ hk₂]
  · intro m hm
    rfl

/-- In the increasing orientation, the cutoff correlation is the positive
reciprocal-frequency interval sum estimated in `PrimeReciprocal`. -/
theorem sum_reciprocalCutoffWeight_correlation_eq_phase
    (X : ℝ) {x y m₀ m₁ k₁ k₂ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₁k₂ : k₁ ≤ k₂) :
    (∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)) =
      reciprocalProductIntervalSum
        (X * ((k₂ - k₁ : ℕ) : ℝ) / ((k₁ * k₂ : ℕ) : ℝ)) 1
        (max m₀ (max (x / k₁) (x / k₂)))
        (min m₁ (min (y / k₁) (y / k₂))) := by
  rw [sum_reciprocalCutoffWeight_correlation_eq_common X hk₁ hk₂]
  unfold commonProductInterval
  exact sum_reciprocalWeight_product_correlation X hk₁ hk₁k₂

/-- Reversing the two columns conjugates a cutoff correlation, so its norm
is unchanged. -/
theorem norm_sum_reciprocalCutoffWeight_correlation_comm
    (X : ℝ) (x y m₀ m₁ k₁ k₂ : ℕ) :
    ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)‖ =
      ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₂ *
          conj (reciprocalCutoffWeight X x y m k₁)‖ := by
  have hconj :
      conj (∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)) =
        ∑ m ∈ Finset.Ioc m₀ m₁,
          reciprocalCutoffWeight X x y m k₂ *
            conj (reciprocalCutoffWeight X x y m k₁) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_mul, starRingEnd_self_apply]
    ring
  calc
    ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)‖ =
      ‖conj (∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂))‖ :=
      (Complex.norm_conj _).symm
    _ = _ := congrArg norm hconj

@[simp] theorem norm_reciprocalCutoffWeight_le
    (X : ℝ) (x y m k : ℕ) :
    ‖reciprocalCutoffWeight X x y m k‖ ≤ 1 := by
  unfold reciprocalCutoffWeight
  split_ifs
  · simp
  · simp

/-- Diagonal correlations have only their interval length as a cost. -/
theorem norm_sum_reciprocalCutoffWeight_diagonal_le
    (X : ℝ) (x y m₀ m₁ k : ℕ) :
    ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k *
          conj (reciprocalCutoffWeight X x y m k)‖ ≤
      (m₁ - m₀ : ℕ) := by
  calc
    _ ≤ ∑ m ∈ Finset.Ioc m₀ m₁,
        ‖reciprocalCutoffWeight X x y m k *
          conj (reciprocalCutoffWeight X x y m k)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ioc m₀ m₁, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [Complex.norm_mul, Complex.norm_conj]
      nlinarith [norm_reciprocalCutoffWeight_le X x y m k,
        norm_nonneg (reciprocalCutoffWeight X x y m k)]
    _ = (m₁ - m₀ : ℕ) := by simp

/-- Every cutoff correlation is trivially bounded by the length of its
common support interval. -/
theorem norm_sum_reciprocalCutoffWeight_correlation_le_commonLength
    (X : ℝ) {x y m₀ m₁ k₁ k₂ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m k₁ *
          conj (reciprocalCutoffWeight X x y m k₂)‖ ≤
      ((min m₁ (min (y / k₁) (y / k₂)) -
        max m₀ (max (x / k₁) (x / k₂)) : ℕ) : ℝ) := by
  rw [sum_reciprocalCutoffWeight_correlation_eq_common X hk₁ hk₂]
  unfold commonProductInterval
  calc
    _ ≤ ∑ m ∈ Finset.Ioc
        (max m₀ (max (x / k₁) (x / k₂)))
        (min m₁ (min (y / k₁) (y / k₂))),
          ‖reciprocalWeight X (m * k₁) *
            conj (reciprocalWeight X (m * k₂))‖ := norm_sum_le _ _
    _ = ∑ _m ∈ Finset.Ioc
        (max m₀ (max (x / k₁) (x / k₂)))
        (min m₁ (min (y / k₁) (y / k₂))), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m _hm
      simp
    _ = _ := by simp

/-! ## Bilinear blocks -/

def reciprocalBilinearBlock
    (X : ℝ) (x y m₀ m₁ k₀ k₁ : ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc m₀ m₁, a m *
    ∑ k ∈ Finset.Ioc k₀ k₁, b k * reciprocalCutoffWeight X x y m k

theorem reciprocalCutoffWeight_comm
    (X : ℝ) (x y m k : ℕ) :
    reciprocalCutoffWeight X x y m k =
      reciprocalCutoffWeight X x y k m := by
  unfold reciprocalCutoffWeight
  rw [Nat.mul_comm]

/-- The product cutoff and reciprocal phase are symmetric in the two
factors.  This permits every dyadic block to use its longer factor as the
outer Cauchy--van der Corput variable. -/
theorem reciprocalBilinearBlock_comm
    (X : ℝ) (x y m₀ m₁ k₀ k₁ : ℕ) (a b : ℕ → ℂ) :
    reciprocalBilinearBlock X x y m₀ m₁ k₀ k₁ a b =
      reciprocalBilinearBlock X x y k₀ k₁ m₀ m₁ b a := by
  unfold reciprocalBilinearBlock
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro m _hm
  rw [reciprocalCutoffWeight_comm]
  ring

/-- Exact Cauchy--correlation bound for a product-cutoff reciprocal block. -/
theorem norm_reciprocalBilinearBlock_sq_le_correlation
    (X : ℝ) (x y m₀ m₁ k₀ k₁ : ℕ) (a b : ℕ → ℂ) :
    ‖reciprocalBilinearBlock X x y m₀ m₁ k₀ k₁ a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc m₀ m₁, ‖a m‖ ^ 2) *
        ∑ r ∈ Finset.Ioc k₀ k₁, ∑ s ∈ Finset.Ioc k₀ k₁,
          ‖b r‖ * ‖b s‖ *
            ‖∑ m ∈ Finset.Ioc m₀ m₁,
              reciprocalCutoffWeight X x y m s *
                conj (reciprocalCutoffWeight X x y m r)‖ := by
  unfold reciprocalBilinearBlock
  exact norm_bilinear_sum_sq_le_correlation
    (Finset.Ioc m₀ m₁) (Finset.Ioc k₀ k₁) a b
      (reciprocalCutoffWeight X x y)

/-- Insert arbitrary pointwise correlation majorants into the exact block
bound. -/
theorem norm_reciprocalBilinearBlock_sq_le_of_correlation
    (X : ℝ) (x y m₀ m₁ k₀ k₁ : ℕ) (a b : ℕ → ℂ)
    (H : ℕ → ℕ → ℝ)
    (hH : ∀ r ∈ Finset.Ioc k₀ k₁, ∀ s ∈ Finset.Ioc k₀ k₁,
      ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤ H r s) :
    ‖reciprocalBilinearBlock X x y m₀ m₁ k₀ k₁ a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc m₀ m₁, ‖a m‖ ^ 2) *
        ∑ r ∈ Finset.Ioc k₀ k₁, ∑ s ∈ Finset.Ioc k₀ k₁,
          ‖b r‖ * ‖b s‖ * H r s := by
  apply (norm_reciprocalBilinearBlock_sq_le_correlation
    X x y m₀ m₁ k₀ k₁ a b).trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_left (hH r hr s hs) (by positivity)
  · exact Finset.sum_nonneg fun m hm ↦ sq_nonneg _

/-- Uniform form of the bilinear block estimate. -/
theorem norm_reciprocalBilinearBlock_sq_le_of_uniform_correlation
    (X : ℝ) (x y m₀ m₁ k₀ k₁ : ℕ) (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ r ∈ Finset.Ioc k₀ k₁, ∀ s ∈ Finset.Ioc k₀ k₁,
      ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤ B) :
    ‖reciprocalBilinearBlock X x y m₀ m₁ k₀ k₁ a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc m₀ m₁, ‖a m‖ ^ 2) *
        (∑ k ∈ Finset.Ioc k₀ k₁, ‖b k‖) ^ 2 * B := by
  have hbase := norm_reciprocalBilinearBlock_sq_le_of_correlation
    X x y m₀ m₁ k₀ k₁ a b (fun _ _ ↦ B) hH
  have hpairs :
      (∑ r ∈ Finset.Ioc k₀ k₁, ∑ s ∈ Finset.Ioc k₀ k₁,
        ‖b r‖ * ‖b s‖ * B) =
        (∑ k ∈ Finset.Ioc k₀ k₁, ‖b k‖) ^ 2 * B := by
    symm
    rw [pow_two, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
  calc
    ‖reciprocalBilinearBlock X x y m₀ m₁ k₀ k₁ a b‖ ^ 2 ≤ _ := hbase
    _ = (∑ m ∈ Finset.Ioc m₀ m₁, ‖a m‖ ^ 2) *
        (∑ k ∈ Finset.Ioc k₀ k₁, ‖b k‖) ^ 2 * B := by
      rw [hpairs]
      ring

end

end BilinearReciprocal
end Erdos378
