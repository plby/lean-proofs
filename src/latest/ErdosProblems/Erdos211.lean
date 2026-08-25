/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 211.
https://www.erdosproblems.com/forum/thread/211

Informal authors:
- József Beck
- Endre Szemerédi
- William T. Trotter Jr.

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos211.md
-/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib
import Util.IncidenceGeometry.SzemerediTrotter

/-!
# Erdős Problem 211

If `1 ≤ k < n` and no affine line contains more than `n - k` points of an
`n`-point subset of the real affine plane, then the set determines `Ω(k n)`
distinct lines.

The proof first derives a two-term rich-line estimate from the formal
Szemerédi--Trotter theorem, integrates that estimate to obtain Beck's
two-extremes theorem, and finishes the rich-line alternative by counting
collisions among lines joining a large collinear subset to outside points.
-/

open Classical
open scoped Real

noncomputable section

namespace Erdos211

/-- The real Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Affine lines in the real Euclidean plane. -/
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

/-- The line determined by an off-diagonal ordered pair of points of `P`. -/
noncomputable def pairLine (P : Finset Point) (pq : P.offDiag) : Line :=
  ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set Point),
    ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩

/-- The finite set of distinct affine lines determined by two points of `P`. -/
noncomputable def determinedLines (P : Finset Point) : Finset Line :=
  P.offDiag.attach.image (pairLine P)

/-- The number of points of `P` incident to `ℓ`. -/
noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)).card

/-- The determined lines incident to at least `t` points of `P`. -/
noncomputable def richLines (P : Finset Point) (t : ℕ) : Finset Line :=
  (determinedLines P).filter fun ℓ ↦ t ≤ richness P ℓ

@[simp] lemma mem_richLines {P : Finset Point} {t : ℕ} {ℓ : Line} :
    ℓ ∈ richLines P t ↔ ℓ ∈ determinedLines P ∧ t ≤ richness P ℓ := by
  simp [richLines]

lemma affineSpan_pair_eq_line {p q : Point} (hpq : p ≠ q) (ℓ : Line)
    (hp : p ∈ (ℓ.1 : Set Point)) (hq : q ∈ (ℓ.1 : Set Point)) :
    affineSpan ℝ ({p, q} : Set Point) = ℓ.1 := by
  have line_le : affineSpan ℝ ({p, q} : Set Point) ≤ ℓ.1 :=
    affineSpan_le.2 (by
      intro z hz
      rcases hz with (rfl | hz)
      · exact hp
      · simpa only [Set.mem_singleton_iff] using hz ▸ hq)
  have line_rank : Module.finrank ℝ
      (affineSpan ℝ ({p, q} : Set Point)).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.2 hpq)
  have dir_eq :
      (affineSpan ℝ ({p, q} : Set Point)).direction = ℓ.1.direction :=
    Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le line_le)
      (line_rank.trans ℓ.2.2.symm)
  exact AffineSubspace.ext_of_direction_eq dir_eq
    ⟨p, subset_affineSpan ℝ _ (by simp), hp⟩

lemma mem_determinedLines_iff_two_points {P : Finset Point} {ℓ : Line} :
    ℓ ∈ determinedLines P ↔ 2 ≤ richness P ℓ := by
  constructor
  · intro hℓ
    obtain ⟨pq, hpq, hpqℓ⟩ := Finset.mem_image.mp hℓ
    have hpqmem : pq.1 ∈ P.offDiag := pq.2
    have hp := (Finset.mem_offDiag.mp hpqmem).1
    have hq := (Finset.mem_offDiag.mp hpqmem).2.1
    have hpqne := (Finset.mem_offDiag.mp hpqmem).2.2
    have hline : (pairLine P pq).1 = ℓ.1 := congrArg Subtype.val hpqℓ
    apply Finset.one_lt_card.mpr
    refine ⟨pq.1.1, ?_, pq.1.2, ?_, hpqne⟩
    · exact Finset.mem_filter.mpr ⟨hp, by
        rw [← hline]
        exact subset_affineSpan ℝ _ (by simp)⟩
    · exact Finset.mem_filter.mpr ⟨hq, by
        rw [← hline]
        exact subset_affineSpan ℝ _ (by simp)⟩
  · intro hcard
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpℓ : p ∈ (ℓ.1 : Set Point) := (Finset.mem_filter.mp hp).2
    have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
    have hqℓ : q ∈ (ℓ.1 : Set Point) := (Finset.mem_filter.mp hq).2
    let pq : P.offDiag :=
      ⟨(p, q), Finset.mem_offDiag.mpr ⟨hpP, hqP, hpq⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨pq, Finset.mem_attach _ pq, ?_⟩
    apply Subtype.ext
    exact affineSpan_pair_eq_line hpq ℓ hpℓ hqℓ

lemma mem_richLines_iff {P : Finset Point} {t : ℕ} (ht : 2 ≤ t) (ℓ : Line) :
    ℓ ∈ richLines P t ↔ t ≤ richness P ℓ := by
  rw [mem_richLines]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨mem_determinedLines_iff_two_points.mpr (ht.trans h), h⟩

/-- Incidences are the sum of the line richnesses. -/
lemma lineIncidences_eq_sum_richness (P : Finset Point) (L : Finset Line) :
    LineIncidences P L = ∑ ℓ ∈ L, richness P ℓ := by
  rw [LineIncidences, Finset.card_eq_sum_ones, Finset.sum_filter,
    show P.product L = P ×ˢ L by rfl]
  rw [Finset.sum_product]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, richness]
  rw [Finset.sum_comm]
  rfl

/-- The form of the rich-line estimate needed for Beck's theorem.  Unlike the
usual one-term corollary, this retains the `n / t` term and is therefore valid
for all `t ≥ 2`, including `t > sqrt n`. -/
theorem richLines_bound_all :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (P : Finset Point) (t : ℕ), 2 ≤ t →
        ((richLines P t).card : ℝ) ≤
          B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)) := by
  obtain ⟨C₀, hC₀, hST⟩ := SzemerediTrotter
  let A : ℝ := 3 * C₀
  let B : ℝ := max (max 1 A) (A ^ 3)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB_A : A ≤ B := le_trans (le_max_right 1 A) (le_max_left _ _)
  have hB_A3 : A ^ 3 ≤ B := le_max_right _ _
  have hB_one : (1 : ℝ) ≤ B :=
    le_trans (le_max_left 1 A) (le_max_left _ _)
  refine ⟨B, hB_one, ?_⟩
  intro P t ht
  let L := richLines P t
  have hLmem : ∀ ℓ, ℓ ∈ L ↔ t ≤ richness P ℓ := by
    intro ℓ
    exact mem_richLines_iff ht ℓ
  have hLcard_nat : L.card ≤ P.card ^ 2 := by
    calc
      L.card ≤ (determinedLines P).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ P.offDiag.attach.card := Finset.card_image_le
      _ = P.offDiag.card := Finset.card_attach
      _ ≤ (P.product P).card := Finset.card_le_card (by
        intro pq hpq
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_offDiag.mp hpq).1, (Finset.mem_offDiag.mp hpq).2.1⟩)
      _ = P.card ^ 2 := by simp [pow_two]
  by_cases hL0 : L.card = 0
  · have hnonneg :
        0 ≤ B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)) := by
      positivity
    simpa [L, hL0] using hnonneg
  have hLpos_nat : 0 < L.card := Nat.pos_of_ne_zero hL0
  have hLpos : 0 < (L.card : ℝ) := by exact_mod_cast hLpos_nat
  have ht_real : 0 < (t : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) ht)
  have hn : 0 ≤ (P.card : ℝ) := by positivity
  have hcrude : (L.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
    exact_mod_cast hLcard_nat
  have hlower_nat : t * L.card ≤ ∑ ℓ ∈ L, richness P ℓ := by
    calc
      t * L.card = ∑ _ℓ ∈ L, t := by simp [Nat.mul_comm]
      _ ≤ ∑ ℓ ∈ L, richness P ℓ :=
        Finset.sum_le_sum (fun ℓ hℓ ↦ (hLmem ℓ).mp hℓ)
  have hlower : (t : ℝ) * (L.card : ℝ) ≤ (LineIncidences P L : ℝ) := by
    rw [lineIncidences_eq_sum_richness]
    exact_mod_cast hlower_nat
  have hinc : (t : ℝ) * (L.card : ℝ) ≤
      C₀ * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
        (P.card : ℝ) + (L.card : ℝ)) :=
    hlower.trans (hST P L)
  have hnL : 0 ≤ (P.card : ℝ) * (L.card : ℝ) :=
    mul_nonneg hn hLpos.le
  let u : ℝ := ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)
  have hu : 0 ≤ u := Real.rpow_nonneg hnL _
  have hcases :
      (t : ℝ) * (L.card : ℝ) ≤ A * u ∨
      (t : ℝ) * (L.card : ℝ) ≤ A * (P.card : ℝ) ∨
      (t : ℝ) * (L.card : ℝ) ≤ A * (L.card : ℝ) := by
    by_cases h₁ : (t : ℝ) * (L.card : ℝ) ≤ A * u
    · exact Or.inl h₁
    by_cases h₂ : (t : ℝ) * (L.card : ℝ) ≤ A * (P.card : ℝ)
    · exact Or.inr (Or.inl h₂)
    refine Or.inr (Or.inr ?_)
    by_contra h₃
    have h₁' : A * u < (t : ℝ) * (L.card : ℝ) := lt_of_not_ge h₁
    have h₂' : A * (P.card : ℝ) < (t : ℝ) * (L.card : ℝ) :=
      lt_of_not_ge h₂
    have h₃' : A * (L.card : ℝ) < (t : ℝ) * (L.card : ℝ) :=
      lt_of_not_ge h₃
    have hstrict :
        C₀ * (u + (P.card : ℝ) + (L.card : ℝ)) <
          (t : ℝ) * (L.card : ℝ) := by
      dsimp [A] at h₁' h₂' h₃'
      nlinarith
    exact (not_lt_of_ge (hinc.trans_eq (by rfl))) hstrict
  have hmainTerm_nonneg : 0 ≤ (P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 := by positivity
  have hlinearTerm_nonneg : 0 ≤ (P.card : ℝ) / (t : ℝ) := by positivity
  rcases hcases with hmain | hlinear | hline
  · have hu_cube : u ^ (3 : ℕ) =
        ((P.card : ℝ) * (L.card : ℝ)) ^ (2 : ℕ) := by
      dsimp [u]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnL]
      norm_num
    have hpow := pow_le_pow_left₀
      (mul_nonneg ht_real.le hLpos.le) hmain 3
    simp only [mul_pow, hu_cube] at hpow
    have hLsq_pos : 0 < (L.card : ℝ) ^ 2 := sq_pos_of_pos hLpos
    have hcancel :
        (t : ℝ) ^ 3 * (L.card : ℝ) ≤ A ^ 3 * (P.card : ℝ) ^ 2 := by
      apply le_of_mul_le_mul_right _ hLsq_pos
      convert hpow using 1 <;> ring
    have ht_cube : 0 < (t : ℝ) ^ 3 := pow_pos ht_real _
    have hmain' :
        (L.card : ℝ) ≤ A ^ 3 * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ ht_cube).2
      simpa [mul_comm] using hcancel
    calc
      (L.card : ℝ) ≤ A ^ 3 * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3) := hmain'
      _ ≤ B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hB_A3 hmainTerm_nonneg
      _ ≤ B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlinearTerm_nonneg)
          (le_trans (by norm_num) hB_one)
  · have hlinear' : (L.card : ℝ) ≤ A * ((P.card : ℝ) / (t : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ ht_real).2
      simpa [mul_comm] using hlinear
    calc
      (L.card : ℝ) ≤ A * ((P.card : ℝ) / (t : ℝ)) := hlinear'
      _ ≤ B * ((P.card : ℝ) / (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hB_A hlinearTerm_nonneg
      _ ≤ B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hmainTerm_nonneg)
          (le_trans (by norm_num) hB_one)
  · have htA : (t : ℝ) ≤ A := le_of_mul_le_mul_right hline hLpos
    have htA3 : (t : ℝ) ^ 3 ≤ A ^ 3 :=
      pow_le_pow_left₀ ht_real.le htA 3
    have htB : (t : ℝ) ^ 3 ≤ B := htA3.trans hB_A3
    have ht_cube : 0 < (t : ℝ) ^ 3 := pow_pos ht_real _
    have hmain' :
        (L.card : ℝ) ≤ B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ ht_cube).2
      calc
        (L.card : ℝ) * (t : ℝ) ^ 3 ≤
            (P.card : ℝ) ^ 2 * (t : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hcrude (pow_nonneg ht_real.le _)
        _ ≤ (P.card : ℝ) ^ 2 * B :=
          mul_le_mul_of_nonneg_left htB (sq_nonneg (P.card : ℝ))
        _ = B * (P.card : ℝ) ^ 2 := by ring
    exact hmain'.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlinearTerm_nonneg)
        (le_trans (by norm_num) hB_one))

/-! ## Finite counting and summation lemmas -/

/-- Ordered pairs of distinct points of `P` which lie on `ℓ`. -/
noncomputable def pairsOnLine (P : Finset Point) (ℓ : Line) : Finset (Point × Point) :=
  P.offDiag.filter fun pq ↦ pq.1 ∈ (ℓ.1 : Set Point) ∧ pq.2 ∈ (ℓ.1 : Set Point)

lemma card_pairsOnLine_le_sq (P : Finset Point) (ℓ : Line) :
    (pairsOnLine P ℓ).card ≤ richness P ℓ ^ 2 := by
  calc
    (pairsOnLine P ℓ).card ≤
        ((P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)).product
          (P.filter fun p ↦ p ∈ (ℓ.1 : Set Point))).card :=
      Finset.card_le_card (by
        intro pq hpq
        have h := Finset.mem_filter.mp hpq
        have hp := Finset.mem_offDiag.mp h.1
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hp.1, h.2.1⟩,
          Finset.mem_filter.mpr ⟨hp.2.1, h.2.2⟩⟩)
    _ = richness P ℓ ^ 2 := by simp [richness, pow_two]

lemma offDiag_subset_pairsOnLine_biUnion (P : Finset Point) :
    P.offDiag ⊆ (determinedLines P).biUnion (pairsOnLine P) := by
  intro pq hpq
  let q : P.offDiag := ⟨pq, hpq⟩
  have hline : pairLine P q ∈ determinedLines P := by
    apply Finset.mem_image.mpr
    exact ⟨q, Finset.mem_attach _ q, rfl⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨pairLine P q, hline, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hpq, ?_, ?_⟩
  · exact subset_affineSpan ℝ _ (by simp [q])
  · exact subset_affineSpan ℝ _ (by simp [q])

/-- Every ordered pair is assigned to a determined line; allowing overlaps
gives the moment inequality used below. -/
lemma offDiag_card_le_sum_richness_sq (P : Finset Point) :
    P.offDiag.card ≤ ∑ ℓ ∈ determinedLines P, richness P ℓ ^ 2 := by
  calc
    P.offDiag.card ≤
        ((determinedLines P).biUnion (pairsOnLine P)).card :=
      Finset.card_le_card (offDiag_subset_pairsOnLine_biUnion P)
    _ ≤ ∑ ℓ ∈ determinedLines P, (pairsOnLine P ℓ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ ℓ ∈ determinedLines P, richness P ℓ ^ 2 :=
      Finset.sum_le_sum fun ℓ _ ↦ card_pairsOnLine_le_sq P ℓ

lemma sq_le_sq_add_sum_two_Icc {R r : ℕ} (hRr : R ≤ r) :
    (r : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 +
      ∑ t ∈ Finset.Icc (R + 1) r, 2 * (t : ℝ) := by
  induction r, hRr using Nat.le_induction with
  | base => simp
  | succ r hRr ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      nlinarith

lemma sum_inv_sq_Icc_le_sub {R M : ℕ} (hR : 1 ≤ R) (hRM : R ≤ M) :
    (∑ t ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (t : ℝ) ^ 2) ≤
      (1 : ℝ) / R - (1 : ℝ) / M := by
  induction M, hRM using Nat.le_induction with
  | base => simp
  | succ M hRM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < R) hRM)
      have hMs : (0 : ℝ) < M + 1 := by positivity
      have hstep : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤
          (1 : ℝ) / M - (1 : ℝ) / ((M + 1 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        nlinarith
      calc
        (∑ t ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (t : ℝ) ^ 2) +
              (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤
            ((1 : ℝ) / R - (1 : ℝ) / M) +
              ((1 : ℝ) / M - (1 : ℝ) / ((M + 1 : ℕ) : ℝ)) :=
          add_le_add ih hstep
        _ = (1 : ℝ) / R - (1 : ℝ) / ((M + 1 : ℕ) : ℝ) := by ring

lemma sum_inv_sq_Icc_le {R M : ℕ} (hR : 1 ≤ R) :
    (∑ t ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (t : ℝ) ^ 2) ≤
      (1 : ℝ) / R := by
  by_cases hRM : R ≤ M
  · exact (sum_inv_sq_Icc_le_sub hR hRM).trans (sub_le_self _ (by positivity))
  · have hempty : Finset.Icc (R + 1) M = ∅ := by
      ext t
      simp
      omega
    simp [hempty]

/-- The square-mass of lines above a cutoff, assuming an upper cutoff `M`.
This is the finite layer-cake step in Beck's argument. -/
lemma richLine_square_mass_bound
    {B : ℝ} (hB : 0 ≤ B)
    (hrich : ∀ (P : Finset Point) (t : ℕ), 2 ≤ t →
      ((richLines P t).card : ℝ) ≤
        B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)))
    (P : Finset Point) {R M : ℕ} (hR : 2 ≤ R)
    (hmax : ∀ ℓ ∈ determinedLines P, richness P ℓ ≤ M) :
    (∑ ℓ ∈ richLines P R, (richness P ℓ : ℝ) ^ 2) ≤
      B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * R) +
        2 * B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * M) := by
  let H := richLines P R
  let T := Finset.Icc (R + 1) M
  have hpoint : ∀ ℓ ∈ H,
      (richness P ℓ : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 +
        ∑ t ∈ T, if t ≤ richness P ℓ then 2 * (t : ℝ) else 0 := by
    intro ℓ hℓ
    have hRℓ : R ≤ richness P ℓ := (mem_richLines.mp hℓ).2
    have hℓM : richness P ℓ ≤ M := hmax ℓ (mem_richLines.mp hℓ).1
    have hfilter : T.filter (fun t ↦ t ≤ richness P ℓ) =
        Finset.Icc (R + 1) (richness P ℓ) := by
      ext t
      simp [T]
      omega
    calc
      (richness P ℓ : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 +
          ∑ t ∈ Finset.Icc (R + 1) (richness P ℓ), 2 * (t : ℝ) :=
        sq_le_sq_add_sum_two_Icc hRℓ
      _ = (R : ℝ) ^ 2 + ∑ t ∈ T,
          if t ≤ richness P ℓ then 2 * (t : ℝ) else 0 := by
        rw [← hfilter, Finset.sum_filter]
  have hfilter (t : ℕ) (ht : t ∈ T) :
      H.filter (fun ℓ ↦ t ≤ richness P ℓ) = richLines P t := by
    dsimp [H]
    ext ℓ
    simp only [Finset.mem_filter, mem_richLines]
    have htR : R ≤ t := by
      have := (Finset.mem_Icc.mp ht).1
      omega
    constructor
    · rintro ⟨⟨hdet, _⟩, htr⟩
      exact ⟨hdet, htr⟩
    · rintro ⟨hdet, htr⟩
      exact ⟨⟨hdet, htR.trans htr⟩, htr⟩
  have hlayers :
      (∑ ℓ ∈ H, ∑ t ∈ T,
          if t ≤ richness P ℓ then 2 * (t : ℝ) else 0) =
        ∑ t ∈ T, 2 * (t : ℝ) * ((richLines P t).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← Finset.sum_filter]
    rw [hfilter t ht]
    simp
    ring
  have hmass :
      (∑ ℓ ∈ H, (richness P ℓ : ℝ) ^ 2) ≤
        (R : ℝ) ^ 2 * H.card +
          ∑ t ∈ T, 2 * (t : ℝ) * ((richLines P t).card : ℝ) := by
    calc
      (∑ ℓ ∈ H, (richness P ℓ : ℝ) ^ 2) ≤
          ∑ ℓ ∈ H, ((R : ℝ) ^ 2 +
            ∑ t ∈ T, if t ≤ richness P ℓ then 2 * (t : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
      _ = (R : ℝ) ^ 2 * H.card +
          ∑ ℓ ∈ H, ∑ t ∈ T,
            if t ≤ richness P ℓ then 2 * (t : ℝ) else 0 := by
        rw [Finset.sum_add_distrib]
        simp
        ring
      _ = _ := by rw [hlayers]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hR)
  have hbase : (R : ℝ) ^ 2 * H.card ≤
      B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * R) := by
    have hb := hrich P R hR
    dsimp [H]
    calc
      (R : ℝ) ^ 2 * ((richLines P R).card : ℝ) ≤
          (R : ℝ) ^ 2 *
            (B * ((P.card : ℝ) ^ 2 / (R : ℝ) ^ 3 +
              (P.card : ℝ) / (R : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * R) := by
        field_simp
  have htail_point : ∀ t ∈ T,
      2 * (t : ℝ) * ((richLines P t).card : ℝ) ≤
        2 * B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 2 + (P.card : ℝ)) := by
    intro t ht
    have ht2 : 2 ≤ t := by
      have := (Finset.mem_Icc.mp ht).1
      omega
    have htpos : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) ht2)
    calc
      2 * (t : ℝ) * ((richLines P t).card : ℝ) ≤
          2 * (t : ℝ) *
            (B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 +
              (P.card : ℝ) / (t : ℝ))) :=
        mul_le_mul_of_nonneg_left (hrich P t ht2) (by positivity)
      _ = 2 * B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 2 + (P.card : ℝ)) := by
        field_simp
  have htail :
      (∑ t ∈ T, 2 * (t : ℝ) * ((richLines P t).card : ℝ)) ≤
        2 * B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * M) := by
    calc
      (∑ t ∈ T, 2 * (t : ℝ) * ((richLines P t).card : ℝ)) ≤
          ∑ t ∈ T,
            2 * B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 2 + (P.card : ℝ)) :=
        Finset.sum_le_sum htail_point
      _ = 2 * B * (P.card : ℝ) ^ 2 *
            (∑ t ∈ T, (1 : ℝ) / (t : ℝ) ^ 2) +
          2 * B * (P.card : ℝ) * T.card := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        simp
        ring
      _ ≤ 2 * B * (P.card : ℝ) ^ 2 * ((1 : ℝ) / R) +
          2 * B * (P.card : ℝ) * M := by
        gcongr
        · exact sum_inv_sq_Icc_le (by omega : 1 ≤ R)
        · have hcard : T.card ≤ M := by
            dsimp [T]
            simp only [Nat.card_Icc]
            omega
          exact_mod_cast hcard
      _ = 2 * B * ((P.card : ℝ) ^ 2 / R + (P.card : ℝ) * M) := by
        field_simp
  simpa [H] using hmass.trans (add_le_add hbase htail)

/-- Beck's many-lines alternative: if every determined line is below the
`n / R` scale, a fixed positive proportion of the ordered pairs lies on
lines of richness below `R`. -/
lemma square_le_eight_mul_lines_of_bounded_richness
    {B : ℝ} (hB : 0 ≤ B)
    (hrich : ∀ (P : Finset Point) (t : ℕ), 2 ≤ t →
      ((richLines P t).card : ℝ) ≤
        B * ((P.card : ℝ) ^ 2 / (t : ℝ) ^ 3 + (P.card : ℝ) / (t : ℝ)))
    (P : Finset Point) {R : ℕ} (hR : 2 ≤ R) (hn : 2 ≤ P.card)
    (hBR : 48 * B ≤ R)
    (hsmall : ∀ ℓ ∈ determinedLines P, R * richness P ℓ < P.card) :
    (P.card : ℝ) ^ 2 ≤
      8 * (R : ℝ) ^ 2 * ((determinedLines P).card : ℝ) := by
  let n := P.card
  let D := determinedLines P
  let M := n / R
  let H := richLines P R
  let L := D.filter fun ℓ ↦ ¬R ≤ richness P ℓ
  have hRpos_nat : 0 < R := by omega
  have hmax : ∀ ℓ ∈ D, richness P ℓ ≤ M := by
    intro ℓ hℓ
    apply (Nat.le_div_iff_mul_le hRpos_nat).2
    have hs := hsmall ℓ hℓ
    rw [Nat.mul_comm]
    exact hs.le
  have hhigh_raw := richLine_square_mass_bound hB hrich P hR hmax
  have hhigh : (∑ ℓ ∈ H, (richness P ℓ : ℝ) ^ 2) ≤
      (n : ℝ) ^ 2 / 8 := by
    by_cases hH : H = ∅
    · simp only [hH, Finset.sum_empty]
      positivity
    have hHne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH
    obtain ⟨ℓ, hℓH⟩ := hHne
    have hRM : R ≤ M :=
      (mem_richLines.mp hℓH).2.trans (hmax ℓ (mem_richLines.mp hℓH).1)
    have hMR : M * R ≤ n := (Nat.le_div_iff_mul_le hRpos_nat).1 le_rfl
    have hRR : R * R ≤ n := by nlinarith
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hRpos_nat
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hnR : (n : ℝ) * R ≤ (n : ℝ) ^ 2 / R := by
      apply (le_div_iff₀ hRpos).2
      have hRR' : (R : ℝ) ^ 2 ≤ n := by
        have hRRpow : R ^ 2 ≤ n := by simpa [pow_two] using hRR
        exact_mod_cast hRRpow
      calc
        (n : ℝ) * R * R = (n : ℝ) * (R : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hRR' hn0
        _ = (n : ℝ) ^ 2 := by ring
    have hMn : (M : ℝ) * R ≤ n := by exact_mod_cast hMR
    have hMdiv : (M : ℝ) ≤ (n : ℝ) / R := (le_div_iff₀ hRpos).2 hMn
    have hnM : (n : ℝ) * M ≤ (n : ℝ) ^ 2 / R := by
      calc
        (n : ℝ) * M ≤ (n : ℝ) * ((n : ℝ) / R) :=
          mul_le_mul_of_nonneg_left hMdiv hn0
        _ = (n : ℝ) ^ 2 / R := by ring
    have hBR' : 48 * B ≤ (R : ℝ) := by exact_mod_cast hBR
    calc
      (∑ ℓ ∈ H, (richness P ℓ : ℝ) ^ 2) ≤
          B * ((n : ℝ) ^ 2 / R + (n : ℝ) * R) +
            2 * B * ((n : ℝ) ^ 2 / R + (n : ℝ) * M) := by
        simpa [H, M, n, D] using hhigh_raw
      _ ≤ B * ((n : ℝ) ^ 2 / R + (n : ℝ) ^ 2 / R) +
            2 * B * ((n : ℝ) ^ 2 / R + (n : ℝ) ^ 2 / R) := by
        gcongr
      _ ≤ (n : ℝ) ^ 2 / 8 := by
        have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
        calc
          B * ((n : ℝ) ^ 2 / R + (n : ℝ) ^ 2 / R) +
                2 * B * ((n : ℝ) ^ 2 / R + (n : ℝ) ^ 2 / R) =
              6 * B * (n : ℝ) ^ 2 / R := by ring
          _ ≤ (n : ℝ) ^ 2 / 8 := by
            apply (div_le_iff₀ hRpos).2
            nlinarith [mul_nonneg hB hn2]
  have hsplit :
      (∑ ℓ ∈ H, (richness P ℓ : ℝ) ^ 2) +
          (∑ ℓ ∈ L, (richness P ℓ : ℝ) ^ 2) =
        ∑ ℓ ∈ D, (richness P ℓ : ℝ) ^ 2 := by
    have hs := Finset.sum_filter_add_sum_filter_not D
      (fun ℓ ↦ R ≤ richness P ℓ) (fun ℓ ↦ (richness P ℓ : ℝ) ^ 2)
    simpa [H, L, D, richLines, add_comm] using hs
  have hpairs_nat := offDiag_card_le_sum_richness_sq P
  have hpairs : ((P.offDiag.card : ℕ) : ℝ) ≤
      ∑ ℓ ∈ D, (richness P ℓ : ℝ) ^ 2 := by
    exact_mod_cast hpairs_nat
  have hoffdiag : ((P.offDiag.card : ℕ) : ℝ) = (n : ℝ) * (n - 1) := by
    rw [Finset.offDiag_card]
    have hle : P.card ≤ P.card * P.card := by nlinarith
    rw [Nat.cast_sub hle]
    dsimp [n]
    push_cast
    ring
  have hn_half : (n : ℝ) ^ 2 / 2 ≤ ((P.offDiag.card : ℕ) : ℝ) := by
    rw [hoffdiag]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlow_lower : 3 * (n : ℝ) ^ 2 / 8 ≤
      ∑ ℓ ∈ L, (richness P ℓ : ℝ) ^ 2 := by
    rw [← hsplit] at hpairs
    nlinarith
  have hlow_upper : (∑ ℓ ∈ L, (richness P ℓ : ℝ) ^ 2) ≤
      (R : ℝ) ^ 2 * ((D.card : ℕ) : ℝ) := by
    calc
      (∑ ℓ ∈ L, (richness P ℓ : ℝ) ^ 2) ≤
          ∑ _ℓ ∈ L, (R : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hlt : richness P ℓ < R := by
          have := (Finset.mem_filter.mp hℓ).2
          omega
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hlt.le) 2
      _ = (R : ℝ) ^ 2 * L.card := by
        simp
        ring
      _ ≤ (R : ℝ) ^ 2 * D.card := by
        have hcard : L.card ≤ D.card := by
          exact Finset.card_le_card (Finset.filter_subset _ _)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact_mod_cast hcard
  calc
    (P.card : ℝ) ^ 2 = (n : ℝ) ^ 2 := by rfl
    _ ≤ 8 * ((R : ℝ) ^ 2 * (D.card : ℝ)) := by nlinarith
    _ = 8 * (R : ℝ) ^ 2 * ((determinedLines P).card : ℝ) := by
      simp [D]
      ring

/-! ## The large-line alternative -/

/-- Lines joining a fixed determined line to an outside set: every failure of
injectivity is charged to an ordered pair of distinct outside points. -/
lemma cross_pairs_le_lines_add_offDiag
    (P : Finset Point) (ℓ : Line) (_hℓ : ℓ ∈ determinedLines P)
    (S : Finset Point) (hSP : S ⊆ P)
    (hSout : ∀ p ∈ S, p ∉ (ℓ.1 : Set Point)) :
    richness P ℓ * S.card ≤ (determinedLines P).card + S.offDiag.card := by
  let A := P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)
  let X := A.product S
  let toPair : X → P.offDiag := fun x ↦
    ⟨x.1, by
      have hx := Finset.mem_product.mp x.2
      have haP := (Finset.mem_filter.mp hx.1).1
      have hbP := hSP hx.2
      apply Finset.mem_offDiag.mpr
      refine ⟨haP, hbP, ?_⟩
      intro hab
      have haℓ := (Finset.mem_filter.mp hx.1).2
      exact hSout x.1.2 hx.2 (hab ▸ haℓ)⟩
  let f : X → Line := fun x ↦ pairLine P (toPair x)
  let C := X.attach.image f
  let F := fun line : Line ↦ X.attach.filter (fun x ↦ f x = line)
  let O : Line → Finset Point :=
    fun line ↦ S.filter (fun p ↦ p ∈ (line.1 : Set Point))
  have hCsub : C ⊆ determinedLines P := by
    intro line hline
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hline
    apply Finset.mem_image.mpr
    exact ⟨toPair x, Finset.mem_attach _ (toPair x), rfl⟩
  have hfiber : ∀ line ∈ C, (F line).card ≤ (O line).card := by
    intro line hline
    apply Finset.card_le_card_of_injOn (fun x : X ↦ x.1.2)
    · intro x hx
      have hxF := Finset.mem_filter.mp hx
      have hxprod := Finset.mem_product.mp x.2
      apply Finset.mem_filter.mpr
      refine ⟨hxprod.2, ?_⟩
      have hb : x.1.2 ∈ ((f x).1 : Set Point) := by
        dsimp [f, toPair, pairLine]
        exact subset_affineSpan ℝ _ (by simp)
      rw [hxF.2] at hb
      exact hb
    · intro x hx y hy hxy
      have hxF := Finset.mem_filter.mp hx
      have hyF := Finset.mem_filter.mp hy
      apply Subtype.ext
      apply Prod.ext
      · by_contra hane
        have hxprod := Finset.mem_product.mp x.2
        have hyprod := Finset.mem_product.mp y.2
        have haxℓ : x.1.1 ∈ (ℓ.1 : Set Point) :=
          (Finset.mem_filter.mp hxprod.1).2
        have hayℓ : y.1.1 ∈ (ℓ.1 : Set Point) :=
          (Finset.mem_filter.mp hyprod.1).2
        have haxLine : x.1.1 ∈ (line.1 : Set Point) := by
          have hmem : x.1.1 ∈ ((f x).1 : Set Point) := by
            dsimp [f, toPair, pairLine]
            exact subset_affineSpan ℝ _ (by simp)
          rw [hxF.2] at hmem
          exact hmem
        have hayLine : y.1.1 ∈ (line.1 : Set Point) := by
          have hmem : y.1.1 ∈ ((f y).1 : Set Point) := by
            dsimp [f, toPair, pairLine]
            exact subset_affineSpan ℝ _ (by simp)
          rw [hyF.2] at hmem
          exact hmem
        have hlineℓ : line.1 = ℓ.1 :=
          (affineSpan_pair_eq_line hane line haxLine hayLine).symm.trans
            (affineSpan_pair_eq_line hane ℓ haxℓ hayℓ)
        have hbxLine : x.1.2 ∈ (line.1 : Set Point) := by
          have hmem : x.1.2 ∈ ((f x).1 : Set Point) := by
            dsimp [f, toPair, pairLine]
            exact subset_affineSpan ℝ _ (by simp)
          rw [hxF.2] at hmem
          exact hmem
        have hbxS : x.1.2 ∈ S := hxprod.2
        exact hSout x.1.2 hbxS (hlineℓ ▸ hbxLine)
      · exact hxy
  have hOpos : ∀ line ∈ C, 1 ≤ (O line).card := by
    intro line hline
    obtain ⟨x, _hx, hfx⟩ := Finset.mem_image.mp hline
    apply Finset.card_pos.mpr
    refine ⟨x.1.2, Finset.mem_filter.mpr ⟨(Finset.mem_product.mp x.2).2, ?_⟩⟩
    have hb : x.1.2 ∈ ((f x).1 : Set Point) := by
      dsimp [f, toPair, pairLine]
      exact subset_affineSpan ℝ _ (by simp)
    rw [hfx] at hb
    exact hb
  have hOcard : ∀ line ∈ C, (O line).card ≤ 1 + (O line).offDiag.card := by
    intro line hline
    rw [Finset.offDiag_card]
    have hp := hOpos line hline
    by_cases hone : (O line).card = 1
    · simp [hone]
    have htwo : 2 ≤ (O line).card := by omega
    have hmul : (O line).card ≤ (O line).card * ((O line).card - 1) := by
      have h := Nat.mul_le_mul_left (O line).card (show 1 ≤ (O line).card - 1 by omega)
      simpa using h
    have hfactor : (O line).card * ((O line).card - 1) =
        (O line).card * (O line).card - (O line).card := by
      simpa using Nat.mul_sub_left_distrib (O line).card (O line).card 1
    omega
  have hpairwise : (C : Set Line).PairwiseDisjoint (fun line ↦ (O line).offDiag) := by
    intro line₁ hline₁ line₂ hline₂ hne
    change Disjoint ((O line₁).offDiag) ((O line₂).offDiag)
    rw [Finset.disjoint_left]
    intro pq hpq₁ hpq₂
    have hp₁ := Finset.mem_offDiag.mp hpq₁
    have hp₂ := Finset.mem_offDiag.mp hpq₂
    have hp₁a := (Finset.mem_filter.mp hp₁.1).2
    have hp₁b := (Finset.mem_filter.mp hp₁.2.1).2
    have hp₂a := (Finset.mem_filter.mp hp₂.1).2
    have hp₂b := (Finset.mem_filter.mp hp₂.2.1).2
    have hspan₁ := affineSpan_pair_eq_line hp₁.2.2 line₁ hp₁a hp₁b
    have hspan₂ := affineSpan_pair_eq_line hp₁.2.2 line₂ hp₂a hp₂b
    apply hne
    apply Subtype.ext
    exact hspan₁.symm.trans hspan₂
  have hbiSub : C.biUnion (fun line ↦ (O line).offDiag) ⊆ S.offDiag := by
    intro pq hpq
    obtain ⟨line, _hline, hpqLine⟩ := Finset.mem_biUnion.mp hpq
    have hp := Finset.mem_offDiag.mp hpqLine
    apply Finset.mem_offDiag.mpr
    exact ⟨(Finset.mem_filter.mp hp.1).1,
      (Finset.mem_filter.mp hp.2.1).1, hp.2.2⟩
  have hpairsum : (∑ line ∈ C, (O line).offDiag.card) ≤ S.offDiag.card := by
    rw [← Finset.card_biUnion hpairwise]
    exact Finset.card_le_card hbiSub
  have hCcard : C.card ≤ (determinedLines P).card :=
    Finset.card_le_card hCsub
  have hdomain : X.card ≤ (determinedLines P).card + S.offDiag.card := by
    calc
      X.card = X.attach.card := by simp
      _ = ∑ line ∈ C, (F line).card := by
        simpa [C, F] using Finset.card_eq_sum_card_image f X.attach
      _ ≤ ∑ line ∈ C, (O line).card := Finset.sum_le_sum hfiber
      _ ≤ ∑ line ∈ C, (1 + (O line).offDiag.card) :=
        Finset.sum_le_sum hOcard
      _ = C.card + ∑ line ∈ C, (O line).offDiag.card := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (determinedLines P).card + S.offDiag.card :=
        Nat.add_le_add hCcard hpairsum
  simpa [X, A, richness] using hdomain

lemma kn_le_eight_mul_R_sq_lines_of_large_line
    (P : Finset Point) {n k R : ℕ} (hR : 2 ≤ R)
    (hk : 1 ≤ k) (hkn : k < n) (hcard : P.card = n)
    (hcap : ∀ line : Line, richness P line ≤ n - k)
    (line : Line) (hline : line ∈ determinedLines P)
    (hlarge : n ≤ R * richness P line) :
    k * n ≤ 8 * R ^ 2 * (determinedLines P).card := by
  let m := richness P line
  let Q := P.filter fun p ↦ p ∉ (line.1 : Set Point)
  let s := min k (m / 2)
  have hm2 : 2 ≤ m := by
    dsimp [m]
    exact mem_determinedLines_iff_two_points.mp hline
  have hpart : m + Q.card = n := by
    have hp := P.card_filter_add_card_filter_not
      (fun p ↦ p ∈ (line.1 : Set Point))
    simpa [m, Q, richness, hcard, add_comm] using hp
  have hkQ : k ≤ Q.card := by
    have hmcap : m ≤ n - k := hcap line
    omega
  have hsQ : s ≤ Q.card := (min_le_left _ _).trans hkQ
  obtain ⟨S, hSQ, hScard⟩ := Finset.exists_subset_card_eq hsQ
  have hSP : S ⊆ P := by
    intro p hp
    exact (Finset.mem_filter.mp (hSQ hp)).1
  have hSout : ∀ p ∈ S, p ∉ (line.1 : Set Point) := by
    intro p hp
    exact (Finset.mem_filter.mp (hSQ hp)).2
  have hcross := cross_pairs_le_lines_add_offDiag P line hline S hSP hSout
  have hs1 : 1 ≤ s := by
    dsimp [s]
    have : 1 ≤ m / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    simp [hk, this]
  have hsoff : ((S.offDiag.card : ℕ) : ℝ) =
      (s : ℝ) ^ 2 - (s : ℝ) := by
    rw [Finset.offDiag_card, hScard]
    have hsle : s ≤ s * s := by nlinarith
    rw [Nat.cast_sub hsle]
    push_cast
    ring
  have hcross_real : (m : ℝ) * s ≤
      ((determinedLines P).card : ℝ) + (s : ℝ) ^ 2 - s := by
    have hc : ((m * S.card : ℕ) : ℝ) ≤
        (((determinedLines P).card + S.offDiag.card : ℕ) : ℝ) := by
      exact_mod_cast hcross
    push_cast at hc
    rw [hScard, hsoff] at hc
    nlinarith
  have h2s : 2 * s ≤ m := by
    calc
      2 * s = s * 2 := by omega
      _ ≤ (m / 2) * 2 := Nat.mul_le_mul_right 2 (min_le_right _ _)
      _ ≤ m := Nat.div_mul_le_self m 2
  have hs_sq : (s : ℝ) ^ 2 ≤ (m : ℝ) * s / 2 := by
    have h2s' : (2 : ℝ) * s ≤ m := by exact_mod_cast h2s
    have hs0 : (0 : ℝ) ≤ s := by positivity
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr h2s')]
  have hmsD : (m : ℝ) * s ≤
      2 * ((determinedLines P).card : ℝ) := by
    have hs0 : (0 : ℝ) ≤ s := by positivity
    nlinarith
  by_cases hkm : k ≤ m / 2
  · have hsk : s = k := min_eq_left hkm
    have hnk : n * k ≤ R * m * k := Nat.mul_le_mul_right k hlarge
    have hnk' : (n : ℝ) * k ≤ (R : ℝ) * m * k := by exact_mod_cast hnk
    have hmkD : (m : ℝ) * k ≤
        2 * ((determinedLines P).card : ℝ) := by simpa [hsk] using hmsD
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have hD0 : (0 : ℝ) ≤ ((determinedLines P).card : ℝ) := by positivity
    have hbound : (n : ℝ) * k ≤
        8 * (R : ℝ) ^ 2 * ((determinedLines P).card : ℝ) := by
      have hmul := mul_nonneg hR0
        (sub_nonneg.mpr hmkD)
      have hRtwo : (2 : ℝ) ≤ R := by exact_mod_cast hR
      nlinarith [mul_nonneg hD0 (sq_nonneg ((R : ℝ) - 1))]
    have hbound_nat : n * k ≤
        8 * R ^ 2 * (determinedLines P).card := by
      exact_mod_cast hbound
    simpa [Nat.mul_comm] using hbound_nat
  · have hsm : s = m / 2 := min_eq_right (le_of_not_ge hkm)
    have hm4s : m ≤ 4 * s := by
      dsimp [s]
      omega
    have hm4s' : (m : ℝ) ≤ 4 * s := by exact_mod_cast hm4s
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hmSqD : (m : ℝ) ^ 2 ≤
        8 * ((determinedLines P).card : ℝ) := by
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm4s')]
    have hkn_le : k * n ≤ n ^ 2 := by nlinarith
    have hlarge' : (n : ℝ) ≤ (R : ℝ) * m := by exact_mod_cast hlarge
    have hsq : (n : ℝ) ^ 2 ≤ ((R : ℝ) * m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlarge' 2
    have hbound : (k : ℝ) * n ≤
        8 * (R : ℝ) ^ 2 * ((determinedLines P).card : ℝ) := by
      have hkn_le' : (k * n : ℝ) ≤ (n ^ 2 : ℕ) := by exact_mod_cast hkn_le
      push_cast at hkn_le'
      calc
        (k : ℝ) * n ≤ (n : ℝ) ^ 2 := by simpa [pow_two] using hkn_le'
        _ ≤ ((R : ℝ) * m) ^ 2 := hsq
        _ = (R : ℝ) ^ 2 * (m : ℝ) ^ 2 := by ring
        _ ≤ (R : ℝ) ^ 2 *
            (8 * ((determinedLines P).card : ℝ)) := by
          gcongr
        _ = 8 * (R : ℝ) ^ 2 * ((determinedLines P).card : ℝ) := by ring
    exact_mod_cast hbound

/-! ## Resolution of Erdős Problem 211 -/

/-- **Erdős Problem 211 (Beck; Szemerédi--Trotter).** There is an absolute
constant `C` such that, whenever `1 ≤ k < n`, every `n`-point set in the real
plane with at most `n-k` points on any affine line determines at least
`k*n/C` distinct affine lines.  The division-free conclusion is the exact
natural-number form of `#lines ≫ k n`. -/
theorem erdos_211 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n k : ℕ) (P : Finset Point),
        1 ≤ k → k < n → P.card = n →
        (∀ line : Line, richness P line ≤ n - k) →
        k * n ≤ C * (determinedLines P).card := by
  obtain ⟨B, hB1, hrich⟩ := richLines_bound_all
  have hB0 : 0 ≤ B := by nlinarith
  obtain ⟨R, hRbig⟩ := exists_nat_ge (max (2 : ℝ) (48 * B))
  have hR : 2 ≤ R := by
    have : (2 : ℝ) ≤ R := (le_max_left _ _).trans hRbig
    exact_mod_cast this
  have hBR : 48 * B ≤ (R : ℝ) := (le_max_right _ _).trans hRbig
  refine ⟨8 * R ^ 2, by positivity, ?_⟩
  intro n k P hk hkn hcard hcap
  have hn : 2 ≤ P.card := by omega
  by_cases hsmall : ∀ line ∈ determinedLines P,
      R * richness P line < P.card
  · have hsquare := square_le_eight_mul_lines_of_bounded_richness
      hB0 hrich P hR hn hBR hsmall
    have hsquare_nat : P.card ^ 2 ≤
        8 * R ^ 2 * (determinedLines P).card := by
      exact_mod_cast hsquare
    have hknsq : k * n ≤ n ^ 2 := by
      have := Nat.mul_le_mul_right n hkn.le
      simpa [pow_two] using this
    calc
      k * n ≤ n ^ 2 := hknsq
      _ = P.card ^ 2 := by rw [hcard]
      _ ≤ 8 * R ^ 2 * (determinedLines P).card := hsquare_nat
  · push Not at hsmall
    obtain ⟨line, hline, hlarge⟩ := hsmall
    exact kn_le_eight_mul_R_sq_lines_of_large_line
      P hR hk hkn hcard hcap line hline (by simpa [hcard] using hlarge)

#print axioms erdos_211

end Erdos211
