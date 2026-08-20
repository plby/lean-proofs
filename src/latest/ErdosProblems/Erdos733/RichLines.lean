import ErdosProblems.Erdos733.ST.SzemerediTrotter

open Classical
open scoped Real

namespace Erdos733

noncomputable section

/-- The global rich-line estimate used in the proof of Erdős Problem 733.

The lower-order `n / k` term makes the estimate valid beyond the usual
`k ≤ √n` range of the rich-line corollary of Szemerédi--Trotter. -/
private theorem globalRichLinesBound_of_ST
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hST : ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset
          {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}),
      (LineIncidences P L : ℝ) ≤
        C₀ * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
          (P.card : ℝ) + (L.card : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ),
        2 ≤ k →
          ∃ L : Finset
              {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ},
            (∀ ℓ, ℓ ∈ L ↔
              k ≤ (P.filter (fun p =>
                p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card) ∧
            (L.card : ℝ) ≤ C *
              ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
                (P.card : ℝ) / (k : ℝ)) := by
  classical
  let A : ℝ := 3 * C₀
  let C : ℝ := max (max 1 A) (A ^ 3)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hC_A : A ≤ C := le_trans (le_max_right 1 A) (le_max_left _ _)
  have hC_A3 : A ^ 3 ≤ C := le_max_right _ _
  have hC_one : (1 : ℝ) ≤ C :=
    le_trans (le_max_left 1 A) (le_max_left _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hC_one
  refine ⟨C, hC, ?_⟩
  intro P k hk
  let pairLine : P.offDiag →
      {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ} :=
    fun pq =>
      ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set (EuclideanSpace ℝ (Fin 2))),
        ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
          rw [direction_affineSpan, vectorSpan_pair]
          exact finrank_span_singleton
            (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩
  let allLines := Finset.image pairLine P.offDiag.attach
  let L := allLines.filter (fun ℓ :
      {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ} =>
    k ≤ (P.filter (fun p =>
      p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card)
  have hmem : ∀ ℓ, ℓ ∈ L ↔
      k ≤ (P.filter (fun p =>
        p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card := by
    intro ℓ
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro hrich
      apply Finset.mem_filter.mpr
      refine ⟨?_, hrich⟩
      have hcard : 2 ≤ (P.filter (fun p =>
          p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card :=
        hk.trans hrich
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hpℓ : p ∈ (ℓ : AffineSubspace ℝ
          (EuclideanSpace ℝ (Fin 2))) := (Finset.mem_filter.mp hp).2
      have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
      have hqℓ : q ∈ (ℓ : AffineSubspace ℝ
          (EuclideanSpace ℝ (Fin 2))) := (Finset.mem_filter.mp hq).2
      let pq : P.offDiag :=
        ⟨(p, q), Finset.mem_offDiag.mpr ⟨hpP, hqP, hpq⟩⟩
      have line_le :
          affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ :=
        affineSpan_le.2 (by
          intro z hz
          rcases hz with (rfl | hz)
          · exact hpℓ
          · simpa only [Set.mem_singleton_iff] using hz ▸ hqℓ)
      have line_rank : Module.finrank ℝ
          (affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))).direction = 1 := by
        rw [direction_affineSpan, vectorSpan_pair]
        exact finrank_span_singleton (vsub_ne_zero.2 hpq)
      have dir_eq :
          (affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))).direction =
            ℓ.1.direction :=
        Submodule.eq_of_le_of_finrank_eq
          (AffineSubspace.direction_le line_le)
          (line_rank.trans ℓ.2.2.symm)
      have line_eq :
          affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ.1 :=
        AffineSubspace.ext_of_direction_eq dir_eq
          ⟨p, subset_affineSpan ℝ _ (by simp), hpℓ⟩
      have map_eq : pairLine pq = ℓ := by
        apply Subtype.ext
        exact line_eq
      exact Finset.mem_image.mpr ⟨pq, Finset.mem_attach _ pq, map_eq⟩
  have hLcard_nat : L.card ≤ P.card ^ 2 := by
    calc
      L.card ≤ allLines.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ P.offDiag.attach.card := Finset.card_image_le
      _ = P.offDiag.card := Finset.card_attach
      _ ≤ (P.product P).card := Finset.card_le_card (by
        intro pq hpq
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_offDiag.mp hpq).1, (Finset.mem_offDiag.mp hpq).2.1⟩)
      _ = P.card ^ 2 := by simp [pow_two]
  refine ⟨L, hmem, ?_⟩
  by_cases hL0 : L.card = 0
  · have hnonneg : 0 ≤ C *
        ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          (P.card : ℝ) / (k : ℝ)) := by
      positivity
    simpa [hL0] using hnonneg
  have hL_nat : 0 < L.card := Nat.pos_of_ne_zero hL0
  have hL : 0 < (L.card : ℝ) := by exact_mod_cast hL_nat
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hn : 0 ≤ (P.card : ℝ) := by positivity
  have hcrude : (L.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
    exact_mod_cast hLcard_nat
  have hinc_nat : LineIncidences P L = ∑ ℓ ∈ L,
      (P.filter (fun p => p ∈
        (ℓ.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card := by
    rw [LineIncidences, Finset.card_eq_sum_ones, Finset.sum_filter,
      show P.product L = P ×ˢ L by rfl]
    rw [Finset.sum_product]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hlower_nat : k * L.card ≤ ∑ ℓ ∈ L,
      (P.filter (fun p => p ∈
        (ℓ.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card := by
    calc
      k * L.card = ∑ _ℓ ∈ L, k := by simp [Nat.mul_comm]
      _ ≤ ∑ ℓ ∈ L, (P.filter (fun p => p ∈
          (ℓ.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card :=
        Finset.sum_le_sum (fun ℓ hℓ => (hmem ℓ).mp hℓ)
  have hlower : (k : ℝ) * (L.card : ℝ) ≤ (LineIncidences P L : ℝ) := by
    rw [hinc_nat]
    exact_mod_cast hlower_nat
  have hinc : (k : ℝ) * (L.card : ℝ) ≤
      C₀ * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
        (P.card : ℝ) + (L.card : ℝ)) :=
    hlower.trans (hST P L)
  have hnL_nonneg : 0 ≤ (P.card : ℝ) * (L.card : ℝ) :=
    mul_nonneg hn hL.le
  let m : ℝ := ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)
  have hm : 0 ≤ m := Real.rpow_nonneg hnL_nonneg _
  have hcases :
      (k : ℝ) * (L.card : ℝ) ≤ A * m ∨
      (k : ℝ) * (L.card : ℝ) ≤ A * (P.card : ℝ) ∨
      (k : ℝ) * (L.card : ℝ) ≤ A * (L.card : ℝ) := by
    by_cases h₁ : (k : ℝ) * (L.card : ℝ) ≤ A * m
    · exact Or.inl h₁
    by_cases h₂ : (k : ℝ) * (L.card : ℝ) ≤ A * (P.card : ℝ)
    · exact Or.inr (Or.inl h₂)
    refine Or.inr (Or.inr ?_)
    by_contra h₃
    have h₁' : A * m < (k : ℝ) * (L.card : ℝ) := lt_of_not_ge h₁
    have h₂' : A * (P.card : ℝ) < (k : ℝ) * (L.card : ℝ) :=
      lt_of_not_ge h₂
    have h₃' : A * (L.card : ℝ) < (k : ℝ) * (L.card : ℝ) :=
      lt_of_not_ge h₃
    have hstrict :
        C₀ * (m + (P.card : ℝ) + (L.card : ℝ)) <
          (k : ℝ) * (L.card : ℝ) := by
      dsimp [A] at h₁' h₂' h₃'
      nlinarith
    exact (not_lt_of_ge (hinc.trans_eq (by rfl))) hstrict
  rcases hcases with hmain | hlinear | hline
  · have hm_cube : m ^ (3 : ℕ) =
        ((P.card : ℝ) * (L.card : ℝ)) ^ (2 : ℕ) := by
      dsimp [m]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnL_nonneg]
      norm_num
    have hpow := pow_le_pow_left₀
      (mul_nonneg hk_real.le hL.le) hmain 3
    simp only [mul_pow, hm_cube] at hpow
    have hL_sq_pos : 0 < (L.card : ℝ) ^ 2 := sq_pos_of_pos hL
    have hcancel :
        (k : ℝ) ^ 3 * (L.card : ℝ) ≤ A ^ 3 * (P.card : ℝ) ^ 2 := by
      apply le_of_mul_le_mul_right _ hL_sq_pos
      convert hpow using 1 <;> ring
    have hnum :
        (k : ℝ) ^ 3 * (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 :=
      hcancel.trans (mul_le_mul_of_nonneg_right hC_A3 (sq_nonneg (P.card : ℝ)))
    have hk_cube : 0 < (k : ℝ) ^ 3 := pow_pos hk_real _
    have hquot : (L.card : ℝ) ≤
        C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
      apply (le_div_iff₀ hk_cube).2
      simpa [mul_comm] using hnum
    calc
      (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := hquot
      _ = C * ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3) := by ring
      _ ≤ C * ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          (P.card : ℝ) / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC.le
  · have hk_pos : 0 < (k : ℝ) := hk_real
    have hquot : (L.card : ℝ) ≤ A * (P.card : ℝ) / (k : ℝ) := by
      apply (le_div_iff₀ hk_pos).2
      simpa [mul_comm] using hlinear
    have hquotC : (L.card : ℝ) ≤ C * (P.card : ℝ) / (k : ℝ) :=
      hquot.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC_A hn) hk_real.le)
    calc
      (L.card : ℝ) ≤ C * (P.card : ℝ) / (k : ℝ) := hquotC
      _ = C * ((P.card : ℝ) / (k : ℝ)) := by ring
      _ ≤ C * ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          (P.card : ℝ) / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC.le
  · have hkA : (k : ℝ) ≤ A :=
      le_of_mul_le_mul_right hline hL
    have hkA3 : (k : ℝ) ^ 3 ≤ A ^ 3 :=
      pow_le_pow_left₀ hk_real.le hkA 3
    have hkC : (k : ℝ) ^ 3 ≤ C := hkA3.trans hC_A3
    have hnum :
        (k : ℝ) ^ 3 * (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 := by
      calc
        (k : ℝ) ^ 3 * (L.card : ℝ) ≤
            (k : ℝ) ^ 3 * (P.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hcrude (pow_nonneg hk_real.le _)
        _ ≤ C * (P.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hkC (sq_nonneg (P.card : ℝ))
    have hk_cube : 0 < (k : ℝ) ^ 3 := pow_pos hk_real _
    have hquot : (L.card : ℝ) ≤
        C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
      apply (le_div_iff₀ hk_cube).2
      simpa [mul_comm] using hnum
    calc
      (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := hquot
      _ = C * ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3) := by ring
      _ ≤ C * ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          (P.card : ℝ) / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC.le

theorem globalRichLinesBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ),
        2 ≤ k →
          ∃ L : Finset
              {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ},
            (∀ ℓ, ℓ ∈ L ↔
              k ≤ (P.filter (fun p =>
                p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card) ∧
            (L.card : ℝ) ≤ C *
              ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
                (P.card : ℝ) / (k : ℝ)) := by
  obtain ⟨C₀, hC₀, hST⟩ := SzemerediTrotter
  exact globalRichLinesBound_of_ST C₀ hC₀ hST

end

end Erdos733
