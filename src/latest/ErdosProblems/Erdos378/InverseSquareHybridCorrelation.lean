/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareCentralCorrelation

/-!
# Hybrid close/separated inverse-square correlations

For an inverse-square phase, neighboring bilinear columns can have almost
the same phase.  They are counted trivially; only pairs farther than a
chosen distance use the high-derivative correlation estimate.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareHybridCorrelation

open InverseSquareCorrelation
open InverseSquareBilinear
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation

noncomputable section

def natDist (r s : ℕ) : ℕ := (r - s) + (s - r)

lemma natDist_comm (r s : ℕ) : natDist r s = natDist s r := by
  unfold natDist
  omega

lemma card_filter_natDist_le (t : Finset ℕ) (r D : ℕ) :
    (t.filter fun s ↦ natDist r s ≤ D).card ≤ 2 * D + 1 := by
  let u := (t.filter fun s ↦ natDist r s ≤ D).image fun s ↦ D + s - r
  have hinj : Set.InjOn (fun s : ℕ ↦ D + s - r)
      ((t.filter fun s ↦ natDist r s ≤ D) : Set ℕ) := by
    intro a ha b hb hab
    have haD := (Finset.mem_filter.mp ha).2
    have hbD := (Finset.mem_filter.mp hb).2
    unfold natDist at haD hbD
    have har : r ≤ D + a := by omega
    have hbr : r ≤ D + b := by omega
    have hab' := congrArg (fun z : ℕ ↦ z + r) hab
    rw [Nat.sub_add_cancel har, Nat.sub_add_cancel hbr] at hab'
    omega
  have husub : u ⊆ Finset.range (2 * D + 1) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    have hsD := (Finset.mem_filter.mp hs).2
    rw [Finset.mem_range]
    unfold natDist at hsD
    omega
  calc
    _ = u.card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (2 * D + 1)).card := Finset.card_le_card husub
    _ = 2 * D + 1 := Finset.card_range _

/-- The total coefficient mass of ordered close pairs is controlled by the
number of possible neighboring offsets and the `ℓ²` mass. -/
lemma sum_close_mul_le (t : Finset ℕ) (b : ℕ → ℝ) (D : ℕ)
    (_hb : ∀ k ∈ t, 0 ≤ b k) :
    (∑ r ∈ t, ∑ s ∈ t,
        if natDist r s ≤ D then b r * b s else 0) ≤
      ((2 * D + 1 : ℕ) : ℝ) * ∑ k ∈ t, (b k) ^ 2 := by
  have hamgm (r : ℕ) (hr : r ∈ t) (s : ℕ) (hs : s ∈ t) :
      b r * b s ≤ ((b r) ^ 2 + (b s) ^ 2) / 2 := by
    nlinarith [sq_nonneg (b r - b s)]
  calc
    _ ≤ ∑ r ∈ t, ∑ s ∈ t,
        if natDist r s ≤ D then ((b r) ^ 2 + (b s) ^ 2) / 2 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      split_ifs
      · exact hamgm r hr s hs
      · exact le_rfl
    _ = (∑ r ∈ t, ∑ s ∈ t,
          if natDist r s ≤ D then (b r) ^ 2 / 2 else 0) +
        (∑ r ∈ t, ∑ s ∈ t,
          if natDist r s ≤ D then (b s) ^ 2 / 2 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> ring
    _ = 2 * (∑ r ∈ t, ∑ s ∈ t,
          if natDist r s ≤ D then (b r) ^ 2 / 2 else 0) := by
      have hswap :
          (∑ r ∈ t, ∑ s ∈ t,
            if natDist r s ≤ D then (b s) ^ 2 / 2 else 0) =
          ∑ r ∈ t, ∑ s ∈ t,
            if natDist r s ≤ D then (b r) ^ 2 / 2 else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [natDist_comm]
      rw [hswap]
      ring
    _ ≤ 2 * (((2 * D + 1 : ℕ) : ℝ) / 2 *
          ∑ r ∈ t, (b r) ^ 2) := by
      gcongr
      calc
        (∑ r ∈ t, ∑ s ∈ t,
            if natDist r s ≤ D then (b r) ^ 2 / 2 else 0) =
            ∑ r ∈ t,
              (((t.filter fun s ↦ natDist r s ≤ D).card : ℕ) : ℝ) *
                ((b r) ^ 2 / 2) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← Finset.sum_filter]
          simp
        _ ≤ ∑ r ∈ t,
            (((2 * D + 1 : ℕ) : ℝ) * ((b r) ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro r hr
          gcongr
          exact_mod_cast card_filter_natDist_le t r D
        _ = (((2 * D + 1 : ℕ) : ℝ) / 2) *
            ∑ r ∈ t, (b r) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = _ := by ring

/-- Cauchy--Schwarz energy estimate which treats pairs at distance at most
`D` trivially and applies a common envelope only to separated pairs. -/
theorem norm_inverseSquareCentral_bilinearBlock_sq_le_hybrid
    {X : ℝ} {x y M K C D : ℕ} (a b : ℕ → ℂ)
    (hX : 0 < X) (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : inverseSquareCentralCorrelationSizeCondition M)
    (hC : 2 ≤ C) (hbaseCap : AdaptiveShifts.baseShift M ≤ M / C)
    (B : ℝ) (hB : 0 ≤ B)
    (hcorr : ∀ r ∈ Finset.Ioc K (2 * K),
      ∀ s ∈ Finset.Ioc K (2 * K),
      r < s → D < s - r →
        ‖∑ m ∈ Finset.Ioc M (2 * M),
          inverseSquareCutoffWeight X x y m s *
            conj (inverseSquareCutoffWeight X x y m r)‖ ≤ B) :
    ‖inverseSquareBilinearBlock X x y M (2 * M) K (2 * K) a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        (((M : ℝ) * ((2 * D + 1 : ℕ) : ℝ) + B * (K : ℝ)) *
          (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖ ^ 2)) := by
  let t := Finset.Ioc K (2 * K)
  have hbase := norm_inverseSquareBilinearBlock_sq_le_correlation
    X x y M (2 * M) K (2 * K) a b
  have hpair :
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            inverseSquareCutoffWeight X x y m s *
              conj (inverseSquareCutoffWeight X x y m r)‖) ≤
        ((M : ℝ) * ((2 * D + 1 : ℕ) : ℝ) + B * (K : ℝ)) *
          (∑ k ∈ t, ‖b k‖ ^ 2) := by
    calc
      _ ≤ ∑ r ∈ t, ∑ s ∈ t,
          ((if natDist r s ≤ D then ‖b r‖ * ‖b s‖ * (M : ℝ) else 0) +
            ‖b r‖ * ‖b s‖ * B) := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro s hs
        by_cases hclose : natDist r s ≤ D
        · simp only [hclose, if_true]
          have htriv := norm_sum_inverseSquareCutoffWeight_correlation_le_commonLength
            (x := x) (y := y) (m₀ := M) (m₁ := 2 * M)
            (k₁ := s) (k₂ := r) X
              (hK.trans (Finset.mem_Ioc.mp hs).1)
              (hK.trans (Finset.mem_Ioc.mp hr).1)
          have htriv' :
              ‖∑ m ∈ Finset.Ioc M (2 * M),
                inverseSquareCutoffWeight X x y m s *
                  conj (inverseSquareCutoffWeight X x y m r)‖ ≤ (M : ℝ) := by
            have hlen :
                min (2 * M) (min (y / s) (y / r)) -
                    max M (max (x / s) (x / r)) ≤ M := by
              have hu : min (2 * M) (min (y / s) (y / r)) ≤ 2 * M :=
                Nat.min_le_left _ _
              have hl : M ≤ max M (max (x / s) (x / r)) :=
                Nat.le_max_left _ _
              omega
            exact htriv.trans (by exact_mod_cast hlen)
          exact (mul_le_mul_of_nonneg_left htriv' (by positivity)).trans
            (le_add_of_nonneg_right (by positivity))
        · simp only [hclose, if_false, zero_add]
          have hne : r ≠ s := by
            intro hrs
            subst s
            simp [natDist] at hclose
          rcases lt_or_gt_of_ne hne with hrs | hsr
          · have hfar : D < s - r := by
              unfold natDist at hclose
              omega
            exact mul_le_mul_of_nonneg_left
              (hcorr r hr s hs hrs hfar) (by positivity)
          · have hfar : D < r - s := by
              unfold natDist at hclose
              omega
            rw [norm_sum_inverseSquareCutoffWeight_correlation_comm
              X x y M (2 * M) s r]
            exact mul_le_mul_of_nonneg_left
              (hcorr s hs r hr hsr hfar) (by positivity)
      _ = (M : ℝ) *
            (∑ r ∈ t, ∑ s ∈ t,
              if natDist r s ≤ D then ‖b r‖ * ‖b s‖ else 0) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          split_ifs <;> ring
        · rw [pow_two]
          calc
            (∑ r ∈ t, ∑ s ∈ t, ‖b r‖ * ‖b s‖ * B) =
                ∑ r ∈ t, ‖b r‖ * (∑ s ∈ t, ‖b s‖) * B := by
              apply Finset.sum_congr rfl
              intro r hr
              rw [← Finset.sum_mul, ← Finset.mul_sum]
            _ = (∑ r ∈ t, ‖b r‖) * (∑ s ∈ t, ‖b s‖) * B := by
              calc
                (∑ r ∈ t, ‖b r‖ * (∑ s ∈ t, ‖b s‖) * B) =
                    ∑ r ∈ t, ‖b r‖ * ((∑ s ∈ t, ‖b s‖) * B) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  ring
                _ = (∑ r ∈ t, ‖b r‖) * ((∑ s ∈ t, ‖b s‖) * B) := by
                  rw [← Finset.sum_mul]
                _ = (∑ r ∈ t, ‖b r‖) * (∑ s ∈ t, ‖b s‖) * B := by
                  ring
            _ = B * ((∑ k ∈ t, ‖b k‖) * (∑ k ∈ t, ‖b k‖)) := by ring
      _ ≤ (M : ℝ) *
            (((2 * D + 1 : ℕ) : ℝ) * ∑ k ∈ t, ‖b k‖ ^ 2) +
          B * ((K : ℝ) * ∑ k ∈ t, ‖b k‖ ^ 2) := by
        apply add_le_add
        · gcongr
          exact sum_close_mul_le t (fun k ↦ ‖b k‖) D
            (fun k hk ↦ norm_nonneg _)
        · gcongr
          have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq t
            (fun _k : ℕ ↦ (1 : ℝ)) (fun k ↦ ‖b k‖)
          have hcard : t.card = K := by
            dsimp only [t]
            simp only [Nat.card_Ioc]
            omega
          simpa [hcard] using hcauchy
      _ = ((M : ℝ) * ((2 * D + 1 : ℕ) : ℝ) + B * (K : ℝ)) *
            (∑ k ∈ t, ‖b k‖ ^ 2) := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_left hpair
    (Finset.sum_nonneg fun m hm ↦ sq_nonneg _))

end

end InverseSquareHybridCorrelation
end Erdos378
