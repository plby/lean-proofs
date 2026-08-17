import ErdosProblems.Erdos49.PrimeSums

/-!
# The three-prime cluster

We cover every three-prime exceptional integer by multiples of a product
`p₃ p₂ p₁`, then use Mertens' theorem twice inside the short multiplicative
prime interval.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

lemma log_log_sub_log_log_le {Y u v K : ℕ}
    (hY : 3 ≤ Y) (hYu : Y ≤ u) (huv : u ≤ v)
    (hK : 1 ≤ K) (hvK : v ≤ u * K) :
    Real.log (Real.log (v : ℝ)) -
      Real.log (Real.log ((u - 1 : ℕ) : ℝ)) ≤
        Real.log (2 * K : ℕ) / Real.log (Y - 1 : ℕ) := by
  have hu3 : 3 ≤ u := hY.trans hYu
  have hu1 : 0 < (u - 1 : ℕ) := by omega
  have hY1 : 0 < (Y - 1 : ℕ) := by omega
  have hvpos : 0 < v := by omega
  have hlogu : 0 < Real.log ((u - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < u - 1 by omega))
  have hlogY : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  have hlogv : 0 < Real.log (v : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < v by omega))
  have h2K : (1 : ℝ) ≤ (2 * K : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * K)
  have hlog2K : 0 ≤ Real.log ((2 * K : ℕ) : ℝ) := Real.log_nonneg h2K
  have huTwo : u ≤ 2 * (u - 1) := by omega
  have hvReal : (v : ℝ) ≤ (u - 1 : ℕ) * (2 * K : ℕ) := by
    exact_mod_cast hvK.trans (Nat.mul_le_mul_right K huTwo) |>.trans_eq (by ring)
  have hlogvUpper : Real.log (v : ℝ) ≤
      Real.log ((u - 1 : ℕ) : ℝ) + Real.log ((2 * K : ℕ) : ℝ) := by
    calc
      Real.log (v : ℝ) ≤ Real.log (((u - 1 : ℕ) : ℝ) * (2 * K : ℕ)) :=
        Real.log_le_log (by positivity) hvReal
      _ = Real.log ((u - 1 : ℕ) : ℝ) + Real.log ((2 * K : ℕ) : ℝ) := by
        rw [Real.log_mul (by positivity : (((u - 1 : ℕ) : ℝ) ≠ 0))
          (by positivity : (((2 * K : ℕ) : ℝ) ≠ 0))]
  have hratioPos : 0 < Real.log (v : ℝ) / Real.log ((u - 1 : ℕ) : ℝ) :=
    div_pos hlogv hlogu
  have hlogRatio :
      Real.log (Real.log (v : ℝ)) -
          Real.log (Real.log ((u - 1 : ℕ) : ℝ)) =
        Real.log (Real.log (v : ℝ) / Real.log ((u - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hlogv.ne' hlogu.ne']
  rw [hlogRatio]
  apply (Real.log_le_sub_one_of_pos hratioPos).trans
  have hratio : Real.log (v : ℝ) / Real.log ((u - 1 : ℕ) : ℝ) - 1 ≤
      Real.log ((2 * K : ℕ) : ℝ) / Real.log ((u - 1 : ℕ) : ℝ) := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hlogu).2
    calc
      Real.log (v : ℝ) ≤ Real.log ((u - 1 : ℕ) : ℝ) +
          Real.log ((2 * K : ℕ) : ℝ) := hlogvUpper
      _ = (Real.log ((2 * K : ℕ) : ℝ) /
            Real.log ((u - 1 : ℕ) : ℝ) + 1) *
          Real.log ((u - 1 : ℕ) : ℝ) := by
        field_simp
        ring
  apply hratio.trans
  apply div_le_div_of_nonneg_left hlog2K hlogY
  apply Real.log_le_log
  · positivity
  · exact_mod_cast (by omega : Y - 1 ≤ u - 1)

lemma primeReciprocalInterval_scaled_upper {Y u v K : ℕ}
    (hY : 3 ≤ Y) (hYu : Y ≤ u) (huv : u ≤ v)
    (hK : 1 ≤ K) (hvK : v ≤ u * K) :
    primeReciprocalInterval u v ≤
      (Real.log (2 * K : ℕ) + 2 * mertensReciprocalError) /
        Real.log (Y - 1 : ℕ) := by
  have hbase := primeReciprocalInterval_upper (hY.trans hYu) huv
  have hlogdiff := log_log_sub_log_log_le hY hYu huv hK hvK
  have hlogY : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  have hlogmono : Real.log (Y - 1 : ℕ) ≤ Real.log (u - 1 : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Y - 1 by omega)
    · exact_mod_cast (by omega : Y - 1 ≤ u - 1)
  have herr : 2 * mertensReciprocalError / Real.log (u - 1 : ℕ) ≤
      2 * mertensReciprocalError / Real.log (Y - 1 : ℕ) := by
    apply div_le_div_of_nonneg_left
    · positivity [mertensReciprocalError_nonneg]
    · exact hlogY
    · exact hlogmono
  calc
    primeReciprocalInterval u v ≤
        (Real.log (Real.log (v : ℝ)) -
          Real.log (Real.log ((u - 1 : ℕ) : ℝ))) +
          2 * mertensReciprocalError / Real.log (u - 1 : ℕ) := hbase
    _ ≤ Real.log (2 * K : ℕ) / Real.log (Y - 1 : ℕ) +
          2 * mertensReciprocalError / Real.log (Y - 1 : ℕ) :=
      add_le_add hlogdiff herr
    _ = (Real.log (2 * K : ℕ) + 2 * mertensReciprocalError) /
          Real.log (Y - 1 : ℕ) := by ring

def tripleClusterCover (N L R : ℕ) : Finset ℕ :=
  let Y := R / L ^ 2
  (Analytic.primeInterval (Y + 1) N).biUnion fun p₃ ↦
    (Analytic.primeInterval p₃ (min N (p₃ * L ^ 2))).biUnion fun p₂ ↦
      (Analytic.primeInterval p₂ (min N (p₃ * L ^ 2))).biUnion fun p₁ ↦
        multiplesUpTo N (p₃ * p₂ * p₁)

lemma tripleExceptional_subset_cover {N L R : ℕ} (hL : 0 < L) :
    tripleExceptional N L R ⊆ tripleClusterCover N L R := by
  intro n hn
  have hndata := Finset.mem_filter.mp hn
  rcases hndata.2 with
    ⟨d, p₃, p₂, p₁, hd, hp₃, hp₂, hp₁, hR, hp₃p₂, hp₂p₁, hp₁max, hnfac⟩
  have hnN := (Finset.mem_Icc.mp hndata.1).2
  have hp₁N : p₁ ≤ N := by
    have : p₁ ≤ n := by
      rw [hnfac]
      exact Nat.le_mul_of_pos_left p₁
        (Nat.mul_pos (Nat.mul_pos hd hp₃.pos) hp₂.pos)
    exact this.trans hnN
  have hp₂N : p₂ ≤ N := hp₂p₁.trans hp₁N
  have hp₃N : p₃ ≤ N := hp₃p₂.trans hp₂N
  have hYp₃ : R / L ^ 2 < p₃ := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < L ^ 2)).2
    simpa [mul_comm] using hR
  have hprodDvd : p₃ * p₂ * p₁ ∣ n := by
    refine ⟨d, ?_⟩
    rw [hnfac]
    ring
  unfold tripleClusterCover
  dsimp only
  apply Finset.mem_biUnion.mpr
  refine ⟨p₃, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, hp₃N⟩, hp₃⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨p₂, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp₃p₂, le_min hp₂N (hp₂p₁.trans hp₁max)⟩, hp₂⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨p₁, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp₂p₁, le_min hp₁N hp₁max⟩, hp₁⟩, ?_⟩
  exact mem_multiplesUpTo.mpr
    ⟨(Finset.mem_Icc.mp hndata.1).1, hnN, hprodDvd⟩

def tripleInnerBound (L Y : ℕ) : ℝ :=
  (Real.log (2 * L ^ 2 : ℕ) + 2 * mertensReciprocalError) /
    Real.log (Y - 1 : ℕ)

theorem tripleExceptional_card_real_le
    {N L R Y : ℕ} (hL : 0 < L) (hYdef : Y = R / L ^ 2)
    (hY : 3 ≤ Y) :
    ((tripleExceptional N L R).card : ℝ) ≤
      (N : ℝ) * primeReciprocalInterval (Y + 1) N *
        tripleInnerBound L Y ^ 2 := by
  have hsubset := tripleExceptional_subset_cover (N := N) (L := L) (R := R) hL
  have hcover : ((tripleClusterCover N L R).card : ℝ) ≤
      (N : ℝ) * primeReciprocalInterval (Y + 1) N *
        tripleInnerBound L Y ^ 2 := by
    unfold tripleClusterCover
    rw [← hYdef]
    calc
      (((Analytic.primeInterval (Y + 1) N).biUnion fun p₃ ↦
        (Analytic.primeInterval p₃ (min N (p₃ * L ^ 2))).biUnion fun p₂ ↦
          (Analytic.primeInterval p₂ (min N (p₃ * L ^ 2))).biUnion fun p₁ ↦
            multiplesUpTo N (p₃ * p₂ * p₁)).card : ℝ) ≤
          ∑ p₃ ∈ Analytic.primeInterval (Y + 1) N,
            ∑ p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
              ∑ p₁ ∈ Analytic.primeInterval p₂ (min N (p₃ * L ^ 2)),
                ((N / (p₃ * p₂ * p₁) : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun p₃ hp₃ ↦ Finset.card_biUnion_le.trans
            (Finset.sum_le_sum fun p₂ hp₂ ↦ Finset.card_biUnion_le.trans
              (Finset.sum_le_sum fun p₁ hp₁ ↦
                multiplesUpTo_card_le N (p₃ * p₂ * p₁))))
      _ ≤ ∑ p₃ ∈ Analytic.primeInterval (Y + 1) N,
          (N : ℝ) * ((1 : ℝ) / p₃) *
            primeReciprocalInterval p₃ (min N (p₃ * L ^ 2)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p₃ hp₃
        calc
          (∑ p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
            ∑ p₁ ∈ Analytic.primeInterval p₂ (min N (p₃ * L ^ 2)),
              ((N / (p₃ * p₂ * p₁) : ℕ) : ℝ)) ≤
              ∑ p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
                ∑ p₁ ∈ Analytic.primeInterval p₂ (min N (p₃ * L ^ 2)),
                  (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁) := by
            apply Finset.sum_le_sum
            intro p₂ hp₂
            apply Finset.sum_le_sum
            intro p₁ hp₁
            calc
              ((N / (p₃ * p₂ * p₁) : ℕ) : ℝ) ≤
                  (N : ℝ) / (p₃ * p₂ * p₁ : ℕ) := Nat.cast_div_le
              _ = (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁) := by
                push_cast
                ring
          _ ≤ (N : ℝ) * (1 / p₃) *
              primeReciprocalInterval p₃ (min N (p₃ * L ^ 2)) ^ 2 := by
            unfold primeReciprocalInterval
            have hsub (p₂ : ℕ)
                (hp₂ : p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2))) :
                Analytic.primeInterval p₂ (min N (p₃ * L ^ 2)) ⊆
                  Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)) := by
              intro p₁ hp₁
              have h₁ := Finset.mem_filter.mp hp₁
              have h₂ := Finset.mem_filter.mp hp₂
              have h₁I := Finset.mem_Icc.mp h₁.1
              have h₂I := Finset.mem_Icc.mp h₂.1
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr
                  ⟨h₂I.1.trans h₁I.1, h₁I.2⟩, h₁.2⟩
            calc
              (∑ p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
                ∑ p₁ ∈ Analytic.primeInterval p₂ (min N (p₃ * L ^ 2)),
                  (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁)) ≤
                  ∑ p₂ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
                    ∑ p₁ ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
                      (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁) := by
                apply Finset.sum_le_sum
                intro p₂ hp₂
                apply Finset.sum_le_sum_of_subset_of_nonneg (hsub p₂ hp₂)
                intro p₁ hp₁ hnot
                positivity
              _ = (N : ℝ) * (1 / p₃) *
                  (∑ p ∈ Analytic.primeInterval p₃ (min N (p₃ * L ^ 2)),
                    (1 : ℝ) / p) ^ 2 := by
                let S := Analytic.primeInterval p₃ (min N (p₃ * L ^ 2))
                have hfactor :
                    (∑ p₂ ∈ S, ∑ p₁ ∈ S,
                    (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁)) =
                      (N : ℝ) * (1 / p₃) *
                        (∑ p₂ ∈ S, (1 : ℝ) / p₂) *
                        (∑ p₁ ∈ S, (1 : ℝ) / p₁) := by
                  calc
                    (∑ p₂ ∈ S, ∑ p₁ ∈ S,
                      (N : ℝ) * (1 / p₃) * (1 / p₂) * (1 / p₁)) =
                      ∑ p₂ ∈ S, ((N : ℝ) * (1 / p₃) * (1 / p₂)) *
                        (∑ p₁ ∈ S, (1 : ℝ) / p₁) := by
                      apply Finset.sum_congr rfl
                      intro p₂ hp₂
                      rw [Finset.mul_sum]
                    _ = (N : ℝ) * (1 / p₃) *
                        (∑ p₂ ∈ S, (1 : ℝ) / p₂) *
                        (∑ p₁ ∈ S, (1 : ℝ) / p₁) := by
                      rw [← Finset.sum_mul, ← Finset.mul_sum]
                simpa only [S, pow_two, mul_assoc] using hfactor
      _ ≤ ∑ p₃ ∈ Analytic.primeInterval (Y + 1) N,
          (N : ℝ) * ((1 : ℝ) / p₃) * tripleInnerBound L Y ^ 2 := by
        apply Finset.sum_le_sum
        intro p₃ hp₃
        have hp₃data := Finset.mem_filter.mp hp₃
        have hp₃I := Finset.mem_Icc.mp hp₃data.1
        have hYp₃ : Y ≤ p₃ := by omega
        have hv : p₃ ≤ min N (p₃ * L ^ 2) := by
          apply le_min hp₃I.2
          exact Nat.le_mul_of_pos_right p₃ (by positivity : 0 < L ^ 2)
        have hLpow : 1 ≤ L ^ 2 := by
          have : 1 ≤ L := by omega
          exact pow_le_pow_left' this 2
        have hinner := primeReciprocalInterval_scaled_upper
          hY hYp₃ hv hLpow (min_le_right _ _)
        unfold tripleInnerBound
        have hsumNonneg : 0 ≤
            primeReciprocalInterval p₃ (min N (p₃ * L ^ 2)) := by
          unfold primeReciprocalInterval
          positivity
        have hboundNonneg : 0 ≤
            (Real.log (2 * L ^ 2 : ℕ) + 2 * mertensReciprocalError) /
              Real.log (Y - 1 : ℕ) := hsumNonneg.trans hinner
        have hsquare := pow_le_pow_left₀ hsumNonneg hinner 2
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (N : ℝ) * primeReciprocalInterval (Y + 1) N *
          tripleInnerBound L Y ^ 2 := by
        unfold primeReciprocalInterval
        calc
          (∑ p ∈ Analytic.primeInterval (Y + 1) N,
              (N : ℝ) * (1 / (p : ℝ)) * tripleInnerBound L Y ^ 2) =
              (∑ p ∈ Analytic.primeInterval (Y + 1) N,
                (N : ℝ) * (1 / (p : ℝ))) * tripleInnerBound L Y ^ 2 := by
                rw [Finset.sum_mul]
          _ = (N : ℝ) *
                (∑ p ∈ Analytic.primeInterval (Y + 1) N, (1 : ℝ) / p) *
                tripleInnerBound L Y ^ 2 := by
                rw [Finset.mul_sum]
  have hcard : ((tripleExceptional N L R).card : ℝ) ≤
      (tripleClusterCover N L R).card := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans hcover

#print axioms tripleExceptional_card_real_le

end

end Erdos49
