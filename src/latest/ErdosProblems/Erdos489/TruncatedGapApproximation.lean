import ErdosProblems.Erdos489.TruncatedGapCost
import ErdosProblems.Erdos489.FiniteSieveApproximation
import ErdosProblems.Erdos489.PeriodicAverage
import ErdosProblems.Erdos489.CountShift
import ErdosProblems.Erdos489.TailMass
import ErdosProblems.Erdos489.UniformApproximation

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- If two bounded nonnegative costs agree off `B`, their total sums differ by
at most `#B` times the common bound. -/
theorem abs_cast_sum_sub_sum_le_card_mul
    (S B : Finset ℕ) (f g : ℕ → ℕ) (K : ℕ)
    (hBS : B ⊆ S)
    (hf : ∀ n ∈ B, f n ≤ K) (hg : ∀ n ∈ B, g n ≤ K)
    (heq : ∀ n ∈ S, n ∉ B → f n = g n) :
    |((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ)| ≤
      (B.card : ℝ) * (K : ℝ) := by
  have hoff : (∑ n ∈ S \ B, f n) = ∑ n ∈ S \ B, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact heq n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2
  have hfs := Finset.sum_sdiff hBS (f := f)
  have hgs := Finset.sum_sdiff hBS (f := g)
  have hfb : ∑ n ∈ B, f n ≤ B.card * K := by
    calc
      ∑ n ∈ B, f n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hf
      _ = B.card * K := by simp
  have hgb : ∑ n ∈ B, g n ≤ B.card * K := by
    calc
      ∑ n ∈ B, g n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hg
      _ = B.card * K := by simp
  have hfbR : ((∑ n ∈ B, f n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hfb
  have hgbR : ((∑ n ∈ B, g n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hgb
  have hfsR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) +
      ((∑ n ∈ B, f n : ℕ) : ℝ) = ((∑ n ∈ S, f n : ℕ) : ℝ) := by
    exact_mod_cast hfs
  have hgsR : ((∑ n ∈ S \ B, g n : ℕ) : ℝ) +
      ((∑ n ∈ B, g n : ℕ) : ℝ) = ((∑ n ∈ S, g n : ℕ) : ℝ) := by
    exact_mod_cast hgs
  have hoffR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) =
      ((∑ n ∈ S \ B, g n : ℕ) : ℝ) := by exact_mod_cast hoff
  have heqR : ((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ) =
      ((∑ n ∈ B, f n : ℕ) : ℝ) - ((∑ n ∈ B, g n : ℕ) : ℝ) := by
    linarith
  rw [heqR, abs_le]
  have hfn : (0 : ℝ) ≤ ((∑ n ∈ B, f n : ℕ) : ℝ) := by positivity
  have hgn : (0 : ℝ) ≤ ((∑ n ∈ B, g n : ℕ) : ℝ) := by positivity
  constructor <;> linarith

noncomputable def fullTruncatedGapAverage
    (p : ℕ → Prop) (H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapAverage
    (p : ℕ → Prop) (R H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapLimit
    (p : ℕ → Prop) (R H : ℕ) : ℝ :=
  let P := ((List.range R).map (Nat.nth p)).prod
  ((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)

 theorem finiteTruncatedGapAverage_tendsto
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (R H : ℕ) :
    Tendsto (finiteTruncatedGapAverage p R H) atTop
      (𝓝 (finiteTruncatedGapLimit p R H)) := by
  let P := ((List.range R).map (Nat.nth p)).prod
  have hP : 0 < P := by
    apply List.prod_pos
    intro a ha
    rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hper := truncatedGapCost_periodic (finiteDivisorSifted p R) H P
    (finiteDivisorSifted_periodic p R)
  change Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))
    atTop (𝓝 (((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)))
  simpa only [Nat.cast_sum] using
    tendsto_periodic_nat_average
      (truncatedGapCost (finiteDivisorSifted p R) H) P hP hper

 theorem full_finite_truncated_sum_difference
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R H x : ℕ) :
    |((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
      ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := by
  classical
  apply abs_cast_sum_sub_sum_le_card_mul
    (Finset.range x) (badGapStarts p R H x)
  · exact badGapStarts_subset_range p R H x
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hnx hgood
    apply truncatedGapCost_eq_of_window_agree
    exact sieve_window_agree_of_not_bad p hp R H x n
      (Finset.mem_range.mp hnx) hgood

/-- For every fixed gap cutoff, one finite periodic prefix eventually
approximates the full truncated-gap average arbitrarily well. -/
theorem exists_prefix_eventually_full_finite_close
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R, ∀ᶠ x : ℕ in atTop,
      |fullTruncatedGapAverage p H x - finiteTruncatedGapAverage p R H x| < ε := by
  classical
  by_cases hH : H = 0
  · subst H
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro x
    simp [fullTruncatedGapAverage, finiteTruncatedGapAverage,
      truncatedGapCost, hε]
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let K : ℕ := (H + 1) * H ^ 3
    have hK : 0 < K := by dsimp [K]; positivity
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    let δ : ℝ := ε / (4 * (K : ℝ))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have htailEv := eventually_finset_tail_sum_le_of_summable
      (fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹)) hsum
      (fun r => inv_nonneg.mpr (by positivity)) δ hδ
    obtain ⟨R, htail, hR⟩ :=
      Filter.Eventually.exists (htailEv.and (eventually_ge_atTop 1))
    have hRpos : 0 < R := by omega
    have hMlim : Tendsto
        (fun x : ℕ => (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)))
        atTop (𝓝 1) := by
      have ht := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
        ((H + 1 : ℕ) : ℝ) 0 1 (d := 1) (by norm_num)
      simpa [Nat.cast_add, add_comm] using ht
    have hM2 : ∀ᶠ x : ℕ in atTop,
        (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)) < 2 :=
      (tendsto_order.1 hMlim).2 2 (by norm_num)
    have hClim := tendsto_count_add_div p hcount (H + 1)
    have hsmallPos : 0 < ε / (2 * (K : ℝ)) := by positivity
    have hCsmall : ∀ᶠ x : ℕ in atTop,
        (Nat.count p (x + (H + 1)) : ℝ) / (x : ℝ) <
          ε / (2 * (K : ℝ)) :=
      (tendsto_order.1 hClim).2 _ hsmallPos
    refine ⟨R, ?_⟩
    filter_upwards [hM2, hCsmall, eventually_ge_atTop 1] with x hxM hxC hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    let M : ℕ := x + H + 1
    have hMeq : M = x + (H + 1) := by dsimp [M]; omega
    have hbad := badGapStarts_card_le p R H x
    have hmis := sieveMismatch_card_cast_le p hp hp2 R M hRpos δ htail
    have hnum0 := full_finite_truncated_sum_difference p hp R H x
    have hbadR : ((badGapStarts p R H x).card : ℝ) ≤
        ((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
      exact_mod_cast (by simpa [M] using hbad)
    have hnum :
        |((∑ n ∈ Finset.range x,
            truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
          ((∑ n ∈ Finset.range x,
            truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
        (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
      calc
        _ ≤ ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := hnum0
        _ ≤ (((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ)) *
              (H ^ 3 : ℕ) := by gcongr
        _ = (K : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
          dsimp [K]
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
          ring
        _ ≤ (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmis hKR.le
    change |(((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) / (x : ℝ)) -
      (((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))| < ε
    rw [← sub_div, abs_div, abs_of_pos hxR]
    calc
      _ ≤ ((K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ))) / (x : ℝ) :=
        div_le_div_of_nonneg_right hnum hxR.le
      _ = (K : ℝ) *
          ((((M : ℝ) / (x : ℝ)) * δ) +
            ((Nat.count p M : ℝ) / (x : ℝ))) := by field_simp
      _ < ε := by
        have hxM' : (M : ℝ) / (x : ℝ) < 2 := by simpa [hMeq] using hxM
        have hxC' : (Nat.count p M : ℝ) / (x : ℝ) <
            ε / (2 * (K : ℝ)) := by simpa [hMeq] using hxC
        have hpart1 : (K : ℝ) * (((M : ℝ) / (x : ℝ)) * δ) < ε / 2 := by
          have hm := mul_lt_mul_of_pos_right hxM' hδ
          dsimp [δ] at hm ⊢
          have hfour : (0 : ℝ) < 4 * K := by positivity
          calc
            (K : ℝ) * ((M : ℝ) / (x : ℝ) * (ε / (4 * K))) <
                (K : ℝ) * (2 * (ε / (4 * K))) :=
              mul_lt_mul_of_pos_left hm hKR
            _ = ε / 2 := by field_simp; ring
        have hpart2 : (K : ℝ) * ((Nat.count p M : ℝ) / (x : ℝ)) < ε / 2 := by
          calc
            _ < (K : ℝ) * (ε / (2 * (K : ℝ))) :=
              mul_lt_mul_of_pos_left hxC' hKR
            _ = ε / 2 := by field_simp
        nlinarith

/-- Consequently, the normalized squared-gap contribution from gaps below
any fixed cutoff has a finite limit. -/
theorem exists_fullTruncatedGapAverage_limit
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) :
    ∃ L : ℝ, Tendsto (fullTruncatedGapAverage p H) atTop (𝓝 L) := by
  apply exists_tendsto_of_uniform_eventual_approx
    (fullTruncatedGapAverage p H)
    (fun R => finiteTruncatedGapAverage p R H)
  · intro ε hε
    exact exists_prefix_eventually_full_finite_close
      p hp hp2 hcount hsum H ε hε
  · intro R
    exact ⟨finiteTruncatedGapLimit p R H,
      finiteTruncatedGapAverage_tendsto p hp hp2 R H⟩

end Erdos489
