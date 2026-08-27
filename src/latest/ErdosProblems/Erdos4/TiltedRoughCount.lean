import ErdosProblems.Erdos4.TiltedTargets
import ErdosProblems.Erdos4.SelbergHarmonicMass
import ErdosProblems.Erdos4.FGKMTQuantitativeTail

/-!
# Rough-number bounds needed by the covering construction

The upper bound follows from the already optimized Selberg square
majorant. A lower asymptotic for the number of composites is unnecessary:
if that target set is small, its surviving members go directly to cleanup.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open SieveMajorant SelbergCoefficients SelbergOptimization

theorem small_divisor_of_rough {w n d : ℕ} (hrough : IsRough w n)
    (hd : 1 ≤ d) (hdw : d ≤ w) (hdn : d ∣ n) : d = 1 := by
  by_contra hd1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpn := hpd.trans hdn
  exact (not_lt_of_ge ((Nat.le_of_dvd hd hpd).trans hdw)) (hrough p hp hpn)

theorem amplitude_rough {w n : ℕ} (hw : 1 ≤ w) (hrough : IsRough w n) (coeff : ℕ → ℝ) :
    amplitude w coeff n = coeff 1 := by
  have hterm : ∀ d ∈ Finset.Icc 1 w,
      (if d ∣ n then coeff d else 0) = if d = 1 then coeff 1 else 0 := by
    intro d hd
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hnot : ¬d ∣ n := fun h => hd1 (small_divisor_of_rough hrough
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 h)
      simp [hnot, hd1]
  unfold amplitude
  rw [Finset.sum_congr rfl hterm]
  simp [hw]

noncomputable def roughIntegers (Y w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter (IsRough w)

theorem roughIntegers_card_le {w : ℕ} (hw : 1 ≤ w) (Y : ℕ) :
    ((roughIntegers Y w).card : ℝ) ≤ (Y : ℝ) / harmonicMass w + (w : ℝ) ^ 4 := by
  classical
  have hweight : ∀ n ∈ roughIntegers Y w, weight w (coefficient w) n = 1 := by
    intro n hn
    rw [weight, amplitude_rough hw (Finset.mem_filter.mp hn).2, coefficient_one hw, one_pow]
  calc
    _ = ∑ _n ∈ roughIntegers Y w, (1 : ℝ) := by simp
    _ = ∑ n ∈ roughIntegers Y w, weight w (coefficient w) n :=
      Finset.sum_congr rfl (fun n hn => (hweight n hn).symm)
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, weight w (coefficient w) n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => weight_nonneg _ _ n)
    _ ≤ _ := sum_weight_coefficient_le hw Y

open Filter in
theorem eventually_roughIntegers_card_le :
    ∀ᶠ w : ℕ in atTop, ∀ Y : ℕ,
      ((roughIntegers Y w).card : ℝ) ≤ 2 * (Y : ℝ) / Real.log w + (w : ℝ) ^ 4 := by
  filter_upwards [SelbergHarmonicMass.eventually_log_div_two_le_harmonicMass] with w hw Y
  have hlog : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast hw.1)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg Y) (by positivity : 0 < Real.log (w : ℝ) / 2) hw.2
  have heq : (Y : ℝ) / (Real.log w / 2) = 2 * (Y : ℝ) / Real.log w := by ring
  exact (roughIntegers_card_le (by omega) Y).trans (add_le_add (hh.trans_eq heq) le_rfl)

theorem roughComposites_subset_roughIntegers (x Y w : ℕ) :
    roughComposites x Y w ⊆ roughIntegers Y w := by
  classical
  intro n hn
  obtain ⟨hxn, hnY, _, _, hrough⟩ := mem_roughComposites.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hnY⟩, hrough⟩

theorem roughComposites_card_le {w : ℕ} (hw : 1 ≤ w) (x Y : ℕ) :
    ((roughComposites x Y w).card : ℝ) ≤ (Y : ℝ) / harmonicMass w + (w : ℝ) ^ 4 :=
  (Nat.cast_le.mpr (Finset.card_le_card (roughComposites_subset_roughIntegers x Y w))).trans
    (roughIntegers_card_le hw Y)

noncomputable def roughNonsquarefree (Y w : ℕ) : Finset ℕ := by
  classical
  exact (roughIntegers Y w).filter (fun n => ¬Squarefree n)

/-- The square-divisor exceptions cost at most `Y / w`, with no prime-counting input. -/
theorem roughNonsquarefree_card_le {w : ℕ} (hw : 0 < w) (Y : ℕ) :
    ((roughNonsquarefree Y w).card : ℝ) ≤ (Y : ℝ) / w := by
  classical
  let S := Finset.Ioc w Y
  let multiples := fun p : ℕ => (Finset.Icc 1 Y).filter (fun n => p * p ∣ n)
  have hsub : roughNonsquarefree Y w ⊆ S.biUnion multiples := by
    intro n hn
    obtain ⟨hnR, hnsq⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hrough⟩ := Finset.mem_filter.mp hnR
    have hnpos := (Finset.mem_Icc.mp hnI).1
    have hnY := (Finset.mem_Icc.mp hnI).2
    have hex : ∃ p, p.Prime ∧ p * p ∣ n := by
      by_contra h
      apply hnsq
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hd
      exact h ⟨p, hp, hd⟩
    obtain ⟨p, hp, hpd⟩ := hex
    have hpn : p ∣ n := (dvd_mul_right p p).trans hpd
    have hpY : p ≤ Y := (Nat.le_of_dvd hnpos hpn).trans hnY
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_Ioc.mpr ⟨hrough p hp hpn, hpY⟩,
      Finset.mem_filter.mpr ⟨hnI, hpd⟩⟩
  have htail := FGKMT.finite_reciprocal_square_tail hw S (fun p hp => (Finset.mem_Ioc.mp hp).1)
  calc
    _ ≤ ((S.biUnion multiples).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ p ∈ S, ((multiples p).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (S.biUnion multiples).card ≤ ∑ p ∈ S, (multiples p).card)
    _ = ∑ p ∈ S, ((Y / (p * p) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : 0 < p := hw.trans (Finset.mem_Ioc.mp hp).1
      rw [card_multiples_Icc _ _ (Nat.mul_pos hp0 hp0)]
    _ ≤ ∑ p ∈ S, (Y : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Nat.cast_mul, pow_two] using (Nat.cast_div_le (α := ℝ) (m := Y) (n := p * p))
    _ = (Y : ℝ) * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rfl
    _ ≤ (Y : ℝ) * (w : ℝ)⁻¹ := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg Y)
    _ = _ := rfl

end Erdos4.Tilted
