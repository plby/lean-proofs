import ErdosProblems.Erdos239.External.Erdos67.Section3

/-!
# Section 3 from the unit-circle Elliott specialization

The off-diagonal terms in the interval-energy expansion are translated
correlations.  This file removes the translation by a finite change of
variables and an explicit boundary estimate.  Consequently Tao's Section 3
needs only `UnitCircleLogElliott`, rather than the general two-affine-form
statement.
-/

open scoped BigOperators ENNReal
open MeasureTheory Finset

namespace Erdos67

noncomputable section

/-- The product occurring in the shifted unit-circle Elliott correlation. -/
def unitCircleShiftProduct (g : CompactCircleCharacter) (h n : ℕ) : ℂ :=
  compactCharacterNatValue g n *
    (starRingEnd ℂ) (compactCharacterNatValue g (n + h))

theorem norm_unitCircleShiftProduct (g : CompactCircleCharacter)
    {h n : ℕ} (hn : 0 < n) :
    ‖unitCircleShiftProduct g h n‖ = 1 := by
  rw [unitCircleShiftProduct, norm_mul, Complex.norm_conj,
    norm_compactCharacterNatValue g hn,
    norm_compactCharacterNatValue g (Nat.add_pos_left hn h), one_mul]

/-- Translating a natural interval translates both endpoints. -/
theorem image_Ioc_add_right (L U r : ℕ) :
    (Finset.Ioc L U).image (fun n ↦ n + r) = Finset.Ioc (L + r) (U + r) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨hLn, hnU⟩, rfl⟩
    omega
  · intro hm
    refine ⟨m - r, ?_, ?_⟩
    · omega
    · omega

/-- Reindex a weighted translated sum onto the translated interval. -/
theorem sum_Ioc_harmonic_translate
    (L U r : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc L U,
        (harmonicWeight (n + r) : ℂ) * F (n + r) =
      ∑ m ∈ Finset.Ioc (L + r) (U + r),
        (harmonicWeight m : ℂ) * F m := by
  rw [← image_Ioc_add_right L U r, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.add_right_cancel hab

theorem harmonicWeight_le_one {n : ℕ} (hn : 0 < n) :
    harmonicWeight n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

/-- A boundary interval of length `r` has harmonic mass at most `r`. -/
theorem sum_Ioc_harmonic_le_length (L r : ℕ) :
    ∑ n ∈ Finset.Ioc L (L + r), harmonicWeight n ≤ (r : ℝ) := by
  calc
    ∑ n ∈ Finset.Ioc L (L + r), harmonicWeight n ≤
        ∑ _n ∈ Finset.Ioc L (L + r), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (Finset.mem_Ioc.mp hn).1
      exact harmonicWeight_le_one (by omega)
    _ = (r : ℝ) := by simp

/-- The norm of a unit-circle shifted-product sum over a boundary interval
is at most the length of that interval. -/
theorem norm_sum_Ioc_shiftProduct_le_length
    (g : CompactCircleCharacter) (h L r : ℕ) :
    ‖∑ n ∈ Finset.Ioc L (L + r),
        (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ ≤ (r : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ioc L (L + r),
        (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ ≤
        ∑ n ∈ Finset.Ioc L (L + r),
          ‖(harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc L (L + r), harmonicWeight n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := (Finset.mem_Ioc.mp hn).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (harmonicWeight_nonneg n),
        norm_unitCircleShiftProduct g (by omega), mul_one]
    _ ≤ (r : ℝ) := sum_Ioc_harmonic_le_length L r

/-- The reciprocal-weight error on Tao's geometric window is at most the
translation length. -/
theorem sum_dyadic_harmonic_shift_error_le (K r : ℕ) :
    ∑ n ∈ dyadicCorrelationWindow K,
        (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) ≤ (r : ℝ) := by
  let L : ℕ := 2 ^ K
  let U : ℕ := 4 ^ K
  have hL : 0 < L := by positivity
  have hULsq : (U : ℝ) = (L : ℝ) ^ 2 := by
    have hnat : U = L * L := by
      dsimp [L, U]
      rw [← mul_pow]
      norm_num
    rw [hnat]
    push_cast
    ring
  calc
    ∑ n ∈ dyadicCorrelationWindow K,
        (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) ≤
        ∑ _n ∈ dyadicCorrelationWindow K,
          (r : ℝ) / (L : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnL : L ≤ n := by
        dsimp [L]
        exact (Finset.mem_Ioc.mp hn).1.le
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hL.trans_le hnL
      have hden : (L : ℝ) ^ 2 ≤ (n : ℝ) * (n + r : ℝ) := by
        have hLn : (L : ℝ) ≤ n := by exact_mod_cast hnL
        have hnnr : (n : ℝ) ≤ (n + r : ℕ) := by exact_mod_cast Nat.le_add_right n r
        nlinarith
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = ((dyadicCorrelationWindow K).card : ℝ) *
          ((r : ℝ) / (L : ℝ) ^ 2) := by simp
    _ ≤ (U : ℝ) * ((r : ℝ) / (L : ℝ) ^ 2) := by
      gcongr
      have hcard : (dyadicCorrelationWindow K).card ≤ U := by
        simp [dyadicCorrelationWindow, U]
      exact_mod_cast hcard
    _ = (r : ℝ) := by
      rw [hULsq]
      field_simp

/-- Changing the reciprocal weight from `1/n` to `1/(n+r)` costs at most
`r` on the geometric window. -/
theorem norm_dyadic_translate_sub_reweighted_le
    (K r h : ℕ) (g : CompactCircleCharacter) :
    ‖(∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
        ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight (n + r) : ℂ) *
            unitCircleShiftProduct g h (n + r)‖ ≤ (r : ℝ) := by
  refine (norm_sum_harmonic_shift_sub_le
    (dyadicCorrelationWindow K) (unitCircleShiftProduct g h) r ?_ ?_).trans ?_
  · intro n hn
    have hn' := (Finset.mem_Ioc.mp hn).1
    exact (pow_pos (by omega) K).trans hn'
  · intro n hn
    exact (norm_unitCircleShiftProduct g (by
      have hn' := (Finset.mem_Ioc.mp hn).1
      exact Nat.add_pos_left ((pow_pos (by omega) K).trans hn') r)).le
  · exact sum_dyadic_harmonic_shift_error_le K r

/-- After reindexing, the translated and untranslated intervals differ only
by two boundary intervals of length `r`. -/
theorem norm_dyadic_reweighted_translate_sub_unshifted_le
    (K r h : ℕ) (g : CompactCircleCharacter)
    (hr : r ≤ 2 ^ K) (hK : 0 < K) :
    ‖(∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight (n + r) : ℂ) *
            unitCircleShiftProduct g h (n + r)) -
        ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ ≤
      2 * (r : ℝ) := by
  let L : ℕ := 2 ^ K
  let U : ℕ := 4 ^ K
  have hLrU : L + r ≤ U := by
    have htwoL : 2 * L ≤ U := by
      dsimp [L, U]
      have hpow : 2 ^ K ≤ 4 ^ K := Nat.pow_le_pow_left (by omega) K
      have hLtwo : 2 * 2 ^ K ≤ 2 ^ K * 2 ^ K := by
        have : 2 ≤ 2 ^ K := by
          have h1K : 1 ≤ K := by omega
          simpa using Nat.pow_le_pow_right (by omega : 0 < 2) h1K
        nlinarith
      have hsquare : 2 ^ K * 2 ^ K = 4 ^ K := by
        rw [← mul_pow]
        norm_num
      omega
    omega
  have hreindex :
      ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight (n + r) : ℂ) *
            unitCircleShiftProduct g h (n + r) =
        ∑ n ∈ Finset.Ioc (L + r) (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n := by
    simpa [dyadicCorrelationWindow, L, U] using
      sum_Ioc_harmonic_translate L U r (unitCircleShiftProduct g h)
  have hunshift :
      ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n =
        (∑ n ∈ Finset.Ioc L (L + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) +
        ∑ n ∈ Finset.Ioc (L + r) U,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n := by
    dsimp [dyadicCorrelationWindow, L, U]
    exact (Finset.sum_Ioc_consecutive
      (fun n : ℕ ↦ (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n)
      (Nat.le_add_right L r) hLrU).symm
  have hshift :
      ∑ n ∈ Finset.Ioc (L + r) (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n =
        (∑ n ∈ Finset.Ioc (L + r) U,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) +
        ∑ n ∈ Finset.Ioc U (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n := by
    exact (Finset.sum_Ioc_consecutive
      (fun n : ℕ ↦ (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n)
      hLrU (Nat.le_add_right U r)).symm
  rw [hreindex, hunshift, hshift]
  have heq :
      ((∑ n ∈ Finset.Ioc (L + r) U,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) +
          ∑ n ∈ Finset.Ioc U (U + r),
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) -
        ((∑ n ∈ Finset.Ioc L (L + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) +
          ∑ n ∈ Finset.Ioc (L + r) U,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) =
        (∑ n ∈ Finset.Ioc U (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) -
        ∑ n ∈ Finset.Ioc L (L + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n := by ring
  rw [heq]
  calc
    ‖(∑ n ∈ Finset.Ioc U (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) -
        ∑ n ∈ Finset.Ioc L (L + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ ≤
        ‖∑ n ∈ Finset.Ioc U (U + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ +
        ‖∑ n ∈ Finset.Ioc L (L + r),
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ :=
      norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := add_le_add
      (norm_sum_Ioc_shiftProduct_le_length g h U r)
      (norm_sum_Ioc_shiftProduct_le_length g h L r)
    _ = 2 * (r : ℝ) := by ring

/-- The complete translation comparison: an off-diagonal translated
correlation differs from the ordinary shifted correlation by at most `3r`. -/
theorem norm_dyadic_translate_sub_shiftedLogCorrelation_le
    (K r h : ℕ) (g : CompactCircleCharacter)
    (hr : r ≤ 2 ^ K) (hK : 0 < K) :
    ‖(∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
        shiftedLogCorrelation (compactCharacterNatValue g) h
          (4 ^ K) (2 ^ K)‖ ≤ 3 * (r : ℝ) := by
  have hweight := norm_dyadic_translate_sub_reweighted_le K r h g
  have hboundary :=
    norm_dyadic_reweighted_translate_sub_unshifted_le K r h g hr hK
  have hwindow := elliottLogWindow_four_two K
  have hshifted :
      shiftedLogCorrelation (compactCharacterNatValue g) h
          (4 ^ K) (2 ^ K) =
        ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n := by
    rw [shiftedLogCorrelation, hwindow]
    simp only [unitCircleShiftProduct, mul_assoc]
  rw [hshifted]
  calc
    ‖(∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
        ∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ ≤
        ‖(∑ n ∈ dyadicCorrelationWindow K,
          (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
          ∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight (n + r) : ℂ) *
              unitCircleShiftProduct g h (n + r)‖ +
        ‖(∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight (n + r) : ℂ) *
              unitCircleShiftProduct g h (n + r)) -
          ∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n‖ := by
      rw [show
        (∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
          ∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n =
        ((∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h (n + r)) -
          ∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight (n + r) : ℂ) *
              unitCircleShiftProduct g h (n + r)) +
        ((∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight (n + r) : ℂ) *
              unitCircleShiftProduct g h (n + r)) -
          ∑ n ∈ dyadicCorrelationWindow K,
            (harmonicWeight n : ℂ) * unitCircleShiftProduct g h n) by ring]
      exact norm_add_le _ _
    _ ≤ (r : ℝ) + 2 * (r : ℝ) := add_le_add hweight hboundary
    _ = 3 * (r : ℝ) := by ring

/-- For ordered shifts `a < b`, the off-diagonal energy correlation is a
translate by `a+1` of the usual positive shift `b-a`. -/
theorem compactCharacterCorrelation_eq_translatedShiftProduct
    (K a b : ℕ) (g : CompactCircleCharacter) (hab : a < b) :
    compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) a b g =
      ∑ n ∈ dyadicCorrelationWindow K,
        (harmonicWeight n : ℂ) *
          unitCircleShiftProduct g (b - a) (n + (a + 1)) := by
  unfold compactCharacterCorrelation harmonicWeight unitCircleShiftProduct
  apply Finset.sum_congr rfl
  intro n hn
  have hleft : n + a + 1 = n + (a + 1) := by omega
  have hright : n + b + 1 = (n + (a + 1)) + (b - a) := by omega
  rw [hleft, hright]
  ring

/-- Reversing the two shifts conjugates the correlation. -/
theorem conj_compactCharacterCorrelation
    (K a b : ℕ) (g : CompactCircleCharacter) :
    (starRingEnd ℂ)
        (compactCharacterCorrelation (dyadicCorrelationWindow K)
          (fun n ↦ (n : ℝ)⁻¹) a b g) =
      compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) b a g := by
  unfold compactCharacterCorrelation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [map_mul, starRingEnd_self_apply]
  have hw : (starRingEnd ℂ) (↑((n : ℝ)⁻¹) : ℂ) = (↑((n : ℝ)⁻¹) : ℂ) := by
    simp
  rw [hw]
  ring

theorem norm_compactCharacterCorrelation_comm
    (K a b : ℕ) (g : CompactCircleCharacter) :
    ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) a b g‖ =
      ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) b a g‖ := by
  rw [← conj_compactCharacterCorrelation K a b g, Complex.norm_conj]

/-- Ordered off-diagonal correlations are controlled by the ordinary shifted
correlation, up to the explicit translation error. -/
theorem norm_compactCharacterCorrelation_le_shifted_add
    (K a b : ℕ) (g : CompactCircleCharacter) (hab : a < b)
    (haK : a + 1 ≤ 2 ^ K) (hK : 0 < K) :
    ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
      ‖shiftedLogCorrelation (compactCharacterNatValue g) (b - a)
          (4 ^ K) (2 ^ K)‖ + 3 * ((a + 1 : ℕ) : ℝ) := by
  rw [compactCharacterCorrelation_eq_translatedShiftProduct K a b g hab]
  let C : ℂ := ∑ n ∈ dyadicCorrelationWindow K,
    (harmonicWeight n : ℂ) *
      unitCircleShiftProduct g (b - a) (n + (a + 1))
  let S : ℂ := shiftedLogCorrelation (compactCharacterNatValue g) (b - a)
    (4 ^ K) (2 ^ K)
  have hdiff : ‖C - S‖ ≤ 3 * ((a + 1 : ℕ) : ℝ) := by
    simpa [C, S] using
      norm_dyadic_translate_sub_shiftedLogCorrelation_le
        K (a + 1) (b - a) g haK hK
  have htri : ‖C‖ ≤ ‖S‖ + ‖C - S‖ := by
    have h := norm_add_le S (C - S)
    rw [show S + (C - S) = C by ring] at h
    exact h
  exact htri.trans (add_le_add le_rfl hdiff)

/-- Symmetric form of the translation comparison.  The Elliott shift is the
positive distance between the two distinct indices, and the translation
length is at most `max a b + 1`. -/
theorem norm_compactCharacterCorrelation_le_shifted_add_general
    (K a b : ℕ) (g : CompactCircleCharacter) (hab : a ≠ b)
    (hmaxK : max a b + 1 ≤ 2 ^ K) (hK : 0 < K) :
    ∃ h : ℕ, 0 < h ∧ h ≤ max a b ∧
      ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
          (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
        ‖shiftedLogCorrelation (compactCharacterNatValue g) h
            (4 ^ K) (2 ^ K)‖ + 3 * ((max a b + 1 : ℕ) : ℝ) := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · refine ⟨b - a, Nat.sub_pos_of_lt hablt, ?_, ?_⟩
    · omega
    · have haK : a + 1 ≤ 2 ^ K := by omega
      have hmain := norm_compactCharacterCorrelation_le_shifted_add
        K a b g hablt haK hK
      have herr : (3 : ℝ) * (a + 1 : ℕ) ≤
          3 * (max a b + 1 : ℕ) := by
        gcongr
        exact le_max_left a b
      exact hmain.trans (add_le_add le_rfl herr)
  · refine ⟨a - b, Nat.sub_pos_of_lt hbalt, ?_, ?_⟩
    · omega
    · rw [norm_compactCharacterCorrelation_comm K a b g]
      have hbK : b + 1 ≤ 2 ^ K := by omega
      have hmain := norm_compactCharacterCorrelation_le_shifted_add
        K b a g hbalt hbK hK
      have herr : (3 : ℝ) * (b + 1 : ℕ) ≤
          3 * (max a b + 1 : ℕ) := by
        gcongr
        exact le_max_right a b
      exact hmain.trans (add_le_add le_rfl herr)

/-! ## Unit-circle Elliott endpoint -/

/-- Unit-circle Elliott controls an ordered off-diagonal energy correlation;
the only loss is the explicit translation error above. -/
theorem UnitCircleLogElliott.compactCharacterCorrelation_ordered
    (helliott : UnitCircleLogElliott)
    (a b : ℕ) (hab : a < b) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        a + 1 ≤ 2 ^ K →
        ∀ g : CompactCircleCharacter,
          ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
          ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
              (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
            η * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * ((a + 1 : ℕ) : ℝ) := by
  have hh : 0 < b - a := Nat.sub_pos_of_lt hab
  obtain ⟨A₀, hA₀, hmain⟩ := helliott η hη (b - a) hh
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK haK g hno
  let f : ℕ → ℂ := compactCharacterNatValue g
  have hfMult : IsCompletelyMultiplicativeOnPositive f :=
    compactCharacterNatValue_isCompletelyMultiplicative g
  have hfUnit : ∀ n : ℕ, 0 < n → ‖f n‖ = 1 :=
    fun n hn ↦ norm_compactCharacterNatValue g hn
  have hpret :
      ∀ q : ℕ, 0 < q → q ≤ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * ((4 ^ K : ℕ) : ℝ) →
            (A : ℝ) ≤ pretentiousDistSqToTwist f χ t (4 ^ K) := by
    intro q hq hqA χ t ht
    by_contra hdist
    apply hno
    exact ⟨q, hq, hqA, χ, t, ht, lt_of_not_ge hdist⟩
  have hWX : 2 ^ K ≤ 4 ^ K := Nat.pow_le_pow_left (by omega) K
  have hshift := hmain A (4 ^ K) (2 ^ K) hA hAK hWX
    f hfMult hfUnit hpret
  have htranslate := norm_compactCharacterCorrelation_le_shifted_add
    K a b g hab haK hK
  exact htranslate.trans (add_le_add hshift le_rfl)

/-- Symmetric form of the preceding endpoint. -/
theorem UnitCircleLogElliott.compactCharacterCorrelation
    (helliott : UnitCircleLogElliott)
    (a b : ℕ) (hab : a ≠ b) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        max a b + 1 ≤ 2 ^ K →
        ∀ g : CompactCircleCharacter,
          ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
          ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
              (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
            η * Real.log ((2 ^ K : ℕ) : ℝ) +
              3 * ((max a b + 1 : ℕ) : ℝ) := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · obtain ⟨A₀, hA₀, hmain⟩ :=
      helliott.compactCharacterCorrelation_ordered a b hablt η hη
    refine ⟨A₀, hA₀, ?_⟩
    intro A K hA hAK hK hmaxK g hno
    have haK : a + 1 ≤ 2 ^ K := by omega
    have hbound := hmain A K hA hAK hK haK g hno
    have herr : (3 : ℝ) * (a + 1 : ℕ) ≤
        3 * (max a b + 1 : ℕ) := by
      gcongr
      exact le_max_left a b
    exact hbound.trans (add_le_add le_rfl herr)
  · obtain ⟨A₀, hA₀, hmain⟩ :=
      helliott.compactCharacterCorrelation_ordered b a hbalt η hη
    refine ⟨A₀, hA₀, ?_⟩
    intro A K hA hAK hK hmaxK g hno
    rw [norm_compactCharacterCorrelation_comm K a b g]
    have hbK : b + 1 ≤ 2 ^ K := by omega
    have hbound := hmain A K hA hAK hK hbK g hno
    have herr : (3 : ℝ) * (b + 1 : ℕ) ≤
        3 * (max a b + 1 : ℕ) := by
      gcongr
      exact le_max_right a b
    exact hbound.trans (add_le_add le_rfl herr)

/-- Uniformity over the finitely many off-diagonal shifts in an interval of
length `H`.  The threshold is enlarged to be at least `H`, so
`A₀ ≤ A ≤ 2^K` automatically makes every translation admissible. -/
theorem UnitCircleLogElliott.uniform_compactCharacterCorrelation
    (helliott : UnitCircleLogElliott)
    (H : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ H ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        ∀ a < H, ∀ b < H, a ≠ b →
          ∀ g : CompactCircleCharacter,
            ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
            ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
                (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
              η * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * (H : ℝ) := by
  classical
  let P : Fin H × Fin H → ℕ → Prop := fun p A ↦
    p.1.val ≠ p.2.val →
      ∀ K : ℕ, A ≤ 2 ^ K → 0 < K →
        ∀ g : CompactCircleCharacter,
          ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
          ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
              (fun n ↦ (n : ℝ)⁻¹) p.1.val p.2.val g‖ ≤
            η * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * (H : ℝ)
  have hP : ∀ p : Fin H × Fin H,
      ∃ N : ℕ, 2 ≤ N ∧ ∀ A : ℕ, N ≤ A → P p A := by
    intro p
    by_cases hp : p.1.val = p.2.val
    · refine ⟨2, le_rfl, ?_⟩
      intro A hA hne
      exact (hne hp).elim
    · obtain ⟨N, hN, hmain⟩ :=
        helliott.compactCharacterCorrelation p.1.val p.2.val hp η hη
      refine ⟨max H N, hN.trans (le_max_right H N), ?_⟩
      intro A hA hne K hAK hK g hno
      have hNA : N ≤ A := (le_max_right H N).trans hA
      have hHA : H ≤ A := (le_max_left H N).trans hA
      have hmaxK : max p.1.val p.2.val + 1 ≤ 2 ^ K := by
        have hfirst : max p.1.val p.2.val + 1 ≤ H := by
          have hp1 := p.1.isLt
          have hp2 := p.2.isLt
          omega
        exact hfirst.trans (hHA.trans hAK)
      have hbound := hmain A K hNA hAK hK hmaxK g hno
      have herr : (3 : ℝ) * (max p.1.val p.2.val + 1 : ℕ) ≤
          3 * (H : ℝ) := by
        gcongr
        exact_mod_cast (show max p.1.val p.2.val + 1 ≤ H by
          have hp1 := p.1.isLt
          have hp2 := p.2.isLt
          omega)
      exact hbound.trans (add_le_add le_rfl herr)
  obtain ⟨N, hN, huniform⟩ := exists_uniform_nat_bound P hP
  let A₀ := max H N
  refine ⟨A₀, hN.trans (le_max_right H N), le_max_left H N, ?_⟩
  intro A K hA hAK hK a ha b hb hab g hno
  let ai : Fin H := ⟨a, ha⟩
  let bi : Fin H := ⟨b, hb⟩
  have hNA : N ≤ A := (le_max_right H N).trans hA
  exact huniform A hNA (ai, bi) hab K hAK hK g hno

/-- Unit-circle version of Tao's high-probability pretentious-set endpoint.
Compared with the affine-form version in `Section3`, the threshold displays
the harmless finite translation error `3H`. -/
theorem UnitCircleLogElliott.exists_highProbability_pretentiousSet_withTranslationError
    (helliott : UnitCircleLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ H ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * (H : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G, HasBoundedPretentiousApproximation A (4 ^ K) g := by
  obtain ⟨A₀, hA₀, hHA₀, hcorr⟩ :=
    UnitCircleLogElliott.uniform_compactCharacterCorrelation helliott H η hη
  refine ⟨A₀, hA₀, hHA₀, ?_⟩
  intro A K hA hAK hK hthreshold
  let G : Set CompactCircleCharacter :=
    {g | compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) H g < B * dyadicCorrelationWeight K}
  refine ⟨G, ?_, ?_, ?_⟩
  · exact isOpen_lt
      (continuous_compactCharacterWeightedEnergy
        (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H)
      continuous_const |>.measurableSet
  · have hmarkov := measure_dyadicWeightedEnergy_ge_le
      μ C B K H hK hBpos hbound
    simpa only [G, Set.compl_ofPred, not_lt] using hmarkov
  · intro g hg
    have henergy :
        compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
            (fun n ↦ (n : ℝ)⁻¹) H g ≤
          B * dyadicCorrelationWeight K := hg.le
    obtain ⟨a, ha, b, hb, hab, hlarge⟩ :=
      exists_large_dyadicCorrelation K H g B hK hH hBH henergy
    by_contra hno
    have hsmall := hcorr A K hA hAK hK a ha b hb hab g hno
    linarith

/-! ## Absorbing the finite translation error -/

/-- Once `A ≤ 2^K` and `A` is above a fixed threshold, the logarithm at
scale `2^K` absorbs the finite error `3H`. -/
theorem exists_threshold_three_mul_le_log
    (H : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ T : ℕ, 2 ≤ T ∧ H ≤ T ∧
      ∀ A K : ℕ, T ≤ A → A ≤ 2 ^ K →
        3 * (H : ℝ) ≤ η * Real.log ((2 ^ K : ℕ) : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden : 0 < η * Real.log (2 : ℝ) := mul_pos hη hlog2
  obtain ⟨J, hJ⟩ :=
    exists_nat_ge (3 * (H : ℝ) / (η * Real.log (2 : ℝ)))
  let T : ℕ := max H (max 2 (2 ^ J))
  refine ⟨T, ?_, ?_, ?_⟩
  · exact (le_max_left 2 (2 ^ J)).trans (le_max_right H (max 2 (2 ^ J)))
  · exact le_max_left H (max 2 (2 ^ J))
  · intro A K hTA hAK
    have hpow : 2 ^ J ≤ 2 ^ K := by
      exact (le_max_right 2 (2 ^ J)).trans
        ((le_max_right H (max 2 (2 ^ J))).trans (hTA.trans hAK))
    have hJK : J ≤ K :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    have hbase : 3 * (H : ℝ) ≤
        (J : ℝ) * (η * Real.log (2 : ℝ)) := by
      exact (div_le_iff₀ hden).mp hJ
    have hscale : (J : ℝ) * (η * Real.log (2 : ℝ)) ≤
        (K : ℝ) * (η * Real.log (2 : ℝ)) := by
      gcongr
    calc
      3 * (H : ℝ) ≤ (K : ℝ) * (η * Real.log (2 : ℝ)) :=
        hbase.trans hscale
      _ = η * Real.log ((2 ^ K : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        ring_nf

/-- The exact uniform correlation signature used by the original Section 4:
the finite translation error has been absorbed by enlarging `A₀`. -/
theorem UnitCircleLogElliott.uniform_compactCharacterCorrelation_absorbed
    (helliott : UnitCircleLogElliott)
    (H : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        ∀ a < H, ∀ b < H, a ≠ b →
          ∀ g : CompactCircleCharacter,
            ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
            ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
                (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
              η * Real.log ((2 ^ K : ℕ) : ℝ) := by
  have hhalf : 0 < η / 2 := by positivity
  obtain ⟨N, hN, hHN, hcorr⟩ :=
    UnitCircleLogElliott.uniform_compactCharacterCorrelation
      helliott H (η / 2) hhalf
  obtain ⟨T, hT, hHT, habsorb⟩ :=
    exists_threshold_three_mul_le_log H (η / 2) hhalf
  let A₀ := max N T
  refine ⟨A₀, hN.trans (le_max_left N T), ?_⟩
  intro A K hA hAK hK a ha b hb hab g hno
  have hNA : N ≤ A := (le_max_left N T).trans (hA)
  have hTA : T ≤ A := (le_max_right N T).trans (hA)
  have hsmall := hcorr A K hNA hAK hK a ha b hb hab g hno
  have herr := habsorb A K hTA hAK
  calc
    ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
        (η / 2) * Real.log ((2 ^ K : ℕ) : ℝ) + 3 * (H : ℝ) := hsmall
    _ ≤ (η / 2) * Real.log ((2 ^ K : ℕ) : ℝ) +
        (η / 2) * Real.log ((2 ^ K : ℕ) : ℝ) :=
      add_le_add le_rfl herr
    _ = η * Real.log ((2 ^ K : ℕ) : ℝ) := by ring

/-- Unit-circle Elliott gives precisely the same high-probability
pretentious-set interface consumed by `Section4Probability`, without using
the full affine-form Elliott proposition. -/
theorem UnitCircleLogElliott.exists_highProbability_pretentiousSet
    (helliott : UnitCircleLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G, HasBoundedPretentiousApproximation A (4 ^ K) g := by
  obtain ⟨A₀, hA₀, hcorr⟩ :=
    UnitCircleLogElliott.uniform_compactCharacterCorrelation_absorbed
      helliott H η hη
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hthreshold
  let G : Set CompactCircleCharacter :=
    {g | compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) H g < B * dyadicCorrelationWeight K}
  refine ⟨G, ?_, ?_, ?_⟩
  · exact isOpen_lt
      (continuous_compactCharacterWeightedEnergy
        (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H)
      continuous_const |>.measurableSet
  · have hmarkov := measure_dyadicWeightedEnergy_ge_le
      μ C B K H hK hBpos hbound
    simpa only [G, Set.compl_ofPred, not_lt] using hmarkov
  · intro g hg
    have henergy :
        compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
            (fun n ↦ (n : ℝ)⁻¹) H g ≤
          B * dyadicCorrelationWeight K := hg.le
    obtain ⟨a, ha, b, hb, hab, hlarge⟩ :=
      exists_large_dyadicCorrelation K H g B hK hH hBH henergy
    by_contra hno
    have hsmall := hcorr A K hA hAK hK a ha b hb hab g hno
    linarith

end

end Erdos67
