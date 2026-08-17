import ErdosProblems.Erdos622.IntermediateImbalance
import ErdosProblems.Erdos622.BalancedCutWindowDKM

/-!
# The shifted Gaussian window in the two-large case of Erdős Problem 622

The preceding analytic development proves that a Gaussian window has mass
strictly greater than one half whenever the product of its positive endpoints
is at least `15 / 32`.  Here we prove the algebraic capacity-product estimate
which supplies that hypothesis and make the strict inequality uniform on the
compact parameter box used in the counting argument.
-/

open Filter MeasureTheory Set
open scoped Interval

namespace Erdos622.ShiftedGaussian

noncomputable section

/-- The algebraic capacity estimate underlying the shifted Gaussian endpoint
product.  For small `κ`, the first capacity is close to `α / 4`; for large
`κ`, its alternate lower bound `15 * κ` takes over. -/
lemma fifteen_sixtyFour_le_capacity_product
    {α κ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ) :
    (15 / 64 : ℝ) ≤
      max (α / 4 - κ) (15 * κ) * max (1 / α) κ := by
  have hinv : 0 < 1 / α := one_div_pos.mpr hα
  have hsecond : 1 / α ≤ max (1 / α) κ := le_max_left _ _
  by_cases hsmall : κ ≤ α / 64
  · have hfirst : α / 4 - κ ≤ max (α / 4 - κ) (15 * κ) :=
      le_max_left _ _
    have hleftNonneg : 0 ≤ α / 4 - κ := by
      nlinarith [hsmall, hα]
    have hmaxFirstNonneg : 0 ≤ max (α / 4 - κ) (15 * κ) :=
      hleftNonneg.trans hfirst
    calc
      (15 / 64 : ℝ) ≤ (α / 4 - κ) * (1 / α) := by
        rw [show (α / 4 - κ) * (1 / α) = (α / 4 - κ) / α by ring]
        rw [le_div_iff₀ hα]
        nlinarith
      _ ≤ max (α / 4 - κ) (15 * κ) * (1 / α) := by
        exact mul_le_mul_of_nonneg_right hfirst hinv.le
      _ ≤ max (α / 4 - κ) (15 * κ) * max (1 / α) κ := by
        exact mul_le_mul_of_nonneg_left hsecond hmaxFirstNonneg
  · have hlarge : α / 64 ≤ κ := le_of_not_ge hsmall
    have hfirst : 15 * κ ≤ max (α / 4 - κ) (15 * κ) :=
      le_max_right _ _
    have h15κ : 0 ≤ 15 * κ := mul_nonneg (by norm_num) hκ
    have hmaxFirstNonneg : 0 ≤ max (α / 4 - κ) (15 * κ) :=
      h15κ.trans hfirst
    calc
      (15 / 64 : ℝ) ≤ (15 * κ) * (1 / α) := by
        rw [show (15 * κ) * (1 / α) = (15 * κ) / α by ring]
        rw [le_div_iff₀ hα]
        nlinarith
      _ ≤ max (α / 4 - κ) (15 * κ) * (1 / α) := by
        exact mul_le_mul_of_nonneg_right hfirst hinv.le
      _ ≤ max (α / 4 - κ) (15 * κ) * max (1 / α) κ := by
        exact mul_le_mul_of_nonneg_left hsecond hmaxFirstNonneg

/-- The capacity endpoints are positive and their Gaussian window has mass
strictly greater than one half. -/
theorem capacity_gaussianWindow_gt_half
    {α κ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ) :
    (1 / 2 : ℝ) <
      gaussianWindow
        (max (α / 4 - κ) (15 * κ) * Real.sqrt 2)
        (max (1 / α) κ * Real.sqrt 2) := by
  let a : ℝ := max (α / 4 - κ) (15 * κ)
  let b : ℝ := max (1 / α) κ
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have ha : 0 < a := by
    dsimp [a]
    by_cases hk0 : κ = 0
    · subst κ
      simpa using (div_pos hα (by norm_num : (0 : ℝ) < 4))
    · exact lt_of_lt_of_le
        (mul_pos (by norm_num) (lt_of_le_of_ne hκ (Ne.symm hk0)))
        (le_max_right _ _)
  have hb : 0 < b := by
    exact (one_div_pos.mpr hα).trans_le (le_max_left _ _)
  apply
    AlmostBipartiteRegimeCounts.gaussianWindow_gt_half_of_fifteen_thirtyTwo_le_mul
  · positivity
  · positivity
  · have hprod := fifteen_sixtyFour_le_capacity_product hα hκ
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    dsimp [a, b] at ha hb
    calc
      (15 / 32 : ℝ) = (15 / 64 : ℝ) * 2 := by norm_num
      _ ≤ (max (α / 4 - κ) (15 * κ) * max (1 / α) κ) * 2 := by
        gcongr
      _ = (max (α / 4 - κ) (15 * κ) * Real.sqrt 2) *
          (max (1 / α) κ * Real.sqrt 2) := by
        nlinarith

/-- On every compact positive range of `α` and the compact loss range
`0 ≤ κ ≤ 1`, the shifted Gaussian advantage has a uniform positive margin. -/
theorem capacity_gaussianWindow_uniform_margin {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ α ∈ Set.Icc η M, ∀ κ ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 : ℝ) + margin ≤
          gaussianWindow
            (max (α / 4 - κ) (15 * κ) * Real.sqrt 2)
            (max (1 / α) κ * Real.sqrt 2) := by
  let f : ℝ × ℝ → ℝ := fun p ↦
    gaussianWindow
      (max (p.1 / 4 - p.2) (15 * p.2) * Real.sqrt 2)
      (max (1 / p.1) p.2 * Real.sqrt 2)
  let K : Set (ℝ × ℝ) := Set.Icc η M ×ˢ Set.Icc (0 : ℝ) 1
  have hhalf : Continuous gaussianHalfInterval :=
    intervalIntegral.continuous_primitive gaussianKernel_intervalIntegrable 0
  have hcont : ContinuousOn f K := by
    intro p hp
    have hpne : p.1 ≠ 0 := (hη.trans_le hp.1.1).ne'
    dsimp [f, gaussianWindow]
    fun_prop
  have hcompact : IsCompact K := by
    exact isCompact_Icc.prod isCompact_Icc
  have hnonempty : K.Nonempty := by
    refine ⟨(η, 0), ?_⟩
    exact ⟨⟨le_rfl, hηM⟩, by norm_num⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  have hp₀α : 0 < p₀.1 := hη.trans_le hp₀.1.1
  have hstrict : (1 / 2 : ℝ) < f p₀ := by
    exact capacity_gaussianWindow_gt_half hp₀α hp₀.2.1
  refine ⟨(f p₀ - 1 / 2) / 2, by linarith, ?_⟩
  intro α hα κ hκ
  have hp : (α, κ) ∈ K := ⟨hα, hκ⟩
  have hle := hmin hp
  change f p₀ ≤ f (α, κ) at hle
  dsimp [f] at hle ⊢
  linarith

/-- The first capacity has a uniform explicit positive lower bound when
`α` is bounded away from zero. -/
lemma fifteen_mul_alpha_div_sixtyFour_le_first_capacity
    {α κ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ) :
    15 * α / 64 ≤ max (α / 4 - κ) (15 * κ) := by
  by_cases hsmall : κ ≤ α / 64
  · calc
      15 * α / 64 ≤ α / 4 - κ := by nlinarith
      _ ≤ max (α / 4 - κ) (15 * κ) := le_max_left _ _
  · have hlarge : α / 64 ≤ κ := le_of_not_ge hsmall
    calc
      15 * α / 64 ≤ 15 * κ := by nlinarith
      _ ≤ max (α / 4 - κ) (15 * κ) := le_max_right _ _

/-- A single positive additive shrink works simultaneously for all capacity
windows in the compact parameter box.  Both shrunken capacities remain
positive, and the Gaussian advantage retains a uniform positive margin. -/
theorem exists_uniform_shrunken_capacity_gaussian_window {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ ρ margin : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < margin ∧
      ∀ α ∈ Set.Icc η M, ∀ κ ∈ Set.Icc (0 : ℝ) 1,
        0 < max (α / 4 - κ) (15 * κ) - ρ ∧
        0 < max (1 / α) κ - ρ ∧
        (1 / 2 : ℝ) + margin ≤
          gaussianWindow
            ((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2)
            ((max (1 / α) κ - ρ) * Real.sqrt 2) := by
  obtain ⟨m, hm, hideal⟩ := capacity_gaussianWindow_uniform_margin hη hηM
  let K : Set (ℝ × ℝ) := Set.Icc η M ×ˢ Set.Icc (0 : ℝ) 1
  let L : Set ((ℝ × ℝ) × ℝ) := K ×ˢ Set.Icc (0 : ℝ) 1
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p ↦
    gaussianWindow
      ((max (p.1.1 / 4 - p.1.2) (15 * p.1.2) - p.2) * Real.sqrt 2)
      ((max (1 / p.1.1) p.1.2 - p.2) * Real.sqrt 2)
  have hcont : ContinuousOn f L := by
    intro p hp
    have hpne : p.1.1 ≠ 0 := (hη.trans_le hp.1.1.1).ne'
    have hhalf : Continuous gaussianHalfInterval :=
      intervalIntegral.continuous_primitive gaussianKernel_intervalIntegrable 0
    dsimp [f, gaussianWindow]
    fun_prop
  have hcompactK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcompactL : IsCompact L := hcompactK.prod isCompact_Icc
  have huc := hcompactL.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc (m / 2) (by linarith)
  have hM : 0 < M := hη.trans_le hηM
  let ρ : ℝ := min (δ / 2)
    (min (15 * η / 128) (min (1 / (2 * M)) (1 / 2)))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρone : ρ < 1 := by
    have hle := min_le_right (δ / 2)
      (min (15 * η / 128) (min (1 / (2 * M)) (1 / 2)))
    have hle' := hle.trans
      ((min_le_right (15 * η / 128) (min (1 / (2 * M)) (1 / 2))).trans
        (min_le_right (1 / (2 * M)) (1 / 2)))
    linarith
  have hρδ : ρ < δ := by
    have hle := min_le_left (δ / 2)
      (min (15 * η / 128) (min (1 / (2 * M)) (1 / 2)))
    linarith
  refine ⟨ρ, m / 2, hρ, hρone, by linarith, ?_⟩
  intro α hα κ hκ
  have hfirstBase := fifteen_mul_alpha_div_sixtyFour_le_first_capacity
    (hη.trans_le hα.1) hκ.1
  have hρη : ρ ≤ 15 * η / 128 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hfirstPos : 0 < max (α / 4 - κ) (15 * κ) - ρ := by
    have hηα : η ≤ α := hα.1
    nlinarith
  have hρM : ρ ≤ 1 / (2 * M) := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hinv : 1 / M ≤ 1 / α :=
    one_div_le_one_div_of_le (hη.trans_le hα.1) hα.2
  have hsecondPos : 0 < max (1 / α) κ - ρ := by
    have hmax : 1 / α ≤ max (1 / α) κ := le_max_left _ _
    have htwoM : 0 < 1 / (2 * M) := by positivity
    have hhalfM : 1 / (2 * M) < 1 / M := by
      calc
        1 / (2 * M) = (1 / M) / 2 := by field_simp
        _ < 1 / M := by
          have hMinv : 0 < 1 / M := one_div_pos.mpr hM
          linarith
    linarith
  refine ⟨hfirstPos, hsecondPos, ?_⟩
  have hpρ : ((α, κ), ρ) ∈ L := by
    exact ⟨⟨hα, hκ⟩, ⟨hρ.le, hρone.le⟩⟩
  have hp0 : ((α, κ), (0 : ℝ)) ∈ L := by
    exact ⟨⟨hα, hκ⟩, by norm_num⟩
  have hdist : dist ((α, κ), ρ) ((α, κ), (0 : ℝ)) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq, sub_zero, abs_of_pos hρ, max_lt_iff]
    exact ⟨hδ, hρδ⟩
  have hfc := hclose ((α, κ), ρ) hpρ ((α, κ), 0) hp0 hdist
  have hideal' := hideal α hα κ hκ
  have hideal0 : (1 / 2 : ℝ) + m ≤
      f ((α, κ), (0 : ℝ)) := by
    simpa only [f, sub_zero] using hideal'
  rw [Real.dist_eq] at hfc
  have hlower := (abs_lt.mp hfc).1
  dsimp [f] at hlower ⊢
  dsimp [f] at hideal0
  linarith

/-- Compact-uniform de Moivre--Laplace estimate for the uniformly shrunken
capacity windows. -/
theorem eventually_uniform_shrunken_capacity_window {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ ρ margin : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < margin ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ α ∈ Set.Icc η M, ∀ κ ∈ Set.Icc (0 : ℝ) 1,
          (1 / 2 : ℝ) + margin / 2 <
            (BinomialCLT.fairBinomialWindowCount N
              (-((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2))
              ((max (1 / α) κ - ρ) * Real.sqrt 2) : ℝ) /
                (2 : ℝ) ^ N := by
  obtain ⟨ρ, margin, hρ, hρone, hmargin, hgauss⟩ :=
    exists_uniform_shrunken_capacity_gaussian_window hη hηM
  refine ⟨ρ, margin, hρ, hρone, hmargin, ?_⟩
  let K : Set (ℝ × ℝ) := Set.Icc η M ×ˢ Set.Icc (0 : ℝ) 1
  let a : ℝ × ℝ → ℝ := fun p ↦
    -((max (p.1 / 4 - p.2) (15 * p.2) - ρ) * Real.sqrt 2)
  let b : ℝ × ℝ → ℝ := fun p ↦
    (max (1 / p.1) p.2 - ρ) * Real.sqrt 2
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have ha : ContinuousOn a K := by
    apply Continuous.continuousOn
    dsimp [a]
    fun_prop
  have hb : ContinuousOn b K := by
    intro p hp
    have hpne : p.1 ≠ 0 := (hη.trans_le hp.1.1).ne'
    dsimp [b]
    fun_prop
  have hinner : ∀ p ∈ K, ∃ z : ℝ × ℝ,
      a p < z.1 ∧ z.2 < b p ∧ z.1 ≤ z.2 ∧
        (1 / 2 : ℝ) + margin / 2 <
          BinomialCLT.gaussianWindowMass z.1 z.2 := by
    intro p hp
    have hg := hgauss p.1 hp.1 p.2 hp.2
    have hu : 0 <
        (max (p.1 / 4 - p.2) (15 * p.2) - ρ) * Real.sqrt 2 := by
      exact mul_pos hg.1 (Real.sqrt_pos.2 (by norm_num))
    have hv : 0 <
        (max (1 / p.1) p.2 - ρ) * Real.sqrt 2 := by
      exact mul_pos hg.2.1 (Real.sqrt_pos.2 (by norm_num))
    apply exists_strict_inner_gaussian_window hu hv
    linarith [hg.2.2]
  filter_upwards [eventually_uniform_compact_windows hcompact a b
      ((1 / 2 : ℝ) + margin / 2) ha hb hinner] with N hN
  intro α hα κ hκ
  exact hN (α, κ) ⟨hα, hκ⟩

/-- The exact uniformly shrunken count transported to every balanced cut of
the ambient `2n`-vertex type. -/
theorem eventually_uniform_balancedCut_shrunken_capacity_difference_count
    {η M : ℝ} (hη : 0 < η) (hηM : η ≤ M) :
    ∃ ρ margin : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < margin ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ A B : Finset (Fin (2 * n)), IsCut A B →
          A.card = n → B.card = n →
          ∀ α ∈ Set.Icc η M, ∀ κ ∈ Set.Icc (0 : ℝ) 1,
            (1 / 2 : ℝ) + margin / 2 <
              (almostBipartiteCount
                (Finset.univ : Finset (Fin (2 * n)))
                (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                  ((S ∩ A).card + (n - (S ∩ B).card)) ∈
                    Set.Icc
                      (-((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2))
                      ((max (1 / α) κ - ρ) * Real.sqrt 2)) : ℝ) /
                (2 : ℝ) ^ (2 * n) := by
  obtain ⟨ρ, margin, hρ, hρone, hmargin, huniform⟩ :=
    eventually_uniform_shrunken_capacity_window hη hηM
  refine ⟨ρ, margin, hρ, hρone, hmargin, ?_⟩
  rw [eventually_atTop] at huniform ⊢
  obtain ⟨N, hN⟩ := huniform
  refine ⟨N, ?_⟩
  intro n hn A B hcut hA hB α hα κ hκ
  rw [almostBipartiteCount_balancedWindow_eq hcut hA hB]
  apply hN (2 * n) (by omega) α hα κ hκ

end

end Erdos622.ShiftedGaussian
