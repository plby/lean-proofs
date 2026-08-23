import ErdosProblems.Erdos587.FinalAssembly

open Filter MeasureTheory
open scoped BigOperators Pointwise

namespace Erdos587
open NVGeneration

theorem rank_two_spread_square_or_common_divisor
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ C l : ℕ}
    {Z : Finset ℤ} {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank)
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₁ : R.length ⟨0, by omega⟩ = L₁)
    (z : ℤ) (hlm : l ≤ (M.fiber z).card)
    (h2l : 2 * l ≤ (M.fiber z).card)
    (hspread : l ≤
      (exchangeDeltas (M.fiberFirst z) hlm).sum)
    (hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₂) + 1) ≤ l)
    (hshort : p * q₂ ≤ L₂)
    (hlong : 4 * (p * q₂) *
      (Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) + 1) ≤ L₂)
    (hres : (usedPositiveResidues (q₁.gcd q₂)
      (B \ M.fiberExchangeReserve z l h2l)).card ≤ C) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q₁.gcd q₂ ∧
        B.card ≤ D.card + 2 * l +
          C * (Nat.log 2 (q₁.gcd q₂) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (q₁.gcd q₂)) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  classical
  let V := M.fiberExchangeReserve z l h2l
  let g := q₁.gcd q₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  let s₀ := positiveIntResidue q₂ (z + R.positiveForm.base)
  let a := q₁ / g
  let mₗ : ℕ := ∑ i : Fin l,
    M.first (M.fiberElement z (lowIndex (by omega) i))
  have hres' : (usedPositiveResidues g (B \ V)).card ≤ C := by
    simpa only [g, V] using hres
  rcases nvQuadraticAdjustmentConstant_spec_with_card
      (r := r + l * s₀) (B \ V) hp hg hres' with
    ⟨U, hUsub, _hUcard, z₁, hz₁⟩ |
      ⟨d, D, hDsub, hd, hdg, hDcard, hdiv⟩
  · left
    have hq₁factor : g * a = q₁ := by
      dsimp only [a]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
    have hq₁factorZ : (q₁ : ℤ) = (g : ℤ) * (a : ℤ) := by
      exact_mod_cast hq₁factor.symm
    have hz₁' := hz₁
    rw [Int.modEq_iff_dvd] at hz₁'
    obtain ⟨k, hk⟩ := hz₁'
    let base₀ := r + l * s₀ + ∑ a ∈ U, a
    have hbase₀ : (base₀ : ℤ) =
        (p : ℤ) * z₁ ^ 2 + (-k) * (g : ℤ) := by
      dsimp only [base₀]
      linear_combination -hk
    let t₁ : ℤ := -k + (a : ℤ) * mₗ
    have hbase :
        (((r + l * s₀ + ∑ a ∈ U, a) + q₁ * mₗ : ℕ) : ℤ) =
          (p : ℤ) * z₁ ^ 2 + t₁ * (g : ℤ) := by
      dsimp only [t₁]
      change (((base₀ + q₁ * mₗ : ℕ) : ℤ)) = _
      push_cast
      rw [hq₁factorZ]
      rw [hbase₀]
      ring
    obtain ⟨x, hx, z₂, hz₂⟩ :=
      nvQuadraticStepConstant_spec (g := q₁) (h := q₂)
        (p := p) (t := t₁) (z₁ := z₁) hq₂ hp
    have hxl : x ≤ l := hx.trans hstep
    have hxgap : x ≤
        (exchangeDeltas (M.fiberFirst z) hlm).sum :=
      hxl.trans hspread
    obtain ⟨T, hTV, hTB, hTcard, u, hu, v, hexchange⟩ :=
      M.exists_fiber_exchange_sum z (l := l) (x := x)
        hlm h2l hxgap
    have hmlCast : (mₗ : ℤ) =
        ∑ i : Fin l, M.fiberFirst z (lowIndex (by omega) i) := by
      dsimp only [mₗ, RankTwoCoverModel.fiberFirst]
      push_cast
      rfl
    have hexchange' :
        (((∑ a ∈ T, a : ℕ) : ℕ) : ℤ) + (u : ℤ) * q₁ =
          (l : ℤ) * (z + R.positiveForm.base) +
            ((mₗ : ℤ) + (x : ℤ)) * q₁ + v * q₂ := by
      rw [← hq₁step, ← hq₂step] at hexchange
      rw [← hmlCast] at hexchange
      simpa only [Int.natCast_add] using hexchange
    have hs₀ : (s₀ : ℤ) ≡ z + R.positiveForm.base
        [ZMOD (q₂ : ℤ)] := by
      exact positiveIntResidue_modEq hq₂ _
    have hexchangeMod :
        (((∑ a ∈ T, a : ℕ) : ℕ) : ℤ) + (u : ℤ) * q₁ ≡
          (l : ℤ) * s₀ + ((mₗ : ℤ) + x) * q₁
            [ZMOD (q₂ : ℤ)] := by
      calc
        (((∑ a ∈ T, a : ℕ) : ℕ) : ℤ) + (u : ℤ) * q₁ =
            (l : ℤ) * (z + R.positiveForm.base) +
              ((mₗ : ℤ) + (x : ℤ)) * q₁ + v * q₂ := hexchange'
        _ ≡ (l : ℤ) * (z + R.positiveForm.base) +
              ((mₗ : ℤ) + (x : ℤ)) * q₁ [ZMOD (q₂ : ℤ)] := by simp
        _ ≡ (l : ℤ) * s₀ + ((mₗ : ℤ) + (x : ℤ)) * q₁
              [ZMOD (q₂ : ℤ)] := by
          exact ((hs₀.mul_left (l : ℤ)).add_right
            (((mₗ : ℤ) + (x : ℤ)) * q₁)).symm
    have hstepMod :
        ((((r + l * s₀ + ∑ a ∈ U, a) + q₁ * mₗ : ℕ) : ℤ) +
            (q₁ : ℤ) * x) ≡ (p : ℤ) * z₂ ^ 2
          [ZMOD (q₂ : ℤ)] := by
      have hz₂' := hz₂
      rw [show q₁.gcd q₂ = g by rfl] at hz₂'
      rw [hbase]
      simpa only [add_assoc, add_left_comm, add_comm] using hz₂'
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_left]
      intro a haU haT
      exact (Finset.mem_sdiff.mp (hUsub haU)).2 (hTV haT)
    have hUTB : U ∪ T ⊆ B := by
      apply Finset.union_subset
      · exact hUsub.trans Finset.sdiff_subset
      · exact hTB
    let wsum := ∑ a ∈ U ∪ T, a
    have hwsum : wsum = (∑ a ∈ U, a) + ∑ a ∈ T, a := by
      dsimp only [wsum]
      exact Finset.sum_union hdisj
    have hbaseMod :
        ((r + wsum + q₁ * u : ℕ) : ℤ) ≡
          (p : ℤ) * z₂ ^ 2 [ZMOD (q₂ : ℤ)] := by
      have hfirst := hexchangeMod.add_left
        (((r + ∑ a ∈ U, a : ℕ) : ℤ))
      have hbridge :
          (((r + ∑ a ∈ U, a : ℕ) : ℤ)) +
              ((l : ℤ) * s₀ + ((mₗ : ℤ) + (x : ℤ)) * q₁) =
            ((((r + l * s₀ + ∑ a ∈ U, a) + q₁ * mₗ : ℕ) : ℤ) +
              (q₁ : ℤ) * x) := by
        push_cast
        ring
      rw [hbridge] at hfirst
      have hcombined := hfirst.trans hstepMod
      convert hcombined using 1
      rw [hwsum]
      push_cast
      ring
    have hwsumMem : wsum ∈ B.subsetSum := by
      rw [Finset.mem_subsetSum_iff]
      exact ⟨U ∪ T, hUTB, rfl⟩
    let base := r + wsum + q₁ * u
    have hAP : natAP base q₂ L₂ ⊆ A.subsetSum := by
      intro m hm
      obtain ⟨y, hy, rfl⟩ := mem_natAP_iff.mp hm
      dsimp only [base]
      have hu' : u ≤ L₁ := by simpa only [hL₁] using hu
      simpa only [add_assoc] using hfamily wsum hwsumMem u hu' y hy
    let w := z₂.natAbs
    have hwSq : (w : ℤ) ^ 2 = z₂ ^ 2 := by simp [w, sq]
    have hmodNat : base ≡ p * w ^ 2 [MOD q₂] := by
      exact_mod_cast (show (base : ℤ) ≡ ((p * w ^ 2 : ℕ) : ℤ)
          [ZMOD (q₂ : ℤ)] by
        simpa only [base, Nat.cast_mul, Nat.cast_pow, hwSq] using hbaseMod)
    have hbaseMem : base ∈ A.subsetSum :=
      hAP (mem_natAP_iff.mpr ⟨0, by simp, by simp⟩)
    have hbaseUpper : base ≤ A.card * N :=
      (Finset.mem_Icc.mp
        (NVGeneration.subsetSum_subset_Icc_of_subset
          (U := A) (A := A) Finset.Subset.rfl hAN le_rfl hbaseMem)).2
    have hsqrt : Nat.sqrt (base / (p * q₂ ^ 2)) ≤
        Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) := by
      apply Nat.sqrt_le_sqrt
      exact Nat.div_le_div_right hbaseUpper
    have hlong' : 4 * (p * q₂) *
        (Nat.sqrt (base / (p * q₂ ^ 2)) + 1) ≤ L₂ :=
      (Nat.mul_le_mul_left (4 * (p * q₂))
        (Nat.add_le_add_right hsqrt 1)).trans hlong
    obtain ⟨m, hmAP, hmpos, v₀, hmv₀⟩ :=
      exists_p_mul_square_mem_natAP_of_modEq
        p q₂ base L₂ w hp hq₂ hmodNat hshort hlong'
    have hmSum := hAP hmAP
    rw [Finset.mem_subsetSum_iff] at hmSum
    obtain ⟨S, hSA, hsum⟩ := hmSum
    refine ⟨S, hSA, ?_, v₀, ?_⟩
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hS
      subst S
      simp at hsum
      omega
    · omega
  · right
    refine ⟨d, D, hDsub.trans Finset.sdiff_subset, hd, ?_, ?_, hdiv⟩
    · simpa only [g] using hdg
    · have hVcard : V.card ≤ 2 * l := by
        simpa only [V] using M.card_fiberExchangeReserve_le z l h2l
      have hVsub : V ⊆ B := by
        simpa only [V] using M.fiberExchangeReserve_subset z l h2l
      have hsplit : (B \ V).card + V.card = B.card :=
        Finset.card_sdiff_add_card_eq_card hVsub
      have hloss :
          C * (Nat.log 2 g *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * g) + 1))) =
          C * (Nat.log 2 (q₁.gcd q₂) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (q₁.gcd q₂)) + 1))) := by rfl
      rw [hloss]
      omega

/-- The complete Nguyen--Vu Section 8 concentration/spread dichotomy for an
ordinary rank-two cover.  The concentrated branch freezes one coordinate;
the spread branch reserves the extreme coordinates and invokes the exchange
chain. -/
theorem rank_two_section8_square_or_common_divisor
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ l : ℕ}
    {Z : Finset ℤ} {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank)
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₁ : R.length ⟨0, by omega⟩ = L₁)
    (hl : 0 < l)
    (hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₂) + 1) ≤ l)
    (hshort : p * q₂ ≤ L₂)
    (hlong : 4 * (p * q₂) *
      (Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) + 1) ≤ L₂) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + Z.card *
          (2 * l +
            Nat.log 2 (q₁.gcd q₂) *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
            Nat.log 2 q₂ *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q₂) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  classical
  by_cases hconcentrated : ∀ z ∈ Z,
      ∀ h2l : 2 * l ≤ (M.fiber z).card,
        (∑ i : Fin l,
          (M.fiberFirst z (highIndex (by omega) i) -
            M.fiberFirst z (lowIndex (by omega) i))) < l
  · obtain ⟨D₀, hD₀B, hD₀card, hD₀res⟩ :=
      M.exists_concentrated_core hq₂ hq₂step hl hconcentrated
    have hfamily₀ : ∀ u ∈ D₀.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum := by
      intro u hu x hx y hy
      exact hfamily u (Finset.subsetSum_mono hD₀B hu) x hx y hy
    rcases rank_two_second_axis_square_or_common_divisor
        hp hq₂ hAN hfamily₀ hD₀res hshort hlong with
      hsquare | ⟨d, D, hDD₀, hd, _hdq₂, hDcard, hdiv⟩
    · exact Or.inl hsquare
    · right
      refine ⟨d, D, hDD₀.trans hD₀B, hd, ?_, hdiv⟩
      calc
        B.card ≤ D₀.card + Z.card * (2 * l) := hD₀card
        _ ≤ (D.card + Z.card *
              (Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1)))) + Z.card * (2 * l) := by
            gcongr
        _ ≤ D.card + Z.card *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) := by
            ring_nf
            omega
  · push Not at hconcentrated
    obtain ⟨z, hzZ, h2l, hgap⟩ := hconcentrated
    have hlm : l ≤ (M.fiber z).card := by omega
    have hcast := intCast_sum_exchangeDeltas
      (M.fiberFirst z) hlm (M.monotone_fiberFirst z)
    have hgapNat : l ≤
        (exchangeDeltas (M.fiberFirst z) hlm).sum := by
      have hgap' : (l : ℤ) ≤
        ∑ i : Fin l,
          (M.fiberFirst z (highIndex hlm i) -
            M.fiberFirst z (lowIndex hlm i)) := by
        simpa only using hgap
      rw [← hcast] at hgap'
      exact_mod_cast hgap'
    let g := q₁.gcd q₂
    have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
    have hgstep₀ : (g : ℤ) ∣ R.positiveForm.step
        ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ := by
      rw [← hq₁step]
      exact_mod_cast Nat.gcd_dvd_left q₁ q₂
    have hgstep₁ : (g : ℤ) ∣ R.positiveForm.step
        ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ := by
      rw [← hq₂step]
      exact_mod_cast Nat.gcd_dvd_right q₁ q₂
    have hresB : (usedPositiveResidues g B).card ≤ Z.card :=
      M.usedPositiveResidues_card_le_common_step hg hgstep₀ hgstep₁
    have hres : (usedPositiveResidues g
        (B \ M.fiberExchangeReserve z l h2l)).card ≤ Z.card := by
      calc
        (usedPositiveResidues g
            (B \ M.fiberExchangeReserve z l h2l)).card ≤
            (usedPositiveResidues g B).card := by
          apply Finset.card_le_card
          exact Finset.image_mono _ Finset.sdiff_subset
        _ ≤ Z.card := hresB
    rcases rank_two_spread_square_or_common_divisor M hp hq₁ hq₂
        hAN hfamily hq₁step hq₂step hL₁ z hlm h2l hgapNat
        hstep hshort hlong (by simpa only [g] using hres) with
      hsquare | ⟨d, D, hDB, hd, _hdg, hDcard, hdiv⟩
    · exact Or.inl hsquare
    · right
      refine ⟨d, D, hDB, hd, ?_, hdiv⟩
      have hZpos : 0 < Z.card := Finset.card_pos.mpr ⟨z, hzZ⟩
      let G := Nat.log 2 (q₁.gcd q₂) *
        (nvQuadraticAdjustmentConstant *
          (Nat.sqrt (p * (q₁.gcd q₂)) + 1))
      let Q := Nat.log 2 q₂ *
        (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q₂) + 1))
      have htwo : 2 * l ≤ Z.card * (2 * l) := by
        calc
          2 * l = 1 * (2 * l) := by simp
          _ ≤ Z.card * (2 * l) :=
            Nat.mul_le_mul_right (2 * l) (by omega)
      have hloss : D.card + 2 * l + Z.card * G ≤
          D.card + Z.card * (2 * l + G + Q) := by
        calc
          D.card + 2 * l + Z.card * G ≤
              D.card + Z.card * (2 * l) + Z.card * G := by omega
          _ ≤ D.card + Z.card * (2 * l + G + Q) := by
            dsimp only [G, Q]
            ring_nf
            omega
      exact hDcard.trans (by simpa only [G, Q] using hloss)

/-- The coordinate-swapped form of the Section 8 dichotomy, used when the
first side of the terminal rank-two progression is the long side. -/
theorem rank_two_section8_square_or_common_divisor_first_axis
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ l : ℕ}
    {Z : Finset ℤ} {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank)
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₂ : R.length ⟨1, by omega⟩ = L₂)
    (hl : 0 < l)
    (hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₁) + 1) ≤ l)
    (hshort : p * q₁ ≤ L₁)
    (hlong : 4 * (p * q₁) *
      (Nat.sqrt ((A.card * N) / (p * q₁ ^ 2)) + 1) ≤ L₁) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + Z.card *
          (2 * l +
            Nat.log 2 (q₁.gcd q₂) *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
            Nat.log 2 q₁ *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q₁) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  let R' := R.rankTwoSwap hrank
  let hrank' : R'.rank = 2 := R.rank_rankTwoSwap hrank
  let M' : RankTwoCoverModel B Z R' hrank' := M.swap
  have hfamily' : ∀ u ∈ B.subsetSum, ∀ x ≤ L₂, ∀ y ≤ L₁,
      r + u + q₂ * x + q₁ * y ∈ A.subsetSum := by
    intro u hu x hx y hy
    simpa only [add_assoc, add_comm, add_left_comm] using
      hfamily u hu y hy x hx
  have hq₂step' : (q₂ : ℤ) = R'.positiveForm.step
      ⟨0, by simp [R', GeneralizedAP.rank_positiveForm]⟩ := by
    simpa only [R', GeneralizedAP.positiveForm_step_rankTwoSwap_zero] using
      hq₂step
  have hq₁step' : (q₁ : ℤ) = R'.positiveForm.step
      ⟨1, by simp [R', GeneralizedAP.rank_positiveForm]⟩ := by
    simpa only [R', GeneralizedAP.positiveForm_step_rankTwoSwap_one] using
      hq₁step
  have hL₂' : R'.length ⟨0, by omega⟩ = L₂ := by
    simpa only [R', GeneralizedAP.length_rankTwoSwap_zero] using hL₂
  simpa only [Nat.gcd_comm] using
    (rank_two_section8_square_or_common_divisor M' hp hq₂ hq₁ hAN
      hfamily' hq₂step' hq₁step' hL₂' hl hstep hshort hlong)

/-- Compose the stopped iterated-difference cover with the ordinary-box
tiling, then run Section 8 with the second coordinate as the long axis. -/
theorem rank_two_section8_of_iteratedDifference_cover
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ l n : ℕ}
    {Z : Finset ℤ} {R : GeneralizedAP} {hrank : R.rank = 2}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₁ : R.length ⟨0, by omega⟩ = L₁)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hl : 0 < l)
    (hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₂) + 1) ≤ l)
    (hshort : p * q₂ ≤ L₂)
    (hlong : 4 * (p * q₂) *
      (Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) + 1) ≤ L₂) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card +
          Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  classical
  obtain ⟨Z', hZ', hcover'⟩ :=
    exists_rank_two_carrier_translate_cover_of_iteratedDifference_cover
      R hrank n hcover
  let M : RankTwoCoverModel B Z' R hrank :=
    Classical.choice (exists_rankTwoCoverModel R hrank hcover')
  rcases rank_two_section8_square_or_common_divisor M hp hq₁ hq₂
      hAN hfamily hq₁step hq₂step hL₁ hl hstep hshort hlong with
    hsquare | ⟨d, D, hDB, hd, hcard, hdiv⟩
  · exact Or.inl hsquare
  · right
    refine ⟨d, D, hDB, hd, ?_, hdiv⟩
    calc
      B.card ≤ D.card + Z'.card *
          (2 * l +
            Nat.log 2 (q₁.gcd q₂) *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
            Nat.log 2 q₂ *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q₂) + 1))) := hcard
      _ ≤ D.card +
          (Z.card * (2 * (2 ^ n) + 1) ^ 2) *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) := by gcongr
      _ = D.card +
          Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) := by ring

/-- Coordinate-swapped stopped-cover form of Section 8. -/
theorem rank_two_section8_of_iteratedDifference_cover_first_axis
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ l n : ℕ}
    {Z : Finset ℤ} {R : GeneralizedAP} {hrank : R.rank = 2}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₂ : R.length ⟨1, by omega⟩ = L₂)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hl : 0 < l)
    (hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₁) + 1) ≤ l)
    (hshort : p * q₁ ≤ L₁)
    (hlong : 4 * (p * q₁) *
      (Nat.sqrt ((A.card * N) / (p * q₁ ^ 2)) + 1) ≤ L₁) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card +
          Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₁ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₁) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  classical
  obtain ⟨Z', hZ', hcover'⟩ :=
    exists_rank_two_carrier_translate_cover_of_iteratedDifference_cover
      R hrank n hcover
  let M : RankTwoCoverModel B Z' R hrank :=
    Classical.choice (exists_rankTwoCoverModel R hrank hcover')
  rcases rank_two_section8_square_or_common_divisor_first_axis M hp hq₁ hq₂
      hAN hfamily hq₁step hq₂step hL₂ hl hstep hshort hlong with
    hsquare | ⟨d, D, hDB, hd, hcard, hdiv⟩
  · exact Or.inl hsquare
  · right
    refine ⟨d, D, hDB, hd, ?_, hdiv⟩
    calc
      B.card ≤ D.card + Z'.card *
          (2 * l +
            Nat.log 2 (q₁.gcd q₂) *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
            Nat.log 2 q₁ *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q₁) + 1))) := hcard
      _ ≤ D.card +
          (Z.card * (2 * (2 ^ n) + 1) ^ 2) *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₁ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₁) + 1))) := by gcongr
      _ = D.card +
          Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₁ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₁) + 1))) := by ring

/-- Properness of a positive rank-two progression gives the precise
normalized-step dichotomy behind Nguyen--Vu's orientation in Section 10. -/
lemma normalized_step_opposite_side_dichotomy
    {r q₁ q₂ L₁ L₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hinj : ∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
      ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
        r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
        x₁ = x₂ ∧ y₁ = y₂) :
    L₁ < q₂ / q₁.gcd q₂ ∨ L₂ < q₁ / q₁.gcd q₂ := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hga : g * a = q₁ := by
    dsimp only [g, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hgb : g * b = q₂ := by
    dsimp only [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have hb : 0 < b := by
    dsimp only [b, g]
    exact Nat.div_pos
      (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hg
  change L₁ < b ∨ L₂ < a
  by_contra hnot
  push Not at hnot
  have hcollision :
      r + q₁ * b + q₂ * 0 = r + q₁ * 0 + q₂ * a := by
    rw [← hga, ← hgb]
    ring
  have heq := hinj b hnot.1 0 (Nat.zero_le L₂)
    0 (Nat.zero_le L₁) a hnot.2 hcollision
  omega

/-- After orienting the two sides so that the second coordinate contributes
at least as much span as the first, properness forces the normalized second
step strictly past the first side length. -/
lemma normalized_second_step_gt_first_side
    {r q₁ q₂ L₁ L₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hinj : ∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
      ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
        r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
        x₁ = x₂ ∧ y₁ = y₂)
    (horient : q₁ * L₁ ≤ q₂ * L₂) :
    L₁ < q₂ / q₁.gcd q₂ := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hga : g * a = q₁ := by
    dsimp only [g, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hgb : g * b = q₂ := by
    dsimp only [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  change L₁ < b
  rcases normalized_step_opposite_side_dichotomy hq₁ hq₂ hinj with
    hL₁ | hL₂
  · exact hL₁
  · have hb : 0 < b := by
      dsimp only [b, g]
      exact Nat.div_pos
        (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hg
    by_contra hnot
    have hbL₁ : b ≤ L₁ := Nat.le_of_not_gt hnot
    have hprod : b * L₂ < a * L₁ := by
      calc
        b * L₂ < b * a := (Nat.mul_lt_mul_left hb).2 hL₂
        _ ≤ L₁ * a := Nat.mul_le_mul_right a hbL₁
        _ = a * L₁ := by ring
    have hgprod : g * (b * L₂) < g * (a * L₁) :=
      (Nat.mul_lt_mul_left hg).2 hprod
    have : q₂ * L₂ < q₁ * L₁ := by
      calc
        q₂ * L₂ = g * (b * L₂) := by rw [← hgb]; ring
        _ < g * (a * L₁) := hgprod
        _ = q₁ * L₁ := by rw [← hga]; ring
    omega

/-- The elementary rectangle-capacity calculation in Nguyen--Vu
Proposition 10.1.  The first coordinate is restricted to
`[L₁ / 8, 2 * (L₁ / 8)]`; the quadratic interval uses one two-hundred-and-
fifty-sixth of the available normalized second-coordinate span. -/
lemma nguyen_vu_balanced_rectangle_capacity
    {p g a b L₁ L₂ H : ℕ} (hp : 0 < p) (hg : 0 < g)
    (horient : a * L₁ ≤ b * L₂)
    (hspan : g * (b * L₂) ≤ H)
    (hbig : 256 * (p * g) *
        (Nat.sqrt (H / (p * g ^ 2)) + 1) ≤ b * L₂) :
    let S := Nat.sqrt (H / (p * g ^ 2)) + 1
    let X := L₁ / 8
    let Hx := L₁ / 8
    let L := (b * L₂) / (256 * (p * g) * S)
    0 < L ∧ X + Hx ≤ L₁ ∧ L ≤ 2 * S ∧
      a * Hx + 32 * (p * g) * S * (L + 1) ≤ b * L₂ := by
  dsimp only
  let S := Nat.sqrt (H / (p * g ^ 2)) + 1
  let Q := b * L₂
  let c := p * g
  let den := 256 * c * S
  let X := L₁ / 8
  let L := Q / den
  have hc : 0 < c := Nat.mul_pos hp hg
  have hS : 0 < S := by dsimp only [S]; omega
  have hden : 0 < den := by dsimp only [den]; positivity
  have hdenQ : den ≤ Q := by simpa only [den, c, S, Q] using hbig
  have hL : 0 < L := by
    dsimp only [L]
    exact Nat.div_pos hdenQ hden
  have hXside : X + X ≤ L₁ := by
    dsimp only [X]
    omega
  have hambientSquare : H ≤ p * g ^ 2 * S ^ 2 := by
    simpa only [S] using
      le_mul_sq_succ_sqrt_div (c := p * g ^ 2) (T := H) (by positivity)
  have hQsquare : Q ≤ c * S ^ 2 := by
    have hgQ : g * Q ≤ g * (c * S ^ 2) := by
      calc
        g * Q ≤ H := by simpa only [Q] using hspan
        _ ≤ p * g ^ 2 * S ^ 2 := hambientSquare
        _ = g * (c * S ^ 2) := by dsimp only [c]; ring
    exact Nat.le_of_mul_le_mul_left hgQ hg
  have hdenL : den * L ≤ Q := by
    dsimp only [L]
    exact Nat.mul_div_le Q den
  have hcSden : c * S ≤ den := by
    dsimp only [den]
    calc
      c * S = 1 * (c * S) := by simp
      _ ≤ 256 * (c * S) := Nat.mul_le_mul_right (c * S) (by omega)
      _ = 256 * c * S := by ring
  have hcSL : (c * S) * L ≤ (c * S) * S := by
    calc
      (c * S) * L ≤ den * L := Nat.mul_le_mul_right L hcSden
      _ ≤ Q := hdenL
      _ ≤ c * S ^ 2 := hQsquare
      _ = (c * S) * S := by ring
  have hLS : L ≤ S :=
    Nat.le_of_mul_le_mul_left hcSL (Nat.mul_pos hc hS)
  have haX : 8 * (a * X) ≤ Q := by
    calc
      8 * (a * X) = a * (8 * X) := by ring
      _ ≤ a * L₁ := Nat.mul_le_mul_left a (by dsimp only [X]; omega)
      _ ≤ Q := by simpa only [Q] using horient
  have hdenSucc : den * (L + 1) ≤ 2 * Q := by
    calc
      den * (L + 1) = den * L + den := by ring
      _ ≤ Q + Q := Nat.add_le_add hdenL hdenQ
      _ = 2 * Q := by ring
  have hquad : 4 * (32 * c * S * (L + 1)) ≤ Q := by
    have htwice :
        2 * (4 * (32 * c * S * (L + 1))) = den * (L + 1) := by
      dsimp only [den]
      ring
    have : 2 * (4 * (32 * c * S * (L + 1))) ≤ 2 * Q := by
      simpa only [htwice] using hdenSucc
    omega
  refine ⟨hL, hXside, hLS.trans (Nat.le_mul_of_pos_left S (by omega)), ?_⟩
  have hsum : 8 * (a * X + 32 * c * S * (L + 1)) ≤ 3 * Q := by
    calc
      8 * (a * X + 32 * c * S * (L + 1)) =
          8 * (a * X) + 2 * (4 * (32 * c * S * (L + 1))) := by ring
      _ ≤ Q + 2 * Q := Nat.add_le_add haX (Nat.mul_le_mul_left 2 hquad)
      _ = 3 * Q := by ring
  have : a * X + 32 * c * S * (L + 1) ≤ Q := by omega
  simpa only [X, L, Q, c, S] using this

/-- The stopped cubic invariant gives the quantitative product lower bound
used twice in Nguyen--Vu's estimates (34) and (35). -/
lemma configured_rank_two_side_product_lower_bound
    {A : Finset ℕ} {N₀ s b L₁ L₂ : ℕ}
    (hA2 : 2 ≤ A.card)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)))
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    A.card * (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 ≤
      12 * nvMasterConstant ^ 2 * (L₁ * L₂) := by
  let X := nvCubicScale N₀ * nvInitialPolylog N₀
  have hX : 0 < X := Nat.mul_pos (nvCubicScale_pos N₀)
    (nvInitialPolylog_pos N₀)
  have hbudget := rank_two_cubic_budget_upper hW hscaled hDU
  have hsucc : (L₁ + 1) * (L₂ + 1) ≤ 4 * (L₁ * L₂) :=
    succ_side_product_le_four_mul hL₁ hL₂
  have hhalf : (A.card / 2) * X ^ 2 ≤
      4 * nvMasterConstant ^ 2 * (L₁ * L₂) := by
    have hmul : ((A.card / 2) * X ^ 2) * X ≤
        (4 * nvMasterConstant ^ 2 * (L₁ * L₂)) * X := by
      calc
        ((A.card / 2) * X ^ 2) * X = (A.card / 2) * X ^ 3 := by ring
        _ ≤ nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
            ((L₁ + 1) * (L₂ + 1)) * X := by
          simpa only [X] using hbudget
        _ ≤ nvMasterConstant * nvMasterConstant *
            (4 * (L₁ * L₂)) * X := by
          gcongr
          · exact nvRobustCubicLoss_le_master
          · exact nvStoppedBudgetFactor_le_master
        _ = (4 * nvMasterConstant ^ 2 * (L₁ * L₂)) * X := by ring
    exact Nat.le_of_mul_le_mul_right hmul hX
  have hcardHalf : A.card ≤ 3 * (A.card / 2) := by omega
  calc
    A.card * X ^ 2 ≤ (3 * (A.card / 2)) * X ^ 2 :=
      Nat.mul_le_mul_right (X ^ 2) hcardHalf
    _ = 3 * ((A.card / 2) * X ^ 2) := by ring
    _ ≤ 3 * (4 * nvMasterConstant ^ 2 * (L₁ * L₂)) :=
      Nat.mul_le_mul_left 3 hhalf
    _ = 12 * nvMasterConstant ^ 2 * (L₁ * L₂) := by ring

/-- A fixed finite threshold used only to turn the asymptotic phrase
"for sufficiently large `N`" in Nguyen--Vu into a concrete hypothesis. -/
def nvBalancedScaleThreshold : ℕ := 2 ^ 40

/-- The structural product lower bound makes the canonical quadratic
interval nonempty.  This is the finite form of the size calculation below
Nguyen--Vu equation (30). -/
lemma configured_balanced_rectangle_is_large
    {A : Finset ℕ} {N N₀ p g L₁ L₂ Q : ℕ}
    (hp : 0 < p) (hg : 0 < g) (hA : 0 < A.card)
    (hpN : p * N ≤ N₀)
    (hscale : nvBalancedScaleThreshold ≤ nvCubicScale N₀)
    (hproduct : A.card *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 ≤
      12 * nvMasterConstant ^ 2 * (L₁ * L₂))
    (hPQ : L₁ * L₂ ≤ Q)
    (hspan : g * Q ≤ A.card * N)
    (hcommon : p * g * nvInitialPolylog N₀ ^ 2 ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀)
    (hmasterCard : 12 * nvMasterConstant ^ 2 ≤ A.card) :
    256 * (p * g) *
        (Nat.sqrt ((A.card * N) / (p * g ^ 2)) + 1) ≤ Q := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let M₀ := nvInitialPolylog N₀
  let X := S * M₀
  let m := A.card
  let H := m * N
  let c := p * g
  let P := L₁ * L₂
  let R := Nat.sqrt (H / (p * g ^ 2)) + 1
  let K := 12 * C ^ 2
  have hC : 0 < C := nvMasterConstant_pos
  have hS : 0 < S := nvCubicScale_pos N₀
  have hM₀ : 0 < M₀ := nvInitialPolylog_pos N₀
  have hX : 0 < X := Nat.mul_pos hS hM₀
  have hm : 0 < m := by simpa only [m] using hA
  have hc : 0 < c := by dsimp only [c]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hthreshold : 12 ^ 2 * 524288 * 64 ≤ S := by
    calc
      12 ^ 2 * 524288 * 64 ≤ nvBalancedScaleThreshold := by
        norm_num [nvBalancedScaleThreshold]
      _ ≤ nvCubicScale N₀ := hscale
      _ = S := rfl
  have hN₀pos : 0 < N₀ := by
    by_contra hnot
    have hzero : N₀ = 0 := Nat.eq_zero_of_not_pos hnot
    subst N₀
    norm_num [nvBalancedScaleThreshold, S, nvCubicScale] at hscale
  have hN₀S : N₀ ≤ 64 * S ^ 3 := by
    simpa only [S, nvCubicScale] using
      ambient_le_sixty_four_mul_scale_cube hN₀pos
  have hM₀C : C ≤ M₀ := by
    dsimp only [M₀, C, nvInitialPolylog]
    exact Nat.le_mul_of_pos_right _
      (pow_pos (nvBinaryLogScale_pos N₀) nvInitialLogExponent)
  have hcrude : K ^ 2 * 524288 * N₀ ≤ m * X ^ 4 := by
    calc
      K ^ 2 * 524288 * N₀ ≤ K ^ 2 * 524288 * (64 * S ^ 3) := by gcongr
      _ = (12 ^ 2 * 524288 * 64) * C ^ 4 * S ^ 3 := by
        dsimp only [K]
        ring
      _ ≤ S * C ^ 4 * S ^ 3 := by gcongr
      _ = C ^ 4 * S ^ 4 := by ring
      _ ≤ M₀ ^ 4 * S ^ 4 := by gcongr
      _ = X ^ 4 := by dsimp only [X]; ring
      _ ≤ m * X ^ 4 := Nat.le_mul_of_pos_left _ hm
  have hpH : p * H ≤ m * N₀ := by
    dsimp only [H, m]
    calc
      p * (A.card * N) = A.card * (p * N) := by ring
      _ ≤ A.card * N₀ := Nat.mul_le_mul_left A.card hpN
  have hKP : m * X ^ 2 ≤ K * P := by
    simpa only [m, X, K, P, C] using hproduct
  have hlargeSquare : 524288 * (p * H) ≤ P ^ 2 := by
    have hleft : K ^ 2 * (524288 * (p * H)) ≤
        (m * X ^ 2) ^ 2 := by
      calc
        K ^ 2 * (524288 * (p * H)) ≤
            K ^ 2 * (524288 * (m * N₀)) := by gcongr
        _ = m * (K ^ 2 * 524288 * N₀) := by ring
        _ ≤ m * (m * X ^ 4) := Nat.mul_le_mul_left m hcrude
        _ = (m * X ^ 2) ^ 2 := by ring
    have hright : (m * X ^ 2) ^ 2 ≤ (K * P) ^ 2 :=
      Nat.pow_le_pow_left hKP 2
    have hmul : K ^ 2 * (524288 * (p * H)) ≤ K ^ 2 * P ^ 2 := by
      calc
        K ^ 2 * (524288 * (p * H)) ≤ (m * X ^ 2) ^ 2 := hleft
        _ ≤ (K * P) ^ 2 := hright
        _ = K ^ 2 * P ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos hK 2)
  have hcX : c ≤ X ^ 2 := by
    have h768 : 768 ≤ S := by omega
    have hcM : c * M₀ ^ 2 ≤ 768 * C ^ 2 * S := by
      simpa only [c, C, S, M₀] using hcommon
    have hc0 : c ≤ c * M₀ ^ 2 :=
      Nat.le_mul_of_pos_right c (pow_pos hM₀ 2)
    calc
      c ≤ c * M₀ ^ 2 := hc0
      _ ≤ 768 * C ^ 2 * S := hcM
      _ ≤ S * C ^ 2 * S := by gcongr
      _ ≤ S * M₀ ^ 2 * S := by gcongr
      _ = X ^ 2 := by dsimp only [X]; ring
  have hXP : X ^ 2 ≤ P := by
    have hmul : m * X ^ 2 ≤ m * P := by
      calc
        m * X ^ 2 ≤ K * P := hKP
        _ ≤ m * P := Nat.mul_le_mul_right P (by
          simpa only [m, K, C] using hmasterCard)
    exact Nat.le_of_mul_le_mul_left hmul hm
  have hcQ : c ≤ Q := hcX.trans (hXP.trans hPQ)
  have hcSq : c ^ 2 ≤ p * H := by
    calc
      c ^ 2 = p * (g * c) := by dsimp only [c]; ring
      _ ≤ p * (g * Q) := by gcongr
      _ ≤ p * H := Nat.mul_le_mul_left p (by simpa only [H] using hspan)
  let T := H / (p * g ^ 2)
  have hcT : c ^ 2 * T ≤ p * H := by
    calc
      c ^ 2 * T = p * ((p * g ^ 2) * T) := by
        dsimp only [c]
        ring
      _ ≤ p * H := Nat.mul_le_mul_left p (by
        dsimp only [T]
        exact Nat.mul_div_le H (p * g ^ 2))
  have hR : R ^ 2 ≤ 4 * (T + 1) := by
    have hsqrtSq := Nat.sqrt_le T
    have hsqrtSelf := Nat.sqrt_le_self T
    dsimp only [R]
    nlinarith
  have hcR : (c * R) ^ 2 ≤ 8 * (p * H) := by
    calc
      (c * R) ^ 2 = c ^ 2 * R ^ 2 := by ring
      _ ≤ c ^ 2 * (4 * (T + 1)) := Nat.mul_le_mul_left (c ^ 2) hR
      _ = 4 * (c ^ 2 * T + c ^ 2) := by ring
      _ ≤ 4 * (p * H + p * H) := by gcongr
      _ = 8 * (p * H) := by ring
  have htargetSq : (256 * c * R) ^ 2 ≤ P ^ 2 := by
    calc
      (256 * c * R) ^ 2 = 65536 * (c * R) ^ 2 := by ring
      _ ≤ 65536 * (8 * (p * H)) := Nat.mul_le_mul_left 65536 hcR
      _ = 524288 * (p * H) := by ring
      _ ≤ P ^ 2 := hlargeSquare
  have htarget : 256 * c * R ≤ P := by
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp htargetSq
  exact_mod_cast (show 256 * c * R ≤ Q from htarget.trans hPQ)

/-- The canonical Nguyen--Vu Fourier cutoff is inverse to the available
first-coordinate smoothing width.  In the source notation this is the
elementary estimate `L₀ L₁ ≪ q₂ log q₂`. -/
lemma canonical_balanced_cutoff_mul_side_le
    {b L₁ Hx : ℕ}
    (hb : 0 < b) (hside : 16 ≤ L₁) (hHx : Hx = L₁ / 8)
    (hproper : L₁ < b) :
    nvBalancedCutoff b Hx * L₁ ≤
      32 * b * nvBalancedMoment b := by
  let k := nvBalancedMoment b
  let U := nvBalancedWidth b Hx
  let M := nvBalancedCutoff b Hx
  have hk : 0 < k := nvBalancedMoment_pos b
  have hHxpos : 0 < Hx := by
    rw [hHx]
    omega
  have hU : 0 < U := nvBalancedWidth_pos b Hx
  have hHxkU : Hx ≤ k * U := by
    change Hx ≤ k * (Hx / k + 1)
    have hraw : Hx < Hx / k * k + k := Nat.lt_div_mul_add hk
    simpa only [mul_add, mul_one, Nat.mul_comm] using hraw.le
  have hdiv : b / U * U ≤ b := Nat.div_mul_le_self b U
  have hcutHx : M * Hx ≤ 2 * b * k := by
    have hmain : (b / U) * Hx ≤ b * k := by
      calc
        (b / U) * Hx ≤ (b / U) * (k * U) :=
          Nat.mul_le_mul_left (b / U) hHxkU
        _ = (b / U * U) * k := by ring
        _ ≤ b * k := Nat.mul_le_mul_right k hdiv
    have hsmall : Hx ≤ b * k := by
      calc
        Hx ≤ L₁ := by rw [hHx]; omega
        _ ≤ b := hproper.le
        _ = b * 1 := by simp
        _ ≤ b * k := Nat.mul_le_mul_left b hk
    change (b / U + 1) * Hx ≤ 2 * b * k
    rw [add_mul]
    calc
      b / U * Hx + 1 * Hx ≤ b * k + b * k :=
        Nat.add_le_add hmain (by simpa using hsmall)
      _ = 2 * b * k := by ring
  have hL₁Hx : L₁ ≤ 16 * Hx := by
    rw [hHx]
    omega
  calc
    nvBalancedCutoff b Hx * L₁ = M * L₁ := rfl
    _ ≤ M * (16 * Hx) := Nat.mul_le_mul_left M hL₁Hx
    _ = 16 * (M * Hx) := by ring
    _ ≤ 16 * (2 * b * k) := Nat.mul_le_mul_left 16 hcutHx
    _ = 32 * b * nvBalancedMoment b := by simp only [k]; ring

/-- If one side of the terminal rank-two box is shorter than a prescribed
scale, the stopped cubic budget forces the other side past any comparison
length whose substituted upper bound is smaller than that budget. -/
lemma rank_two_second_side_gt_of_cubic_budget
    {W C b D F L₁ L₂ U X T : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ^ 2 ≤ F * ((L₁ + 1) * (L₂ + 1)))
    (hDU : D ≤ U) (hL₁X : L₁ + 1 ≤ X)
    (hlarge : C * F * (T + 1) * U * X < W) :
    T < L₂ := by
  have hupper := rank_two_cubic_budget_upper hW hscaled hDU
  by_contra hnot
  have hL₂T : L₂ + 1 ≤ T + 1 := by omega
  have hbound :
      C * F * ((L₁ + 1) * (L₂ + 1)) * U ≤
        C * F * (X * (T + 1)) * U := by gcongr
  have : W ≤ C * F * (T + 1) * U * X := by
    calc
      W ≤ C * F * ((L₁ + 1) * (L₂ + 1)) * U := hupper
      _ ≤ C * F * (X * (T + 1)) * U := hbound
      _ = C * F * (T + 1) * U * X := by ring
  omega

/-- The complete Section 8 reserve cost, including the bounded box tiling,
is absorbed by the configured one-step loss. -/
lemma configured_section8_loss_bound
    {N₀ p q g n : ℕ}
    (hN₀ : 0 < N₀) (hq : 0 < q) (hg : 0 < g)
    (hgq : g ≤ q) (hqN : q ≤ N₀ ^ 2)
    (hpq : p * q ≤
      1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2)
    (hn : n ≤ freimanRank (64 ^ 2) + 2) :
    nvStoppedRemainderTranslateCount 65 64 *
        (2 * (2 ^ n) + 1) ^ 2 *
        (2 * (nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1) +
          Nat.log 2 g *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * g) + 1)) +
          Nat.log 2 q *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
      nvOneStepLoss N₀ := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let ell := nvBinaryLogScale N₀
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have hCpos : 0 < C := by omega
  have hS : 0 < S := nvCubicScale_pos N₀
  have hell : 0 < ell := nvBinaryLogScale_pos N₀
  have hgN : g ≤ N₀ ^ 2 := hgq.trans hqN
  have hlogq : Nat.log 2 q ≤ 2 * ell := by
    simpa only [ell] using
      log_two_le_twice_binaryLogScale_of_le_square hq hN₀ hqN
  have hlogg : Nat.log 2 g ≤ 2 * ell := by
    simpa only [ell] using
      log_two_le_twice_binaryLogScale_of_le_square hg hN₀ hgN
  have hsquareq : p * q ≤ (32 * C * S) ^ 2 := by
    calc
      p * q ≤ 1024 * C ^ 2 * S ^ 2 := by
        simpa only [C, S] using hpq
      _ = (32 * C * S) ^ 2 := by ring
  have hsqrtq : Nat.sqrt (p * q) + 1 ≤ 33 * C * S := by
    have hraw := sqrt_succ_le_of_le_square hsquareq
    have hone : 1 ≤ C * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc
      Nat.sqrt (p * q) + 1 ≤ 32 * C * S + 1 := by simpa using hraw
      _ ≤ 33 * C * S := by nlinarith
  have hpg : p * g ≤ p * q := Nat.mul_le_mul_left p hgq
  have hsqrtg : Nat.sqrt (p * g) + 1 ≤ 33 * C * S := by
    exact (Nat.add_le_add_right (Nat.sqrt_le_sqrt hpg) 1).trans hsqrtq
  have hpown : 2 ^ n ≤ 2 ^ (freimanRank (64 ^ 2) + 2) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
  have hbox : (2 * (2 ^ n) + 1) ^ 2 ≤ C := by
    calc
      (2 * (2 ^ n) + 1) ^ 2 ≤
          (2 * (2 ^ (freimanRank (64 ^ 2) + 2)) + 1) ^ 2 := by
            apply Nat.pow_le_pow_left _ 2
            omega
      _ = nvSection8BoxConstant := by rfl
      _ ≤ C := by simpa only [C] using nvSection8BoxConstant_le_master
  have hl :
      nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1 ≤
        34 * C ^ 2 * S := by
    calc
      nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1 ≤
          C * (33 * C * S) + 1 := by
            gcongr
            exact nvQuadraticStepConstant_le_master
      _ ≤ 34 * C ^ 2 * S := by
        have hone : 1 ≤ C ^ 2 * S :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith
  have hadj : nvQuadraticAdjustmentConstant ≤ C := by
    simpa only [C] using nvQuadraticAdjustmentConstant_le_master
  have hinner :
      2 * (nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1) +
          Nat.log 2 g *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * g) + 1)) +
          Nat.log 2 q *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1)) ≤
        200 * C ^ 2 * S * ell := by
    calc
      2 * (nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1) +
          Nat.log 2 g *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * g) + 1)) +
          Nat.log 2 q *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1)) ≤
        2 * (34 * C ^ 2 * S) +
          (2 * ell) * (C * (33 * C * S)) +
          (2 * ell) * (C * (33 * C * S)) := by gcongr
      _ ≤ 200 * C ^ 2 * S * ell := by
        have : 1 ≤ ell := by omega
        nlinarith
  have hraw :
      nvStoppedRemainderTranslateCount 65 64 *
          (2 * (2 ^ n) + 1) ^ 2 *
          (2 * (nvQuadraticStepConstant * (Nat.sqrt (p * q) + 1) + 1) +
            Nat.log 2 g *
              (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * g) + 1)) +
            Nat.log 2 q *
              (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
        200 * C ^ 4 * S * ell := by
    calc
      _ ≤ C * C * (200 * C ^ 2 * S * ell) := by
        gcongr
        exact nvRemainderTranslateCount_le_master
      _ = 200 * C ^ 4 * S * ell := by ring
  have hcoeff : 200 * C ^ 4 ≤ C ^ 10 := by
    have h200 : 200 ≤ C ^ 6 := by
      calc
        200 ≤ C := by omega
        _ = C ^ 1 := by simp
        _ ≤ C ^ 6 := Nat.pow_le_pow_right hCpos (by omega)
    calc
      200 * C ^ 4 ≤ C ^ 6 * C ^ 4 := Nat.mul_le_mul_right _ h200
      _ = C ^ 10 := by rw [← pow_add]
  have hpell : ell ^ 1 ≤ ell ^ nvLossLogExponent :=
    Nat.pow_le_pow_right hell (by
      have hE := nvLossLogExponent_pos
      omega)
  calc
    _ ≤ 200 * C ^ 4 * S * ell := hraw
    _ = (200 * C ^ 4) * S * ell ^ 1 := by ring
    _ ≤ C ^ 10 * S * ell ^ nvLossLogExponent := by gcongr
    _ = nvOneStepLoss N₀ := by simp only [nvOneStepLoss, C, S, ell]

/-- Configured Nguyen--Vu small-first-side branch.  The cubic stopping
budget forces the second side to be long, Section 8 produces the square or
common-divisor alternative, and the complete reserve cost is absorbed by one
configured loss. -/
theorem configured_rank_two_section8_second_axis
    {A B : Finset ℕ} {N N₀ p s b n r q₁ q₂ L₁ L₂ : ℕ}
    {R : GeneralizedAP} {Z : Finset ℤ} {hrank : R.rank = 2}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hL₁pos : 0 < L₁) (hL₂pos : 0 < L₂)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₁ : R.length ⟨0, by omega⟩ = L₁)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ nvStoppedRemainderTranslateCount 65 64)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)))
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N)
    (hn : n ≤ freimanRank (64 ^ 2) + 2)
    (hsmall : L₁ < nvCubicScale N₀ * nvInitialPolylog N₀) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + nvOneStepLoss N₀ ∧
        ∀ a ∈ D, d ∣ a := by
  let X := nvCubicScale N₀ * nvInitialPolylog N₀
  let H := A.card * N
  let T := 8 * (Nat.sqrt (p * H) + 1)
  have hL₁X : L₁ + 1 ≤ X := by
    dsimp only [X]
    omega
  have hdominance := configured_rank_one_terminal_dominance
    hp hpN hAN hlarge nvRobustCubicLoss_le_master
      nvStoppedBudgetFactor_le_master
  have hlarge' :
      nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (T + 1) * X * X <
        (A.card / 2) * X ^ 3 := by
    change nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (8 * (Nat.sqrt (p * H) + 1) + 1) * X ^ 2 <
      (A.card / 2) * X ^ 3 at hdominance
    calc
      nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (T + 1) * X * X =
        nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (8 * (Nat.sqrt (p * H) + 1) + 1) * X ^ 2 := by
            simp only [T, pow_two]
            ring
      _ < (A.card / 2) * X ^ 3 := hdominance
  have hL₂large : T < L₂ :=
    rank_two_second_side_gt_of_cubic_budget hW hscaled hDU hL₁X hlarge'
  have hbig : 64 * p * H ≤ L₂ ^ 2 := by
    have hsqrt : p * H ≤ (Nat.sqrt (p * H) + 1) ^ 2 :=
      square_bound_of_sqrt_succ _
    have hTsq : T ^ 2 < L₂ ^ 2 := by nlinarith
    calc
      64 * p * H = 64 * (p * H) := by ring
      _ ≤ 64 * (Nat.sqrt (p * H) + 1) ^ 2 := by gcongr
      _ = T ^ 2 := by simp only [T]; ring
      _ ≤ L₂ ^ 2 := hTsq.le
  have hq₂L₂ : q₂ * L₂ ≤ H := by
    dsimp only [H]
    omega
  obtain ⟨hshort, hlong⟩ :=
    rank_one_location_bounds hp hq₂ hL₂pos hq₂L₂
      (by simpa only [H] using hbig)
  have hq₂W := rank_two_second_step_budget_upper
    hW hscaled hDU hL₂pos hq₂L₂
  have hq₂W' : q₂ * ((A.card / 2) * X ^ 3) ≤
      2 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        H * X ^ 2 := by
    calc
      q₂ * ((A.card / 2) * X ^ 3) ≤
          2 * nvRobustCubicLoss 64 *
            nvStoppedBudgetScaledCardFactor 64 * (L₁ + 1) * H * X := by
        simpa only [X] using hq₂W
      _ ≤ 2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * X * H * X := by gcongr
      _ = 2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * H * X ^ 2 := by ring
  have hA2 : 2 ≤ A.card := by
    have hloss := nvOneStepLoss_pos N₀
    have hell := nvBinaryLogScale_pos N
    have hmono : nvOneStepLoss N₀ ≤
        nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hpq₂ : p * q₂ ≤
      384 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
    apply configured_rank_one_step_bound hp hpN hAN hA2
    simpa only [X, H] using hq₂W'
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hq₂H : q₂ ≤ H := by
    calc
      q₂ = q₂ * 1 := by simp
      _ ≤ q₂ * L₂ := Nat.mul_le_mul_left q₂ (by omega)
      _ ≤ H := hq₂L₂
  have hq₂N₀ : q₂ ≤ N₀ ^ 2 := by
    have hcardN : A.card ≤ N := card_le_ambient_of_subset_Icc hAN
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    calc
      q₂ ≤ H := hq₂H
      _ ≤ N * N := by
        dsimp only [H]
        exact Nat.mul_le_mul_right N hcardN
      _ ≤ N₀ * N₀ := Nat.mul_le_mul hNN₀ hNN₀
      _ = N₀ ^ 2 := by ring
  let l := nvQuadraticStepConstant * (Nat.sqrt (p * q₂) + 1) + 1
  have hl : 0 < l := by dsimp only [l]; omega
  have hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₂) + 1) ≤ l := by
    dsimp only [l]
    omega
  rcases rank_two_section8_of_iteratedDifference_cover (hrank := hrank) hp hq₁ hq₂
      hAN hfamily hq₁step hq₂step hL₁ hcover hl hstep hshort hlong with
    hsquare | ⟨d, D, hDB, hd, hcard, hdiv⟩
  · exact Or.inl hsquare
  · right
    refine ⟨d, D, hDB, hd, ?_, hdiv⟩
    have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
    have hgq₂ : q₁.gcd q₂ ≤ q₂ := Nat.gcd_le_right q₁ hq₂
    have hpq₂' : p * q₂ ≤
        1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 :=
      hpq₂.trans (by gcongr; norm_num)
    have hloss := configured_section8_loss_bound hN₀pos hq₂ hg hgq₂
      hq₂N₀ hpq₂' hn
    have hcost :
        Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) ≤
          nvOneStepLoss N₀ := by
      calc
        _ ≤ nvStoppedRemainderTranslateCount 65 64 *
            (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₂ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₂) + 1))) := by gcongr
        _ ≤ nvOneStepLoss N₀ := by simpa only [l] using hloss
    exact hcard.trans (Nat.add_le_add_left hcost D.card)

/-- Configured Nguyen--Vu small-second-side branch, symmetric to
`configured_rank_two_section8_second_axis`. -/
theorem configured_rank_two_section8_first_axis
    {A B : Finset ℕ} {N N₀ p s b n r q₁ q₂ L₁ L₂ : ℕ}
    {R : GeneralizedAP} {Z : Finset ℤ} {hrank : R.rank = 2}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hL₁pos : 0 < L₁) (hL₂pos : 0 < L₂)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hL₂ : R.length ⟨1, by omega⟩ = L₂)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ nvStoppedRemainderTranslateCount 65 64)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)))
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N)
    (hn : n ≤ freimanRank (64 ^ 2) + 2)
    (hsmall : L₂ < nvCubicScale N₀ * nvInitialPolylog N₀) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + nvOneStepLoss N₀ ∧
        ∀ a ∈ D, d ∣ a := by
  let X := nvCubicScale N₀ * nvInitialPolylog N₀
  let H := A.card * N
  let T := 8 * (Nat.sqrt (p * H) + 1)
  have hL₂X : L₂ + 1 ≤ X := by
    dsimp only [X]
    omega
  have hdominance := configured_rank_one_terminal_dominance
    hp hpN hAN hlarge nvRobustCubicLoss_le_master
      nvStoppedBudgetFactor_le_master
  have hlarge' :
      nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (T + 1) * X * X <
        (A.card / 2) * X ^ 3 := by
    change nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (8 * (Nat.sqrt (p * H) + 1) + 1) * X ^ 2 <
      (A.card / 2) * X ^ 3 at hdominance
    calc
      nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (T + 1) * X * X =
        nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (8 * (Nat.sqrt (p * H) + 1) + 1) * X ^ 2 := by
            simp only [T, pow_two]
            ring
      _ < (A.card / 2) * X ^ 3 := hdominance
  have hscaled' : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₂ + 1) * (L₁ + 1)) := by
    simpa only [mul_comm] using hscaled
  have hL₁large : T < L₁ :=
    rank_two_second_side_gt_of_cubic_budget hW hscaled' hDU hL₂X hlarge'
  have hbig : 64 * p * H ≤ L₁ ^ 2 := by
    have hsqrt : p * H ≤ (Nat.sqrt (p * H) + 1) ^ 2 :=
      square_bound_of_sqrt_succ _
    have hTsq : T ^ 2 < L₁ ^ 2 := by nlinarith
    calc
      64 * p * H = 64 * (p * H) := by ring
      _ ≤ 64 * (Nat.sqrt (p * H) + 1) ^ 2 := by gcongr
      _ = T ^ 2 := by simp only [T]; ring
      _ ≤ L₁ ^ 2 := hTsq.le
  have hq₁L₁ : q₁ * L₁ ≤ H := by
    dsimp only [H]
    omega
  obtain ⟨hshort, hlong⟩ :=
    rank_one_location_bounds hp hq₁ hL₁pos hq₁L₁
      (by simpa only [H] using hbig)
  have hq₁W := rank_two_first_step_budget_upper
    hW hscaled hDU hL₁pos hq₁L₁
  have hq₁W' : q₁ * ((A.card / 2) * X ^ 3) ≤
      2 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        H * X ^ 2 := by
    calc
      q₁ * ((A.card / 2) * X ^ 3) ≤
          2 * nvRobustCubicLoss 64 *
            nvStoppedBudgetScaledCardFactor 64 * (L₂ + 1) * H * X := by
        simpa only [X] using hq₁W
      _ ≤ 2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * X * H * X := by gcongr
      _ = 2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * H * X ^ 2 := by ring
  have hA2 : 2 ≤ A.card := by
    have hloss := nvOneStepLoss_pos N₀
    have hell := nvBinaryLogScale_pos N
    have hmono : nvOneStepLoss N₀ ≤
        nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hpq₁ : p * q₁ ≤
      384 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
    apply configured_rank_one_step_bound hp hpN hAN hA2
    simpa only [X, H] using hq₁W'
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hq₁H : q₁ ≤ H := by
    calc
      q₁ = q₁ * 1 := by simp
      _ ≤ q₁ * L₁ := Nat.mul_le_mul_left q₁ (by omega)
      _ ≤ H := hq₁L₁
  have hq₁N₀ : q₁ ≤ N₀ ^ 2 := by
    have hcardN : A.card ≤ N := card_le_ambient_of_subset_Icc hAN
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    calc
      q₁ ≤ H := hq₁H
      _ ≤ N * N := by
        dsimp only [H]
        exact Nat.mul_le_mul_right N hcardN
      _ ≤ N₀ * N₀ := Nat.mul_le_mul hNN₀ hNN₀
      _ = N₀ ^ 2 := by ring
  let l := nvQuadraticStepConstant * (Nat.sqrt (p * q₁) + 1) + 1
  have hl : 0 < l := by dsimp only [l]; omega
  have hstep : nvQuadraticStepConstant * (Nat.sqrt (p * q₁) + 1) ≤ l := by
    dsimp only [l]
    omega
  rcases rank_two_section8_of_iteratedDifference_cover_first_axis
      (hrank := hrank) hp hq₁ hq₂ hAN hfamily hq₁step hq₂step hL₂
      hcover hl hstep hshort hlong with
    hsquare | ⟨d, D, hDB, hd, hcard, hdiv⟩
  · exact Or.inl hsquare
  · right
    refine ⟨d, D, hDB, hd, ?_, hdiv⟩
    have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
    have hgq₁ : q₁.gcd q₂ ≤ q₁ := Nat.gcd_le_left q₂ hq₁
    have hpq₁' : p * q₁ ≤
        1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 :=
      hpq₁.trans (by gcongr; norm_num)
    have hloss := configured_section8_loss_bound hN₀pos hq₁ hg hgq₁
      hq₁N₀ hpq₁' hn
    have hcost :
        Z.card * (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₁ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₁) + 1))) ≤
          nvOneStepLoss N₀ := by
      calc
        _ ≤ nvStoppedRemainderTranslateCount 65 64 *
            (2 * (2 ^ n) + 1) ^ 2 *
            (2 * l +
              Nat.log 2 (q₁.gcd q₂) *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * (q₁.gcd q₂)) + 1)) +
              Nat.log 2 q₁ *
                (nvQuadraticAdjustmentConstant *
                  (Nat.sqrt (p * q₁) + 1))) := by gcongr
        _ ≤ nvOneStepLoss N₀ := by simpa only [l] using hloss
    exact hcard.trans (Nat.add_le_add_left hcost D.card)

/-- The configured rank-two terminal theorem with both quantitative
small-side exits discharged.  Its only remaining input is the genuinely
balanced form of Proposition 10.1, where both side lengths dominate the
stopping scale. -/
theorem configured_rank_two_terminal_of_balanced_locator
    {A B : Finset ℕ} {N N₀ p s b n : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hR : R.Proper) (hrank : R.rank = 2)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hcontain : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ nvStoppedRemainderTranslateCount 65 64)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ R.rank ≤
      nvStoppedBudgetScaledCardFactor 64 * R.carrier.card)
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hn : n ≤ freimanRank (64 ^ 2) + 2)
    (hlocator : ∀ {r q₁ q₂ L₁ L₂ : ℕ},
      0 < q₁ → 0 < q₂ →
      (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
      (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
        ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
          r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
          x₁ = x₂ ∧ y₁ = y₂) →
      q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
      b * (2 ^ s) ^ 2 ≤
        nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
      nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₁ →
      nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₂ →
      (∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
        ((r + u : ℕ) : ℤ) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
          ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
            0 < p * w ^ 2 ∧
            r + u + q₁ * x + q₂ * y = p * w ^ 2)) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + nvOneStepLoss N₀ ∧
        ∀ a ∈ D, d ∣ a := by
  obtain ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂, _hrbase, hq₁step, hq₂step,
      hL₁, hL₂, hfamily, hinj⟩ :=
    exists_natGAP_two_family_of_translated_rank_two_GAP
      R t hR hrank hside hcontain
  have hL₁pos : 0 < L₁ := by
    simpa only [hL₁] using hside ⟨0, by omega⟩
  have hL₂pos : 0 < L₂ := by
    simpa only [hL₂] using hside ⟨1, by omega⟩
  have hscaled₂ : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) := by
    have hcard := carrier_card_eq_rank_two R hR hrank
    rw [hrank, hcard] at hscaled
    simpa only [hL₁, hL₂] using hscaled
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hzero : 0 ∈ B.subsetSum := by simp
  have hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N := by
    apply natGAP_two_span_le_of_subsetSum_bound hsumBound
    intro x hx y hy
    simpa only [Nat.add_zero] using hfamily 0 hzero x hx y hy
  let X := nvCubicScale N₀ * nvInitialPolylog N₀
  by_cases hL₁small : L₁ < X
  · exact configured_rank_two_section8_second_axis (hrank := hrank)
      hp hpN hAN hlarge
      hq₁ hq₂ hL₁pos hL₂pos hfamily hq₁step hq₂step hL₁.symm hcover hZ
      hW hscaled₂ hDU hspan hn (by simpa only [X] using hL₁small)
  by_cases hL₂small : L₂ < X
  · exact configured_rank_two_section8_first_axis (hrank := hrank)
      hp hpN hAN hlarge
      hq₁ hq₂ hL₁pos hL₂pos hfamily hq₁step hq₂step hL₂.symm hcover hZ
      hW hscaled₂ hDU hspan hn (by simpa only [X] using hL₂small)
  have hL₁large : X ≤ L₁ := Nat.le_of_not_gt hL₁small
  have hL₂large : X ≤ L₂ := Nat.le_of_not_gt hL₂small
  have hgspan : q₁.gcd q₂ * L₁ * L₂ ≤ A.card * N :=
    (gcd_mul_side_product_le_span_of_injective hq₁ hq₂ hinj).trans hspan
  have hgW : q₁.gcd q₂ * ((A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) ≤
      4 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) :=
    rank_two_common_step_budget_upper hW hscaled₂ hDU hL₁pos hL₂pos hgspan
  have hA2 : 2 ≤ A.card := by
    have hloss := nvOneStepLoss_pos N₀
    have hell := nvBinaryLogScale_pos N
    have hmono : nvOneStepLoss N₀ ≤
        nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hpgM : p * q₁.gcd q₂ * nvInitialPolylog N₀ ^ 2 ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀ :=
    configured_rank_two_common_step_bound hp hpN hAN hA2 hgW
  have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hM : 0 < nvInitialPolylog N₀ := nvInitialPolylog_pos N₀
  have hpg : p * q₁.gcd q₂ ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀ := by
    have hmono : p * q₁.gcd q₂ ≤
        p * q₁.gcd q₂ * nvInitialPolylog N₀ ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos hM 2)
    exact hmono.trans hpgM
  have hpg' : p * q₁.gcd q₂ ≤
      1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
    calc
      p * q₁.gcd q₂ ≤ 768 * nvMasterConstant ^ 2 * nvCubicScale N₀ := hpg
      _ ≤ 1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ := by gcongr; norm_num
      _ ≤ 1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
        gcongr
        have hS := nvCubicScale_pos N₀
        calc
          nvCubicScale N₀ = nvCubicScale N₀ * 1 := by simp
          _ ≤ nvCubicScale N₀ * nvCubicScale N₀ := by gcongr; omega
          _ = nvCubicScale N₀ ^ 2 := by ring
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hgH : q₁.gcd q₂ ≤ A.card * N := by
    calc
      q₁.gcd q₂ ≤ q₁ := Nat.gcd_le_left q₂ hq₁
      _ = q₁ * 1 := by simp
      _ ≤ q₁ * L₁ := Nat.mul_le_mul_left q₁ (by omega)
      _ ≤ q₁ * L₁ + q₂ * L₂ := Nat.le_add_right _ _
      _ ≤ A.card * N := hspan
  have hgN₀ : q₁.gcd q₂ ≤ N₀ ^ 2 := by
    have hcardN : A.card ≤ N := card_le_ambient_of_subset_Icc hAN
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    calc
      q₁.gcd q₂ ≤ A.card * N := hgH
      _ ≤ N * N := Nat.mul_le_mul_right N hcardN
      _ ≤ N₀ * N₀ := Nat.mul_le_mul hNN₀ hNN₀
      _ = N₀ ^ 2 := by ring
  rcases rank_two_square_or_common_divisor_of_locator hp hq₁ hq₂
      hR hrank hside hq₁step hq₂step hfamily hcover hZ
      (hlocator hq₁ hq₂ hfamily hinj hspan hscaled₂
        (by simpa only [X] using hL₁large)
        (by simpa only [X] using hL₂large)) with
    hsquare | ⟨d, D, hDB, hd, _hdg, hcard, hdiv⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨d, D, hDB, hd, ?_, hdiv⟩
    have hloss := configured_residue_loss_bound hN₀pos hg hgN₀ hpg'
    exact hcard.trans (Nat.add_le_add_left hloss D.card)

/-- Complete one configured Nguyen--Vu divisor-descent step, with the
remaining Proposition 10.1 input restricted to the balanced rank-two case.
The unbalanced cases are discharged by the two Section 8 arguments above. -/
theorem configured_nguyen_vu_one_step_of_balanced_rank_two_locator
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hlocator : ∀ {B : Finset ℕ} {s b r q₁ q₂ L₁ L₂ : ℕ},
      B ⊆ A → A.card - nvOneStepLoss N₀ ≤ B.card →
      0 < q₁ → 0 < q₂ →
      (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
      (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
        ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
          r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
          x₁ = x₂ ∧ y₁ = y₂) →
      q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
      (A.card / 2) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
        nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3 →
      b * (2 ^ s) ^ 2 ≤
        nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
      2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀ →
      nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₁ →
      nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₂ →
      ∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
        ((r + u : ℕ) : ℤ) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
          ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
            0 < p * w ^ 2 ∧
            r + u + q₁ * x + q₂ * y = p * w ^ 2) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ A ∧ 1 < d ∧ (∀ a ∈ D, d ∣ a) ∧
        A.card ≤ D.card + 2 * nvOneStepLoss N₀ := by
  obtain ⟨s, b, G, m, J, B, i, j, P, Q, R, d, t, E, F, Z,
      hW, _hMdyadic, hDU, hbhalf, _hbcommon, _hMm, _hJcard,
      hBreserve, hBcard, _hcapacity, _hiJ, _hjJ, _hij,
      _hQrank, _hQbase, _hQproper, _hPproper, _hPrank,
      _hcommonP, _hPbox, _hdiffP, _hQbox, _hQcarrier,
      hRproper, hRrank, hside, hbcarrier, hscaled, hd,
      hcontain, _hEsub, _hEcard, _hFsub, _hFcard, _hBcovermid,
      hZcard, hcover⟩ :=
    exists_configured_nguyen_vu_rank_two_structure hp hpN hAN hlarge
  have hBA : B ⊆ A := hBreserve.trans G.reserve_subset
  have hsumSub : B.subsetSum ⊆ G.reserve.subsetSum :=
    Finset.subsetSum_mono hBreserve
  have hcastSub : natToIntFinset B.subsetSum ⊆
      natToIntFinset G.reserve.subsetSum := by
    exact Finset.image_mono _ hsumSub
  have hcontainB : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum :=
    (Finset.add_subset_add_left hcastSub).trans hcontain
  have hcoverB : natToIntFinset B ⊆
      Z + iteratedDifference ((d + 2) + 1) R.carrier := by
    convert hcover using 1 <;> omega
  have hn : d + 2 ≤ freimanRank (64 ^ 2) + 2 := by omega
  have hLossA : nvOneStepLoss N₀ < A.card := by
    calc
      nvOneStepLoss N₀ = nvOneStepLoss N₀ * 1 := by simp
      _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N := by
        gcongr
        exact nvBinaryLogScale_pos N
      _ < A.card := hlarge
  have finishDivisor
      {D : Finset ℕ}
      (hDB : D ⊆ B)
      (hcard : B.card ≤ D.card + nvOneStepLoss N₀) :
      D ⊆ A ∧ A.card ≤ D.card + 2 * nvOneStepLoss N₀ := by
    constructor
    · exact hDB.trans hBA
    · omega
  rcases (show R.rank = 0 ∨ R.rank = 1 ∨ R.rank = 2 by omega) with
    hrank0 | hrank1 | hrank2
  · exact (configured_rank_zero_impossible hlarge hRproper hrank0
      hbhalf hbcarrier).elim
  · rcases configured_rank_one_terminal hp hpN hAN hBA hlarge
        hRproper hrank1 hside hcontainB hcoverB hZcard hW hscaled hDU with
      hsquare | ⟨e, D, hDB, he, hcard, hdiv⟩
    · exact Or.inl hsquare
    · obtain ⟨hDA, hcardA⟩ := finishDivisor hDB hcard
      exact Or.inr ⟨e, D, hDA, he, hdiv, hcardA⟩
  · have hlocator' : ∀ {r q₁ q₂ L₁ L₂ : ℕ},
        0 < q₁ → 0 < q₂ →
        (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
          r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
        (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
          ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
            r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
            x₁ = x₂ ∧ y₁ = y₂) →
        q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
        b * (2 ^ s) ^ 2 ≤
          nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
        nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₁ →
        nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₂ →
        ∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
          ((r + u : ℕ) : ℤ) =
              (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
            ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
              0 < p * w ^ 2 ∧
              r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
      intro r q₁ q₂ L₁ L₂ hq₁ hq₂ hfamily hinj hspan hscaled₂
          hL₁large hL₂large
      exact hlocator hBA hBcard hq₁ hq₂ hfamily hinj hspan
        hW hscaled₂ hDU hL₁large hL₂large
    rcases configured_rank_two_terminal_of_balanced_locator hp hpN hAN hlarge
        hRproper hrank2 hside hcontainB hcoverB hZcard hW hscaled hDU hn
        hlocator' with
      hsquare | ⟨e, D, hDB, he, hcard, hdiv⟩
    · exact Or.inl hsquare
    · obtain ⟨hDA, hcardA⟩ := finishDivisor hDB hcard
      exact Or.inr ⟨e, D, hDA, he, hdiv, hcardA⟩

/-! ### Final descent and asymptotic conversion

The following wrapper closes all bookkeeping after the configured one-step
theorem.  Its hypothesis has exactly the conclusion of
`configured_nguyen_vu_one_step_of_balanced_rank_two_locator`; consequently
the only input still needed for the main theorem is the balanced rank-two
locator itself, not a second iteration or real-asymptotic argument. -/

theorem nguyen_vu_of_configured_one_step
    (hstep : ∀ {A : Finset ℕ} {N N₀ p : ℕ},
      0 < p → p * N ≤ N₀ → A ⊆ Finset.Icc 1 N →
      nvOneStepLoss N₀ * nvBinaryLogScale N < A.card →
      HasPMultipleSquareSubsetSum p A ∨
        ∃ d : ℕ, ∃ D : Finset ℕ,
          D ⊆ A ∧ 1 < d ∧ (∀ a ∈ D, d ∣ a) ∧
          A.card ≤ D.card + 2 * nvOneStepLoss N₀) :
    ∃ᵉ (O > 0) (O' > 0), ∀ᶠ N in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * Real.nthRoot 3 N * (N : ℝ).log ^ O := by
  let P := nvLossLogExponent + 1
  let K := 2 * nvMasterConstant ^ 10
  have hP : 0 < P := by
    dsimp only [P]
    omega
  have hK : 0 < K := by
    dsimp only [K]
    exact Nat.mul_pos (by norm_num) (pow_pos nvMasterConstant_pos 10)
  apply nguyen_vu_of_eventual_dyadic_square_forcing P K hP hK
  filter_upwards [] with N
  intro A hAN hlarge
  have hthreshold :
      2 * nvOneStepLoss N * nvBinaryLogScale N =
        K * 4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ P := by
    simp only [nvOneStepLoss, nvCubicScale, nvBinaryLogScale, P, K,
      pow_succ]
    ring
  have hlarge' :
      2 * nvOneStepLoss N * (Nat.log 2 N + 1) < A.card := by
    simp only [nvBinaryLogScale] at hthreshold
    rw [hthreshold]
    exact hlarge
  have honeN : 1 * N ≤ N := by simp
  obtain ⟨S, hSA, hSne, z, hsum⟩ :=
    has_pMultipleSquareSubsetSum_of_logarithmic_descent_step
      (N₀ := N) (L := 2 * nvOneStepLoss N)
      (Nat.mul_pos (by norm_num) (nvOneStepLoss_pos N))
      (by
        intro p M B hp hpM hBM hBlarge
        apply hstep hp hpM hBM
        have hle : nvOneStepLoss N * nvBinaryLogScale M ≤
            2 * nvOneStepLoss N * (Nat.log 2 M + 1) := by
          simp only [nvBinaryLogScale]
          gcongr
          omega
        exact hle.trans_lt hBlarge)
      N 1 A (by norm_num) honeN hAN hlarge'
  refine ⟨S, hSA, hSne.ne_empty, ?_⟩
  refine ⟨z, ?_⟩
  simpa only [one_mul, pow_two] using hsum

#print axioms nguyen_vu_of_configured_one_step

end Erdos587
