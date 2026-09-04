import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryCellPartition
import Wikipedia.GreenTao.Sieve.CFZCarryBlockEulerBridge

/-!
# Residue discrepancy on canonical CFZ carry cells

The canonical carry partition freezes the affine family independently of
all divisor choices.  To use it in the divisor expansion, one must still
average a periodic residue function on each carry fiber.

This file starts that comparison at the exact level.  A block indicator
tests the carry vector at the lower corner of a side-`D` quotient block.
On the coordinatewise box trimmed to a multiple of `D`, that indicator
depends only on the quotient coordinate.  It is therefore independent of
every `D`-periodic residue function, and their normalized mean factors
exactly.

The next lemmas compare this block indicator with the genuine canonical
cell indicator.  They can disagree only on the already-counted family
carry-bad set.  Together with the outer trimming boundary this yields the
required `O_{k,m}(D/N)` discrepancy without introducing a new geometric
axiom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Point and quotient-block indicators -/

/-- Real indicator that a point has the prescribed complete canonical carry
vector. -/
noncomputable def cfzCanonicalCarryIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) : ℝ :=
  if cfzCanonicalCarryVector (N := N) forms x = carry then 1 else 0

/-- Blockwise approximation to the canonical carry indicator: sample the
carry vector at the lower corner of the side-`D` quotient block. -/
noncomputable def cfzCanonicalCarryBlockIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) : ℝ :=
  cfzCanonicalCarryIndicator (N := N) forms carry
    (quotientBlockBase D x)

theorem abs_cfzCanonicalCarryIndicator_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) :
    |cfzCanonicalCarryIndicator (N := N) forms carry x| ≤ 1 := by
  unfold cfzCanonicalCarryIndicator
  split <;> norm_num

theorem abs_cfzCanonicalCarryBlockIndicator_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) :
    |cfzCanonicalCarryBlockIndicator (N := N) D forms carry x| ≤ 1 := by
  exact
    abs_cfzCanonicalCarryIndicator_le_one forms carry
      (quotientBlockBase D x)

/-- Away from the family carry-bad set, sampling the carry vector at the
block base gives the actual carry vector of the point. -/
theorem cfzCanonicalCarryVector_quotientBlockBase_eq_of_not_mem_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    cfzCanonicalCarryVector (N := N) forms
        (quotientBlockBase D x) =
      cfzCanonicalCarryVector (N := N) forms x := by
  funext q
  exact cfzCarry_quotientBlockBase_eq_of_not_bad
    hD (forms q) hx (by
      intro hbad
      apply hgood
      apply Finset.mem_biUnion.mpr
      exact
        ⟨q, Finset.mem_univ q,
          mem_cfzCarryBadPoints.mpr hbad⟩)

/-- Consequently the point and block indicators agree away from the family
carry-bad set. -/
theorem cfzCanonicalCarryIndicator_eq_blockIndicator_of_not_mem_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    cfzCanonicalCarryIndicator (N := N) forms carry x =
      cfzCanonicalCarryBlockIndicator
        (N := N) D forms carry x := by
  unfold cfzCanonicalCarryBlockIndicator
    cfzCanonicalCarryIndicator
  rw [cfzCanonicalCarryVector_quotientBlockBase_eq_of_not_mem_bad
    hD forms hx hgood]

/-! ## The carry-bad set inside the complete-block box -/

/-- Restrict the global family carry-bad set to the box trimmed to complete
side-`D` quotient blocks. -/
noncomputable def cfzTrimmedFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) :=
  (cfzFamilyCarryBadPoints (N := N) D forms).filter fun x =>
    x ∈ natBox
      (fun _ : CFZVariable k => trimToMultiple D N)

@[simp]
theorem mem_cfzTrimmedFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    {forms : κ → CFZFormIndex k}
    {x : CFZVariable k → ℕ} :
    x ∈ cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms ↔
      x ∈ cfzFamilyCarryBadPoints (N := N) D forms ∧
        x ∈ natBox
          (fun _ : CFZVariable k => trimToMultiple D N) := by
  simp [cfzTrimmedFamilyCarryBadPoints]

theorem cfzTrimmedFamilyCarryBadPoints_subset_natBox
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    cfzTrimmedFamilyCarryBadPoints (N := N) D forms ⊆
      natBox
        (fun _ : CFZVariable k => trimToMultiple D N) := by
  intro x hx
  exact (mem_cfzTrimmedFamilyCarryBadPoints.mp hx).2

theorem card_cfzTrimmedFamilyCarryBadPoints_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    (cfzTrimmedFamilyCarryBadPoints (N := N) D forms).card ≤
      (cfzFamilyCarryBadPoints (N := N) D forms).card := by
  exact Finset.card_filter_le _ _

/-! ## Exact quotient/residue factorization -/

/-- On the complete side-`D` blocks, the block carry indicator and any
`D`-periodic residue function are independent. -/
theorem boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (hDN : D ≤ N)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hF : PeriodicInEachCoordinate F D) :
    boxMean
        (fun _ : CFZVariable k => trimToMultiple D N)
        (fun x =>
          cfzCanonicalCarryBlockIndicator
              (N := N) D forms carry x *
            F x) =
      mean (fun a :
          FiniteBox (fun _ : CFZVariable k => N / D) =>
        cfzCanonicalCarryIndicator (N := N) forms carry
          (fun v => D * (a v : ℕ))) *
        meanMod D F := by
  have hq : 0 < N / D := Nat.div_pos hDN hD
  let a₀ : FiniteBox (fun _ : CFZVariable k => N / D) :=
    fun _ => ⟨0, hq⟩
  let r₀ : FiniteBox (fun _ : CFZVariable k => D) :=
    fun _ => ⟨0, hD⟩
  let : Nonempty
      (FiniteBox (fun _ : CFZVariable k => N / D)) := ⟨a₀⟩
  let : Nonempty
      (FiniteBox (fun _ : CFZVariable k => D)) := ⟨r₀⟩
  have hside :
      (fun _ : CFZVariable k => trimToMultiple D N) =
        fun _ : CFZVariable k => (N / D) * D := by
    funext v
    rfl
  rw [hside,
    boxMean_mul_eq_mean₂_quotient_residue]
  unfold mean₂
  calc
    mean (fun a :
        FiniteBox (fun _ : CFZVariable k => N / D) =>
      mean (fun r : FiniteBox (fun _ : CFZVariable k => D) =>
        cfzCanonicalCarryBlockIndicator
            (N := N) D forms carry
            (fun v => (r v : ℕ) + D * (a v : ℕ)) *
          F (fun v => (r v : ℕ) + D * (a v : ℕ)))) =
        mean (fun a :
            FiniteBox (fun _ : CFZVariable k => N / D) =>
          mean (fun r : FiniteBox
              (fun _ : CFZVariable k => D) =>
            cfzCanonicalCarryIndicator (N := N) forms carry
                (fun v => D * (a v : ℕ)) *
              F (fun v => (r v : ℕ)))) := by
      apply congrArg mean
      funext a
      apply congrArg mean
      funext r
      congr 1
      · unfold cfzCanonicalCarryBlockIndicator
        rw [quotientBlockBase_residue_add_block
          hD (fun v => (a v : ℕ)) r]
      · apply hF
        intro v
        exact Nat.add_mul_mod_self_left _ _ _
    _ = mean (fun a :
          FiniteBox (fun _ : CFZVariable k => N / D) =>
        cfzCanonicalCarryIndicator (N := N) forms carry
            (fun v => D * (a v : ℕ)) *
          mean (fun r : FiniteBox
              (fun _ : CFZVariable k => D) =>
            F (fun v => (r v : ℕ)))) := by
      apply congrArg mean
      funext a
      exact mean_smul _ _
    _ = mean (fun a :
          FiniteBox (fun _ : CFZVariable k => N / D) =>
        cfzCanonicalCarryIndicator (N := N) forms carry
          (fun v => D * (a v : ℕ))) *
        mean (fun r : FiniteBox
            (fun _ : CFZVariable k => D) =>
          F (fun v => (r v : ℕ))) := by
      let c : ℝ :=
        mean (fun r : FiniteBox
            (fun _ : CFZVariable k => D) =>
          F (fun v => (r v : ℕ)))
      let I :
          FiniteBox (fun _ : CFZVariable k => N / D) → ℝ :=
        fun a =>
          cfzCanonicalCarryIndicator (N := N) forms carry
            (fun v => D * (a v : ℕ))
      change mean (fun a => I a * c) = mean I * c
      calc
        mean (fun a => I a * c) =
            mean (fun a => c * I a) := by
          congr 1
          funext a
          ring
        _ = c * mean I := mean_smul c I
        _ = mean I * c := by ring
    _ = mean (fun a :
          FiniteBox (fun _ : CFZVariable k => N / D) =>
        cfzCanonicalCarryIndicator (N := N) forms carry
          (fun v => D * (a v : ℕ))) *
        meanMod D F := by
      rw [meanMod, boxMean_eq_mean_finiteBox]

/-- Equivalent factorization with the quotient-block density expressed as
the box mean of the block indicator itself. -/
theorem boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic_eq_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (hDN : D ≤ N)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hF : PeriodicInEachCoordinate F D) :
    boxMean
        (fun _ : CFZVariable k => trimToMultiple D N)
        (fun x =>
          cfzCanonicalCarryBlockIndicator
              (N := N) D forms carry x *
            F x) =
      boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryBlockIndicator
            (N := N) D forms carry) *
        meanMod D F := by
  have hq : 0 < N / D := Nat.div_pos hDN hD
  let a₀ : FiniteBox (fun _ : CFZVariable k => N / D) :=
    fun _ => ⟨0, hq⟩
  let r₀ : FiniteBox (fun _ : CFZVariable k => D) :=
    fun _ => ⟨0, hD⟩
  let : Nonempty
      (FiniteBox (fun _ : CFZVariable k => N / D)) := ⟨a₀⟩
  let : Nonempty
      (FiniteBox (fun _ : CFZVariable k => D)) := ⟨r₀⟩
  let Q : ℝ :=
    mean (fun a :
        FiniteBox (fun _ : CFZVariable k => N / D) =>
      cfzCanonicalCarryIndicator (N := N) forms carry
        (fun v => D * (a v : ℕ)))
  have hmain :=
    boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic
      hD hDN forms carry F hF
  have hone :=
    boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic
      hD hDN forms carry
      (fun _ : CFZVariable k → ℕ => (1 : ℝ))
      (periodicInEachCoordinate_const 1 D)
  have hmeanOne :
      meanMod D
          (fun _ : CFZVariable k → ℕ => (1 : ℝ)) = 1 := by
    rw [meanMod, boxMean_eq_mean_finiteBox, mean_const]
  have hblock :
      boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryBlockIndicator
            (N := N) D forms carry) = Q
      := by
    simpa only [mul_one, hmeanOne, Q] using hone
  rw [hblock]
  simpa only [Q] using hmain

/-! ## Point/block comparison on the trimmed box -/

/-- Multiplying by a function of absolute value at most one preserves the
point/block disagreement bound. -/
theorem abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hFbound : ∀ x, |F x| ≤ 1) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryIndicator
                (N := N) forms carry x *
              F x) -
        boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryBlockIndicator
                (N := N) D forms carry x *
              F x)| ≤
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ) := by
  apply abs_boxMean_sub_boxMean_le_bad
    (fun _ : CFZVariable k => trimToMultiple D N)
    (cfzTrimmedFamilyCarryBadPoints
      (N := N) D forms)
  · exact cfzTrimmedFamilyCarryBadPoints_subset_natBox D forms
  · intro x hx hgood
    have hxN :
        x ∈ natBox (fun _ : CFZVariable k => N) :=
      natBox_trimmed_subset D
        (fun _ : CFZVariable k => N) hx
    have hgoodGlobal :
        x ∉ cfzFamilyCarryBadPoints (N := N) D forms := by
      intro hbad
      apply hgood
      exact mem_cfzTrimmedFamilyCarryBadPoints.mpr
        ⟨hbad, hx⟩
    rw [cfzCanonicalCarryIndicator_eq_blockIndicator_of_not_mem_bad
      hD forms carry hxN hgoodGlobal]
  · intro x _hx
    unfold cfzCanonicalCarryBlockIndicator
      cfzCanonicalCarryIndicator
    by_cases hp :
        cfzCanonicalCarryVector (N := N) forms x = carry
    · by_cases hb :
          cfzCanonicalCarryVector (N := N) forms
              (quotientBlockBase D x) = carry
      · simp [hp, hb]
      · simpa [hp, hb] using hFbound x
    · by_cases hb :
          cfzCanonicalCarryVector (N := N) forms
              (quotientBlockBase D x) = carry
      · simpa [hp, hb, abs_neg] using hFbound x
      · simp [hp, hb]

/-- The same comparison for the unweighted cell indicators. -/
theorem abs_boxMean_cfzCanonicalCarryIndicator_sub_blockIndicator_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryIndicator
            (N := N) forms carry) -
        boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryBlockIndicator
            (N := N) D forms carry)| ≤
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ) := by
  simpa only [mul_one] using
    abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
      hD forms carry
      (fun _ : CFZVariable k → ℕ => (1 : ℝ))
      (fun _ => by norm_num)

/-! ## Canonical-cell residue discrepancy on the trimmed box -/

/-- On the complete-block box, the mean of a periodic function restricted
to one canonical carry fiber differs from the fiber density times the
residue mean only through carry-bad blocks. -/
theorem
    abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_density_mul_meanMod_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (hDN : D ≤ N)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hperiodic : PeriodicInEachCoordinate F D)
    (hFbound : ∀ x, |F x| ≤ 1) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryIndicator
                (N := N) forms carry x *
              F x) -
        boxMean
            (fun _ : CFZVariable k => trimToMultiple D N)
            (cfzCanonicalCarryIndicator
              (N := N) forms carry) *
          meanMod D F| ≤
      2 *
        (((cfzTrimmedFamilyCarryBadPoints
            (N := N) D forms).card : ℝ) /
          ∏ _v : CFZVariable k,
            (trimToMultiple D N : ℝ)) := by
  let side : CFZVariable k → ℕ :=
    fun _ => trimToMultiple D N
  let pointI : (CFZVariable k → ℕ) → ℝ :=
    cfzCanonicalCarryIndicator (N := N) forms carry
  let blockI : (CFZVariable k → ℕ) → ℝ :=
    cfzCanonicalCarryBlockIndicator
      (N := N) D forms carry
  let δ : ℝ :=
    ((cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms).card : ℝ) /
      ∏ _v : CFZVariable k,
        (trimToMultiple D N : ℝ)
  let A : ℝ := boxMean side (fun x => pointI x * F x)
  let B : ℝ := boxMean side (fun x => blockI x * F x)
  let C : ℝ := boxMean side pointI
  let Q : ℝ := boxMean side blockI
  let μ : ℝ := meanMod D F
  have hAB : |A - B| ≤ δ := by
    simpa only [A, B, side, pointI, blockI, δ] using
      abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
        hD forms carry F hFbound
  have hCQ : |C - Q| ≤ δ := by
    simpa only [C, Q, side, pointI, blockI, δ] using
      abs_boxMean_cfzCanonicalCarryIndicator_sub_blockIndicator_le
        hD forms carry
  have hQμ : B = Q * μ := by
    simpa only [B, Q, side, blockI, μ] using
      boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic_eq_mul
        hD hDN forms carry F hperiodic
  have hμ : |μ| ≤ 1 := by
    simpa only [μ] using
      abs_meanMod_le_of_abs_le hD F 1 hFbound
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hdecomp :
      A - C * μ = (A - B) + (Q - C) * μ := by
    rw [hQμ]
    ring
  change |A - C * μ| ≤ 2 * δ
  rw [hdecomp]
  calc
    |(A - B) + (Q - C) * μ| ≤
        |A - B| + |(Q - C) * μ| :=
      abs_add_le _ _
    _ = |A - B| + |Q - C| * |μ| := by
      rw [abs_mul]
    _ ≤ δ + δ * 1 := by
      gcongr
      simpa only [abs_sub_comm] using hCQ
    _ = 2 * δ := by ring

/-! ## Full-box discrepancy -/

/-- Full canonical-cell discrepancy.  The first term is the outer
incomplete-block boundary; the second is the carry-transition boundary on
the complete-block box. -/
theorem
    abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_density_mul_meanMod_le_full
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (hDN : D ≤ N)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hperiodic : PeriodicInEachCoordinate F D)
    (hFbound : ∀ x, |F x| ≤ 1) :
    |boxMean
          (fun _ : CFZVariable k => N)
          (fun x =>
            cfzCanonicalCarryIndicator
                (N := N) forms carry x *
              F x) -
        boxMean
            (fun _ : CFZVariable k => N)
            (cfzCanonicalCarryIndicator
              (N := N) forms carry) *
          meanMod D F| ≤
      4 *
          (((∏ _v : CFZVariable k, N) -
              ∏ _v : CFZVariable k,
                trimToMultiple D N : ℕ) : ℝ) /
            ∏ _v : CFZVariable k, (N : ℝ) +
        2 *
          (((cfzTrimmedFamilyCarryBadPoints
              (N := N) D forms).card : ℝ) /
            ∏ _v : CFZVariable k,
              (trimToMultiple D N : ℝ)) := by
  let fullSide : CFZVariable k → ℕ := fun _ => N
  let trimSide : CFZVariable k → ℕ :=
    fun _ => trimToMultiple D N
  let pointI : (CFZVariable k → ℕ) → ℝ :=
    cfzCanonicalCarryIndicator (N := N) forms carry
  let A : ℝ := boxMean fullSide (fun x => pointI x * F x)
  let A' : ℝ := boxMean trimSide (fun x => pointI x * F x)
  let C : ℝ := boxMean fullSide pointI
  let C' : ℝ := boxMean trimSide pointI
  let μ : ℝ := meanMod D F
  let outer : ℝ :=
    2 *
      (((∏ _v : CFZVariable k, N) -
          ∏ _v : CFZVariable k,
            trimToMultiple D N : ℕ) : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ)
  let bad : ℝ :=
    ((cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms).card : ℝ) /
      ∏ _v : CFZVariable k,
        (trimToMultiple D N : ℝ)
  have hpointMulBound :
      ∀ x, |pointI x * F x| ≤ 1 := by
    intro x
    rw [abs_mul]
    calc
      |pointI x| * |F x| ≤ 1 * 1 := by
        gcongr
        · exact
            abs_cfzCanonicalCarryIndicator_le_one
              forms carry x
        · exact hFbound x
      _ = 1 := by norm_num
  have hAouter : |A - A'| ≤ outer := by
    have h :=
      abs_boxMean_sub_trimmedBoxMean_le_boundary
        D fullSide
        (fun x => pointI x * F x) 1
        hD (fun _ => hDN) hpointMulBound
    have htrimSide :
        trimmedSide D fullSide = trimSide := by
      rfl
    rw [htrimSide] at h
    dsimp only [fullSide, trimSide] at h
    simpa only [A, A', outer, fullSide, trimSide,
      mul_one] using h
  have hCouter : |C - C'| ≤ outer := by
    have h :=
      abs_boxMean_sub_trimmedBoxMean_le_boundary
        D fullSide pointI 1
        hD (fun _ => hDN)
        (fun x =>
          abs_cfzCanonicalCarryIndicator_le_one
            forms carry x)
    have htrimSide :
        trimmedSide D fullSide = trimSide := by
      rfl
    rw [htrimSide] at h
    dsimp only [fullSide, trimSide] at h
    simpa only [C, C', outer, fullSide, trimSide,
      mul_one] using h
  have htrim : |A' - C' * μ| ≤ 2 * bad := by
    simpa only [A', C', μ, bad, trimSide, pointI] using
      abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_density_mul_meanMod_le
        hD hDN forms carry F hperiodic hFbound
  have hμ : |μ| ≤ 1 := by
    simpa only [μ] using
      abs_meanMod_le_of_abs_le hD F 1 hFbound
  have houter_nonneg : 0 ≤ outer := by
    dsimp only [outer]
    positivity
  have hbad_nonneg : 0 ≤ bad := by
    dsimp only [bad]
    positivity
  have hdecomp :
      A - C * μ =
        (A - A') + (A' - C' * μ) + (C' - C) * μ := by
    ring
  have hfinal : |A - C * μ| ≤ 2 * outer + 2 * bad := by
    rw [hdecomp]
    calc
      |(A - A') + (A' - C' * μ) + (C' - C) * μ| ≤
          |A - A'| + |A' - C' * μ| +
            |(C' - C) * μ| := by
        have h₁ :=
          abs_add_le
            ((A - A') + (A' - C' * μ))
            ((C' - C) * μ)
        have h₂ := abs_add_le (A - A') (A' - C' * μ)
        linarith
      _ = |A - A'| + |A' - C' * μ| +
            |C' - C| * |μ| := by
        rw [abs_mul]
      _ ≤ outer + 2 * bad + outer * 1 := by
        gcongr
        simpa only [abs_sub_comm] using hCouter
      _ = 2 * outer + 2 * bad := by ring
  convert hfinal using 1
  dsimp only [A, C, μ, outer, bad, fullSide, pointI]
  ring

end Wikipedia.SzemeredisTheorem
