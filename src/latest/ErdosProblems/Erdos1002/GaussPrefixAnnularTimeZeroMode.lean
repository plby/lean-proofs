import ErdosProblems.Erdos1002.GaussPrefixAnnularUniformZeroMode
import ErdosProblems.Erdos1002.PsiMixing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The annular zero mode at the left time endpoint

The uniform-to-Gauss estimate for one chronological tuple decays from
the first selected depth.  Hence it cannot be applied directly to the
first time cell, whose lower endpoint is zero.  We split that cell at
the moving depth `sqrt (annularDepthAmbientSize N)`.  Tuples beginning
before this depth have zero logarithmic density and are handled by
absolute continuity.  On the complementary family the transfer error
is a polynomial times a genuine geometric decay.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularTimeZeroModePropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- The part of a tuple family whose first chronological depth is below
`gap`. -/
def earlyFirstNatTupleFamily
    {r : ℕ} (hr : 0 < r) (gap : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  tuples.filter (fun t ↦ t ⟨0, hr⟩ < gap)

/-- The complementary part, whose first depth is at least `gap`. -/
def lateFirstNatTupleFamily
    {r : ℕ} (hr : 0 < r) (gap : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  tuples.filter (fun t ↦ gap ≤ t ⟨0, hr⟩)

@[simp] theorem mem_earlyFirstNatTupleFamily_iff
    {r gap : ℕ} {hr : 0 < r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ earlyFirstNatTupleFamily hr gap tuples ↔
      t ∈ tuples ∧ t ⟨0, hr⟩ < gap := by
  simp [earlyFirstNatTupleFamily]

@[simp] theorem mem_lateFirstNatTupleFamily_iff
    {r gap : ℕ} {hr : 0 < r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ lateFirstNatTupleFamily hr gap tuples ↔
      t ∈ tuples ∧ gap ≤ t ⟨0, hr⟩ := by
  simp [lateFirstNatTupleFamily]

theorem card_earlyFirstNatTupleFamily_add_card_lateFirstNatTupleFamily
    {r gap : ℕ} (hr : 0 < r)
    (tuples : Finset (Fin r → ℕ)) :
    (earlyFirstNatTupleFamily hr gap tuples).card +
      (lateFirstNatTupleFamily hr gap tuples).card =
        tuples.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_union, mem_earlyFirstNatTupleFamily_iff,
      mem_lateFirstNatTupleFamily_iff]
    constructor
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩)
      · exact ht
      · exact ht
    · intro ht
      rcases lt_or_ge (t ⟨0, hr⟩) gap with hlt | hge
      · exact Or.inl ⟨ht, hlt⟩
      · exact Or.inr ⟨ht, hge⟩
  · rw [Finset.disjoint_left]
    intro t he hl
    have he' := (mem_earlyFirstNatTupleFamily_iff.mp he).2
    have hl' := (mem_lateFirstNatTupleFamily_iff.mp hl).2
    omega

/-- An arbitrary family of `r` natural tuples lying below `H` has at
most `H^r` members. -/
theorem card_boundedNatTupleFamily_le
    {r H : ℕ} (tuples : Finset (Fin r → ℕ))
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    tuples.card ≤ H ^ r := by
  let code : (↥tuples) → (Fin r → Fin H) :=
    fun u i ↦ ⟨u.1 i, hbound u.1 u.2 i⟩
  have hinjective : Function.Injective code := by
    intro u v huv
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun huv i)
  calc
    tuples.card = Fintype.card (↥tuples) := by
      symm
      exact Fintype.card_coe tuples
    _ ≤ Fintype.card (Fin r → Fin H) :=
      Fintype.card_le_of_injective code hinjective
    _ = H ^ r := by simp

/-- If the first coordinate is additionally below `gap`, it contributes
only `gap` choices; all remaining coordinates contribute `H^(r-1)`. -/
theorem card_earlyFirstNatTupleFamily_le_of_bounded
    {r H gap : ℕ} (hr : 0 < r)
    (tuples : Finset (Fin r → ℕ))
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    (earlyFirstNatTupleFamily hr gap tuples).card ≤
      gap * H ^ (r - 1) := by
  let first : Fin r := ⟨0, hr⟩
  let code :
      (↥(earlyFirstNatTupleFamily hr gap tuples)) →
        Fin gap × ({i : Fin r // i ≠ first} → Fin H) :=
    fun u ↦
      (⟨u.1 first,
          (mem_earlyFirstNatTupleFamily_iff.mp u.2).2⟩,
        fun i ↦
          ⟨u.1 i.1,
            hbound u.1
              (mem_earlyFirstNatTupleFamily_iff.mp u.2).1 i.1⟩)
  have hinjective : Function.Injective code := by
    intro u v huv
    apply Subtype.ext
    funext i
    by_cases hi : i = first
    · subst i
      exact congrArg (fun z ↦ z.1.1) huv
    · exact congrArg Fin.val
        (congrFun (congrArg Prod.snd huv) ⟨i, hi⟩)
  calc
    (earlyFirstNatTupleFamily hr gap tuples).card =
        Fintype.card (↥(earlyFirstNatTupleFamily hr gap tuples)) := by
      symm
      exact Fintype.card_coe _
    _ ≤ Fintype.card
        (Fin gap × ({i : Fin r // i ≠ first} → Fin H)) :=
      Fintype.card_le_of_injective code hinjective
    _ = gap * H ^ (r - 1) := by
      simp [first, Fintype.card_subtype_compl]

/-- Canonical annular tuples whose first depth lies below the square-root
separation threshold. -/
def earlyCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  earlyFirstNatTupleFamily hr (annularSeparationGap N)
    (canonicalAnnularGridTupleFamily N k e)

/-- The complementary canonical family. -/
def lateCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  lateFirstNatTupleFamily hr (annularSeparationGap N)
    (canonicalAnnularGridTupleFamily N k e)

theorem aggregate_early_add_late_canonical_card
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k) :
    aggregateTupleFamilyCard
        (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) +
      aggregateTupleFamilyCard
        (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) =
      aggregateTupleFamilyCard
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) := by
  unfold aggregateTupleFamilyCard
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact card_earlyFirstNatTupleFamily_add_card_lateFirstNatTupleFamily
    hr (canonicalAnnularGridTupleFamily N k e)

/-- Literal aggregate cardinal bound for the early-start family. -/
theorem aggregate_earlyCanonicalAnnularGridTupleFamily_card_le
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    {N : ℕ} (hN : 1 < N) :
    aggregateTupleFamilyCard
        (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) ≤
      Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) *
        (annularSeparationGap N *
          annularDepthAmbientSize N ^ (MixedOccurrenceCount k - 1)) := by
  unfold aggregateTupleFamilyCard
  calc
    ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (earlyCanonicalAnnularGridTupleFamily N k hr e).card ≤
      ∑ _e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        annularSeparationGap N *
          annularDepthAmbientSize N ^ (MixedOccurrenceCount k - 1) := by
      apply Finset.sum_le_sum
      intro e _he
      exact card_earlyFirstNatTupleFamily_le_of_bounded hr
        (canonicalAnnularGridTupleFamily N k e)
        (fun t ht j ↦
          canonicalAnnularGridTupleFamily_lt_ambient
            hgrid k htime hN e t ht j)
    _ = _ := by simp

/-- The early-start canonical family has zero logarithmic density. -/
theorem tendsto_aggregate_earlyCanonicalAnnularGridTupleFamily_density_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let H : ℕ → ℕ := annularDepthAmbientSize
  let C : ℕ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
  let upper : ℕ → ℝ := fun N ↦
    (C : ℝ) *
      ((annularSeparationGap N : ℝ) / Real.log (N : ℝ)) *
      (((H N : ℝ) / Real.log (N : ℝ)) ^ (r - 1))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hraw :=
      ((tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ (C : ℝ)) atTop (nhds (C : ℝ))).mul
          tendsto_annularSeparationGap_div_log_zero).mul
        (tendsto_annularDepthAmbientSize_div_log.pow (r - 1))
    simpa only [upper, H, mul_zero, zero_mul] using! hraw
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hN hlog
    have hcardNat :=
      aggregate_earlyCanonicalAnnularGridTupleFamily_card_le
        hgrid k hr htime hN
    have hcardReal :
        (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) ≤
          (C : ℝ) * (annularSeparationGap N : ℝ) *
            (H N : ℝ) ^ (r - 1) := by
      have hcast :
          (aggregateTupleFamilyCard
            (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) ≤
            ((Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) *
              (annularSeparationGap N *
                annularDepthAmbientSize N ^
                  (MixedOccurrenceCount k - 1)) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcardNat
      simpa only [C, H, r, Nat.cast_mul, Nat.cast_pow,
        mul_assoc] using! hcast
    have hdiv := div_le_div_of_nonneg_right hcardReal
      (pow_nonneg hlog.le r)
    calc
      (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) /
          Real.log (N : ℝ) ^ r ≤
        ((C : ℝ) * (annularSeparationGap N : ℝ) *
            (H N : ℝ) ^ (r - 1)) /
          Real.log (N : ℝ) ^ r := hdiv
      _ = upper N := by
        have hpow :
            Real.log (N : ℝ) ^ r =
              Real.log (N : ℝ) ^ (r - 1) *
                Real.log (N : ℝ) := by
          conv_lhs => rw [show r = (r - 1) + 1 by omega]
          exact pow_succ _ _
        dsimp only [upper]
        rw [hpow, div_pow]
        field_simp [ne_of_gt hlog]
  · exact hupper

/-- The complete canonical tagged family is bounded by the ambient
coordinate box, with no asymptotic argument. -/
theorem aggregate_canonicalAnnularGridTupleFamily_card_le
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    {N : ℕ} (hN : 1 < N) :
    aggregateTupleFamilyCard
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) ≤
      Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) *
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
  unfold aggregateTupleFamilyCard
  calc
    ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (canonicalAnnularGridTupleFamily N k e).card ≤
      ∑ _e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
      apply Finset.sum_le_sum
      intro e _he
      exact card_boundedNatTupleFamily_le
        (canonicalAnnularGridTupleFamily N k e)
        (fun t ht j ↦
          canonicalAnnularGridTupleFamily_lt_ambient
            hgrid k htime hN e t ht j)
    _ = _ := by simp

theorem aggregate_lateCanonicalAnnularGridTupleFamily_card_le_full
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k) :
    aggregateTupleFamilyCard
        (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) ≤
      aggregateTupleFamilyCard
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) := by
  unfold aggregateTupleFamilyCard
  apply Finset.sum_le_sum
  intro e _he
  unfold lateCanonicalAnnularGridTupleFamily
  exact Finset.card_filter_le _ _

/-- A square-root depth threshold kills every fixed polynomial in the
ambient logarithmic horizon under the exact Gauss transfer ratio. -/
theorem tendsto_annularAmbientPower_mul_transferDecay_zero (r : ℕ) :
    Tendsto
      (fun N ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2))
      atTop (nhds 0) := by
  let θ : ℝ := 540 / 527
  let gapSucc : ℕ → ℕ := fun N ↦ annularSeparationGap N + 1
  have hθ : 1 < θ := by
    dsimp only [θ]
    norm_num
  have hgapSucc : Tendsto gapSucc atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun N ↦ Nat.le_add_right (annularSeparationGap N) 1)
      tendsto_annularSeparationGap_atTop
  have hpoly :=
    (tendsto_natPower_mul_inverse_geometric
      (2 * r) 1 (by omega) hθ).comp hgapSucc
  let upper : ℕ → ℝ := fun N ↦
    (θ * Real.log 2) *
      ((gapSucc N : ℝ) ^ (2 * r) *
        (θ ^ gapSucc N)⁻¹)
  have hupper : Tendsto upper atTop (nhds 0) := by
    have h := hpoly.const_mul (θ * Real.log 2)
    simpa only [upper, one_mul, mul_zero] using! h
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards with N
    have hHNat :
        annularDepthAmbientSize N ≤
          (annularSeparationGap N + 1) ^ 2 := by
      exact Nat.le_of_lt (Nat.lt_succ_sqrt' (annularDepthAmbientSize N))
    have hHReal :
        (annularDepthAmbientSize N : ℝ) ^ r ≤
          ((annularSeparationGap N + 1 : ℕ) : ℝ) ^ (2 * r) := by
      have hcast :
          (annularDepthAmbientSize N : ℝ) ≤
            (((annularSeparationGap N + 1) ^ 2 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hHNat
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
          annularDepthAmbientSize N) hcast r
      simpa only [Nat.cast_pow, ← pow_mul] using! hp
    have hfactor :
        (527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2 =
          (θ * Real.log 2) *
            (θ ^ gapSucc N)⁻¹ := by
      dsimp only [θ, gapSucc]
      rw [show (527 / 540 : ℝ) = (540 / 527 : ℝ)⁻¹ by
        norm_num, inv_pow, pow_succ, mul_inv_rev]
      field_simp
    rw [hfactor]
    have hfactorNonneg :
        0 ≤ (θ * Real.log 2) * (θ ^ gapSucc N)⁻¹ := by
      positivity
    calc
      (annularDepthAmbientSize N : ℝ) ^ r *
          ((θ * Real.log 2) * (θ ^ gapSucc N)⁻¹) ≤
        ((gapSucc N : ℕ) : ℝ) ^ (2 * r) *
          ((θ * Real.log 2) * (θ ^ gapSucc N)⁻¹) :=
        mul_le_mul_of_nonneg_right hHReal hfactorNonneg
      _ = upper N := by
        dsimp only [upper]
        ring
  · exact hupper

/-- The complete tagged canonical cardinal is still harmless after
multiplication by the square-root transfer decay. -/
theorem
    tendsto_aggregateCanonicalAnnularGridTupleCard_mul_transferDecay_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2))
      atTop (nhds 0) := by
  let C : ℕ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
  let upper : ℕ → ℝ := fun N ↦
    (C : ℝ) *
      ((annularDepthAmbientSize N : ℝ) ^ MixedOccurrenceCount k *
        ((527 / 540 : ℝ) ^ annularSeparationGap N *
          Real.log 2))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have h :=
      (tendsto_annularAmbientPower_mul_transferDecay_zero
        (MixedOccurrenceCount k)).const_mul (C : ℝ)
    simpa only [upper, mul_zero] using! h
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hcardNat :=
      aggregate_canonicalAnnularGridTupleFamily_card_le
        hgrid k htime hN
    have hcardReal :
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) ≤
          (C : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^ MixedOccurrenceCount k := by
      have hcast :
          (aggregateTupleFamilyCard
            (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) ≤
            ((Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) *
              annularDepthAmbientSize N ^ MixedOccurrenceCount k : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcardNat
      simpa only [C, Nat.cast_mul, Nat.cast_pow] using! hcast
    have hfac :
        0 ≤ (527 / 540 : ℝ) ^ annularSeparationGap N *
          Real.log 2 := by positivity
    calc
      (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2) ≤
        ((C : ℝ) *
          (annularDepthAmbientSize N : ℝ) ^ MixedOccurrenceCount k) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2) :=
        mul_le_mul_of_nonneg_right hcardReal hfac
      _ = upper N := by
        dsimp only [upper]
        ring
  · exact hupper

/-- The same transfer decay bound holds for the late subfamily. -/
theorem
    tendsto_aggregateLateCanonicalAnnularGridTupleCard_mul_transferDecay_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) : ℝ) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2))
      atTop (nhds 0) := by
  apply squeeze_zero' (g := fun N ↦
    (aggregateTupleFamilyCard
      (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) *
      ((527 / 540 : ℝ) ^ annularSeparationGap N *
        Real.log 2))
  · exact Eventually.of_forall fun N ↦ by positivity
  · exact Eventually.of_forall fun N ↦
      mul_le_mul_of_nonneg_right
        (by
          exact_mod_cast
            aggregate_lateCanonicalAnnularGridTupleFamily_card_le_full
              N k hr)
        (by positivity)
  · exact
      tendsto_aggregateCanonicalAnnularGridTupleCard_mul_transferDecay_zero
        hgrid k htime

theorem aggregateShortTupleFamilyCard_le_aggregateTupleFamilyCard
    {r : ℕ} {β : Type*} [Fintype β]
    (gap : ℕ) (tuples : β → Finset (Fin r → ℕ)) :
    aggregateShortTupleFamilyCard (gap := gap) tuples ≤
      aggregateTupleFamilyCard tuples := by
  unfold aggregateShortTupleFamilyCard aggregateTupleFamilyCard
  apply Finset.sum_le_sum
  intro b _hb
  unfold shortNatTupleFamily
  exact Finset.card_filter_le _ _

/-- Absolute continuity, summed over all order tags. -/
theorem
    aggregateUniformMovingSignedApproximationTupleMassSum_le_gauss
    {r : ℕ} {β : Type*} [Fintype β]
    (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateUniformMovingSignedApproximationTupleMassSum
        scale lower upper tuples ≤
      (2 * Real.log 2) *
        aggregateGaussMovingSignedApproximationTupleSum
          scale lower upper tuples := by
  unfold aggregateUniformMovingSignedApproximationTupleMassSum
    aggregateMovingSignedApproximationTupleMassSum
    aggregateGaussMovingSignedApproximationTupleSum
  calc
    (∑ b, movingSignedApproximationTupleMassSum
        uniform01Measure scale (lower b) (upper b) (tuples b)) ≤
      ∑ b, (2 * Real.log 2) *
        gaussMovingSignedApproximationTupleSum
          scale (lower b) (upper b) (tuples b) := by
      apply Finset.sum_le_sum
      intro b _hb
      exact movingSignedApproximationTupleMassSum_uniform_le_gauss
        scale (lower b) (upper b) (tuples b)
    _ = (2 * Real.log 2) *
        ∑ b, gaussMovingSignedApproximationTupleSum
          scale (lower b) (upper b) (tuples b) := by
      rw [Finset.mul_sum]

/-- Under Gauss measure, the early-start family has zero mass because
its normalized cardinal density is zero. -/
theorem tendsto_annularCanonicalGaussEarlyMass_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateGaussMovingSignedApproximationTupleSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e))
      atTop (nhds 0) := by
  let tupleFamily :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e
  have htotal : Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard (tupleFamily N) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
    simpa only [tupleFamily] using!
      tendsto_aggregate_earlyCanonicalAnnularGridTupleFamily_density_zero
        hgrid k hr htime
  have hshort : Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := annularSeparationGap N) (tupleFamily N) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
    apply squeeze_zero'
      (g := fun N ↦
        (aggregateTupleFamilyCard (tupleFamily N) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
    · filter_upwards
        [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
      positivity
    · filter_upwards
        [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
      apply div_le_div_of_nonneg_right
      · exact_mod_cast
          aggregateShortTupleFamilyCard_le_aggregateTupleFamilyCard
            (annularSeparationGap N) (tupleFamily N)
      · positivity
    · exact htotal
  have hlimit :=
    tendsto_aggregateGaussMovingSignedApproximationTupleSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A) (density := 0)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      (fun e j ↦
        flattenedAnnular_oriented_lower_pos
          hε hεA hgrid hsigned e j)
      (fun e j ↦
        flattenedAnnular_oriented_lower_lt_upper
          hεA hgrid e j)
      (fun e j ↦
        flattenedAnnular_oriented_upper_le
          hεA hgrid hsigned e j)
      (flattenedAnnular_oriented_product_eq ε A)
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      (tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0)
      tupleFamily
      (fun N e t ht ↦
        canonicalAnnularGridTupleFamily_chronological N k e t
          (mem_earlyFirstNatTupleFamily_iff.mp ht).1)
      (fun N e t ht j ↦
        canonicalAnnularGridTupleFamily_parity N k e t
          (mem_earlyFirstNatTupleFamily_iff.mp ht).1 j)
      htotal hshort
  simpa only [zero_mul, tupleFamily] using! hlimit

/-- The early-start family also has zero mass under the original
uniform-Lebesgue measure, without any positive-time hypothesis. -/
theorem tendsto_annularCanonicalUniformEarlyMass_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e))
      atTop (nhds 0) := by
  let gaussMass : ℕ → ℝ := fun N ↦
    aggregateGaussMovingSignedApproximationTupleSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (Real.log (N : ℝ))
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e)
  apply squeeze_zero'
    (g := fun N ↦ (2 * Real.log 2) * gaussMass N)
  · exact Eventually.of_forall fun N ↦ by
      unfold aggregateUniformMovingSignedApproximationTupleMassSum
        aggregateMovingSignedApproximationTupleMassSum
        movingSignedApproximationTupleMassSum
      positivity
  · exact Eventually.of_forall fun N ↦
      aggregateUniformMovingSignedApproximationTupleMassSum_le_gauss
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e)
  · have hgauss :=
      tendsto_annularCanonicalGaussEarlyMass_zero
        hε hεA hgrid k hr htime hsigned
    have h := hgauss.const_mul (2 * Real.log 2)
    simpa only [gaussMass, mul_zero] using! h

/-- Removing the zero-density early-start block does not change the
canonical tuple density. -/
theorem tendsto_aggregate_lateCanonicalAnnularGridTupleFamily_density
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
  have hfull :=
    tendsto_totalCanonicalAnnularGridTupleCard_density
      hgrid k hr htime
  have hearly :=
    tendsto_aggregate_earlyCanonicalAnnularGridTupleFamily_density_zero
      hgrid k hr htime
  have hsub := hfull.sub hearly
  have hsub' : Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k -
        (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [totalCanonicalAnnularGridTupleCard, sub_zero] using! hsub
  apply hsub'.congr'
  filter_upwards with N
  have hcardNat := aggregate_early_add_late_canonical_card N k hr
  have hcardReal :
      (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) +
        (aggregateTupleFamilyCard
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) : ℝ) =
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) := by
    exact_mod_cast hcardNat
  have hlate :
      (aggregateTupleFamilyCard
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) : ℝ) =
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) -
        (aggregateTupleFamilyCard
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) : ℝ) := by
    linarith
  rw [hlate]
  ring

theorem aggregateShort_lateCanonicalAnnularGridTupleFamily_card_le_full
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k) :
    aggregateShortTupleFamilyCard
        (gap := annularSeparationGap N)
        (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) ≤
      aggregateShortTupleFamilyCard
        (gap := annularSeparationGap N)
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) := by
  unfold aggregateShortTupleFamilyCard
  apply Finset.sum_le_sum
  intro e _he
  apply Finset.card_le_card
  intro t ht
  have ht' := mem_shortNatTupleFamily_iff.mp ht
  exact mem_shortNatTupleFamily_iff.mpr
    ⟨(mem_lateFirstNatTupleFamily_iff.mp ht'.1).1, ht'.2⟩

/-- The late-start subfamily inherits the full short-gap density zero. -/
theorem
    tendsto_aggregateShort_lateCanonicalAnnularGridTupleFamily_density_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := annularSeparationGap N)
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  have hfull : Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := annularSeparationGap N)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
    simpa only [aggregateShortTupleFamilyCard,
      totalShortCanonicalAnnularGridTupleCard] using!
      tendsto_totalShortCanonicalAnnularGridTupleCard_sqrt_density_zero
        hgrid k hr htime
  apply squeeze_zero'
    (g := fun N ↦
      (aggregateShortTupleFamilyCard
        (gap := annularSeparationGap N)
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
  · filter_upwards
      [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
    positivity
  · filter_upwards
      [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        aggregateShort_lateCanonicalAnnularGridTupleFamily_card_le_full
          N k hr
    · positivity
  · exact hfull

/-- The late-start block satisfies the uniform transfer theorem with the
square-root threshold as its literal first-depth floor. -/
theorem tendsto_annularCanonicalUniformLateMass
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e))
      atTop
      (nhds (annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k)) := by
  let tupleFamily :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ lateCanonicalAnnularGridTupleFamily N k hr e
  refine
    tendsto_aggregateUniformMovingSignedApproximationTupleMassSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A)
      (density := annularOccurrenceTimeDensity k)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      ?_ ?_ ?_ ?_
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      (tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0)
      tupleFamily
      ?_ ?_ ?_ ?_
      annularSeparationGap ?_ ?_
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_pos
        hε hεA hgrid hsigned e j
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_lt_upper
        hεA hgrid e j
  · exact fun e j ↦
      flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned e j
  · exact flattenedAnnular_oriented_product_eq ε A
  · exact fun N e t ht ↦
      canonicalAnnularGridTupleFamily_chronological N k e t
        (mem_lateFirstNatTupleFamily_iff.mp ht).1
  · exact fun N e t ht j ↦
      canonicalAnnularGridTupleFamily_parity N k e t
        (mem_lateFirstNatTupleFamily_iff.mp ht).1 j
  · simpa only [tupleFamily] using!
      tendsto_aggregate_lateCanonicalAnnularGridTupleFamily_density
        hgrid k hr htime
  · simpa only [tupleFamily] using!
      tendsto_aggregateShort_lateCanonicalAnnularGridTupleFamily_density_zero
        hgrid k hr htime
  · exact Eventually.of_forall fun N e t ht ↦
      (mem_lateFirstNatTupleFamily_iff.mp ht).2
  · simpa only [tupleFamily] using!
      tendsto_aggregateLateCanonicalAnnularGridTupleCard_mul_transferDecay_zero
        hgrid k hr htime

/-- Exact mass partition at the first-depth threshold. -/
theorem
    aggregateUniformMovingSignedApproximationTupleMassSum_canonical_eq_early_add_late
    {ε A : ℝ} {grid N : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k) :
    aggregateUniformMovingSignedApproximationTupleMassSum
        (β := Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) =
      aggregateUniformMovingSignedApproximationTupleMassSum
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) +
        aggregateUniformMovingSignedApproximationTupleMassSum
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e) := by
  unfold aggregateUniformMovingSignedApproximationTupleMassSum
    aggregateMovingSignedApproximationTupleMassSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  unfold movingSignedApproximationTupleMassSum
  let f : (Fin (MixedOccurrenceCount k) → ℕ) → ℝ :=
    fun times ↦ uniform01Measure.real
      (gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) times)
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not
      (canonicalAnnularGridTupleFamily N k e)
      (fun t ↦ t ⟨0, hr⟩ < annularSeparationGap N) f
  simpa only [earlyCanonicalAnnularGridTupleFamily,
    lateCanonicalAnnularGridTupleFamily,
    earlyFirstNatTupleFamily, lateFirstNatTupleFamily,
    not_lt, f] using! hpartition.symm

/-- Final zero-mode theorem, now including the left time cell.  No
positive lower time endpoint is assumed. -/
theorem tendsto_annularCanonicalUniformZeroMode_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e))
      atTop
      (nhds (annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k)) := by
  have hearly :=
    tendsto_annularCanonicalUniformEarlyMass_zero
      hε hεA hgrid k hr htime hsigned
  have hlate :=
    tendsto_annularCanonicalUniformLateMass
      hε hεA hgrid k hr htime hsigned
  have hadd := hearly.add hlate
  have hadd' : Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) +
        aggregateUniformMovingSignedApproximationTupleMassSum
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ lateCanonicalAnnularGridTupleFamily N k hr e))
      atTop
      (nhds (annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k)) := by
    simpa only [zero_add] using! hadd
  apply hadd'.congr'
  filter_upwards with N
  exact
    (aggregateUniformMovingSignedApproximationTupleMassSum_canonical_eq_early_add_late
      (ε := ε) (A := A) k hr).symm

end

end Erdos1002
