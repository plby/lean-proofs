/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1211.
https://www.erdosproblems.com/forum/thread/1211

Informal authors:
- David Conlon
- Jacob Fox
- Huy Tuan Pham

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1211.md
-/
import ErdosProblems.Erdos1211.Erdos1211Transfer
import ErdosProblems.Erdos1211.Erdos1211Upper

/-!
# Erdős Problem 1211

For a set of natural numbers, let `subsetSums A` be the sums of finite sets of
distinct elements of `A`.  This file proves that, in every partition of the
natural numbers into two colours, one monochromatic subset-sum set has upper
logarithmic density at least `(2 + √3) / 4`, and that this constant is sharp.

The mathematical proof and the formal dependency map are in `tex/1211.tex`.
-/

namespace Erdos1211

open BigOperators Filter Set
open scoped Topology

attribute [local instance] Classical.propDecidable
noncomputable section

/-- Sums of finite sets of distinct elements of `A`.  The empty sum is included. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ n = ∑ a ∈ F, a}

/-- The harmonic mass of the positive members of `X` strictly below the real cutoff `x`. -/
def harmonicMassBelow (X : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (fun n ↦ n ∈ X), (n : ℝ)⁻¹

/-- The normalized logarithmic mass at the real cutoff `x`. -/
def logarithmicRatio (X : Set ℕ) (x : ℝ) : ℝ :=
  harmonicMassBelow X x / Real.log x

/-- Upper logarithmic density, with the literal real cutoff from the problem statement. -/
def upperLogDensity (X : Set ℕ) : ℝ :=
  limsup (logarithmicRatio X) atTop

/-- `A` and `B` are disjoint and together contain every natural number. -/
def IsNatPartition (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ

/-- The sharp constant in Problem 1211. -/
def sharpConstant : ℝ :=
  (2 + Real.sqrt 3) / 4

/-- The larger of the two monochromatic upper logarithmic densities. -/
def partitionValue (A B : Set ℕ) : ℝ :=
  max (upperLogDensity (subsetSums A))
    (upperLogDensity (subsetSums B))

/-- The exact sharp assertion whose proof resolves Erdős Problem 1211. -/
def Resolution : Prop :=
  (∀ A B : Set ℕ, IsNatPartition A B →
      sharpConstant ≤ partitionValue A B) ∧
    ∃ A B : Set ℕ, IsNatPartition A B ∧
      partitionValue A B = sharpConstant

lemma subsetSums_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  rintro n ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hAB, rfl⟩

@[simp] lemma zero_mem_subsetSums (A : Set ℕ) : 0 ∈ subsetSums A := by
  exact ⟨∅, by simp, by simp⟩

lemma singleton_mem_subsetSums {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  refine ⟨{a}, ?_, by simp⟩
  simpa using ha

lemma harmonicMassBelow_nonneg (X : Set ℕ) (x : ℝ) :
    0 ≤ harmonicMassBelow X x := by
  simp only [harmonicMassBelow]
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

lemma harmonicMassBelow_mono {X Y : Set ℕ} (hXY : X ⊆ Y) (x : ℝ) :
    harmonicMassBelow X x ≤ harmonicMassBelow Y x := by
  classical
  simp only [harmonicMassBelow]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    exact ⟨hn.1, hXY hn.2⟩
  · intro n _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-! ### Equivalence of real and integer cutoffs -/

lemma harmonicMassBelow_eq_harmonicPrefix (X : Set ℕ) (x : ℝ) :
    harmonicMassBelow X x = Erdos1211DensityNat.harmonicPrefix X ⌈x⌉₊ := by
  rw [Erdos1211DensityNat.harmonicPrefix_eq_sum_filter]
  rfl

lemma logarithmicRatio_natCast (X : Set ℕ) (N : ℕ) :
    logarithmicRatio X (N : ℝ) = Erdos1211DensityNat.logRatio X N := by
  rw [logarithmicRatio, harmonicMassBelow_eq_harmonicPrefix,
    Nat.ceil_natCast, Erdos1211DensityNat.logRatio]

def ceilLogFactor (x : ℝ) : ℝ :=
  Real.log (⌈x⌉₊ : ℝ) / Real.log x

lemma tendsto_ceil_log_sub_log :
    Tendsto (fun x : ℝ ↦ Real.log (⌈x⌉₊ : ℝ) - Real.log x)
      atTop (nhds 0) := by
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.log (⌈x⌉₊ : ℝ) - Real.log x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hceilpos : (0 : ℝ) < (⌈x⌉₊ : ℕ) := by
      exact_mod_cast (Nat.ceil_pos.mpr hxpos)
    have hlog := Real.log_le_log hxpos (Nat.le_ceil x)
    linarith
  have hupper : ∀ᶠ x : ℝ in atTop,
      Real.log (⌈x⌉₊ : ℝ) - Real.log x ≤
        Real.log (x + 1) - Real.log x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hceilpos : (0 : ℝ) < (⌈x⌉₊ : ℕ) := by
      exact_mod_cast (Nat.ceil_pos.mpr hxpos)
    have hxone : 0 < x + 1 := by linarith
    have hceil := Nat.ceil_lt_add_one hxpos.le
    have hlog := Real.log_le_log hceilpos hceil.le
    linarith
  exact squeeze_zero' hnonneg hupper (Real.tendsto_log_comp_add_sub_log 1)

lemma ceilLogFactor_tendsto_one : Tendsto ceilLogFactor atTop (nhds 1) := by
  have hzero := tendsto_ceil_log_sub_log.div_atTop Real.tendsto_log_atTop
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have heq :
      (fun x : ℝ ↦ 1 +
        (Real.log (⌈x⌉₊ : ℝ) - Real.log x) / Real.log x) =ᶠ[atTop]
      ceilLogFactor := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hlog : Real.log x ≠ 0 :=
      (Real.log_pos hx).ne'
    rw [ceilLogFactor]
    field_simp
    ring
  simpa only [add_zero] using hone.congr' heq

lemma logarithmicRatio_eq_nat_mul_factor {X : Set ℕ} {x : ℝ} (hx : 1 < x) :
    logarithmicRatio X x =
      Erdos1211DensityNat.logRatio X ⌈x⌉₊ * ceilLogFactor x := by
  have hceilTwo : 2 ≤ ⌈x⌉₊ := by
    rw [Nat.add_one_le_ceil_iff]
    exact_mod_cast hx
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlogceil : Real.log (⌈x⌉₊ : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast Nat.zero_lt_of_lt (Nat.one_lt_two.trans_le hceilTwo)
    · exact_mod_cast (show ⌈x⌉₊ ≠ 1 by omega)
  rw [logarithmicRatio, harmonicMassBelow_eq_harmonicPrefix,
    Erdos1211DensityNat.logRatio, ceilLogFactor]
  field_simp

lemma logarithmicRatio_nonneg (X : Set ℕ) (x : ℝ) :
    0 ≤ logarithmicRatio X x := by
  by_cases hx : (1 : ℝ) < x
  · rw [logarithmicRatio_eq_nat_mul_factor hx]
    exact mul_nonneg (Erdos1211DensityNat.logRatio_nonneg _ _)
      (div_nonneg
        (Real.log_nonneg (by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.ceil_pos.mpr (zero_lt_one.trans hx)))))
        (Real.log_nonneg hx.le))
  · have hceil : ⌈x⌉₊ ≤ 1 := by
      exact (Nat.ceil_le).2 (by
        simpa only [Nat.cast_one] using (le_of_not_gt hx))
    have hempty : Finset.Ico 1 ⌈x⌉₊ = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [logarithmicRatio, harmonicMassBelow, hempty]
    simp

lemma isCoboundedUnder_le_logarithmicRatio (X : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (logarithmicRatio X) := by
  exact (isBoundedUnder_of ⟨0, logarithmicRatio_nonneg X⟩).isCoboundedUnder_le

lemma isBoundedUnder_le_logarithmicRatio (X : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (logarithmicRatio X) := by
  have hnat : ∀ᶠ N : ℕ in atTop,
      Erdos1211DensityNat.logRatio X N ≤ 2 := by
    have hu : ∀ᶠ N : ℕ in atTop,
        Erdos1211DensityNat.logRatio Set.univ N ≤ 2 :=
      Erdos1211DensityNat.logRatio_univ_tendsto_one.eventually
        (Iic_mem_nhds (show (1 : ℝ) < 2 by norm_num))
    filter_upwards [hu] with N hN
    exact (Erdos1211DensityNat.logRatio_mono (Set.subset_univ X) N).trans hN
  have hnatCeil : ∀ᶠ x : ℝ in atTop,
      Erdos1211DensityNat.logRatio X ⌈x⌉₊ ≤ 2 :=
    tendsto_nat_ceil_atTop.eventually hnat
  have hfactor : ∀ᶠ x : ℝ in atTop, ceilLogFactor x ≤ 2 :=
    ceilLogFactor_tendsto_one.eventually
      (Iic_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  apply isBoundedUnder_of_eventually_le
  filter_upwards [Filter.eventually_gt_atTop 1, hnatCeil, hfactor]
    with x hx hratio hfac
  rw [logarithmicRatio_eq_nat_mul_factor hx]
  have hnonneg := Erdos1211DensityNat.logRatio_nonneg X ⌈x⌉₊
  calc
    Erdos1211DensityNat.logRatio X ⌈x⌉₊ * ceilLogFactor x
        ≤ Erdos1211DensityNat.logRatio X ⌈x⌉₊ * 2 :=
      mul_le_mul_of_nonneg_left hfac hnonneg
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_right hratio (by norm_num)
    _ ≤ 4 := by norm_num

lemma nat_upperLogDensity_le_upperLogDensity (X : Set ℕ) :
    Erdos1211DensityNat.upperLogDensity X ≤ upperLogDensity X := by
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have hfreqNat : ∃ᶠ N : ℕ in atTop,
      c < Erdos1211DensityNat.logRatio X N :=
    Filter.frequently_lt_of_lt_limsup
      (Erdos1211DensityNat.isCoboundedUnder_le_logRatio X) hc
  have hfreqReal : ∃ᶠ x : ℝ in atTop, c < logarithmicRatio X x := by
    rw [frequently_atTop] at hfreqNat ⊢
    intro a
    obtain ⟨N, hN, hcN⟩ := hfreqNat ⌈a⌉₊
    refine ⟨(N : ℝ), ?_, ?_⟩
    · exact (Nat.le_ceil a).trans (by exact_mod_cast hN)
    · rwa [logarithmicRatio_natCast]
  exact Filter.le_limsup_of_frequently_le
    (hfreqReal.mono fun _ hx ↦ hx.le)
    (isBoundedUnder_le_logarithmicRatio X)

lemma upperLogDensity_le_nat_upperLogDensity (X : Set ℕ) :
    upperLogDensity X ≤ Erdos1211DensityNat.upperLogDensity X := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let delta : ℝ := min (epsilon / 4) (1 / 4)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hdeltaE : delta ≤ epsilon / 4 := min_le_left _ _
  have hdeltaQ : delta ≤ 1 / 4 := min_le_right _ _
  let D := Erdos1211DensityNat.upperLogDensity X
  have hDnonneg : 0 ≤ D := Erdos1211DensityNat.upperLogDensity_nonneg X
  have hDone : D ≤ 1 := Erdos1211DensityNat.upperLogDensity_le_one X
  have hnat : ∀ᶠ N : ℕ in atTop,
      Erdos1211DensityNat.logRatio X N < D + delta :=
    Filter.eventually_lt_add_pos_of_limsup_le
      (Erdos1211DensityNat.isBoundedUnder_le_logRatio X) le_rfl hdelta
  have hnatCeil : ∀ᶠ x : ℝ in atTop,
      Erdos1211DensityNat.logRatio X ⌈x⌉₊ < D + delta :=
    tendsto_nat_ceil_atTop.eventually hnat
  have hfactor : ∀ᶠ x : ℝ in atTop,
      ceilLogFactor x < 1 + delta :=
    ceilLogFactor_tendsto_one.eventually
      (Iio_mem_nhds (lt_add_of_pos_right 1 hdelta))
  have hevent : ∀ᶠ x : ℝ in atTop,
      logarithmicRatio X x ≤ D + epsilon := by
    filter_upwards [Filter.eventually_gt_atTop 1, hnatCeil, hfactor]
      with x hx hratio hfac
    rw [logarithmicRatio_eq_nat_mul_factor hx]
    have hratioNonneg := Erdos1211DensityNat.logRatio_nonneg X ⌈x⌉₊
    have honeDelta : 0 ≤ 1 + delta := by linarith
    have hDdelta : D * delta ≤ delta := by nlinarith
    have hdeltaSq : delta * delta ≤ delta / 4 := by nlinarith
    calc
      Erdos1211DensityNat.logRatio X ⌈x⌉₊ * ceilLogFactor x
          ≤ Erdos1211DensityNat.logRatio X ⌈x⌉₊ * (1 + delta) :=
        mul_le_mul_of_nonneg_left hfac.le hratioNonneg
      _ ≤ (D + delta) * (1 + delta) :=
        mul_le_mul_of_nonneg_right hratio.le honeDelta
      _ ≤ D + epsilon := by nlinarith
  exact Filter.limsup_le_of_le
    (isCoboundedUnder_le_logarithmicRatio X) hevent

theorem upperLogDensity_eq_nat (X : Set ℕ) :
    upperLogDensity X = Erdos1211DensityNat.upperLogDensity X :=
  le_antisymm (upperLogDensity_le_nat_upperLogDensity X)
    (nat_upperLogDensity_le_upperLogDensity X)

/-! ### The universal lower bound -/

def partitionColor (A : Set ℕ) (n : ℕ) : Fin 2 :=
  if n ∈ A then 0 else 1

@[simp] lemma partitionColor_eq_zero_iff (A : Set ℕ) (n : ℕ) :
    partitionColor A n = 0 ↔ n ∈ A := by
  simp [partitionColor]

@[simp] lemma partitionColor_eq_one_iff (A : Set ℕ) (n : ℕ) :
    partitionColor A n = 1 ↔ n ∉ A := by
  simp [partitionColor]

lemma mem_right_of_partitionColor_eq_one {A B : Set ℕ}
    (hpart : IsNatPartition A B) {n : ℕ}
    (hn : partitionColor A n = 1) : n ∈ B := by
  have hnA : n ∉ A := (partitionColor_eq_one_iff A n).mp hn
  have hnUnion : n ∈ A ∪ B := by
    rw [hpart.2]
    exact Set.mem_univ n
  exact hnUnion.resolve_left hnA

theorem sharpConstant_le_partitionValue (A B : Set ℕ)
    (hpart : IsNatPartition A B) :
    sharpConstant ≤ partitionValue A B := by
  let chi : ℕ → Fin 2 := partitionColor A
  let sigma : Fin 2 → Set ℕ := fun i ↦
    if i = 0 then subsetSums A else subsetSums B
  have hembed : ∀ j : ℕ,
      (↑((Erdos1211Transfer.localColorSet chi j).subsetSum) : Set ℕ) ⊆
        sigma (Erdos1211Transfer.winningColor chi j) := by
    intro j s hs
    obtain ⟨F, hFlocal, rfl⟩ := Finset.mem_subsetSum_iff.mp hs
    have hwin : Erdos1211Transfer.winningColor chi j = 0 ∨
        Erdos1211Transfer.winningColor chi j = 1 := by
      rcases Fin.eq_zero_or_eq_succ
          (Erdos1211Transfer.winningColor chi j) with hzero | ⟨k, hk⟩
      · exact Or.inl hzero
      · right
        have hkzero : k = 0 := Subsingleton.elim _ _
        subst k
        exact hk
    rcases hwin with hwin | hwin
    · have hFA : (↑F : Set ℕ) ⊆ A := by
        intro n hn
        have hnLocal : n ∈ Erdos1211Transfer.localColorSet chi j :=
          hFlocal hn
        have hnColor : chi n =
            Erdos1211Transfer.winningColor chi j :=
          (Finset.mem_filter.mp hnLocal).2
        have hnZero : partitionColor A n = 0 := by
          simpa only [chi, hwin] using hnColor
        exact (partitionColor_eq_zero_iff A n).mp hnZero
      simpa only [sigma, hwin, if_pos] using
        (show (∑ n ∈ F, n) ∈ subsetSums A from ⟨F, hFA, rfl⟩)
    · have hFB : (↑F : Set ℕ) ⊆ B := by
        intro n hn
        have hnLocal : n ∈ Erdos1211Transfer.localColorSet chi j :=
          hFlocal hn
        have hnColor : chi n =
            Erdos1211Transfer.winningColor chi j :=
          (Finset.mem_filter.mp hnLocal).2
        have hnOne : partitionColor A n = 1 := by
          simpa only [chi, hwin] using hnColor
        exact mem_right_of_partitionColor_eq_one hpart hnOne
      have hone : (1 : Fin 2) ≠ 0 := by decide
      simpa only [sigma, hwin, if_neg hone] using
        (show (∑ n ∈ F, n) ∈ subsetSums B from ⟨F, hFB, rfl⟩)
  have hlower := Erdos1211Transfer.sharp_le_max_upperLogDensity chi sigma hembed
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simpa only [sharpConstant, Erdos1211Dynamics.sharpConstant,
    partitionValue, upperLogDensity_eq_nat, sigma, if_pos, if_neg hone] using hlower

/-! ### The sharp Pell-block construction -/

lemma subsetSums_colorClass_eq (i : Fin 2) :
    subsetSums (Erdos1211Upper.colorClass i) =
      Erdos1211Upper.monochromaticSubsetSums i := by
  ext s
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, fun n hn ↦ hF hn, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, fun _ hn ↦ hF _ hn, rfl⟩

lemma extremal_isNatPartition :
    IsNatPartition (Erdos1211Upper.colorClass 0)
      (Erdos1211Upper.colorClass 1) :=
  ⟨Erdos1211Upper.colorClass_disjoint,
    Erdos1211Upper.colorClass_union⟩

lemma extremal_partitionValue_le :
    partitionValue (Erdos1211Upper.colorClass 0)
        (Erdos1211Upper.colorClass 1) ≤ sharpConstant := by
  rw [partitionValue, upperLogDensity_eq_nat, upperLogDensity_eq_nat,
    subsetSums_colorClass_eq, subsetSums_colorClass_eq]
  apply max_le
  · simpa only [sharpConstant, Erdos1211Upper.sharp] using
      Erdos1211Upper.upperLogDensity_monochromaticSubsetSums_le_sharp 0
  · simpa only [sharpConstant, Erdos1211Upper.sharp] using
      Erdos1211Upper.upperLogDensity_monochromaticSubsetSums_le_sharp 1

lemma extremal_partitionValue_eq :
    partitionValue (Erdos1211Upper.colorClass 0)
        (Erdos1211Upper.colorClass 1) = sharpConstant := by
  apply le_antisymm extremal_partitionValue_le
  exact sharpConstant_le_partitionValue _ _ extremal_isNatPartition

/-- **Resolution of Erdős Problem 1211.**  The least possible value of the
larger monochromatic upper logarithmic density is `(2 + √3) / 4`. -/
theorem erdos_1211 :
    (∀ A B : Set ℕ, IsNatPartition A B →
        sharpConstant ≤ partitionValue A B) ∧
      ∃ A B : Set ℕ, IsNatPartition A B ∧
        partitionValue A B = sharpConstant := by
  constructor
  · intro A B hpart
    exact sharpConstant_le_partitionValue A B hpart
  · exact ⟨Erdos1211Upper.colorClass 0, Erdos1211Upper.colorClass 1,
      extremal_isNatPartition, extremal_partitionValue_eq⟩

end

end Erdos1211

alias _root_.Erdos1211.erdos1211 := _root_.Erdos1211.erdos_1211
