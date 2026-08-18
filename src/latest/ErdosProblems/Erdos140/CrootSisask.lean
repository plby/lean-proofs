import APAP.Physics.AlmostPeriodicity
import ErdosProblems.Erdos140.MarcinkiewiczZygmund
import Mathlib.Combinatorics.Pigeonhole

/-!
# Croot--Sisask almost-periodicity for Erdős Problem 140

This module records the exact finite Croot--Sisask theorem used in the
localized Bloom--Sisask argument. The underlying proof is the fully
formalized finite sampling argument in `APAP.Physics.AlmostPeriodicity`.
It supplies the finite MZ sampling estimate, retains half the samples, and
uses the large-fibre lemma to obtain the explicit `K ^ (-512 m / ε²)` loss.

Only the sound finite almost-periodicity module is imported. In particular,
this file does not import APAP's unfinished integer Roth theorem or its
unfinished regular-Bohr-set module.
-/

namespace Erdos140

open Finset
open scoped BigOperators Pointwise translate mu Indicator ENNReal NNReal

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

noncomputable def crootSisaskSampleSize (q : ℕ) (ε : ℝ) : ℕ :=
  ⌈(64 : ℝ) * q / (ε / 2) ^ 2⌉₊

/-- The standard subset form of Croot--Sisask. Every element of `T - T` is
an almost period, and the exact sampling/pigeonhole density is retained. -/
theorem croot_sisask_subset
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (q : ℕ) (hq : 1 ≤ q) (ε : ℝ) (hε : 0 < ε) (f : G → ℂ) :
    let k := crootSisaskSampleSize q ε
    ∃ T : Finset G,
      T ⊆ S ∧
      T.Nonempty ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ‖τ (t - s) (mu A ∗ᵈ f) - mu A ∗ᵈ f‖_[2 * q] ≤
          ε * ‖f‖_[2 * q] := by
  classical
  let k := crootSisaskSampleSize q ε
  let L := AlmostPeriodicity.l k q (ε / 2) f A
  have hkLower : (64 : ℝ) * q / (ε / 2) ^ 2 ≤ k := by
    change (64 : ℝ) * q / (ε / 2) ^ 2 ≤
      (↑⌈(64 : ℝ) * q / (ε / 2) ^ 2⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hkpos : 0 < k := by
    rw [← @Nat.cast_pos ℝ]
    exact hkLower.trans_lt'
      (div_pos (mul_pos (by norm_num) (by positivity)) (pow_pos (half_pos hε) 2))
  have hLcard : (#A : ℝ) ^ k / 2 ≤ #L :=
    AlmostPeriodicity.lemma28 (half_pos hε) hq hkLower
  have hLne : L.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ]
    exact hLcard.trans_lt' (by positivity)
  let P : Finset ((Fin k → G) × G) := L ×ˢ S
  let X : Finset (Fin k → G) := (A + S) ^^ k
  let φ : ((Fin k → G) × G) → (Fin k → G) := fun z ↦ z.1 + fun _ ↦ z.2
  have hXne : X.Nonempty := (hA.add hS).piFinset_const
  have hmap : ∀ z ∈ P, φ z ∈ X := by
    rintro ⟨l, s⟩ hls
    simp only [P, mem_product] at hls
    simp only [X, Fintype.mem_piFinset, φ, Pi.add_apply]
    have hlGood : l ∈ L := hls.1
    change l ∈ AlmostPeriodicity.l k q (ε / 2) f A at hlGood
    rw [AlmostPeriodicity.l, mem_filter] at hlGood
    have hl : l ∈ A ^^ k := hlGood.1
    intro i
    exact Finset.add_mem_add (Fintype.mem_piFinset.1 hl i) hls.2
  have hXcard : #X = #(A + S) ^ k := by simp [X]
  have hXcardR : (#X : ℝ) = (#(A + S) : ℝ) ^ k := by
    rw [hXcard]
    norm_cast
  have hXcardNe : (#X : ℝ) ≠ 0 := by exact_mod_cast hXne.card_ne_zero
  have hpigeon :
      ∃ x ∈ X, ((#L : ℝ) * #S) / #X ≤
        ∑ z ∈ P with φ z = x, (1 : ℝ) := by
    refine Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap hXne ?_
    simp only [nsmul_eq_mul, sum_const, P, card_product, Nat.cast_mul]
    rw [mul_comm (#X : ℝ), div_mul_cancel₀ _ hXcardNe, mul_one]
  obtain ⟨x, hxX, hx⟩ := hpigeon
  let Q : Finset ((Fin k → G) × G) := {z ∈ P | φ z = x}
  let T : Finset G := Q.image Prod.snd
  have hQcard : (#Q : ℝ) = ∑ z ∈ P with φ z = x, (1 : ℝ) := by simp [Q]
  have hsndInj : Set.InjOn Prod.snd (Q : Set ((Fin k → G) × G)) := by
    rintro ⟨l₁, s₁⟩ hz₁ ⟨l₂, s₂⟩ hz₂ hs
    have hz₁' : (l₁, s₁) ∈ Q := hz₁
    have hz₂' : (l₂, s₂) ∈ Q := hz₂
    have hφ : l₁ + (fun _ ↦ s₁) = l₂ + fun _ ↦ s₂ :=
      (mem_filter.1 hz₁').2.trans (mem_filter.1 hz₂').2.symm
    cases hs
    apply Prod.ext
    · funext i
      exact add_right_cancel (congr_fun hφ i)
    · rfl
  have hTcard : #T = #Q := card_image_iff.mpr hsndInj
  have hQpos : (0 : ℝ) < #Q := by
    have hratioPos : 0 < ((#L : ℝ) * #S) / #X :=
      div_pos (mul_pos (by exact_mod_cast hLne.card_pos) (by exact_mod_cast hS.card_pos))
        (by exact_mod_cast hXne.card_pos)
    exact hratioPos.trans_le (by simpa [hQcard] using hx)
  have hTne : T.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ, hTcard]
    exact hQpos
  refine ⟨T, ?_, hTne, ?_, ?_⟩
  · intro s hsT
    obtain ⟨z, hzQ, rfl⟩ := mem_image.1 hsT
    exact (mem_product.1 (mem_filter.1 hzQ).1).2
  · calc
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k)
          = (((#A : ℝ) ^ k / 2 * #S) / #X) := by rw [hXcardR]
      _ ≤ ((#L : ℝ) * #S) / #X := by gcongr
      _ ≤ #Q := by simpa [hQcard] using hx
      _ = #T := by exact_mod_cast hTcard.symm
  · intro s hsT t htT
    obtain ⟨⟨a, s'⟩, hasQ, hs'⟩ := mem_image.1 hsT
    obtain ⟨⟨b, t'⟩, hbtQ, ht'⟩ := mem_image.1 htT
    simp only at hs' ht'
    subst s'
    subst t'
    have has : a ∈ L := (mem_product.1 (mem_filter.1 hasQ).1).1
    have hbt : b ∈ L := (mem_product.1 (mem_filter.1 hbtQ).1).1
    have hax : a + (fun _ ↦ s) = x := (mem_filter.1 hasQ).2
    have hbx : b + (fun _ ↦ t) = x := (mem_filter.1 hbtQ).2
    have hab : a + (fun _ ↦ s - t) = b := by
      funext i
      have ha := congr_fun hax i
      have hb := congr_fun hbx i
      simp only [Pi.add_apply] at ha hb ⊢
      calc
        a i + (s - t) = (a i + s) - t := by abel
        _ = x i - t := by rw [ha]
        _ = b i := by rw [← hb]; abel
    have habGood : a + (fun _ ↦ s - t) ∈ L := by rw [hab]; exact hbt
    have htri := AlmostPeriodicity.just_the_triangle_inequality
      (A := A) (f := f) (m := q) (k := k) (t := s - t) has habGood hkpos hq
    simpa [neg_sub, mul_div_cancel₀ _ (two_ne_zero' ℝ)] using htri

private theorem crootSisaskRatioBound
    {G : Type*} [Fintype G] (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty)
    (q : ℕ) (hq : q = ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊) :
    ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) ≤ Real.exp 1 := by
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hden : 0 < 1 + Real.log r⁻¹ := by
    have hloginv : 0 ≤ Real.log r⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    linarith
  have hq₁ : 1 ≤ q := by
    rw [hq, Nat.one_le_ceil_iff]
    have hloginv : 0 ≤ Real.log r⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    dsimp [r] at hloginv ⊢
    linarith
  calc
    ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹)
        ≤ r ^ (-((2 * q : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) inf_le_right <| neg_nonpos.2 <| by positivity
    _ ≤ r ^ (-(1 + Real.log r⁻¹)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) hrle <| neg_le_neg <| inv_anti₀
        hden <| (Nat.le_ceil _).trans <| by
          rw [← hq]
          exact_mod_cast Nat.le_mul_of_pos_left q (by norm_num : 0 < 2)
    _ ≤ r ^ (-(0 + Real.log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := hrle.eq_or_lt
      · simp [hr]
      have : 0 < Real.log r⁻¹ := Real.log_pos <| (one_lt_inv₀ hrpos).2 hr
      exact Real.rpow_le_rpow_of_exponent_ge (by positivity) hrle
        (by gcongr; exact zero_le_one)
    _ = r ^ (Real.log r)⁻¹ := by simp [inv_neg]
    _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one

private theorem crootSisaskHolderNormAt
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} (B C : Finset G) (u x : G) (q : ℕ) (hq₁ : 1 ≤ q) :
    ‖(τ u ((mu A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖ ≤
        ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[2 * q] *
          ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent (2 * q)] := by
  let M : ℕ := 2 * q
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    dsimp [M]
    omega
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  have hM' : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  set F : G → ℂ := τ u (mu A ∗ᵈ 𝟭_[B]) - mu A ∗ᵈ 𝟭_[B]
  have hconv :
      (τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x =
        (F ∗ᵈ mu C) x := by simp [sub_ddconv, F]
  have hsum : (F ∗ᵈ mu C) x = ∑ y, F y * mu (x +ᵥ -C) y := by
    rw [ddconv_eq_sum_sub']
    congr with y
    simp [neg_add_eq_sub]
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        = ‖∑ y, F y * mu (x +ᵥ -C) y‖ := by rw [hconv, hsum]
    _ ≤ ∑ y, ‖F y * mu (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * mu (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ = _ := by simp [F, M]

private theorem crootSisaskHolderAt
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} {ε : ℝ} (B C : Finset G)
    (hC : C.Nonempty) (u x : G) (q : ℕ) (hq₁ : 1 ≤ q)
    (hF₀ :
      ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[
          2 * q] ≤
        ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[
          2 * q]) :
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖ ≤
        ε * (((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) / Real.exp 1) := by
  let M : ℕ := 2 * q
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    dsimp [M]
    omega
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        ≤ ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[M] *
            ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
          simpa [M] using crootSisaskHolderNormAt B C u x q hq₁
    _ ≤ ε / Real.exp 1 * #B ^ (M : ℝ)⁻¹ *
          ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      have hF₁ :
          ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[M] ≤
            ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[M] := by
        simpa only [M, Nat.cast_mul, Nat.cast_ofNat] using hF₀
      have hind : ‖(𝟭_[B] : G → ℂ)‖_[M] = (#B : ℝ) ^ (M : ℝ)⁻¹ := by
        rw [show (M : ℝ≥0∞) = ((M : ℝ≥0) : ℝ≥0∞) by norm_num,
          MeasureTheory.dLpNorm_indicator_one hM₀]
        norm_num
      rw [← hind]
      exact hF₁
    _ = ε * (((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹) / Real.exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, Real.div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [Real.rpow_neg, Real.rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ = ε * (((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) / Real.exp 1) := by
      simp [M]

private theorem crootSisaskHolderUpgrade
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} {ε : ℝ} (hε : 0 < ε) (B C : Finset G)
    (hC : C.Nonempty) (u : G) (q : ℕ) (hq₁ : 1 ≤ q)
    (hratio : ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) ≤ Real.exp 1)
    (hF₀ :
      ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[
          2 * q] ≤
        ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[
          2 * q]) :
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ (crootSisaskHolderAt B C hC u x q hq₁ hF₀).trans ?_
  refine mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 ?_)
  exact hratio

/-- Three-factor `L^∞` Croot--Sisask while retaining `T ⊆ S`.
Every difference of two elements of `T` is an `L^∞` almost period. -/
theorem croot_sisask_linfty_subset
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    let q := ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊
    let k := crootSisaskSampleSize q (ε / Real.exp 1)
    ∃ T : Finset G,
      T ⊆ S ∧ T.Nonempty ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ‖(τ (t - s) ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
          (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  let m : ℝ := 1 + Real.log r⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hm₀ : 0 < m := by
    have : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    positivity
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hTS, hTne, hcard, hT⟩ :=
    croot_sisask_subset hA hS ⌈m⌉₊ hm₁ (ε / Real.exp 1) (by positivity)
      (𝟭_[B] : G → ℂ)
  refine ⟨T, hTS, hTne, ?_, ?_⟩
  · simpa [r, m] using hcard
  · intro s hs t ht
    apply crootSisaskHolderUpgrade hε B C hC (t - s) ⌈m⌉₊ hm₁
      (crootSisaskRatioBound B C hB hC ⌈m⌉₊ (by simp [r, m]))
    simpa [r, m] using hT s hs t ht
  /-
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  let m : ℝ := 1 + Real.log r⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hm₀ : 0 < m := by
    have : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    positivity
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hTS, hTne, hcard, hT⟩ :=
    croot_sisask_subset hA hS ⌈m⌉₊ hm₁ (ε / Real.exp 1) (by positivity)
      (𝟭_[B] : G → ℂ)
  norm_cast at hT
  let M : ℕ := 2 * ⌈m⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    simp [← Nat.succ_le_iff, M]
    linarith
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  have hM' : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  refine ⟨T, hTS, hTne, hcard, ?_⟩
  intro s hs t ht
  let u : G := t - s
  set F : G → ℂ := τ u (mu A ∗ᵈ 𝟭_[B]) - mu A ∗ᵈ 𝟭_[B]
  have hconv (x : G) :
      (τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x =
        (F ∗ᵈ mu C) x := by simp [sub_ddconv, F]
  have hsum (x : G) : (F ∗ᵈ mu C) x = ∑ y, F y * mu (x +ᵥ -C) y := by
    rw [ddconv_eq_sum_sub']
    congr with y
    simp [neg_add_eq_sub]
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        = ‖∑ y, F y * mu (x +ᵥ -C) y‖ := by rw [hconv, hsum]
    _ ≤ ∑ y, ‖F y * mu (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * mu (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖mu_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ ≤ ε / Real.exp 1 * #B ^ (M : ℝ)⁻¹ *
          ‖mu_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      simpa [← ENNReal.coe_natCast, MeasureTheory.dLpNorm_indicator_one hM₀, F, u, M]
        using hT s hs t ht
    _ = ε * (((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹) / Real.exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ ≤ ε := mul_le_of_le_one_right (by positivity) <| (div_le_one <| by positivity).2 ?_
  calc
    ((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹)
        ≤ r ^ (-(M : ℝ)⁻¹) :=
      rpow_le_rpow_of_nonpos (by positivity) inf_le_right <| neg_nonpos.2 <| by positivity
    _ ≤ r ^ (-(1 + Real.log r⁻¹)⁻¹) :=
      rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left <| neg_le_neg <| inv_anti₀
        (by positivity) <| (Nat.le_ceil _).trans <| mod_cast Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ r ^ (-(0 + Real.log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
      · simp [hr]
      have : 0 < Real.log r⁻¹ := Real.log_pos <| (one_lt_inv₀ (by positivity)).2 hr
      exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left (by gcongr; exact zero_le_one)
    _ = r ^ (Real.log r)⁻¹ := by simp [inv_neg]
    _ ≤ Real.exp 1 := rpow_inv_log_le_exp_one
  -/

/-- Boosted subset-preserving `L^∞` almost-periodicity. The large set `T`
remains a subset of `S`; recentering it at `z ∈ T` makes zero an element of
the averaging set. -/
theorem croot_sisask_linfty_subset_boosted
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : m ≠ 0)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    let q := ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊
    let k := crootSisaskSampleSize q ((ε / m) / Real.exp 1)
    ∃ (T : Finset G) (z : G),
      T ⊆ S ∧ z ∈ T ∧
      (-z +ᵥ T).Nonempty ∧ (-z +ᵥ T) ⊆ S - S ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ‖(mu (-z +ᵥ T) ∗ᵈ^ m ∗ᵈ ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_iff_ne_zero.2 hm)
  have hδ : 0 < ε / (m : ℝ) := div_pos hε hmpos
  obtain ⟨T, hTS, hTne, hcard, hperiod⟩ :=
    croot_sisask_linfty_subset hA hS (ε / (m : ℝ)) hδ B C hB hC
  obtain ⟨z, hz⟩ := hTne
  let X : Finset G := -z +ᵥ T
  have hXne : X.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ -z +ᵥ T
    rw [mem_vadd_finset]
    exact ⟨z, hz, by simp⟩
  have hXperiod : ∀ x ∈ X,
      ‖(τ x ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε / (m : ℝ) := by
    intro x hx
    change x ∈ -z +ᵥ T at hx
    rw [mem_vadd_finset] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hp := hperiod z hz t ht
    simpa [sub_eq_add_neg, add_comm] using hp
  have hXsub : -z +ᵥ T ⊆ S - S := by
    intro x hx
    rw [mem_vadd_finset] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simpa [sub_eq_add_neg, add_comm] using sub_mem_sub (hTS ht) (hTS hz)
  set F : G → ℂ := (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C
  refine ⟨T, z, hTS, hz, ?_, hXsub, ?_, ?_⟩
  · simpa [X] using hXne
  · simpa using hcard
  · change ‖mu X ∗ᵈ^ m ∗ᵈ F - F‖_[∞] ≤ ε
    calc
      (‖mu X ∗ᵈ^ m ∗ᵈ F - F‖_[∞] : ℝ)
          = ‖𝔼 a ∈ X ^^ m, (τ (∑ i, a i) F - F)‖_[∞] := by
            rw [mu_iterConv_ddconv, expect_sub_distrib, expect_const hXne.piFinset_const]
      _ ≤ 𝔼 a ∈ X ^^ m, ‖τ (∑ i, a i) F - F‖_[∞] :=
        MeasureTheory.dLpNorm_expect_le le_top
      _ ≤ 𝔼 _a ∈ X ^^ m, ε := by
        refine expect_le_expect fun a ha ↦ ?_
        calc
          (‖τ (∑ i, a i) F - F‖_[∞] : ℝ)
              ≤ ∑ i, ‖τ (a i) F - F‖_[∞] :=
                MeasureTheory.dLpNorm_translate_sum_sub_le le_top _ _ _
          _ ≤ ∑ _i, ε / (m : ℝ) := by
            gcongr
            simpa [F] using hXperiod (a _) (Fintype.mem_piFinset.1 ha _)
          _ = ε := by
            simp only [sum_const, card_fin, nsmul_eq_mul]
            rw [mul_div_cancel₀]
            exact_mod_cast hm
      _ = ε := by rw [expect_const hXne.piFinset_const]

/-- Finite Croot--Sisask almost-periodicity with an explicit large-set bound.
The exponent `2 * m` is the even moment furnished by the sampling proof. -/
alias croot_sisask := AlmostPeriodicity.almost_periodicity

/-- The three-factor `L^∞` consequence of Croot--Sisask obtained by Hölder. -/
alias croot_sisask_linfty := AlmostPeriodicity.linfty_almost_periodicity

/-- The boosted three-factor form, in which averaging over `k`-fold sums of
almost periods changes the convolution by at most `ε` in `L^∞`. -/
alias croot_sisask_linfty_boosted :=
  AlmostPeriodicity.linfty_almost_periodicity_boosted

#print axioms croot_sisask
#print axioms croot_sisask_subset
#print axioms croot_sisask_linfty_subset
#print axioms croot_sisask_linfty_subset_boosted
#print axioms croot_sisask_linfty
#print axioms croot_sisask_linfty_boosted

end Erdos140
