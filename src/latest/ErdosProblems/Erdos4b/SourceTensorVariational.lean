/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceCompactPrimitive

/-!
# Literal tensor energies and their compact-primitive source profiles

All signs from taking tail primitives are common to every summand and
cancel after squaring. The companion ratio contributes only one fixed
positive scalar, independently of the dimension.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

def sourceTensorValue {ι J : Type*} [Fintype ι]
    (S : Finset J) (ψ : J → ι → ℝ → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ j ∈ S, ∏ i, ψ j i (t i)

def sourceTensorEnergy {ι J : Type*} [Fintype ι]
    (S : Finset J) (ψ : J → ι → ℝ → ℝ) : ℝ :=
  ∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0), sourceTensorValue S ψ t ^ 2

def sourceTensorFaceValue {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) (h : Fin K)
    (t : PinnedShiftIndex h → ℝ) : ℝ :=
  ∑ j ∈ S, (∫ u : ℝ in Set.Ioi 0, ψ j h u) * ∏ i, ψ j i.val (t i)

def sourceTensorFaceEnergy {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) (h : Fin K) : ℝ :=
  ∫ t : PinnedShiftIndex h → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0),
    sourceTensorFaceValue S ψ h t ^ 2

theorem weighted_tensor_neg_square {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℝ) (f : J → ι → ℝ) :
    (∑ j ∈ S, c j * ∏ i, -f j i) ^ 2 = (∑ j ∈ S, c j * ∏ i, f j i) ^ 2 := by
  simp_rw [Finset.prod_neg, Finset.card_univ]
  have hid : (∑ j ∈ S, c j * ((-1 : ℝ) ^ Fintype.card ι * ∏ i, f j i)) =
      (-1 : ℝ) ^ Fintype.card ι * (∑ j ∈ S, c j * ∏ i, f j i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hid, mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
  norm_num

theorem sourceFirstVariationalIntegral_primitive {ι J : Type*} [Fintype ι]
    (S : Finset J) (b : J → ι → ℝ) (ψ : J → ι → ℝ → ℝ)
    (hψ : ∀ j ∈ S, ∀ i, Continuous (ψ j i)) :
    sourceFirstVariationalIntegral S (fun j i ↦ sourceCompactPrimitive (b j i) (ψ j i)) =
      sourceTensorEnergy S ψ := by
  apply setIntegral_congr_fun (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ioi)
  intro t ht
  change (∑ j ∈ S, ∏ i, deriv (sourceCompactPrimitive (b j i) (ψ j i)) (t i)) ^ 2 = _
  have hid : (∑ j ∈ S, ∏ i, deriv (sourceCompactPrimitive (b j i) (ψ j i)) (t i)) =
      ∑ j ∈ S, ∏ i, -ψ j i (t i) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.prod_congr rfl
    intro i hi
    exact sourceCompactPrimitive_deriv (hψ j hj i) (ht i (Set.mem_univ i)).le
  rw [hid]
  simpa only [one_mul, sourceTensorValue] using
    weighted_tensor_neg_square S (fun _ ↦ 1) (fun j i ↦ ψ j i (t i))

theorem sourcePinnedFirstVariationalIntegral_primitive {K : ℕ} {J : Type*}
    (S : Finset J) (b : J → Fin K → ℝ) (ψ : J → Fin K → ℝ → ℝ)
    (hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i)
    (hψ : ∀ j ∈ S, ∀ i, Continuous (ψ j i))
    (hsupport : ∀ j ∈ S, ∀ i t, b j i ≤ t → ψ j i t = 0) (h : Fin K) :
    sourcePinnedFirstVariationalIntegral S
      (fun j i ↦ sourceCompactPrimitive (b j i) (ψ j i)) h = sourceTensorFaceEnergy S ψ h := by
  apply setIntegral_congr_fun (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ioi)
  intro t ht
  change (∑ j ∈ S, sourceCompactPrimitive (b j h) (ψ j h) 0 *
    ∏ i : PinnedShiftIndex h, deriv (sourceCompactPrimitive (b j i.val) (ψ j i.val)) (t i)) ^ 2 = _
  have hid : (∑ j ∈ S, sourceCompactPrimitive (b j h) (ψ j h) 0 *
      ∏ i : PinnedShiftIndex h, deriv (sourceCompactPrimitive (b j i.val) (ψ j i.val)) (t i)) =
      ∑ j ∈ S, (∫ u : ℝ in Set.Ioi 0, ψ j h u) *
        ∏ i : PinnedShiftIndex h, -ψ j i.val (t i) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sourceCompactPrimitive_zero_eq_integral (hb j hj h) (hsupport j hj h)]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact sourceCompactPrimitive_deriv (hψ j hj i.val) (ht i (Set.mem_univ i)).le
  rw [hid]
  exact weighted_tensor_neg_square S (fun j ↦ ∫ u : ℝ in Set.Ioi 0, ψ j h u)
    (fun j (i : PinnedShiftIndex h) ↦ ψ j i.val (t i))

theorem sourcePrimitiveProfileConditions {K : ℕ} {J : Type*} (hK : 0 < K)
    (S : Finset J) (b : J → Fin K → ℝ) (ψ : J → Fin K → ℝ → ℝ)
    (hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i)
    (hsmooth : ∀ j i, ContDiff ℝ ∞ (ψ j i))
    (hsupport : ∀ j i t, b j i ≤ t → ψ j i t = 0)
    (hbudget : ∀ j ∈ S, (∑ i, b j i) ≤ (1 : ℝ) / 10)
    (hI : 0 < sourceTensorEnergy S ψ)
    (hJ : ∀ h : Fin K, 0 < sourceTensorFaceEnergy S ψ h) :
    SourceProfileConditions S (fun j i ↦ sourceCompactPrimitive (b j i) (ψ j i))
      sourceCompanionProfile := by
  refine ⟨hK, fun j i ↦ sourceCompactPrimitive_compact (hsupport j i),
    fun j i ↦ sourceCompactPrimitive_smooth (hsmooth j i),
    sourceCompanionProfile_compact, sourceCompanionProfile_smooth, ?_, ?_,
    fun _ ht hn ↦ sourceCompanionProfile_support ht hn, ?_, ?_⟩
  · intro j hj t ht hn
    exact sourceCompactPrimitive_simplex S b ψ (fun j _ ↦ hsupport j) hbudget hj t hn
  · intro j hj i t ht hn
    have hi := (sourceCompactPrimitive_ceiling (hsupport j i) hn).le
    have hsum : b j i ≤ ∑ i, b j i :=
      Finset.single_le_sum (fun i _ ↦ hb j hj i) (Finset.mem_univ i)
    exact hi.trans (hsum.trans (hbudget j hj))
  · rw [sourceFirstVariationalIntegral_primitive S b ψ (fun j _ i ↦ (hsmooth j i).continuous)]
    exact mul_pos hI (sourceCompanionProfile_main_pos K)
  · intro h
    rw [sourcePinnedFirstVariationalIntegral_primitive S b ψ hb
      (fun j _ i ↦ (hsmooth j i).continuous) (fun j _ ↦ hsupport j)]
    exact mul_pos (hJ h) (sourceCompanionProfile_pinned_pos K)

theorem sourceProfileRatio_fixedCompanion {K : ℕ} {J : Type*} (hK : 0 < K)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) :
    sourceProfileRatio S F sourceCompanionProfile =
      ((∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h) /
        sourceFirstVariationalIntegral S F) / sourceCompanionEnergy := by
  unfold sourceProfileRatio
  rw [← Finset.sum_mul, mul_div_mul_comm, sourceCompanionProfile_ratio hK]
  ring

theorem sourceProfileRatio_primitive {K : ℕ} {J : Type*} (hK : 0 < K)
    (S : Finset J) (b : J → Fin K → ℝ) (ψ : J → Fin K → ℝ → ℝ)
    (hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i)
    (hψ : ∀ j ∈ S, ∀ i, Continuous (ψ j i))
    (hsupport : ∀ j ∈ S, ∀ i t, b j i ≤ t → ψ j i t = 0) :
    sourceProfileRatio S (fun j i ↦ sourceCompactPrimitive (b j i) (ψ j i))
      sourceCompanionProfile =
      ((∑ h : Fin K, sourceTensorFaceEnergy S ψ h) / sourceTensorEnergy S ψ) /
        sourceCompanionEnergy := by
  rw [sourceProfileRatio_fixedCompanion hK,
    sourceFirstVariationalIntegral_primitive S b ψ hψ]
  simp_rw [sourcePinnedFirstVariationalIntegral_primitive S b ψ hb hψ hsupport]

end

end Erdos4b
