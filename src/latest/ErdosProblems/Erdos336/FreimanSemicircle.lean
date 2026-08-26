import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open MeasureTheory intervalIntegral

noncomputable def cutSin (c x : ℝ) : ℝ := if x ≤ c then Real.sin x else 0

lemma integral_sin_eq_cos_sub (a b : ℝ) :
    (∫ x in a..b, Real.sin x) = Real.cos a - Real.cos b := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => 0 - Real.cos y) (Real.sin x) x := by
    intro x hx
    simpa using (Real.hasDerivAt_cos x).const_sub 0
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv intervalIntegral.intervalIntegrable_sin

lemma integral_cutSin (c : ℝ) (hc : c ∈ Set.Icc (-Real.pi) Real.pi) :
    (∫ x in -Real.pi..Real.pi, cutSin c x) =
      Real.cos (-Real.pi) - Real.cos c := by
  rw [show cutSin c = Set.indicator {x : ℝ | x ≤ c} Real.sin by
    ext x
    simp [cutSin, Set.indicator]]
  rw [intervalIntegral.integral_indicator hc]
  exact integral_sin_eq_cos_sub _ _

lemma intervalIntegrable_cutSin (c a b : ℝ) :
    IntervalIntegrable (cutSin c) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  rw [show cutSin c = Set.indicator (Set.Iic c) Real.sin by
    ext x
    simp [cutSin, Set.indicator]]
  rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Iic]
  exact ((intervalIntegrable_iff.mp
    (intervalIntegral.intervalIntegrable_sin (a := a) (b := b))).mono_set
      Set.inter_subset_right)

noncomputable def semicircleIntegrand (φ x : ℝ) : ℝ :=
  if φ < 0 then cutSin (φ + Real.pi) x - cutSin φ x
  else cutSin (φ - Real.pi) x + Real.sin x - cutSin φ x

lemma integral_semicircleIntegrand
    {φ : ℝ} (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi) :
    (∫ x in -Real.pi..Real.pi, semicircleIntegrand φ x) =
      2 * Real.cos φ := by
  by_cases hφ : φ < 0
  · rw [show semicircleIntegrand φ = fun x =>
        cutSin (φ + Real.pi) x - cutSin φ x by
      funext x; simp [semicircleIntegrand, hφ]]
    rw [intervalIntegral.integral_sub]
    · rw [integral_cutSin, integral_cutSin]
      · rw [Real.cos_add_pi]
        ring
      · exact ⟨hφlo, hφhi⟩
      · constructor <;> linarith [Real.pi_pos]
    · exact intervalIntegrable_cutSin _ _ _
    · exact intervalIntegrable_cutSin _ _ _
  · rw [show semicircleIntegrand φ = fun x =>
        cutSin (φ - Real.pi) x + Real.sin x - cutSin φ x by
      funext x; simp [semicircleIntegrand, hφ]]
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_add]
    · rw [integral_cutSin, integral_sin_eq_cos_sub, integral_cutSin]
      · rw [Real.cos_sub_pi]
        norm_num
        ring
      · exact ⟨hφlo, hφhi⟩
      · constructor <;> linarith [Real.pi_pos]
    · exact intervalIntegrable_cutSin _ _ _
    · exact intervalIntegral.intervalIntegrable_sin
    · exact (intervalIntegrable_cutSin _ _ _).add
        intervalIntegral.intervalIntegrable_sin
    · exact intervalIntegrable_cutSin _ _ _


def semicircleArcMem (φ θ : ℝ) : Prop :=
  if θ < 0 then φ < θ ∨ θ + Real.pi ≤ φ
  else θ - Real.pi ≤ φ ∧ φ < θ

noncomputable instance (φ θ : ℝ) : Decidable (semicircleArcMem φ θ) := by
  unfold semicircleArcMem
  infer_instance

lemma semicircleIntegrand_eq_ite
    {φ θ : ℝ} (hφlo : -Real.pi ≤ φ) (hφhi : φ < Real.pi)
    (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ Real.pi) :
    semicircleIntegrand φ θ =
      if semicircleArcMem φ θ then Real.sin θ else 0 := by
  classical
  by_cases hφ : φ < 0 <;> by_cases hθ : θ < 0
  all_goals
    by_cases h1 : θ ≤ φ + Real.pi
    all_goals by_cases h2 : θ ≤ φ
    all_goals by_cases h3 : θ ≤ φ - Real.pi
    all_goals by_cases h4 : φ < θ
    all_goals by_cases h5 : θ + Real.pi ≤ φ
    all_goals
      simp [semicircleIntegrand, semicircleArcMem, cutSin,
        hφ, hθ, h1, h2, h3, h4, h5]
      all_goals linarith [Real.pi_pos]

variable {ι : Type*} [Fintype ι]

noncomputable def angleSemicircleCount (φ : ι → ℝ) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => semicircleArcMem (φ i) θ).card

lemma intervalIntegrable_semicircleIntegrand (φ a b : ℝ) :
    IntervalIntegrable (semicircleIntegrand φ) MeasureTheory.volume a b := by
  by_cases hφ : φ < 0
  · rw [show semicircleIntegrand φ = fun x =>
        cutSin (φ + Real.pi) x - cutSin φ x by
      funext x
      simp [semicircleIntegrand, hφ]]
    exact (intervalIntegrable_cutSin _ _ _).sub
      (intervalIntegrable_cutSin _ _ _)
  · rw [show semicircleIntegrand φ = fun x =>
        cutSin (φ - Real.pi) x + Real.sin x - cutSin φ x by
      funext x
      simp [semicircleIntegrand, hφ]]
    exact ((intervalIntegrable_cutSin _ _ _).add
      intervalIntegral.intervalIntegrable_sin).sub
        (intervalIntegrable_cutSin _ _ _)

lemma sum_semicircleIntegrand_eq_count_mul
    (φ : ι → ℝ)
    (hφ : ∀ i, -Real.pi ≤ φ i ∧ φ i < Real.pi)
    {θ : ℝ} (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ Real.pi) :
    (∑ i, semicircleIntegrand (φ i) θ) =
      (angleSemicircleCount φ θ : ℝ) * Real.sin θ := by
  classical
  calc
    (∑ i, semicircleIntegrand (φ i) θ) =
        ∑ i, if semicircleArcMem (φ i) θ then Real.sin θ else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact semicircleIntegrand_eq_ite (hφ i).1 (hφ i).2 hθlo hθhi
    _ = (angleSemicircleCount φ θ : ℝ) * Real.sin θ := by
      rw [angleSemicircleCount, ← Finset.sum_filter]
      simp

noncomputable def freimanBoundIntegrand (N n : ℕ) (θ : ℝ) : ℝ :=
  ((N : ℝ) - n) * cutSin 0 θ +
    (n : ℝ) * (Real.sin θ - cutSin 0 θ)

lemma intervalIntegrable_freimanBoundIntegrand (N n : ℕ) (a b : ℝ) :
    IntervalIntegrable (freimanBoundIntegrand N n) MeasureTheory.volume a b := by
  unfold freimanBoundIntegrand
  exact ((intervalIntegrable_cutSin 0 a b).const_mul _).add
    ((intervalIntegral.intervalIntegrable_sin.sub
      (intervalIntegrable_cutSin 0 a b)).const_mul _)
lemma integral_freimanBoundIntegrand (N n : ℕ) :
    (∫ θ in -Real.pi..Real.pi, freimanBoundIntegrand N n θ) =
      4 * (n : ℝ) - 2 * (N : ℝ) := by
  have hcutInt := intervalIntegrable_cutSin 0 (-Real.pi) Real.pi
  have hsinInt : IntervalIntegrable Real.sin MeasureTheory.volume
      (-Real.pi) Real.pi := intervalIntegral.intervalIntegrable_sin
  have hleft := hcutInt.const_mul ((N : ℝ) - n)
  have hright := (hsinInt.sub hcutInt).const_mul (n : ℝ)
  have hc : (0 : ℝ) ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  unfold freimanBoundIntegrand
  rw [intervalIntegral.integral_add hleft hright,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hsinInt hcutInt,
    integral_cutSin 0 hc, integral_sin_eq_cos_sub]
  norm_num
  ring

/-- Analytic core of Freiman's semicircle lemma. -/
theorem freiman_semicircle_integral_bound
    (φ : ι → ℝ) (n : ℕ)
    (hφ : ∀ i, -Real.pi ≤ φ i ∧ φ i < Real.pi)
    (hupper : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      angleSemicircleCount φ θ ≤ n)
    (hlower : ∀ θ ∈ Set.Icc (-Real.pi) (0 : ℝ),
      Fintype.card ι ≤ angleSemicircleCount φ θ + n) :
    (∑ i, Real.cos (φ i)) ≤ 2 * (n : ℝ) - Fintype.card ι := by
  let F : ℝ → ℝ := fun θ => ∑ i, semicircleIntegrand (φ i) θ
  have hFint : IntervalIntegrable F MeasureTheory.volume (-Real.pi) Real.pi := by
    dsimp [F]
    have hsum := IntervalIntegrable.sum (Finset.univ : Finset ι)
      (a := -Real.pi) (b := Real.pi)
      (f := fun i θ => semicircleIntegrand (φ i) θ) (fun i hi =>
        intervalIntegrable_semicircleIntegrand _ _ _)
    have heq : (∑ i : ι, fun θ => semicircleIntegrand (φ i) θ) =
        (fun θ => ∑ i : ι, semicircleIntegrand (φ i) θ) := by
      funext θ
      simp
    rw [← heq]
    exact hsum
  have hBint := intervalIntegrable_freimanBoundIntegrand
    (Fintype.card ι) n (-Real.pi) Real.pi
  have hpoint : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      F θ ≤ freimanBoundIntegrand (Fintype.card ι) n θ := by
    intro θ hθ
    rw [show F θ = (angleSemicircleCount φ θ : ℝ) * Real.sin θ by
      exact sum_semicircleIntegrand_eq_count_mul φ hφ hθ.1 hθ.2]
    by_cases hθ0 : θ < 0
    · have hsin : Real.sin θ ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_lt hθ0) hθ.1
      have hlow := hlower θ ⟨hθ.1, le_of_lt hθ0⟩
      have hlowR' : (Fintype.card ι : ℝ) ≤
          angleSemicircleCount φ θ + n := by exact_mod_cast hlow
      have hlowR : (Fintype.card ι : ℝ) - n ≤
          angleSemicircleCount φ θ := by linarith
      simp [freimanBoundIntegrand, cutSin, le_of_lt hθ0]
      nlinarith
    · have hθnonneg : 0 ≤ θ := le_of_not_gt hθ0
      have hsin : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθnonneg hθ.2
      have hupp := hupper θ ⟨hθnonneg, hθ.2⟩
      have huppR : (angleSemicircleCount φ θ : ℝ) ≤ n := by exact_mod_cast hupp
      unfold freimanBoundIntegrand cutSin
      by_cases hθle : θ ≤ 0
      · have hθeq : θ = 0 := le_antisymm hθle hθnonneg
        subst θ
        simp
      · simp [hθle]
        nlinarith
  have hintle : (∫ θ in -Real.pi..Real.pi, F θ) ≤
      ∫ θ in -Real.pi..Real.pi,
        freimanBoundIntegrand (Fintype.card ι) n θ :=
    intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hFint hBint hpoint
  have hFvalue : (∫ θ in -Real.pi..Real.pi, F θ) =
      2 * ∑ i, Real.cos (φ i) := by
    dsimp [F]
    rw [intervalIntegral.integral_finset_sum]
    · simp_rw [integral_semicircleIntegrand (hφ _).1 (le_of_lt (hφ _).2)]
      rw [Finset.mul_sum]
    · intro i hi
      exact intervalIntegrable_semicircleIntegrand _ _ _
  rw [hFvalue, integral_freimanBoundIntegrand] at hintle
  linarith

lemma angleSemicircleCount_complement_lower
    (φ : ι → ℝ) (hφ : ∀ i, -Real.pi ≤ φ i ∧ φ i < Real.pi)
    {θ : ℝ} (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ 0) :
    Fintype.card ι ≤ angleSemicircleCount φ θ +
      angleSemicircleCount φ (θ + Real.pi) := by
  classical
  have hcover : ∀ i : ι,
      semicircleArcMem (φ i) θ ∨
        semicircleArcMem (φ i) (θ + Real.pi) := by
    intro i
    have hshift : 0 ≤ θ + Real.pi := by linarith
    have hshiftpi : θ + Real.pi ≤ Real.pi := by linarith
    by_cases ht : θ < 0
    · rw [semicircleArcMem, semicircleArcMem]
      simp only [ht, if_true, not_lt.mpr hshift, if_false]
      by_cases hleft : φ i < θ
      · exact Or.inl (Or.inl hleft)
      by_cases hright : θ + Real.pi ≤ φ i
      · exact Or.inl (Or.inr hright)
      · right
        constructor <;> linarith
    · have ht0 : θ = 0 := le_antisymm hθhi (le_of_not_gt ht)
      subst θ
      rcases hφ i with ⟨hlo, hhi⟩
      by_cases hi0 : φ i < 0
      · left
        simp [semicircleArcMem, hi0, hlo, (not_lt_of_ge Real.pi_pos.le)]
      · right
        have hi0' : 0 ≤ φ i := le_of_not_gt hi0
        simp [semicircleArcMem, hi0, hi0', hhi,
          (not_lt_of_ge Real.pi_pos.le)]
  let P := Finset.univ.filter fun i => semicircleArcMem (φ i) θ
  let Q := Finset.univ.filter fun i =>
    semicircleArcMem (φ i) (θ + Real.pi)
  have hsub : (Finset.univ : Finset ι) ⊆ P ∪ Q := by
    intro i hi
    simp only [P, Q, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hcover i
  calc
    Fintype.card ι = (Finset.univ : Finset ι).card := by simp
    _ ≤ (P ∪ Q).card := Finset.card_le_card hsub
    _ ≤ P.card + Q.card := Finset.card_union_le P Q
    _ = angleSemicircleCount φ θ +
        angleSemicircleCount φ (θ + Real.pi) := rfl

/-- If every half-open semicircle has at most `n` points, the horizontal
resultant is at most `2n-N`. -/
theorem freiman_angle_semicircle_bound
    (φ : ι → ℝ) (n : ℕ)
    (hφ : ∀ i, -Real.pi ≤ φ i ∧ φ i < Real.pi)
    (hcount : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      angleSemicircleCount φ θ ≤ n) :
    (∑ i, Real.cos (φ i)) ≤ 2 * (n : ℝ) - Fintype.card ι := by
  apply freiman_semicircle_integral_bound φ n hφ hcount
  intro θ hθ
  have hcomp := angleSemicircleCount_complement_lower φ hφ hθ.1 hθ.2
  have hshiftmem : θ + Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hupp := hcount (θ + Real.pi) hshiftmem
  omega

/-- A resultant larger than four fifths forces a half-open semicircle
containing more than nine tenths of the points. -/
theorem exists_halfopen_semicircle_nine_tenths
    (φ : ι → ℝ)
    (hφ : ∀ i, -Real.pi ≤ φ i ∧ φ i < Real.pi)
    (hresult : 4 * (Fintype.card ι : ℝ) <
      5 * ∑ i, Real.cos (φ i)) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      9 * Fintype.card ι < 10 * angleSemicircleCount φ θ := by
  by_contra hnone
  push_neg at hnone
  let n := (9 * Fintype.card ι) / 10
  have hcount : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      angleSemicircleCount φ θ ≤ n := by
    intro θ hθ
    dsimp [n]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).2
    simpa [mul_comm] using hnone θ hθ
  have hbound := freiman_angle_semicircle_bound φ n hφ hcount
  have hnNat : 10 * n ≤ 9 * Fintype.card ι := by
    dsimp [n]
    simpa [mul_comm] using Nat.div_mul_le_self (9 * Fintype.card ι) 10
  have hnR : 10 * (n : ℝ) ≤ 9 * (Fintype.card ι : ℝ) := by
    exact_mod_cast hnNat
  nlinarith

end Erdos336
