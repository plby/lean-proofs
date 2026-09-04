import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite bounded differences

A denominator-explicit McDiarmid inequality for a uniform finite product.
The proof reduces the one-coordinate step to Mathlib's Hoeffding lemma and
then performs the Doob-style product induction by finite sums.
-/

open MeasureTheory ProbabilityTheory

namespace Erdos19

noncomputable section

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma integral_uniform_fintype (f : Ω → ℝ) :
    letI : MeasurableSpace Ω := ⊤
    ∫ x, f x ∂(PMF.uniformOfFintype Ω).toMeasure =
      (∑ x, f x) / Fintype.card Ω := by
  let : MeasurableSpace Ω := ⊤
  rw [integral_fintype Integrable.of_finite]
  have hx (x : Ω) :
      (PMF.uniformOfFintype Ω).toMeasure.real {x} =
        (1 : ℝ) / Fintype.card Ω := by
    rw [Measure.real_def, PMF.toMeasure_uniformOfFintype_apply]
    · simp
    · exact MeasurableSpace.measurableSet_top
  simp_rw [hx]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma finite_hoeffding_mgf (f : Ω → ℝ) {a b t : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) :
    (∑ x, Real.exp (t * (f x - (∑ y, f y) / Fintype.card Ω))) /
        Fintype.card Ω ≤
      Real.exp (((‖b - a‖₊ : ℝ) / 2) ^ 2 * t ^ 2 / 2) := by
  let : MeasurableSpace Ω := ⊤
  let μ := (PMF.uniformOfFintype Ω).toMeasure
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ)
    (X := f) measurable_from_top.aemeasurable
    (ae_of_all μ hf)
  have hmgf := hsub.mgf_le t
  rw [mgf, integral_uniform_fintype] at hmgf
  rw [integral_uniform_fintype] at hmgf
  simpa [μ] using hmgf

noncomputable def finiteAverage {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card A

lemma finiteAverage_finSucc {K : Type*} [Fintype K] [Nonempty K]
    (n : ℕ) (f : (Fin (n + 1) → K) → ℝ) :
    finiteAverage f = finiteAverage (fun a : K ↦
      finiteAverage (fun tail : Fin n → K ↦
        f ((Fin.succFunEquiv K n).symm (tail, a)))) := by
  classical
  unfold finiteAverage
  have hsum :
      (∑ x : Fin (n + 1) → K, f x) =
        ∑ a : K, ∑ tail : Fin n → K,
          f ((Fin.succFunEquiv K n).symm (tail, a)) := by
    calc
      (∑ x : Fin (n + 1) → K, f x) =
          ∑ p : (Fin n → K) × K,
            f ((Fin.succFunEquiv K n).symm p) := by
        exact ((Fin.succFunEquiv K n).symm.sum_comp f).symm
      _ = ∑ tail : Fin n → K, ∑ a : K,
          f ((Fin.succFunEquiv K n).symm (tail, a)) :=
        Fintype.sum_prod_type _
      _ = ∑ a : K, ∑ tail : Fin n → K,
          f ((Fin.succFunEquiv K n).symm (tail, a)) := by
        rw [Finset.sum_comm]
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin, pow_succ,
    Nat.cast_pow, Nat.cast_mul]
  have hK : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  field_simp [hK]
  rw [← Finset.sum_div]
  field_simp [hK]

lemma succFunEquiv_symm_eq_lastCases {K : Type*} (n : ℕ)
    (tail : Fin n → K) (a : K) :
    (Fin.succFunEquiv K n).symm (tail, a) = Fin.lastCases a tail := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [Fin.lastCases_last]
    change Fin.append tail (fun _ : Fin 1 ↦ a) (Fin.last n) = a
    rw [show Fin.last n = Fin.natAdd n (0 : Fin 1) by ext; simp]
    exact Fin.append_right tail (fun _ : Fin 1 ↦ a) 0
  · rw [Fin.lastCases_castSucc]
    change Fin.append tail (fun _ : Fin 1 ↦ a) (Fin.castAdd 1 j) = tail j
    exact Fin.append_left tail (fun _ : Fin 1 ↦ a) j

def RealCoordinateLipschitzFin {K : Type*} {n : ℕ}
    (f : (Fin n → K) → ℝ) (c : ℝ) : Prop :=
  ∀ x y i, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c

lemma abs_finiteAverage_sub_le {A : Type*} [Fintype A] [Nonempty A]
    {f g : A → ℝ} {c : ℝ} (h : ∀ x, |f x - g x| ≤ c) :
    |finiteAverage f - finiteAverage g| ≤ c := by
  classical
  let x0 : A := Classical.choice (inferInstance : Nonempty A)
  have hc : 0 ≤ c := (abs_nonneg (f x0 - g x0)).trans (h x0)
  unfold finiteAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div]
  have hcard : |(Fintype.card A : ℝ)| = Fintype.card A := by
    rw [abs_of_nonneg]
    positivity
  rw [hcard]
  have hsum : abs (∑ x : A, (f x - g x)) ≤ ∑ _x : A, c := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun x _hx ↦ h x)
  have hcardpos : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  calc
    abs (∑ x : A, (f x - g x)) / Fintype.card A ≤
        (∑ _x : A, c) / Fintype.card A :=
      div_le_div_of_nonneg_right hsum hcardpos.le
    _ = c := by
      simp [hcardpos.ne']

lemma RealCoordinateLipschitzFin.section
    {K : Type*} {n : ℕ} {f : (Fin (n + 1) → K) → ℝ} {c : ℝ}
    (h : RealCoordinateLipschitzFin f c) (a : K) :
    RealCoordinateLipschitzFin
      (fun tail : Fin n → K ↦ f (Fin.lastCases a tail)) c := by
  intro x y i hxy
  apply h (Fin.lastCases a x) (Fin.lastCases a y) i.castSucc
  intro j hj
  revert hj
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · intro _hj
    simp
  · intro hj
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    apply hxy k
    intro hki
    subst k
    exact hj rfl

lemma RealCoordinateLipschitzFin.sectionAverage_abs_sub_le
    {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    {f : (Fin (n + 1) → K) → ℝ} {c : ℝ}
    (h : RealCoordinateLipschitzFin f c) (a b : K) :
    |finiteAverage (fun tail : Fin n → K ↦ f (Fin.lastCases a tail)) -
      finiteAverage (fun tail : Fin n → K ↦ f (Fin.lastCases b tail))| ≤ c := by
  apply abs_finiteAverage_sub_le
  intro tail
  apply h (Fin.lastCases a tail) (Fin.lastCases b tail) (Fin.last n)
  intro j hj
  revert hj
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · intro hj
    exact (hj rfl).elim
  · intro _hj
    simp

lemma finiteAverage_neg {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    finiteAverage (fun x ↦ -f x) = -finiteAverage f := by
  classical
  unfold finiteAverage
  rw [Finset.sum_neg_distrib]
  ring

lemma finiteAverage_const_mul {A : Type*} [Fintype A] [Nonempty A]
    (a : ℝ) (f : A → ℝ) :
    finiteAverage (fun x ↦ a * f x) = a * finiteAverage f := by
  classical
  unfold finiteAverage
  rw [← Finset.mul_sum]
  ring

lemma finite_boundedDifferences_mgf
    {K : Type*} [Fintype K] [Nonempty K]
    (n : ℕ) (f : (Fin n → K) → ℝ) {c t : ℝ}
    (hc : 0 ≤ c) (hLip : RealCoordinateLipschitzFin f c) :
    finiteAverage (fun x ↦ Real.exp (t * (finiteAverage f - f x))) ≤
      Real.exp (n * c ^ 2 * t ^ 2 / 2) := by
  induction n with
  | zero =>
      have hfun : ∀ x y : Fin 0 → K, x = y := fun x y ↦ Subsingleton.elim _ _
      let x0 : Fin 0 → K := Fin.elim0
      have havg : finiteAverage f = f x0 := by
        unfold finiteAverage
        simp [hfun _ x0]
      simp [havg, hfun _ x0, finiteAverage]
  | succ n ih =>
      classical
      let sect : K → (Fin n → K) → ℝ := fun a tail ↦
        f (Fin.lastCases a tail)
      let m : K → ℝ := fun a ↦ finiteAverage (sect a)
      have havg : finiteAverage f = finiteAverage m := by
        rw [finiteAverage_finSucc n f]
        apply congrArg finiteAverage
        funext a
        apply congrArg finiteAverage
        funext tail
        rw [succFunEquiv_symm_eq_lastCases]
      have hsection (a : K) : RealCoordinateLipschitzFin (sect a) c := by
        exact hLip.section a
      have hinner (a : K) :
          finiteAverage (fun tail : Fin n → K ↦
            Real.exp (t * (m a - sect a tail))) ≤
            Real.exp (n * c ^ 2 * t ^ 2 / 2) := by
        exact ih (sect a) (hsection a)
      let a0 : K := Classical.choice (inferInstance : Nonempty K)
      have hmabs (a : K) : |m a - m a0| ≤ c := by
        exact hLip.sectionAverage_abs_sub_le a a0
      have hmrange (a : K) :
          -m a ∈ Set.Icc (-m a0 - c) (-m a0 + c) := by
        have habs := (abs_le.mp (hmabs a))
        constructor <;> linarith
      have hHoeff := finite_hoeffding_mgf (fun a : K ↦ -m a)
        (t := t) hmrange
      have hcenter (a : K) :
          -m a - (∑ y : K, -m y) / Fintype.card K =
            finiteAverage f - m a := by
        rw [show (∑ y : K, -m y) / Fintype.card K = -finiteAverage m by
          simpa [finiteAverage] using finiteAverage_neg m]
        rw [havg]
        ring
      have hHoeff' :
          finiteAverage (fun a : K ↦
            Real.exp (t * (finiteAverage f - m a))) ≤
            Real.exp (c ^ 2 * t ^ 2 / 2) := by
        simp_rw [hcenter] at hHoeff
        have hnorm : (‖(-m a0 + c) - (-m a0 - c)‖₊ : ℝ) = 2 * c := by
          rw [show (-m a0 + c) - (-m a0 - c) = 2 * c by ring]
          simp [hc]
        calc
          finiteAverage (fun a : K ↦
              Real.exp (t * (finiteAverage f - m a))) ≤
              Real.exp (((‖(-m a0 + c) - (-m a0 - c)‖₊ : ℝ) / 2) ^ 2 *
                t ^ 2 / 2) := hHoeff
          _ = Real.exp (c ^ 2 * t ^ 2 / 2) := by
            rw [hnorm]
            ring_nf
      rw [finiteAverage_finSucc n
        (fun x ↦ Real.exp (t * (finiteAverage f - f x)))]
      simp_rw [succFunEquiv_symm_eq_lastCases]
      change finiteAverage (fun a : K ↦ finiteAverage (fun tail : Fin n → K ↦
        Real.exp (t * (finiteAverage f - sect a tail)))) ≤ _
      have hfactor (a : K) :
          finiteAverage (fun tail : Fin n → K ↦
            Real.exp (t * (finiteAverage f - sect a tail))) =
            Real.exp (t * (finiteAverage f - m a)) *
              finiteAverage (fun tail : Fin n → K ↦
                Real.exp (t * (m a - sect a tail))) := by
        rw [← finiteAverage_const_mul]
        apply congrArg finiteAverage
        funext tail
        rw [← Real.exp_add]
        congr 1
        ring
      simp_rw [hfactor]
      calc
        finiteAverage (fun a : K ↦
            Real.exp (t * (finiteAverage f - m a)) *
              finiteAverage (fun tail : Fin n → K ↦
                Real.exp (t * (m a - sect a tail)))) ≤
            finiteAverage (fun a : K ↦
              Real.exp (t * (finiteAverage f - m a)) *
                Real.exp (n * c ^ 2 * t ^ 2 / 2)) := by
          unfold finiteAverage
          apply div_le_div_of_nonneg_right
          · apply Finset.sum_le_sum
            intro a _ha
            exact mul_le_mul_of_nonneg_left (hinner a) (Real.exp_pos _).le
          · positivity
        _ = Real.exp (n * c ^ 2 * t ^ 2 / 2) *
            finiteAverage (fun a : K ↦
              Real.exp (t * (finiteAverage f - m a))) := by
          unfold finiteAverage
          rw [← Finset.sum_mul]
          ring
        _ ≤ Real.exp (n * c ^ 2 * t ^ 2 / 2) *
            Real.exp (c ^ 2 * t ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left hHoeff' (Real.exp_pos _).le
        _ = Real.exp ((↑(n + 1) : ℝ) * c ^ 2 * t ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

def finiteLowerTail {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (f : (Fin n → K) → ℝ) (ε : ℝ) : Finset (Fin n → K) :=
  Finset.univ.filter fun x ↦ ε ≤ finiteAverage f - f x

lemma finite_boundedDifferences_lowerTail
    {K : Type*} [Fintype K] [Nonempty K]
    (n : ℕ) (f : (Fin n → K) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε)
    (hn : 0 < n) (hLip : RealCoordinateLipschitzFin f c) :
    ((finiteLowerTail f ε).card : ℝ) / Fintype.card (Fin n → K) ≤
      Real.exp (-ε ^ 2 / (2 * n * c ^ 2)) := by
  classical
  let q : ℝ := Fintype.card (Fin n → K)
  let u : ℝ := ε / (n * c ^ 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * c ^ 2 := mul_pos hnR (sq_pos_of_pos hc)
  have hu : 0 ≤ u := div_nonneg hε hden.le
  have hterm (x : Fin n → K) (hx : x ∈ finiteLowerTail f ε) :
      Real.exp (u * ε) ≤ Real.exp (u * (finiteAverage f - f x)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hu
    exact (Finset.mem_filter.mp hx).2
  have hsubset : finiteLowerTail f ε ⊆ Finset.univ := Finset.subset_univ _
  have hsum :
      (finiteLowerTail f ε).card * Real.exp (u * ε) ≤
        ∑ x : Fin n → K, Real.exp (u * (finiteAverage f - f x)) := by
    calc
      (finiteLowerTail f ε).card * Real.exp (u * ε) =
          ∑ _x ∈ finiteLowerTail f ε, Real.exp (u * ε) := by simp
      _ ≤ ∑ x ∈ finiteLowerTail f ε,
          Real.exp (u * (finiteAverage f - f x)) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hterm x hx
      _ ≤ ∑ x : Fin n → K,
          Real.exp (u * (finiteAverage f - f x)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro x _hx _hnot
        exact (Real.exp_pos _).le
  have hmgf := finite_boundedDifferences_mgf n f (t := u) hc.le hLip
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  have hprobMul :
      (((finiteLowerTail f ε).card : ℝ) / q) * Real.exp (u * ε) ≤
        Real.exp (n * c ^ 2 * u ^ 2 / 2) := by
    calc
      (((finiteLowerTail f ε).card : ℝ) / q) * Real.exp (u * ε) =
          ((finiteLowerTail f ε).card * Real.exp (u * ε)) / q := by ring
      _ ≤ (∑ x : Fin n → K,
          Real.exp (u * (finiteAverage f - f x))) / q :=
        div_le_div_of_nonneg_right hsum hq.le
      _ ≤ Real.exp (n * c ^ 2 * u ^ 2 / 2) := by
        simpa [q, finiteAverage] using hmgf
  calc
    ((finiteLowerTail f ε).card : ℝ) / Fintype.card (Fin n → K) =
        (((finiteLowerTail f ε).card : ℝ) / q) := rfl
    _ ≤ Real.exp (n * c ^ 2 * u ^ 2 / 2) / Real.exp (u * ε) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hprobMul
    _ = Real.exp (-ε ^ 2 / (2 * n * c ^ 2)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [u]
      field_simp
      ring

end

end Erdos19
