/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Finite concentration inequalities for Erdős Problem 88

The results in this file use explicit counting measure.  The main theorem is
the exponential-moment form of McDiarmid's inequality on a finite Boolean
cube, followed by its optimized one-sided Azuma--Hoeffding tail bound.
-/

open scoped BigOperators

namespace Erdos88
namespace Concentration

open Classical Finset Real

section UniformFinite

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def uniformExpectation (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

noncomputable def uniformProbability (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

@[simp] lemma uniformExpectation_const (c : ℝ) :
    uniformExpectation (fun _ : Ω => c) = c := by
  simp [uniformExpectation]

lemma uniformExpectation_add (X Y : Ω → ℝ) :
    uniformExpectation (fun ω => X ω + Y ω) =
      uniformExpectation X + uniformExpectation Y := by
  simp [uniformExpectation, Finset.sum_add_distrib, add_div]

lemma uniformProbability_nonneg (P : Ω → Prop) :
    0 ≤ uniformProbability P := by
  classical
  rw [uniformProbability]
  positivity

lemma uniformProbability_le_one (P : Ω → Prop) :
    uniformProbability P ≤ 1 := by
  classical
  rw [uniformProbability, div_le_one (by exact_mod_cast Fintype.card_pos)]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset P Finset.univ)

lemma uniformProbability_mono {P Q : Ω → Prop}
    (hPQ : ∀ ω, P ω → Q ω) :
    uniformProbability P ≤ uniformProbability Q := by
  classical
  rw [uniformProbability, uniformProbability,
    div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < Fintype.card Ω)]
  exact_mod_cast Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hPQ ω hω)

/-- Counting form of Markov's inequality. -/
lemma counting_markov (g : Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ ω, 0 ≤ g ω) :
    ((Finset.univ.filter fun ω => g ω ≥ c).card : ℝ) * c ≤ ∑ ω, g ω := by
  have h := Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) =>
    show g x ≥ if g x ≥ c then c else 0 by split_ifs <;> linarith [hg x]
  simpa [Finset.sum_ite] using h

/-- Division-free second-moment form of Markov's inequality. -/
lemma counting_second_moment_tail (X : Ω → ℝ) (u : ℝ) (hu : 0 < u) :
    ((Finset.univ.filter fun ω => u ≤ |X ω|).card : ℝ) * u ^ 2 ≤
      ∑ ω, |X ω| ^ 2 := by
  have hfilter :
      Finset.univ.filter (fun ω => u ≤ |X ω|) =
        Finset.univ.filter (fun ω => |X ω| ^ 2 ≥ u ^ 2) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (sq_le_sq₀ hu.le (abs_nonneg (X ω))).symm
  rw [hfilter]
  exact counting_markov (fun ω => |X ω| ^ 2) (u ^ 2) (sq_pos_of_pos hu)
    (fun ω => sq_nonneg _)

end UniformFinite

section CubeAzuma

lemma avg_exp_le (a d : ℝ) :
    exp (a + d) + exp (a - d) ≤ 2 * exp (a + d ^ 2 / 2) := by
  have hdiv : Real.exp d + Real.exp (-d) ≤ 2 * Real.exp (d ^ 2 / 2) := by
    have h := Real.cosh_le_exp_half_sq d
    rw [Real.cosh_eq] at h
    linarith
  calc
    Real.exp (a + d) + Real.exp (a - d) =
        Real.exp a * (Real.exp d + Real.exp (-d)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp a * (2 * Real.exp (d ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hdiv (Real.exp_nonneg a)
    _ = 2 * Real.exp (a + d ^ 2 / 2) := by
      rw [Real.exp_add]
      ring

lemma sum_fin_succ_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → Bool, f x =
      ∑ b : Bool, ∑ y : Fin n → Bool, f (Fin.cons b y) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun x _ => (x 0, x ∘ Fin.succ)) ?_ ?_ ?_ ?_ <;>
    simp +decide
  · exact fun a₁ a₂ h₁ h₂ => funext fun i => by
      induction i using Fin.inductionOn <;> simp_all +decide [funext_iff]
  · exact ⟨fun b => ⟨Fin.cons false b, rfl, rfl⟩,
      fun b => ⟨Fin.cons true b, rfl, rfl⟩⟩
  · exact fun x => by
      congr
      ext i
      induction i using Fin.inductionOn <;> aesop

noncomputable def avgFn {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun y => (f (Fin.cons false y) + f (Fin.cons true y)) / 2

lemma avgFn_mean {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ y : Fin n → Bool, avgFn f y) / ((2 : ℝ) ^ n) =
      (∑ x : Fin (n + 1) → Bool, f x) / ((2 : ℝ) ^ (n + 1)) := by
  simp +decide [sum_fin_succ_eq, avgFn]
  simpa only [← Finset.sum_div _ _ _, Finset.sum_add_distrib, add_comm] using by ring

lemma avgFn_bounded_diff {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ)
    (b : Fin (n + 1) → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) :
    ∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |avgFn f x - avgFn f y| ≤ b (Fin.succ i) := by
  intros i x y hxy
  simp [avgFn]
  rw [abs_le]
  constructor <;>
    linarith [abs_le.mp (hbd i.succ (Fin.cons false x) (Fin.cons false y)
      (fun j hj => by cases j using Fin.inductionOn <;> aesop)),
      abs_le.mp (hbd i.succ (Fin.cons true x) (Fin.cons true y)
        (fun j hj => by cases j using Fin.inductionOn <;> aesop))]

/-- Exponential-moment form of bounded differences on a finite Boolean cube. -/
theorem cube_exp_moment_bound (n : ℕ) (f : (Fin n → Bool) → ℝ)
    (b : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (lam : ℝ) :
    ∑ x : Fin n → Bool,
        exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≤
      ((2 : ℝ) ^ n) * exp (lam ^ 2 / 8 * ∑ i, (b i) ^ 2) := by
  revert n f b hbd
  refine fun n => Nat.recOn n ?_ ?_
  · intros f b hbd
    norm_num
  · intro n ih f b hbd
    set μ : ℝ := (∑ x, f x) / 2 ^ (n + 1)
    set g : (Fin n → Bool) → ℝ := avgFn f
    set μg : ℝ := (∑ y, g y) / 2 ^ n
    have hμg : μg = μ := avgFn_mean f
    have hdecomp : ∀ y : Fin n → Bool,
        Real.exp (lam * (μ - f (Fin.cons false y))) +
            Real.exp (lam * (μ - f (Fin.cons true y))) ≤
          2 * Real.exp (lam * (μg - g y) + lam ^ 2 * (b 0) ^ 2 / 8) := by
      intro y
      set d := (f (Fin.cons true y) - f (Fin.cons false y)) / 2
      have hexp :
          Real.exp (lam * (μ - f (Fin.cons false y))) +
              Real.exp (lam * (μ - f (Fin.cons true y))) ≤
            2 * Real.exp (lam * (μg - g y) + lam ^ 2 * d ^ 2 / 2) := by
        convert avg_exp_le (lam * (μg - g y)) (lam * d) using 1 <;> ring_nf
        simp +zetaDelta at *
        rw [hμg]
        ring_nf
        unfold avgFn
        ring_nf
      have hdbound : d ^ 2 ≤ (b 0) ^ 2 / 4 := by
        simp +zetaDelta at *
        nlinarith only [abs_le.mp (hbd 0 (Fin.cons true y) (Fin.cons false y)
          (fun j hj => by cases j using Fin.inductionOn <;> tauto))]
      exact hexp.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) zero_le_two)
    have hind :
        ∑ y : Fin n → Bool, Real.exp (lam * (μg - g y)) ≤
          2 ^ n * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i.succ) ^ 2) := by
      exact ih g (fun i => b (Fin.succ i)) (avgFn_bounded_diff f b hbd)
    have hcombined :
        ∑ x : Fin (n + 1) → Bool, Real.exp (lam * (μ - f x)) ≤
          2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) *
            ∑ y : Fin n → Bool, Real.exp (lam * (μg - g y)) := by
      calc
        ∑ x : Fin (n + 1) → Bool, Real.exp (lam * (μ - f x)) =
            ∑ y : Fin n → Bool,
              (Real.exp (lam * (μ - f (Fin.cons false y))) +
                Real.exp (lam * (μ - f (Fin.cons true y)))) := by
          rw [sum_fin_succ_eq, Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => by
            rw [Finset.sum_eq_add false true] <;> simp +decide
        _ ≤ ∑ y : Fin n → Bool,
            2 * Real.exp (lam * (μg - g y) + lam ^ 2 * (b 0) ^ 2 / 8) := by
          exact Finset.sum_le_sum fun y _ => hdecomp y
        _ = 2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) *
            ∑ y : Fin n → Bool, Real.exp (lam * (μg - g y)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by
            rw [Real.exp_add]
            ring
    refine le_trans (hcombined.trans
      (mul_le_mul_of_nonneg_left hind (by positivity))) ?_
    calc
      2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) *
          (2 ^ n * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i.succ) ^ 2)) =
        2 ^ n.succ * Real.exp
          (lam ^ 2 * (b 0) ^ 2 / 8 +
            lam ^ 2 / 8 * ∑ i : Fin n, (b i.succ) ^ 2) := by
        rw [Real.exp_add, pow_succ]
        norm_num
        ring
      _ = 2 ^ n.succ *
          Real.exp (lam ^ 2 / 8 * ∑ i : Fin n.succ, (b i) ^ 2) := by
        congr 1
        rw [Fin.sum_univ_succ]
        ring_nf
      _ ≤ 2 ^ n.succ *
          Real.exp (lam ^ 2 / 8 * ∑ i : Fin n.succ, (b i) ^ 2) := le_rfl

/-- Optimized one-sided Azuma--Hoeffding/McDiarmid inequality on a Boolean cube. -/
theorem cube_lower_tail :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let μ := (∑ x : Fin n → Bool, f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter fun x : Fin n → Bool => f x ≤ μ - t).card : ℝ) ≤
      (2 ^ n : ℝ) * exp (-2 * t ^ 2 / ∑ i, (b i) ^ 2) := by
  intros n f b hbd hb t ht
  set lam := 4 * t / (∑ i, b i ^ 2)
  have hexp :
      ∑ x : Fin n → Bool,
          Real.exp (lam * ((∑ z, f z) / ((2 : ℝ) ^ n) - f x)) ≤
        ((2 : ℝ) ^ n) *
          Real.exp (lam ^ 2 / 8 * ∑ i, (b i) ^ 2) :=
    cube_exp_moment_bound n f b hbd lam
  have hmarkov :
      ((Finset.univ.filter fun x =>
          Real.exp (lam * ((∑ z, f z) / ((2 : ℝ) ^ n) - f x)) ≥
            Real.exp (lam * t)).card : ℝ) ≤
        ((2 : ℝ) ^ n) *
          Real.exp (lam ^ 2 / 8 * ∑ i, (b i) ^ 2 - lam * t) := by
    have hm :
        ((Finset.univ.filter fun x =>
            Real.exp (lam * ((∑ z, f z) / ((2 : ℝ) ^ n) - f x)) ≥
              Real.exp (lam * t)).card : ℝ) * Real.exp (lam * t) ≤
          ∑ x : Fin n → Bool,
            Real.exp (lam * ((∑ z, f z) / ((2 : ℝ) ^ n) - f x)) :=
      counting_markov
        (fun x => Real.exp (lam * ((∑ z, f z) / 2 ^ n - f x)))
        (Real.exp (lam * t)) (Real.exp_pos _) (fun x => Real.exp_nonneg _)
    rw [Real.exp_sub, ← mul_div_assoc, le_div_iff₀ (Real.exp_pos _)]
    linarith
  refine le_trans ?_ (hmarkov.trans ?_)
  · norm_num
    exact Finset.card_mono fun x hx => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        nlinarith [Finset.mem_filter.mp hx,
          show 0 ≤ lam by
            exact div_nonneg (mul_nonneg zero_le_four ht)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)]⟩
  · grind

end CubeAzuma

end Concentration
end Erdos88

/-! ## Conditional Hoeffding bridge

This measure-theoretic lemma is independent of the finite-cube implementation
above.  It converts the bounded, conditionally centered increments of a Doob
martingale into the exact hypothesis expected by Mathlib's Azuma--Hoeffding
theorem. -/

open MeasureTheory Real
open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {a : ℝ}

/-- A bounded, conditionally centered increment is conditionally
sub-Gaussian. -/
lemma hasCondSubgaussianMGF_of_abs_le_of_condExp_eq_zero
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (ha : 0 ≤ a) (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ a)
    (hmean : μ[Y | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm Y ((Real.toNNReal a) ^ 2) μ := by
  have hYint : Integrable Y μ :=
    Integrable.of_bound hY.aestronglyMeasurable a (by
      filter_upwards [hbound] with ω hω
      simpa [Real.norm_eq_abs] using hω)
  have hmean_trim : μ[Y | m] =ᵐ[μ.trim hm] 0 :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
      stronglyMeasurable_condExp (by fun_prop) hmean
  have hkernel_mean := condExp_ae_eq_trim_integral_condExpKernel hm hYint
  have hkernel_bound : ∀ᵐ ω' ∂μ.trim hm,
      ∀ᵐ ω ∂condExpKernel μ m ω', |Y ω| ≤ a := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim]
    exact hbound
  change Kernel.HasSubgaussianMGF Y ((Real.toNNReal a) ^ 2)
    (condExpKernel μ m) (μ.trim hm)
  refine ⟨?_, ?_⟩
  · rw [condExpKernel_comp_trim]
    intro t
    exact integrable_exp_mul_of_mem_Icc hY.aemeasurable (by
      filter_upwards [hbound] with ω hω
      exact ⟨(abs_le.mp hω).1, (abs_le.mp hω).2⟩)
  · filter_upwards [hkernel_bound, hkernel_mean, hmean_trim] with ω' hb hm' hm0
    have hprob : IsProbabilityMeasure (condExpKernel μ m ω') := by infer_instance
    have hsg : HasSubgaussianMGF Y ((‖a - (-a)‖₊ / 2) ^ 2)
        (condExpKernel μ m ω') :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        hY.aemeasurable
        (by
          filter_upwards [hb] with ω hω
          exact ⟨(abs_le.mp hω).1, (abs_le.mp hω).2⟩)
        (hm'.symm.trans hm0)
    have hc : ((‖a - (-a)‖₊ / 2) ^ 2) = (Real.toNNReal a) ^ 2 := by
      rw [sub_neg_eq_add, Real.nnnorm_of_nonneg (add_nonneg ha ha)]
      rw [Real.toNNReal_of_nonneg ha]
      congr 1
      apply NNReal.eq
      simp
    exact hc ▸ hsg.mgf_le

end ProbabilityTheory
