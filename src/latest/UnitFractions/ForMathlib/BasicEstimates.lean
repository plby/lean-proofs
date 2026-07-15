import Mathlib
import UnitFractions.ForMathlib.IntegralRPow
import UnitFractions.ForMathlib.Misc

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology

/-!
This file contains the Lean 4 statement port of the old Lean 3
`for_mathlib/basic_estimates` file.

When a result already exists upstream in Mathlib 4, this file prefers the
Mathlib version instead of reintroducing a duplicate local theorem.
-/

theorem tendsto_log_coe_at_top : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_coe_at_top : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_coe_at_top

section Summatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ n ≤ x, a n`.
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n

theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]

theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]

end Summatory

section PrimeSummatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ p ≤ x, a p`
where `p` ranges over primes.
-/
def prime_summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ (Finset.Icc k ⌊x⌋₊).filter Nat.Prime, a n

theorem prime_summatory_eq_summatory (a : ℕ → M) :
    prime_summatory a = summatory (fun n => if n.Prime then a n else 0) := by
  ext k x
  simp [prime_summatory, summatory, Finset.sum_filter]

end PrimeSummatory

def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, Int.fract t * (t ^ 2)⁻¹

namespace Nat

theorem cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end Nat

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
  by nlinarith [log_le_sub_one_of_pos hx]

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

scoped[Chebyshev] notation "ϑ" => chebyshev_first

theorem chebyshev_first_pos {x : ℝ} (hx : 2 ≤ x) : 0 < chebyshev_first x :=
  Chebyshev.theta_pos hx

theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (x + 1)]
  congr 1
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, and_assoc]
  constructor
  · rintro ⟨hp1, hp2⟩
    exact ⟨hp2.one_le, hp1, hp2⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp2, hp3⟩

def partial_euler_product (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] theorem partial_euler_product_zero : partial_euler_product 0 = 1 := by
  simp [partial_euler_product]

theorem partial_euler_trivial_lower_bound {n : ℕ} : 1 ≤ partial_euler_product n := by
  refine Finset.one_le_prod ?_
  intro p hp
  simp only [mem_filter] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by nlinarith [inv_nonneg.2 (show 0 ≤ (p : ℝ) by positivity)])

theorem trivial_divisor_bound {n : ℕ} : (ArithmeticFunction.sigma 0 n : ℝ) ≤ n := by
  exact_mod_cast (show ArithmeticFunction.sigma 0 n ≤ n by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Nat.card_divisors_le_self n)

theorem my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n := by
  rw [summatory_eq_floor (a := a) (k := k) x, Nat.floor_eq_on_Ico n x hx]

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

lemma summatory_zero_eq_of_lt {x : ℝ} (hx : x < 1) :
  summatory a 0 x = a 0 := by
  rw [summatory_eq_floor (a := a) (k := 0) x, Nat.floor_eq_zero.mpr hx, summatory_nat]
  simp

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n+1) = a (n + 1) + summatory a k n := by
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by exact_mod_cast rfl]
  rw [summatory_nat, summatory_nat]
  have hIcc : Finset.Icc k (n + 1) = insert (n + 1) (Finset.Icc k n) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert]
  · intro hmem
    exact Nat.not_succ_le_self n (Finset.mem_Icc.mp hmem).2

lemma summatory_succ_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) (k : ℕ) (n : ℕ)
  (hk : k ≤ n + 1) :
  a (n + 1) = summatory a k (n + 1) - summatory a k n := by
  rw [summatory_succ (a := a) k n hk, add_sub_cancel_right]

lemma summatory_eq_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a 1 n - summatory a 1 (n - 1) := by
  intro n hn
  cases n with
  | zero =>
      cases hn rfl
  | succ n =>
      simpa using summatory_succ_sub (a := a) 1 n (by omega)

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

lemma summatory_nonneg' {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] {a : ℕ → M}
    (k : ℕ) (x : ℝ) (ha : ∀ (i : ℕ), k ≤ i → (i : ℝ) ≤ x → 0 ≤ a i)
    (hk : k ≠ 0) :
  0 ≤ summatory a k x := by
  rw [summatory]
  refine Finset.sum_nonneg ?_
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi0 : i ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_iff_ne_zero.mpr hk) hi.1)
  exact ha i hi.1 ((Nat.le_floor_iff' hi0).1 hi.2)

lemma summatory_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] (a : ℕ → M)
    (x : ℝ) (k : ℕ) (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x := by
  rw [summatory]
  exact Finset.sum_nonneg (fun i _ ↦ ha i)

lemma summatory_monotone_of_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (a : ℕ → M)
  (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  Monotone (summatory a k) := by
  intro i j hij
  rw [summatory, summatory]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hij)
  · intro n _ _; exact ha n

lemma abs_summatory_bound {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k z, ‖a i‖ := by
  exact (abs_summatory_le_sum a).trans <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hx))
      (by intro i _ _; exact norm_nonneg _)

@[fun_prop] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor

end SummatoryExtra

namespace ArithmeticFunction

lemma sigma_zero_eq_zeta_mul_zeta :
  ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  ArithmeticFunction.sigma 0 i = ∑ _ ∈ i.divisors, 1 := by
  rw [ArithmeticFunction.sigma_apply, Finset.sum_congr rfl]
  intro _ _
  simp

end ArithmeticFunction

namespace Finset

lemma Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

lemma prod_eq_prod_iff_of_le' {ι : Type*}
  {s : Finset ι} {f g : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro hf h
    constructor
    · intro _ i hi
      exact False.elim (Finset.notMem_empty i hi)
    · intro _
      simp
  · intro a s ha ih hf h
    constructor
    · intro hprod
      rw [Finset.prod_insert ha, Finset.prod_insert ha] at hprod
      have hs_le : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        Finset.prod_le_prod' (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hs_pos : 0 < ∏ i ∈ s, f i :=
        Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hfa : f a = g a := by
        rcases lt_or_eq_of_le (h a (Finset.mem_insert_self a s)) with hlt | hEq
        · have hlt' : f a * ∏ i ∈ s, f i < g a * ∏ i ∈ s, g i := by
            exact (Nat.mul_lt_mul_of_pos_right hlt hs_pos).trans_le (Nat.mul_le_mul_left _ hs_le)
          exact (False.elim (Nat.lt_irrefl _ (hprod ▸ hlt')))
        · exact hEq
      have hs_eq : ∏ i ∈ s, f i = ∏ i ∈ s, g i := by
        exact Nat.eq_of_mul_eq_mul_left (hf a (Finset.mem_insert_self a s)) (hfa ▸ hprod)
      have hs_all : ∀ i ∈ s, f i = g i :=
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))).1 hs_eq
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hfa
      · exact hs_all i hi
    · intro hall
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [hall a (Finset.mem_insert_self a s)]
      refine congrArg (g a * ·) ?_
      apply (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))).2
      intro i hi
      exact hall i (Finset.mem_insert_of_mem hi)

end Finset

namespace Nat

@[simp] lemma floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

lemma divisors_nonempty_iff {n : ℕ} : n.divisors.Nonempty ↔ n ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty, Nat.divisors_eq_empty]

end Nat

lemma tendsto_log_log_log_coe_at_top :
    Tendsto (fun x : ℕ ↦ log (log (log (x : ℝ)))) atTop atTop := by
  exact tendsto_log_atTop.comp tendsto_log_log_coe_at_top

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Icc x y) := Integrable.smul b hf'
  refine hsmul.integrable.mono ?_ ?_
  · exact measurable_summatory.aestronglyMeasurable.mul hf'.1
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_)
      (norm_nonneg _)
    · exact hz.2.trans (Nat.le_ceil y)
    · rw [Real.norm_eq_abs]
      exact le_abs_self b

theorem partial_summation_nat {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i) (hf' : IntegrableOn f' (Icc k N)) :
  ∑ n ∈ Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
  let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
  have hc_sum :
      ∑ n ∈ Finset.Icc k N, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k N, f n * c n := by
    rw [show Finset.Icc k N = (Finset.Ioc k N).cons k Finset.left_notMem_Ioc by
      simpa using (Finset.Icc_eq_cons_Ioc hN)]
    rw [Finset.sum_cons]
    have htail :
        ∑ n ∈ Finset.Ioc k N, a n * f n =
          ∑ n ∈ Finset.Ioc k N, if k ≤ n then a n * f n else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
      simp [hk]
    simp [c, mul_comm, htail]
  have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) N)] deriv f := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) N)), f' t = deriv f t
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact (hf t ht).deriv.symm
  have hc_abel := sum_mul_eq_sub_sub_integral_mul' (c := c) (f := f) hN
    (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
  have hc_partial : ∀ n, (∑ i ∈ Finset.Icc 0 n, c i) = summatory a k n := by
    intro n
    calc
      ∑ i ∈ Finset.Icc 0 n, c i = ∑ i ∈ Finset.Icc k n, c i := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi ⊢
          exact ⟨Nat.zero_le _, hi.2⟩
        · intro i hi0 hi
          have hi0' := Finset.mem_Icc.mp hi0
          have hki : ¬ k ≤ i := by
            intro hk
            exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
          simp [c, hki]
      _ = ∑ i ∈ Finset.Icc k n, a i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
        simp [c, hk]
      _ = summatory a k n := by rw [← summatory_nat]
  have hcongr :
      ∀ᵐ t ∂volume,
        t ∈ Set.Ioc (k : ℝ) N →
          deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, summatory_eq_floor (a := a) (k := k) t,
      mul_comm]
  have hIocIcc :
      (∫ t in Set.Ioc (k : ℝ) N, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
        ∫ t in Set.Icc (k : ℝ) N, summatory a k t * f' t := by
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
      setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hc_sum, hc_abel, hc_partial, hc_partial, summatory_self, hIocIcc]
  simp [c, mul_comm]
  ring

theorem partial_summation {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one (a := fun n ↦ a n * f n) hk h,
      summatory_eq_of_lt_one (a := a) hk h, zero_mul]
  · have hle : (k : ℝ) ≤ x := le_of_not_gt h
    have hx : k ≤ ⌊x⌋₊ := by rwa [Nat.le_floor_iff' hk]
    let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
    have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) x)] deriv f := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) x)), f' t = deriv f t
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact (hf t ht).deriv.symm
    have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f)
      (show 0 ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k) hle
      (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
    rw [Nat.floor_natCast] at habel
    have hc_partial : ∀ t : ℝ, (∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) = summatory a k t := by
      intro t
      calc
        ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = ∑ i ∈ Finset.Icc k ⌊t⌋₊, c i := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi0 hi
            have hi0' := Finset.mem_Icc.mp hi0
            have hki : ¬ k ≤ i := by
              intro hk
              exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
            simp [c, hki]
        _ = ∑ i ∈ Finset.Icc k ⌊t⌋₊, a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
          simp [c, hk]
        _ = summatory a k t := by rw [summatory]
    have hsum :
        ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k ⌊x⌋₊, f n * c n := by
      rw [show Finset.Icc k ⌊x⌋₊ = (Finset.Ioc k ⌊x⌋₊).cons k Finset.left_notMem_Ioc by
        simpa using (Finset.Icc_eq_cons_Ioc hx)]
      rw [Finset.sum_cons]
      have htail :
          ∑ n ∈ Finset.Ioc k ⌊x⌋₊, a n * f n =
            ∑ n ∈ Finset.Ioc k ⌊x⌋₊, if k ≤ n then a n * f n else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
        simp [hk]
      simp [c, mul_comm, htail]
    have hcongr :
        ∀ᵐ t ∂volume,
          t ∈ Set.Ioc (k : ℝ) x →
            deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, mul_comm]
    have hIocIcc :
        (∫ t in Set.Ioc (k : ℝ) x, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
          ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
        setIntegral_congr_set Ioc_ae_eq_Icc]
    have hc_k : ∑ i ∈ Finset.Icc 0 k, c i = summatory a k k := by
      simpa using hc_partial (k : ℝ)
    rw [summatory, hsum, habel, hc_partial x, hc_k, summatory_self, hIocIcc]
    simp [c, mul_comm]
    ring

theorem partial_summation_cont {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc

theorem partial_summation' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} (hk : k ≠ 0) (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ici k)) {x : ℝ} :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono_set Icc_subset_Ici_self)

theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Icc_subset_Ici_self)

lemma fract_mul_integrable {f : ℝ → ℝ} (s : Set ℝ)
  (hf' : IntegrableOn f s) :
  IntegrableOn (Int.fract * f) s := by
  refine Integrable.mono hf' ?_ (Filter.Eventually.of_forall ?_)
  · exact measurable_fract.aestronglyMeasurable.mul hf'.1
  · intro x
    simp only [norm_mul, Pi.mul_apply, norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

private lemma harmonic_series_aux_identity {x : ℝ} (hx : 1 ≤ x) :
    summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
      (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
        Int.fract x * x⁻¹ := by
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt (fun x ↦ x⁻¹) (-(i ^ 2)⁻¹) i := by
    intro i hi
    exact hasDerivAt_inv (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun i : ℝ ↦ (i ^ 2)⁻¹) (Ici 1) := by
    refine (ContinuousOn.inv₀ (f := fun i : ℝ ↦ i ^ 2) (s := Ici 1)
      (continuous_pow 2).continuousOn ?_)
    · intro i hi
      exact pow_ne_zero 2 (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont.neg) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_floor, sub_mul, Nat.cast_one]
  · have hEqOn :
        EqOn
          (fun a : ℝ ↦ Int.fract a * (a ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 a * -(a ^ 2)⁻¹)
          (fun y : ℝ ↦ y⁻¹) (Ioc 1 x) := by
      intro y hy
      dsimp
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      rw [hs, mul_neg, sub_neg_eq_add, ← add_mul, Int.fract_add_floor]
      have hycalc : y * (y⁻¹ * y⁻¹) = y⁻¹ := by
        field_simp [hy'.ne']
      simpa [sq, mul_inv, mul_assoc] using hycalc
    have hInt0 :
        ∫ t in Ioc 1 x,
            (Int.fract t * (t ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹) = log x := by
      rw [setIntegral_congr_fun measurableSet_Ioc hEqOn, ← intervalIntegral.integral_of_le hx,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    have hfloor : ((⌊x⌋ : ℝ)) = x - Int.fract x := by
      rw [Int.self_sub_fract]
    have hf :
        Integrable (fun t : ℝ ↦ Int.fract t * (t ^ 2)⁻¹) (volume.restrict (Ioc 1 x)) := by
      exact (fract_mul_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)).integrable
    have hgpos :
        Integrable (fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (volume.restrict (Ioc 1 x)) := by
      exact (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)
        |>.mono_set Ioc_subset_Icc_self).integrable
    have hxinv : x * x⁻¹ = (1 : ℝ) := by
      field_simp [(zero_lt_one.trans_le hx).ne']
    have hA : (x - Int.fract x) * x⁻¹ = 1 - Int.fract x * x⁻¹ := by
      rw [sub_mul, hxinv]
    rw [hfloor, hA] at *
    let I : ℝ := ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹
    let K : ℝ := ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹
    have hIK : I + K = log x := by
      calc
        I + K =
            ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ +
              summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹ := by
                symm
                simpa [I, K] using (integral_add hf hgpos)
        _ = log x := by
          simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using hInt0
    have hJneg :
        ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹ = -K := by
      simpa [K, mul_neg] using
        (integral_neg (f := fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (μ := volume.restrict (Ioc 1 x)))
    have hK : K = log x - I := by
      linarith
    rw [hJneg, hK]
    simp [I, sq, hxinv]
    ring_nf

lemma euler_mascheroni_convergence_rate :
  Asymptotics.IsBigOWith 1 atTop
    (fun x : ℝ ↦ 1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨1, ?_⟩
  intro x hx
  have h : IntegrableOn (fun x : ℝ ↦ Int.fract x * (x ^ 2)⁻¹) (Ioi 1) := by
    refine fract_mul_integrable _ ?_
    exact integrable_on_pow_inv_Ioi one_lt_two zero_lt_one
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ← setIntegral_sdiff measurableSet_Ioc h Ioc_subset_Ioi_self,
    Ioi_diff_Icc hx, norm_of_nonneg]
  · refine (setIntegral_mono_on (h.mono_set (Ioi_subset_Ioi hx))
      (integrable_on_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx))
      measurableSet_Ioi ?_).trans ?_
    · intro t ht
      exact mul_le_of_le_one_left (inv_nonneg.2 (sq_nonneg _)) (Int.fract_lt_one _).le
    · rw [integral_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx)]
      norm_num
  · exact
      setIntegral_nonneg measurableSet_Ioi
        (fun t ht ↦ div_nonneg (Int.fract_nonneg _) (sq_nonneg _))

lemma euler_mascheroni_integral_Ioc_convergence :
  Tendsto (fun x : ℝ ↦ 1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  simpa using
    (euler_mascheroni_convergence_rate.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  Tendsto (fun x : ℝ ↦ (1 : ℝ) - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  refine euler_mascheroni_integral_Ioc_convergence.congr' ?_
  change ∀ᶠ x : ℝ in atTop,
    1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ =
      1 - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹
  rw [eventually_atTop]
  exact ⟨1, fun x hx ↦ by rw [intervalIntegral.integral_of_le hx]⟩

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
      Int.fract x * x⁻¹ := by
  simpa using harmonic_series_aux_identity hx

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le

lemma harmonic_series_is_O_with :
  Asymptotics.IsBigOWith 2 atTop
    (fun x ↦ summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  have hfract :
      Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * x⁻¹) (fun x ↦ x⁻¹) :=
    is_O_with_one_fract_mul _
  refine (euler_mascheroni_convergence_rate.sub hfract).congr' ?_ ?_ Filter.EventuallyEq.rfl
  · norm_num
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (harmonic_series_is_O_aux hx).symm

theorem harmonic_series_real_limit :
    Tendsto (fun x ↦ (∑ i ∈ Finset.Icc 1 ⌊x⌋₊, (i : ℝ)⁻¹) - log x) atTop
      (𝓝 euler_mascheroni) := by
  simpa [summatory] using
    (harmonic_series_is_O_with.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

theorem harmonic_series_limit :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, (i : ℝ)⁻¹) - log n) atTop
      (𝓝 euler_mascheroni) := by
  exact (harmonic_series_real_limit.comp tendsto_natCast_atTop_atTop).congr (fun x ↦ by simp)

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, Int.fract t * t⁻¹) - Int.fract x * log x) := by
  rw [intervalIntegral.integral_of_le hx]
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Ici 1) continuousOn_id ?_
    intro x hx
    exact (zero_lt_one.trans_le hx).ne'
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  clear ps
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_fract, sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left,
    sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← add_assoc, sub_add_cancel, Nat.cast_one,
    ← integral_add]
  · have hEqOn :
        EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Ioc 1 x) := by
      intro y hy
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      dsimp
      rw [hs]
      have hyinv : y * y⁻¹ = (1 : ℝ) := by
        field_simp [hy'.ne']
      calc
        (1 : ℝ) = y * y⁻¹ := by simpa using hyinv.symm
        _ = (Int.fract y + (⌊y⌋ : ℝ)) * y⁻¹ := by
          rw [Int.fract_add_floor]
        _ = Int.fract y * y⁻¹ + (⌊y⌋ : ℝ) * y⁻¹ := by ring
    rw [← integral_one, intervalIntegral.integral_of_le hx,
      setIntegral_congr_fun measurableSet_Ioc hEqOn]
  · refine fract_mul_integrable _ ?_
    exact (cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Ioc_subset_Icc_self

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : Filter ℝ) (h : Tendsto f l atTop)
    (c : ℝ) :
  Asymptotics.IsLittleO l (fun _ : ℝ ↦ c) f := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in atTop, ‖c‖ ≤ ε * ‖x‖ := by
    filter_upwards [eventually_ge_atTop (‖c‖ * ε⁻¹), eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂
    rw [norm_of_nonneg hx₂]
    calc
      ‖c‖ = ε * (‖c‖ * ε⁻¹) := by
        field_simp [hε.ne']
      _ ≤ ε * x := mul_le_mul_of_nonneg_left hx₁ hε.le
  exact h.eventually hbound

lemma is_o_one_log (c : ℝ) : Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ c) log := by
  exact is_o_const_of_tendsto_at_top _ _ Real.tendsto_log_atTop _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  Asymptotics.IsBigOWith c atTop
    (fun x ↦ summatory (fun i ↦ log i) 1 x - (x * log x - x))
    (fun x ↦ log x) := by
  have f₁ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * log x) log :=
    is_O_with_one_fract_mul _
  have f₂ : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 : ℝ)) log := is_o_one_log _
  have f₃ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ ∫ t in 1..x, Int.fract t * t⁻¹) log := by
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        change IntegrableOn (Int.fract * fun y : ℝ ↦ y⁻¹) (Icc 1 x)
        exact fract_mul_integrable (s := Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
        intro y hy
        refine mul_le_of_le_one_left (inv_nonneg.2 (zero_le_one.trans hy.1)) (Int.fract_lt_one _).le
      exact intervalIntegral.integral_mono_on (μ := volume) hx hfract h₁ h₂
    · refine intervalIntegral.integral_nonneg hx ?_
      intro y hy
      exact mul_nonneg (Int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1))
  refine (f₂.add_isBigOWith (f₃.sub f₁) ?_).congr' rfl ?_ Filter.EventuallyEq.rfl
  · norm_num [hc]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa using (summatory_log_aux hx).symm

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (fun n ↦ f n * ⌊x / n⌋) 1 y =
    summatory (fun n ↦ ∑ i ∈ n.divisors, f i) 1 x := by
  simp_rw [summatory, ← Nat.cast_floor_eq_cast_int_floor (div_nonneg hy (Nat.cast_nonneg _)),
    ← summatory_const_one, summatory, Finset.mul_sum, mul_one]
  calc
    ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc 1 ⌊x / i⌋₊, f i
      = ∑ i ∈ Finset.Icc 1 ⌊y⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x / i⌋₊).image (fun j => i * j), f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_image ?_
            intro a ha b hb hab
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            exact Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp hi1) hab
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ i ∈ n.divisors, f i := by
          refine Finset.sum_comm'
            (t := fun i : ℕ => (Finset.Icc 1 ⌊x / i⌋₊).image fun j : ℕ => i * j)
            (t' := (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ)) (s' := fun n : ℕ => n.divisors)
            (f := fun i (_n : ℕ) => f i) ?_
          intro i n
          constructor
          · rintro ⟨hi, hn⟩
            rw [Finset.mem_image] at hn
            rcases hn with ⟨j, hj, rfl⟩
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).1
                  ((Finset.mem_Icc.mp hj).2)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := by
              have hmul : (i : ℝ) * j ≤ (i : ℝ) * (x / i) :=
                mul_le_mul_of_nonneg_left hjx (show 0 ≤ (i : ℝ) by positivity)
              have hdiv : (i : ℝ) * (x / i) = x := by
                field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hi1))]
              simpa [Nat.cast_mul, hdiv] using hmul
            have hi_ne : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
            have hj_ne : j ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hj1)
            have hij_ne : i * j ≠ 0 := Nat.mul_ne_zero hi_ne hj_ne
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_divisors]
              exact ⟨dvd_mul_right i j, hij_ne⟩
            · rw [Finset.mem_Icc]
              exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hij_ne),
                (Nat.le_floor_iff hy).2 hxij⟩
          · rintro ⟨hin, hn⟩
            rw [Nat.mem_divisors] at hin
            rcases hin with ⟨⟨j, rfl⟩, hij_ne⟩
            have hi_ne : i ≠ 0 := by
              intro hi0
              exact hij_ne (by simp [hi0])
            have hj_ne : j ≠ 0 := by
              intro hj0
              exact hij_ne (by simp [hj0])
            have hi1 : 1 ≤ i := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hi_ne)
            have hj1 : 1 ≤ j := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hj_ne)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hy).1 (Finset.mem_Icc.mp hn).2
            have hix : (i : ℝ) ≤ x := by
              exact
                le_trans
                  (by
                    exact_mod_cast Nat.le_mul_of_pos_right i
                      (Nat.pos_iff_ne_zero.mpr hj_ne))
                  hxij
            have hiy : (i : ℝ) ≤ y := le_trans hix xy
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (le_div_iff₀ (Nat.cast_pos.2 hi1)).2
                  (by simpa [Nat.cast_mul, mul_comm] using hxij)
            refine ⟨Finset.mem_Icc.mpr ⟨hi1, (Nat.le_floor_iff (hy.trans xy)).2 hiy⟩, ?_⟩
            rw [Finset.mem_image]
            exact ⟨j, Finset.mem_Icc.mpr ⟨hj1,
              (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).2 hjx⟩, rfl⟩

lemma exp_sub_mul {x c : ℝ} {hc : 0 ≤ c} : c - c * log c ≤ exp x - c * x := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp [(Real.exp_pos _).le]
  suffices hmain : Real.exp (Real.log c) - c * Real.log c ≤ Real.exp x - c * x by
    rwa [Real.exp_log hc] at hmain
  have h₁ : Differentiable ℝ (fun x ↦ Real.exp x - c * x) :=
    Real.differentiable_exp.sub (differentiable_id.const_mul _)
  have h₂ : ∀ t, deriv (fun y ↦ Real.exp y - c * y) t = Real.exp t - c := by
    intro t
    change deriv (Real.exp - fun y : ℝ ↦ c * y) t = Real.exp t - c
    simpa using ((Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul c)).deriv
  cases le_total (Real.log c) x with
  | inl hx =>
      have hmono : MonotoneOn (fun y ↦ Real.exp y - c * y) (Icc (Real.log c) x) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (Real.log c) x) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonneg, ← Real.log_le_iff_le_exp hc]
            exact hy.1.le
      exact hmono (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
  | inr hx =>
      have hanti : AntitoneOn (fun y ↦ Real.exp y - c * y) (Icc x (Real.log c)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x (Real.log c)) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonpos, ← Real.le_log_iff_exp_le hc]
            exact hy.2.le
      exact hanti (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx

lemma div_bound_aux1 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ^ K ≤ n) (h2 : 0 < K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) := by
  transitivity (2 : ℝ) ^ (r : ℝ)
  · have hpow : (1 + (1 : ℝ)) ^ r = (2 : ℝ) ^ (r : ℝ) := by
      norm_num
    rw [← hpow, add_comm]
    simpa using (one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num : -2 ≤ (1 : ℝ)) r)
  · have hnonneg : 0 ≤ (2 : ℝ) ^ K := by
      positivity
    refine le_trans ?_ (Real.rpow_le_rpow hnonneg h1 ?_)
    · rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_div_cancel₀ _ h2.ne']
    · exact div_nonneg (Nat.cast_nonneg _) h2.le

lemma bernoulli_aux (x : ℝ) : x + 1 / 2 ≤ 2 ^ x := by
  have h : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have h₁ :
      1 / Real.log 2 - 1 / Real.log 2 * Real.log (1 / Real.log 2) ≤
        Real.exp (Real.log 2 * x) - 1 / Real.log 2 * (Real.log 2 * x) := by
    apply exp_sub_mul
    simp only [one_div, inv_nonneg]
    exact h.le
  rw [Real.rpow_def_of_pos zero_lt_two, ← le_sub_iff_add_le']
  rw [← mul_assoc, div_mul_cancel₀ _ h.ne', one_mul] at h₁
  apply le_trans ?_ h₁
  rw [one_div (Real.log 2), Real.log_inv]
  simp only [one_div, mul_neg, sub_neg_eq_add]
  suffices h2 : Real.log 2 / 2 - 1 ≤ Real.log (Real.log 2) by
    field_simp [h]
    linarith
  transitivity (-1 / 2 : ℝ)
  · linarith [Real.log_two_lt_d9]
  · have hlog : (-1 : ℝ) ≤ 2 * Real.log (Real.log 2) := by
      simpa [Real.log_rpow h] using
        (Real.le_log_iff_exp_le (Real.rpow_pos_of_pos h _)).2 (by
          apply Real.exp_neg_one_lt_d9.le.trans
          apply le_trans _ (Real.rpow_le_rpow (by positivity) Real.log_two_gt_d9.le zero_le_two)
          · rw [Real.rpow_two]
            norm_num)
    nlinarith

lemma div_bound_aux2 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ≤ n) (h2 : 2 ≤ K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) * K := by
  have h4 : ((r : ℝ) + 1) / K ≤ 2 ^ ((r : ℝ) / K) := by
    transitivity (r : ℝ) / K + 1 / 2
    · rw [add_div]
      simp only [one_div, add_le_add_iff_left]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 h2
    · exact bernoulli_aux _
  have hK0 : 0 < K := by
    positivity
  transitivity (2 : ℝ) ^ ((r : ℝ) / K) * K
  · rwa [← div_le_iff₀ hK0]
  · apply mul_le_mul_of_nonneg_right _ hK0.le
    exact Real.rpow_le_rpow (by positivity) h1 (div_nonneg (Nat.cast_nonneg _) hK0.le)

lemma divisor_function_exact_prime_power (r : ℕ) {p : ℕ} (h : p.Prime) :
    ArithmeticFunction.sigma 0 (p ^ r) = r + 1 := by
  simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := r) h

lemma divisor_function_exact {n : ℕ} :
  n ≠ 0 → ArithmeticFunction.sigma 0 n = n.factorization.prod (fun _ k ↦ k + 1) := by
  intro hn
  change ArithmeticFunction.sigma 0 n = n.primeFactors.prod (fun p ↦ n.factorization p + 1)
  simpa [ArithmeticFunction.sigma_zero_apply] using (Nat.card_divisors hn)

lemma divisor_function_div_pow_eq {n : ℕ} (K : ℝ) (hn : n ≠ 0) :
  (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
    n.factorization.prod (fun p k ↦ (k + 1) / ((p : ℝ) ^ ((k : ℝ) / K))) := by
  change
      (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
        n.primeFactors.prod
          (fun p ↦ (n.factorization p + 1) / ((p : ℝ) ^ ((n.factorization p : ℝ) / K)))
  rw [div_eq_mul_inv]
  have hsigma : (ArithmeticFunction.sigma 0 n : ℝ) =
      n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) := by
    exact_mod_cast (divisor_function_exact (n := n) hn)
  rw [hsigma]
  have hpow : (n : ℝ) ^ K⁻¹ =
      n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
    calc
      (n : ℝ) ^ K⁻¹ = (((n.factorization.prod fun p k => p ^ k : ℕ) : ℕ) : ℝ) ^ K⁻¹ := by
        rw [Nat.prod_factorization_pow_eq_self hn]
      _ = (n.primeFactors.prod fun p ↦ ((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹ := by
        simp [Finsupp.prod]
      _ = n.primeFactors.prod (fun p ↦ (((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹) := by
        symm
        exact Real.finsetProd_rpow _ (fun p => ((p : ℕ) : ℝ) ^ (n.factorization p))
          (by intro p hp; positivity) _
      _ = n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
        congr with p
        rw [← Real.rpow_natCast, ← Real.rpow_mul, div_eq_mul_inv]
        positivity
  rw [hpow]
  simpa [div_eq_mul_inv] using (show
    n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) *
        n.primeFactors.prod (fun p ↦ ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) =
      n.primeFactors.prod
        (fun p ↦ (n.factorization p + 1 : ℝ) * ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) by
      rw [← Finset.prod_mul_distrib])

lemma prod_of_subset_le_prod_of_one_le {ι N : Type*} [CommSemiring N] [Preorder N]
    [ZeroLEOneClass N] [PosMulMono N]
    {s t : Finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i)
    (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  exact Finset.prod_le_prod_of_subset_of_one_le h hs hf

lemma anyk_divisor_bound (n : ℕ) {K : ℝ} (hK : 2 ≤ K) :
  (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ) ^ (1 / K) * K ^ ((2 : ℝ) ^ K) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [ArithmeticFunction.sigma_apply, Nat.divisors_zero, Nat.cast_zero, pow_zero]
    rw [zero_rpow]
    · simp
    · simpa [one_div] using inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_two hK))
  rw [show (n : ℝ) ^ (1 / K) = (n : ℝ) ^ K⁻¹ by rw [one_div], mul_comm]
  rw [← div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)]
  rw [divisor_function_div_pow_eq _ hn.ne']
  let s : Finset ℕ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ K)
  have hsubset : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine (Finset.prod_le_prod_of_subset_of_le_one hsubset ?_ ?_).trans ?_
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp hp'
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpbound : (2 : ℝ) ^ K ≤ p := by
      apply le_of_not_gt
      intro hlt
      exact hp' (by simp [s, hp, hlt])
    rw [div_le_iff₀]
    · simpa using div_bound_aux1 (p : ℝ) (n.factorization p) K hpbound (by linarith)
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  refine (Finset.prod_le_prod ?_ ?_).trans ((Finset.prod_const K).trans_le ?_)
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors (hsubset hp)
    rw [div_le_iff₀]
    · simpa [mul_comm] using
        div_bound_aux2 (p : ℝ) (n.factorization p) K
          (by exact_mod_cast hpprime.two_le) hK
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  · rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have hsIcc : s ⊆ Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊ := by
      intro p hp
      have hp' : p ∈ n.primeFactors ∧ (p : ℝ) < (2 : ℝ) ^ K := by
        simpa [s] using hp
      rw [Finset.mem_Icc]
      refine ⟨Nat.pos_of_mem_primeFactors hp'.1, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hp'.2.le
    have hsle : s.card ≤ ⌊((2 : ℝ) ^ K)⌋₊ := by
      calc
        s.card ≤ (Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊).card := Finset.card_le_card hsIcc
        _ = ⌊((2 : ℝ) ^ K)⌋₊ := by
          rw [Nat.card_Icc]
          omega
    exact le_trans (by exact_mod_cast hsle) (Nat.floor_le (by positivity))

lemma log_log_mul_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
  Tendsto (fun x : ℝ ↦ log (log x) * log x / x ^ ε) atTop (𝓝 0) := by
  refine IsLittleO.tendsto_div_nhds_zero ?_
  refine ((isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (isBigO_refl _ _)).trans ?_
  refine ((isLittleO_log_rpow_atTop (half_pos hε)).pow two_pos).congr' ?_ ?_
  · filter_upwards with x using by simp [sq]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_two, ← Real.rpow_mul hx, div_mul_cancel₀ ε two_ne_zero]

lemma divisor_bound₁ {ε : ℝ} (hε1 : 0 < ε) (hε2 : ε ≤ 1) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_coe_at_top
  have hx :
      Tendsto
        (fun n : ℕ =>
          2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3)))
        atTop (𝓝 0) := by
    simpa using
      ((log_log_mul_log_div_rpow (div_pos hε1 zero_lt_three)).comp hl).const_mul 2
  have hε : 0 < Real.log 2 * ε / 2 := by
    exact half_pos (mul_pos (Real.log_pos one_lt_two) hε1)
  filter_upwards
    [tendsto_log_log_coe_at_top (eventually_ge_atTop ((Real.log 2 * (1 + ε / 2))⁻¹)),
      tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ)),
      hl (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_log_coe_at_top (eventually_ge_atTop (2 * Real.log 2 * (1 + ε / 2))),
      h (eventually_gt_atTop (0 : ℝ)),
      hx (Metric.closedBall_mem_nhds 0 hε)] with
    n hlln' hlln hln hlln'' hn hx'
  dsimp at hlln hlln' hln hlln'' hn
  set K : ℝ := log (log (n : ℝ)) / (Real.log 2 * (1 + ε / 2)) with hK
  have hpowK_pos : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos zero_lt_two _
  have hε' : 0 < Real.log 2 * (1 + ε / 2) := by
    exact mul_pos (Real.log_pos one_lt_two) (by linarith)
  have hpowK : (2 : ℝ) ^ K ≤ Real.log n ^ (1 - ε / 3) := by
    refine (Real.log_le_log_iff hpowK_pos (Real.rpow_pos_of_pos hln _)).mp ?_
    rw [Real.log_rpow zero_lt_two,
      Real.log_rpow hln, hK, mul_comm (Real.log 2), ← div_div,
      div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne', div_le_iff₀]
    · have hfactor : 1 ≤ (1 - ε / 3) * (1 + ε / 2) := by
        nlinarith [hε1, hε2]
      have hmain :
          log (log (n : ℝ)) ≤
            ((1 - ε / 3) * (1 + ε / 2)) * log (log (n : ℝ)) :=
        le_mul_of_one_le_left hlln.le hfactor
      nlinarith [hmain]
    · linarith
  have hlogK : log K ≤ 2 * log (log (Real.log n)) := by
    have haux : log ((Real.log 2 * (1 + ε / 2))⁻¹) ≤ log (log (Real.log n)) := by
      exact log_le_log_of_le (inv_pos.2 hε') hlln'
    rw [hK, div_eq_mul_inv, Real.log_mul hlln.ne' (inv_ne_zero (ne_of_gt hε')), two_mul]
    linarith
  have hK₂ : 2 ≤ K := by
    rwa [le_div_iff₀ hε', ← mul_assoc]
  have hK₀ : 0 < K := zero_lt_two.trans_le hK₂
  have hK' : 0 < K ^ ((2 : ℝ) ^ K) := Real.rpow_pos_of_pos hK₀ _
  refine (anyk_divisor_bound n hK₂).trans ?_
  refine (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hn _) hK')
    (Real.rpow_pos_of_pos hn _)).mp ?_
  rw [
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' hK'.ne', Real.log_rpow hn, Real.log_rpow hK₀,
    Real.log_rpow hn]
  have hmul :
      (2 : ℝ) ^ K * log K ≤
        Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) :=
    mul_le_mul hpowK hlogK (Real.log_nonneg (one_le_two.trans hK₂)) (Real.rpow_nonneg hln.le _)
  have hsum :
      1 / K * log (n : ℝ) + (2 : ℝ) ^ K * log K ≤
        1 / K * log (n : ℝ) +
          Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hmul (1 / K * log (n : ℝ))
  refine hsum.trans ?_
  rw [hK, one_div_div, ← div_mul_eq_mul_div]
  suffices hs :
      Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) ≤
        Real.log 2 / log (log (n : ℝ)) * (ε / 2) * log (n : ℝ) by
    linarith
  suffices hs' :
      2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / (log (n : ℝ) ^ (ε / 3))) ≤
        Real.log 2 * ε / 2 by
    rw [Real.rpow_sub hln, div_eq_mul_one_div, Real.rpow_one, div_mul_eq_mul_div,
      mul_comm _ (log (n : ℝ)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hln.le
    rw [le_div_iff₀ hlln]
    field_simp at hs' ⊢
    simpa [mul_assoc] using hs'
  have hx'' :
      |2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3))| ≤
        Real.log 2 * ε / 2 := by
    simpa [mem_closedBall_zero_iff, norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hln _)] using hx'
  exact le_of_abs_le hx''

lemma divisor_bound {ε : ℝ} (hε1 : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  rcases le_total ε 1 with hε2 | hε2
  · exact divisor_bound₁ hε1 hε2
  · filter_upwards
      [divisor_bound₁ zero_lt_one le_rfl,
        tendsto_log_log_coe_at_top (eventually_ge_atTop (0 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with n hn hn' hn''
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn'') ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hn')

lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop, (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ)^ε := by
  rcases le_total (1 : ℝ) ε with hε1 | hε1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine trivial_divisor_bound.trans ?_
    exact Real.le_rpow_self_of_one_le (by exact_mod_cast hn) hε1
  · have hx : Tendsto (fun n : ℕ => Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹) atTop (𝓝 0) := by
      simpa [mul_assoc] using
        (tendsto_log_log_coe_at_top.inv_tendsto_atTop).const_mul (Real.log 2 * 2)
    filter_upwards
      [divisor_bound zero_lt_one,
        eventually_ge_atTop (1 : ℕ),
        hx (Metric.closedBall_mem_nhds 0 hε)] with n hn hn' hx'
    have hx'' : |Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹| ≤ ε := by
      simpa [mem_closedBall_zero_iff, norm_eq_abs] using hx'
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn') ?_)
    rw [div_mul_eq_mul_div, div_eq_mul_inv]
    simpa [one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using le_of_abs_le hx''

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]

lemma helpful_floor_identity {x : ℝ} :
  ⌊x⌋ - 2 * ⌊x/2⌋ ≤ 1 := by
  have h : (⌊x⌋ - 2 * ⌊x / 2⌋ : Int) < 2 := by
    exact_mod_cast (show ((⌊x⌋ : ℝ) - 2 * ⌊x / 2⌋) < 2 by
      linarith [Int.sub_one_lt_floor (x / 2), Int.floor_le x])
  linarith

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 := by
  have h₁ : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hx₁, by simpa [one_add_one_eq_two] using hx₂⟩
  have h₂ : ⌊x / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  rw [h₁, h₂]
  simp

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ := by
  have h₄ : (2 * ⌊x / 2⌋ : Int) - 1 < ⌊x⌋ := by
    exact_mod_cast (show (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ by
      linarith [Int.floor_le (x / 2), Int.sub_one_lt_floor x])
  exact Int.sub_one_lt_iff.mp h₄

def chebyshev_error (x : ℝ) : ℝ := by
  exact
    (summatory (fun i ↦ Real.log i) 1 x - (x * log x - x)) -
      2 * (summatory (fun i ↦ Real.log i) 1 (x / 2) - (x / 2 * log (x / 2) - x / 2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x =
    Real.log 2 * x + chebyshev_error x := by
  have hhalf :
      summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Real.log n) 1 (x / 2) := by
    rw [show summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Λ n * ⌊(x / 2) / n⌋) 1 x by
          rw [summatory]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_right_comm]]
    exact von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le)
  have hx2 : (2 : ℝ) * (x / 2) = x := by
    simpa using (mul_div_cancel₀ x two_ne_zero)
  calc
    summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x
      = summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 x -
          2 * summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x := by
            rw [summatory, summatory, summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = summatory (fun n ↦ Real.log n) 1 x - 2 * summatory (fun n ↦ Real.log n) 1 (x / 2) := by
          rw [von_mangoldt_summatory hx₀.le le_rfl, hhalf]
    _ = Real.log 2 * x + chebyshev_error x := by
          rw [chebyshev_error, mul_sub, Real.log_div hx₀.ne' two_ne_zero, mul_sub, hx2]
          ring

def chebyshev_first' (x : ℝ) : ℝ := by
  exact ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Real.log n

def chebyshev_second' (x : ℝ) : ℝ := by
  exact Finset.sum (Finset.range ⌊x⌋₊) fun n => Λ n

lemma chebyshev_first_eq {x : ℝ} :
  chebyshev_first x = ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n := by
  change Chebyshev.theta x =
    ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n
  rw [Chebyshev.theta_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first'_eq {x : ℝ} :
  chebyshev_first' x = ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Λ n := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first_le_chebyshev_second : chebyshev_first ≤ chebyshev_second := by
  intro x
  exact Chebyshev.theta_le_psi x

lemma chebyshev_first'_le_chebyshev_second' : chebyshev_first' ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_first'_eq, chebyshev_second']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma chebyshev_first_nonneg : 0 ≤ chebyshev_first := by
  intro x
  exact Chebyshev.theta_nonneg x

lemma chebyshev_first'_nonneg : 0 ≤ chebyshev_first' := by
  intro x
  rw [chebyshev_first'_eq]
  exact Finset.sum_nonneg' fun _ => ArithmeticFunction.vonMangoldt_nonneg

lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x

lemma chebyshev_second'_nonneg : 0 ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_second']
  exact Finset.sum_nonneg' fun _ => ArithmeticFunction.vonMangoldt_nonneg

lemma log_nat_nonneg : ∀ (n : ℕ), 0 ≤ log (n : ℝ) := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      exact log_nonneg (by simp)

lemma chebyshev_first_monotone : Monotone chebyshev_first := by
  exact Chebyshev.theta_mono

lemma is_O_chebyshev_first_chebyshev_second :
    Asymptotics.IsBigO atTop chebyshev_first chebyshev_second := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with x
  rw [one_mul, norm_of_nonneg (chebyshev_first_nonneg x),
    norm_of_nonneg (chebyshev_second_nonneg x)]
  exact chebyshev_first_le_chebyshev_second x

lemma chebyshev_second_eq_summatory : chebyshev_second = summatory Λ 1 := by
  ext x
  change Chebyshev.psi x = summatory (⇑Λ) 1 x
  rw [Chebyshev.psi_eq_sum_Icc, summatory]
  rw [Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · simp
  · simp

@[simp] lemma chebyshev_first_zero : chebyshev_first 0 = 0 := by
  exact Chebyshev.theta_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  exact Chebyshev.psi_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_first'_zero : chebyshev_first' 0 = 0 := by
  simp [chebyshev_first']

@[simp] lemma chebyshev_second'_zero : chebyshev_second' 0 = 0 := by
  simp [chebyshev_second']

lemma chebyshev_lower_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_error x ≤ chebyshev_second x - Real.log 2 * x := by
  rw [le_sub_iff_add_le', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hfloor : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) ≤ 1 := by
    exact_mod_cast helpful_floor_identity
  simpa using mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_second x - chebyshev_second (x / 2) - Real.log 2 * x ≤ chebyshev_error x := by
  rw [sub_le_iff_le_add', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  have hs : Finset.Icc 1 ⌊x / 2⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (half_le_self hx.le))
  rw [summatory, ← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  · simp_rw [Finset.mem_sdiff, Finset.mem_Icc, and_imp, not_and, not_le, Nat.le_floor_iff hx.le,
      Nat.floor_lt (div_nonneg hx.le zero_le_two), Nat.succ_le_iff]
    intro i hi₁ hi₂ hi₃
    replace hi₃ := hi₃ hi₁
    have hge1 : 1 ≤ x / i := by
      refine (one_le_div₀ ?_).2 hi₂
      exact_mod_cast hi₁
    have hlt2 : x / i < 2 := by
      have hi_pos : (0 : ℝ) < i := by
        exact_mod_cast hi₁
      have hmul : x < 2 * i := by
        linarith
      exact (div_lt_iff₀ hi_pos).2 (by simpa [mul_comm] using hmul)
    have hEq : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) = 1 := by
      exact_mod_cast (helpful_floor_identity2 (x := x / i) hge1 hlt2)
    rw [hEq, mul_one]
  · intro i _ _
    have hcoeff' : (2 : ℝ) * ↑⌊x / ↑i / 2⌋ ≤ ↑⌊x / ↑i⌋ := by
      exact_mod_cast (helpful_floor_identity3 (x := x / i))
    have hcoeff : 0 ≤ (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) := by
      linarith
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hcoeff)

lemma chebyshev_error_O :
  Asymptotics.IsBigO atTop chebyshev_error log := by
  have h23 : (2 : ℝ) < 3 := by norm_num
  refine (summatory_log h23).isBigO.sub ?_
  refine (((summatory_log h23).isBigO.comp_tendsto
    (tendsto_id.atTop_div_const zero_lt_two)).const_mul_left 2).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxhalf : 1 ≤ x / 2 := by linarith
  have hxlog : log (x / 2) ≤ log x := log_le_log_of_le (by linarith) (by linarith)
  simpa [Function.comp_apply, one_mul, norm_of_nonneg (log_nonneg hxhalf),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))] using hxlog

lemma chebyshev_lower_explicit {c : ℝ} (hc : c < Real.log 2) :
  ∀ᶠ x : ℝ in atTop, c * x ≤ chebyshev_second x := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h₁] with x hx₁ hx₂
  have hx₂' : ‖chebyshev_error x‖ ≤ (Real.log 2 - c) * x := by
    simpa [id, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx₁)] using hx₂
  have hmain := (neg_le_of_abs_le hx₂').trans (chebyshev_lower_aux (zero_lt_one.trans_le hx₁))
  linarith

lemma chebyshev_lower :
  Asymptotics.IsBigO atTop id chebyshev_second := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(Real.log 2 / 2)⁻¹, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    chebyshev_lower_explicit (half_lt_self (Real.log_pos one_lt_two))] with x hx₁ hx₂
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (half_pos (Real.log_pos one_lt_two))]
  simp [id, Real.norm_eq_abs, abs_of_nonneg hx₁, norm_of_nonneg (chebyshev_second_nonneg x)]
  simpa [mul_comm] using hx₂

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  chebyshev_second n ≤ n * Real.log n := by
  rw [chebyshev_second_eq_summatory, summatory_nat, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log n) ?_).trans ?_
  · intro i hi
    apply von_mangoldt_upper.trans
    simp only [Finset.mem_Icc] at hi
    exact log_le_log_of_le (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · simp

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  chebyshev_second x ≤ x * log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← chebyshev_second_eq_summatory]
  refine (chebyshev_trivial_upper_nat _).trans ?_
  refine mul_le_mul (Nat.floor_le hx₀.le)
    ?_ (log_nonneg (by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff x).2 hx
      exact this)) hx₀.le
  · exact log_le_log_of_le (by
      have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Nat.floor_pos.mpr hx)
      exact hfloorpos) (Nat.floor_le hx₀.le)

lemma chebyshev_upper_inductive {c : ℝ} (hc : Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, chebyshev_second x ≤ 2 * c * x + C * log C := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp h₁
  let C : ℝ := max 1 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : (n : ℝ) ≤ C
  · rw [chebyshev_second_eq_summatory]
    refine
      (summatory_monotone_of_nonneg _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) hn).trans
        ?_
    rw [← chebyshev_second_eq_summatory]
    refine (chebyshev_trivial_upper (le_max_left _ _)).trans ?_
    refine le_add_of_nonneg_left (mul_nonneg ?_ (Nat.cast_nonneg _))
    exact mul_nonneg zero_le_two ((Real.log_nonneg one_le_two).trans hc.le)
  · have hn : C < n := lt_of_not_ge hn
    have hn' : 0 < n := by
      refine Nat.succ_le_iff.mp ?_
      exact Nat.one_le_cast.mp ((le_max_left _ _).trans hn.le)
    have h₁ := chebyshev_upper_aux (Nat.cast_pos.mpr hn')
    rw [sub_sub, sub_le_iff_le_add] at h₁
    apply h₁.trans
    rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← Nat.cast_two,
      Nat.floor_div_eq_div, Nat.cast_two, ← add_assoc]
    have h₃ := hC₀ (n : ℝ) ((le_max_right _ _).trans hn.le)
    rw [Real.norm_eq_abs] at h₃
    replace h₃ := le_of_abs_le h₃
    have h₂ := ih (n / 2) (Nat.div_lt_self hn' one_lt_two)
    rw [← chebyshev_second_eq_summatory]
    have hsum :
        chebyshev_error (n : ℝ) + chebyshev_second (n / 2 : ℕ) + Real.log 2 * (n : ℝ) ≤
          (c - Real.log 2) * ‖(n : ℝ)‖ + (2 * c * (n / 2 : ℕ) + C * log C) +
            Real.log 2 * (n : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right (add_le_add h₃ h₂) (Real.log 2 * (n : ℝ))
    refine hsum.trans ?_
    have hc0 : 0 ≤ c := (Real.log_nonneg one_le_two).trans hc.le
    have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧
    Asymptotics.IsBigOWith 1 atTop chebyshev_second (fun x ↦ c * x + C * log C) := by
  have hc' : Real.log 2 < c / 2 := by
    nlinarith
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc'
  refine ⟨C, hC₁, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨0, ?_⟩
  intro x hx
  rw [Real.norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory,
    summatory_eq_floor, ← chebyshev_second_eq_summatory, one_mul]
  refine (hC ⌊x⌋₊).trans (le_trans ?_ (le_abs_self _))
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by nlinarith
  have hmul : c * (⌊x⌋₊ : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left hfloor hc0
  have hEq : 2 * (c / 2) * (⌊x⌋₊ : ℝ) = c * (⌊x⌋₊ : ℝ) := by ring
  simpa [hEq, add_assoc, add_left_comm, add_comm] using add_le_add_right hmul (C * log C)

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * Real.log 2 < c) :
  Asymptotics.IsBigOWith c atTop chebyshev_second id := by
  let c' : ℝ := Real.log 2 + c / 2
  have hc'₁ : c' < c := by
    dsimp [c']
    nlinarith
  have hc'₂ : 2 * Real.log 2 < c' := by
    dsimp [c']
    nlinarith
  have hc'₀ : 0 ≤ c' := by
    dsimp [c']
    nlinarith [Real.log_nonneg one_le_two, hc]
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂
  have hconst : (fun _ : ℝ ↦ C * log C) =o[atTop] id := by
    exact (isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop)
  have hmain : Asymptotics.IsBigOWith c atTop (fun x ↦ c' * x + C * log C) id := by
    have hc'₁' : ‖c'‖ < c := by
      simpa [Real.norm_of_nonneg hc'₀] using hc'₁
    simpa [c'] using
      (Asymptotics.isBigOWith_const_mul_self c' id atTop).add_isLittleO hconst hc'₁'
  exact (hC.trans hmain zero_le_one).congr_const (one_mul c)

lemma chebyshev_upper : Asymptotics.IsBigO atTop chebyshev_second id := by
  exact (chebyshev_upper_explicit (lt_add_one _)).isBigO

lemma chebyshev_first_upper : Asymptotics.IsBigO atTop chebyshev_first id := by
  exact is_O_chebyshev_first_chebyshev_second.trans chebyshev_upper

lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : Summable f) :
  Asymptotics.IsBigO atTop (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
    (fun _ ↦ (1 : ℝ)) := by
  simpa using hf.hasSum.tendsto_sum_nat.isBigO_one ℝ

lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) := by
  set f : ℝ → ℝ := log
  set g : ℝ → ℝ := fun x ↦ x^(1 / 2 : ℝ) - x^(-1 / 2 : ℝ)
  set f' : ℝ → ℝ := Inv.inv
  set g' : ℝ → ℝ := fun x ↦ 1 / 2 * x^(-3 / 2 : ℝ) + 1 / 2 * x^(-1 / 2 : ℝ)
  suffices h : ∀ y ∈ Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · have hpow : (2⁻¹ : ℝ) - 1 = -1 / 2 := by norm_num
      simpa [Set.Ici, id, one_mul, hpow] using
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (1 / 2 : ℝ)) (Or.inl hy'.ne'))
    · have hpow : (-1 / 2 : ℝ) - 1 = -3 / 2 := by norm_num
      have hpow' : (-2⁻¹ : ℝ) - 1 = -3 / 2 := by norm_num
      have hcoef : (-1 / 2 : ℝ) = -2⁻¹ := by norm_num
      have hderiv :=
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (-1 / 2 : ℝ)) (Or.inl hy'.ne'))
      simpa [Set.Ici, id, one_mul, hpow, hpow', hcoef, neg_mul, mul_assoc] using hderiv
  have hmain :=
    image_le_of_deriv_right_le_deriv_boundary
      (f := f) (f' := f') (a := 1) (b := x)
      (continuousOn_log.mono fun y hy ↦ (zero_lt_one.trans_le hy.1).ne')
      f_deriv
      (by simp [f])
      ((continuousOn_id.rpow_const (by simp)).sub
        (continuousOn_id.rpow_const fun y hy ↦ Or.inl (zero_lt_one.trans_le hy.1).ne'))
      g_deriv
      (by
        intro y hy
        dsimp [f', g']
        rw [← mul_add, mul_comm, ← div_eq_mul_one_div,
          le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), ← sub_nonneg, ← Real.rpow_neg_one]
        convert sq_nonneg (y^(-1 / 4 : ℝ) - y^(-3 / 4 : ℝ)) using 1
        have hy' : 0 < y := zero_lt_one.trans_le hy.1
        rw [sub_sq, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_two,
          ← Real.rpow_mul hy'.le, mul_assoc, ← Real.rpow_add hy', ← Real.rpow_mul hy'.le]
        norm_num
        ring)
  intro y hy
  exact hmain hy

lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx' : x ≠ 0 := hx0.ne'
  have hden : 0 < x * (x - 1) := by nlinarith
  have hrewrite : (x⁻¹)^2 / (1 - x⁻¹) = 1 / (x * (x - 1)) := by
    field_simp [hx']
  rw [hrewrite, ← div_eq_mul_one_div]
  rw [div_le_iff₀ hden]
  calc
    log x ≤ x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ) := log_le_thing hx.le
    _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by
      have hx1 : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
        calc
          x ^ (-3 / 2 : ℝ) * x = x ^ (-3 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-3 / 2 : ℝ) 1]; norm_num
      have hx2 : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
        calc
          x ^ (-1 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-1 / 2 : ℝ) 1]; norm_num
      calc
        x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ)
            = x ^ (-1 / 2 : ℝ) * x - x ^ (-1 / 2 : ℝ) := by rw [hx2]
        _ = x ^ (-1 / 2 : ℝ) * (x - 1) := by ring
        _ = (x ^ (-3 / 2 : ℝ) * x) * (x - 1) := by rw [hx1]
        _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by ring

@[to_additive]
lemma prod_prime_powers' {M : Type*} [CommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.prod_sigma', eq_comm]
  refine Finset.prod_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

@[to_additive]
lemma prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [prod_prime_powers']
  refine Finset.prod_congr rfl ?_
  intro p hp
  refine Finset.prod_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

lemma sum_prime_powers' {M : Type*} [AddCommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.sum_sigma', eq_comm]
  refine Finset.sum_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

lemma sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [sum_prime_powers']
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

@[to_additive]
lemma exact_prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine prod_prime_powers.trans (Finset.prod_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.prod_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

lemma exact_sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine sum_prime_powers.trans (Finset.sum_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

theorem geom_sum_Ico'_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (_hmn : m ≤ n) :
  ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx₀ hx₁

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n ∈ Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, sum_prime_powers, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  simp only [Finset.mem_Icc, Nat.cast_pow, and_imp]
  intro p hp₁ hp₂
  split_ifs with hp
  · have hp₃ : (p : ℝ) ≤ x := (Nat.le_floor_iff' hp.ne_zero).1 hp₂
    have hInsert :
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, if_pos]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow
          ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
    rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
    refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hp.one_lt))
    rw [show Finset.Icc 2 ⌊x⌋₊ = Finset.Ico 2 (⌊x⌋₊ + 1) by
      ext i
      simp]
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le ?_ ?_ ?_) ?_
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    · exact Nat.succ_le_succ (hp₁.trans hp₂)
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rw [abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n := by
    intro x hx
    rw [← summatory, ← von_mangoldt_summatory hx le_rfl, mul_sum, summatory,
      ← Finset.sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [mul_div_left_comm x, abs_sub_comm, ← mul_sub, abs_mul,
      ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg, Int.self_sub_floor, Int.fract_nonneg]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  refine Asymptotics.IsBigO.trans ?_ chebyshev_upper
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg))]
  exact hbound x hx

lemma is_O_von_mangoldt_div_self :
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
        (fun x ↦ x) by
    refine ((isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop).mul h).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← mul_sub, inv_mul_cancel_left₀ hx.ne']
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [inv_mul_cancel₀ hx.ne']
  refine summatory_log_sub.symm.triangle ?_
  have h₁ := (summatory_log (lt_add_one 2)).isBigO
  refine ((h₁.trans isLittleO_log_id_atTop.isBigO).sub (isBigO_refl _ _)).congr_left ?_
  intro x
  dsimp [summatory]
  ring

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  rw [prime_summatory, prime_summatory]
  refine (Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left one_le_two))
    (fun y hy => ?_) (fun _ _ => rfl)).symm
  rcases Finset.mem_sdiff.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_filter.mp hy1 with ⟨hyIcc, hyPrime⟩
  exact False.elim <| hy2 <|
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hyPrime.two_le, (Finset.mem_Icc.mp hyIcc).2⟩, hyPrime⟩

lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  exact is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self

lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have :
      (Finset.range (x + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 x := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2.pos, Nat.lt_succ_iff.mp hn.1⟩
  exact (Finset.card_le_card this).trans (by simp)

lemma chebyshev_first_eq_prime_summatory :
  chebyshev_first = prime_summatory (fun n ↦ Real.log n) 1 := by
  ext x
  change Chebyshev.theta x = prime_summatory (fun n ↦ Real.log n) 1 x
  rw [Chebyshev.theta_eq_sum_Icc, prime_summatory]
  congr 1

@[simp] lemma prime_counting'_zero : π' 0 = 0 := by
  rfl

@[simp] lemma prime_counting'_one : π' 1 = 0 := by
  rfl

@[simp] lemma prime_counting'_two : π' 2 = 0 := by
  rfl

lemma chebyshev_first_trivial_bound (x : ℝ) :
  chebyshev_first x ≤ π ⌊x⌋₊ * log x := by
  by_cases hx : x ≤ 0
  · rw [show chebyshev_first = Chebyshev.theta by rfl]
    rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_le_of_lt hx (by norm_num : (0 : ℝ) < 2))]
    simp [Nat.floor_eq_zero.2 (hx.trans_lt zero_lt_one)]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [chebyshev_first_eq_prime_summatory, prime_summatory, prime_counting_eq_card_primes,
      ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ (log x) ?_
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    have hyle : (y : ℝ) ≤ x := by
      exact le_trans (by exact_mod_cast hy.1.2) (Nat.floor_le hx0.le)
    exact log_le_log_of_le (show 0 < (y : ℝ) by exact_mod_cast hy.2.pos) hyle

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (fun _ ↦ 1) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (fun _ ↦ (1 : ℝ)) 1 x := by
  rw [prime_counting_eq_prime_summatory]
  simp [prime_summatory]

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - chebyshev_first x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
  have hmul :
      (fun n : ℕ ↦ ite (Nat.Prime n) (Real.log n : ℝ) 0) =
        fun n : ℕ ↦ ite (Nat.Prime n) (1 : ℝ) 0 * Real.log n := by
    funext n
    rw [boole_mul]
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory']
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', hmul,
    partial_summation_cont' (fun n ↦ ite (Nat.Prime n) (1 : ℝ) 0) Real.log (fun y ↦ y⁻¹)
      one_ne_zero (fun y hy ↦ hasDerivAt_log <| by
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        intro hzero
        rw [hzero] at hy'
        norm_num at hy')
      (by
        refine ContinuousOn.inv₀ continuousOn_id ?_
        intro y hy hzero
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        rw [hzero] at hy'
        norm_num at hy') x, Nat.cast_one]

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  Asymptotics.IsBigO atTop
    (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x - chebyshev_first x) id := by
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  change ‖∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Icc 1 x, (1 : ℝ) = x - 1 := by
      simp [hx.le]
    rw [hconst]
    linarith

lemma is_O_prime_counting_div_log :
  Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x) := by
  have h :
      Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) id := by
    refine (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left ?_
    intro x
    ring
  refine (Asymptotics.IsBigO.mul h (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_assoc, mul_inv_cancel₀ (Real.log_pos hx).ne', mul_one]
  · filter_upwards with x
    simp [div_eq_mul_inv]

lemma prime_counting_le_const_mul_div_log :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, (π (⌊x⌋₊) : ℝ) ≤ c * ‖x / Real.log x‖ := by
  obtain ⟨c₀, hc₀, hc₀'⟩ := is_O_prime_counting_div_log.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀'
  obtain ⟨c₁, hc₁⟩ := hc₀'
  refine ⟨max c₀ c₁, lt_max_of_lt_left hc₀, ?_⟩
  intro x
  have hmax : 0 < max c₀ c₁ := lt_max_of_lt_left hc₀
  have hc₁' :
      ∀ y : ℝ, c₁ ≤ y → ‖(π ⌊y⌋₊ : ℝ)‖ ≤ c₀ * ‖y / Real.log y‖ := by
    intro y hy
    exact hc₁ y hy
  simp only [Real.norm_natCast] at hc₁'
  rcases le_total c₁ x with hx₀ | hx₀
  · exact (hc₁' x hx₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rcases lt_trichotomy x 1 with hx₁ | rfl | hx₁
  · rw [Nat.floor_eq_zero.2 hx₁, Nat.primeCounting_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_of_le_left hc₀.le) (norm_nonneg _)
  · simp
  refine (Nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊)).trans ?_
  refine (((Nat.floor_le (zero_le_one.trans hx₁.le)).trans hx₀).trans (le_max_right c₀ c₁)).trans ?_
  rw [le_mul_iff_one_le_right hmax, norm_div, Real.norm_of_nonneg (Real.log_nonneg hx₁.le),
    Real.norm_of_nonneg (zero_le_one.trans hx₁.le), one_le_div (Real.log_pos hx₁)]
  exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hx₁)).trans (by simp)

lemma chebyshev_second_sub_chebyshev_first_eq {x : ℝ} (hx : 2 ≤ x) :
  chebyshev_second x - chebyshev_first x ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
  rw [show chebyshev_second = Chebyshev.psi by rfl, show chebyshev_first = Chebyshev.theta by rfl]
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx, add_tsub_cancel_left]
  refine (Finset.sum_le_card_nsmul _ _ ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * log x) ?_).trans ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hpow : x ^ (1 / k : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hx)
      refine one_div_le_one_div_of_le zero_lt_two hk'
    apply (chebyshev_first_monotone hpow).trans
    refine (chebyshev_first_le_chebyshev_second _).trans ?_
    refine (chebyshev_trivial_upper (one_le_rpow (one_le_two.trans hx) (by positivity))).trans ?_
    rw [Real.log_rpow (zero_lt_two.trans_le hx)]
    ring_nf
    exact le_rfl
  · have hcard :
        ((Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) ≤ Real.log x / Real.log 2 := by
      let m : ℕ := ⌊Real.log x / Real.log 2⌋₊
      refine le_trans ?_ (Nat.floor_le ?_)
      · have hsub : Finset.Icc 2 m ⊆ Finset.Icc 1 m := by
          intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          exact ⟨one_le_two.trans hn.1, hn.2⟩
        have hcard' : ((Finset.Icc 2 m).card : ℝ) ≤ ((Finset.Icc 1 m).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        simp [m, Nat.card_Icc] at hcard' ⊢
      · exact div_nonneg (Real.log_nonneg (one_le_two.trans hx)) (Real.log_pos one_lt_two).le
    rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_right hcard ?_).trans ?_
    · exact
        mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.log_nonneg (one_le_two.trans hx))
    have hconst : (1 / 2 : ℝ) / Real.log 2 ≤ 1 := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9]
    have hfac :
        (Real.log x / Real.log 2) * ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * Real.log x) =
          ((1 / 2 : ℝ) / Real.log 2) * (x ^ (1 / 2 : ℝ) * (Real.log x)^2) := by
      field_simp [(Real.log_pos one_lt_two).ne']
    rw [hfac]
    refine (mul_le_mul_of_nonneg_right hconst ?_).trans ?_
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · simp

lemma chebyshev_first_two : chebyshev_first 2 = Real.log 2 := by
  rw [chebyshev_first_eq_prime_summatory, prime_summatory]
  norm_num
  rw [show (Finset.Icc 1 2).filter Nat.Prime = ({2} : Finset ℕ) by decide]
  simp

lemma chebyshev_first_trivial_lower : ∀ x, 2 ≤ x → 0.5 ≤ chebyshev_first x := by
  intro x hx
  have hmono : chebyshev_first 2 ≤ chebyshev_first x := chebyshev_first_monotone hx
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  rw [chebyshev_first_two] at hmono
  linarith

lemma chebyshev_first_lower : Asymptotics.IsBigO atTop id chebyshev_first := by
  have hdiffO :
      Asymptotics.IsBigO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x)
        (fun x ↦ x ^ (1 / 2 : ℝ) * (log x)^2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hnonneg₁ : 0 ≤ chebyshev_second x - chebyshev_first x := by
      exact sub_nonneg_of_le (chebyshev_first_le_chebyshev_second x)
    have hnonneg₂ : 0 ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
      exact mul_nonneg (by positivity) (sq_nonneg _)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg₁, Real.norm_eq_abs, abs_of_nonneg hnonneg₂]
    exact chebyshev_second_sub_chebyshev_first_eq hx
  have hdiff :
      Asymptotics.IsLittleO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x) id := by
    refine hdiffO.trans_isLittleO ?_
    have ht : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)^2) (fun x ↦ x ^ (1 / 2 : ℝ)) := by
      refine ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).pow two_pos).congr' ?_ ?_
      · filter_upwards with x using by simp [sq]
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_two, ← Real.rpow_mul hx]
        congr 1
        ring
    refine ((isBigO_refl (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop).mul_isLittleO ht).congr' ?_ ?_
    · filter_upwards with x using by rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx, add_halves, Real.rpow_one]
      rfl
  have haux := hdiff.symm.trans_isBigO chebyshev_lower
  exact (chebyshev_lower.trans haux.right_isBigO_add).congr_right (fun x ↦ by ring)

lemma chebyshev_first_all :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * ‖x‖ ≤ ‖chebyshev_first x‖ := by
  obtain ⟨c₀, hc₀, h⟩ := chebyshev_first_lower.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.1 h.bound
  let c : ℝ := max c₀ (2 * X)
  have hc : 0 < c := lt_max_of_lt_left hc₀
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  intro x hx
  rw [inv_mul_le_iff₀ hc]
  rcases le_total X x with hx' | hx'
  · exact (hX x hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_of_nonneg (zero_le_two.trans hx)]
  have hhalf : (1 / 2 : ℝ) ≤ chebyshev_first x := by
    have hlow := chebyshev_first_trivial_lower x hx
    norm_num at hlow ⊢
    exact hlow
  refine hx'.trans ?_
  rw [show X = (2 * X) * (1 / 2 : ℝ) by ring]
  exact
    (mul_le_mul (le_max_right c₀ (2 * X)) hhalf (by norm_num) hc.le)


lemma is_O_div_log_prime_counting :
  Asymptotics.IsBigO atTop (fun x ↦ x / log x) (fun x ↦ (π ⌊x⌋₊ : ℝ)) := by
  have hθ :
      Asymptotics.IsBigO atTop chebyshev_first
        (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [one_mul, Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_eq_abs]
    exact (chebyshev_first_trivial_bound x).trans (le_abs_self _)
  refine ((chebyshev_first_lower.trans hθ).mul
    (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards with x using by simp [id, div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_inv_cancel_right₀ (Real.log_pos hx).ne']

def prime_log_div_sum_error (x : ℝ) : ℝ := by
  exact prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring

lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := by
  exact log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (pow_ne_zero 2 (Real.log_pos hx').ne')

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    have hrewrite : (y * log y ^ 2)⁻¹ = -((-y⁻¹) / (log y)^2) := by
      rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv]
    rw [hrewrite]
    exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hy1).ne').neg
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact my_func_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]

lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
  Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) := by
  suffices h :
      Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 ((log a)⁻¹ - 0)) by
    simpa using h
  have hEq :
      ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹ := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_inv_self_mul_log_sq ha (ha.trans_le hi)]
  rw [tendsto_congr' hEq]
  exact (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hb)).const_sub _

lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log a)⁻¹ a (fun x ↦ ?_) tendsto_id ?_
  · by_cases hx : a ≤ x
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact my_func_continuous_on.mono fun y hy ↦ ha.trans_le hy.1
    · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hx)]
  · refine (integral_Ioi_my_func_tendsto_aux ha tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop a] with x hx
    have hax : a ≤ x := le_of_lt hx
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using hy
    rw [Real.norm_of_nonneg]
    exact inv_nonneg.2 (mul_nonneg (le_trans (by linarith) hy'.1) (sq_nonneg _))

lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul (Real.continuousOn_log.mono ?_)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (Real.log_pos hx').ne'

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact my_func2_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]

lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) := by
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ ?_
    intro y hy
    have hy2 : 2 ≤ y := hy.1
    have hy0 : 0 < y := by linarith
    exact mul_ne_zero hy0.ne' (pow_ne_zero _ (Real.log_pos (by linarith)).ne')
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_set_ae Ico_ae_eq_Icc).2 ?_
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul]
    refine (partial_summation_integrable _ (ContinuousOn.integrableOn_Icc hlog')).sub ?_
    exact (hlog.mul hlog').integrableOn_Icc
  · have hbound :
        ∀ᵐ x : ℝ ∂volume.restrict (Ici k),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ ‖c * (x * log x ^ 2)⁻¹‖ := by
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ hx) (norm_nonneg _)).trans ?_
      have hcnorm : c * |(1 : ℝ)| ≤ ‖c‖ := by
        simp [Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Ici (2 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_inv₀.mono hne).neg
    · exact (Real.continuousOn_log.mono hne).pow _
    · intro y hy
      exact pow_ne_zero _ (Real.log_pos (one_lt_two.trans_le hy)).ne'
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  rw [sub_eq_iff_eq_add]
  convert hps using 1
  · rw [prime_summatory_eq_summatory]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hpy : y.Prime
    · have hy1 : (1 : ℝ) < y := by
        rw [Nat.one_lt_cast, ← Nat.succ_le_iff]
        exact (Finset.mem_Icc.mp hy).1
      simp [a, f, hpy]
      field_simp [(show (y : ℝ) ≠ 0 by positivity), (Real.log_pos hy1).ne']
    · simp [a, hpy]
  · rw [← prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq]
    rw [prime_reciprocal_integral]
    simp only [div_eq_mul_inv, Pi.add_apply, add_mul, f', f, neg_mul, mul_neg, integral_neg,
      sub_neg_eq_add, ← mul_inv]
    have h₁ :
        Integrable (fun a ↦ (a * Real.log a)⁻¹)
          (volume.restrict (Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (my_func2_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
        (setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          (integrable_on_prime_log_div_sum_error.mono_set
            (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self))
          (integrable_on_prime_log_div_sum_error.mono_set <| by
            intro y hy
            exact hx.trans hy.le) :
          ∫ t in Set.Ioc (2 : ℝ) x ∪ Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
            (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
              ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
    rw [mul_inv_cancel₀ (Real.log_pos (one_lt_two.trans_le hx)).ne', hEq,
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf

lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Ici y),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ c * (x * log x ^ 2)⁻¹ := by
      intro y hy
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans ?_
      rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg]
      exact zero_le_two.trans (hk₂.trans (hy.trans hx))
    have hI :
        Asymptotics.IsBigO atTop
          (fun y ↦ ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_my_func_Ioi hy]
    exact hI.trans_eventuallyEq hEq |>.trans (Asymptotics.isBigO_const_mul_self c _ _)

def meissel_mertens : ℝ := by
  exact 1 - log (Real.log 2) + prime_reciprocal_integral

lemma prime_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (fun x ↦ (log x)⁻¹) := by
  refine prime_reciprocal_error.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_summatory_one_eq_prime_summatory_two, meissel_mertens, ← prime_reciprocal_eq hx]

lemma is_o_log_inv_one {c : ℝ} (hc : c ≠ 0) :
    Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)⁻¹) (fun _ : ℝ ↦ (c : ℝ)) := by
  exact (Asymptotics.IsLittleO.inv_rev (is_o_one_log c⁻¹) (by simp [hc])).congr_right (by simp)

lemma is_o_const_log_log (c : ℝ) :
    Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ (c : ℝ)) (fun x : ℝ ↦ log (log x)) := by
  exact is_o_const_of_tendsto_at_top _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) _

lemma prime_reciprocal_upper :
  Asymptotics.IsBigO atTop (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x)
    (fun x ↦ log (log x)) := by
  refine ((prime_reciprocal.trans
      ((is_o_log_inv_one one_ne_zero).trans (is_o_const_log_log _)).isBigO).add
      ((isBigO_refl _ _).add_isLittleO (is_o_const_log_log meissel_mertens))).congr_left ?_
  intro x
  ring

lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ := by
  field_simp [hx₀, hx₁]
  ring

lemma sum_thing_has_sum (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) ((k + 1 : ℝ)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => inv_nonneg.2 (by positivity))]
  have htel :
      ∀ i : ℕ,
        ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ =
          (↑(i + (k + 1)) : ℝ)⁻¹ - (↑(i + 1 + (k + 1)) : ℝ)⁻¹ := by
    intro i
    simp only [Nat.cast_add_one, Nat.cast_add, add_right_comm (i : ℝ) 1, ← add_assoc]
    convert mul_add_one_inv (i + k + 1) ?_ ?_ using 2
    · norm_num [add_assoc]
    · exact_mod_cast Nat.succ_ne_zero (i + k)
    · exact_mod_cast Nat.succ_ne_zero (i + k + 1)
  simp only [htel, Finset.sum_range_sub', zero_add, Nat.cast_add_one]
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat (k + 1))).const_sub
      ((k + 1 : ℝ)⁻¹)

lemma sum_thing'_has_sum : HasSum (fun n : ℕ ↦ ((n - 1) * n : ℝ)⁻¹) 1 := by
  refine (hasSum_nat_add_iff' 2).1 ?_
  have hzero :
      (∑ i ∈ Finset.range 2, (((i : ℝ) - 1) * (i : ℝ))⁻¹) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hzero]
  norm_num
  have hbase :
      HasSum (fun n : ℕ ↦ ((↑n + ↑0 + 1) * (↑n + ↑0 + 2) : ℝ)⁻¹) 1 := by
    simpa using sum_thing_has_sum 0
  refine HasSum.congr_fun hbase ?_
  intro n
  have hn2 : (↑n + 2 : ℝ) ≠ 0 := by positivity
  have hn1 : (↑n + 2 - 1 : ℝ) ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  field_simp [hn1, hn2, Nat.cast_add]
  ring

lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum (fun n : ℕ ↦ ((n + k) * (n + k + 1) : ℝ)⁻¹) ((k : ℝ)⁻¹) := by
  convert sum_thing_has_sum (k - 1) using 1
  · ext n
    rw [add_assoc, add_assoc, Nat.cast_sub hk, Nat.cast_one, sub_add_cancel, add_sub, sub_add]
    norm_num [add_assoc]
  · simp [hk]

lemma sum_thing''_indicator_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum ({n | k < n}.indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹)) ((k : ℝ)⁻¹) := by
  have hrange : Set.range (fun i : ℕ => i + (k + 1)) = {n | k < n} := by
    ext n
    constructor
    · rintro ⟨i, rfl⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) i)
    · intro hn
      refine ⟨n - (k + 1), Nat.sub_add_cancel ?_⟩
      exact Nat.succ_le_of_lt hn
  rw [← hrange]
  have hinj : Function.Injective (fun i : ℕ => i + (k + 1)) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (Function.Injective.hasSum_iff hinj ?_).1
  · convert sum_thing'''_has_sum hk using 1
    ext n
    simp [Set.indicator_of_mem, ← add_assoc]
  · intro n hn
    simp [Set.indicator_of_notMem, hn]

lemma prime_sum_thing_summable' (s : Set ℕ) :
  Summable (s.indicator ((setOf Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) := by
  exact (sum_thing'_has_sum.summable.indicator _).indicator _

lemma indicator_mono {α β : Type*} [Zero β] [Preorder β] {s t : Set α} {f : α → β}
    (h : s ⊆ t) (hf : ∀ x, x ∉ s → x ∈ t → 0 ≤ f x) :
  indicator s f ≤ indicator t f := by
  intro x
  by_cases hs : x ∈ s
  · simp [Set.indicator_of_mem, hs, h hs]
  · by_cases ht : x ∈ t
    · simp [Set.indicator_of_notMem, hs, ht, hf x hs ht]
    · simp [Set.indicator_of_notMem, hs, ht]

lemma prime_sum_thing {k : ℕ} (hk : 1 ≤ k) :
  tsum
      ({n | k < n}.indicator ((setOf Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) ≤
    ((k : ℝ)⁻¹) := by
  refine hasSum_le ?_ (prime_sum_thing_summable' _).hasSum (sum_thing''_indicator_has_sum hk)
  intro n
  by_cases hkn : k < n
  · by_cases hpn : Nat.Prime n
    · simp [Set.indicator_of_mem, hkn, hpn]
    · have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (lt_of_le_of_lt hk hkn)
      have hnonneg : 0 ≤ (n : ℝ)⁻¹ * ((n : ℝ) - 1)⁻¹ := by
        apply mul_nonneg
        · positivity
        · exact inv_nonneg.2 (sub_nonneg.mpr hn1.le)
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hkn, hpn, hnonneg]
  · simp [Set.indicator_of_notMem, hkn]

lemma my_mul_thing' : ∀ {n : ℕ}, (0 : ℝ) ≤ (((n - 1) * n : ℝ)⁻¹) := by
  intro n
  exact inv_nonneg.2 my_mul_thing

lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ range (⌊x⌋₊ + 1), f i - c)
    (fun x ↦ x⁻¹) := by
  have hf'' : Summable f := (sum_thing'_has_sum.summable).of_nonneg_of_le hf' hf
  refine ⟨tsum f, (Asymptotics.IsBigO.of_bound 2 ?_).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ ⌊x⌋₊ := by
    rwa [Nat.le_floor_iff' one_ne_zero, Nat.cast_one]
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa
  rw [← Summable.sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg fun i ↦ hf' (i + _)), norm_of_nonneg (zero_le_one.trans hx)]
  transitivity (⌊x⌋₊ : ℝ)⁻¹
  · refine hasSum_le (fun n ↦ ?_) ((summable_nat_add_iff _).2 hf'').hasSum
      (sum_thing'''_has_sum hx')
    have hsub : (↑n : ℝ) + (↑⌊x⌋₊ + 1) - 1 = ↑n + ↑⌊x⌋₊ := by ring
    simpa [Nat.cast_add, Nat.cast_add_one, add_assoc, add_left_comm, add_comm, mul_comm,
      mul_left_comm, mul_assoc, hsub] using hf (n + (⌊x⌋₊ + 1))
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := zero_lt_one.trans_le hx''
  field_simp [hxpos.ne', hfloorpos.ne']
  nlinarith [Nat.lt_floor_add_one x]

lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Icc 1 ⌊x⌋₊, f i - c)
    (fun x ↦ x⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf'
  refine ⟨c, hc.congr_left ?_⟩
  intro x
  have hIco : Finset.Ico 0 (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    simpa using (Finset.Ico_succ_right_eq_Icc 0 ⌊x⌋₊)
  rw [Finset.range_eq_Ico, hIco, Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · have h0 : f 0 = 0 := ((hf' 0).antisymm (by simpa using hf 0)).symm
    simp [h0]
  · simp

lemma intermediate_bound :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ x⁻¹) := by
  simp only [prime_summatory, Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · rfl
    · exact my_mul_thing'
  · split_ifs with h
    · exact my_mul_thing'
    · simp

lemma prime_proper_powers {x : ℝ} {f : ℕ → ℝ} :
  (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f q) - prime_summatory f 1 x =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 2 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  rw [exact_sum_prime_powers, prime_summatory, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  have hk : 1 ≤ ⌊log x / Real.log p⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  rw [Finset.Icc_eq_insert_Icc_succ hk, Finset.sum_insert, pow_one, add_comm]
  · rw [Finset.mem_Icc]
    norm_num

lemma is_O_reciprocal_difference_aux {x : ℝ} :
  |(∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
      prime_summatory (fun p ↦ (((p - 1) * p : ℝ)⁻¹)) 1 x| ≤
    ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) := by
  rw [prime_proper_powers, prime_summatory, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by simpa using hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  let N : ℕ := ⌊log x / Real.log p⌋₊
  have hk : 1 ≤ N := by
    dsimp [N]
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  have hgeom :
      ∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹ =
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) := by
    simpa only [← Finset.Ico_succ_right_eq_Icc, inv_pow, Nat.succ_eq_add_one,
      Nat.succ_eq_succ] using
      (geom_sum_Ico' (x := (p : ℝ)⁻¹)
        (by simpa using (inv_ne_one.mpr hp1.ne'))
        (Nat.succ_le_succ hk))
  have hdiff :
      |(∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹) - (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    rw [hgeom]
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) -
            (((p - 1) * p : ℝ)⁻¹) =
          -(((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1)) := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      have haux : (p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N = p := by
        rw [inv_pow]
        field_simp [hp0'.ne', pow_ne_zero N hp0'.ne']
      have hrewrite :
          (1 - (p : ℝ) ^ 2 * (1 / (p : ℝ)) ^ (N + 1) - 1) * (p : ℝ) ^ N =
            -((p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N) := by
        ring_nf
      rw [hrewrite, haux]
    rw [hstep, abs_neg, abs_of_nonneg]
    exact div_nonneg (inv_nonneg.2 (pow_nonneg hp0'.le _)) (sub_nonneg.2 hp1.le)
  have hdiff' :
      |(∑ k ∈ Finset.Icc 2 ⌊log x / Real.log p⌋₊, (↑(p ^ k) : ℝ)⁻¹) -
          (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    simpa [N, Nat.cast_pow] using hdiff
  rw [hdiff']
  have hratio :
      ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) ≤ 2 * ((p : ℝ) ^ (N + 1))⁻¹ := by
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) =
          ((p : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) ^ (N + 1))⁻¹ := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      ring_nf
    rw [hstep]
    have hp_ratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
      have hp_sub : 0 < (p : ℝ) - 1 := sub_pos_of_lt hp1
      rw [div_le_iff₀ hp_sub]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      nlinarith
    exact mul_le_mul_of_nonneg_right hp_ratio (inv_nonneg.2 (pow_nonneg hp0'.le _))
  have hxp : x < (p : ℝ) ^ (N + 1) := by
    have hlogb : Real.logb p x < (N + 1 : ℝ) := by
      dsimp [N]
      simpa [Real.log_div_log] using Nat.lt_floor_add_one (log x / Real.log p)
    have hxpow : x < (p : ℝ) ^ ((N + 1 : ℕ) : ℝ) := by
      convert (Real.logb_lt_iff_lt_rpow hp1 hx).1 hlogb using 1
      norm_num
    rwa [Real.rpow_natCast] at hxpow
  have hinv : ((p : ℝ) ^ (N + 1))⁻¹ ≤ x⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hx hxp.le)
  exact hratio.trans (mul_le_mul_of_nonneg_left hinv (by positivity))

lemma is_O_reciprocal_difference : ∃ c,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := intermediate_bound
  refine ⟨c, ?_⟩
  have hc' : Asymptotics.IsBigO atTop
      (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
      (fun x ↦ (log x)⁻¹) := by
    refine hc.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine Asymptotics.IsBigO.triangle ?_ hc'
  have haux0 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ) * x⁻¹)
      (fun x ↦ (log x)⁻¹) := by
    refine (is_O_prime_counting_div_log.mul (isBigO_refl _ _)).congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hx.ne', one_mul]
  have haux : Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ))
      (fun x ↦ (log x)⁻¹) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (haux0.const_mul_left 2)
  have hbound :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦
          (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
            prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
            prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x)
        (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [one_mul, norm_eq_abs, norm_eq_abs]
    have hcard :
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
          (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
      have hcard' :
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := by
        rw [Finset.sum_const, prime_counting_eq_card_primes]
      calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := hcard'
        _ = (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
          exact nsmul_eq_mul (π ⌊x⌋₊) (2 * x⁻¹)
    exact (is_O_reciprocal_difference_aux).trans (le_trans (le_of_eq hcard) (le_abs_self _))
  exact hbound.trans haux

lemma prime_power_reciprocal : ∃ b,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) - (log (log x) + b))
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_reciprocal_difference
  refine ⟨meissel_mertens + c, ?_⟩
  exact (hc.add prime_reciprocal).congr_left fun x ↦ by ring_nf

lemma summable_indicator_iff_subtype {α β : Type*} [TopologicalSpace α] [AddCommMonoid α]
  {s : Set β} (f : β → α) :
  Summable (f ∘ Subtype.val : s → α) ↔ Summable (s.indicator f) := by
  simpa [Function.comp_def] using (summable_subtype_iff_indicator (s := s) (f := f))

lemma is_unit_of_is_unit_pow {α : Type*} [CommMonoid α] {a : α} :
  ∀ n, n ≠ 0 → (IsUnit (a ^ n) ↔ IsUnit a) := by
  intro n
  induction n with
  | zero =>
      intro h
      exact (h rfl).elim
  | succ n ih =>
      cases n with
      | zero =>
          intro _
          simp
      | succ n =>
          intro _
          rw [pow_succ, IsUnit.mul_iff, ih (Nat.succ_ne_zero _), and_self]

lemma is_prime_pow_and_not_prime_iff {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (x : α) :
  IsPrimePow x ∧ ¬ Prime x ↔ (∃ p k, Prime p ∧ 1 < k ∧ p ^ k = x) := by
  constructor
  · rintro ⟨⟨p, k, hp, hk, rfl⟩, hx⟩
    refine ⟨p, k, hp, ?_, rfl⟩
    rw [← Nat.succ_le_iff] at hk
    exact lt_of_le_of_ne hk fun h => hx (h ▸ by simpa using hp)
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hk0 : k ≠ 0 := by omega
    refine ⟨IsPrimePow.pow hp.isPrimePow hk0, fun hx => ?_⟩
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_add]
      simp [pow_one, mul_comm]
    have hu : IsUnit (p ^ (k - 1)) :=
      (hx.irreducible.isUnit_or_isUnit hpow).resolve_left hp.not_unit
    exact hp.not_unit <| (is_unit_of_is_unit_pow (a := p) (k - 1) (by omega)).mp hu

lemma log_one_sub_recip {p : ℕ} (hp : 1 < p) :
  |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ (((p - 1) * p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hpInv : |(p : ℝ)⁻¹| < 1 := by
    simpa [abs_of_nonneg hp0.le] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  have h := Real.abs_log_sub_add_sum_range_le hpInv 1
  have h' :
      |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) := by
    simpa [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, div_one, pow_one]
      using h
  have hrew : |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) = (((p - 1) * p : ℝ)⁻¹) := by
    rw [abs_inv, abs_of_nonneg hp0.le, pow_two, div_eq_mul_inv]
    field_simp [hp0.ne']
  exact h'.trans_eq hrew

lemma my_func_neg {p : ℕ} (hp : 1 < p) : (p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹) ≤ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hsub : 0 < 1 - (p : ℝ)⁻¹ := by
    exact sub_pos_of_lt <| by simpa [one_div] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  linarith [log_le_sub_one_of_pos hsub]

lemma mertens_third_log_error :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c)
    (fun x : ℝ ↦ x⁻¹) := by
  simp only [Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · exact neg_le_of_neg_le (neg_le_of_abs_le (log_one_sub_recip h.one_lt))
    · exact my_mul_thing'
  · split_ifs with h
    · rw [neg_nonneg]
      exact my_func_neg h.one_lt
    · rfl

lemma mertens_third_log :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        log (1 - (p : ℝ)⁻¹)⁻¹ - (log (log x) + c))
    (fun x : ℝ ↦ (log x)⁻¹) := by
  obtain ⟨c₂, hc₂⟩ := mertens_third_log_error
  have hc₂' : Asymptotics.IsBigO atTop
      (fun x : ℝ ↦
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c₂)
      (fun x ↦ (log x)⁻¹) := by
    refine hc₂.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine ⟨c₂ + meissel_mertens, (prime_reciprocal.add hc₂').congr_left ?_⟩
  intro x
  simp only [Real.log_inv, Finset.sum_neg_distrib, Finset.sum_add_distrib, neg_add,
    prime_summatory]
  ring

lemma partial_euler_trivial_upper_bound {n : ℕ} : partial_euler_product n ≤ 2 ^ π n := by
  rw [partial_euler_product, prime_counting_eq_card_primes, ← Finset.prod_const]
  have hpos : ∀ i : ℕ, i.Prime → 0 < (1 - (i : ℝ)⁻¹) := fun i hi =>
    sub_pos_of_lt <| by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.pos
      simpa using (one_div_lt_one_div hi0 zero_lt_one).2 (by exact_mod_cast hi.one_lt)
  refine Finset.prod_le_prod (fun i hi => (inv_pos.2 (hpos i (Finset.mem_filter.mp hi).2)).le)
    (fun i hi => ?_)
  rcases Finset.mem_filter.mp hi with ⟨_, hip⟩
  have hip0 : (0 : ℝ) < i := by exact_mod_cast hip.pos
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (i : ℝ)⁻¹ := by
    field_simp [hip0.ne']
    nlinarith [show (2 : ℝ) ≤ i by exact_mod_cast hip.two_le]
  have hinv : (1 - (i : ℝ)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (hpos _ hip) (by positivity)]
    exact hhalf
  norm_num at hinv ⊢
  exact hinv

lemma mertens_third :
  ∃ c, 0 < c ∧
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊ - c * Real.log x)
      (fun _ ↦ (1 : ℝ)) := by
  obtain ⟨c, hc⟩ := mertens_third_log
  obtain ⟨k, hk₀, hk⟩ := hc.exists_pos
  refine ⟨Real.exp c, Real.exp_pos _, Asymptotics.IsBigO.of_bound (2 * (k * Real.exp c)) ?_⟩
  filter_upwards [hk.bound, Real.tendsto_log_atTop.eventually (eventually_ge_atTop k)] with x hx hx'
  have hk' : k * (Real.log x)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (hk₀.trans_le hx')]
    simpa using hx'
  rw [norm_eq_abs, norm_inv, Real.norm_of_nonneg (hk₀.le.trans hx')] at hx
  have i := (Real.abs_exp_sub_one_le (hx.trans hk')).trans
    (mul_le_mul_of_nonneg_left hx zero_le_two)
  have hx'' : 0 < Real.log x := hk₀.trans_le hx'
  have hx''' : 0 < Real.exp c * Real.log x := mul_pos (Real.exp_pos _) hx''
  have hp : ∀ p, p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime → 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact inv_pos.2 (sub_pos_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.2.one_lt)))
  rw [Real.exp_sub, Real.exp_add, Real.exp_log hx'', ← Real.log_prod (fun p h ↦ (hp p h).ne'),
    Real.exp_log (Finset.prod_pos hp), mul_comm, div_sub_one hx'''.ne', abs_div,
    abs_of_nonneg hx'''.le, div_le_iff₀ hx''', mul_assoc, mul_mul_mul_comm,
    inv_mul_cancel₀ hx''.ne', mul_one] at i
  simpa [partial_euler_product, norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using i

lemma weak_mertens_third_upper :
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊) log := by
  let ⟨c, _, hc⟩ := mertens_third
  exact ((hc.trans (is_o_one_log 1).isBigO).add
    (Asymptotics.isBigO_const_mul_self c _ _)).congr_left (by simp)

lemma weak_mertens_third_lower :
    Asymptotics.IsBigO atTop log (fun x ↦ partial_euler_product ⌊x⌋₊) := by
  obtain ⟨c, hc₀, hc⟩ := mertens_third
  have h := Asymptotics.isBigO_self_const_mul hc₀.ne' log atTop
  have h' := hc.trans_isLittleO ((is_o_one_log 1).trans_isBigO h)
  exact (h.trans h'.right_isBigO_add).congr_right (by simp)

lemma weak_mertens_third_upper_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 2 ≤ x → ‖partial_euler_product (⌊x⌋₊)‖ ≤ c * ‖log x‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_upper.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  refine ⟨max c (2 ^ c₁ / Real.log 2), lt_max_of_lt_left hc₀, fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    norm_of_nonneg (Real.log_nonneg (one_le_two.trans hx))]
  have hpow : (2 : ℝ) ^ π ⌊x⌋₊ ≤ 2 ^ c₁ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have hpi : (π ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℕ) := by
      exact_mod_cast (prime_counting_le_self ⌊x⌋₊)
    exact le_trans hpi ((Nat.floor_le (zero_le_two.trans hx)).trans h)
  have hupper : 2 ^ c₁ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
    calc
      2 ^ c₁ = (2 ^ c₁ / Real.log 2) * Real.log 2 := by
        field_simp [(Real.log_pos one_lt_two).ne']
      _ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
        refine mul_le_mul (le_max_right _ _) (Real.log_le_log zero_lt_two hx)
          (Real.log_nonneg one_le_two) ?_
        exact le_trans (by positivity : 0 ≤ 2 ^ c₁ / Real.log 2) (le_max_right _ _)
  exact (partial_euler_trivial_upper_bound.trans hpow).trans hupper

lemma weak_mertens_third_lower_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 1 ≤ x → c * ‖log x‖ ≤ ‖partial_euler_product (⌊x⌋₊)‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_lower.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  let c' := max c (Real.log c₁)
  have hc' : 0 < c' := lt_max_of_lt_left hc₀
  refine ⟨c'⁻¹, inv_pos.2 hc', fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · rw [inv_mul_le_iff₀ hc']
    exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (Real.log_nonneg hx),
    norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound)]
  have hlog : Real.log x ≤ c' := by
    exact le_trans (Real.log_le_log (zero_lt_one.trans_le hx) h) (le_max_right _ _)
  have hone : c'⁻¹ * Real.log x ≤ 1 := by
    rw [inv_mul_le_iff₀ hc', mul_one]
    exact hlog
  exact hone.trans (partial_euler_trivial_lower_bound (n := ⌊x⌋₊))

lemma two_pow_card_distinct_divisors_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
  2 ^ ω n ≤ ArithmeticFunction.sigma 0 n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.pow_card_le_prod _ _ _ ?_
  intro p hp
  have hp0 : 0 < n.factorization p :=
    Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  omega

lemma mul_eq_mul_iff {a b c d : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d) :
  a * b = c * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases hac.eq_or_lt with rfl | hac'
    · exact ⟨rfl, Nat.mul_left_cancel ha (show a * b = a * d by simpa using h)⟩
    rcases hbd.eq_or_lt with rfl | hbd'
    · exact ⟨Nat.mul_right_cancel hb (show a * b = c * b by simpa using h), rfl⟩
    exact False.elim <| (mul_lt_mul'' hac' hbd' ha.le hb.le).ne h
  · rintro ⟨rfl, rfl⟩
    rfl

lemma divisor_count_eq_pow_iff_squarefree {n : ℕ} :
  ArithmeticFunction.sigma 0 n = 2 ^ ω n ↔ Squarefree n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization, ← Finset.prod_const,
    Nat.squarefree_iff_factorization_le_one hn, eq_comm]
  rw [Finset.prod_eq_prod_iff_of_le']
  · constructor
    · intro h p
      by_cases hp : p ∈ n.factorization.support
      · have hpEq : 2 = n.factorization p + 1 := h p hp
        omega
      · rw [Finsupp.notMem_support_iff.mp hp]
        exact Nat.zero_le 1
    · intro h p hp
      have hp0 : 0 < n.factorization p :=
        Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hp1 : n.factorization p ≤ 1 := h p
      omega
  · intro _ _
    exact zero_lt_two
  · intro p hp
    have hp0 : 0 < n.factorization p :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    omega

lemma tendsto_primorial_at_top :
  Tendsto primorial atTop atTop := by
  apply primorial_monotone.tendsto_atTop_atTop
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  refine ⟨p, hp₁.trans ?_⟩
  exact Nat.le_of_dvd (primorial_pos _) hp₂.dvd_primorial

lemma primorial_three : primorial 3 = 6 := by
  decide

lemma two_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ≤ primorial n := by
  rw [← primorial_two]
  exact primorial_monotone hn

lemma squarefree_prime_prod {ι : Type*} {s : Finset ι} (f : ι → ℕ)
    (hs : ∀ i ∈ s, (f i).Prime) (hf : Set.InjOn f (s : Set ι)) :
  Squarefree (s.prod f) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (hs i hi) (hs j hj)).2 fun hEq => hij (hf hi hj hEq)
  · intro i hi
    exact (hs i hi).squarefree

lemma divisor_lower_bound_aux (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ n : ℕ in atTop,
      1 / log (log (n : ℝ)) * (1 - ε) ≤ 1 / (log (log (n : ℝ)) - c) := by
  suffices hmain :
      ∀ᶠ x : ℝ in atTop, 1 / x * (1 - ε) ≤ 1 / (x - c) by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually hmain
  filter_upwards [eventually_ge_atTop (c + -c / ε), eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop c] with x hx hx' hx''
  have hx0 : 0 < x - c := sub_pos_of_lt hx''
  have haux : ε * c - c ≤ ε * x := by
    have := mul_le_mul_of_nonneg_left hx hε.le
    simpa [sub_eq_add_neg, mul_add, mul_div_cancel₀ _ hε.ne'] using this
  have hmul : (1 - ε) * (x - c) ≤ x := by
    nlinarith
  have hmid : 1 - ε ≤ x / (x - c) := (le_div_iff₀ hx0).2 hmul
  have hleft : 1 / x * (1 - ε) = (1 - ε) / x := by ring
  rw [hleft]
  exact (div_le_iff₀ hx').2 <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmid

lemma factors_primorial {n : ℕ} :
  (primorial n).primeFactorsList = (List.range (n + 1)).filter Nat.Prime := by
  have hrange : (List.range (n + 1)).Nodup := by
    simpa using (List.nodup_range : (List.range (n + 1)).Nodup)
  have hnodup : ((List.range (n + 1)).filter Nat.Prime).Nodup := hrange.filter _
  have htf :
      ((List.range (n + 1)).filter Nat.Prime).toFinset =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext x
    simp
  have hprod : ((List.range (n + 1)).filter Nat.Prime).prod = primorial n := by
    calc
      ((List.range (n + 1)).filter Nat.Prime).prod
          = ((List.range (n + 1)).filter Nat.Prime).toFinset.prod id := by
              simpa using (List.prod_toFinset id hnodup).symm
      _ = primorial n := by
            rw [htf, primorial]
            rfl
  refine
    ((Nat.primeFactorsList_unique hprod (fun p hp => by
        simpa using (List.mem_filter.mp hp).2)).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  have hpair : List.Pairwise (fun a b : ℕ => a ≤ b) (List.range (n + 1)) := by
    simpa using (List.sortedLT_range (n + 1)).pairwise.imp (@Nat.le_of_lt)
  exact hpair.sublist List.filter_sublist

@[simp] lemma to_finset_filter
  {α : Type*} {l : List α} (p : α → Prop) [DecidableEq α] [DecidablePred p] :
  (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp

@[simp] lemma to_finset_range {n : ℕ} : (List.range n).toFinset = Finset.range n := by
  simpa using List.toFinset_range n

lemma factors_to_finset_primorial {n : ℕ} :
  (primorial n).primeFactorsList.toFinset = (Finset.range (n + 1)).filter Nat.Prime := by
  rw [factors_primorial]
  simp

lemma card_distinct_factors_primorial {n : ℕ} : ω (primorial n) = π n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    factors_to_finset_primorial, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

lemma card_factors_primorial {n : ℕ} : Ω (primorial n) = π n := by
  rw [← card_distinct_factors_primorial, eq_comm,
    ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (primorial_pos _).ne']
  exact squarefree_primorial _

lemma le_log_sigma_zero_primorial :
  ∃ c : ℝ, ∀ p, 2 ≤ p →
    (log (primorial p : ℝ) * Real.log 2) / (log (log (primorial p : ℝ)) - c) ≤
      Real.log (ArithmeticFunction.sigma 0 (primorial p)) := by
  obtain ⟨c, hc₀, hc⟩ := chebyshev_first_all
  refine ⟨Real.log c, ?_⟩
  intro p hp
  have hp₁ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₂ : 0 < (p : ℝ) := zero_lt_two.trans_le hp₁
  have hp₃ : 0 < chebyshev_first p := chebyshev_first_pos hp₁
  have htheta : log (primorial p : ℝ) = chebyshev_first p := by
    simpa [chebyshev_first] using (Chebyshev.theta_eq_log_primorial (p : ℝ)).symm
  have hpow : ((2 : ℝ) ^ ω (primorial p)) = (2 : ℝ) ^ ((ω (primorial p) : ℝ)) := by
    rw [← Real.rpow_natCast]
  rw [divisor_count_eq_pow_iff_squarefree.2 (squarefree_primorial _), Nat.cast_pow, Nat.cast_two,
    hpow, Real.log_rpow (by positivity), card_distinct_factors_primorial, htheta]
  have h₁ : chebyshev_first p ≤ π p * log (p : ℝ) := by
    simpa using chebyshev_first_trivial_bound (p : ℝ)
  have hcp : c * (p : ℝ) ≤ chebyshev_first p := by
    simpa [Real.norm_of_nonneg hp₂.le, Real.norm_of_nonneg hp₃.le] using hc (p : ℝ) hp₁
  have h₂ : log (p : ℝ) ≤ log (chebyshev_first p) - Real.log c := by
    have hlog := log_le_log_of_le (mul_pos hc₀ hp₂) hcp
    rw [Real.log_mul hc₀.ne' hp₂.ne'] at hlog
    linarith
  have h₃ : 0 < log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp)
  have h₄ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg one_le_two
  have h₅ : (0 : ℝ) ≤ π p := Nat.cast_nonneg (π p)
  have hden : 0 < log (chebyshev_first p) - Real.log c := by
    linarith
  refine (div_le_iff₀ hden).2 ?_
  calc
    chebyshev_first p * Real.log 2 ≤ (π p * log (p : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h₁ h₄
    _ ≤ (π p * (log (chebyshev_first p) - Real.log c)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ h₅) h₄
    _ = π p * Real.log 2 * (log (chebyshev_first p) - Real.log c) := by ring

lemma one_le_sigma {k n : ℕ} (hn : n ≠ 0) : 1 ≤ ArithmeticFunction.sigma k n := by
  simpa [ArithmeticFunction.sigma_apply] using
    (Finset.single_le_sum
      (f := fun d : ℕ ↦ d ^ k)
      (fun d _ => Nat.zero_le _)
      (by simp [hn] : 1 ∈ n.divisors))

lemma divisor_lower_bound_log {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
  obtain ⟨c, hc⟩ := le_log_sigma_zero_primorial
  have hmain :
      ∃ᶠ n : ℕ in atTop,
        log (n : ℝ) * Real.log 2 / (log (log (n : ℝ)) - c) ≤
          log (ArithmeticFunction.sigma 0 n : ℝ) := by
    exact tendsto_primorial_at_top.frequently (eventually_atTop.2 ⟨2, hc⟩).frequently
  apply (hmain.and_eventually (divisor_lower_bound_aux c hε)).mp
  simp only [and_imp]
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁ hn₂
  apply hn₁.trans'
  rw [mul_div_assoc, mul_comm (log (n : ℝ))]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (Nat.one_le_cast.2 hn₀))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hn₂ (Real.log_nonneg one_le_two)

lemma divisor_lower_bound {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) ≤
        ArithmeticFunction.sigma 0 n := by
  apply (divisor_lower_bound_log hε).mp
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁
  have hn₀' : 0 < n := hn₀
  have hn₀'' : (0 : ℝ) < n := by exact_mod_cast hn₀'
  have hsigma : (0 : ℝ) < ArithmeticFunction.sigma 0 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀'.ne'
  have hlog :
      log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε))) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
    simpa [Real.log_rpow hn₀''] using hn₁
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hn₀'' _) hsigma).1 hlog

lemma cobounded_of_frequently {α : Type*} [ConditionallyCompleteLattice α]
  {f : Filter α} (c : α) (hc : ∃ᶠ x in f, c ≤ x) :
  Filter.IsCobounded (· ≤ ·) f := by
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨x, hxc, hxd⟩ := (hc.and_eventually hd).exists
  exact hxc.trans hxd

lemma Limsup_eq_of_eventually_of_frequently {f : Filter ℝ} (c : ℝ)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c + ε)
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c - ε ≤ x) :
  limsup id f = c := by
  have hb : f.IsBounded (· ≤ ·) := ⟨c + 1, upper 1 zero_lt_one⟩
  have hb' : f.IsBoundedUnder (· ≤ ·) id := by
    simpa [Filter.IsBoundedUnder]
      using hb
  have hc : f.IsCobounded (· ≤ ·) :=
    cobounded_of_frequently (c - 1) (by simpa using lower 1 zero_lt_one)
  have hc' : f.IsCoboundedUnder (· ≤ ·) id := by
    simpa [Filter.IsCoboundedUnder]
      using hc
  apply le_antisymm
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    simpa using (limsup_le_of_le (u := id) (f := f) (a := c + ε) hc' (upper ε hε))
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    rw [← sub_le_iff_le_add]
    simpa using (le_limsup_of_frequently_le (u := id) (f := f) (a := c - ε) (lower ε hε) hb')

lemma Limsup_eq_of_eventually_of_frequently_mul {f : Filter ℝ} {c : ℝ} (hc : 0 ≤ c)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c * (1 + ε))
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c * (1 - ε) ≤ x) :
  limsup id f = c := by
  rcases hc.eq_or_lt with rfl | hc'
  · refine Limsup_eq_of_eventually_of_frequently 0 (fun ε hε => ?_) (fun ε hε => ?_)
    · apply Filter.EventuallyLE.trans (upper 1 zero_lt_one)
        (Filter.Eventually.of_forall fun x => ?_)
      linarith [hε.le]
    · apply (lower 1 zero_lt_one).mono
      intro x hx
      linarith [hε.le]
  · apply Limsup_eq_of_eventually_of_frequently
    · intro ε hε
      refine (upper (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        x ≤ c * (1 + ε / c) := hx
        _ = c + ε := by
          field_simp [hc'.ne']
    · intro ε hε
      refine (lower (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        c - ε = c * (1 - ε / c) := by
          field_simp [hc'.ne']
        _ ≤ x := hx

lemma divisor_limsup :
  atTop.limsup
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)) =
    log (2 : ℝ) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have l := Real.tendsto_log_atTop
  refine Limsup_eq_of_eventually_of_frequently_mul
    (f := Filter.map
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ))
      atTop)
    (Real.log_nonneg one_le_two) ?_ ?_
  · intro ε hε
    change ∀ᶠ n : ℕ in atTop,
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ) ≤
        Real.log 2 * (1 + ε)
    filter_upwards [divisor_bound hε, eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    have hlog : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε))) := by
      exact log_le_log_of_le (by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀.ne') hn
    have hlog' : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ) := by
      simpa [Real.log_rpow hn₁] using hlog
    refine (div_le_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hlog' hn₃.le
    have hEq :
        ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) * log (log (n : ℝ)) =
          Real.log 2 * (1 + ε) * log (n : ℝ) := by
      field_simp [hn₃.ne']
    calc
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ))
          ≤ ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) *
              log (log (n : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Real.log 2 * (1 + ε) * log (n : ℝ) := hEq
  · intro ε hε
    change ∃ᶠ n : ℕ in atTop,
      Real.log 2 * (1 - ε) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)
    refine (divisor_lower_bound_log hε).mp ?_
    filter_upwards [eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    intro hn
    refine (le_div_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hn hn₃.le
    have hEq :
        Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := by
      field_simp [hn₃.ne']
    calc
      Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := hEq
      _ ≤ log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
