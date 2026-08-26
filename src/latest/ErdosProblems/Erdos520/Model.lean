import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-- Sample space for independent signs indexed by the natural numbers.

Only prime coordinates are used by the random multiplicative function.
-/
abbrev Omega := ℕ → Bool

/-- The fair law on one Boolean coordinate. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true

instance coin_isProbabilityMeasure : IsProbabilityMeasure coin where
  measure_univ := by
    simp [coin, ENNReal.inv_two_add_inv_two]

/-- Product law for the independent prime signs. -/
noncomputable def μ : Measure Omega :=
  Measure.infinitePi fun _ : ℕ => coin

instance μ_isProbabilityMeasure : IsProbabilityMeasure μ := by
  dsimp [μ]
  infer_instance

/-- The coordinate signs are independent under `μ`. -/
theorem iIndepFun_coordinates :
    iIndepFun (fun p (omega : Omega) => omega p) μ := by
  simpa [μ] using!
    (iIndepFun_infinitePi
      (P := fun _ : ℕ => coin)
      (X := fun _ : ℕ => id)
      (by fun_prop))

/-- Rademacher sign attached to a coordinate. -/
def ε (omega : Omega) (p : ℕ) : ℝ :=
  if omega p then 1 else -1

theorem measurable_ε (p : ℕ) : Measurable fun omega : Omega => ε omega p := by
  exact (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (measurable_pi_apply p)

/-- The real Rademacher signs inherit independence from the Boolean
coordinates. -/
theorem iIndepFun_ε : iIndepFun (fun p (omega : Omega) => ε omega p) μ := by
  simpa [ε, Function.comp_def] using!
    iIndepFun_coordinates.comp
      (fun (_p : ℕ) (b : Bool) => if b then (1 : ℝ) else -1)
      (fun _p => measurable_of_finite _)

@[simp] theorem ε_sq (omega : Omega) (p : ℕ) : ε omega p ^ 2 = 1 := by
  simp [ε]

@[simp] theorem abs_ε (omega : Omega) (p : ℕ) : |ε omega p| = 1 := by
  simp only [ε]
  split <;> simp

theorem integrable_ε (p : ℕ) : Integrable (fun omega : Omega => ε omega p) μ := by
  apply Integrable.of_bound (measurable_ε p).aestronglyMeasurable 1
  exact ae_of_all μ fun omega => by simp

/-- Each prime sign is centered. -/
theorem integral_ε (p : ℕ) : ∫ omega, ε omega p ∂μ = 0 := by
  let g : Bool → ℝ := fun b => if b then 1 else -1
  have hmap : Measure.map (fun omega : Omega => omega p) μ = coin := by
    simpa [μ] using! Measure.infinitePi_map_eval (fun _ : ℕ => coin) p
  calc
    (∫ omega, ε omega p ∂μ) = ∫ omega, g (omega p) ∂μ := by rfl
    _ = ∫ b, g b ∂Measure.map (fun omega : Omega => omega p) μ := by
      symm
      exact integral_map (measurable_pi_apply p).aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂coin := by rw [hmap]
    _ = 0 := by
      have hgfalse : Integrable g ((1 / 2 : ℝ≥0∞) • Measure.dirac false) :=
        (integrable_dirac (f := g) (by simp)).smul_measure (by norm_num)
      have hgtrue : Integrable g ((1 / 2 : ℝ≥0∞) • Measure.dirac true) :=
        (integrable_dirac (f := g) (by simp)).smul_measure (by norm_num)
      rw [coin, integral_add_measure hgfalse hgtrue,
        integral_smul_measure, integral_smul_measure]
      norm_num [g]

/-- The squarefree-supported Rademacher random multiplicative function.

For squarefree `n`, this is the product of the independent signs at the prime
divisors of `n`; on nonsquarefree inputs it is zero.
-/
noncomputable def f (omega : Omega) (n : ℕ) : ℝ :=
  if Squarefree n then
    ∏ p ∈ n.primeFactors, ε omega p
  else
    0

@[simp] theorem f_eq_zero_of_not_squarefree (omega : Omega) {n : ℕ}
    (hn : ¬Squarefree n) :
    f omega n = 0 := by
  simp [f, hn]

/-- Any integer containing the square of a prime has zero coefficient in the
squarefree Rademacher model.  This is the reason Caich's squareful
largest-prime remainder `M_f^(2)` vanishes identically here. -/
@[simp] theorem f_eq_zero_of_prime_sq_dvd (omega : Omega) {n p : ℕ}
    (hp : p.Prime) (hdiv : p * p ∣ n) :
    f omega n = 0 := by
  apply f_eq_zero_of_not_squarefree
  intro hsquarefree
  exact (Nat.squarefree_iff_prime_squarefree.mp hsquarefree p hp) hdiv

/-- Finite sums supported on integers with a repeated prime factor vanish. -/
theorem sum_f_eq_zero_of_prime_sq_dvd (omega : Omega) (s : Finset ℕ)
    (hs : ∀ n ∈ s, ∃ p, p.Prime ∧ p * p ∣ n) :
    ∑ n ∈ s, f omega n = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rcases hs n hn with ⟨p, hp, hdiv⟩
  exact f_eq_zero_of_prime_sq_dvd omega hp hdiv

@[simp] theorem f_eq_prod_primeFactors_of_squarefree (omega : Omega) {n : ℕ}
    (hn : Squarefree n) :
    f omega n = ∏ p ∈ n.primeFactors, ε omega p := by
  simp [f, hn]

@[simp] theorem f_one (omega : Omega) : f omega 1 = 1 := by
  simp [f]

/-- The squarefree Rademacher model is multiplicative on coprime inputs. -/
theorem f_mul_of_coprime (omega : Omega) {m n : ℕ} (hmn : m.Coprime n) :
    f omega (m * n) = f omega m * f omega n := by
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · simp only [f, if_pos ((Nat.squarefree_mul hmn).2 ⟨hm, hn⟩), if_pos hm, if_pos hn]
      rw [hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
    · simp [f, hm, hn, Nat.squarefree_mul hmn]
  · simp [f, hm, Nat.squarefree_mul hmn]

/-- The one-indexed partial sum `M_f(N) = ∑_{n=1}^N f(n)`. -/
noncomputable def partialSum (omega : Omega) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f omega (k + 1)

@[simp] theorem partialSum_zero (omega : Omega) : partialSum omega 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ (omega : Omega) (N : ℕ) :
    partialSum omega (N + 1) = partialSum omega N + f omega (N + 1) := by
  simp [partialSum, Finset.sum_range_succ]

end Problem520
end Erdos
