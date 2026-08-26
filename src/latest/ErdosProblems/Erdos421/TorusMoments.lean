import ErdosProblems.Erdos421.CompleteMeanValue
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Exact continuous Fourier moments for the integer power-sum system -/

namespace Erdos421

open MeasureTheory
open scoped ComplexConjugate

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_torusCharacter_mul_conj {k : ℕ} (m n : Fin k → ℤ) :
    (∫ a : UnitAddTorus (Fin k),
      UnitAddTorus.mFourier m a * conj (UnitAddTorus.mFourier n a)) =
        if m = n then (1 : ℂ) else 0 := by
  classical
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin k)) n m
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp, eq_comm] using h

noncomputable def torusCharacterSum {X : Type*} {k : ℕ} (S : Finset X)
    (f : X → Fin k → ℤ) (a : UnitAddTorus (Fin k)) : ℂ :=
  ∑ x ∈ S, UnitAddTorus.mFourier (f x) a

theorem continuous_torusCharacterSum {X : Type*} {k : ℕ} (S : Finset X)
    (f : X → Fin k → ℤ) : Continuous (torusCharacterSum S f) := by
  unfold torusCharacterSum
  fun_prop

theorem integral_torusCharacterSum_mul_conj {X : Type*} {k : ℕ} (S : Finset X)
    (f : X → Fin k → ℤ) :
    (∫ a : UnitAddTorus (Fin k), torusCharacterSum S f a * conj (torusCharacterSum S f a)) =
      (((S ×ˢ S).filter (fun p ↦ f p.1 = f p.2)).card : ℂ) := by
  classical
  have hterm (x y : X) : Integrable (fun a : UnitAddTorus (Fin k) ↦
      UnitAddTorus.mFourier (f x) a * conj (UnitAddTorus.mFourier (f y) a)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hexpand (a : UnitAddTorus (Fin k)) :
      torusCharacterSum S f a * conj (torusCharacterSum S f a) =
        ∑ x ∈ S, ∑ y ∈ S,
          UnitAddTorus.mFourier (f x) a * conj (UnitAddTorus.mFourier (f y) a) := by
    simp only [torusCharacterSum, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [integral_finsetSum S (fun x _ ↦ integrable_finsetSum S (fun y _ ↦ hterm x y))]
  simp_rw [integral_finsetSum S (fun y _ ↦ hterm _ y), integral_torusCharacter_mul_conj]
  rw [← Finset.sum_product (f := fun p : X × X ↦ if f p.1 = f p.2 then (1 : ℂ) else 0),
    ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem integral_norm_torusCharacterSum_sq {X : Type*} {k : ℕ} (S : Finset X)
    (f : X → Fin k → ℤ) :
    (∫ a : UnitAddTorus (Fin k), ‖torusCharacterSum S f a‖ ^ 2) =
      (((S ×ˢ S).filter (fun p ↦ f p.1 = f p.2)).card : ℝ) := by
  classical
  have h := integral_torusCharacterSum_mul_conj S f
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal,
    ← Complex.ofReal_natCast] at h
  exact Complex.ofReal_injective h

theorem torusCharacter_sum {X : Type*} {k : ℕ} (S : Finset X)
    (f : X → Fin k → ℤ) (a : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (∑ x ∈ S, f x) a =
      ∏ x ∈ S, UnitAddTorus.mFourier (f x) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, UnitAddTorus.mFourier_zero,
      ContinuousMap.one_apply]
  | @insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, UnitAddTorus.mFourier_add, ih]

theorem torusCharacterSum_power {X : Type*} [Fintype X] {k : ℕ}
    (f : X → Fin k → ℤ) (a : UnitAddTorus (Fin k)) (s : ℕ) :
    torusCharacterSum Finset.univ f a ^ s =
      torusCharacterSum Finset.univ (fun x : Fin s → X ↦ ∑ i : Fin s, f (x i)) a := by
  simp only [torusCharacterSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  exact (torusCharacter_sum Finset.univ (fun i ↦ f (x i)) a).symm

theorem torusCharacterSum_moment {X : Type*} [Fintype X] {k : ℕ}
    (f : X → Fin k → ℤ) (s : ℕ) :
    (∫ a : UnitAddTorus (Fin k), ‖torusCharacterSum Finset.univ f a‖ ^ (2 * s)) =
      (((Finset.univ : Finset ((Fin s → X) × (Fin s → X))).filter
        (fun p ↦ (∑ i : Fin s, f (p.1 i)) = ∑ i : Fin s, f (p.2 i))).card : ℝ) := by
  classical
  have h := integral_norm_torusCharacterSum_sq (Finset.univ : Finset (Fin s → X))
    (fun x ↦ ∑ i : Fin s, f (x i))
  simpa only [← torusCharacterSum_power, norm_pow, ← pow_mul, Nat.mul_comm s 2,
    Finset.univ_product_univ] using h

def vinogradovIntegerPoint (k : ℕ) {N : ℕ} (x : Fin N) : Fin k → ℤ :=
  fun j ↦ ((x : ℤ) + 1) ^ ((j : ℕ) + 1)

noncomputable def torusVinogradovWeylSum (k N : ℕ) (a : UnitAddTorus (Fin k)) : ℂ :=
  torusCharacterSum Finset.univ (vinogradovIntegerPoint k : Fin N → Fin k → ℤ) a

theorem sum_vinogradovIntegerPoint {s k N : ℕ} (x : Fin s → Fin N) :
    (∑ i : Fin s, vinogradovIntegerPoint k (x i)) = vinogradovSums k x := by
  funext j
  simp only [Finset.sum_apply, vinogradovIntegerPoint, vinogradovSums]

theorem torusVinogradovWeylSum_moment (s k N : ℕ) :
    (∫ a : UnitAddTorus (Fin k), ‖torusVinogradovWeylSum k N a‖ ^ (2 * s)) =
      (vinogradovCount s k N : ℝ) := by
  have h := torusCharacterSum_moment (vinogradovIntegerPoint k : Fin N → Fin k → ℤ) s
  simpa only [sum_vinogradovIntegerPoint, torusVinogradovWeylSum, vinogradovCount,
    vinogradovSolutions, sub_eq_zero] using h

theorem torusVinogradovWeylSum_complete_meanValue {k : ℕ} (hk : 2 ≤ k) (r N : ℕ) :
    (∫ a : UnitAddTorus (Fin k), ‖torusVinogradovWeylSum k N a‖ ^ (2 * ((r + 1) * k))) ≤
      (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) *
        (N : ℝ) ^ meanValueExponent k r := by
  rw [torusVinogradovWeylSum_moment]
  exact vinogradovCount_complete_meanValue hk r N

theorem torusCharacter_real_apply {k : ℕ} (n : Fin k → ℤ) (b : Fin k → ℝ) :
    UnitAddTorus.mFourier n (fun j ↦ (b j : UnitAddCircle)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ j : Fin k, (n j : ℂ) * (b j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def realVinogradovWeylSum (k N : ℕ) (b : Fin k → ℝ) : ℂ :=
  ∑ x : Fin N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    ∑ j : Fin k, (vinogradovIntegerPoint k x j : ℂ) * (b j : ℂ))

theorem torusVinogradovWeylSum_real (k N : ℕ) (b : Fin k → ℝ) :
    torusVinogradovWeylSum k N (fun j ↦ (b j : UnitAddCircle)) =
      realVinogradovWeylSum k N b := by
  simp only [torusVinogradovWeylSum, torusCharacterSum, torusCharacter_real_apply,
    realVinogradovWeylSum]

theorem realVinogradovWeylSum_moment (s k N : ℕ) (b : Fin k → ℝ) :
    (∫ a : Fin k → ℝ in {a | ∀ j, a j ∈ Set.Ioc (b j) (b j + 1)},
      ‖realVinogradovWeylSum k N a‖ ^ (2 * s)) = (vinogradovCount s k N : ℝ) := by
  have h := UnitAddTorus.integral_preimage
    (fun a : UnitAddTorus (Fin k) ↦ ‖torusVinogradovWeylSum k N a‖ ^ (2 * s)) b
  rw [torusVinogradovWeylSum_moment] at h
  simpa only [torusVinogradovWeylSum_real] using h.symm

end Erdos421
