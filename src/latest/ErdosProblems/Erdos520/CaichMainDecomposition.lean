import ErdosProblems.Erdos520.CaichCoreMainCleanup

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# Exact decomposition of the averaged main smoothing term

This file proves the finite-sum/Fubini bookkeeping omitted in the paper:
one block of `caichInitialSmoothedMain` is exactly its core term plus its
upper boundary strip.  Together with `CaichCoreMainCleanup`, the two pieces
are literal integrals rather than an unspecified remainder.
-/

/-- One prime's contribution to the time-coordinate core kernel. -/
noncomputable def caichCorePrimeTimeTerm
    (X : ℝ) (omega : Omega) (x p : ℕ) (t : ℝ) : ℝ :=
  if t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t then
    (p : ℝ)⁻¹ * |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2
  else 0

theorem caichCoreTimeKernel_eq_sum_primeTerms
    (X : ℝ) (omega : Omega) (x a b : ℕ) (t : ℝ) :
    caichCoreTimeKernel X omega x a b t =
      ∑ p ∈ freshPrimes a b,
        caichCorePrimeTimeTerm X omega x p t := by
  rfl

theorem measurable_caichCorePrimeTimeTerm
    (X : ℝ) (omega : Omega) (x p : ℕ) :
    Measurable (caichCorePrimeTimeTerm X omega x p) := by
  unfold caichCorePrimeTimeTerm
  apply Measurable.ite
  · exact (measurableSet_lt
      (measurable_id.div measurable_const) measurable_const).inter
      (measurableSet_le measurable_const measurable_id)
  · exact measurable_const.mul
      (((measurable_caichStrictSmoothReal_cutoff omega p).comp
        (measurable_const.div measurable_id)).abs.pow_const 2)
  · exact measurable_const

theorem measurable_caichCoreTimeKernel
    (X : ℝ) (omega : Omega) (x a b : ℕ) :
    Measurable (caichCoreTimeKernel X omega x a b) := by
  rw [funext fun t ↦ caichCoreTimeKernel_eq_sum_primeTerms
    X omega x a b t]
  exact Finset.measurable_sum _ fun p _ ↦
    measurable_caichCorePrimeTimeTerm X omega x p

theorem caichCorePrimeTimeTerm_nonneg
    (X : ℝ) (omega : Omega) (x p : ℕ) (t : ℝ) :
    0 ≤ caichCorePrimeTimeTerm X omega x p t := by
  unfold caichCorePrimeTimeTerm
  split_ifs <;> positivity

theorem caichCoreTimeKernel_nonneg
    (X : ℝ) (omega : Omega) (x a b : ℕ) (t : ℝ) :
    0 ≤ caichCoreTimeKernel X omega x a b t := by
  rw [caichCoreTimeKernel_eq_sum_primeTerms]
  exact Finset.sum_nonneg fun p hp ↦
    caichCorePrimeTimeTerm_nonneg X omega x p t

/-- A finite uniform bound sufficient for all compact-interval
integrability obligations. -/
noncomputable def caichCorePrimeTimeBound (x p : ℕ) : ℝ :=
  (p : ℝ)⁻¹ *
    ((((p - 1 + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2

theorem caichCorePrimeTimeTerm_le_bound
    (X : ℝ) (omega : Omega) (x p : ℕ) (t : ℝ) :
    caichCorePrimeTimeTerm X omega x p t ≤
      caichCorePrimeTimeBound x p := by
  unfold caichCorePrimeTimeTerm caichCorePrimeTimeBound
  split_ifs
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _)
        (abs_caichStrictSmoothReal_le omega ((x : ℝ) / t) p) 2)
      (by positivity)
  · positivity

theorem integrableOn_caichCorePrimeTimeTerm
    (X : ℝ) (omega : Omega) (x p : ℕ) (s : Set ℝ)
    (hs : volume s < ⊤) :
    IntegrableOn (caichCorePrimeTimeTerm X omega x p) s := by
  apply IntegrableOn.of_bound hs
    (measurable_caichCorePrimeTimeTerm X omega x p).aestronglyMeasurable
    (caichCorePrimeTimeBound x p)
  filter_upwards with t
  rw [Real.norm_eq_abs,
    abs_of_nonneg (caichCorePrimeTimeTerm_nonneg X omega x p t)]
  exact caichCorePrimeTimeTerm_le_bound X omega x p t

theorem integrableOn_caichCoreTimeKernel_Ioc
    (X : ℝ) (omega : Omega) (x a b : ℕ) {u v : ℝ} :
    IntegrableOn (caichCoreTimeKernel X omega x a b) (Ioc u v) := by
  rw [funext fun t ↦ caichCoreTimeKernel_eq_sum_primeTerms
    X omega x a b t]
  exact integrable_finset_sum _ fun p hp ↦
    integrableOn_caichCorePrimeTimeTerm X omega x p (Ioc u v)
      measure_Ioc_lt_top

/-! ## One-prime support identity -/

private theorem caichCorePrimeTimeSupport_eq_Ico
    {X : ℝ} (hX : 0 < X) (p : ℕ) :
    {t : ℝ | t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t} =
      Ico (p : ℝ) ((p : ℝ) * (1 + 1 / X)) := by
  have hfactor : 0 < 1 + 1 / X := by positivity
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · rintro ⟨hupper, hlower⟩
    exact ⟨hlower, (div_lt_iff₀ hfactor).mp hupper⟩
  · rintro ⟨hlower, hupper⟩
    exact ⟨(div_lt_iff₀ hfactor).mpr hupper, hlower⟩

/-- On a global interval containing the whole short prime interval, the
indicator term integrates to the original interval integral. -/
theorem setIntegral_caichCorePrimeTimeTerm
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x : ℕ)
    {a b p : ℕ} (hp : p ∈ freshPrimes a b) :
    (∫ t in Ioc (a : ℝ) ((b : ℝ) * (1 + 1 / X)),
        caichCorePrimeTimeTerm X omega x p t) =
      (p : ℝ)⁻¹ *
        ∫ t in (p : ℝ)..(p : ℝ) * (1 + 1 / X),
          |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2 := by
  let S : Set ℝ :=
    {t : ℝ | t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t}
  let g : ℝ → ℝ := fun t ↦
    (p : ℝ)⁻¹ * |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2
  have hfactor : 0 < 1 + 1 / X := by positivity
  have hmem := mem_freshPrimes.mp hp
  have hpq : (p : ℝ) ≤ (p : ℝ) * (1 + 1 / X) := by
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hmem.1.pos
    have hone : (1 : ℝ) ≤ 1 + 1 / X := by
      have hinv : (0 : ℝ) ≤ 1 / X := by positivity
      linarith
    calc
      (p : ℝ) = (p : ℝ) * 1 := by ring
      _ ≤ (p : ℝ) * (1 + 1 / X) :=
        mul_le_mul_of_nonneg_left hone hpR.le
  have hS : S = Ico (p : ℝ) ((p : ℝ) * (1 + 1 / X)) := by
    exact caichCorePrimeTimeSupport_eq_Ico hX p
  have hSmeas : MeasurableSet S := hS ▸ measurableSet_Ico
  have hcontain : S ⊆ Ioc (a : ℝ) ((b : ℝ) * (1 + 1 / X)) := by
    rw [hS]
    intro t ht
    have hap : (a : ℝ) < (p : ℝ) := by exact_mod_cast hmem.2.1
    have hpb : (p : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmem.2.2
    exact ⟨hap.trans_le ht.1,
      ht.2.le.trans (mul_le_mul_of_nonneg_right hpb hfactor.le)⟩
  have hinter :
      Ioc (a : ℝ) ((b : ℝ) * (1 + 1 / X)) ∩ S = S :=
    inter_eq_right.mpr hcontain
  have hterm : caichCorePrimeTimeTerm X omega x p = S.indicator g := by
    funext t
    unfold caichCorePrimeTimeTerm
    dsimp only [S, g]
    by_cases ht : t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t
    · have hmemS : t ∈ {t : ℝ |
          t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t} := ht
      rw [if_pos ht, Set.indicator_of_mem hmemS]
    · have hnotmemS : t ∉ {t : ℝ |
          t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t} := ht
      rw [if_neg ht, Set.indicator_of_notMem hnotmemS]
  rw [hterm, setIntegral_indicator hSmeas, hinter, hS,
    integral_Ico_eq_integral_Ioc, integral_const_mul]
  rw [← intervalIntegral.integral_of_le hpq]

/-! ## Recombining primes and the two adjacent time intervals -/

/-- Time-coordinate boundary strip. -/
noncomputable def caichBoundaryAveragedBlockMainTime
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  X * ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
    caichCoreTimeKernel X omega x a b t

/-- The original averaged main term of one block is the time-kernel integral
over the entire containing interval. -/
theorem caichInitialSmoothedMain_eq_globalCoreTime
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x a b : ℕ) :
    caichInitialSmoothedMain X omega x a b =
      X * ∫ t in Ioc (a : ℝ) ((b : ℝ) * (1 + 1 / X)),
        caichCoreTimeKernel X omega x a b t := by
  have hkernel :
      caichCoreTimeKernel X omega x a b = fun t ↦
        ∑ p ∈ freshPrimes a b,
          caichCorePrimeTimeTerm X omega x p t := by
    funext t
    exact caichCoreTimeKernel_eq_sum_primeTerms X omega x a b t
  unfold caichInitialSmoothedMain caichShortPrimeAverage
  rw [hkernel,
    integral_finset_sum (freshPrimes a b) (fun p hp ↦
      integrableOn_caichCorePrimeTimeTerm X omega x p
        (Ioc (a : ℝ) ((b : ℝ) * (1 + 1 / X))) measure_Ioc_lt_top),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [setIntegral_caichCorePrimeTimeTerm hX omega x hp]
  ring

/-- Splitting the containing interval at the block endpoint gives the exact
core and boundary time pieces. -/
theorem caichInitialSmoothedMain_eq_coreTime_add_boundaryTime
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x : ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    caichInitialSmoothedMain X omega x a b =
      caichCoreAveragedBlockMainTime X omega x a b +
        caichBoundaryAveragedBlockMainTime X omega x a b := by
  have hfactor : 0 < 1 + 1 / X := by positivity
  have hbb : (b : ℝ) ≤ (b : ℝ) * (1 + 1 / X) := by
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
    have hone : (1 : ℝ) ≤ 1 + 1 / X := by
      have hinv : (0 : ℝ) ≤ 1 / X := by positivity
      linarith
    calc
      (b : ℝ) = (b : ℝ) * 1 := by ring
      _ ≤ (b : ℝ) * (1 + 1 / X) :=
        mul_le_mul_of_nonneg_left hone hb0
  let F : ℝ → ℝ := caichCoreTimeKernel X omega x a b
  have hcore : IntegrableOn F (Ioc (a : ℝ) (b : ℝ)) :=
    integrableOn_caichCoreTimeKernel_Ioc X omega x a b
  have hboundary : IntegrableOn F
      (Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X))) :=
    integrableOn_caichCoreTimeKernel_Ioc X omega x a b
  have hunion := setIntegral_union
    (Ioc_disjoint_Ioc_of_le (le_refl (b : ℝ))) measurableSet_Ioc
    hcore hboundary
  rw [Ioc_union_Ioc_eq_Ioc (by exact_mod_cast hab) hbb] at hunion
  rw [caichInitialSmoothedMain_eq_globalCoreTime hX]
  unfold caichCoreAveragedBlockMainTime
    caichBoundaryAveragedBlockMainTime
  dsimp only [F] at hunion
  rw [hunion]
  ring

/-- The explicit `z`-coordinate boundary is exactly its time-coordinate
counterpart. -/
theorem caichBoundaryAveragedBlockMain_eq_time
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x : ℕ)
    {a b : ℕ} (hx : 0 < x) (hb : 1 ≤ b) :
    caichBoundaryAveragedBlockMain X omega x a b =
      caichBoundaryAveragedBlockMainTime X omega x a b := by
  let B : ℝ := (b : ℝ) * (1 + 1 / X)
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hfactor : (0 : ℝ) < 1 + 1 / X := by positivity
  have hBpos : (0 : ℝ) < B := by
    exact mul_pos hbR hfactor
  have hbB : (b : ℝ) ≤ B := by
    dsimp only [B]
    have hone : (1 : ℝ) ≤ 1 + 1 / X := by
      have hinv : (0 : ℝ) ≤ 1 / X := by positivity
      linarith
    calc
      (b : ℝ) = (b : ℝ) * 1 := by ring
      _ ≤ (b : ℝ) * (1 + 1 / X) :=
        mul_le_mul_of_nonneg_left hone hbR.le
  have hsub := integral_comp_const_div_Ioc
    (g := caichCoreTimeKernel X omega x a b)
    (d := (x : ℝ)) (a := (b : ℝ)) (b := B)
    (by exact_mod_cast hx) hbR hbB
  have hpullback :
      (∫ z in Ioc ((x : ℝ) / B) ((x : ℝ) / (b : ℝ)),
          caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2) =
        ∫ z in Ioc ((x : ℝ) / B) ((x : ℝ) / (b : ℝ)),
          caichCoreBlockKernel X omega x a b z / z ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    have hzpos : 0 < z := by
      have hxB : (0 : ℝ) ≤ (x : ℝ) / B :=
        div_nonneg (Nat.cast_nonneg x) hBpos.le
      exact hxB.trans_lt hz.1
    change
      caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2 =
        caichCoreBlockKernel X omega x a b z / z ^ 2
    rw [caichCoreTimeKernel_comp_div hX.ne' hx hzpos.ne' omega]
  unfold caichBoundaryAveragedBlockMain
    caichBoundaryAveragedBlockMainTime
  dsimp only [B] at hsub hpullback ⊢
  calc
    (x : ℝ) * X *
          (∫ z in Ioc
              ((x : ℝ) / ((b : ℝ) * (1 + 1 / X)))
              ((x : ℝ) / (b : ℝ)),
            caichCoreBlockKernel X omega x a b z / z ^ 2) =
        X * ((x : ℝ) *
          (∫ z in Ioc
              ((x : ℝ) / ((b : ℝ) * (1 + 1 / X)))
              ((x : ℝ) / (b : ℝ)),
            caichCoreBlockKernel X omega x a b z / z ^ 2)) := by ring
    _ = X * ((x : ℝ) *
          (∫ z in Ioc
              ((x : ℝ) / ((b : ℝ) * (1 + 1 / X)))
              ((x : ℝ) / (b : ℝ)),
            caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2)) := by
      rw [hpullback]
    _ = X *
          (∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
            caichCoreTimeKernel X omega x a b t) := by
      rw [hsub]

/-- Final one-block identity in the literal `z`-coordinate objects. -/
theorem caichInitialSmoothedMain_eq_core_add_boundary
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x : ℕ)
    {a b : ℕ} (hx : 0 < x) (ha : 1 ≤ a) (hab : a ≤ b) :
    caichInitialSmoothedMain X omega x a b =
      caichCoreAveragedBlockMain X omega x a b +
        caichBoundaryAveragedBlockMain X omega x a b := by
  rw [caichInitialSmoothedMain_eq_coreTime_add_boundaryTime hX omega x hab,
    ← caichCoreAveragedBlockMain_eq_time hX hx ha hab omega,
    ← caichBoundaryAveragedBlockMain_eq_time hX omega x hx (ha.trans hab)]

end Problem520
end Erdos
