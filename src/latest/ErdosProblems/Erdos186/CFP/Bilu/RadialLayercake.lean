import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal MeasureTheory Pointwise

namespace Erdos186.CFP.Bilu.RadialLayercake

theorem lintegral_ge_of_tail_ge
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf0 : 0 ≤ f) (hf : Measurable f)
    {g : ℝ → ℝ≥0∞}
    (hg : ∀ s ∈ Set.Ioi (0 : ℝ), g s ≤ mu {x | s ≤ f x}) :
    (∫⁻ s in Set.Ioi (0 : ℝ), g s) ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂mu := by
  rw [MeasureTheory.lintegral_eq_lintegral_meas_le mu
    (ae_of_all mu hf0) hf.aemeasurable]
  exact setLIntegral_mono' measurableSet_Ioi hg

theorem scaled_set_superlevel_bound
    {m l : ℕ} {P : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → ℝ} {a t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf : ∀ y ∈ P, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      a * (1 - u) ^ l ≤ f (u • y)) :
    ENNReal.ofReal (t ^ m) * volume P ≤
      volume {x | a * (1 - t) ^ l ≤ f x} := by
  have hscale := addHaar_smul_of_nonneg volume ht0 P
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hscale
  rw [← hscale]
  apply measure_mono
  rintro x ⟨y, hy, rfl⟩
  exact hf y hy t ⟨ht0, ht1⟩

theorem beta_integral_recurrence (m l : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ (l + 1)) =
      ((l + 1 : ℕ) : ℝ) / (m + 1) *
        ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ l := by
  let u : ℝ → ℝ := fun x ↦ (1 - x) ^ (l + 1)
  let u' : ℝ → ℝ := fun x ↦ -((l + 1 : ℕ) : ℝ) * (1 - x) ^ l
  let v : ℝ → ℝ := fun x ↦ x ^ (m + 1) / ((m + 1 : ℕ) : ℝ)
  let v' : ℝ → ℝ := fun x ↦ x ^ m
  have hu : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    convert ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).pow (l + 1) using 1
    all_goals first | rfl | (simp [u', Nat.cast_add]; ring)
  have hv : ∀ x : ℝ, HasDerivAt v (v' x) x := by
    intro x
    convert ((hasDerivAt_id x).pow (m + 1)).div_const (((m + 1 : ℕ) : ℝ)) using 1
    all_goals first | rfl | (simp [v']; field_simp)
  have hu_int : IntervalIntegrable u' volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [u']
    fun_prop
  have hv_int : IntervalIntegrable v' volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [v']
    fun_prop
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hu x) (fun x _ ↦ hv x) hu_int hv_int
  have hint :
      (∫ x in (0 : ℝ)..1, u' x * v x) =
        (-((l + 1 : ℕ) : ℝ) / (m + 1)) *
          ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ l := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [u', v]
    push_cast
    field_simp
  calc
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ (l + 1)) =
        ∫ x in (0 : ℝ)..1, u x * v' x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [u, v']
      ring
    _ = u 1 * v 1 - u 0 * v 0 -
        ∫ x in (0 : ℝ)..1, u' x * v x := H
    _ = ((l + 1 : ℕ) : ℝ) / (m + 1) *
        ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ l := by
      rw [hint]
      simp [u, v]
      ring

theorem beta_integral_choose (m l : ℕ) :
    (((l + 1 : ℕ) : ℝ) * ((m + l + 1).choose (l + 1) : ℕ) : ℝ) *
        (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ l) = 1 := by
  induction l generalizing m with
  | zero =>
      rw [show (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ 0) =
          ∫ x in (0 : ℝ)..1, x ^ m by simp]
      rw [integral_pow]
      simp
      field_simp
  | succ l ih =>
      have hchoose_nat :
          (l + 2) * (m + l + 2).choose (l + 2) =
            (m + 1) * (m + l + 2).choose (l + 1) := by
        calc
          (l + 2) * (m + l + 2).choose (l + 2) =
              (m + l + 2) * (m + l + 1).choose (l + 1) := by
            rw [mul_comm]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Nat.add_one_mul_choose_eq (m + l + 1) (l + 1)).symm
          _ = (m + 1) * (m + l + 2).choose (l + 1) := by
            rw [mul_comm (m + l + 2), Nat.choose_mul_succ_eq]
            rw [show m + l + 2 - (l + 1) = m + 1 by omega]
            ring
      have hchoose_real :
          (((l + 2) * (m + l + 2).choose (l + 2) : ℕ) : ℝ) =
            (((m + 1) * (m + l + 2).choose (l + 1) : ℕ) : ℝ) := by
        exact_mod_cast hchoose_nat
      rw [beta_integral_recurrence m l]
      have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      calc
        (((l + 2 : ℕ) : ℝ) * ((m + l + 2).choose (l + 2) : ℕ) : ℝ) *
            (((l + 1 : ℕ) : ℝ) / (m + 1) *
              ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ l) =
            (((l + 1 : ℕ) : ℝ) * ((m + l + 2).choose (l + 1) : ℕ) : ℝ) *
              ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ l := by
          norm_cast at hchoose_real
          rw [← Nat.cast_mul, hchoose_real, Nat.cast_mul]
          push_cast
          field_simp
        _ = 1 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (m + 1)

theorem beta_integral_symm (m l : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ l) =
      ∫ x in (0 : ℝ)..1, x ^ l * (1 - x) ^ m := by
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := fun x : ℝ ↦ x ^ m * (1 - x) ^ l)
    (a := (0 : ℝ)) (b := 1) (c := (-1 : ℝ)) (by norm_num) (1 : ℝ)
  rw [show (∫ x in (0 : ℝ)..1, x ^ l * (1 - x) ^ m) =
      ∫ x in (0 : ℝ)..1, ((-1 : ℝ) * x + 1) ^ m *
        (1 - ((-1 : ℝ) * x + 1)) ^ l by
    apply intervalIntegral.integral_congr
    intro x hx
    ring]
  rw [hchange]
  rw [intervalIntegral.integral_symm]
  simp

theorem beta_integral_scaled_choose (m l : ℕ) {a : ℝ} (ha : 0 < a) :
    (((l + 1 : ℕ) : ℝ) * ((m + l + 1).choose (l + 1) : ℕ) : ℝ) *
        (∫ s in (0 : ℝ)..a, (1 - s / a) ^ m * s ^ l) = a ^ (l + 1) := by
  let F : ℝ → ℝ := fun s ↦ (1 - s / a) ^ m * s ^ l
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := F) (a := (0 : ℝ)) (b := 1) (c := a) ha.ne' (0 : ℝ)
  simp only [add_zero, mul_zero, mul_one, smul_eq_mul] at hchange
  have hsolve : (∫ s in (0 : ℝ)..a, F s) =
      a * ∫ x in (0 : ℝ)..1, F (a * x) := by
    calc
      (∫ s in (0 : ℝ)..a, F s) =
          a * (a⁻¹ * ∫ s in (0 : ℝ)..a, F s) := by field_simp
      _ = a * ∫ x in (0 : ℝ)..1, F (a * x) :=
        congrArg (fun z : ℝ ↦ a * z) hchange.symm
  rw [show (∫ s in (0 : ℝ)..a, (1 - s / a) ^ m * s ^ l) =
      ∫ s in (0 : ℝ)..a, F s from rfl, hsolve]
  have hunit : (∫ x in (0 : ℝ)..1, F (a * x)) =
      a ^ l * ∫ x in (0 : ℝ)..1, x ^ l * (1 - x) ^ m := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [F]
    field_simp
    ring
  rw [hunit, ← beta_integral_symm m l]
  have hbeta := beta_integral_choose m l
  calc
    (((l + 1 : ℕ) : ℝ) * ((m + l + 1).choose (l + 1) : ℕ) : ℝ) *
        (a * (a ^ l * ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ l)) =
        a ^ (l + 1) *
          ((((l + 1 : ℕ) : ℝ) * ((m + l + 1).choose (l + 1) : ℕ) : ℝ) *
            ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ l) := by
      rw [pow_succ']
      ring
    _ = a ^ (l + 1) := by rw [hbeta, mul_one]

theorem lintegral_beta_scaled_choose (m l : ℕ) {a : ℝ} (ha : 0 < a) :
    (l + 1 : ℝ≥0∞) * ((m + l + 1).choose (l + 1) : ℝ≥0∞) *
        (∫⁻ s in Set.Ioo (0 : ℝ) a,
          ENNReal.ofReal ((1 - s / a) ^ m * s ^ l)) =
      ENNReal.ofReal (a ^ (l + 1)) := by
  let F : ℝ → ℝ := fun s ↦ (1 - s / a) ^ m * s ^ l
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFintIoc : Integrable F (volume.restrict (Set.Ioc (0 : ℝ) a)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (hFcont.intervalIntegrable 0 a)
  have hFintIoo : Integrable F (volume.restrict (Set.Ioo (0 : ℝ) a)) := by
    rwa [restrict_Ioo_eq_restrict_Ioc]
  have hFnn : (fun _ : ℝ ↦ (0 : ℝ))
      ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) a)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg
      (pow_nonneg (sub_nonneg.mpr ((div_le_one ha).2 hs.2.le)) m)
      (pow_nonneg hs.1.le l)
  have hlin :
      (∫⁻ s in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (F s)) =
        ENNReal.ofReal (∫ s in (0 : ℝ)..a, F s) := by
    calc
      (∫⁻ s in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (F s)) =
          ENNReal.ofReal (∫ s in Set.Ioo (0 : ℝ) a, F s) := by
        exact (ofReal_integral_eq_lintegral_ofReal hFintIoo hFnn).symm
      _ = ENNReal.ofReal (∫ s in (0 : ℝ)..a, F s) := by
        rw [intervalIntegral.integral_of_le ha.le]
        congr 2
        exact restrict_Ioo_eq_restrict_Ioc
  change (l + 1 : ℝ≥0∞) * ((m + l + 1).choose (l + 1) : ℝ≥0∞) *
      (∫⁻ s in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (F s)) = _
  rw [hlin]
  have hlcast : (l + 1 : ℝ≥0∞) = ENNReal.ofReal (((l + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (Nat.cast_nonneg l) zero_le_one]
    norm_num
  have hccast : ((m + l + 1).choose (l + 1) : ℝ≥0∞) =
      ENNReal.ofReal ((((m + l + 1).choose (l + 1) : ℕ) : ℝ)) := by
    norm_num
  rw [hlcast, hccast]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [beta_integral_scaled_choose m l ha]

theorem radial_rpow_lower_bound
    {m L : ℕ} (hL : 0 < L)
    {P : Set (EuclideanSpace ℝ (Fin m))}
    {q : EuclideanSpace ℝ (Fin m) → ℝ} {a : ℝ} (ha : 0 < a)
    (hq0 : 0 ≤ q) (hqmeas : Measurable q)
    (hrad : ∀ y ∈ P, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      a * (1 - t) ≤ q (t • y)) :
    ENNReal.ofReal (a ^ L) * volume P ≤
      (Nat.choose (m + L) L : ℝ≥0∞) *
        ∫⁻ x, ENNReal.ofReal (q x ^ (L : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  have hp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hlayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul
    volume (ae_of_all volume hq0) hqmeas.aemeasurable hp
  let tail : ℝ → ℝ≥0∞ := fun s ↦ volume {x | s ≤ q x}
  let profile : ℝ → ℝ≥0∞ := fun s ↦
    ENNReal.ofReal ((1 - s / a) ^ m * s ^ k)
  have hprofile : Measurable profile := by
    dsimp only [profile]
    fun_prop
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) a,
      profile s * volume P ≤
        tail s * ENNReal.ofReal (s ^ (((k + 1 : ℕ) : ℝ) - 1)) := by
    intro s hs
    let t : ℝ := 1 - s / a
    have ht0 : 0 ≤ t := sub_nonneg.mpr ((div_le_one ha).2 hs.2.le)
    have ht1 : t ≤ 1 := sub_le_self _ (div_nonneg hs.1.le ha.le)
    have hscale0 := scaled_set_superlevel_bound (m := m) (l := 1)
      (P := P) (f := q) (a := a) (t := t) ht0 ht1 (by
        intro y hy u hu
        simpa using hrad y hy u hu)
    have hthreshold : a * (1 - t) = s := by
      dsimp only [t]
      field_simp
      ring
    have hscale : ENNReal.ofReal (t ^ m) * volume P ≤ tail s := by
      simpa [hthreshold, tail] using hscale0
    have hs_pow : s ^ (((k + 1 : ℕ) : ℝ) - 1) = s ^ k := by
      rw [show (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) by norm_num]
      exact Real.rpow_natCast s k
    calc
      profile s * volume P =
          (ENNReal.ofReal (t ^ m) * volume P) * ENNReal.ofReal (s ^ k) := by
        dsimp only [profile, t]
        rw [ENNReal.ofReal_mul (pow_nonneg ht0 m)]
        ac_rfl
      _ ≤ tail s * ENNReal.ofReal (s ^ k) := by
        simpa [mul_comm] using
          (mul_left_mono (a := ENNReal.ofReal (s ^ k)) hscale)
      _ = tail s * ENNReal.ofReal (s ^ (((k + 1 : ℕ) : ℝ) - 1)) := by
        rw [hs_pow]
  let J : ℝ≥0∞ := ∫⁻ s in Set.Ioo (0 : ℝ) a, profile s
  let T : ℝ≥0∞ := ∫⁻ s in Set.Ioi (0 : ℝ),
    tail s * ENNReal.ofReal (s ^ (((k + 1 : ℕ) : ℝ) - 1))
  have hJT : J * volume P ≤ T := by
    have hlocal :
        (∫⁻ s in Set.Ioo (0 : ℝ) a, profile s * volume P) ≤
          ∫⁻ s in Set.Ioo (0 : ℝ) a,
            tail s * ENNReal.ofReal (s ^ (((k + 1 : ℕ) : ℝ) - 1)) :=
      setLIntegral_mono' measurableSet_Ioo hpoint
    have hset :
        (∫⁻ s in Set.Ioo (0 : ℝ) a,
            tail s * ENNReal.ofReal (s ^ (((k + 1 : ℕ) : ℝ) - 1))) ≤ T := by
      exact lintegral_mono_set Set.Ioo_subset_Ioi_self
    rw [show J * volume P =
        ∫⁻ s in Set.Ioo (0 : ℝ) a, profile s * volume P by
      dsimp only [J]
      exact (lintegral_mul_const'' (volume P) hprofile.aemeasurable.restrict).symm]
    exact hlocal.trans hset
  have hbeta :
      (k + 1 : ℝ≥0∞) * ((m + k + 1).choose (k + 1) : ℝ≥0∞) * J =
        ENNReal.ofReal (a ^ (k + 1)) := by
    simpa only [J, profile] using lintegral_beta_scaled_choose m k ha
  have hlayer' :
      (∫⁻ x, ENNReal.ofReal (q x ^ (((k + 1 : ℕ) : ℝ)))) =
        (k + 1 : ℝ≥0∞) * T := by
    have hkcast : ENNReal.ofReal (((k + 1 : ℕ) : ℝ)) = (k + 1 : ℝ≥0∞) := by
      rw [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one]
      norm_num
    simpa only [tail, T, hkcast] using hlayer
  calc
    ENNReal.ofReal (a ^ (k + 1)) * volume P =
        ((k + 1 : ℝ≥0∞) * ((m + k + 1).choose (k + 1) : ℝ≥0∞) * J) *
          volume P := by rw [hbeta]
    _ = (k + 1 : ℝ≥0∞) * ((m + k + 1).choose (k + 1) : ℝ≥0∞) *
          (J * volume P) := by ac_rfl
    _ ≤ (k + 1 : ℝ≥0∞) * ((m + k + 1).choose (k + 1) : ℝ≥0∞) * T := by
      simpa [mul_comm] using
        (mul_left_mono (a :=
          (k + 1 : ℝ≥0∞) * ((m + k + 1).choose (k + 1) : ℝ≥0∞)) hJT)
    _ = ((m + (k + 1)).choose (k + 1) : ℝ≥0∞) *
          ((k + 1 : ℝ≥0∞) * T) := by
      simp only [Nat.add_assoc]
      ac_rfl
    _ = ((m + (k + 1)).choose (k + 1) : ℝ≥0∞) *
          (∫⁻ x, ENNReal.ofReal (q x ^ (((k + 1 : ℕ) : ℝ)))) := by
      rw [hlayer']

#print axioms radial_rpow_lower_bound

end Erdos186.CFP.Bilu.RadialLayercake
