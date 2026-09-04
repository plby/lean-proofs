/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1195.
https://www.erdosproblems.com/forum/thread/1195

Informal authors:
- Boon Suan Ho
- GPT-5.4 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1195.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 1195.
https://www.erdosproblems.com/1195

Informal authors:
- Boon Suan Ho
- GPT-5.4 Pro

Formal author:
- OpenAI Codex

The accompanying detailed proof and Leanization notes are in `tex/1195.tex`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.NumberTheory.WellApproximable
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 1195

For a measurable set `S ⊆ (0, ∞)`, put
`A_S(x) = volume (S ∩ (0, x))`.  We prove the sharp growth criterion: a
nonnegative nondecreasing function `F`, tending to infinity, is eventually
bounded above by `A_S` for an infinite-measure set with no integral quotient
between distinct points if and only if `F(x) / x^2` is integrable on
`[1, ∞)`.

The construction uses logarithmic combs in successive multiplicative annuli.
At every stage, simultaneous recurrence aligns the finitely many relevant
integer translations.  All future conflicts are then removed with a summable
measure loss.
-/

namespace Erdos1195

open Filter MeasureTheory Set
open scoped ENNReal Topology Function

/-- The real-valued Lebesgue counting function of a set on `(0,x)`. -/
noncomputable def countingFunction (S : Set ℝ) (x : ℝ) : ℝ :=
  (volume (S ∩ Ioo 0 x)).toReal

/-- No quotient of two distinct points of `S` is an integer. -/
def IntegerRatioFree (S : Set ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ∀ z : ℤ, x / y ≠ (z : ℝ)

/-- The ordered positive-natural form of the forbidden-ratio condition. -/
def PositiveNatRatioFree (S : Set ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x < y →
    ∀ n : ℕ, 2 ≤ n → y ≠ (n : ℝ) * x

lemma countingFunction_nonneg (S : Set ℝ) (x : ℝ) :
    0 ≤ countingFunction S x := by
  exact ENNReal.toReal_nonneg

lemma countingFunction_mono (S : Set ℝ) : Monotone (countingFunction S) := by
  intro x y hxy
  unfold countingFunction
  apply ENNReal.toReal_mono
  · exact MeasureTheory.measure_ne_top_of_subset inter_subset_right <| by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
  · exact measure_mono (inter_subset_inter_right _ (Ioo_subset_Ioo_right hxy))

lemma integerRatioFree_iff_positiveNatRatioFree {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    IntegerRatioFree S ↔ PositiveNatRatioFree S := by
  constructor
  · intro h x hx y hy hxy n hn hEq
    have hx0 : 0 < x := hS hx
    have hy0 : 0 < y := hS hy
    have hxy_ne : y ≠ x := ne_of_gt hxy
    have hdiv : y / x = (n : ℝ) := by
      rw [hEq]
      field_simp
    exact h hy hx hxy_ne n hdiv
  · intro h x hx y hy hxy z hz
    have hx0 : 0 < x := hS hx
    have hy0 : 0 < y := hS hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · have hzpos : 0 < z := by
        have : 0 < (z : ℝ) := hz ▸ div_pos hx0 hy0
        exact_mod_cast this
      have hz1 : (1 : ℤ) ≤ z := by omega
      have hz1' : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
      have hlt1 : x / y < 1 := (div_lt_one hy0).2 hlt
      rw [hz] at hlt1
      linarith
    · exact hxy heq
    · have hzpos : 0 < z := by
        have : 0 < (z : ℝ) := hz ▸ div_pos hx0 hy0
        exact_mod_cast this
      have hz2 : 2 ≤ z.toNat := by
        have hz1 : (1 : ℤ) ≤ z := by omega
        have hz_ne_one : z ≠ 1 := by
          intro hzone
          have hdiv_one : x / y = 1 := by simpa [hzone] using hz
          exact hxy ((div_eq_one_iff_eq (ne_of_gt hy0)).1 hdiv_one)
        have hzInt2 : (2 : ℤ) ≤ z := by omega
        have htoNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzpos.le
        omega
      have hmul : x = (z.toNat : ℝ) * y := by
        have hyne : y ≠ 0 := ne_of_gt hy0
        apply (div_eq_iff hyne).mp
        rw [hz]
        norm_cast
        exact (Int.toNat_of_nonneg hzpos.le).symm
      exact h hy hx hgt (z.toNat) hz2 hmul

/-! ## Simultaneous recurrence on a finite torus -/

/-- A finite family of points of the unit additive circle has a common positive
multiple arbitrarily close to zero.  This is the compact-group pigeonhole
principle in the form used to choose the frequencies of the logarithmic
combs. -/
lemma exists_simultaneous_nsmul_dist_le {ι : Type*} [Finite ι]
    (ξ : ι → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ ∀ i, dist (q • ξ i) 0 ≤ δ := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let μ : Measure (ι → UnitAddCircle) := volume
  let B : Set (ι → UnitAddCircle) := Metric.closedBall 0 (δ / 2)
  have hB : 0 < μ B := by
    exact Metric.measure_closedBall_pos μ 0 (half_pos hδ)
  obtain ⟨n, hn, hmass'⟩ :=
    ENNReal.exists_nat_pos_mul_gt hB.ne' (measure_ne_top μ univ)
  have hmass : μ univ ≤ (n + 1) • μ B := by
    calc
      μ univ ≤ (n : ℕ) * μ B := hmass'.le
      _ ≤ (n + 1 : ℕ) * μ B := by
        have hnle : (n : ℝ≥0∞) ≤ (n + 1 : ℕ) := by
          exact_mod_cast Nat.le_succ n
        exact mul_le_mul_of_nonneg_right hnle bot_le
      _ = (n + 1) • μ B := by simp [nsmul_eq_mul]
  obtain ⟨q, hq, hnorm⟩ :=
    NormedAddCommGroup.exists_norm_nsmul_le (μ := μ) ξ hn δ hmass
  refine ⟨q, hq.1, fun i => ?_⟩
  have hi : ‖(q • ξ) i‖₊ ≤ ‖q • ξ‖₊ := by
    rw [Pi.nnnorm_def (q • ξ)]
    exact Finset.le_sup (s := Finset.univ) (f := fun k => ‖(q • ξ) k‖₊)
      (Finset.mem_univ i)
  calc
    dist (q • ξ i) 0 = ‖q • ξ i‖ := by simp only [dist_zero_right]
    _ = ‖(q • ξ) i‖ := by simp
    _ ≤ ‖q • ξ‖ := by exact_mod_cast hi
    _ ≤ δ := hnorm

/-! ## Dyadic logarithmic combs -/

/-- The exponential parametrization whose unit intervals are dyadic annuli. -/
noncomputable def dyadicExp (t : ℝ) : ℝ := Real.exp (Real.log 2 * t)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma dyadicExp_pos (t : ℝ) : 0 < dyadicExp t := Real.exp_pos _

lemma dyadicExp_strictMono : StrictMono dyadicExp := by
  intro s t hst
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hst log_two_pos)

@[simp] lemma dyadicExp_nat (n : ℕ) : dyadicExp n = (2 : ℝ) ^ n := by
  rw [dyadicExp, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The half-width `1/(4d)` used for a comb.  The denominator form makes all
tooth endpoints land on a later grid once that grid is a multiple of `4d`. -/
noncomputable def combWidth (d : ℕ) : ℝ := 1 / (4 * d : ℝ)

lemma combWidth_pos {d : ℕ} (hd : 0 < d) : 0 < combWidth d := by
  unfold combWidth
  positivity

lemma combWidth_le_quarter {d : ℕ} (hd : 0 < d) : combWidth d ≤ 1 / 4 := by
  unfold combWidth
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d) (by norm_num : (0 : ℝ) < 4)).2
  nlinarith

/-- One open tooth in the `j`-th dyadic annulus. -/
noncomputable def logTooth (j q d r : ℕ) : Set ℝ :=
  Ioo
    (dyadicExp (j + ((r : ℝ) + 1 / 2 - combWidth d) / q))
    (dyadicExp (j + ((r : ℝ) + 1 / 2 + combWidth d) / q))

/-- A logarithmic comb with `q` teeth in the `j`-th dyadic annulus. -/
noncomputable def logComb (j q d : ℕ) : Set ℝ :=
  ⋃ r : Fin q, logTooth j q d r

lemma measurableSet_logTooth (j q d r : ℕ) : MeasurableSet (logTooth j q d r) :=
  measurableSet_Ioo

lemma measurableSet_logComb (j q d : ℕ) : MeasurableSet (logComb j q d) := by
  exact MeasurableSet.iUnion fun r => measurableSet_logTooth j q d r

lemma logTooth_subset_dyadic_annulus {j q d r : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hr : r < q) :
    logTooth j q d r ⊆ Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) := by
  intro x hx
  rw [logTooth, mem_Ioo] at hx
  rw [← dyadicExp_nat j, ← dyadicExp_nat (j + 1), mem_Ioo]
  constructor
  · exact (dyadicExp_strictMono <| by
      have hw := combWidth_le_quarter hd
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have hr0 : (0 : ℝ) ≤ r := by positivity
      apply lt_add_of_pos_right
      exact div_pos (by linarith) hq0).trans hx.1
  · exact hx.2.trans (dyadicExp_strictMono <| by
      have hw := combWidth_le_quarter hd
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have hrq : (r : ℝ) + 1 ≤ q := by exact_mod_cast hr
      rw [Nat.cast_add, Nat.cast_one]
      apply (add_lt_add_iff_left (j : ℝ)).2
      apply (div_lt_one hq0).2
      linarith)

lemma logComb_subset_dyadic_annulus {j q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    logComb j q d ⊆ Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) := by
  intro x hx
  rw [logComb, mem_iUnion] at hx
  obtain ⟨r, hr⟩ := hx
  exact logTooth_subset_dyadic_annulus hq hd r.isLt hr

lemma pairwise_disjoint_logTooth {j q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    ∀ ⦃r s : Fin q⦄, r ≠ s →
      Disjoint (logTooth j q d r) (logTooth j q d s) := by
  have aux : ∀ {r s : Fin q}, r < s →
      Disjoint (logTooth j q d r) (logTooth j q d s) := by
    intro r s hrs'
    rw [Set.disjoint_left]
    intro x hxr hxs
    rw [logTooth, mem_Ioo] at hxr hxs
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hrsReal : (r : ℝ) + 1 ≤ s := by exact_mod_cast hrs'
    have hw := combWidth_le_quarter hd
    have hends :
        (j : ℝ) + ((r : ℝ) + 1 / 2 + combWidth d) / q <
          (j : ℝ) + ((s : ℝ) + 1 / 2 - combWidth d) / q := by
      apply (add_lt_add_iff_left (j : ℝ)).2
      apply (div_lt_div_iff_of_pos_right hq0).2
      linarith
    have := dyadicExp_strictMono hends
    linarith
  intro r s hrs
  rcases lt_or_gt_of_ne hrs with hrs' | hrs'
  · exact aux hrs'
  · exact (aux hrs').symm

lemma measureReal_logComb_eq_sum {j q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    volume.real (logComb j q d) =
      ∑ r : Fin q, volume.real (logTooth j q d r) := by
  rw [logComb]
  exact measureReal_iUnion_fintype (pairwise_disjoint_logTooth hq hd)
    (fun r => measurableSet_logTooth j q d r) (fun r => by
      unfold logTooth
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)

lemma exp_mul_sub_exp_mul_lower {c u v : ℝ} (hc : 0 ≤ c) (huv : u ≤ v) :
    Real.exp (c * u) * (c * (v - u)) ≤
      Real.exp (c * v) - Real.exp (c * u) := by
  have hcu : 0 ≤ c * (v - u) := mul_nonneg hc (sub_nonneg.2 huv)
  have hexp := Real.add_one_le_exp (c * (v - u))
  calc
    Real.exp (c * u) * (c * (v - u))
        ≤ Real.exp (c * u) * (Real.exp (c * (v - u)) - 1) := by
          gcongr
          linarith
    _ = Real.exp (c * v) - Real.exp (c * u) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring

lemma measureReal_logTooth_lower {j q d r : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (2 : ℝ) ^ j * (2 * combWidth d * Real.log 2 / q) ≤
      volume.real (logTooth j q d r) := by
  let u : ℝ := (j : ℝ) + ((r : ℝ) + 1 / 2 - combWidth d) / q
  let v : ℝ := (j : ℝ) + ((r : ℝ) + 1 / 2 + combWidth d) / q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hwpos := combWidth_pos hd
  have huv : u ≤ v := by
    dsimp [u, v]
    gcongr
    linarith
  have hju : (j : ℝ) ≤ u := by
    dsimp [u]
    apply le_add_of_nonneg_right
    apply div_nonneg
    · have hr0 : (0 : ℝ) ≤ r := by positivity
      have hw := combWidth_le_quarter hd
      linarith
    · exact hq0.le
  have hexpju : (2 : ℝ) ^ j ≤ Real.exp (Real.log 2 * u) := by
    rw [← dyadicExp_nat j]
    exact (dyadicExp_strictMono.monotone hju)
  have hbasic := exp_mul_sub_exp_mul_lower log_two_pos.le huv
  have hvu : v - u = 2 * combWidth d / q := by
    dsimp [u, v]
    field_simp
    ring
  rw [logTooth, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal]
  · dsimp [logTooth, dyadicExp]
    change (2 : ℝ) ^ j * (2 * combWidth d * Real.log 2 / q) ≤
      Real.exp (Real.log 2 * v) - Real.exp (Real.log 2 * u)
    calc
      (2 : ℝ) ^ j * (2 * combWidth d * Real.log 2 / q)
          = (2 : ℝ) ^ j * (Real.log 2 * (v - u)) := by rw [hvu]; ring
      _
          ≤ Real.exp (Real.log 2 * u) * (Real.log 2 * (v - u)) := by
            gcongr
      _ ≤ Real.exp (Real.log 2 * v) - Real.exp (Real.log 2 * u) := hbasic
  · exact sub_nonneg.2 (dyadicExp_strictMono.monotone huv)

lemma measureReal_logComb_lower {j q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (2 : ℝ) ^ j * (2 * combWidth d * Real.log 2) ≤
      volume.real (logComb j q d) := by
  rw [measureReal_logComb_eq_sum hq hd]
  calc
    (2 : ℝ) ^ j * (2 * combWidth d * Real.log 2)
        = ∑ _r : Fin q,
            ((2 : ℝ) ^ j * (2 * combWidth d * Real.log 2 / q)) := by
          simp [div_eq_mul_inv]
          field_simp
    _ ≤ ∑ r : Fin q, volume.real (logTooth j q d r) := by
      gcongr with r
      exact measureReal_logTooth_lower hq hd

/-- Base-two logarithmic coordinate. -/
noncomputable def logCoord (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The point on the unit circle recording the `q`-fold logarithmic phase. -/
noncomputable def logPhase (q : ℕ) (x : ℝ) : UnitAddCircle :=
  (((q : ℝ) * logCoord x : ℝ) : UnitAddCircle)

/-- The global periodic comb of points whose `q`-fold logarithmic phase is
within `a` of the middle of a cell. -/
noncomputable def globalLogComb (q : ℕ) (a : ℝ) : Set ℝ :=
  {x | dist (logPhase q x) ((1 / 2 : ℝ) : UnitAddCircle) < a}

lemma measurableSet_globalLogComb (q : ℕ) (a : ℝ) :
    MeasurableSet (globalLogComb q a) := by
  have hreal : Measurable (fun x : ℝ => (q : ℝ) * logCoord x) := by
    exact measurable_const.mul (Real.measurable_log.div_const (Real.log 2))
  have hphase : Measurable (logPhase q) :=
    (AddCircle.continuous_mk' (p := (1 : ℝ))).measurable.comp hreal
  apply measurableSet_lt
  · exact hphase.dist measurable_const
  · exact measurable_const

lemma logCoord_dyadicExp (t : ℝ) : logCoord (dyadicExp t) = t := by
  rw [logCoord, dyadicExp, Real.log_exp]
  field_simp [log_two_pos.ne']

lemma logTooth_subset_globalLogComb {j q d r : ℕ}
    (hq : 0 < q) (hd : 0 < d) :
    logTooth j q d r ⊆ globalLogComb q (combWidth d) := by
  intro x hx
  rw [logTooth, mem_Ioo] at hx
  have hx0 : 0 < x := (dyadicExp_pos _).trans hx.1
  let u : ℝ := (j : ℝ) + ((r : ℝ) + 1 / 2 - combWidth d) / q
  let v : ℝ := (j : ℝ) + ((r : ℝ) + 1 / 2 + combWidth d) / q
  have hlu : u < logCoord x := by
    have hlog : Real.log (dyadicExp u) < Real.log x :=
      (Real.log_lt_log_iff (dyadicExp_pos u) hx0).2 hx.1
    unfold logCoord
    apply (lt_div_iff₀ log_two_pos).2
    simpa [dyadicExp, mul_comm] using hlog
  have huv : logCoord x < v := by
    have hlog : Real.log x < Real.log (dyadicExp v) :=
      (Real.log_lt_log_iff hx0 (dyadicExp_pos v)).2 hx.2
    unfold logCoord
    apply (div_lt_iff₀ log_two_pos).2
    simpa [dyadicExp, mul_comm] using hlog
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  let z : ℕ := q * j + r
  have hnear :
      |(q : ℝ) * logCoord x - 1 / 2 - z| < combWidth d := by
    rw [abs_lt]
    dsimp [u, v, z] at hlu huv ⊢
    field_simp at hlu huv
    constructor <;> push_cast <;> nlinarith
  have hz : (((z : ℝ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨(z : ℤ), by simp⟩
  have hcoe :
      ((((q : ℝ) * logCoord x - 1 / 2 : ℝ)) : UnitAddCircle) =
        ((((q : ℝ) * logCoord x - 1 / 2 - z : ℝ)) : UnitAddCircle) := by
    calc
      ((((q : ℝ) * logCoord x - 1 / 2 : ℝ)) : UnitAddCircle) =
          ((((q : ℝ) * logCoord x - 1 / 2 : ℝ)) : UnitAddCircle) -
            (((z : ℝ) : UnitAddCircle)) := by rw [hz, sub_zero]
      _ = ((((q : ℝ) * logCoord x - 1 / 2 - z : ℝ)) : UnitAddCircle) := rfl
  rw [globalLogComb, mem_ofPred_eq, logPhase, dist_eq_norm, ← AddCircle.coe_sub]
  change ‖((((q : ℝ) * logCoord x - 1 / 2 : ℝ)) : UnitAddCircle)‖ < combWidth d
  rw [hcoe]
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2]
  · exact hnear
  · exact hnear.le.trans (combWidth_le_quarter hd |>.trans <| by norm_num)

lemma logComb_subset_globalLogComb {j q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    logComb j q d ⊆ globalLogComb q (combWidth d) := by
  intro x hx
  rw [logComb, mem_iUnion] at hx
  obtain ⟨r, hr⟩ := hx
  exact logTooth_subset_globalLogComb hq hd hr

lemma logCoord_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logCoord (x * y) = logCoord x + logCoord y := by
  simp only [logCoord, Real.log_mul hx hy]
  ring

lemma logPhase_mul {q : ℕ} {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logPhase q (x * y) = logPhase q x +
      (((q : ℝ) * logCoord y : ℝ) : UnitAddCircle) := by
  unfold logPhase
  rw [logCoord_mul hx hy, ← AddCircle.coe_add]
  congr 1
  ring

lemma mem_globalLogComb_of_mul_mem {q : ℕ} {a x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hrec : dist ((((q : ℝ) * logCoord y : ℝ)) : UnitAddCircle) 0 ≤ a)
    (hxy : x * y ∈ globalLogComb q a) :
    x ∈ globalLogComb q (2 * a) := by
  let c : UnitAddCircle := ((1 / 2 : ℝ) : UnitAddCircle)
  let s : UnitAddCircle := (((q : ℝ) * logCoord y : ℝ) : UnitAddCircle)
  have hphase : logPhase q (x * y) = logPhase q x + s := logPhase_mul hx hy
  have hmem : dist (logPhase q (x * y)) c < a := hxy
  rw [globalLogComb, mem_ofPred_eq]
  change dist (logPhase q x) c < 2 * a
  calc
    dist (logPhase q x) c = dist (logPhase q x + s) (c + s) := by
      exact (dist_add_right (logPhase q x) c s).symm
    _ ≤ dist (logPhase q x + s) c + dist c (c + s) := dist_triangle _ _ _
    _ = dist (logPhase q (x * y)) c + dist s 0 := by
      rw [← hphase]
      simp [dist_comm]
    _ < a + a := add_lt_add_of_lt_of_le hmem hrec
    _ = 2 * a := by ring

/-- Simultaneous recurrence can be imposed while requiring the new frequency
to be a multiple of a prescribed positive integer. -/
lemma exists_multiple_log_recurrence (D N : ℕ) {a : ℝ}
    (hD : 0 < D) (ha : 0 < a) :
    ∃ q : ℕ, 0 < q ∧ D ∣ q ∧
      ∀ n : ℕ, n ≤ N →
        dist (q • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤ a := by
  let ξ : Fin (N + 1) → UnitAddCircle := fun n =>
    D • ((logCoord n : ℝ) : UnitAddCircle)
  obtain ⟨r, hr, hrec⟩ := exists_simultaneous_nsmul_dist_le ξ ha
  refine ⟨D * r, Nat.mul_pos hD hr, ⟨r, rfl⟩, fun n hn => ?_⟩
  have hn' : n < N + 1 := Nat.lt_succ_of_le hn
  simpa [ξ, mul_nsmul] using hrec ⟨n, hn'⟩

/-! ### Quantitative grid estimates -/

/-- A full cell of the frequency-`q` logarithmic grid. -/
noncomputable def logCell (q k : ℕ) : Set ℝ :=
  Ioo (dyadicExp ((k : ℝ) / q)) (dyadicExp (((k : ℝ) + 1) / q))

/-- The central part of a logarithmic grid cell. -/
noncomputable def centralLogCell (q k : ℕ) (a : ℝ) : Set ℝ :=
  Ioo (dyadicExp (((k : ℝ) + 1 / 2 - a) / q))
    (dyadicExp (((k : ℝ) + 1 / 2 + a) / q))

lemma measurableSet_logCell (q k : ℕ) : MeasurableSet (logCell q k) := measurableSet_Ioo

lemma measurableSet_centralLogCell (q k : ℕ) (a : ℝ) :
    MeasurableSet (centralLogCell q k a) := measurableSet_Ioo

lemma exp_mul_sub_exp_mul_upper {c u v : ℝ} (hc : 0 ≤ c) (huv : u ≤ v) :
    Real.exp (c * v) - Real.exp (c * u) ≤
      Real.exp (c * v) * (c * (v - u)) := by
  have huv' : c * u ≤ c * v := mul_le_mul_of_nonneg_left huv hc
  have h := Real.add_one_le_exp (c * (u - v))
  have heq : Real.exp (c * v) * Real.exp (c * (u - v)) = Real.exp (c * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_pos (c * v)).le]

lemma measureReal_centralLogCell_le {q k : ℕ} {a : ℝ}
    (hq : 0 < q) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) :
    volume.real (centralLogCell q k a) ≤
      4 * a * volume.real (logCell q k) := by
  let z : ℝ := (k : ℝ) / q
  let u : ℝ := ((k : ℝ) + 1 / 2 - a) / q
  let v : ℝ := ((k : ℝ) + 1 / 2 + a) / q
  let w : ℝ := ((k : ℝ) + 1) / q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have huz : z ≤ u := by
    dsimp [z, u]
    apply (div_le_div_iff_of_pos_right hq0).2
    linarith
  have huv : u ≤ v := by
    dsimp [u, v]
    apply (div_le_div_iff_of_pos_right hq0).2
    linarith
  have hvw : v ≤ w := by
    dsimp [v, w]
    apply (div_le_div_iff_of_pos_right hq0).2
    linarith
  have hzw : z ≤ w := huz.trans (huv.trans hvw)
  have hupper := exp_mul_sub_exp_mul_upper log_two_pos.le huv
  have hlower := exp_mul_sub_exp_mul_lower log_two_pos.le hzw
  have hvz : Real.exp (Real.log 2 * v) ≤ 2 * Real.exp (Real.log 2 * z) := by
    calc
      Real.exp (Real.log 2 * v) ≤ Real.exp (Real.log 2 * w) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvw log_two_pos.le)
      _ = Real.exp (Real.log 2 * z) * Real.exp (Real.log 2 * (w - z)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (Real.log 2 * z) * Real.exp (Real.log 2) := by
        gcongr
        calc
          Real.log 2 * (w - z) ≤ Real.log 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ log_two_pos.le
            dsimp [z, w]
            field_simp
            norm_num
            exact_mod_cast hq
          _ = Real.log 2 := by ring
      _ = 2 * Real.exp (Real.log 2 * z) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
  have hvu : v - u = 2 * a / q := by
    dsimp [u, v]
    field_simp
    ring
  have hwz : w - z = 1 / q := by
    dsimp [z, w]
    field_simp
    ring
  rw [centralLogCell, logCell, Measure.real, Measure.real, Real.volume_Ioo,
    Real.volume_Ioo, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · dsimp [dyadicExp]
    change Real.exp (Real.log 2 * v) - Real.exp (Real.log 2 * u) ≤
      4 * a * (Real.exp (Real.log 2 * w) - Real.exp (Real.log 2 * z))
    rw [hvu] at hupper
    rw [hwz] at hlower
    have hlog : 0 < Real.log 2 := log_two_pos
    have hzexp : 0 < Real.exp (Real.log 2 * z) := Real.exp_pos _
    have hqreal : 0 < (q : ℝ) := hq0
    calc
      Real.exp (Real.log 2 * v) - Real.exp (Real.log 2 * u)
          ≤ Real.exp (Real.log 2 * v) * (Real.log 2 * (2 * a / q)) := hupper
      _ ≤ (2 * Real.exp (Real.log 2 * z)) * (Real.log 2 * (2 * a / q)) := by
        gcongr
      _ = 4 * a * (Real.exp (Real.log 2 * z) * (Real.log 2 * (1 / q))) := by
        field_simp
        ring
      _ ≤ 4 * a * (Real.exp (Real.log 2 * w) - Real.exp (Real.log 2 * z)) := by
        gcongr
  · exact sub_nonneg.2 (dyadicExp_strictMono.monotone hzw)
  · exact sub_nonneg.2 (dyadicExp_strictMono.monotone huv)

lemma dyadicExp_logCoord {x : ℝ} (hx : 0 < x) : dyadicExp (logCoord x) = x := by
  rw [dyadicExp, logCoord]
  have hlogne := log_two_pos.ne'
  rw [mul_div_cancel₀ _ hlogne, Real.exp_log hx]

/-- A segment consisting of `L` consecutive cells starting at cell `m`. -/
noncomputable def logSegment (q m L : ℕ) : Set ℝ :=
  Ioo (dyadicExp ((m : ℝ) / q)) (dyadicExp (((m + L : ℕ) : ℝ) / q))

noncomputable def centralCells (q m L : ℕ) (a : ℝ) : Set ℝ :=
  ⋃ r : Fin L, centralLogCell q (m + r) a

lemma measurableSet_logSegment (q m L : ℕ) : MeasurableSet (logSegment q m L) :=
  measurableSet_Ioo

lemma measurableSet_centralCells (q m L : ℕ) (a : ℝ) :
    MeasurableSet (centralCells q m L a) := by
  exact MeasurableSet.iUnion fun r => measurableSet_centralLogCell q (m + r) a

lemma logSegment_inter_globalLogComb_subset {q m L : ℕ} {a : ℝ}
    (hq : 0 < q) (ha : a < 1 / 2) :
    logSegment q m L ∩ globalLogComb q a ⊆ centralCells q m L a := by
  intro x hx
  rcases hx with ⟨hxseg, hxphase⟩
  rw [logSegment, mem_Ioo] at hxseg
  have hx0 : 0 < x := (dyadicExp_pos _).trans hxseg.1
  have htm : (m : ℝ) / q < logCoord x := by
    calc
      (m : ℝ) / q = logCoord (dyadicExp ((m : ℝ) / q)) :=
        (logCoord_dyadicExp _).symm
      _ < logCoord x := by
        unfold logCoord
        apply (div_lt_div_iff_of_pos_right log_two_pos).2
        exact (Real.log_lt_log_iff (dyadicExp_pos ((m : ℝ) / q)) hx0).2 hxseg.1
  have htM : logCoord x < ((m + L : ℕ) : ℝ) / q := by
    calc
      logCoord x < logCoord (dyadicExp (((m + L : ℕ) : ℝ) / q)) := by
        unfold logCoord
        apply (div_lt_div_iff_of_pos_right log_two_pos).2
        exact (Real.log_lt_log_iff hx0
          (dyadicExp_pos (((m + L : ℕ) : ℝ) / q))).2 hxseg.2
      _ = ((m + L : ℕ) : ℝ) / q := logCoord_dyadicExp _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  let e : ℝ := (q : ℝ) * logCoord x - 1 / 2
  let z : ℤ := round e
  have hnear : |e - z| < a := by
    rw [globalLogComb, mem_ofPred_eq, logPhase, dist_eq_norm, ← AddCircle.coe_sub] at hxphase
    change ‖((e : ℝ) : UnitAddCircle)‖ < a at hxphase
    rw [AddCircle.norm_eq] at hxphase
    simpa [e, z] using hxphase
  have hzlt : (z : ℝ) < (q : ℝ) * logCoord x := by
    rw [abs_lt] at hnear
    dsimp [e] at hnear
    linarith
  have hltz : (q : ℝ) * logCoord x < (z : ℝ) + 1 := by
    rw [abs_lt] at hnear
    dsimp [e] at hnear
    linarith
  have hmz : (m : ℤ) ≤ z := by
    have hmt : (m : ℝ) < (q : ℝ) * logCoord x := by
      simpa [mul_comm] using ((div_lt_iff₀ hq0).1 htm)
    have hreal : (m : ℝ) < (z : ℝ) + 1 := hmt.trans hltz
    have hint : (m : ℤ) < z + 1 := by exact_mod_cast hreal
    omega
  have hzM : z < (m + L : ℤ) := by
    have htM' : (q : ℝ) * logCoord x < (m + L : ℕ) :=
      by simpa [mul_comm] using (lt_div_iff₀ hq0).1 htM
    exact_mod_cast hzlt.trans htM'
  have hz0 : 0 ≤ z := (Int.natCast_nonneg m).trans hmz
  let k : ℕ := z.toNat
  have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz0
  have hmk : m ≤ k := by
    have : (m : ℤ) ≤ (k : ℤ) := by simpa [hkz] using hmz
    exact_mod_cast this
  have hkM : k < m + L := by
    have : (k : ℤ) < (m + L : ℕ) := by simpa [hkz] using hzM
    exact_mod_cast this
  let r : Fin L := ⟨k - m, by omega⟩
  have hmr : m + (r : ℕ) = k := by dsimp [r]; omega
  have hmrR : (m : ℝ) + (r : ℝ) = k := by exact_mod_cast hmr
  have hkzR : (k : ℝ) = z := by exact_mod_cast hkz
  rw [centralCells, mem_iUnion]
  refine ⟨r, ?_⟩
  rw [centralLogCell, mem_Ioo]
  rw [← dyadicExp_logCoord hx0]
  rw [abs_lt] at hnear
  constructor
  · apply dyadicExp_strictMono
    push_cast
    rw [hmrR, hkzR]
    apply (div_lt_iff₀ hq0).2
    dsimp [e] at hnear
    nlinarith
  · apply dyadicExp_strictMono
    push_cast
    rw [hmrR, hkzR]
    apply (lt_div_iff₀ hq0).2
    dsimp [e] at hnear
    nlinarith

lemma volumeReal_Ioo {a b : ℝ} (hab : a ≤ b) :
    volume.real (Ioo a b) = b - a := by
  rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

lemma centralLogCell_subset_logCell {q k : ℕ} {a : ℝ}
    (hq : 0 < q) (ha : a ≤ 1 / 2) :
    centralLogCell q k a ⊆ logCell q k := by
  intro x hx
  rw [centralLogCell, mem_Ioo] at hx
  rw [logCell, mem_Ioo]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · exact (dyadicExp_strictMono.monotone (by
      apply (div_le_div_iff_of_pos_right hq0).2
      linarith)).trans_lt hx.1
  · exact hx.2.trans_le (dyadicExp_strictMono.monotone (by
      apply (div_le_div_iff_of_pos_right hq0).2
      linarith))

lemma centralCells_subset_logSegment {q m L : ℕ} {a : ℝ}
    (hq : 0 < q) (ha : a ≤ 1 / 2) :
    centralCells q m L a ⊆ logSegment q m L := by
  intro x hx
  rw [centralCells, mem_iUnion] at hx
  obtain ⟨r, hr⟩ := hx
  have hcell := centralLogCell_subset_logCell hq ha hr
  rw [logCell, mem_Ioo] at hcell
  rw [logSegment, mem_Ioo]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrsucc : (m + (r : ℕ) + 1 : ℕ) ≤ m + L := by omega
  constructor
  · exact (dyadicExp_strictMono.monotone (by
      apply (div_le_div_iff_of_pos_right hq0).2
      push_cast
      linarith)).trans_lt hcell.1
  · exact hcell.2.trans_le (dyadicExp_strictMono.monotone (by
      apply (div_le_div_iff_of_pos_right hq0).2
      exact_mod_cast hrsucc))

lemma sum_measureReal_logCell {q m L : ℕ} (hq : 0 < q) :
    (∑ r : Fin L, volume.real (logCell q (m + r))) =
      volume.real (logSegment q m L) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hcell (k : ℕ) :
      volume.real (logCell q k) =
        dyadicExp (((k : ℝ) + 1) / q) - dyadicExp ((k : ℝ) / q) := by
    rw [logCell, volumeReal_Ioo]
    exact dyadicExp_strictMono.monotone <|
      (div_le_div_iff_of_pos_right hq0).2 (by linarith)
  have hseg :
      volume.real (logSegment q m L) =
        dyadicExp (((m + L : ℕ) : ℝ) / q) - dyadicExp ((m : ℝ) / q) := by
    rw [logSegment, volumeReal_Ioo]
    exact dyadicExp_strictMono.monotone <|
      (div_le_div_iff_of_pos_right hq0).2 (by
        exact_mod_cast Nat.le_add_right m L)
  rw [hseg]
  let f : ℕ → ℝ := fun r => dyadicExp (((m + r : ℕ) : ℝ) / q)
  calc
    (∑ r : Fin L, volume.real (logCell q (m + r))) =
        ∑ r ∈ Finset.range L, volume.real (logCell q (m + r)) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro r hr
          have hrlt := Finset.mem_range.mp hr
          simp [hrlt]
    _ = ∑ r ∈ Finset.range L, (f (r + 1) - f r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hcell]
      simp only [f, Nat.cast_add, Nat.cast_one]
      congr 2
      all_goals ring
    _ = f L - f 0 := Finset.sum_range_sub f L
    _ = dyadicExp (((m + L : ℕ) : ℝ) / q) - dyadicExp ((m : ℝ) / q) := by
      simp [f]

lemma measureReal_logSegment_inter_globalLogComb_le {q m L : ℕ} {a : ℝ}
    (hq : 0 < q) (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    volume.real (logSegment q m L ∩ globalLogComb q a) ≤
      4 * a * volume.real (logSegment q m L) := by
  have hsub := logSegment_inter_globalLogComb_subset (q := q) (m := m) (L := L) hq ha
  have hcentSub := centralCells_subset_logSegment (q := q) (m := m) (L := L) hq ha.le
  have hfinite : volume (centralCells q m L a) ≠ ∞ :=
    measure_ne_top_of_subset hcentSub <| by
      rw [logSegment, Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
  calc
    volume.real (logSegment q m L ∩ globalLogComb q a)
        ≤ volume.real (centralCells q m L a) := measureReal_mono hsub hfinite
    _ ≤ ∑ r : Fin L, volume.real (centralLogCell q (m + r) a) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ r : Fin L, 4 * a * volume.real (logCell q (m + r)) := by
      gcongr with r
      exact measureReal_centralLogCell_le hq ha0 ha.le
    _ = 4 * a * volume.real (logSegment q m L) := by
      rw [← Finset.mul_sum, sum_measureReal_logCell hq]

lemma logTooth_eq_logSegment_of_dvd {j q d r Q : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q) (hdiv : 4 * d * q ∣ Q) :
    ∃ m L : ℕ, logTooth j q d r = logSegment Q m L := by
  obtain ⟨c, hc⟩ := hdiv
  have hcpos : 0 < c := by
    by_contra hc0
    have : c = 0 := Nat.eq_zero_of_not_pos hc0
    subst c
    simp at hc
    omega
  let A : ℕ := 4 * d * q * j + 4 * d * r + (2 * d - 1)
  let m : ℕ := c * A
  let L : ℕ := 2 * c
  have hdsub : 1 ≤ 2 * d := by omega
  have hlower :
      (j : ℝ) + ((r : ℝ) + 1 / 2 - combWidth d) / q = (m : ℝ) / Q := by
    dsimp [m, A]
    rw [hc]
    unfold combWidth
    push_cast [Nat.cast_sub hdsub]
    field_simp
    ring
  have hupper :
      (j : ℝ) + ((r : ℝ) + 1 / 2 + combWidth d) / q =
        ((m + L : ℕ) : ℝ) / Q := by
    dsimp [m, L, A]
    rw [hc]
    unfold combWidth
    push_cast [Nat.cast_sub hdsub]
    field_simp
    ring
  refine ⟨m, L, ?_⟩
  rw [logTooth, logSegment, hlower, hupper]

lemma measureReal_logComb_inter_globalLogComb_le {j q d Q : ℕ} {a : ℝ}
    (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q)
    (hdiv : 4 * d * q ∣ Q) (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    volume.real (logComb j q d ∩ globalLogComb Q a) ≤
      4 * a * volume.real (logComb j q d) := by
  have hinter :
      logComb j q d ∩ globalLogComb Q a =
        ⋃ r : Fin q, logTooth j q d r ∩ globalLogComb Q a := by
    ext x
    simp [logComb]
  rw [hinter]
  calc
    volume.real (⋃ r : Fin q, logTooth j q d r ∩ globalLogComb Q a)
        ≤ ∑ r : Fin q,
            volume.real (logTooth j q d r ∩ globalLogComb Q a) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ r : Fin q, 4 * a * volume.real (logTooth j q d r) := by
      gcongr with r
      obtain ⟨m, L, hr⟩ := logTooth_eq_logSegment_of_dvd hq hd hQ hdiv
      rw [hr]
      exact measureReal_logSegment_inter_globalLogComb_le hQ ha0 ha
    _ = 4 * a * volume.real (logComb j q d) := by
      rw [← Finset.mul_sum, measureReal_logComb_eq_sum hq hd]

/-! ### Infinite deletion -/

lemma measureReal_iUnion_le_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (s : ι → Set α)
    (hfinite : ∀ i, μ (s i) ≠ ∞)
    (hsum : Summable fun i => μ.real (s i)) :
    μ.real (⋃ i, s i) ≤ ∑' i, μ.real (s i) := by
  have hnonneg : ∀ i, 0 ≤ μ.real (s i) := fun _ => measureReal_nonneg
  have htsum :
      ∑' i, μ (s i) = ENNReal.ofReal (∑' i, μ.real (s i)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
    apply tsum_congr
    intro i
    exact (ofReal_measureReal (hfinite i)).symm
  have hright : ENNReal.ofReal (∑' i, μ.real (s i)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hleft : μ (⋃ i, s i) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_iUnion_le s).trans_lt (by rw [htsum]; exact hright.lt_top)
  change (μ (⋃ i, s i)).toReal ≤ ∑' i, μ.real (s i)
  rw [← ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]
  apply (ENNReal.toReal_le_toReal hleft hright).2
  rw [← htsum]
  exact measure_iUnion_le s

noncomputable def futureShadows (q d : ℕ → ℕ) (i : ℕ) : Set ℝ :=
  ⋃ j : {j : ℕ // i < j}, globalLogComb (q j) (2 * combWidth (d j))

noncomputable def trimmedComb (J : ℕ) (q d : ℕ → ℕ) (i : ℕ) : Set ℝ :=
  logComb (J + i) (q i) (d i) \ futureShadows q d i

noncomputable def constructedSet (J : ℕ) (q d : ℕ → ℕ) : Set ℝ :=
  ⋃ i, trimmedComb J q d i

lemma measurableSet_futureShadows (q d : ℕ → ℕ) (i : ℕ) :
    MeasurableSet (futureShadows q d i) := by
  exact MeasurableSet.iUnion fun j => measurableSet_globalLogComb _ _

lemma measurableSet_trimmedComb (J : ℕ) (q d : ℕ → ℕ) (i : ℕ) :
    MeasurableSet (trimmedComb J q d i) :=
  (measurableSet_logComb _ _ _).diff (measurableSet_futureShadows q d i)

lemma measurableSet_constructedSet (J : ℕ) (q d : ℕ → ℕ) :
    MeasurableSet (constructedSet J q d) := by
  exact MeasurableSet.iUnion fun i => measurableSet_trimmedComb J q d i

lemma trimmedComb_subset_logComb (J : ℕ) (q d : ℕ → ℕ) (i : ℕ) :
    trimmedComb J q d i ⊆ logComb (J + i) (q i) (d i) := sdiff_subset

lemma measureReal_trimmedComb_lower
    (J : ℕ) (q d : ℕ → ℕ)
    (hq : ∀ i, 0 < q i) (hd : ∀ i, 0 < d i)
    (halign : ∀ i j, i < j → 4 * d i * q i ∣ q j)
    (hsum : Summable fun j => combWidth (d j))
    (htotal : ∑' j, combWidth (d j) ≤ 1 / 16) (i : ℕ) :
    (1 / 2 : ℝ) * volume.real (logComb (J + i) (q i) (d i)) ≤
      volume.real (trimmedComb J q d i) := by
  let H : Set ℝ := logComb (J + i) (q i) (d i)
  let shadow : {j : ℕ // i < j} → Set ℝ := fun j =>
    H ∩ globalLogComb (q j) (2 * combWidth (d j))
  have hshadow (j : {j : ℕ // i < j}) :
      volume.real (shadow j) ≤
        8 * combWidth (d j) * volume.real H := by
    dsimp [shadow, H]
    have hwpos := combWidth_pos (hd j)
    have hwlt : 2 * combWidth (d j) < 1 / 2 := by
      have hw := combWidth_le_quarter (hd j)
      have hjwidth : combWidth (d j) ≤ ∑' k, combWidth (d k) := by
        exact hsum.le_tsum j (fun k _ => (combWidth_pos (hd k)).le)
      linarith
    have h := measureReal_logComb_inter_globalLogComb_le
      (j := J + i) (q := q i) (d := d i) (Q := q j)
      (a := 2 * combWidth (d j)) (hq i) (hd i) (hq j)
      (halign i j j.property) (mul_nonneg (by norm_num) hwpos.le) hwlt
    convert h using 1
    all_goals ring
  have hdomSum : Summable fun j : {j : ℕ // i < j} =>
      (8 * volume.real H) * combWidth (d j) := by
    have hwsub : Summable fun j : {j : ℕ // i < j} => combWidth (d j) :=
      hsum.comp_injective Subtype.coe_injective
    exact hwsub.mul_left (8 * volume.real H)
  have hshadowSum : Summable fun j => volume.real (shadow j) :=
    hdomSum.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun j => by simpa [mul_assoc, mul_left_comm, mul_comm] using hshadow j)
  have hunion :
      volume.real (H ∩ futureShadows q d i) ≤
        ∑' j : {j : ℕ // i < j}, volume.real (shadow j) := by
    have hinter : H ∩ futureShadows q d i = ⋃ j, shadow j := by
      ext x
      simp [futureShadows, shadow]
    rw [hinter]
    apply measureReal_iUnion_le_tsum volume shadow
    · intro j
      exact measure_ne_top_of_subset inter_subset_left <| by
        dsimp [H]
        exact measure_ne_top_of_subset
          (logComb_subset_dyadic_annulus (hq i) (hd i)) <| by
            rw [Real.volume_Ioo]
            exact ENNReal.ofReal_ne_top
    · exact hshadowSum
  have htsumShadow :
      (∑' j : {j : ℕ // i < j}, volume.real (shadow j)) ≤
        8 * volume.real H * ∑' j, combWidth (d j) := by
    calc
      (∑' j : {j : ℕ // i < j}, volume.real (shadow j))
          ≤ ∑' j : {j : ℕ // i < j},
              (8 * volume.real H) * combWidth (d j) := by
            apply hshadowSum.tsum_le_tsum
              (fun j => by simpa [mul_assoc, mul_left_comm, mul_comm] using hshadow j)
              hdomSum
      _ = 8 * volume.real H *
          (∑' j : {j : ℕ // i < j}, combWidth (d j)) := by
            rw [← tsum_mul_left]
      _ ≤ 8 * volume.real H * ∑' j, combWidth (d j) := by
            gcongr
            exact Summable.tsum_subtype_le (fun j => combWidth (d j))
              {j : ℕ | i < j} (fun j => (combWidth_pos (hd j)).le) hsum
  have hloss : volume.real (H ∩ futureShadows q d i) ≤
      (1 / 2 : ℝ) * volume.real H := by
    calc
      volume.real (H ∩ futureShadows q d i)
          ≤ 8 * volume.real H * ∑' j, combWidth (d j) := hunion.trans htsumShadow
      _ ≤ 8 * volume.real H * (1 / 16) := by gcongr
      _ = (1 / 2 : ℝ) * volume.real H := by ring
  have hHfinite : volume H ≠ ∞ := by
    dsimp [H]
    exact measure_ne_top_of_subset (logComb_subset_dyadic_annulus (hq i) (hd i)) <| by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
  have hsplit := measureReal_sdiff_add_inter
    (s := H) (t := futureShadows q d i) (measurableSet_futureShadows q d i) hHfinite
  dsimp [trimmedComb, H]
  dsimp [trimmedComb, H] at hsplit hloss
  linarith

lemma constructedSet_subset_Ioi (J : ℕ) (q d : ℕ → ℕ)
    (hq : ∀ i, 0 < q i) (hd : ∀ i, 0 < d i) :
    constructedSet J q d ⊆ Ioi 0 := by
  intro x hx
  rw [constructedSet, mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  have hiH := trimmedComb_subset_logComb J q d i hi
  have hiA := logComb_subset_dyadic_annulus (hq i) (hd i) hiH
  exact (by positivity : (0 : ℝ) < (2 : ℝ) ^ (J + i)).trans hiA.1

lemma positiveNatRatioFree_constructedSet
    (J : ℕ) (q d : ℕ → ℕ)
    (hq : ∀ i, 0 < q i) (hd : ∀ i, 0 < d i)
    (hrec : ∀ j (n : ℕ), n ≤ 2 ^ (j + 1) →
      dist (q j • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤ combWidth (d j)) :
    PositiveNatRatioFree (constructedSet J q d) := by
  intro x hx y hy hxy n hn hEq
  rw [constructedSet, mem_iUnion] at hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hiH := trimmedComb_subset_logComb J q d i hi
  have hjH := trimmedComb_subset_logComb J q d j hj
  have hiA := logComb_subset_dyadic_annulus (hq i) (hd i) hiH
  have hjA := logComb_subset_dyadic_annulus (hq j) (hd j) hjH
  have hij : i < j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hij
    · subst j
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hxpos : 0 < x := (by positivity : (0 : ℝ) < (2 : ℝ) ^ (J + i)).trans hiA.1
      have hpow : (2 : ℝ) ^ (J + i + 1) = 2 * (2 : ℝ) ^ (J + i) := by
        rw [pow_succ]
        ring
      rw [hEq] at hjA
      have htwoX : 2 * x ≤ (n : ℝ) * x :=
        mul_le_mul_of_nonneg_right hnreal hxpos.le
      have hnUpper : (n : ℝ) * x < 2 * (2 : ℝ) ^ (J + i) := by
        rw [← hpow]
        exact hjA.2
      have hlowerX : 2 * (2 : ℝ) ^ (J + i) < 2 * x :=
        mul_lt_mul_of_pos_left hiA.1 (by norm_num)
      exact False.elim <| (lt_irrefl (2 * x)) ((htwoX.trans_lt hnUpper).trans hlowerX)
    · have hpow : (2 : ℝ) ^ (J + j + 1) ≤ (2 : ℝ) ^ (J + i) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hyx : y < x := (hjA.2.trans_le hpow).trans hiA.1
      exact False.elim <| (not_lt_of_ge hxy.le) hyx
  have hxpos : 0 < x := (by positivity : (0 : ℝ) < (2 : ℝ) ^ (J + i)).trans hiA.1
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnBound : n ≤ 2 ^ (j + 1) := by
    have hpowJ : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    have hpowEq :
        (2 : ℝ) ^ (J + j + 1) = (2 : ℝ) ^ J * (2 : ℝ) ^ (j + 1) := by
      rw [show J + j + 1 = J + (j + 1) by omega, pow_add]
    have hnlt : (n : ℝ) < (2 : ℝ) ^ (j + 1) := by
      have hpowLower : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + i) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hxJ : (2 : ℝ) ^ J < x := hpowLower.trans_lt hiA.1
      have hmul : (n : ℝ) * (2 : ℝ) ^ J < (2 : ℝ) ^ (J + j + 1) := by
        calc
          (n : ℝ) * (2 : ℝ) ^ J < (n : ℝ) * x :=
            mul_lt_mul_of_pos_left hxJ (by positivity)
          _ = y := hEq.symm
          _ < (2 : ℝ) ^ (J + j + 1) := hjA.2
      rw [hpowEq] at hmul
      nlinarith
    exact_mod_cast hnlt.le
  have hrec' :
      dist ((((q j : ℕ) : ℝ) * logCoord n : ℝ) : UnitAddCircle) 0 ≤
        combWidth (d j) := by
    have heq :
        ((((q j : ℕ) : ℝ) * logCoord n : ℝ) : UnitAddCircle) =
          q j • ((logCoord n : ℝ) : UnitAddCircle) := by
      rw [← AddCircle.coe_nsmul]
      congr 1
      simp [nsmul_eq_mul]
    rw [heq]
    exact hrec j n hnBound
  have hyGlobal : y ∈ globalLogComb (q j) (combWidth (d j)) :=
    logComb_subset_globalLogComb (hq j) (hd j) hjH
  have hmulGlobal : x * (n : ℝ) ∈ globalLogComb (q j) (combWidth (d j)) := by
    rw [mul_comm, ← hEq]
    exact hyGlobal
  have hxShadow : x ∈ globalLogComb (q j) (2 * combWidth (d j)) :=
    mem_globalLogComb_of_mul_mem hx0 hn0 hrec' hmulGlobal
  have hxFuture : x ∈ futureShadows q d i := by
    rw [futureShadows, mem_iUnion]
    exact ⟨⟨j, hij⟩, hxShadow⟩
  exact hi.2 hxFuture

lemma integerRatioFree_constructedSet
    (J : ℕ) (q d : ℕ → ℕ)
    (hq : ∀ i, 0 < q i) (hd : ∀ i, 0 < d i)
    (hrec : ∀ j (n : ℕ), n ≤ 2 ^ (j + 1) →
      dist (q j • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤ combWidth (d j)) :
    IntegerRatioFree (constructedSet J q d) :=
  (integerRatioFree_iff_positiveNatRatioFree
    (constructedSet_subset_Ioi J q d hq hd)).2
    (positiveNatRatioFree_constructedSet J q d hq hd hrec)

/-! ### Recursive choice of aligned recurrent frequencies -/

noncomputable def nextFrequency (D N d : ℕ) : ℕ :=
  if h : 0 < D ∧ 0 < d then
    Classical.choose (exists_multiple_log_recurrence D N h.1 (combWidth_pos h.2))
  else 1

lemma nextFrequency_spec {D N d : ℕ} (hD : 0 < D) (hd : 0 < d) :
    0 < nextFrequency D N d ∧ D ∣ nextFrequency D N d ∧
      ∀ n : ℕ, n ≤ N →
        dist (nextFrequency D N d • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤
          combWidth d := by
  rw [nextFrequency, dif_pos ⟨hD, hd⟩]
  exact Classical.choose_spec
    (exists_multiple_log_recurrence D N hD (combWidth_pos hd))

noncomputable def frequencies (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => nextFrequency 1 (2 ^ (0 + 1)) (d 0)
  | k + 1 => nextFrequency (4 * d k * frequencies d k)
      (2 ^ ((k + 1) + 1)) (d (k + 1))

lemma frequencies_pos (d : ℕ → ℕ) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < frequencies d i := by
  intro i
  induction i with
  | zero =>
      exact (nextFrequency_spec (by norm_num) (hd 0)).1
  | succ k ih =>
      rw [frequencies]
      exact (nextFrequency_spec
        (Nat.mul_pos (Nat.mul_pos (by norm_num) (hd k)) ih) (hd (k + 1))).1

lemma frequencies_recurrence (d : ℕ → ℕ) (hd : ∀ i, 0 < d i) :
    ∀ j (n : ℕ), n ≤ 2 ^ (j + 1) →
      dist (frequencies d j • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤
        combWidth (d j) := by
  intro j
  cases j with
  | zero =>
      change ∀ n : ℕ, n ≤ 2 →
        dist (nextFrequency 1 2 (d 0) • ((logCoord n : ℝ) : UnitAddCircle)) 0 ≤
          combWidth (d 0)
      exact
        (nextFrequency_spec (D := 1) (N := 2) (d := d 0)
          (by norm_num) (hd 0)).2.2
  | succ k =>
      rw [frequencies]
      exact (nextFrequency_spec
          (D := 4 * d k * frequencies d k)
          (N := 2 ^ ((k + 1) + 1)) (d := d (k + 1))
          (Nat.mul_pos (Nat.mul_pos (by norm_num) (hd k)) (frequencies_pos d hd k))
          (hd (k + 1))).2.2

lemma frequency_factor_dvd_succ (d : ℕ → ℕ) (hd : ∀ i, 0 < d i) (i : ℕ) :
    4 * d i * frequencies d i ∣ frequencies d (i + 1) := by
  rw [frequencies]
  exact (nextFrequency_spec
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (hd i)) (frequencies_pos d hd i))
    (hd (i + 1))).2.1

lemma frequency_dvd_of_le (d : ℕ → ℕ) (hd : ∀ i, 0 < d i)
    {i j : ℕ} (hij : i ≤ j) : frequencies d i ∣ frequencies d j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact dvd_refl _
  | succ j ih =>
      rcases eq_or_lt_of_le hij with hij' | hij'
      · subst i
        exact dvd_refl _
      · exact (ih (by omega)).trans <|
          (dvd_mul_left (frequencies d j) (4 * d j)).trans
            (frequency_factor_dvd_succ d hd j)

lemma frequencies_aligned (d : ℕ → ℕ) (hd : ∀ i, 0 < d i) :
    ∀ i j, i < j → 4 * d i * frequencies d i ∣ frequencies d j := by
  intro i j hij
  exact (frequency_factor_dvd_succ d hd i).trans
    (frequency_dvd_of_le d hd (by omega))

/-! ### Choosing reciprocal widths -/

lemma exists_combWidth_majorant {s : ℝ} (hs : 0 < s) (hs8 : s ≤ 1 / 8) :
    ∃ d : ℕ, 0 < d ∧ s ≤ combWidth d ∧ combWidth d ≤ 2 * s := by
  let z : ℝ := 1 / (4 * s)
  let d : ℕ := ⌊z⌋₊
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz2 : 2 ≤ z := by
    dsimp [z]
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).2
    nlinarith
  have hdle : (d : ℝ) ≤ z := Nat.floor_le hz0
  have hzlt : z < (d : ℝ) + 1 := Nat.lt_floor_add_one z
  have hdpos : 0 < d := by
    have : (1 : ℝ) < (d : ℝ) + 1 :=
      (by norm_num : (1 : ℝ) < 2).trans_le hz2 |>.trans hzlt
    exact_mod_cast (by linarith : (0 : ℝ) < d)
  have hdlower : z / 2 ≤ d := by linarith
  refine ⟨d, hdpos, ?_, ?_⟩
  · unfold combWidth
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    dsimp [z] at hdle
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
    have hspos : 0 < s := hs
    field_simp at hdle
    nlinarith
  · unfold combWidth
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    dsimp [z] at hdlower
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
    field_simp at hdlower
    nlinarith

noncomputable def widthDenominator (s : ℝ) : ℕ :=
  if h : 0 < s ∧ s ≤ 1 / 8 then
    Classical.choose (exists_combWidth_majorant h.1 h.2)
  else 1

lemma widthDenominator_spec {s : ℝ} (hs : 0 < s) (hs8 : s ≤ 1 / 8) :
    0 < widthDenominator s ∧ s ≤ combWidth (widthDenominator s) ∧
      combWidth (widthDenominator s) ≤ 2 * s := by
  rw [widthDenominator, dif_pos ⟨hs, hs8⟩]
  exact Classical.choose_spec (exists_combWidth_majorant hs hs8)

noncomputable def geometricError (k : ℕ) : ℝ :=
  (1 / 512 : ℝ) * ((1 / 2 : ℝ) ^ k)

lemma geometricError_pos (k : ℕ) : 0 < geometricError k := by
  unfold geometricError
  positivity

lemma summable_geometricError : Summable geometricError := by
  unfold geometricError
  exact summable_geometric_two.mul_left _

lemma tsum_geometricError : ∑' k, geometricError k = (1 / 256 : ℝ) := by
  change (∑' k : ℕ, (1 / 512 : ℝ) * ((1 / 2 : ℝ) ^ k)) = 1 / 256
  rw [tsum_mul_left, tsum_geometric_two]
  norm_num

noncomputable def denominatorsFor (p : ℕ → ℝ) (k : ℕ) : ℕ :=
  widthDenominator (p k + geometricError k)

lemma denominatorsFor_spec {p : ℕ → ℝ}
    (hp0 : ∀ k, 0 ≤ p k)
    (htotal : ∑' k, p k ≤ 1 / 256)
    (hp : Summable p) :
    (∀ k, 0 < denominatorsFor p k) ∧
    (∀ k, p k ≤ combWidth (denominatorsFor p k)) ∧
    Summable (fun k => combWidth (denominatorsFor p k)) ∧
    (∑' k, combWidth (denominatorsFor p k)) ≤ 1 / 64 := by
  have hs8 (k : ℕ) : p k + geometricError k ≤ 1 / 8 := by
    have hpk : p k ≤ ∑' n, p n := hp.le_tsum k (fun n _ => hp0 n)
    have hek : geometricError k ≤ ∑' n, geometricError n :=
      summable_geometricError.le_tsum k (fun n _ => (geometricError_pos n).le)
    rw [tsum_geometricError] at hek
    linarith
  have hspec (k : ℕ) := widthDenominator_spec
    (add_pos_of_nonneg_of_pos (hp0 k) (geometricError_pos k)) (hs8 k)
  have hdom (k : ℕ) :
      combWidth (denominatorsFor p k) ≤ 2 * (p k + geometricError k) := by
    exact (hspec k).2.2
  have hsumPG : Summable fun k => 2 * (p k + geometricError k) :=
    (hp.add summable_geometricError).mul_left 2
  have hsumW : Summable fun k => combWidth (denominatorsFor p k) :=
    hsumPG.of_nonneg_of_le
      (fun k => (combWidth_pos (hspec k).1).le) hdom
  refine ⟨fun k => (hspec k).1,
    fun k => (le_add_of_nonneg_right (geometricError_pos k).le).trans (hspec k).2.1,
    hsumW, ?_⟩
  calc
    (∑' k, combWidth (denominatorsFor p k))
        ≤ ∑' k, 2 * (p k + geometricError k) :=
      hsumW.tsum_le_tsum hdom hsumPG
    _ = 2 * ((∑' k, p k) + ∑' k, geometricError k) := by
      rw [tsum_mul_left, hp.tsum_add summable_geometricError]
    _ ≤ 2 * ((1 / 256 : ℝ) + 1 / 256) := by
      rw [tsum_geometricError]
      gcongr
    _ = (1 / 64 : ℝ) := by norm_num

/-! ## The dyadic integral criterion -/

/-- The half-open dyadic cells partitioning `[1, ∞)`. -/
noncomputable def dyadicCell (n : ℕ) : Set ℝ :=
  Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))

lemma dyadicCell_pairwise : _root_.Pairwise (Disjoint on dyadicCell) := by
  exact Monotone.pairwise_disjoint_on_Ico_succ
    (monotone_nat_of_le_succ fun n => by
      rw [pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ n := by positivity
      nlinarith)

lemma iUnion_dyadicCell : (⋃ n, dyadicCell n) = Ici 1 := by
  simpa [dyadicCell] using
    (iUnion_Ico_map_succ_eq_Ici
      (f := fun n : ℕ => (2 : ℝ) ^ n)
      (fun n => by
        change (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ n
        exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le n))
      (not_bddAbove_iff.mpr fun b => by
        obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop b).exists
        exact ⟨(2 : ℝ) ^ n, ⟨n, rfl⟩, hn⟩))

lemma restrict_Ici_eq_sum_dyadic :
    volume.restrict (Ici (1 : ℝ)) =
      Measure.sum (fun n => volume.restrict (dyadicCell n)) := by
  rw [← iUnion_dyadicCell]
  exact Measure.restrict_iUnion dyadicCell_pairwise (fun _ => measurableSet_Ico)

lemma integral_const_dyadicCell (n : ℕ) (c : ℝ) :
    (∫ _x : ℝ in dyadicCell n, c) = (2 : ℝ) ^ n * c := by
  rw [integral_const]
  rw [measureReal_restrict_apply MeasurableSet.univ]
  simp only [univ_inter, measureReal_def, smul_eq_mul]
  unfold dyadicCell
  rw [Real.volume_Ico]
  rw [pow_succ]
  have hp : 0 ≤ (2 : ℝ) ^ n := by positivity
  rw [show (2 : ℝ) ^ n * 2 - (2 : ℝ) ^ n = (2 : ℝ) ^ n by ring,
    ENNReal.toReal_ofReal hp]

/-- The dyadic samples occurring in Cauchy condensation. -/
noncomputable def dyadicTerm (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  F ((2 : ℝ) ^ n) / (2 : ℝ) ^ n

lemma summable_dyadicTerm_of_integrable
    (F : ℝ → ℝ)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x)
    (hmono : MonotoneOn F (Ici (1 : ℝ)))
    (hInt : IntegrableOn (fun x => F x / x ^ 2) (Ici (1 : ℝ))) :
    Summable (dyadicTerm F) := by
  have hIntSum : Integrable (fun x => F x / x ^ 2)
      (Measure.sum (fun n => volume.restrict (dyadicCell n))) := by
    rw [← restrict_Ici_eq_sum_dyadic]
    exact hInt
  have hsumInt : Summable (fun n =>
      ∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖) :=
    hIntSum.summable_integral
  have hterm0 (n : ℕ) : 0 ≤ dyadicTerm F n := by
    exact div_nonneg
      (hF0 _ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)
  have hlower (n : ℕ) : dyadicTerm F n / 4 ≤
      ∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖ := by
    let a : ℝ := (2 : ℝ) ^ n
    let c : ℝ := F a / (4 * a ^ 2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hFa : 0 ≤ F a := hF0 a (by
      dsimp [a]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hconst : IntegrableOn (fun _x : ℝ => c) (dyadicCell n) := by
      apply integrableOn_const
      · unfold dyadicCell
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    have htarget : IntegrableOn (fun x : ℝ => ‖F x / x ^ 2‖) (dyadicCell n) := by
      exact (hInt.mono_set (by
        intro x hx
        exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx.1)) |>.norm
    have hpoint : ∀ x ∈ dyadicCell n, c ≤ ‖F x / x ^ 2‖ := by
      intro x hx
      have hxa : a ≤ x := hx.1
      have hx2a : x < 2 * a := by
        simpa [dyadicCell, a, pow_succ, mul_comm] using hx.2
      have hx0 : 0 < x := ha.trans_le hxa
      have hFx : F a ≤ F x := hmono
        (by dsimp [a]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (by
          exact (show (1 : ℝ) ≤ a by
            dsimp [a]
            exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hxa) hxa
      have hFx0 : 0 ≤ F x := hFa.trans hFx
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hFx0 (sq_nonneg x))]
      dsimp [c]
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * a ^ 2)
        (sq_pos_of_pos hx0)).2
      have hsquare : x ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      nlinarith
    have hmonoInt := setIntegral_mono_on hconst htarget measurableSet_Ico hpoint
    rw [integral_const_dyadicCell] at hmonoInt
    calc
      dyadicTerm F n / 4 = a * c := by
        dsimp [dyadicTerm, a, c]
        have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        field_simp
      _ ≤ ∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖ := by
        simpa [a] using hmonoInt
  have hscaled : Summable (fun n => dyadicTerm F n / 4) :=
    hsumInt.of_nonneg_of_le (fun n => div_nonneg (hterm0 n) (by norm_num)) hlower
  have hmul := hscaled.mul_left 4
  exact hmul.congr (fun n => by ring)

/-- A globally monotone measurable extension of `F|[1,∞)`. -/
noncomputable def monotoneTailExtension (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F (max 1 x)

lemma monotone_monotoneTailExtension {F : ℝ → ℝ}
    (hmono : MonotoneOn F (Ici (1 : ℝ))) :
    Monotone (monotoneTailExtension F) := by
  intro x y hxy
  apply hmono
  · exact (show (1 : ℝ) ≤ max 1 x from le_max_left _ _)
  · exact (show (1 : ℝ) ≤ max 1 y from le_max_left _ _)
  · exact max_le_max_left (1 : ℝ) hxy

lemma integrable_of_summable_dyadicTerm
    (F : ℝ → ℝ)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x)
    (hmono : MonotoneOn F (Ici (1 : ℝ)))
    (hsum : Summable (dyadicTerm F)) :
    IntegrableOn (fun x => F x / x ^ 2) (Ici (1 : ℝ)) := by
  have htailMeas : Measurable (monotoneTailExtension F) :=
    (monotone_monotoneTailExtension hmono).measurable
  have hquotMeas : Measurable (fun x : ℝ => monotoneTailExtension F x / x ^ 2) :=
    htailMeas.div (measurable_id.pow_const 2)
  have hcell (n : ℕ) :
      IntegrableOn (fun x => F x / x ^ 2) (dyadicCell n) := by
    let a : ℝ := (2 : ℝ) ^ n
    let b : ℝ := F (2 * a) / a ^ 2
    have ha : 0 < a := by dsimp [a]; positivity
    have h2aIci : 2 * a ∈ Ici (1 : ℝ) := by
      change (1 : ℝ) ≤ 2 * a
      have : (1 : ℝ) ≤ a := by
        dsimp [a]
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (hF0 _ h2aIci) (sq_nonneg a)
    have hbInt : Integrable (fun _x : ℝ => b) (volume.restrict (dyadicCell n)) := by
      apply integrableOn_const
      · unfold dyadicCell
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    have hstrong : AEStronglyMeasurable (fun x : ℝ => F x / x ^ 2)
        (volume.restrict (dyadicCell n)) := by
      apply (hquotMeas.aestronglyMeasurable
        (μ := volume.restrict (dyadicCell n))).congr
      apply (ae_restrict_iff' measurableSet_Ico).2
      filter_upwards with x hx
      have hx1 : (1 : ℝ) ≤ x :=
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx.1
      simp [monotoneTailExtension, max_eq_right hx1]
    apply Integrable.mono' hbInt hstrong
    apply (ae_restrict_iff' measurableSet_Ico).2
    filter_upwards with x hx
    have hax : a ≤ x := hx.1
    have hx2a : x ≤ 2 * a := by
      have := hx.2.le
      simpa [dyadicCell, a, pow_succ, mul_comm] using this
    have hx1 : (1 : ℝ) ≤ x := by
      exact (show (1 : ℝ) ≤ a by
        dsimp [a]
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hax
    have hFx0 : 0 ≤ F x := hF0 x hx1
    have hFxle : F x ≤ F (2 * a) := hmono hx1 h2aIci hx2a
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hFx0 (sq_nonneg x))]
    dsimp [b]
    apply (div_le_div_iff₀ (sq_pos_of_pos (ha.trans_le hax)) (sq_pos_of_pos ha)).2
    have hsquare : a ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith
  have hIntBound (n : ℕ) :
      (∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖) ≤
        2 * dyadicTerm F (n + 1) := by
    let a : ℝ := (2 : ℝ) ^ n
    let b : ℝ := F (2 * a) / a ^ 2
    have ha : 0 < a := by dsimp [a]; positivity
    have h2aIci : 2 * a ∈ Ici (1 : ℝ) := by
      change (1 : ℝ) ≤ 2 * a
      have : (1 : ℝ) ≤ a := by
        dsimp [a]
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (hF0 _ h2aIci) (sq_nonneg a)
    have hbInt : IntegrableOn (fun _x : ℝ => b) (dyadicCell n) := by
      apply integrableOn_const
      · unfold dyadicCell
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    have hpoint : ∀ x ∈ dyadicCell n, ‖F x / x ^ 2‖ ≤ b := by
      intro x hx
      have hax : a ≤ x := hx.1
      have hx2a : x ≤ 2 * a := by
        have := hx.2.le
        simpa [dyadicCell, a, pow_succ, mul_comm] using this
      have hx1 : (1 : ℝ) ≤ x :=
        (show (1 : ℝ) ≤ a by
          dsimp [a]
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hax
      have hFx0 : 0 ≤ F x := hF0 x hx1
      have hFxle : F x ≤ F (2 * a) := hmono hx1 h2aIci hx2a
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hFx0 (sq_nonneg x))]
      dsimp [b]
      apply (div_le_div_iff₀ (sq_pos_of_pos (ha.trans_le hax)) (sq_pos_of_pos ha)).2
      have hsquare : a ^ 2 ≤ x ^ 2 := by nlinarith
      nlinarith
    have hi := setIntegral_mono_on (hcell n).norm hbInt measurableSet_Ico hpoint
    rw [integral_const_dyadicCell] at hi
    calc
      (∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖) ≤ a * b := by
        simpa [a] using hi
      _ = 2 * dyadicTerm F (n + 1) := by
        dsimp [a, b, dyadicTerm]
        rw [pow_succ]
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        field_simp
        ring_nf
  have hshift : Summable (fun n => dyadicTerm F (n + 1)) := by
    have h := hsum.comp_injective (i := fun n : ℕ => n + 1)
      (fun _ _ h => Nat.add_right_cancel h)
    simpa [Function.comp_def] using h
  have hdom : Summable (fun n => 2 * dyadicTerm F (n + 1)) := hshift.mul_left 2
  have hsumInt : Summable (fun n =>
      ∫ x : ℝ in dyadicCell n, ‖F x / x ^ 2‖) :=
    hdom.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hIntBound
  rw [← iUnion_dyadicCell]
  exact integrableOn_iUnion_of_summable_integral_norm hcell hsumInt

/-! ## Quantitative construction -/

/-- Width required in the `n`-th annulus to dominate the value two annuli
ahead. -/
noncomputable def normalizedTarget (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  F ((2 : ℝ) ^ (n + 2)) / (Real.log 2 * (2 : ℝ) ^ n)

lemma normalizedTarget_eq (F : ℝ → ℝ) (n : ℕ) :
    normalizedTarget F n = (4 / Real.log 2) * dyadicTerm F (n + 2) := by
  unfold normalizedTarget dyadicTerm
  rw [pow_add]
  norm_num
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hl := log_two_pos.ne'
  field_simp

lemma summable_normalizedTarget {F : ℝ → ℝ}
    (hsum : Summable (dyadicTerm F)) : Summable (normalizedTarget F) := by
  have hshift : Summable (fun n => dyadicTerm F (n + 2)) := by
    have h := hsum.comp_injective (i := fun n : ℕ => n + 2)
      (fun _ _ h => Nat.add_right_cancel h)
    simpa [Function.comp_def] using h
  exact (hshift.mul_left (4 / Real.log 2)).congr
    (fun n => (normalizedTarget_eq F n).symm)

lemma normalizedTarget_nonneg {F : ℝ → ℝ}
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x) (n : ℕ) :
    0 ≤ normalizedTarget F n := by
  unfold normalizedTarget
  exact div_nonneg
    (hF0 _ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    (mul_nonneg log_two_pos.le (by positivity))

lemma exists_small_normalizedTarget_tail {F : ℝ → ℝ}
    (hsum : Summable (dyadicTerm F)) :
    ∃ J : ℕ,
      Summable (fun k => normalizedTarget F (k + J)) ∧
      (∑' k, normalizedTarget F (k + J)) ≤ 1 / 256 := by
  have hnorm := summable_normalizedTarget hsum
  have htend : Tendsto (fun J => ∑' k, normalizedTarget F (k + J))
      atTop (𝓝 0) := _root_.tendsto_sum_nat_add (normalizedTarget F)
  have hev : ∀ᶠ J in atTop,
      (∑' k, normalizedTarget F (k + J)) < 1 / 256 :=
    (tendsto_order.1 htend).2 _ (by norm_num)
  obtain ⟨J, hJ⟩ := hev.exists
  refine ⟨J, ?_, hJ.le⟩
  have h := hnorm.comp_injective (i := fun k : ℕ => k + J)
    (fun _ _ h => Nat.add_right_cancel h)
  simpa [Function.comp_def] using h

lemma normalizedTarget_le_trimmedComb
    (F : ℝ → ℝ) (J : ℕ) (q d : ℕ → ℕ)
    (hq : ∀ i, 0 < q i) (hd : ∀ i, 0 < d i)
    (halign : ∀ i j, i < j → 4 * d i * q i ∣ q j)
    (hsum : Summable fun j => combWidth (d j))
    (htotal : ∑' j, combWidth (d j) ≤ 1 / 16)
    (hwidth : ∀ i, normalizedTarget F (i + J) ≤ combWidth (d i)) (i : ℕ) :
    F ((2 : ℝ) ^ (J + i + 2)) ≤ volume.real (trimmedComb J q d i) := by
  have htrim := measureReal_trimmedComb_lower J q d hq hd halign hsum htotal i
  have hraw := measureReal_logComb_lower (j := J + i) (hq i) (hd i)
  have hlog : 0 < Real.log 2 := log_two_pos
  have hpow : (0 : ℝ) < 2 ^ (J + i) := by positivity
  have hw0 : 0 ≤ combWidth (d i) := (combWidth_pos (hd i)).le
  have hnorm := hwidth i
  rw [normalizedTarget] at hnorm
  have htarget : F ((2 : ℝ) ^ (J + i + 2)) ≤
      (2 : ℝ) ^ (J + i) * combWidth (d i) * Real.log 2 := by
    have hden : 0 < Real.log 2 * (2 : ℝ) ^ (i + J) := by positivity
    apply (div_le_iff₀ hden).mp at hnorm
    rw [show i + J = J + i by omega] at hnorm
    nlinarith
  calc
    F ((2 : ℝ) ^ (J + i + 2))
        ≤ (2 : ℝ) ^ (J + i) * combWidth (d i) * Real.log 2 := htarget
    _ = (1 / 2 : ℝ) *
        ((2 : ℝ) ^ (J + i) * (2 * combWidth (d i) * Real.log 2)) := by ring
    _ ≤ (1 / 2 : ℝ) * volume.real (logComb (J + i) (q i) (d i)) := by
      gcongr
    _ ≤ volume.real (trimmedComb J q d i) := htrim

/-- The exact witness property in the resolution of Problem 1195. -/
def HasErdos1195Witness (F : ℝ → ℝ) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ volume S = ∞ ∧ IntegerRatioFree S ∧
    ∀ᶠ x in atTop, F x ≤ countingFunction S x

theorem exists_witness_of_integrable
    (F : ℝ → ℝ)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x)
    (hmono : MonotoneOn F (Ici (1 : ℝ)))
    (hFtop : Tendsto F atTop atTop)
    (hInt : IntegrableOn (fun x => F x / x ^ 2) (Ici (1 : ℝ))) :
    HasErdos1195Witness F := by
  have hdyad := summable_dyadicTerm_of_integrable F hF0 hmono hInt
  obtain ⟨J, hpSum, hpTotal⟩ := exists_small_normalizedTarget_tail hdyad
  let p : ℕ → ℝ := fun k => normalizedTarget F (k + J)
  have hp0 : ∀ k, 0 ≤ p k := fun k => normalizedTarget_nonneg hF0 _
  have hpSpec := denominatorsFor_spec hp0 hpTotal hpSum
  let d : ℕ → ℕ := denominatorsFor p
  let q : ℕ → ℕ := frequencies d
  let S : Set ℝ := constructedSet J q d
  have hd : ∀ i, 0 < d i := hpSpec.1
  have hwidth : ∀ i, p i ≤ combWidth (d i) := hpSpec.2.1
  have hwSum : Summable fun i => combWidth (d i) := hpSpec.2.2.1
  have hwTotal : ∑' i, combWidth (d i) ≤ 1 / 16 :=
    hpSpec.2.2.2.trans (by norm_num)
  have hq : ∀ i, 0 < q i := frequencies_pos d hd
  have halign : ∀ i j, i < j → 4 * d i * q i ∣ q j := frequencies_aligned d hd
  have hmass (i : ℕ) :
      F ((2 : ℝ) ^ (J + i + 2)) ≤ volume.real (trimmedComb J q d i) := by
    apply normalizedTarget_le_trimmedComb F J q d hq hd halign hwSum hwTotal
    intro k
    simpa [p, add_comm] using hwidth k
  have hgrowth : ∀ᶠ x in atTop, F x ≤ countingFunction S x := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ (J + 2))] with x hx
    have hxIci : x ∈ Ici (1 : ℝ) :=
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx
    have hxCells := hxIci
    rw [← iUnion_dyadicCell] at hxCells
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxCells
    have hJn : J + 2 ≤ n := by
      by_contra hnot
      have hnle : n + 1 ≤ J + 2 := by omega
      have hple : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (J + 2) :=
        pow_le_pow_right₀ (by norm_num) hnle
      exact (not_lt_of_ge hx) (hn.2.trans_le hple)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hJn
    have hblockSub : trimmedComb J q d (k + 1) ⊆ S ∩ Ioo 0 x := by
      intro y hy
      constructor
      · exact mem_iUnion.mpr ⟨k + 1, hy⟩
      · have hyH := trimmedComb_subset_logComb J q d (k + 1) hy
        have hyA := logComb_subset_dyadic_annulus (hq (k + 1)) (hd (k + 1)) hyH
        constructor
        · exact (by positivity : (0 : ℝ) < 2 ^ (J + (k + 1))).trans hyA.1
        · have hupp : y < (2 : ℝ) ^ (J + (k + 1) + 1) := hyA.2
          have hlowerx : (2 : ℝ) ^ (J + 2 + k) ≤ x := hn.1
          rw [show J + (k + 1) + 1 = J + 2 + k by omega] at hupp
          exact hupp.trans_le hlowerx
    have hcount : volume.real (trimmedComb J q d (k + 1)) ≤ countingFunction S x := by
      unfold countingFunction
      exact measureReal_mono hblockSub (measure_ne_top_of_subset inter_subset_right <| by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    have hFx : F x ≤ F ((2 : ℝ) ^ (J + 2 + k + 1)) := by
      apply hmono hxIci
      · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      · exact hn.2.le
    calc
      F x ≤ F ((2 : ℝ) ^ (J + 2 + k + 1)) := hFx
      _ ≤ volume.real (trimmedComb J q d (k + 1)) := by
        simpa [show J + (k + 1) + 2 = J + 2 + k + 1 by omega] using hmass (k + 1)
      _ ≤ countingFunction S x := hcount
  have hSinf : volume S = ∞ := by
    by_contra hne
    have hevF : ∀ᶠ x in atTop, volume.real S < F x := hFtop.eventually_gt_atTop _
    have hfalse : ∀ᶠ _x : ℝ in atTop, False := by
      filter_upwards [hgrowth, hevF] with x hxg hxF
      have hcountLe : countingFunction S x ≤ volume.real S := by
        unfold countingFunction
        exact measureReal_mono inter_subset_left hne
      linarith
    exact hfalse.exists.elim fun _ h => h
  exact ⟨S, measurableSet_constructedSet J q d, hSinf,
    integerRatioFree_constructedSet J q d hq hd (frequencies_recurrence d hd), hgrowth⟩

/-! ## The packing obstruction -/

/-- The part of `S` in the `n`-th dyadic annulus. -/
noncomputable def annularSlice (S : Set ℝ) (n : ℕ) : Set ℝ :=
  S ∩ dyadicCell n

/-- The `n`-th annular slice scaled back into `[1,2)`. -/
noncomputable def scaledSlice (S : Set ℝ) (n : ℕ) : Set ℝ :=
  (fun u : ℝ => (2 : ℝ) ^ n * u) ⁻¹' annularSlice S n

lemma measurableSet_annularSlice {S : Set ℝ} (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (annularSlice S n) := hS.inter measurableSet_Ico

lemma measurableSet_scaledSlice {S : Set ℝ} (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (scaledSlice S n) :=
  (measurableSet_annularSlice hS n).preimage (measurable_const_mul _)

lemma scaledSlice_subset_Ico (S : Set ℝ) (n : ℕ) :
    scaledSlice S n ⊆ Ico (1 : ℝ) 2 := by
  intro u hu
  have hcell : (2 : ℝ) ^ n * u ∈ dyadicCell n := hu.2
  rw [dyadicCell, mem_Ico, pow_succ] at hcell
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  constructor <;> nlinarith

lemma pairwise_disjoint_scaledSlice {S : Set ℝ} (hSpos : S ⊆ Ioi 0)
    (hfree : IntegerRatioFree S) :
    _root_.Pairwise (Disjoint on scaledSlice S) := by
  have hPN : PositiveNatRatioFree S :=
    (integerRatioFree_iff_positiveNatRatioFree hSpos).1 hfree
  have aux {n m : ℕ} (hnm : n < m) : Disjoint (scaledSlice S n) (scaledSlice S m) := by
    rw [Set.disjoint_left]
    intro u hun hum
    have huIco := scaledSlice_subset_Ico S n hun
    have hu0 : 0 < u := zero_lt_one.trans_le huIco.1
    have hxn : (2 : ℝ) ^ n * u ∈ S := hun.1
    have hxm : (2 : ℝ) ^ m * u ∈ S := hum.1
    have hpowlt : (2 : ℝ) ^ n < (2 : ℝ) ^ m :=
      pow_lt_pow_right₀ (by norm_num) hnm
    have hxy : (2 : ℝ) ^ n * u < (2 : ℝ) ^ m * u :=
      mul_lt_mul_of_pos_right hpowlt hu0
    let N : ℕ := 2 ^ (m - n)
    have hN : 2 ≤ N := by
      dsimp [N]
      have : 1 ≤ m - n := by omega
      exact (show 2 ^ 1 ≤ 2 ^ (m - n) from
        pow_le_pow_right₀ (by omega) this)
    have hEq : (2 : ℝ) ^ m * u = (N : ℝ) * ((2 : ℝ) ^ n * u) := by
      dsimp [N]
      push_cast
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    exact hPN hxn hxm hxy N hN hEq
  intro n m hne
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · exact aux hnm
  · exact (aux hmn).symm

lemma measureReal_scaledSlice_eq (S : Set ℝ) (n : ℕ) :
    volume.real (scaledSlice S n) =
      volume.real (annularSlice S n) / (2 : ℝ) ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hfin : volume (annularSlice S n) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right <| by
      unfold dyadicCell
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
  unfold scaledSlice
  rw [measureReal_def, Real.volume_preimage_mul_left hp.ne', ENNReal.toReal_mul]
  · rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (inv_pos.mpr hp)]
      rw [inv_eq_one_div]
      simp only [measureReal_def]
      ring
    · positivity

/-- Normalized mass in one dyadic annulus. -/
noncomputable def sliceTerm (S : Set ℝ) (n : ℕ) : ℝ :=
  volume.real (annularSlice S n) / (2 : ℝ) ^ n

lemma summable_sliceTerm {S : Set ℝ} (hS : MeasurableSet S)
    (hSpos : S ⊆ Ioi 0) (hfree : IntegerRatioFree S) :
    Summable (sliceTerm S) := by
  have hpair := pairwise_disjoint_scaledSlice hSpos hfree
  have hmeas : ∀ n, MeasurableSet (scaledSlice S n) :=
    measurableSet_scaledSlice hS
  have hunionSub : (⋃ n, scaledSlice S n) ⊆ Ico (1 : ℝ) 2 := by
    exact iUnion_subset fun n => scaledSlice_subset_Ico S n
  have htop : volume (⋃ n, scaledSlice S n) ≠ ∞ :=
    measure_ne_top_of_subset hunionSub <| by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
  have htsum : (∑' n, volume (scaledSlice S n)) ≠ ∞ := by
    rw [← measure_iUnion hpair hmeas]
    exact htop
  have hs := ENNReal.summable_toReal htsum
  exact hs.congr fun n => by
    rw [← measureReal_def, measureReal_scaledSlice_eq]
    rfl

lemma countingFunction_dyadic_le (S : Set ℝ) (n : ℕ) :
    countingFunction S ((2 : ℝ) ^ n) ≤
      volume.real (S ∩ Ioo 0 1) +
        ∑ k ∈ Finset.range n, volume.real (annularSlice S k) := by
  let U : Set ℝ := (S ∩ Ioo 0 1) ∪
    ⋃ k ∈ Finset.range n, annularSlice S k
  have hsub : S ∩ Ioo 0 ((2 : ℝ) ^ n) ⊆ U := by
    intro x hx
    by_cases hx1 : x < 1
    · exact Or.inl ⟨hx.1, hx.2.1, hx1⟩
    · have hxIci : x ∈ Ici (1 : ℝ) := le_of_not_gt hx1
      have hxCells := hxIci
      rw [← iUnion_dyadicCell] at hxCells
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxCells
      have hkn : k < n := by
        by_contra hnot
        have hnk : n ≤ k := le_of_not_gt hnot
        have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num) hnk
        exact (not_lt_of_ge (hp.trans hk.1)) hx.2.2
      exact Or.inr <| mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkn, hx.1, hk⟩
  have hUfinite : volume U ≠ ∞ :=
    measure_ne_top_of_subset (s := Ioo 0 ((2 : ℝ) ^ n)) (fun x hx => by
      rcases hx with hx | hx
      · exact ⟨hx.2.1, hx.2.2.trans_le
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))⟩
      · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        have hcell := hxk.2
        have hklt : k < n := Finset.mem_range.mp hk
        have hk1 : k + 1 ≤ n := by omega
        have hx0 : 0 < x := by
          have : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
            one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
          exact zero_lt_one.trans_le (this.trans hcell.1)
        exact ⟨hx0,
          hcell.2.trans_le (pow_le_pow_right₀
            (by norm_num : (1 : ℝ) ≤ 2) hk1)⟩) <| by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
  calc
    countingFunction S ((2 : ℝ) ^ n)
        ≤ volume.real U := by
      unfold countingFunction
      exact measureReal_mono hsub hUfinite
    _ ≤ volume.real (S ∩ Ioo 0 1) +
        volume.real (⋃ k ∈ Finset.range n, annularSlice S k) :=
      measureReal_union_le _ _
    _ ≤ volume.real (S ∩ Ioo 0 1) +
        ∑ k ∈ Finset.range n, volume.real (annularSlice S k) := by
      gcongr
      exact measureReal_biUnion_finset_le (Finset.range n) (annularSlice S)

lemma summable_countingFunction_dyadic {S : Set ℝ}
    (hS : MeasurableSet S) (hSpos : S ⊆ Ioi 0)
    (hfree : IntegerRatioFree S) :
    Summable (fun n => countingFunction S ((2 : ℝ) ^ n) / (2 : ℝ) ^ n) := by
  have hs := summable_sliceTerm hS hSpos hfree
  let c : ℝ := volume.real (S ∩ Ioo 0 1)
  let g : ℕ → ℝ := fun r => (1 / 2 : ℝ) ^ r
  have hg : Summable g := summable_geometric_two
  have hprod : Summable (fun z : ℕ × ℕ => sliceTerm S z.1 * g z.2) := by
    apply (summable_prod_of_nonneg (f := fun z : ℕ × ℕ =>
      sliceTerm S z.1 * g z.2) (fun z => mul_nonneg
        (by unfold sliceTerm; exact div_nonneg measureReal_nonneg (by positivity))
        (by dsimp [g]; positivity))).2
    refine ⟨?_, ?_⟩
    · intro k
      exact hg.mul_left (sliceTerm S k)
    · have heq : (fun k => ∑' r, sliceTerm S k * g r) =
          fun k => 2 * sliceTerm S k := by
        funext k
        rw [tsum_mul_left, show (∑' r, g r) = 2 by
          exact tsum_geometric_two]
        ring
      rw [heq]
      exact hs.mul_left 2
  have hconv : Summable (fun n =>
      ∑ k ∈ Finset.range (n + 1), sliceTerm S k * g (n - k)) :=
    summable_sum_mul_range_of_summable_mul hprod
  have hbase : Summable (fun n => c * g n) := hg.mul_left c
  have hdom : Summable (fun n => c * g n +
      ∑ k ∈ Finset.range (n + 1), sliceTerm S k * g (n - k)) :=
    hbase.add hconv
  apply hdom.of_nonneg_of_le
  · intro n
    exact div_nonneg (countingFunction_nonneg S _) (by positivity)
  · intro n
    have hcount := countingFunction_dyadic_le S n
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    calc
      countingFunction S ((2 : ℝ) ^ n) / (2 : ℝ) ^ n
          ≤ (c + ∑ k ∈ Finset.range n, volume.real (annularSlice S k)) /
              (2 : ℝ) ^ n := by
            apply div_le_div_of_nonneg_right
            · simpa [c] using hcount
            · exact hpow.le
      _ = c * g n + ∑ k ∈ Finset.range n,
          sliceTerm S k * g (n - k) := by
            rw [add_div, Finset.sum_div]
            congr 1
            · dsimp [g]
              rw [one_div_pow]
              ring
            · apply Finset.sum_congr rfl
              intro k hk
              have hkn : k ≤ n := (Finset.mem_range.mp hk).le
              dsimp [sliceTerm, g]
              rw [one_div_pow]
              rw [show n = k + (n - k) by omega, pow_add]
              have hpk : (0 : ℝ) < 2 ^ k := by positivity
              have hpr : (0 : ℝ) < 2 ^ (n - k) := by positivity
              field_simp
              congr 1
              congr 1
              omega
      _ ≤ c * g n + ∑ k ∈ Finset.range (n + 1),
          sliceTerm S k * g (n - k) := by
            apply add_le_add (le_refl _)
            · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              intro k _hkbig _hknot
              exact mul_nonneg
                (by unfold sliceTerm; exact div_nonneg measureReal_nonneg (by positivity))
                (by dsimp [g]; positivity)

lemma summable_dyadicTerm_of_witness
    (F : ℝ → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hSpos : S ⊆ Ioi 0)
    (hfree : IntegerRatioFree S)
    (hgrowth : ∀ᶠ x in atTop, F x ≤ countingFunction S x)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x) :
    Summable (dyadicTerm F) := by
  have hcount := summable_countingFunction_dyadic hS hSpos hfree
  have hev : ∀ᶠ n : ℕ in atTop,
      F ((2 : ℝ) ^ n) ≤ countingFunction S ((2 : ℝ) ^ n) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually hgrowth
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have htail : Summable (fun k => dyadicTerm F (k + N)) := by
    have hcountTail := hcount.comp_injective (i := fun k : ℕ => k + N)
      (fun _ _ h => Nat.add_right_cancel h)
    apply hcountTail.of_nonneg_of_le
    · intro k
      unfold dyadicTerm
      exact div_nonneg
        (hF0 _ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)
    · intro k
      unfold dyadicTerm
      apply div_le_div_of_nonneg_right
      · exact hN (k + N) (by omega)
      · positivity
  exact (summable_nat_add_iff N).1 (by simpa [add_comm] using htail)

lemma integerRatioFree_mono {S T : Set ℝ} (hTS : T ⊆ S)
    (hS : IntegerRatioFree S) : IntegerRatioFree T := by
  intro x hx y hy hxy z
  exact hS (hTS hx) (hTS hy) hxy z

lemma countingFunction_positivePart (S : Set ℝ) (x : ℝ) :
    countingFunction (S ∩ Ioi 0) x = countingFunction S x := by
  unfold countingFunction
  apply congrArg ENNReal.toReal
  apply congrArg volume
  ext y
  simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
  tauto

/-!
## Resolution of Erdős Problem 1195

This is the stated sharp criterion.  The function is represented on all of
`ℝ`; the hypotheses say precisely that its restriction to `[1,∞)` takes
nonnegative values, is nondecreasing, and tends to infinity.
-/

theorem erdos_1195
    (F : ℝ → ℝ)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x)
    (hmono : MonotoneOn F (Ici (1 : ℝ)))
    (hFtop : Tendsto F atTop atTop) :
    HasErdos1195Witness F ↔
      IntegrableOn (fun x => F x / x ^ 2) (Ici (1 : ℝ)) := by
  constructor
  · rintro ⟨S, hSmeas, _hSinf, hSfree, hgrowth⟩
    let P : Set ℝ := S ∩ Ioi 0
    have hPmeas : MeasurableSet P := hSmeas.inter measurableSet_Ioi
    have hPpos : P ⊆ Ioi 0 := inter_subset_right
    have hPfree : IntegerRatioFree P :=
      integerRatioFree_mono inter_subset_left hSfree
    have hgrowthP : ∀ᶠ x in atTop, F x ≤ countingFunction P x := by
      filter_upwards [hgrowth] with x hx
      simpa [P, countingFunction_positivePart] using hx
    exact integrable_of_summable_dyadicTerm F hF0 hmono
      (summable_dyadicTerm_of_witness F hPmeas hPpos hPfree hgrowthP hF0)
  · exact exists_witness_of_integrable F hF0 hmono hFtop

end Erdos1195

#print axioms Erdos1195.erdos_1195
