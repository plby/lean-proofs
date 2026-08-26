/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Binary expansion pushes the fair-coin measure on `2^ω` forward to Lebesgue measure on `[0, 1)`.
-/
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ErdosProblems.Erdos501.Flypitch4.RandomAlgebra
import ErdosProblems.Erdos501.Flypitch4.Erdos501.ZFCCore

set_option relaxedAutoImplicit true

/-!
# Binary expansion is measure preserving (step S1 of `PLAN.md`)

`binExp f = ∑ n, f n · 2^{-(n+1)}` (`= ½ · cantorFunction (1/2) f`) maps `2^ω` onto `[0, 1]`, and
`map_binExp : cantorMeasure.map binExp = volume.restrict (Ico 0 1)`.  Together with
`ZFCCore.map_profileTest` this gives (P2) of Definition 3.1 for the test points
`x_m(z) = m + binExp (z 0)` on the profile space `2^P` (`map_profileTest_binExp`).

Proof: `binExp f = (f 0)/2 + binExp (shift f)/2`, and the first coordinate and the shift are
independent under the coin measure with the shift measure preserving (`map_zero_shift`); hence the
distribution function `F t = cantorMeasure {f | binExp f ≤ t}` satisfies
`F t = ½ F(2t − 1) + ½ F(2t)`, which forces `F(k/2ⁿ) = k/2ⁿ` (`F_dyadic`) and then `F t = t` on `[0, 1)`
by monotonicity (`F_eq`); finally two finite measures with the same distribution function agree
(`Measure.ext_of_Iic`).
-/

open MeasureTheory ProbabilityTheory Set Flypitch Flypitch.RandomAlgebra Filter Topology Cardinal
open scoped ENNReal

namespace Flypitch.Erdos501.ZFCCore

/-! ### The binary expansion -/

/-- Binary expansion `f ↦ ∑ n, f n · 2^{-(n+1)} ∈ [0, 1]`. -/
noncomputable def binExp (f : ℕ → Bool) : ℝ := (1 / 2) * cantorFunction (1 / 2) f

/-- The shift on `2^ω`. -/
def shift (f : ℕ → Bool) : ℕ → Bool := fun n => f (n + 1)

lemma binExp_succ (f : ℕ → Bool) :
    binExp f = (cond (f 0) 1 0) / 2 + binExp (shift f) / 2 := by
  unfold binExp shift
  rw [cantorFunction_succ f (by norm_num) (by norm_num)]
  ring

lemma cantorFunction_half_nonneg (f : ℕ → Bool) : 0 ≤ cantorFunction (1 / 2) f :=
  tsum_nonneg fun _ => cantorFunctionAux_nonneg (by norm_num)

lemma cantorFunction_half_le_two (f : ℕ → Bool) : cantorFunction (1 / 2) f ≤ 2 := by
  calc cantorFunction (1 / 2) f ≤ cantorFunction (1 / 2) (fun _ => true) :=
        cantorFunction_le (by norm_num) (by norm_num) (fun _ _ => rfl)
    _ = 2 := by
        unfold cantorFunction
        simp only [cantorFunctionAux, Bool.cond_true]
        exact tsum_geometric_two

lemma binExp_nonneg (f : ℕ → Bool) : 0 ≤ binExp f :=
  mul_nonneg (by norm_num) (cantorFunction_half_nonneg f)

lemma binExp_le_one (f : ℕ → Bool) : binExp f ≤ 1 := by
  unfold binExp; linarith [cantorFunction_half_le_two f]

lemma measurable_binExp : Measurable binExp := by
  have hS : ∀ N : ℕ, Measurable fun f : ℕ → Bool =>
      (1 / 2 : ℝ) * ∑ n ∈ Finset.range N, cantorFunctionAux (1 / 2) f n := by
    intro N
    refine (Finset.measurable_sum _ fun n _ => ?_).const_mul _
    exact (measurable_of_countable (fun b : Bool => cond b ((1 / 2 : ℝ) ^ n) 0)).comp
      (measurable_pi_apply n)
  refine measurable_of_tendsto_metrizable hS (tendsto_pi_nhds.mpr fun f => ?_)
  exact ((summable_cantor_function f (by norm_num) (by norm_num)).hasSum.tendsto_sum_nat).const_mul _

lemma measurable_shift : Measurable shift :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

/-! ### The product structure: `f 0` and `shift f` are independent, `shift` is measure preserving -/

lemma map_eval_zero : cantorMeasure.map (fun f : ℕ → Bool => f 0) = fairCoin := by
  unfold cantorMeasure
  exact Measure.infinitePi_map_eval _ 0

lemma iIndepFun_eval_cantor :
    iIndepFun (fun (n : ℕ) (f : ℕ → Bool) => f n) cantorMeasure := by
  unfold cantorMeasure
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) => (id : Bool → Bool)) (fun _ => measurable_id)

lemma map_shift : cantorMeasure.map shift = cantorMeasure := by
  have h : iIndepFun (fun n (f : ℕ → Bool) => f (n + 1)) cantorMeasure :=
    iIndepFun_eval_cantor.precomp Nat.succ_injective
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => measurable_pi_apply (n + 1))] at h
  refine h.trans ?_
  unfold cantorMeasure
  congr 1
  funext n
  exact Measure.infinitePi_map_eval _ (n + 1)

lemma indepFun_zero_shift : IndepFun (fun f : ℕ → Bool => f 0) shift cantorMeasure := by
  have h := iIndepFun_eval_cantor
  rw [iIndepFun_iff_iIndep] at h
  have h2 := indep_iSup_of_disjoint (h_indep := h)
    (h_le := fun i => (measurable_pi_apply i : Measurable fun f : ℕ → Bool => f i).comap_le)
    (S := {0}) (T := Set.range Nat.succ)
    (Set.disjoint_singleton_left.mpr (by rintro ⟨n, hn⟩; exact Nat.succ_ne_zero n hn))
  rw [IndepFun_iff_Indep]
  convert h2 using 1
  · rw [iSup_singleton]
  · rw [iSup_range]
    show MeasurableSpace.comap shift MeasurableSpace.pi = _
    unfold MeasurableSpace.pi
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    rfl

/-- The joint law of `(f 0, shift f)` under the coin measure is `fairCoin ⊗ cantorMeasure`. -/
lemma map_zero_shift :
    cantorMeasure.map (fun f => (f 0, shift f)) = fairCoin.prod cantorMeasure := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_shift.aemeasurable).mp indepFun_zero_shift, map_shift, map_eval_zero]

/-! ### The distribution function `F t = cantorMeasure {f | binExp f ≤ t}` -/

/-- The distribution function of `binExp`. -/
noncomputable def F (t : ℝ) : ℝ≥0∞ := cantorMeasure {f | binExp f ≤ t}

lemma F_le_one (t : ℝ) : F t ≤ 1 := prob_le_one

lemma F_ne_top (t : ℝ) : F t ≠ ∞ := ((F_le_one t).trans_lt ENNReal.one_lt_top).ne

lemma F_mono {a b : ℝ} (hab : a ≤ b) : F a ≤ F b :=
  measure_mono fun f (hf : binExp f ≤ a) => hf.trans hab

lemma F_neg {t : ℝ} (ht : t < 0) : F t = 0 := by
  unfold F
  have hE : {f | binExp f ≤ t} = ∅ := Set.eq_empty_of_forall_notMem fun f hf =>
    ((hf : binExp f ≤ t).trans_lt ht).not_ge (binExp_nonneg f)
  rw [hE, measure_empty]

lemma F_ge_one {t : ℝ} (ht : 1 ≤ t) : F t = 1 := by
  unfold F
  have hU : {f | binExp f ≤ t} = Set.univ :=
    Set.eq_univ_of_forall fun f => (binExp_le_one f).trans ht
  rw [hU, measure_univ]

/-- The self-similarity of the distribution function. -/
lemma F_rec (t : ℝ) : F t = 2⁻¹ * F (2 * t - 1) + 2⁻¹ * F (2 * t) := by
  unfold F
  set B : Set (Bool × (ℕ → Bool)) := {p | (cond p.1 1 0) / 2 + binExp p.2 / 2 ≤ t} with hBdef
  have hset : {f | binExp f ≤ t} = (fun f => (f 0, shift f)) ⁻¹' B := by
    ext f
    simp only [mem_setOf_eq, mem_preimage, B]
    rw [binExp_succ f]
  have hB : MeasurableSet B :=
    measurableSet_le ((((measurable_of_countable fun b : Bool => (cond b (1 : ℝ) 0)).comp
      measurable_fst).div_const 2).add ((measurable_binExp.comp measurable_snd).div_const 2))
      measurable_const
  rw [hset, ← Measure.map_apply ((measurable_pi_apply 0).prodMk measurable_shift) hB,
    map_zero_shift, Measure.prod_apply hB]
  simp only [fairCoin]
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac,
    smul_eq_mul, mul_add]
  congr 2
  · congr 1
    ext g
    simp only [mem_preimage, mem_setOf_eq, B, Bool.cond_true]
    constructor <;> intro h <;> linarith
  · congr 1
    ext g
    simp only [mem_preimage, mem_setOf_eq, B, Bool.cond_false]
    constructor <;> intro h <;> linarith

lemma F_zero : F 0 = 0 := by
  have h := F_rec 0
  rw [show (2 : ℝ) * 0 - 1 = -1 by norm_num, show (2 : ℝ) * 0 = 0 by norm_num,
    F_neg (by norm_num : (-1 : ℝ) < 0), mul_zero, zero_add] at h
  have h' : (F 0).toReal = 2⁻¹ * (F 0).toReal := by
    conv_lhs => rw [h]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have h0 : (F 0).toReal = 0 := by linarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right (F_ne_top 0)

/-- `F` takes the value `k/2ⁿ` at the dyadic rational `k/2ⁿ`, `k ≤ 2ⁿ`. -/
lemma F_dyadic : ∀ n k : ℕ, k ≤ 2 ^ n → F ((k : ℝ) / 2 ^ n) = ENNReal.ofReal ((k : ℝ) / 2 ^ n) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    · simp [F_zero]
    · simp [F_ge_one le_rfl]
  | succ n ih =>
    intro k hk
    have h2 : (2 : ℝ) * ((k : ℝ) / 2 ^ (n + 1)) = (k : ℝ) / 2 ^ n := by
      field_simp; ring
    rw [F_rec, h2]
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rcases le_or_gt k (2 ^ n) with hle | hlt
    · -- `k / 2ⁿ ≤ 1`: the first term vanishes
      have h0 : F ((k : ℝ) / 2 ^ n - 1) = 0 := by
        have hle' : (k : ℝ) / 2 ^ n - 1 ≤ 0 := by
          rw [sub_nonpos, div_le_one hpos]; exact_mod_cast hle
        rcases hle'.lt_or_eq with h | h
        · exact F_neg h
        · rw [h]; exact F_zero
      rw [h0, ih k hle, mul_zero, zero_add,
        show (k : ℝ) / 2 ^ (n + 1) = 2⁻¹ * ((k : ℝ) / 2 ^ n) by field_simp; ring,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_ofNat]
    · -- `k / 2ⁿ > 1`: the second term is `1`, the first is `F ((k - 2ⁿ) / 2ⁿ)`
      have h1 : F ((k : ℝ) / 2 ^ n) = 1 :=
        F_ge_one (by rw [le_div_iff₀ hpos, one_mul]; exact_mod_cast hlt.le)
      have hk' : k - 2 ^ n ≤ 2 ^ n := by
        rw [pow_succ] at hk; omega
      have hcast : (k : ℝ) / 2 ^ n - 1 = ((k - 2 ^ n : ℕ) : ℝ) / 2 ^ n := by
        rw [Nat.cast_sub hlt.le, Nat.cast_pow, Nat.cast_ofNat]; field_simp
      rw [h1, hcast, ih _ hk', mul_one]
      rw [show (k : ℝ) / 2 ^ (n + 1) = 2⁻¹ * (((k - 2 ^ n : ℕ) : ℝ) / 2 ^ n) + 2⁻¹ by
            rw [Nat.cast_sub hlt.le, Nat.cast_pow, Nat.cast_ofNat]; field_simp; ring,
        ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

/-- `F t = t` on `[0, 1)`. -/
lemma F_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : F t = ENNReal.ofReal t := by
  -- squeeze between the dyadic values `⌊t 2ⁿ⌋/2ⁿ ≤ t < (⌊t 2ⁿ⌋ + 1)/2ⁿ`
  have key : ∀ n : ℕ, t - 1 / 2 ^ n ≤ (F t).toReal ∧ (F t).toReal ≤ t + 1 / 2 ^ n := by
    intro n
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    set k := ⌊t * 2 ^ n⌋₊ with hk
    have hk1 : (k : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by positivity)
    have hk2 : t * 2 ^ n < k + 1 := Nat.lt_floor_add_one _
    have hkn : k + 1 ≤ 2 ^ n := by
      have hlt : (k : ℝ) < 2 ^ n := hk1.trans_lt (by nlinarith)
      have : k < 2 ^ n := by exact_mod_cast hlt
      omega
    have hlo : (k : ℝ) / 2 ^ n ≤ t := by rw [div_le_iff₀ hpos]; exact hk1
    have hhi : t ≤ ((k + 1 : ℕ) : ℝ) / 2 ^ n := by
      rw [le_div_iff₀ hpos]; push_cast; exact hk2.le
    have hd1 := F_dyadic n k (by omega)
    have hd2 := F_dyadic n (k + 1) hkn
    have hhi' : t ≤ (k : ℝ) / 2 ^ n + 1 / 2 ^ n := by
      rw [← add_div, le_div_iff₀ hpos]; exact hk2.le
    have hcast : (((k + 1 : ℕ) : ℝ) / 2 ^ n) = (k : ℝ) / 2 ^ n + 1 / 2 ^ n := by
      push_cast; rw [add_div]
    constructor
    · have : ENNReal.ofReal ((k : ℝ) / 2 ^ n) ≤ F t := hd1 ▸ F_mono hlo
      have h' := (ENNReal.ofReal_le_iff_le_toReal (F_ne_top t)).mp this
      linarith
    · have : F t ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) / 2 ^ n) := hd2 ▸ F_mono hhi
      have h' := ENNReal.toReal_le_of_le_ofReal (by positivity) this
      linarith
  have hlim : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, (1 : ℝ) / 2 ^ n < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by rw [one_div_pow] at hn; exact hn⟩
  have hreal : (F t).toReal = t := by
    apply le_antisymm
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      obtain ⟨n, hn⟩ := hlim (a - t) (by linarith)
      linarith [(key n).2]
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      obtain ⟨n, hn⟩ := hlim (a - (F t).toReal) (by linarith)
      linarith [(key n).1]
  calc F t = ENNReal.ofReal (F t).toReal := (ENNReal.ofReal_toReal (F_ne_top t)).symm
    _ = ENNReal.ofReal t := by rw [hreal]

/-! ### The main theorem -/

/-- **Binary expansion is measure preserving**: the coin measure on `2^ω` pushed forward by
`binExp` is Lebesgue measure on `[0, 1)`. -/
theorem map_binExp : cantorMeasure.map binExp = volume.restrict (Ico (0 : ℝ) 1) := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply measurable_binExp measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  show F t = volume (Iic t ∩ Ico (0 : ℝ) 1)
  rcases lt_or_ge t 0 with h | h
  · rw [F_neg h, show Iic t ∩ Ico (0 : ℝ) 1 = ∅ from
      Set.eq_empty_of_forall_notMem fun x hx => by
        have h1 : x ≤ t := Set.mem_Iic.mp hx.1
        have h2 : 0 ≤ x := hx.2.1
        linarith, measure_empty]
  rcases lt_or_ge t 1 with h1 | h1
  · rw [F_eq h h1, show Iic t ∩ Ico (0 : ℝ) 1 = Icc 0 t from by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]; constructor
        · rintro ⟨hx1, hx2, -⟩; exact ⟨hx2, hx1⟩
        · rintro ⟨hx1, hx2⟩; exact ⟨hx2, hx1, by linarith⟩,
      Real.volume_Icc, sub_zero]
  · rw [F_ge_one h1, show Iic t ∩ Ico (0 : ℝ) 1 = Ico 0 1 from by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Ico]; constructor
        · rintro ⟨-, hx⟩; exact hx
        · rintro ⟨hx1, hx2⟩; exact ⟨by linarith, hx1, hx2⟩,
      Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

/-- **(P2) for the profile test points**, unconditionally: on `2^P` with the product coin measure,
`z ↦ m + binExp (z 0)` has law Lebesgue measure on `[m, m + 1)`. -/
theorem map_profileTest_binExp (m : ℤ) :
    (Measure.infinitePi (fun _ : ℕ => cantorMeasure)).map
        (fun z : ℕ → (ℕ → Bool) => (m : ℝ) + binExp (z 0)) =
      volume.restrict (Ico (m : ℝ) (m + 1)) :=
  map_profileTest measurable_binExp map_binExp m

end Flypitch.Erdos501.ZFCCore
