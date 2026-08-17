/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the negative resolution of Erdős Problem 868 by
Daniel Larsen and Michael Larsen.

Mathematical proof and formalization notes: ../../../tex/868.tex
Primary source: https://github.com/Larsen-Daniel/Erdos-868/blob/main/868.pdf
-/

import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Cofinite
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Basic

open Filter
open scoped Pointwise

namespace Set

variable {M : Type*} [AddCommMonoid M]

/-- An asymptotic additive basis of order `o`: its `o`-fold pointwise sum is cofinite.

This is the definition from
`FormalConjecturesForMathlib.Combinatorics.Additive.Basis`; the local Mathlib
snapshot does not yet contain that file. -/
def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

lemma isAsymptoticAddBasisOfOrder_iff_atTop {A : Set ℕ} {o : ℕ} :
    A.IsAsymptoticAddBasisOfOrder o ↔ ∀ᶠ m in atTop, m ∈ o • A := by
  rw [IsAsymptoticAddBasisOfOrder, Nat.cofinite_eq_atTop]

end Set

namespace Erdos868

/-! ## Doubly exponential block scale -/

/-- The Larsen--Larsen scale `Xₙ = 2^(2^n)`. -/
def X (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- The integer block `[Xₙ, Xₙ₊₁)`. -/
def block (n : ℕ) : Finset ℕ := Finset.Ico (X n) (X (n + 1))

lemma X_pos (n : ℕ) : 0 < X n := by
  exact pow_pos (by decide) _

lemma X_ne_zero (n : ℕ) : X n ≠ 0 := (X_pos n).ne'

lemma X_succ (n : ℕ) : X (n + 1) = (X n) ^ 2 := by
  simp [X, pow_succ, pow_mul]

lemma X_strictMono : StrictMono X := by
  intro a b hab
  apply pow_lt_pow_right₀ (by decide)
  exact pow_lt_pow_right₀ (by decide) hab

lemma X_mono : Monotone X := X_strictMono.monotone

lemma mem_block {n m : ℕ} : m ∈ block n ↔ X n ≤ m ∧ m < X (n + 1) := by
  simp [block]

lemma block_disjoint {m n : ℕ} (hmn : m ≠ n) : Disjoint (block m) (block n) := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [Finset.disjoint_left]
    intro x hxm hxn
    have hm := mem_block.1 hxm
    have hn := mem_block.1 hxn
    exact (Nat.not_lt_of_ge hn.1) (hm.2.trans_le (X_mono (Nat.succ_le_iff.2 h)))
  · exact (block_disjoint hmn.symm).symm

/-! ## The independent Bernoulli reservoir -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases n with _ | n
  · simp
  · apply Real.log_nonneg
    exact_mod_cast Nat.succ_pos n

/-- The Larsen--Larsen selection probability
`min 1 (40 * sqrt (log n / n))`. -/
noncomputable def selectionProbReal (n : ℕ) : ℝ :=
  min 1 (40 * Real.sqrt (Real.log n / n))

lemma selectionProbReal_nonneg (n : ℕ) : 0 ≤ selectionProbReal n := by
  rw [selectionProbReal]
  apply le_min (by positivity)
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

lemma selectionProbReal_le_one (n : ℕ) : selectionProbReal n ≤ 1 :=
  min_le_left _ _

noncomputable def selectionProb (n : ℕ) : {x : ℝ // x ∈ Set.Icc 0 1} :=
  ⟨selectionProbReal n, selectionProbReal_nonneg n, selectionProbReal_le_one n⟩

/-- The sample space carrying all independent membership bits. -/
abbrev ReservoirSample := ℕ → Bool

noncomputable def coordinateMeasure (n : ℕ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (selectionProb n)

noncomputable instance (n : ℕ) : IsProbabilityMeasure (coordinateMeasure n) := by
  unfold coordinateMeasure
  infer_instance

noncomputable def reservoirMeasure : Measure ReservoirSample :=
  Measure.infinitePi coordinateMeasure

def membershipBit (n : ℕ) (ω : ReservoirSample) : Bool := ω n

lemma membershipBit_measurable (n : ℕ) : Measurable (membershipBit n) := by
  change Measurable (fun ω : ℕ → Bool ↦ ω n)
  exact measurable_pi_apply n

lemma membershipBit_iIndep : iIndepFun membershipBit reservoirMeasure := by
  change iIndepFun (fun i (ω : ℕ → Bool) ↦ ω i) (Measure.infinitePi coordinateMeasure)
  exact iIndepFun_infinitePi (P := coordinateMeasure) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)

lemma membershipBit_true_probability (n : ℕ) :
    reservoirMeasure.real {ω | membershipBit n ω = true} = selectionProbReal n := by
  change reservoirMeasure.real ((membershipBit n) ⁻¹' {true}) = selectionProbReal n
  rw [← map_measureReal_apply (membershipBit_measurable n) (MeasurableSet.singleton true)]
  change ((Measure.infinitePi coordinateMeasure).map
    (fun ω : ℕ → Bool ↦ ω n)).real {true} = _
  rw [Measure.infinitePi_map_eval]
  simp [coordinateMeasure, selectionProb]

/-- Regrouping mutually independent scalar random variables along disjoint fibres
preserves independence.  Mathlib contains the converse uncurrying lemma; this is
the direction needed to group the two endpoints of each additive representation. -/
lemma iIndepFun_curry_of_uncurry {ι : Type*} {κ : ι → Type*}
    {Ω' : Type*} [MeasurableSpace Ω']
    {𝓧 : (i : ι) → κ i → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}
    {P : Measure Ω'} {Y : (i : ι) → (j : κ i) → Ω' → 𝓧 i j}
    (mY : ∀ i j, Measurable (Y i j))
    (h : iIndepFun (fun (p : (i : ι) × κ i) ω ↦ Y p.1 p.2 ω) P) :
    iIndepFun (fun i ω ↦ (Y i · ω)) P := by
  let F : (p : (i : ι) × κ i) → Ω' → 𝓧 p.1 p.2 :=
    fun p ω ↦ Y p.1 p.2 ω
  have hP : IsProbabilityMeasure P := h.isProbabilityMeasure
  have : ∀ i j, IsProbabilityMeasure (P.map (Y i j)) :=
    fun i j ↦ Measure.isProbabilityMeasure_map (mY i j).aemeasurable
  have hmF : ∀ p, Measurable (F p) := fun p ↦ mY p.1 p.2
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  apply (MeasurableEquiv.piCurry 𝓧).symm.map_measurableEquiv_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change P.map (fun ω p ↦ F p ω) =
    (Measure.infinitePi fun i ↦ P.map (fun ω j ↦ Y i j ω)).map
      (MeasurableEquiv.piCurry 𝓧).symm
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map hmF).1 h]
  have h_group : ∀ i,
      P.map (fun ω j ↦ Y i j ω) = Measure.infinitePi (fun j ↦ P.map (Y i j)) := by
    intro i
    have hi : iIndepFun (Y i) P := by
      apply iIndepFun.precomp (g := fun j : κ i ↦ Sigma.mk i j) (f := F)
      · intro a b hab
        cases hab
        rfl
      · exact h
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (mY i)).1 hi
  simp_rw [h_group]
  simpa [F] using
    (Measure.infinitePi_map_piCurry_symm (fun i j ↦ P.map (Y i j))).symm

/-- Strict unordered representations `i + (m-i) = m`, with both endpoints
at least `lo` and with the smaller endpoint listed first. -/
noncomputable def strictReprIndices (lo m : ℕ) : Finset ℕ :=
  (Finset.Icc lo m).filter (fun i ↦ 2 * i < m)

/-- The two membership coordinates belonging to a strict unordered
representation. -/
def reprEndpoint (lo m : ℕ) (p : (i : strictReprIndices lo m) × Fin 2) : ℕ :=
  if p.2 = 0 then p.1 else m - p.1

lemma reprEndpoint_injective (lo m : ℕ) : Function.Injective (reprEndpoint lo m) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ huv
  have hi : 2 * (i : ℕ) < m := (Finset.mem_filter.1 i.property).2
  have hj : 2 * (j : ℕ) < m := (Finset.mem_filter.1 j.property).2
  have him : (i : ℕ) ≤ m := by omega
  have hjm : (j : ℕ) ≤ m := by omega
  have hij : (i : ℕ) = (j : ℕ) := by
    fin_cases u <;> fin_cases v
    · simpa [reprEndpoint] using huv
    · simp [reprEndpoint] at huv
      have hs : m - (j : ℕ) + (j : ℕ) = m := Nat.sub_add_cancel hjm
      omega
    · simp [reprEndpoint] at huv
      have hs : m - (i : ℕ) + (i : ℕ) = m := Nat.sub_add_cancel him
      omega
    · simp [reprEndpoint] at huv
      have hsi : m - (i : ℕ) + (i : ℕ) = m := Nat.sub_add_cancel him
      have hsj : m - (j : ℕ) + (j : ℕ) = m := Nat.sub_add_cancel hjm
      omega
  have hij' : i = j := Subtype.ext hij
  subst j
  have huv' : u = v := by
    fin_cases u <;> fin_cases v <;> simp [reprEndpoint] at huv ⊢ <;> omega
  subst v
  rfl

/-- Indicator that both endpoints of one strict unordered representation
belong to the reservoir. -/
def pairPresent (lo m : ℕ) (i : strictReprIndices lo m)
    (ω : ReservoirSample) : Bool :=
  membershipBit i ω && membershipBit (m - i) ω

lemma pairPresent_measurable (lo m : ℕ) (i : strictReprIndices lo m) :
    Measurable (pairPresent lo m i) := by
  unfold pairPresent
  simpa only [Function.comp_def] using
    (measurable_of_finite (fun x : Bool × Bool ↦ x.1 && x.2)).comp
      ((membershipBit_measurable i).prodMk (membershipBit_measurable (m - i)))

/-- For a fixed target sum, its strict unordered representation indicators
are mutually independent: distinct pairs have disjoint endpoints. -/
lemma pairPresent_iIndep (lo m : ℕ) :
    iIndepFun (pairPresent lo m) reservoirMeasure := by
  let Y : (i : strictReprIndices lo m) → (j : Fin 2) → ReservoirSample → Bool :=
    fun i j ω ↦ membershipBit (reprEndpoint lo m ⟨i, j⟩) ω
  have hflat : iIndepFun
      (fun (p : (i : strictReprIndices lo m) × Fin 2) ω ↦ Y p.1 p.2 ω)
      reservoirMeasure := by
    exact iIndepFun.precomp (reprEndpoint_injective lo m) membershipBit_iIndep
  have hgroup : iIndepFun (fun i ω ↦ (Y i · ω)) reservoirMeasure :=
    iIndepFun_curry_of_uncurry
      (fun i j ↦ membershipBit_measurable (reprEndpoint lo m ⟨i, j⟩)) hflat
  have hcomp := hgroup.comp (fun _ x ↦ x 0 && x 1) (fun _ ↦ by fun_prop)
  unfold pairPresent
  change iIndepFun (fun (i : strictReprIndices lo m) ω ↦
    membershipBit (i : ℕ) ω && membershipBit (m - (i : ℕ)) ω) reservoirMeasure
  convert hcomp using 1
  funext i ω
  simp [Y, reprEndpoint]

lemma selectionProbReal_formula_eventually :
    ∀ᶠ n : ℕ in atTop,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n) := by
  have hreal : Tendsto (fun x : ℝ ↦ 40 * Real.sqrt (Real.log x / x))
      atTop (nhds 0) := by
    simpa using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.sqrt.const_mul 40)
  have hnat : Tendsto (fun n : ℕ ↦ 40 * Real.sqrt (Real.log n / n))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ ↦ 40 * Real.sqrt (Real.log x / x)) ∘
      fun n : ℕ ↦ (n : ℝ)) atTop (nhds 0)
    exact hreal.comp tendsto_natCast_atTop_atTop
  have hlt : ∀ᶠ n : ℕ in atTop,
      40 * Real.sqrt (Real.log n / n) < 1 :=
    (tendsto_order.1 hnat).2 1 (by norm_num)
  filter_upwards [hlt] with n hn
  rw [selectionProbReal, min_eq_right hn.le]

def middleIndexEmbedding (m : ℕ) :
    Fin (m / 10) ↪ strictReprIndices (m / 3) m where
  toFun k := ⟨m / 3 + k, by
    change m / 3 + (k : ℕ) ∈
      (Finset.Icc (m / 3) m).filter (fun i ↦ 2 * i < m)
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simp only [Subtype.mk.injEq] at hij
    omega

lemma ten_card_strictReprIndices_ge (m : ℕ) :
    m / 10 ≤ Fintype.card (strictReprIndices (m / 3) m) := by
  simpa using Fintype.card_le_of_injective _ (middleIndexEmbedding m).injective

noncomputable def pairProbability (lo m : ℕ) (i : strictReprIndices lo m) :
    {x : ℝ // x ∈ Set.Icc 0 1} :=
  ⟨selectionProbReal i * selectionProbReal (m - i),
    mul_nonneg (selectionProbReal_nonneg _) (selectionProbReal_nonneg _),
    mul_le_one₀ (selectionProbReal_le_one _) (selectionProbReal_nonneg _)
      (selectionProbReal_le_one _)⟩

noncomputable def pairMean (lo m : ℕ) : ℝ :=
  ∑ i : strictReprIndices lo m, (pairProbability lo m i : ℝ)

lemma log_div_cast_le_log_div_cast {m n : ℕ} (hm : 1 ≤ m / 3)
    (hlo : m / 3 ≤ n) (hhi : n ≤ m) :
    Real.log (m / 3 : ℕ) / (m : ℝ) ≤ Real.log n / (n : ℝ) := by
  have hm3pos : (0 : ℝ) < (m / 3 : ℕ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hlo
  have hmpos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt hm) (hlo.trans hhi)
  have hlog : Real.log (m / 3 : ℕ) ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn hm3pos hnpos (by exact_mod_cast hlo)
  calc
    Real.log (m / 3 : ℕ) / (m : ℝ) ≤ Real.log n / (m : ℝ) :=
      div_le_div_of_nonneg_right hlog hmpos.le
    _ ≤ Real.log n / (n : ℝ) := by
      exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hlo.trans' hm))
        hnpos (by exact_mod_cast hhi)

lemma pairProbability_lower_bound (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 3 (3 * N) ≤ m) (i : strictReprIndices (m / 3) m) :
    1600 * (Real.log (m / 3 : ℕ) / (m : ℝ)) ≤
      (pairProbability (m / 3) m i : ℝ) := by
  have hi_mem := (Finset.mem_filter.1 i.property)
  have hilo : m / 3 ≤ (i : ℕ) := (Finset.mem_Icc.1 hi_mem.1).1
  have hihi : (i : ℕ) ≤ m := (Finset.mem_Icc.1 hi_mem.1).2
  have histrict : 2 * (i : ℕ) < m := hi_mem.2
  have hjlo : m / 3 ≤ m - (i : ℕ) := by omega
  have hjhi : m - (i : ℕ) ≤ m := Nat.sub_le _ _
  have hmthird : N ≤ m / 3 := by omega
  have hiN : N ≤ (i : ℕ) := hmthird.trans hilo
  have hjN : N ≤ m - (i : ℕ) := hmthird.trans hjlo
  have hmone : 1 ≤ m / 3 := by omega
  let q : ℝ := Real.log (m / 3 : ℕ) / (m : ℝ)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hri : q ≤ Real.log (i : ℕ) / (i : ℝ) :=
    log_div_cast_le_log_div_cast hmone hilo hihi
  have hrj : q ≤ Real.log ((m - (i : ℕ) : ℕ) : ℝ) /
      ((m - (i : ℕ) : ℕ) : ℝ) :=
    log_div_cast_le_log_div_cast hmone hjlo hjhi
  have hsqi := Real.sqrt_le_sqrt hri
  have hsqj := Real.sqrt_le_sqrt hrj
  have hprod : Real.sqrt q * Real.sqrt q ≤
      Real.sqrt (Real.log (i : ℕ) / (i : ℝ)) *
        Real.sqrt (Real.log ((m - (i : ℕ) : ℕ) : ℝ) /
          ((m - (i : ℕ) : ℕ) : ℝ)) :=
    mul_le_mul hsqi hsqj (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.mul_self_sqrt hq0] at hprod
  change 1600 * (Real.log (m / 3 : ℕ) / (m : ℝ)) ≤
    selectionProbReal (i : ℕ) * selectionProbReal (m - (i : ℕ))
  rw [hformula _ hiN, hformula _ hjN]
  nlinarith

lemma pairMean_lower_bound (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 20 (3 * N) ≤ m) :
    80 * Real.log (m / 3 : ℕ) ≤ pairMean (m / 3) m := by
  let q : ℝ := Real.log (m / 3 : ℕ) / (m : ℝ)
  have hm3 : max 3 (3 * N) ≤ m := by omega
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsum :
      (Fintype.card (strictReprIndices (m / 3) m) : ℝ) * (1600 * q) ≤
        pairMean (m / 3) m := by
    unfold pairMean
    calc
      (Fintype.card (strictReprIndices (m / 3) m) : ℝ) * (1600 * q) =
          ∑ _i : strictReprIndices (m / 3) m, 1600 * q := by simp
      _ ≤ ∑ i : strictReprIndices (m / 3) m,
          (pairProbability (m / 3) m i : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact pairProbability_lower_bound N m hformula hm3 i
  have hcardNat := ten_card_strictReprIndices_ge m
  have hfloor : m ≤ 20 * (m / 10) := by omega
  have hcard : (m : ℝ) / 20 ≤
      (Fintype.card (strictReprIndices (m / 3) m) : ℝ) := by
    have hfloorR : (m : ℝ) ≤ 20 * (m / 10 : ℕ) := by exact_mod_cast hfloor
    have hcardR : (m / 10 : ℕ) ≤
        (Fintype.card (strictReprIndices (m / 3) m) : ℝ) := by
      exact_mod_cast hcardNat
    nlinarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hqm : q * (m : ℝ) = Real.log (m / 3 : ℕ) := by
    dsimp [q]
    field_simp
  nlinarith

lemma strictRepr_left_ne_right (lo m : ℕ) (i : strictReprIndices lo m) :
    (i : ℕ) ≠ m - (i : ℕ) := by
  have hi : 2 * (i : ℕ) < m := (Finset.mem_filter.1 i.property).2
  have him : (i : ℕ) ≤ m := by omega
  intro h
  have hs : m - (i : ℕ) + (i : ℕ) = m := Nat.sub_add_cancel him
  omega

lemma pairPresent_true_probability (lo m : ℕ) (i : strictReprIndices lo m) :
    reservoirMeasure.real {ω | pairPresent lo m i ω = true} =
      selectionProbReal i * selectionProbReal (m - i) := by
  have hind := membershipBit_iIndep.indepFun (strictRepr_left_ne_right lo m i)
  have h := hind.measure_inter_preimage_eq_mul {true} {true}
    (MeasurableSet.singleton true) (MeasurableSet.singleton true)
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul] at hr
  change reservoirMeasure.real
      (membershipBit i ⁻¹' {true} ∩ membershipBit (m - i) ⁻¹' {true}) =
    reservoirMeasure.real (membershipBit i ⁻¹' {true}) *
      reservoirMeasure.real (membershipBit (m - i) ⁻¹' {true}) at hr
  have hpi : reservoirMeasure.real (membershipBit i ⁻¹' {true}) =
      selectionProbReal i := by
    rw [show membershipBit i ⁻¹' {true} =
        {ω | membershipBit i ω = true} by ext ω; simp]
    exact membershipBit_true_probability i
  have hpj : reservoirMeasure.real (membershipBit (m - i) ⁻¹' {true}) =
      selectionProbReal (m - i) := by
    rw [show membershipBit (m - i) ⁻¹' {true} =
        {ω | membershipBit (m - i) ω = true} by ext ω; simp]
    exact membershipBit_true_probability (m - i)
  rw [hpi, hpj] at hr
  rw [show {ω | pairPresent lo m i ω = true} =
      membershipBit i ⁻¹' {true} ∩ membershipBit (m - i) ⁻¹' {true} by
    ext ω
    simp [pairPresent]]
  exact hr

noncomputable local instance : IsProbabilityMeasure reservoirMeasure := by
  unfold reservoirMeasure
  infer_instance

def boolIndicator (X : ReservoirSample → Bool) (ω : ReservoirSample) : ℝ :=
  if X ω then 1 else 0

lemma boolIndicator_measurable {Y : ReservoirSample → Bool} (hY : Measurable Y) :
    Measurable (boolIndicator Y) := by
  exact (measurable_of_finite (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp hY

lemma pairPresent_map (lo m : ℕ) (i : strictReprIndices lo m) :
    reservoirMeasure.map (pairPresent lo m i) =
      ProbabilityTheory.bernoulliMeasure true false (pairProbability lo m i) := by
  letI : IsProbabilityMeasure (reservoirMeasure.map (pairPresent lo m i)) :=
    Measure.isProbabilityMeasure_map (pairPresent_measurable lo m i).aemeasurable
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (pairPresent_measurable lo m i) (MeasurableSet.singleton b)]
  cases b with
  | false =>
      have hcompl : {ω | pairPresent lo m i ω = false} =
          {ω | pairPresent lo m i ω = true}ᶜ := by
        ext ω
        cases h : pairPresent lo m i ω <;> simp [h]
      rw [show (pairPresent lo m i ⁻¹' {false}) =
          {ω | pairPresent lo m i ω = false} by rfl, hcompl,
        measureReal_compl (μ := reservoirMeasure)
          (s := {ω | pairPresent lo m i ω = true})
          (pairPresent_measurable lo m i (MeasurableSet.singleton true))]
      simp [pairProbability, pairPresent_true_probability]
  | true =>
      rw [show (pairPresent lo m i ⁻¹' {true}) =
          {ω | pairPresent lo m i ω = true} by ext ω; simp]
      simpa [pairProbability] using pairPresent_true_probability lo m i

lemma pairIndicator_mgf (lo m : ℕ) (i : strictReprIndices lo m) (t : ℝ) :
    mgf (boolIndicator (pairPresent lo m i)) reservoirMeasure t =
      (1 - pairProbability lo m i : ℝ) +
        (pairProbability lo m i : ℝ) * Real.exp t := by
  unfold boolIndicator
  change mgf ((fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ pairPresent lo m i)
    reservoirMeasure t = _
  rw [← mgf_map (Y := pairPresent lo m i)
    (pairPresent_measurable lo m i).aemeasurable (by fun_prop)]
  rw [pairPresent_map]
  rw [mgf]
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simp [boolIndicator, mul_comm, add_comm]

noncomputable def pairSum (lo m : ℕ) (ω : ReservoirSample) : ℝ :=
  ∑ i : strictReprIndices lo m, boolIndicator (pairPresent lo m i) ω

lemma pairIndicator_iIndep (lo m : ℕ) :
    iIndepFun (fun i ↦ boolIndicator (pairPresent lo m i)) reservoirMeasure := by
  have h := (pairPresent_iIndep lo m).comp (γ := fun _ ↦ ℝ)
    (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)
  unfold boolIndicator
  change iIndepFun (fun i ω ↦ if pairPresent lo m i ω then (1 : ℝ) else 0)
    reservoirMeasure
  exact h

lemma pairIndicator_measurable (lo m : ℕ) (i : strictReprIndices lo m) :
    Measurable (boolIndicator (pairPresent lo m i)) :=
  boolIndicator_measurable (pairPresent_measurable lo m i)

lemma pairSum_measurable (lo m : ℕ) : Measurable (pairSum lo m) := by
  unfold pairSum
  apply Finset.measurable_sum Finset.univ
  intro i hi
  exact pairIndicator_measurable lo m i

lemma pairSum_mgf_le (lo m : ℕ) (t : ℝ) :
    mgf (pairSum lo m) reservoirMeasure t ≤
      Real.exp ((Real.exp t - 1) * pairMean lo m) := by
  unfold pairSum
  calc
    mgf (fun ω ↦ ∑ i : strictReprIndices lo m,
        boolIndicator (pairPresent lo m i) ω) reservoirMeasure t =
        ∏ i : strictReprIndices lo m,
          ((1 - pairProbability lo m i : ℝ) +
            (pairProbability lo m i : ℝ) * Real.exp t) := by
          calc
            _ = mgf (∑ i : strictReprIndices lo m,
                boolIndicator (pairPresent lo m i)) reservoirMeasure t := by
                  congr 1
                  funext ω
                  simp
            _ = ∏ i : strictReprIndices lo m,
                mgf (boolIndicator (pairPresent lo m i)) reservoirMeasure t := by
                  simpa using (pairIndicator_iIndep lo m).mgf_sum
                    (fun i ↦ pairIndicator_measurable lo m i) Finset.univ (t := t)
            _ = _ := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  exact pairIndicator_mgf lo m i t
    _ ≤ ∏ i : strictReprIndices lo m,
            Real.exp ((pairProbability lo m i : ℝ) * (Real.exp t - 1)) := by
          apply Finset.prod_le_prod
          · intro i hi
            have hq0 : 0 ≤ (pairProbability lo m i : ℝ) := (pairProbability lo m i).property.1
            have hq1 : (pairProbability lo m i : ℝ) ≤ 1 :=
              (pairProbability lo m i).property.2
            positivity
          · intro i hi
            calc
              (1 - pairProbability lo m i : ℝ) +
                    (pairProbability lo m i : ℝ) * Real.exp t =
                  1 + (pairProbability lo m i : ℝ) * (Real.exp t - 1) := by ring
              _ ≤ Real.exp ((pairProbability lo m i : ℝ) * (Real.exp t - 1)) :=
                by simpa [add_comm] using
                  Real.add_one_le_exp ((pairProbability lo m i : ℝ) * (Real.exp t - 1))
    _ = Real.exp (∑ i : strictReprIndices lo m,
          (pairProbability lo m i : ℝ) * (Real.exp t - 1)) := by
          rw [← Real.exp_sum]
    _ = Real.exp ((Real.exp t - 1) * pairMean lo m) := by
          congr 1
          unfold pairMean
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

lemma pairSum_nonneg (lo m : ℕ) (ω : ReservoirSample) : 0 ≤ pairSum lo m ω := by
  unfold pairSum
  apply Finset.sum_nonneg
  intro i hi
  cases h : pairPresent lo m i ω <;> simp [boolIndicator, h]

lemma pairSum_le_card (lo m : ℕ) (ω : ReservoirSample) :
    pairSum lo m ω ≤ Fintype.card (strictReprIndices lo m) := by
  unfold pairSum
  calc
    (∑ i : strictReprIndices lo m, boolIndicator (pairPresent lo m i) ω)
        ≤ ∑ _i : strictReprIndices lo m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          cases h : pairPresent lo m i ω <;> simp [boolIndicator, h]
    _ = Fintype.card (strictReprIndices lo m) := by simp

lemma pairSum_exp_integrable (lo m : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * pairSum lo m ω)) reservoirMeasure := by
  apply Integrable.of_bound ((pairSum_measurable lo m).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * Fintype.card (strictReprIndices lo m)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h0 := pairSum_nonneg lo m ω
  have hcard := pairSum_le_card lo m ω
  have ht : t ≤ |t| := le_abs_self t
  have habs : 0 ≤ |t| := abs_nonneg t
  nlinarith

lemma pairSum_lower_tail (lo m : ℕ) (a t : ℝ) (ht : t ≤ 0) :
    reservoirMeasure.real {ω | pairSum lo m ω ≤ a} ≤
      Real.exp (-t * a + (Real.exp t - 1) * pairMean lo m) := by
  calc
    reservoirMeasure.real {ω | pairSum lo m ω ≤ a}
        ≤ Real.exp (-t * a) * mgf (pairSum lo m) reservoirMeasure t :=
          measure_le_le_exp_mul_mgf a ht (pairSum_exp_integrable lo m t)
    _ ≤ Real.exp (-t * a) *
          Real.exp ((Real.exp t - 1) * pairMean lo m) := by
          exact mul_le_mul_of_nonneg_left (pairSum_mgf_le lo m t) (Real.exp_nonneg _)
    _ = Real.exp (-t * a + (Real.exp t - 1) * pairMean lo m) := by
          rw [Real.exp_add]

lemma pairSum_upper_tail (lo m : ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    reservoirMeasure.real {ω | a ≤ pairSum lo m ω} ≤
      Real.exp (-t * a + (Real.exp t - 1) * pairMean lo m) := by
  calc
    reservoirMeasure.real {ω | a ≤ pairSum lo m ω}
        ≤ Real.exp (-t * a) * mgf (pairSum lo m) reservoirMeasure t :=
          measure_ge_le_exp_mul_mgf a ht (pairSum_exp_integrable lo m t)
    _ ≤ Real.exp (-t * a) *
          Real.exp ((Real.exp t - 1) * pairMean lo m) := by
          exact mul_le_mul_of_nonneg_left (pairSum_mgf_le lo m t) (Real.exp_nonneg _)
    _ = Real.exp (-t * a + (Real.exp t - 1) * pairMean lo m) := by
          rw [Real.exp_add]

lemma pairMean_nonneg (lo m : ℕ) : 0 ≤ pairMean lo m := by
  unfold pairMean
  apply Finset.sum_nonneg
  intro i hi
  exact (pairProbability lo m i).property.1

lemma pairSum_half_mean_tail (lo m : ℕ) :
    reservoirMeasure.real {ω | pairSum lo m ω ≤ pairMean lo m / 2} ≤
      Real.exp (-(pairMean lo m) / 10) := by
  have hexp : Real.exp (-1) ≤ (2 / 5 : ℝ) := by
    exact Real.exp_neg_one_lt_d9.le.trans (by norm_num)
  calc
    reservoirMeasure.real {ω | pairSum lo m ω ≤ pairMean lo m / 2} ≤
        Real.exp (-(-1 : ℝ) * (pairMean lo m / 2) +
          (Real.exp (-1) - 1) * pairMean lo m) :=
      pairSum_lower_tail lo m (pairMean lo m / 2) (-1) (by norm_num)
    _ ≤ Real.exp (-(pairMean lo m) / 10) := by
      apply Real.exp_le_exp.mpr
      have hmean := pairMean_nonneg lo m
      nlinarith

lemma middle_pairSum_failure_bound (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 20 (3 * N) ≤ m) :
    reservoirMeasure.real
        {ω | pairSum (m / 3) m ω ≤ 40 * Real.log (m / 3 : ℕ)} ≤
      Real.exp (-8 * Real.log (m / 3 : ℕ)) := by
  have hmean := pairMean_lower_bound N m hformula hm
  have hlog : 0 ≤ Real.log (m / 3 : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ m / 3 by omega)
  calc
    reservoirMeasure.real
        {ω | pairSum (m / 3) m ω ≤ 40 * Real.log (m / 3 : ℕ)} ≤
      reservoirMeasure.real
        {ω | pairSum (m / 3) m ω ≤ pairMean (m / 3) m / 2} := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro ω hω
          change pairSum (m / 3) m ω ≤ 40 * Real.log (m / 3 : ℕ) at hω
          change pairSum (m / 3) m ω ≤ pairMean (m / 3) m / 2
          nlinarith
    _ ≤ Real.exp (-(pairMean (m / 3) m) / 10) :=
      pairSum_half_mean_tail (m / 3) m
    _ ≤ Real.exp (-8 * Real.log (m / 3 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

def reprBad (m : ℕ) : Set ReservoirSample :=
  {ω | pairSum (m / 3) m ω ≤ 40 * Real.log (m / 3 : ℕ)}

lemma reprBad_measurable (m : ℕ) : MeasurableSet (reprBad m) := by
  exact measurableSet_le (pairSum_measurable (m / 3) m) measurable_const

def stageBad (n : ℕ) : Set ReservoirSample :=
  ⋃ m ∈ block n, reprBad m

lemma stageBad_measurable (n : ℕ) : MeasurableSet (stageBad n) := by
  unfold stageBad
  exact Finset.measurableSet_biUnion (block n) fun m hm ↦ reprBad_measurable m

lemma stageBad_measureReal_le_sum (n : ℕ) :
    reservoirMeasure.real (stageBad n) ≤
      ∑ m ∈ block n, reservoirMeasure.real (reprBad m) := by
  exact measureReal_biUnion_finset_le (block n) reprBad

lemma half_log_le_log_third {m : ℕ} (hm : 16 ≤ m) :
    Real.log (m : ℝ) / 2 ≤ Real.log (m / 3 : ℕ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hthirdpos : (0 : ℝ) < (m / 3 : ℕ) := by
    exact_mod_cast (show 0 < m / 3 by omega)
  have hfloorNat : m ≤ 4 * (m / 3) := by omega
  have hfloor : (m : ℝ) / 4 ≤ (m / 3 : ℕ) := by
    have hfloorR : (m : ℝ) ≤ 4 * (m / 3 : ℕ) := by exact_mod_cast hfloorNat
    linarith
  have hdivpos : (0 : ℝ) < (m : ℝ) / 4 := div_pos hmpos (by norm_num)
  have hlogfloor : Real.log ((m : ℝ) / 4) ≤ Real.log (m / 3 : ℕ) :=
    Real.strictMonoOn_log.monotoneOn hdivpos hthirdpos hfloor
  have hsixteen : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogsixteen : Real.log (16 : ℝ) ≤ Real.log m :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hmpos hsixteen
  have hlogfour : 2 * Real.log (4 : ℝ) ≤ Real.log m := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow] at hlogsixteen
    norm_num at hlogsixteen ⊢
    exact hlogsixteen
  rw [Real.log_div (by positivity) (by norm_num)] at hlogfloor
  norm_num at hlogfloor
  nlinarith

lemma exp_neg_four_log_nat {m : ℕ} (hm : 0 < m) :
    Real.exp (-4 * Real.log (m : ℝ)) = 1 / (m : ℝ) ^ 4 := by
  rw [show -4 * Real.log (m : ℝ) = -(4 * Real.log (m : ℝ)) by ring,
    Real.exp_neg, show 4 * Real.log (m : ℝ) = (4 : ℕ) * Real.log (m : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hm)]
  ring

lemma reprBad_measureReal_le_inv_four (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max (max 20 (3 * N)) 16 ≤ m) :
    reservoirMeasure.real (reprBad m) ≤ 1 / (m : ℝ) ^ 4 := by
  have hbase : max 20 (3 * N) ≤ m := le_trans (le_max_left _ _) hm
  have hm16 : 16 ≤ m := le_trans (le_max_right _ _) hm
  calc
    reservoirMeasure.real (reprBad m) ≤
        Real.exp (-8 * Real.log (m / 3 : ℕ)) :=
      middle_pairSum_failure_bound N m hformula hbase
    _ ≤ Real.exp (-4 * Real.log (m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hhalf := half_log_le_log_third hm16
      linarith
    _ = 1 / (m : ℝ) ^ 4 := exp_neg_four_log_nat (by omega)

lemma block_card_le_X_succ (n : ℕ) : (block n).card ≤ X (n + 1) := by
  rw [block, Nat.card_Ico]
  omega

lemma stageBad_measureReal_le_inv_X_sq (N n : ℕ)
    (hformula : ∀ m ≥ N,
      selectionProbReal m = 40 * Real.sqrt (Real.log m / m))
    (hX : max (max 20 (3 * N)) 16 ≤ X n) :
    reservoirMeasure.real (stageBad n) ≤ 1 / (X n : ℝ) ^ 2 := by
  have hXpos : (0 : ℝ) < X n := by exact_mod_cast X_pos n
  calc
    reservoirMeasure.real (stageBad n) ≤
        ∑ m ∈ block n, reservoirMeasure.real (reprBad m) :=
      stageBad_measureReal_le_sum n
    _ ≤ ∑ m ∈ block n, 1 / (m : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro m hm
      have hmX : X n ≤ m := (mem_block.1 hm).1
      exact reprBad_measureReal_le_inv_four N m hformula (hX.trans hmX)
    _ ≤ ∑ _m ∈ block n, 1 / (X n : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro m hm
      have hmX : X n ≤ m := (mem_block.1 hm).1
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hpow : (X n : ℝ) ^ 4 ≤ (m : ℝ) ^ 4 := by
        gcongr
      exact hpow
    _ = (block n).card * (1 / (X n : ℝ) ^ 4) := by simp
    _ ≤ (X n : ℝ) ^ 2 * (1 / (X n : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : ((block n).card : ℝ) ≤ (X (n + 1) : ℝ) := by
          exact_mod_cast block_card_le_X_succ n
        simpa [X_succ] using hcard
      · positivity
    _ = 1 / (X n : ℝ) ^ 2 := by
      field_simp

lemma two_pow_le_X (n : ℕ) : 2 ^ n ≤ X n := by
  unfold X
  exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt n.lt_two_pow_self)

lemma inv_X_sq_le_geometric (n : ℕ) :
    1 / (X n : ℝ) ^ 2 ≤ (1 / 4 : ℝ) ^ n := by
  have hcast : ((2 ^ n : ℕ) : ℝ) ≤ (X n : ℝ) := by exact_mod_cast two_pow_le_X n
  calc
    1 / (X n : ℝ) ^ 2 ≤ 1 / (((2 ^ n : ℕ) : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
    _ = (1 / 4 : ℝ) ^ n := by
      rw [show (1 / 4 : ℝ) = (2 : ℝ)⁻¹ ^ 2 by norm_num,
        ← pow_mul, inv_pow, mul_comm]
      simp only [Nat.cast_pow, Nat.cast_ofNat, one_div]
      rw [← pow_mul]

lemma summable_inv_X_sq : Summable (fun n : ℕ ↦ 1 / (X n : ℝ) ^ 2) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).of_nonneg_of_le
  · intro n
    positivity
  · exact inv_X_sq_le_geometric

lemma summable_stageBad_measureReal :
    Summable (fun n : ℕ ↦ reservoirMeasure.real (stageBad n)) := by
  obtain ⟨N, hformula⟩ := Filter.eventually_atTop.mp selectionProbReal_formula_eventually
  have hXevent : ∀ᶠ n : ℕ in atTop,
      max (max 20 (3 * N)) 16 ≤ X n :=
    X_strictMono.tendsto_atTop (Filter.eventually_ge_atTop _)
  apply summable_inv_X_sq.of_norm_bounded_eventually_nat
  filter_upwards [hXevent] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
  exact stageBad_measureReal_le_inv_X_sq N n hformula hn

lemma tsum_stageBad_ne_top :
    (∑' n : ℕ, reservoirMeasure (stageBad n)) ≠ ⊤ := by
  rw [show (fun n : ℕ ↦ reservoirMeasure (stageBad n)) =
      (fun n ↦ ((reservoirMeasure (stageBad n)).toNNReal : ENNReal)) by
    funext n
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_stageBad_measureReal

/-- A deterministic reservoir outcome for which every sufficiently late block
has the required logarithmic supply of strict middle representations. -/
lemma exists_good_reservoir : ∃ ω : ReservoirSample,
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ block n,
      40 * Real.log (m / 3 : ℕ) < pairSum (m / 3) m ω := by
  have hae : ∀ᵐ ω ∂reservoirMeasure, ∀ᶠ n : ℕ in atTop, ω ∉ stageBad n :=
    MeasureTheory.ae_eventually_notMem tsum_stageBad_ne_top
  obtain ⟨ω, hω⟩ := hae.exists
  refine ⟨ω, ?_⟩
  filter_upwards [hω] with n hn m hm
  have hnot : ω ∉ reprBad m := by
    intro hbad
    exact hn (by
      unfold stageBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad))
  exact lt_of_not_ge hnot


/-! ## Upper reservoir estimates -/

lemma log_div_nat_le_four_log_div {m x : ℕ} (hm : 3 ≤ m)
    (hlo : m / 3 ≤ x) (hhi : x ≤ m) :
    Real.log x / (x : ℝ) ≤ 5 * (Real.log m / (m : ℝ)) := by
  have hxposN : 0 < x := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposN
  have hlogx : Real.log (x : ℝ) ≤ Real.log (m : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hxpos hmpos (by exact_mod_cast hhi)
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hmxN : m ≤ 5 * x := by omega
  have hmx : (m : ℝ) ≤ 5 * x := by exact_mod_cast hmxN
  rw [div_le_iff₀ hxpos, show 5 * (Real.log (m : ℝ) / (m : ℝ)) * (x : ℝ) =
      (5 * Real.log (m : ℝ) * x) / m by ring]
  rw [le_div_iff₀ hmpos]
  calc
    Real.log (x : ℝ) * m ≤ Real.log (m : ℝ) * m :=
      mul_le_mul_of_nonneg_right hlogx hmpos.le
    _ ≤ Real.log (m : ℝ) * (5 * x) := mul_le_mul_of_nonneg_left hmx hlog0
    _ = 5 * Real.log (m : ℝ) * x := by ring

lemma pairProbability_upper_bound (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 3 (3 * N) ≤ m) (i : strictReprIndices (m / 3) m) :
    (pairProbability (m / 3) m i : ℝ) ≤
      10000 * (Real.log m / (m : ℝ)) := by
  have hi_mem := Finset.mem_filter.1 i.property
  have hilo : m / 3 ≤ (i : ℕ) := (Finset.mem_Icc.1 hi_mem.1).1
  have hihi : (i : ℕ) ≤ m := (Finset.mem_Icc.1 hi_mem.1).2
  have histrict : 2 * (i : ℕ) < m := hi_mem.2
  have hjlo : m / 3 ≤ m - (i : ℕ) := by omega
  have hjhi : m - (i : ℕ) ≤ m := Nat.sub_le _ _
  have hmthird : N ≤ m / 3 := by omega
  have hiN : N ≤ (i : ℕ) := hmthird.trans hilo
  have hjN : N ≤ m - (i : ℕ) := hmthird.trans hjlo
  have hm3 : 3 ≤ m := le_trans (le_max_left _ _) hm
  let q : ℝ := Real.log (m : ℝ) / (m : ℝ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hri : Real.log (i : ℕ) / ((i : ℕ) : ℝ) ≤ 5 * q :=
    log_div_nat_le_four_log_div hm3 hilo hihi
  have hrj : Real.log (m - (i : ℕ) : ℕ) / ((m - (i : ℕ) : ℕ) : ℝ) ≤ 5 * q :=
    log_div_nat_le_four_log_div hm3 hjlo hjhi
  have hsqi := Real.sqrt_le_sqrt hri
  have hsqj := Real.sqrt_le_sqrt hrj
  have hprod := mul_le_mul hsqi hsqj (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h5q : 0 ≤ 5 * q := by positivity
  have hsquare : Real.sqrt (5 * q) * Real.sqrt (5 * q) = 5 * q :=
    Real.mul_self_sqrt h5q
  change selectionProbReal (i : ℕ) * selectionProbReal (m - (i : ℕ)) ≤ 10000 * q
  rw [hformula _ hiN, hformula _ hjN]
  nlinarith [hprod, hsquare]

lemma strictReprIndices_card_le_succ (lo m : ℕ) :
    Fintype.card (strictReprIndices lo m) ≤ m + 1 := by
  rw [Fintype.card_coe]
  calc
    (strictReprIndices lo m).card ≤ (Finset.Icc lo m).card :=
      Finset.card_filter_le _ _
    _ ≤ (Finset.Icc 0 m).card := Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨Nat.zero_le x, hx.2⟩)
    _ = m + 1 := by simp

lemma pairMean_upper_bound (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 3 (3 * N) ≤ m) :
    pairMean (m / 3) m ≤ 20000 * Real.log m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog0 : 0 ≤ Real.log (m : ℝ) := by positivity
  have hsum : pairMean (m / 3) m ≤
      (Fintype.card (strictReprIndices (m / 3) m) : ℝ) *
        (10000 * (Real.log m / (m : ℝ))) := by
    unfold pairMean
    calc
      (∑ i : strictReprIndices (m / 3) m, (pairProbability (m / 3) m i : ℝ)) ≤
          ∑ _i : strictReprIndices (m / 3) m,
            10000 * (Real.log m / (m : ℝ)) := by
              apply Finset.sum_le_sum
              intro i hi
              exact pairProbability_upper_bound N m hformula hm i
      _ = _ := by simp
  have hcardN := strictReprIndices_card_le_succ (m / 3) m
  have hcard : (Fintype.card (strictReprIndices (m / 3) m) : ℝ) ≤ 2 * m := by
    exact_mod_cast (hcardN.trans (by omega : m + 1 ≤ 2 * m))
  have hq0 : 0 ≤ 10000 * (Real.log m / (m : ℝ)) := by positivity
  calc
    pairMean (m / 3) m ≤ _ := hsum
    _ ≤ (2 * m : ℝ) * (10000 * (Real.log m / (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard hq0
    _ = 20000 * Real.log m := by field_simp; ring

lemma pairSum_large_tail (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 3 (3 * N) ≤ m) :
    reservoirMeasure.real
      {ω | 60000 * Real.log m ≤ pairSum (m / 3) m ω} ≤
        Real.exp (-8 * Real.log m) := by
  have hmean := pairMean_upper_bound N m hformula hm
  have hlog0 : 0 ≤ Real.log (m : ℝ) := by positivity
  have hexp : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  calc
    reservoirMeasure.real
      {ω | 60000 * Real.log m ≤ pairSum (m / 3) m ω} ≤
        Real.exp (-1 * (60000 * Real.log m) +
          (Real.exp 1 - 1) * pairMean (m / 3) m) :=
      pairSum_upper_tail (m / 3) m (60000 * Real.log m) 1 (by norm_num)
    _ ≤ Real.exp (-8 * Real.log m) := by
      apply Real.exp_le_exp.mpr
      have hmul1 : (Real.exp 1 - 1) * pairMean (m / 3) m ≤
          2 * pairMean (m / 3) m :=
        mul_le_mul_of_nonneg_right hexp (pairMean_nonneg _ _)
      have hmul2 : 2 * pairMean (m / 3) m ≤ 40000 * Real.log m := by
        linarith
      linarith

def reprUpperBad (m : ℕ) : Set ReservoirSample :=
  {ω | 60000 * Real.log m ≤ pairSum (m / 3) m ω}

lemma reprUpperBad_measurable (m : ℕ) : MeasurableSet (reprUpperBad m) := by
  exact measurableSet_le measurable_const (pairSum_measurable (m / 3) m)

lemma exp_neg_eight_log_nat {m : ℕ} (hm : 0 < m) :
    Real.exp (-8 * Real.log (m : ℝ)) = 1 / (m : ℝ) ^ 8 := by
  rw [show -8 * Real.log (m : ℝ) = -(8 * Real.log (m : ℝ)) by ring,
    Real.exp_neg, show 8 * Real.log (m : ℝ) = (8 : ℕ) * Real.log (m : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hm)]
  ring

lemma reprUpperBad_measureReal_le_inv_eight (N m : ℕ)
    (hformula : ∀ n ≥ N,
      selectionProbReal n = 40 * Real.sqrt (Real.log n / n))
    (hm : max 3 (3 * N) ≤ m) :
    reservoirMeasure.real (reprUpperBad m) ≤ 1 / (m : ℝ) ^ 8 := by
  rw [← exp_neg_eight_log_nat (show 0 < m by omega)]
  exact pairSum_large_tail N m hformula hm

def stageUpperBad (n : ℕ) : Set ReservoirSample :=
  ⋃ m ∈ block n, reprUpperBad m

lemma stageUpperBad_measurable (n : ℕ) : MeasurableSet (stageUpperBad n) := by
  unfold stageUpperBad
  exact Finset.measurableSet_biUnion (block n) fun m hm ↦ reprUpperBad_measurable m

lemma stageUpperBad_measureReal_le_sum (n : ℕ) :
    reservoirMeasure.real (stageUpperBad n) ≤
      ∑ m ∈ block n, reservoirMeasure.real (reprUpperBad m) := by
  exact measureReal_biUnion_finset_le (block n) reprUpperBad

lemma stageUpperBad_measureReal_le_inv_X_sq (N n : ℕ)
    (hformula : ∀ m ≥ N,
      selectionProbReal m = 40 * Real.sqrt (Real.log m / m))
    (hX : max 3 (3 * N) ≤ X n) :
    reservoirMeasure.real (stageUpperBad n) ≤ 1 / (X n : ℝ) ^ 2 := by
  have hXpos : (0 : ℝ) < X n := by exact_mod_cast X_pos n
  calc
    reservoirMeasure.real (stageUpperBad n) ≤
        ∑ m ∈ block n, reservoirMeasure.real (reprUpperBad m) :=
      stageUpperBad_measureReal_le_sum n
    _ ≤ ∑ m ∈ block n, 1 / (m : ℝ) ^ 8 := by
      apply Finset.sum_le_sum
      intro m hm
      exact reprUpperBad_measureReal_le_inv_eight N m hformula
        (hX.trans (mem_block.1 hm).1)
    _ ≤ ∑ _m ∈ block n, 1 / (X n : ℝ) ^ 8 := by
      apply Finset.sum_le_sum
      intro m hm
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
      exact_mod_cast (mem_block.1 hm).1
    _ = (block n).card * (1 / (X n : ℝ) ^ 8) := by simp
    _ ≤ (X n : ℝ) ^ 2 * (1 / (X n : ℝ) ^ 8) := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : ((block n).card : ℝ) ≤ (X (n + 1) : ℝ) := by
          exact_mod_cast block_card_le_X_succ n
        simpa [X_succ] using hcard
      · positivity
    _ ≤ 1 / (X n : ℝ) ^ 2 := by
      have hXone : (1 : ℝ) ≤ X n := by exact_mod_cast (X_pos n)
      field_simp [ne_of_gt hXpos]
      nlinarith [sq_nonneg ((X n : ℝ) ^ 2 - 1)]

lemma summable_stageUpperBad_measureReal :
    Summable (fun n : ℕ ↦ reservoirMeasure.real (stageUpperBad n)) := by
  obtain ⟨N, hformula⟩ := Filter.eventually_atTop.mp selectionProbReal_formula_eventually
  have hXevent : ∀ᶠ n : ℕ in atTop, max 3 (3 * N) ≤ X n :=
    X_strictMono.tendsto_atTop (Filter.eventually_ge_atTop _)
  apply summable_inv_X_sq.of_norm_bounded_eventually_nat
  filter_upwards [hXevent] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact stageUpperBad_measureReal_le_inv_X_sq N n hformula hn

lemma tsum_stageUpperBad_ne_top :
    (∑' n : ℕ, reservoirMeasure (stageUpperBad n)) ≠ ⊤ := by
  rw [show (fun n : ℕ ↦ reservoirMeasure (stageUpperBad n)) =
      (fun n ↦ ((reservoirMeasure (stageUpperBad n)).toNNReal : ENNReal)) by
    funext n
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_stageUpperBad_measureReal

/-- One reservoir outcome simultaneously has the lower and upper logarithmic
representation bounds in every sufficiently late block. -/
lemma exists_two_sided_good_reservoir : ∃ ω : ReservoirSample,
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ block n,
      40 * Real.log (m / 3 : ℕ) < pairSum (m / 3) m ω ∧
        pairSum (m / 3) m ω < 60000 * Real.log m := by
  have hlo : ∀ᵐ ω ∂reservoirMeasure, ∀ᶠ n : ℕ in atTop, ω ∉ stageBad n :=
    MeasureTheory.ae_eventually_notMem tsum_stageBad_ne_top
  have hhi : ∀ᵐ ω ∂reservoirMeasure, ∀ᶠ n : ℕ in atTop, ω ∉ stageUpperBad n :=
    MeasureTheory.ae_eventually_notMem tsum_stageUpperBad_ne_top
  obtain ⟨ω, hωlo, hωhi⟩ := (hlo.and hhi).exists
  refine ⟨ω, ?_⟩
  filter_upwards [hωlo, hωhi] with n hnlo hnhi m hm
  constructor
  · exact lt_of_not_ge (fun hbad ↦ hnlo (by
      unfold stageBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad)))
  · exact lt_of_not_ge (fun hbad ↦ hnhi (by
      unfold stageUpperBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad)))


/-! ## Common-sum collision packing -/

/-- The three coordinates in a common-sum triple
`x + y = q`, `y + z = r`, parametrized by its middle coordinate. -/
def tripleEndpoint (q r y : ℕ) (j : Fin 3) : ℕ :=
  if j = 0 then y else if j = 1 then q - y else r - y

noncomputable def tripleSet (q r y : ℕ) : Finset ℕ :=
  Finset.univ.image (tripleEndpoint q r y)

lemma mem_tripleSet {q r y x : ℕ} :
    x ∈ tripleSet q r y ↔ ∃ j : Fin 3, tripleEndpoint q r y j = x := by
  classical
  simp [tripleSet]

lemma tripleSet_nonempty (q r y : ℕ) : (tripleSet q r y).Nonempty := by
  classical
  exact ⟨y, mem_tripleSet.2 ⟨0, by simp [tripleEndpoint]⟩⟩

lemma tripleEndpoint_injective_in_center {q r : ℕ} (j : Fin 3) :
    Set.InjOn (fun y ↦ tripleEndpoint q r y j)
      {y | y ≤ q ∧ y ≤ r} := by
  intro y hy z hz h
  simp only [Set.mem_setOf_eq] at hy hz
  fin_cases j <;> simp [tripleEndpoint] at h <;> omega

def tripleOverlap (q r y z : ℕ) : Prop :=
  ¬ Disjoint (tripleSet q r y) (tripleSet q r z)

noncomputable instance tripleOverlapDecidable (q r y z : ℕ) :
    Decidable (tripleOverlap q r y z) := Classical.propDecidable _

lemma tripleOverlap_symm {q r y z : ℕ} :
    tripleOverlap q r y z → tripleOverlap q r z y := by
  simpa [tripleOverlap, disjoint_comm]

lemma tripleOverlap_refl (q r y : ℕ) : tripleOverlap q r y y := by
  intro h
  have hy : y ∈ tripleSet q r y := mem_tripleSet.2 ⟨0, by simp [tripleEndpoint]⟩
  exact (Finset.disjoint_left.1 h hy hy)

lemma tripleOverlap_iff {q r y z : ℕ} :
    tripleOverlap q r y z ↔
      ∃ i j : Fin 3, tripleEndpoint q r y i = tripleEndpoint q r z j := by
  classical
  rw [tripleOverlap, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, hz⟩
    obtain ⟨i, hi⟩ := mem_tripleSet.1 hx
    obtain ⟨j, hj⟩ := mem_tripleSet.1 hz
    exact ⟨i, j, hi.trans hj.symm⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨tripleEndpoint q r y i, mem_tripleSet.2 ⟨i, rfl⟩,
      mem_tripleSet.2 ⟨j, hij.symm⟩⟩

lemma card_filter_endpoint_eq_le_one (S : Finset ℕ) {q r y : ℕ}
    (hvalid : ∀ z ∈ S, z ≤ q ∧ z ≤ r) (i j : Fin 3) :
    (S.filter (fun z ↦ tripleEndpoint q r y i = tripleEndpoint q r z j)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  apply tripleEndpoint_injective_in_center j (hvalid a ha.1) (hvalid b hb.1)
  exact ha.2.symm.trans hb.2

lemma overlap_neighbors_card_le_nine (S : Finset ℕ) {q r : ℕ}
    (hvalid : ∀ z ∈ S, z ≤ q ∧ z ≤ r) (y : ℕ) :
    (S.filter (tripleOverlap q r y)).card ≤ 9 := by
  classical
  let fibres : Fin 3 × Fin 3 → Finset ℕ := fun ij ↦
    S.filter (fun z ↦
      tripleEndpoint q r y ij.1 = tripleEndpoint q r z ij.2)
  have hsub : S.filter (tripleOverlap q r y) ⊆ Finset.univ.biUnion fibres := by
    intro z hz
    simp only [Finset.mem_filter] at hz
    obtain ⟨i, j, hij⟩ := tripleOverlap_iff.1 hz.2
    exact Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
      Finset.mem_filter.2 ⟨hz.1, hij⟩⟩
  calc
    (S.filter (tripleOverlap q r y)).card ≤ (Finset.univ.biUnion fibres).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ ij : Fin 3 × Fin 3, (fibres ij).card := by
      simpa using Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
        (t := fibres)
    _ ≤ ∑ _ij : Fin 3 × Fin 3, 1 := by
      apply Finset.sum_le_sum
      intro ij hij
      exact card_filter_endpoint_eq_le_one S hvalid ij.1 ij.2
    _ = 9 := by decide

lemma exists_pairwise_avoiding_of_mul_le_card
    {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (hR_symm : ∀ {a b}, R a b → R b a) (D : ℕ) (hD : 0 < D) :
    ∀ (k : ℕ) (S : Finset α),
      (∀ a ∈ S, R a a) →
      (∀ a ∈ S, (S.filter (R a)).card ≤ D) →
      D * k ≤ S.card →
      ∃ T : Finset α, T ⊆ S ∧ T.card = k ∧
        ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ R a b := by
  intro k
  induction k with
  | zero =>
      intro S hrefl hdegree hcard
      exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ih =>
      intro S hrefl hdegree hcard
      have hSpos : 0 < S.card := by
        have : 0 < D * (k + 1) := Nat.mul_pos hD (by omega)
        omega
      obtain ⟨a, haS⟩ := Finset.card_pos.1 hSpos
      let N := S.filter (R a)
      let S' := S \ N
      have hNS : N ⊆ S := Finset.filter_subset _ _
      have hNcard : N.card ≤ D := hdegree a haS
      have hScard : D * k ≤ S'.card := by
        have hcardSum : D * k + D ≤ S.card := by
          simpa [Nat.mul_succ] using hcard
        have hcard' : S'.card = S.card - N.card := by
          dsimp [S']
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hNS]
        have hNleS : N.card ≤ S.card := Finset.card_le_card hNS
        omega
      have hSsub : S' ⊆ S := Finset.sdiff_subset
      have hrefl' : ∀ b ∈ S', R b b := fun b hb ↦ hrefl b (hSsub hb)
      have hdegree' : ∀ b ∈ S', (S'.filter (R b)).card ≤ D := by
        intro b hb
        exact (Finset.card_le_card (Finset.filter_subset_filter _ hSsub)).trans
          (hdegree b (hSsub hb))
      obtain ⟨T, hTS', hTcard, hTpair⟩ := ih S' hrefl' hdegree' hScard
      have haN : a ∈ N := Finset.mem_filter.2 ⟨haS, hrefl a haS⟩
      have haS' : a ∉ S' := by simp [S', haN]
      have haT : a ∉ T := fun ha ↦ haS' (hTS' ha)
      refine ⟨insert a T, ?_, ?_, ?_⟩
      · intro b hb
        simp only [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact haS
        · exact hSsub (hTS' hb)
      · simp [haT, hTcard]
      · intro x hx y hy hxy
        simp only [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact (hxy rfl).elim
        · intro hay
          have hyS' := hTS' hy
          have hyNotN : y ∉ N := (Finset.mem_sdiff.1 hyS').2
          exact hyNotN (Finset.mem_filter.2 ⟨hSsub hyS', hay⟩)
        · intro hxa
          have hxS' := hTS' hx
          have hxNotN : x ∉ N := (Finset.mem_sdiff.1 hxS').2
          exact hxNotN (Finset.mem_filter.2 ⟨hSsub hxS', hR_symm hxa⟩)
        · exact hTpair x hx y hy hxy

def nondegenerateCenters (q r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun y ↦ 2 * y ≠ q ∧ 2 * y ≠ r)

lemma card_degenerateCenters_le_two (q r : ℕ) (S : Finset ℕ) :
    (S \ nondegenerateCenters q r S).card ≤ 2 := by
  classical
  have hsub : S \ nondegenerateCenters q r S ⊆
      (S.filter (fun y ↦ 2 * y = q)) ∪ (S.filter (fun y ↦ 2 * y = r)) := by
    intro y hy
    have hyS := (Finset.mem_sdiff.1 hy).1
    have hynot := (Finset.mem_sdiff.1 hy).2
    simp only [nondegenerateCenters, Finset.mem_filter, hyS, true_and] at hynot
    simp only [Finset.mem_union, Finset.mem_filter, hyS, true_and]
    by_cases hq : 2 * y = q
    · exact Or.inl hq
    · right
      by_contra hr
      exact hynot ⟨hq, hr⟩
  calc
    (S \ nondegenerateCenters q r S).card ≤
        ((S.filter (fun y ↦ 2 * y = q)) ∪ (S.filter (fun y ↦ 2 * y = r))).card :=
      Finset.card_le_card hsub
    _ ≤ (S.filter (fun y ↦ 2 * y = q)).card +
        (S.filter (fun y ↦ 2 * y = r)).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := by
      gcongr <;> rw [Finset.card_le_one] <;> intro a ha b hb <;>
        simp only [Finset.mem_filter] at ha hb <;> omega
    _ = 2 := by norm_num

lemma tripleSet_card_eq_three {q r y : ℕ} (hqr : q ≠ r)
    (hyq : y ≤ q) (hyr : y ≤ r) (hdeg : 2 * y ≠ q ∧ 2 * y ≠ r) :
    (tripleSet q r y).card = 3 := by
  classical
  have hinj : Set.InjOn (tripleEndpoint q r y) (Finset.univ : Finset (Fin 3)) := by
    intro i hi j hj hij
    fin_cases i <;> fin_cases j <;> simp [tripleEndpoint] at hij ⊢ <;> omega
  rw [tripleSet, Finset.card_image_iff.mpr hinj]
  decide

lemma exists_twenty_disjoint_triples {q r : ℕ} (hqr : q ≠ r)
    (S : Finset ℕ) (hvalid : ∀ y ∈ S, y ≤ q ∧ y ≤ r)
    (hcard : 182 ≤ S.card) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = 20 ∧
      (∀ y ∈ T, (tripleSet q r y).card = 3) ∧
      ∀ y ∈ T, ∀ z ∈ T, y ≠ z → Disjoint (tripleSet q r y) (tripleSet q r z) := by
  classical
  let S' := nondegenerateCenters q r S
  have hS'sub : S' ⊆ S := Finset.filter_subset _ _
  have hS'card : 180 ≤ S'.card := by
    have hdiff := card_degenerateCenters_le_two q r S
    change (S \ S').card ≤ 2 at hdiff
    have hsubcard : S'.card ≤ S.card := Finset.card_le_card hS'sub
    have hcardeq : (S \ S').card = S.card - S'.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hS'sub]
    omega
  have hrefl : ∀ y ∈ S', tripleOverlap q r y y :=
    fun y hy ↦ tripleOverlap_refl q r y
  have hdegree : ∀ y ∈ S', (S'.filter (tripleOverlap q r y)).card ≤ 9 := by
    intro y hy
    exact overlap_neighbors_card_le_nine S'
      (fun z hz ↦ hvalid z (hS'sub hz)) y
  obtain ⟨T, hTS', hTcard, hTpair⟩ :=
    exists_pairwise_avoiding_of_mul_le_card (tripleOverlap q r)
      (@tripleOverlap_symm q r) 9 (by norm_num) 20 S' hrefl hdegree (by norm_num at hS'card ⊢; omega)
  refine ⟨T, fun y hy ↦ hS'sub (hTS' hy), hTcard, ?_, ?_⟩
  · intro y hy
    have hyS' := Finset.mem_filter.1 (hTS' hy)
    exact tripleSet_card_eq_three hqr (hvalid y (hS'sub (hTS' hy))).1
      (hvalid y (hS'sub (hTS' hy))).2 hyS'.2
  · intro y hy z hz hyz
    exact not_not.mp (hTpair y hy z hz hyz)


/-! ## Summable collision events on dyadic scales -/

def allSelected {ι : Type*} [Fintype ι] (e : ι → ℕ) : Set ReservoirSample :=
  {ω | ∀ i, membershipBit (e i) ω = true}

lemma allSelected_measurable {ι : Type*} [Fintype ι] (e : ι → ℕ) :
    MeasurableSet (allSelected e) := by
  rw [show allSelected e = ⋂ i, membershipBit (e i) ⁻¹' {true} by
    ext ω
    simp [allSelected]]
  exact MeasurableSet.iInter fun i ↦
    membershipBit_measurable (e i) (MeasurableSet.singleton true)

lemma measureReal_allSelected_eq_prod {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) :
    reservoirMeasure.real (allSelected e) =
      ∏ i, selectionProbReal (e i) := by
  have hind : iIndepFun (fun i ω ↦ membershipBit (e i) ω) reservoirMeasure :=
    iIndepFun.precomp he membershipBit_iIndep
  have h := hind.measure_inter_preimage_eq_mul (Finset.univ : Finset ι)
    (sets := fun _ ↦ {true}) (fun _ _ ↦ MeasurableSet.singleton true)
  have hr := congrArg ENNReal.toReal h
  have hset : (⋂ i ∈ (Finset.univ : Finset ι),
      (fun ω ↦ membershipBit (e i) ω) ⁻¹' {true}) = allSelected e := by
    ext ω
    simp [allSelected]
  rw [hset] at hr
  rw [ENNReal.toReal_prod] at hr
  have hcoord : ∀ i : ι,
      (reservoirMeasure ((fun ω ↦ membershipBit (e i) ω) ⁻¹' {true})).toReal =
        selectionProbReal (e i) := by
    intro i
    change reservoirMeasure.real {ω | membershipBit (e i) ω = true} = _
    exact membershipBit_true_probability (e i)
  simp_rw [hcoord] at hr
  exact hr

lemma measureReal_allSelected_le_pow {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) (P : ℝ)
    (_hP0 : 0 ≤ P) (hprob : ∀ i, selectionProbReal (e i) ≤ P) :
    reservoirMeasure.real (allSelected e) ≤ P ^ Fintype.card ι := by
  rw [measureReal_allSelected_eq_prod e he]
  calc
    (∏ i, selectionProbReal (e i)) ≤ ∏ _i : ι, P := by
      apply Finset.prod_le_prod
      · intro i hi
        exact selectionProbReal_nonneg _
      · intro i hi
        exact hprob i
    _ = P ^ Fintype.card ι := by simp

lemma selectionProbReal_le_formula (n : ℕ) :
    selectionProbReal n ≤ 40 * Real.sqrt (Real.log n / n) := by
  exact min_le_right _ _

lemma log_div_extended_upper {N x : ℕ} (hN : 8 ≤ N)
    (hlo : N / 4 ≤ x) (hhi : x ≤ 2 * N) :
    Real.log x / (x : ℝ) ≤ 16 * (Real.log N / (N : ℝ)) := by
  have hxposN : 0 < x := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposN
  have htwoNpos : (0 : ℝ) < 2 * N := by positivity
  have hlogx : Real.log (x : ℝ) ≤ Real.log (2 * N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hxpos htwoNpos (by exact_mod_cast hhi)
  have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogtwo : Real.log (2 * N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    have hlog2N : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hNpos (by exact_mod_cast (show 2 ≤ N by omega))
    linarith
  have hlog : Real.log (x : ℝ) ≤ 2 * Real.log (N : ℝ) := hlogx.trans hlogtwo
  have hNxN : N ≤ 8 * x := by omega
  have hNx : (N : ℝ) ≤ 8 * x := by exact_mod_cast hNxN
  rw [div_le_iff₀ hxpos,
    show 16 * (Real.log (N : ℝ) / (N : ℝ)) * (x : ℝ) =
      (16 * Real.log (N : ℝ) * x) / N by ring,
    le_div_iff₀ hNpos]
  calc
    Real.log (x : ℝ) * N ≤ (2 * Real.log (N : ℝ)) * N :=
      mul_le_mul_of_nonneg_right hlog hNpos.le
    _ ≤ (2 * Real.log (N : ℝ)) * (8 * x) :=
      mul_le_mul_of_nonneg_left hNx (by positivity)
    _ = 16 * Real.log (N : ℝ) * x := by ring

lemma selectionProbReal_extended_upper {N x : ℕ} (hN : 8 ≤ N)
    (hlo : N / 4 ≤ x) (hhi : x ≤ 2 * N) :
    selectionProbReal x ≤ 160 * Real.sqrt (Real.log N / (N : ℝ)) := by
  have hq0 : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := by positivity
  calc
    selectionProbReal x ≤ 40 * Real.sqrt (Real.log x / (x : ℝ)) :=
      selectionProbReal_le_formula x
    _ ≤ 40 * Real.sqrt (16 * (Real.log N / (N : ℝ))) := by
      gcongr
      exact log_div_extended_upper hN hlo hhi
    _ = 160 * Real.sqrt (Real.log N / (N : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
      have hs : Real.sqrt (16 : ℝ) = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hs]
      ring

def dyadicScale (k : ℕ) : ℕ := 2 ^ k

def dyadicBlock (k : ℕ) : Finset ℕ :=
  Finset.Ico (dyadicScale k) (2 * dyadicScale k)

lemma dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  exact pow_pos (by decide) _

lemma dyadicScale_succ (k : ℕ) : dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, pow_succ, mul_comm]

lemma mem_dyadicBlock {k m : ℕ} :
    m ∈ dyadicBlock k ↔ dyadicScale k ≤ m ∧ m < 2 * dyadicScale k := by
  simp [dyadicBlock]

def extendedAtScale (N x : ℕ) : Prop :=
  N / 4 ≤ x ∧ x ≤ 2 * N

abbrev CollisionTuple (N : ℕ) := Fin 20 → Fin (2 * N + 1)

def collisionTupleEndpoint (q r : ℕ) {N : ℕ} (ys : CollisionTuple N)
    (p : Fin 20 × Fin 3) : ℕ :=
  tripleEndpoint q r (ys p.1) p.2

def collisionTupleGood (N q r : ℕ) (ys : CollisionTuple N) : Prop :=
  q ≠ r ∧
    (∀ i, (ys i : ℕ) ≤ q ∧ (ys i : ℕ) ≤ r) ∧
    (∀ p, extendedAtScale N (collisionTupleEndpoint q r ys p)) ∧
    Function.Injective (collisionTupleEndpoint q r ys)

noncomputable def collisionTupleEvent (N q r : ℕ) (ys : CollisionTuple N) :
    Set ReservoirSample := by
  classical
  exact if collisionTupleGood N q r ys then
      allSelected (collisionTupleEndpoint q r ys)
    else ∅

lemma collisionTupleEvent_measurable (N q r : ℕ) (ys : CollisionTuple N) :
    MeasurableSet (collisionTupleEvent N q r ys) := by
  classical
  unfold collisionTupleEvent
  split_ifs
  · exact allSelected_measurable _
  · exact MeasurableSet.empty

lemma collisionTupleEvent_measureReal_le (N q r : ℕ) (ys : CollisionTuple N)
    (hN : 8 ≤ N) :
    reservoirMeasure.real (collisionTupleEvent N q r ys) ≤
      (160 * Real.sqrt (Real.log N / (N : ℝ))) ^ 60 := by
  classical
  unfold collisionTupleEvent
  split_ifs with hgood
  · have hcard : Fintype.card (Fin 20 × Fin 3) = 60 := by decide
    rw [← hcard]
    exact measureReal_allSelected_le_pow _ hgood.2.2.2 _ (by positivity)
      (fun p ↦ selectionProbReal_extended_upper hN (hgood.2.2.1 p).1 (hgood.2.2.1 p).2)
  · simp only [measureReal_empty]
    positivity

noncomputable def collisionBad (k : ℕ) : Set ReservoirSample :=
  let N := dyadicScale k
  ⋃ q ∈ dyadicBlock k, ⋃ r ∈ dyadicBlock k,
    ⋃ ys : CollisionTuple N, collisionTupleEvent N q r ys

lemma collisionBad_measurable (k : ℕ) : MeasurableSet (collisionBad k) := by
  classical
  unfold collisionBad
  exact Finset.measurableSet_biUnion (dyadicBlock k) fun q hq ↦
    Finset.measurableSet_biUnion (dyadicBlock k) fun r hr ↦
      MeasurableSet.iUnion fun ys ↦ collisionTupleEvent_measurable _ _ _ _

lemma collisionBad_measureReal_le_sum (k : ℕ) :
    reservoirMeasure.real (collisionBad k) ≤
      ∑ q ∈ dyadicBlock k, ∑ r ∈ dyadicBlock k,
        ∑ ys : CollisionTuple (dyadicScale k),
          reservoirMeasure.real
            (collisionTupleEvent (dyadicScale k) q r ys) := by
  classical
  unfold collisionBad
  calc
    reservoirMeasure.real
        (⋃ q ∈ dyadicBlock k, ⋃ r ∈ dyadicBlock k,
          ⋃ ys : CollisionTuple (dyadicScale k),
            collisionTupleEvent (dyadicScale k) q r ys) ≤
      ∑ q ∈ dyadicBlock k,
        reservoirMeasure.real
          (⋃ r ∈ dyadicBlock k, ⋃ ys : CollisionTuple (dyadicScale k),
            collisionTupleEvent (dyadicScale k) q r ys) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ dyadicBlock k, ∑ r ∈ dyadicBlock k,
        reservoirMeasure.real
          (⋃ ys : CollisionTuple (dyadicScale k),
            collisionTupleEvent (dyadicScale k) q r ys) := by
      apply Finset.sum_le_sum
      intro q hq
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ dyadicBlock k, ∑ r ∈ dyadicBlock k,
        ∑ ys : CollisionTuple (dyadicScale k),
          reservoirMeasure.real
            (collisionTupleEvent (dyadicScale k) q r ys) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      exact measureReal_iUnion_fintype_le _

lemma dyadicBlock_card_le (k : ℕ) : (dyadicBlock k).card ≤ dyadicScale k := by
  rw [dyadicBlock, Nat.card_Ico]
  omega

lemma collisionTuple_card (N : ℕ) :
    Fintype.card (CollisionTuple N) = (2 * N + 1) ^ 20 := by
  simp [CollisionTuple]

lemma collisionBad_measureReal_le_raw (k : ℕ) (hk : 3 ≤ k) :
    reservoirMeasure.real (collisionBad k) ≤
      (dyadicScale k : ℝ) ^ 2 *
        (Fintype.card (CollisionTuple (dyadicScale k)) : ℝ) *
        (160 * Real.sqrt (Real.log (dyadicScale k) / (dyadicScale k : ℝ))) ^ 60 := by
  let P : ℝ := 160 * Real.sqrt
    (Real.log (dyadicScale k) / (dyadicScale k : ℝ))
  have hN : 8 ≤ dyadicScale k := by
    change 2 ^ 3 ≤ 2 ^ k
    exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hk
  have hcardR : ((dyadicBlock k).card : ℝ) ≤ dyadicScale k := by
    exact_mod_cast dyadicBlock_card_le k
  calc
    reservoirMeasure.real (collisionBad k) ≤
        ∑ q ∈ dyadicBlock k, ∑ r ∈ dyadicBlock k,
          ∑ ys : CollisionTuple (dyadicScale k),
            reservoirMeasure.real
              (collisionTupleEvent (dyadicScale k) q r ys) :=
      collisionBad_measureReal_le_sum k
    _ ≤ ∑ _q ∈ dyadicBlock k, ∑ _r ∈ dyadicBlock k,
          ∑ _ys : CollisionTuple (dyadicScale k), P ^ 60 := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro ys hys
      exact collisionTupleEvent_measureReal_le _ _ _ _ hN
    _ = ((dyadicBlock k).card : ℝ) ^ 2 *
          (Fintype.card (CollisionTuple (dyadicScale k)) : ℝ) * P ^ 60 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ (dyadicScale k : ℝ) ^ 2 *
          (Fintype.card (CollisionTuple (dyadicScale k)) : ℝ) * P ^ 60 := by
      have hP : 0 ≤ P ^ 60 := by positivity
      have htuple : 0 ≤ (Fintype.card (CollisionTuple (dyadicScale k)) : ℝ) := by positivity
      gcongr
    _ = _ := rfl

lemma sqrt_pow_sixty (q : ℝ) (hq : 0 ≤ q) :
    (160 * Real.sqrt q) ^ 60 = (160 : ℝ) ^ 60 * q ^ 30 := by
  rw [mul_pow]
  congr 1
  calc
    Real.sqrt q ^ 60 = (Real.sqrt q ^ 2) ^ 30 := by rw [← pow_mul]
    _ = q ^ 30 := by rw [Real.sq_sqrt hq]

lemma log_dyadicScale (k : ℕ) :
    Real.log (dyadicScale k : ℝ) = k * Real.log 2 := by
  rw [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma inv_dyadicScale_pow_eight (k : ℕ) :
    1 / (dyadicScale k : ℝ) ^ 8 = (1 / 256 : ℝ) ^ k := by
  rw [dyadicScale, Nat.cast_pow, Nat.cast_ofNat]
  change 1 / (((2 : ℝ) ^ k) ^ 8) = (1 / 256 : ℝ) ^ k
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num]
  simp only [one_div, inv_pow, ← pow_mul]
  rw [mul_comm]

noncomputable def collisionConstant : ℝ := (3 : ℝ) ^ 20 * 160 ^ 60

lemma collisionConstant_nonneg : 0 ≤ collisionConstant := by
  unfold collisionConstant
  positivity

lemma collisionBad_measureReal_le_geometric (k : ℕ) (hk : 3 ≤ k) :
    reservoirMeasure.real (collisionBad k) ≤
      collisionConstant * (k : ℝ) ^ 30 * (1 / 2 : ℝ) ^ k := by
  let N : ℕ := dyadicScale k
  have hNpos : 0 < N := dyadicScale_pos k
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hq0 : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := by positivity
  have hbaseNat : 2 * N + 1 ≤ 3 * N := by omega
  have htupleNat : Fintype.card (CollisionTuple N) ≤ (3 * N) ^ 20 := by
    rw [collisionTuple_card]
    exact Nat.pow_le_pow_left hbaseNat 20
  have htuple : (Fintype.card (CollisionTuple N) : ℝ) ≤ ((3 * N : ℕ) : ℝ) ^ 20 := by
    exact_mod_cast htupleNat
  have hraw := collisionBad_measureReal_le_raw k hk
  change reservoirMeasure.real (collisionBad k) ≤
    (N : ℝ) ^ 2 * (Fintype.card (CollisionTuple N) : ℝ) *
      (160 * Real.sqrt (Real.log N / (N : ℝ))) ^ 60 at hraw
  calc
    reservoirMeasure.real (collisionBad k) ≤
        (N : ℝ) ^ 2 * (Fintype.card (CollisionTuple N) : ℝ) *
          (160 * Real.sqrt (Real.log N / (N : ℝ))) ^ 60 := hraw
    _ ≤ (N : ℝ) ^ 2 * ((3 * N : ℕ) : ℝ) ^ 20 *
          (160 * Real.sqrt (Real.log N / (N : ℝ))) ^ 60 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htuple (by positivity)) (by positivity)
    _ = collisionConstant * (Real.log N) ^ 30 /
          (N : ℝ) ^ 8 := by
      unfold collisionConstant
      rw [sqrt_pow_sixty _ hq0]
      push_cast
      field_simp [ne_of_gt hNposR]
    _ ≤ collisionConstant * (k : ℝ) ^ 30 /
          (N : ℝ) ^ 8 := by
      have hlog2pos : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at this ⊢
        exact this
      have hlogN : Real.log (N : ℝ) = (k : ℝ) * Real.log 2 := by
        simpa [N] using log_dyadicScale k
      have hlogle : Real.log (N : ℝ) ≤ k := by
        rw [hlogN]
        nlinarith
      gcongr
      exact collisionConstant_nonneg
    _ = collisionConstant * (k : ℝ) ^ 30 *
          (1 / 256 : ℝ) ^ k := by
      rw [← inv_dyadicScale_pow_eight k]
      change _ / (N : ℝ) ^ 8 = _ * (1 / (N : ℝ) ^ 8)
      ring
    _ ≤ collisionConstant * (k : ℝ) ^ 30 *
          (1 / 2 : ℝ) ^ k := by
      have hpow : (1 / 256 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 256)
          (by norm_num : (1 / 256 : ℝ) ≤ 1 / 2) _
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg collisionConstant_nonneg (by positivity))

lemma summable_collisionBad_measureReal :
    Summable (fun k : ℕ ↦ reservoirMeasure.real (collisionBad k)) := by
  have hmajor : Summable (fun k : ℕ ↦
      collisionConstant * (k : ℝ) ^ 30 * (1 / 2 : ℝ) ^ k) := by
    have h : Summable (fun k : ℕ ↦ (k : ℝ) ^ 30 * (1 / 2 : ℝ) ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 30
        (r := (1 / 2 : ℝ)) (by norm_num)
    simpa only [mul_assoc] using h.mul_left collisionConstant
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact collisionBad_measureReal_le_geometric k hk

lemma tsum_collisionBad_ne_top :
    (∑' k : ℕ, reservoirMeasure (collisionBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ reservoirMeasure (collisionBad k)) =
      (fun k ↦ ((reservoirMeasure (collisionBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_collisionBad_measureReal

lemma exists_collision_good_reservoir : ∃ ω : ReservoirSample,
    ∀ᶠ k : ℕ in atTop, ω ∉ collisionBad k := by
  exact (MeasureTheory.ae_eventually_notMem tsum_collisionBad_ne_top).exists

noncomputable def commonTripleCenters (N q r : ℕ) (ω : ReservoirSample) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 (min q r)).filter (fun y ↦
      ∀ j : Fin 3, extendedAtScale N (tripleEndpoint q r y j) ∧
        membershipBit (tripleEndpoint q r y j) ω = true)

lemma mem_commonTripleCenters {N q r y : ℕ} {ω : ReservoirSample} :
    y ∈ commonTripleCenters N q r ω ↔
      (y ≤ q ∧ y ≤ r) ∧
        ∀ j : Fin 3, extendedAtScale N (tripleEndpoint q r y j) ∧
          membershipBit (tripleEndpoint q r y j) ω = true := by
  classical
  simp [commonTripleCenters, le_min_iff]

lemma collisionBad_of_many {k q r : ℕ} {ω : ReservoirSample}
    (hq : q ∈ dyadicBlock k) (hr : r ∈ dyadicBlock k) (hqr : q ≠ r)
    (hmany : 182 ≤ (commonTripleCenters (dyadicScale k) q r ω).card) :
    ω ∈ collisionBad k := by
  classical
  let S := commonTripleCenters (dyadicScale k) q r ω
  have hvalid : ∀ y ∈ S, y ≤ q ∧ y ≤ r := by
    intro y hy
    exact (mem_commonTripleCenters.1 hy).1
  obtain ⟨T, hTS, hTcard, hTthree, hTdisj⟩ :=
    exists_twenty_disjoint_triples hqr S hvalid hmany
  let eT : Fin 20 ≃ T := (T.equivFin.trans (finCongr hTcard)).symm
  let ys : CollisionTuple (dyadicScale k) := fun i ↦
    ⟨(eT i : ℕ), by
      have hyq := (mem_commonTripleCenters.1 (hTS (eT i).property)).1.1
      have hq' := (mem_dyadicBlock.1 hq).2
      omega⟩
  have hysT (i : Fin 20) : (ys i : ℕ) ∈ T := (eT i).property
  have hcenter (i : Fin 20) : (ys i : ℕ) ∈ S := hTS (hysT i)
  have hendpoint_inj : Function.Injective (collisionTupleEndpoint q r ys) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      have hwithin : Function.Injective (tripleEndpoint q r (ys i)) := by
        have hcard := hTthree (ys i) (hysT i)
        have hinjOn : Set.InjOn (tripleEndpoint q r (ys i))
            (Finset.univ : Finset (Fin 3)) :=
          Finset.card_image_iff.mp (by simpa [tripleSet] using hcard)
        exact fun a b hab ↦ hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
      have : a = b := hwithin hab
      subst b
      rfl
    · have hdisj := hTdisj (ys i) (hysT i) (ys j) (hysT j) (by
          intro hy
          have := eT.injective (Subtype.ext hy)
          exact hij this)
      exfalso
      exact Finset.disjoint_left.1 hdisj
        (mem_tripleSet.2 ⟨a, rfl⟩)
        (mem_tripleSet.2 ⟨b, hab.symm⟩)
  have hgood : collisionTupleGood (dyadicScale k) q r ys := by
    refine ⟨hqr, ?_, ?_, hendpoint_inj⟩
    · intro i
      exact (mem_commonTripleCenters.1 (hcenter i)).1
    · rintro ⟨i, j⟩
      exact (mem_commonTripleCenters.1 (hcenter i)).2 j |>.1
  unfold collisionBad
  exact Set.mem_iUnion_of_mem q (Set.mem_iUnion_of_mem hq
    (Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hr
      (Set.mem_iUnion_of_mem ys (by
        change ω ∈ collisionTupleEvent (dyadicScale k) q r ys
        rw [collisionTupleEvent, if_pos hgood]
        rintro ⟨i, j⟩
        exact (mem_commonTripleCenters.1 (hcenter i)).2 j |>.2)))))


/-! ## Enlarged-block point-count estimates -/

lemma membershipBit_map (n : ℕ) :
    reservoirMeasure.map (membershipBit n) = coordinateMeasure n := by
  change (Measure.infinitePi coordinateMeasure).map
      (fun ω : ℕ → Bool ↦ ω n) = coordinateMeasure n
  exact Measure.infinitePi_map_eval coordinateMeasure n

lemma pointIndicator_mgf (n : ℕ) (t : ℝ) :
    mgf (boolIndicator (membershipBit n)) reservoirMeasure t =
      (1 - selectionProbReal n) + selectionProbReal n * Real.exp t := by
  unfold boolIndicator
  change mgf ((fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ membershipBit n)
    reservoirMeasure t = _
  rw [← mgf_map (Y := membershipBit n)
    (membershipBit_measurable n).aemeasurable (by fun_prop)]
  rw [membershipBit_map, coordinateMeasure, mgf,
    ProbabilityTheory.integral_bernoulliMeasure]
  simp [selectionProb, mul_comm, add_comm]

noncomputable def pointMean (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, selectionProbReal n

noncomputable def pointSum (S : Finset ℕ) (ω : ReservoirSample) : ℝ :=
  ∑ n ∈ S, boolIndicator (membershipBit n) ω

lemma pointIndicator_iIndep (S : Finset ℕ) :
    iIndepFun (fun n : S ↦ boolIndicator (membershipBit n)) reservoirMeasure := by
  have hbits : iIndepFun (fun n : S ↦ membershipBit n) reservoirMeasure :=
    iIndepFun.precomp Subtype.val_injective membershipBit_iIndep
  have h := hbits.comp (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)
  exact h

lemma pointSum_measurable (S : Finset ℕ) : Measurable (pointSum S) := by
  unfold pointSum
  apply Finset.measurable_sum S
  intro n hn
  exact boolIndicator_measurable (membershipBit_measurable n)

lemma pointSum_mgf_le (S : Finset ℕ) (t : ℝ) :
    mgf (pointSum S) reservoirMeasure t ≤
      Real.exp ((Real.exp t - 1) * pointMean S) := by
  calc
    mgf (pointSum S) reservoirMeasure t =
        mgf (fun ω ↦ ∑ n : S, boolIndicator (membershipBit n) ω)
          reservoirMeasure t := by
      congr 1
      funext ω
      unfold pointSum
      have huniv : (Finset.univ : Finset S) = S.attach := by
        ext n
        simp
      rw [huniv]
      exact (Finset.sum_attach S
        (fun n ↦ boolIndicator (membershipBit n) ω)).symm
    _ = mgf (∑ n : S, boolIndicator (membershipBit n)) reservoirMeasure t := by
      congr 1
      funext ω
      simp
    _ =
        ∏ n : S, mgf (boolIndicator (membershipBit n)) reservoirMeasure t := by
      simpa using (pointIndicator_iIndep S).mgf_sum
        (fun n ↦ boolIndicator_measurable (membershipBit_measurable n)) Finset.univ (t := t)
    _ = ∏ n : S, ((1 - selectionProbReal n) +
          selectionProbReal n * Real.exp t) := by
      apply Finset.prod_congr rfl
      intro n hn
      exact pointIndicator_mgf n t
    _ ≤ ∏ n : S, Real.exp (selectionProbReal n * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro n hn
        have hp0 := selectionProbReal_nonneg n
        have hp1 := selectionProbReal_le_one n
        positivity
      · intro n hn
        calc
          (1 - selectionProbReal n) + selectionProbReal n * Real.exp t =
              1 + selectionProbReal n * (Real.exp t - 1) := by ring
          _ ≤ Real.exp (selectionProbReal n * (Real.exp t - 1)) :=
            by simpa [add_comm] using
              Real.add_one_le_exp (selectionProbReal n * (Real.exp t - 1))
    _ = Real.exp (∑ n : S, selectionProbReal n * (Real.exp t - 1)) := by
      rw [← Real.exp_sum]
    _ = Real.exp ((Real.exp t - 1) * pointMean S) := by
      congr 1
      unfold pointMean
      rw [Finset.mul_sum]
      rw [Finset.sum_subtype S (fun x ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro n hn
      ring

lemma pointMean_nonneg (S : Finset ℕ) : 0 ≤ pointMean S := by
  unfold pointMean
  apply Finset.sum_nonneg
  intro n hn
  exact selectionProbReal_nonneg n

lemma pointSum_nonneg (S : Finset ℕ) (ω : ReservoirSample) : 0 ≤ pointSum S ω := by
  unfold pointSum
  apply Finset.sum_nonneg
  intro n hn
  cases h : membershipBit n ω <;> simp [boolIndicator, h]

lemma pointSum_le_card (S : Finset ℕ) (ω : ReservoirSample) :
    pointSum S ω ≤ S.card := by
  unfold pointSum
  calc
    (∑ n ∈ S, boolIndicator (membershipBit n) ω) ≤
        ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      cases h : membershipBit n ω <;> simp [boolIndicator, h]
    _ = S.card := by simp

lemma pointSum_exp_integrable (S : Finset ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * pointSum S ω)) reservoirMeasure := by
  apply Integrable.of_bound ((pointSum_measurable S).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * S.card))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h0 := pointSum_nonneg S ω
  have hc := pointSum_le_card S ω
  have ht : t ≤ |t| := le_abs_self t
  nlinarith [abs_nonneg t]

lemma pointSum_upper_tail (S : Finset ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    reservoirMeasure.real {ω | a ≤ pointSum S ω} ≤
      Real.exp (-t * a + (Real.exp t - 1) * pointMean S) := by
  calc
    reservoirMeasure.real {ω | a ≤ pointSum S ω} ≤
        Real.exp (-t * a) * mgf (pointSum S) reservoirMeasure t :=
      measure_ge_le_exp_mul_mgf a ht (pointSum_exp_integrable S t)
    _ ≤ Real.exp (-t * a) *
        Real.exp ((Real.exp t - 1) * pointMean S) :=
      mul_le_mul_of_nonneg_left (pointSum_mgf_le S t) (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_add]

def extendedIndices (N : ℕ) : Finset ℕ := Finset.Icc (N / 4) (2 * N)

lemma extendedIndices_card_le (N : ℕ) : (extendedIndices N).card ≤ 2 * N + 1 := by
  unfold extendedIndices
  rw [Nat.card_Icc]
  omega

lemma pointMean_extended_le (N : ℕ) (hN : 8 ≤ N) :
    pointMean (extendedIndices N) ≤
      480 * N * Real.sqrt (Real.log N / (N : ℝ)) := by
  have hcardNat : (extendedIndices N).card ≤ 3 * N :=
    (extendedIndices_card_le N).trans (by omega)
  have hcard : ((extendedIndices N).card : ℝ) ≤ 3 * N := by exact_mod_cast hcardNat
  have hsqrt0 : 0 ≤ Real.sqrt (Real.log N / (N : ℝ)) := Real.sqrt_nonneg _
  unfold pointMean
  calc
    (∑ n ∈ extendedIndices N, selectionProbReal n) ≤
        ∑ _n ∈ extendedIndices N,
          160 * Real.sqrt (Real.log N / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.1 hn
      exact selectionProbReal_extended_upper hN hn'.1 hn'.2
    _ = (extendedIndices N).card *
          (160 * Real.sqrt (Real.log N / (N : ℝ))) := by simp
    _ ≤ (3 * N : ℝ) *
          (160 * Real.sqrt (Real.log N / (N : ℝ))) := by
      gcongr
    _ = 480 * N * Real.sqrt (Real.log N / (N : ℝ)) := by ring

lemma sqrt_log_div_ge_log_div (N : ℕ) (hN : 1 ≤ N) :
    Real.log N / (N : ℝ) ≤ Real.sqrt (Real.log N / (N : ℝ)) := by
  let q : ℝ := Real.log N / (N : ℝ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hlogle : Real.log (N : ℝ) ≤ N := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hNpos]
    exact hlogle
  nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]

lemma pointSum_extended_large_tail (N : ℕ) (hN : 8 ≤ N) :
    reservoirMeasure.real
      {ω | 1000 * N * Real.sqrt (Real.log N / (N : ℝ)) ≤
        pointSum (extendedIndices N) ω} ≤
      Real.exp (-40 * Real.log N) := by
  have hmean := pointMean_extended_le N hN
  have hexp : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hmul1 : (Real.exp 1 - 1) * pointMean (extendedIndices N) ≤
      2 * pointMean (extendedIndices N) :=
    mul_le_mul_of_nonneg_right hexp (pointMean_nonneg _)
  have hmul2 : 2 * pointMean (extendedIndices N) ≤
      960 * N * Real.sqrt (Real.log N / (N : ℝ)) := by linarith
  have hsqrt := sqrt_log_div_ge_log_div N (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hscale : Real.log (N : ℝ) ≤
      N * Real.sqrt (Real.log N / (N : ℝ)) := by
    calc
      Real.log (N : ℝ) = (N : ℝ) * (Real.log N / (N : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hNpos.le
  calc
    reservoirMeasure.real
      {ω | 1000 * N * Real.sqrt (Real.log N / (N : ℝ)) ≤
        pointSum (extendedIndices N) ω} ≤
      Real.exp (-(1 : ℝ) *
          (1000 * N * Real.sqrt (Real.log N / (N : ℝ))) +
        (Real.exp 1 - 1) * pointMean (extendedIndices N)) :=
      pointSum_upper_tail _ _ 1 (by norm_num)
    _ ≤ Real.exp (-40 * Real.log N) := by
      apply Real.exp_le_exp.mpr
      linarith

def pointUpperBad (k : ℕ) : Set ReservoirSample :=
  {ω | 1000 * dyadicScale k *
      Real.sqrt (Real.log (dyadicScale k) / (dyadicScale k : ℝ)) ≤
    pointSum (extendedIndices (dyadicScale k)) ω}

lemma pointUpperBad_measurable (k : ℕ) : MeasurableSet (pointUpperBad k) := by
  exact measurableSet_le measurable_const (pointSum_measurable _)

lemma exp_neg_forty_log_dyadic (k : ℕ) :
    Real.exp (-40 * Real.log (dyadicScale k : ℝ)) = (1 / 2 ^ 40 : ℝ) ^ k := by
  rw [log_dyadicScale]
  rw [show -40 * ((k : ℝ) * Real.log 2) = (k : ℕ) * (-40 * Real.log 2) by
    push_cast; ring, Real.exp_nat_mul]
  congr 1
  rw [show -40 * Real.log (2 : ℝ) = -(40 * Real.log 2) by ring,
    Real.exp_neg, show 40 * Real.log (2 : ℝ) = (40 : ℕ) * Real.log 2 by norm_num,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

lemma summable_pointUpperBad_measureReal :
    Summable (fun k : ℕ ↦ reservoirMeasure.real (pointUpperBad k)) := by
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 ^ 40 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  rw [← exp_neg_forty_log_dyadic]
  exact pointSum_extended_large_tail (dyadicScale k) (by
    change 2 ^ 3 ≤ 2 ^ k
    exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hk)

lemma tsum_pointUpperBad_ne_top :
    (∑' k : ℕ, reservoirMeasure (pointUpperBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ reservoirMeasure (pointUpperBad k)) =
      (fun k ↦ ((reservoirMeasure (pointUpperBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_pointUpperBad_measureReal


/-- A single deterministic reservoir outcome satisfying every probabilistic
estimate used in the subsequent deletion construction. -/
lemma exists_master_reservoir : ∃ ω : ReservoirSample,
    (∀ᶠ n : ℕ in atTop, ∀ m ∈ block n,
      40 * Real.log (m / 3 : ℕ) < pairSum (m / 3) m ω ∧
        pairSum (m / 3) m ω < 60000 * Real.log m) ∧
    (∀ᶠ k : ℕ in atTop, ω ∉ collisionBad k) ∧
    (∀ᶠ k : ℕ in atTop, ω ∉ pointUpperBad k) := by
  have hlo : ∀ᵐ ω ∂reservoirMeasure, ∀ᶠ n : ℕ in atTop, ω ∉ stageBad n :=
    MeasureTheory.ae_eventually_notMem tsum_stageBad_ne_top
  have hhi : ∀ᵐ ω ∂reservoirMeasure, ∀ᶠ n : ℕ in atTop, ω ∉ stageUpperBad n :=
    MeasureTheory.ae_eventually_notMem tsum_stageUpperBad_ne_top
  have hcollision : ∀ᵐ ω ∂reservoirMeasure,
      ∀ᶠ k : ℕ in atTop, ω ∉ collisionBad k :=
    MeasureTheory.ae_eventually_notMem tsum_collisionBad_ne_top
  have hpoints : ∀ᵐ ω ∂reservoirMeasure,
      ∀ᶠ k : ℕ in atTop, ω ∉ pointUpperBad k :=
    MeasureTheory.ae_eventually_notMem tsum_pointUpperBad_ne_top
  obtain ⟨ω, hall⟩ := (hlo.and hhi |>.and hcollision |>.and hpoints).exists
  rcases hall with ⟨⟨⟨hωlo, hωhi⟩, hωcollision⟩, hωpoints⟩
  refine ⟨ω, ?_, hωcollision, hωpoints⟩
  filter_upwards [hωlo, hωhi] with n hnlo hnhi m hm
  constructor
  · exact lt_of_not_ge (fun hbad ↦ hnlo (by
      unfold stageBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad)))
  · exact lt_of_not_ge (fun hbad ↦ hnhi (by
      unfold stageUpperBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad)))

noncomputable def selectedIndices (N : ℕ) (ω : ReservoirSample) : Finset ℕ :=
  (extendedIndices N).filter (fun n ↦ membershipBit n ω = true)

lemma mem_selectedIndices {N n : ℕ} {ω : ReservoirSample} :
    n ∈ selectedIndices N ω ↔
      extendedAtScale N n ∧ membershipBit n ω = true := by
  classical
  simp [selectedIndices, extendedIndices, extendedAtScale]

lemma pointSum_eq_selectedIndices_card (N : ℕ) (ω : ReservoirSample) :
    pointSum (extendedIndices N) ω = (selectedIndices N ω).card := by
  classical
  have aux : ∀ s : Finset ℕ,
      (∑ n ∈ s, boolIndicator (membershipBit n) ω) =
        ((s.filter (fun n ↦ membershipBit n ω = true)).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
        cases h : membershipBit n ω <;>
          simp [Finset.sum_insert hn, Finset.filter_insert, boolIndicator, h, hn, ih] <;> ring
  unfold pointSum selectedIndices
  exact aux (extendedIndices N)

lemma master_reservoir_eventual_properties : ∃ ω : ReservoirSample,
    (∀ᶠ n : ℕ in atTop, ∀ m ∈ block n,
      40 * Real.log (m / 3 : ℕ) < pairSum (m / 3) m ω ∧
        pairSum (m / 3) m ω < 60000 * Real.log m) ∧
    (∀ᶠ k : ℕ in atTop, ∀ q ∈ dyadicBlock k, ∀ r ∈ dyadicBlock k,
      q ≠ r → (commonTripleCenters (dyadicScale k) q r ω).card ≤ 181) ∧
    (∀ᶠ k : ℕ in atTop,
      (selectedIndices (dyadicScale k) ω).card <
        1000 * dyadicScale k *
          Real.sqrt (Real.log (dyadicScale k) / (dyadicScale k : ℝ))) := by
  obtain ⟨ω, hrepr, hcollision, hpoints⟩ := exists_master_reservoir
  refine ⟨ω, hrepr, ?_, ?_⟩
  · filter_upwards [hcollision] with k hk q hq r hr hqr
    by_contra hcard
    have hmany : 182 ≤ (commonTripleCenters (dyadicScale k) q r ω).card := by omega
    exact hk (collisionBad_of_many hq hr hqr hmany)
  · filter_upwards [hpoints] with k hk
    rw [← pointSum_eq_selectedIndices_card]
    exact lt_of_not_ge hk

/-- The ordered representation function used by the formal-conjectures specification. -/
noncomputable def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

/-- Unordered order-two representations, in the convention of Larsen--Larsen. -/
noncomputable def unordRepr (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p ↦ p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)

lemma mem_unordRepr {A : Set ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ unordRepr A n ↔ p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n := by
  classical
  rw [unordRepr, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    have hp1 : p.1 ≤ n := by
      rw [← h.2.2.2]
      exact Nat.le_add_right _ _
    have hp2 : p.2 ≤ n := by
      rw [← h.2.2.2]
      exact Nat.le_add_left _ _
    exact ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hp1),
      Finset.mem_range.2 (Nat.lt_succ_of_le hp2)⟩, h⟩

private lemma add_repr_finite (A : Set ℕ) (o n : ℕ) :
    { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.Finite := by
  apply (Set.Finite.pi' fun _ : Fin o ↦ Set.finite_le_nat n).subset
  intro a ha i
  calc
    a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = n := ha.2

private def pairFun (p : ℕ × ℕ) : Fin 2 → ℕ :=
  fun i ↦ if i = 0 then p.1 else p.2

/-- The formal-conjectures ordered count dominates the paper's unordered count. -/
lemma unordRepr_card_le_ncard_add_repr (A : Set ℕ) (n : ℕ) :
    (unordRepr A n).card ≤ ncard_add_repr A 2 n := by
  rw [ncard_add_repr, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard_of_injOn pairFun (ht := add_repr_finite A 2 n)
  · intro p hp
    rw [Finset.mem_coe] at hp
    have h := mem_unordRepr.1 hp
    refine ⟨?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      by_cases hi : i = 0
      · simpa [pairFun, hi] using h.2.1
      · simpa [pairFun, hi] using h.2.2.1
    · simpa [Fin.sum_univ_two, pairFun] using h.2.2.2
  · intro p hp q hq hpq
    apply Prod.ext
    · have := congrFun hpq (0 : Fin 2)
      simpa [pairFun] using this
    · have := congrFun hpq (1 : Fin 2)
      simpa [pairFun] using this

/-- The deterministic subset selected by a reservoir outcome. -/
def reservoirSet (ω : ReservoirSample) : Set ℕ :=
  {n | membershipBit n ω = true}

/-- Strict middle pairs whose two endpoints were retained by the reservoir. -/
noncomputable def presentPairs (lo m : ℕ) (ω : ReservoirSample) :
    Finset (strictReprIndices lo m) :=
  Finset.univ.filter (fun i ↦ pairPresent lo m i ω = true)

lemma mem_presentPairs {lo m : ℕ} {ω : ReservoirSample}
    {i : strictReprIndices lo m} :
    i ∈ presentPairs lo m ω ↔
      membershipBit i ω = true ∧ membershipBit (m - i) ω = true := by
  classical
  simp [presentPairs, pairPresent, Bool.and_eq_true]

lemma pairSum_eq_presentPairs_card (lo m : ℕ) (ω : ReservoirSample) :
    pairSum lo m ω = (presentPairs lo m ω).card := by
  classical
  have aux : ∀ s : Finset (strictReprIndices lo m),
      (∑ i ∈ s, boolIndicator (pairPresent lo m i) ω) =
        ((s.filter (fun i ↦ pairPresent lo m i ω = true)).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        cases h : pairPresent lo m i ω <;>
          simp [Finset.sum_insert hi, Finset.filter_insert, boolIndicator, h, hi, ih] <;> ring
  unfold pairSum presentPairs
  simpa using aux Finset.univ

def presentPairToUnord (m i : ℕ) : ℕ × ℕ := (i, m - i)

lemma presentPairToUnord_injective (m : ℕ) : Function.Injective (presentPairToUnord m) := by
  intro i j h
  exact congrArg Prod.fst h

lemma presentPair_mem_unordRepr {lo m : ℕ} {ω : ReservoirSample}
    {i : strictReprIndices lo m}
    (hi : i ∈ presentPairs lo m ω) :
    presentPairToUnord m i ∈ unordRepr (reservoirSet ω) m := by
  have h := mem_presentPairs.1 hi
  have hstrict : 2 * (i : ℕ) < m := (Finset.mem_filter.1 i.property).2
  have him : (i : ℕ) ≤ m := by omega
  rw [mem_unordRepr]
  change (i : ℕ) ≤ m - (i : ℕ) ∧ membershipBit i ω = true ∧
    membershipBit (m - i) ω = true ∧ (i : ℕ) + (m - i) = m
  exact ⟨by omega, h.1, h.2, Nat.add_sub_of_le him⟩

lemma presentPairs_card_le_unordRepr (lo m : ℕ) (ω : ReservoirSample) :
    (presentPairs lo m ω).card ≤ (unordRepr (reservoirSet ω) m).card := by
  classical
  exact Finset.card_le_card_of_injOn (fun i ↦ presentPairToUnord m i)
    (fun i hi ↦ presentPair_mem_unordRepr hi)
    (fun i hi j hj hij ↦ Subtype.ext ((presentPairToUnord_injective m) hij))

lemma pairSum_le_ncard_add_repr (lo m : ℕ) (ω : ReservoirSample) :
    pairSum lo m ω ≤ ncard_add_repr (reservoirSet ω) 2 m := by
  rw [pairSum_eq_presentPairs_card]
  exact_mod_cast (presentPairs_card_le_unordRepr lo m ω).trans
    (unordRepr_card_le_ncard_add_repr (reservoirSet ω) m)

private lemma unordRepr_eq_of_common_summand {A : Set ℕ} {n d : ℕ}
    {p q : ℕ × ℕ} (hp : p ∈ unordRepr A n) (hq : q ∈ unordRepr A n)
    (hpd : p.1 = d ∨ p.2 = d) (hqd : q.1 = d ∨ q.2 = d) : p = q := by
  have hp' := mem_unordRepr.1 hp
  have hq' := mem_unordRepr.1 hq
  apply Prod.ext <;> grind

/-- Two distinct unordered representations cannot both use a fixed summand, so one
survives deletion of that summand. -/
lemma two_unordRepr_survives_erase {A : Set ℕ} {n d : ℕ}
    (hcard : 2 ≤ (unordRepr A n).card) : n ∈ 2 • (A \ {d}) := by
  have hone : 1 < (unordRepr A n).card := lt_of_lt_of_le (by decide) hcard
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hone
  have choose_rep : ∃ r ∈ unordRepr A n, r.1 ≠ d ∧ r.2 ≠ d := by
    by_cases hpavoid : p.1 ≠ d ∧ p.2 ≠ d
    · exact ⟨p, hp, hpavoid⟩
    · have hpuses : p.1 = d ∨ p.2 = d := by grind
      have hq1 : q.1 ≠ d := by
        intro h
        exact hpq (unordRepr_eq_of_common_summand hp hq hpuses (Or.inl h))
      have hq2 : q.2 ≠ d := by
        intro h
        exact hpq (unordRepr_eq_of_common_summand hp hq hpuses (Or.inr h))
      exact ⟨q, hq, hq1, hq2⟩
  obtain ⟨r, hr, hr1, hr2⟩ := choose_rep
  have hr' := mem_unordRepr.1 hr
  have : n ∈ (A \ {d}) + (A \ {d}) :=
    ⟨r.1, ⟨hr'.2.1, by simpa using hr1⟩,
      r.2, ⟨hr'.2.2.1, by simpa using hr2⟩, hr'.2.2.2⟩
  simpa [two_nsmul] using this

lemma ncard_add_repr_pos_iff (A : Set ℕ) (o n : ℕ) :
    0 < ncard_add_repr A o n ↔
      ∃ a : Fin o → ℕ, Set.range a ⊆ A ∧ ∑ i, a i = n := by
  rw [ncard_add_repr, Set.ncard_pos (add_repr_finite A o n)]
  rfl

lemma mem_nsmul_iff_add_repr (A : Set ℕ) (o n : ℕ) :
    n ∈ o • A ↔ ∃ a : Fin o → ℕ, Set.range a ⊆ A ∧ ∑ i, a i = n := by
  rw [Set.mem_nsmul]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i ↦ a i, ?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      exact (a i).property
    · simpa only [List.sum_ofFn] using ha
  · rintro ⟨a, haA, ha⟩
    let b : Fin o → A := fun i ↦ ⟨a i, haA ⟨i, rfl⟩⟩
    refine ⟨b, ?_⟩
    simpa only [List.sum_ofFn, b] using ha

lemma isAsymptoticAddBasisOfOrder_iff_repr_pos (A : Set ℕ) (o : ℕ) :
    A.IsAsymptoticAddBasisOfOrder o ↔
      ∀ᶠ n in atTop, 0 < ncard_add_repr A o n := by
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop]
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact (ncard_add_repr_pos_iff A o n).2 ((mem_nsmul_iff_add_repr A o n).1 hn)
  · intro h
    filter_upwards [h] with n hn
    exact (mem_nsmul_iff_add_repr A o n).2 ((ncard_add_repr_pos_iff A o n).1 hn)

/-- The exact deterministic output needed from the Larsen--Larsen construction. -/
structure RobustCounterexample where
  A : Set ℕ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  basis : A.IsAsymptoticAddBasisOfOrder 2
  logarithmic_representations :
    ∀ᶠ n : ℕ in atTop, epsilon * Real.log n < ncard_add_repr A 2 n
  every_subbasis_erasable :
    ∀ B ⊆ A, B.IsAsymptoticAddBasisOfOrder 2 →
      ∀ b ∈ B, (B \ {b}).IsAsymptoticAddBasisOfOrder 2

/-- The deterministic consequences extracted from the probabilistic block construction.

The `canary_survives` field is the transversal conclusion: every subbasis has two
canary representations, so one remains after deleting a prescribed element.  The
`target_summands_finite` field is the scale-separation conclusion for the fragile targets. -/
structure ConstructionCertificate where
  A : Set ℕ
  B : Set ℕ
  C : Set ℕ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  basis : A.IsAsymptoticAddBasisOfOrder 2
  logarithmic_representations :
    ∀ᶠ n : ℕ in atTop, epsilon * Real.log n < ncard_add_repr A 2 n
  cover : ∀ᶠ n : ℕ in atTop, n ∈ B ∨ n ∈ C
  canary_survives :
    ∀ D ⊆ A, D.IsAsymptoticAddBasisOfOrder 2 → ∀ d ∈ D,
      ∀ᶠ n : ℕ in atTop, n ∈ C → n ∈ 2 • (D \ {d})
  target_summands_finite :
    ∀ d ∈ A, {n : ℕ | n ∈ B ∧ ∃ a ∈ A, d + a = n}.Finite

/-- The canary/target form delivered directly by the Larsen--Larsen transversal construction.

If a canary has at most one representation in a candidate subbasis `D`, `trap` supplies a
later target that `D` cannot represent. -/
structure TrapCertificate where
  A : Set ℕ
  B : Set ℕ
  C : Set ℕ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  basis : A.IsAsymptoticAddBasisOfOrder 2
  logarithmic_representations :
    ∀ᶠ n : ℕ in atTop, epsilon * Real.log n < ncard_add_repr A 2 n
  cover : ∀ᶠ n : ℕ in atTop, n ∈ B ∨ n ∈ C
  trap :
    ∀ D ⊆ A, ∀ c ∈ C, (unordRepr D c).card ≤ 1 →
      ∃ b ∈ B, c ≤ b ∧ b ∉ 2 • D
  target_summands_finite :
    ∀ d ∈ A, {n : ℕ | n ∈ B ∧ ∃ a ∈ A, d + a = n}.Finite

lemma TrapCertificate.canary_survives (c : TrapCertificate)
    (D : Set ℕ) (hDA : D ⊆ c.A) (hD : D.IsAsymptoticAddBasisOfOrder 2)
    (d : ℕ) (_hdD : d ∈ D) :
    ∀ᶠ n : ℕ in atTop, n ∈ c.C → n ∈ 2 • (D \ {d}) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Set.isAsymptoticAddBasisOfOrder_iff_atTop.1 hD)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro hnC
  have htwo : 2 ≤ (unordRepr D n).card := by
    by_contra hnot
    have hone : (unordRepr D n).card ≤ 1 := by grind
    obtain ⟨b, _hbB, hnb, hbmiss⟩ := c.trap D hDA n hnC hone
    exact hbmiss (hN b (hn.trans hnb))
  exact two_unordRepr_survives_erase htwo

def TrapCertificate.toConstructionCertificate (c : TrapCertificate) :
    ConstructionCertificate where
  A := c.A
  B := c.B
  C := c.C
  epsilon := c.epsilon
  epsilon_pos := c.epsilon_pos
  basis := c.basis
  logarithmic_representations := c.logarithmic_representations
  cover := c.cover
  canary_survives := c.canary_survives
  target_summands_finite := c.target_summands_finite

/-- Union of the finite fragile-target blocks. -/
def stagedSet (S : ℕ → Finset ℕ) : Set ℕ := {x | ∃ n, x ∈ S n}

/-- The four eventual deterministic properties proved by the random block construction.

Here `Cn n` is the canary set in block `n`, while the transversals for it are encoded in
the target block `Bn (n + 10)`. -/
structure StagedTrapCertificate where
  A : Set ℕ
  Bn : ℕ → Finset ℕ
  Cn : ℕ → Finset ℕ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  basis : A.IsAsymptoticAddBasisOfOrder 2
  logarithmic_representations :
    ∀ᶠ n : ℕ in atTop, epsilon * Real.log n < ncard_add_repr A 2 n
  cover : ∀ᶠ n : ℕ in atTop, n ∈ stagedSet Bn ∨ n ∈ stagedSet Cn
  canary_trap :
    ∀ D ⊆ A, ∀ n c, c ∈ Cn n → (unordRepr D c).card ≤ 1 →
      ∃ b ∈ Bn (n + 10), c ≤ b ∧ b ∉ 2 • D
  target_summands_escape :
    ∀ d ∈ A, ∃ N, ∀ n ≥ N, ∀ b ∈ Bn n, ¬∃ a ∈ A, d + a = b

lemma StagedTrapCertificate.target_summands_finite (c : StagedTrapCertificate)
    (d : ℕ) (hdA : d ∈ c.A) :
    {b : ℕ | b ∈ stagedSet c.Bn ∧ ∃ a ∈ c.A, d + a = b}.Finite := by
  obtain ⟨N, hN⟩ := c.target_summands_escape d hdA
  apply (Finset.finite_toSet ((Finset.range N).biUnion c.Bn)).subset
  intro b hb
  obtain ⟨n, hbn⟩ := hb.1
  have hn : n < N := by
    by_contra hn
    exact hN n (Nat.le_of_not_gt hn) b hbn hb.2
  exact Finset.mem_biUnion.2 ⟨n, Finset.mem_range.2 hn, hbn⟩

def StagedTrapCertificate.toTrapCertificate (c : StagedTrapCertificate) : TrapCertificate where
  A := c.A
  B := stagedSet c.Bn
  C := stagedSet c.Cn
  epsilon := c.epsilon
  epsilon_pos := c.epsilon_pos
  basis := c.basis
  logarithmic_representations := c.logarithmic_representations
  cover := c.cover
  trap := by
    intro D hDA canary hcanary hone
    obtain ⟨n, hcn⟩ := hcanary
    obtain ⟨b, hbn, hcb, hbmiss⟩ := c.canary_trap D hDA n canary hcn hone
    exact ⟨b, ⟨n + 10, hbn⟩, hcb, hbmiss⟩
  target_summands_finite := c.target_summands_finite

lemma ConstructionCertificate.every_subbasis_erasable (c : ConstructionCertificate)
    (D : Set ℕ) (hDA : D ⊆ c.A) (hD : D.IsAsymptoticAddBasisOfOrder 2)
    (d : ℕ) (hdD : d ∈ D) :
    (D \ {d}).IsAsymptoticAddBasisOfOrder 2 := by
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop] at hD ⊢
  have hescape : ∀ᶠ n : ℕ in atTop,
      n ∉ {n : ℕ | n ∈ c.B ∧ ∃ a ∈ c.A, d + a = n} := by
    rw [← Nat.cofinite_eq_atTop]
    exact (c.target_summands_finite d (hDA hdD)).compl_mem_cofinite
  filter_upwards [hD, c.cover, c.canary_survives D hDA
    (Set.isAsymptoticAddBasisOfOrder_iff_atTop.2 hD) d hdD, hescape]
      with n hnD hncover hnC hnescape
  rcases hncover with hnB | hnCmem
  · have hnD' : n ∈ D + D := by simpa [two_nsmul] using hnD
    rcases hnD' with ⟨a, haD, b, hbD, hab⟩
    have haA : a ∈ c.A := hDA haD
    have hbA : b ∈ c.A := hDA hbD
    have had : a ≠ d := by
      intro had
      subst a
      exact hnescape ⟨hnB, b, hbA, hab⟩
    have hbd : b ≠ d := by
      intro hbd
      subst b
      exact hnescape ⟨hnB, a, haA, by simpa [add_comm] using hab⟩
    have : n ∈ (D \ {d}) + (D \ {d}) :=
      ⟨a, ⟨haD, by simpa using had⟩, b, ⟨hbD, by simpa using hbd⟩, hab⟩
    simpa [two_nsmul] using this
  · exact hnC hnCmem

def ConstructionCertificate.toRobustCounterexample (c : ConstructionCertificate) :
    RobustCounterexample where
  A := c.A
  epsilon := c.epsilon
  epsilon_pos := c.epsilon_pos
  basis := c.basis
  logarithmic_representations := c.logarithmic_representations
  every_subbasis_erasable := c.every_subbasis_erasable

lemma RobustCounterexample.representations_tendsto (c : RobustCounterexample) :
    Tendsto (fun n ↦ ncard_add_repr c.A 2 n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  have hlog : Tendsto (fun n : ℕ ↦ c.epsilon * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop c.epsilon_pos
  obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp hlog) (N : ℝ)
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp c.logarithmic_representations
  refine ⟨max i j, fun n hn ↦ ?_⟩
  have hN : (N : ℝ) ≤ c.epsilon * Real.log n := hi n (le_trans (le_max_left _ _) hn)
  have hrepr := hj n (le_trans (le_max_right _ _) hn)
  exact_mod_cast (hN.trans hrepr.le)

lemma RobustCounterexample.no_minimal_subbasis (c : RobustCounterexample) :
    ¬∃ B ⊆ c.A, B.IsAsymptoticAddBasisOfOrder 2 ∧
      ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  rintro ⟨B, hBA, hB, hminimal⟩
  have hBne : B.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hB
    rw [isAsymptoticAddBasisOfOrder_iff_repr_pos] at hB
    obtain ⟨n, hn⟩ := hB.exists
    simpa [ncard_add_repr_pos_iff] using hn
  obtain ⟨b, hb⟩ := hBne
  exact hminimal b hb (c.every_subbasis_erasable B hBA hB b hb)

lemma parts_i_of_robustCounterexample (c : RobustCounterexample) :
    ¬ ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      atTop.Tendsto (fun n ↦ ncard_add_repr A 2 n) atTop → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  intro h
  exact c.no_minimal_subbasis (h c.A c.basis c.representations_tendsto)

lemma parts_ii_of_robustCounterexample (c : RobustCounterexample) :
    ¬ ∀ᵉ (A : Set ℕ) (ε > 0), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  intro h
  exact c.no_minimal_subbasis
    (h c.A c.epsilon c.epsilon_pos c.basis c.logarithmic_representations)

/-- The wider geometric scale used for the dense auxiliary reservoir.  Its
ratio `256` makes the probability `8⁻ⁿ` equal to the power law `x⁻³˸⁸`
up to a fixed factor on each block. -/
def Z (k : ℕ) : ℕ := 256 ^ k

def zBlock (k : ℕ) : Finset ℕ := Finset.Ico (Z k) (Z (k + 1))

lemma Z_pos (k : ℕ) : 0 < Z k := pow_pos (by decide) _

lemma Z_ne_zero (k : ℕ) : Z k ≠ 0 := (Z_pos k).ne'

lemma Z_succ (k : ℕ) : Z (k + 1) = 256 * Z k := by
  simp [Z, pow_succ, mul_comm]

lemma Z_mono : Monotone Z := by
  intro a b hab
  exact Nat.pow_le_pow_right (by norm_num) hab

lemma Z_strictMono : StrictMono Z := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) hab

lemma Z_eq_two_pow (k : ℕ) : Z k = 2 ^ (8 * k) := by
  rw [Z, show 256 = 2 ^ 8 by norm_num, ← pow_mul]

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ n := pow_pos (by decide) _
      omega

lemma mem_zBlock {k n : ℕ} : n ∈ zBlock k ↔ Z k ≤ n ∧ n < Z (k + 1) := by
  simp [zBlock]

noncomputable def denseProbReal (n : ℕ) : ℝ :=
  if n = 0 then 1 else (1 / 8 : ℝ) ^ Nat.log 256 n

lemma denseProbReal_nonneg (n : ℕ) : 0 ≤ denseProbReal n := by
  unfold denseProbReal
  split_ifs <;> positivity

lemma denseProbReal_le_one (n : ℕ) : denseProbReal n ≤ 1 := by
  unfold denseProbReal
  split_ifs
  · exact le_rfl
  · exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1)

noncomputable def denseProb (n : ℕ) : {x : ℝ // x ∈ Set.Icc 0 1} :=
  ⟨denseProbReal n, denseProbReal_nonneg n, denseProbReal_le_one n⟩

noncomputable def denseCoordinateMeasure (n : ℕ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (denseProb n)

noncomputable instance (n : ℕ) : IsProbabilityMeasure (denseCoordinateMeasure n) := by
  unfold denseCoordinateMeasure
  infer_instance

abbrev DenseSample := ℕ → Bool

noncomputable def denseMeasure : Measure DenseSample :=
  Measure.infinitePi denseCoordinateMeasure

noncomputable local instance : IsProbabilityMeasure denseMeasure := by
  unfold denseMeasure
  infer_instance

def denseBit (n : ℕ) (ω : DenseSample) : Bool := ω n

lemma denseBit_measurable (n : ℕ) : Measurable (denseBit n) := by
  exact measurable_pi_apply n

lemma denseBit_iIndep : iIndepFun denseBit denseMeasure := by
  change iIndepFun (fun i (ω : ℕ → Bool) ↦ ω i)
    (Measure.infinitePi denseCoordinateMeasure)
  exact iIndepFun_infinitePi (P := denseCoordinateMeasure) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)

lemma denseBit_true_probability (n : ℕ) :
    denseMeasure.real {ω | denseBit n ω = true} = denseProbReal n := by
  change denseMeasure.real ((denseBit n) ⁻¹' {true}) = denseProbReal n
  rw [← map_measureReal_apply (denseBit_measurable n) (MeasurableSet.singleton true)]
  change ((Measure.infinitePi denseCoordinateMeasure).map
    (fun ω : ℕ → Bool ↦ ω n)).real {true} = _
  rw [Measure.infinitePi_map_eval]
  simp [denseCoordinateMeasure, denseProb]

lemma nat_log_256_eq_of_mem_zBlock {k n : ℕ} (hn : n ∈ zBlock k) :
    Nat.log 256 n = k := by
  have h := mem_zBlock.1 hn
  exact Nat.log_eq_of_pow_le_of_lt_pow h.1 h.2

lemma denseProbReal_of_mem_zBlock {k n : ℕ} (hn : n ∈ zBlock k) :
    denseProbReal n = (1 / 8 : ℝ) ^ k := by
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact (Nat.not_le_of_gt (Z_pos k)) (mem_zBlock.1 hn).1
  simp [denseProbReal, hn0, nat_log_256_eq_of_mem_zBlock hn]

lemma denseProbReal_lower_of_lt_Z_succ {k n : ℕ} (hn0 : n ≠ 0)
    (hn : n < Z (k + 1)) : (1 / 8 : ℝ) ^ k ≤ denseProbReal n := by
  rw [denseProbReal, if_neg hn0]
  have hlog : Nat.log 256 n ≤ k := by
    rw [← Nat.lt_succ_iff, Nat.log_lt_iff_lt_pow (by norm_num) hn0]
    simpa [Z] using hn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlog

lemma denseProbReal_lower_of_lt_Z_succ' {k n : ℕ}
    (hn : n < Z (k + 1)) : (1 / 8 : ℝ) ^ k ≤ denseProbReal n := by
  by_cases hn0 : n = 0
  · subst n
    rw [denseProbReal, if_pos rfl]
    exact pow_le_one₀ (by positivity) (by norm_num)
  · exact denseProbReal_lower_of_lt_Z_succ hn0 hn

lemma denseProbReal_upper_of_Z_le {k n : ℕ} (hk : Z k ≤ n) :
    denseProbReal n ≤ (1 / 8 : ℝ) ^ k := by
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact (Nat.not_le_of_gt (Z_pos k)) hk
  rw [denseProbReal, if_neg hn0]
  have hlog : k ≤ Nat.log 256 n := (Nat.le_log_iff_pow_le (by norm_num) hn0).2 hk
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlog

def densePairPresent (lo m : ℕ) (i : strictReprIndices lo m)
    (ω : DenseSample) : Bool :=
  denseBit i ω && denseBit (m - i) ω

lemma densePairPresent_measurable (lo m : ℕ) (i : strictReprIndices lo m) :
    Measurable (densePairPresent lo m i) := by
  unfold densePairPresent
  simpa only [Function.comp_def] using
    (measurable_of_finite (fun x : Bool × Bool ↦ x.1 && x.2)).comp
      ((denseBit_measurable i).prodMk (denseBit_measurable (m - i)))

lemma densePairPresent_iIndep (lo m : ℕ) :
    iIndepFun (densePairPresent lo m) denseMeasure := by
  let Y : (i : strictReprIndices lo m) → (j : Fin 2) → DenseSample → Bool :=
    fun i j ω ↦ denseBit (reprEndpoint lo m ⟨i, j⟩) ω
  have hflat : iIndepFun
      (fun (p : (i : strictReprIndices lo m) × Fin 2) ω ↦ Y p.1 p.2 ω)
      denseMeasure := by
    exact iIndepFun.precomp (reprEndpoint_injective lo m) denseBit_iIndep
  have hgroup : iIndepFun (fun i ω ↦ (Y i · ω)) denseMeasure :=
    iIndepFun_curry_of_uncurry
      (fun i j ↦ denseBit_measurable (reprEndpoint lo m ⟨i, j⟩)) hflat
  have hcomp := hgroup.comp (fun _ x ↦ x 0 && x 1) (fun _ ↦ by fun_prop)
  unfold densePairPresent
  change iIndepFun (fun (i : strictReprIndices lo m) ω ↦
    denseBit (i : ℕ) ω && denseBit (m - (i : ℕ)) ω) denseMeasure
  convert hcomp using 1
  funext i ω
  simp [Y, reprEndpoint]

noncomputable def densePairProbability (lo m : ℕ) (i : strictReprIndices lo m) :
    {x : ℝ // x ∈ Set.Icc 0 1} :=
  ⟨denseProbReal i * denseProbReal (m - i),
    mul_nonneg (denseProbReal_nonneg _) (denseProbReal_nonneg _),
    mul_le_one₀ (denseProbReal_le_one _) (denseProbReal_nonneg _)
      (denseProbReal_le_one _)⟩

noncomputable def densePairMean (lo m : ℕ) : ℝ :=
  ∑ i : strictReprIndices lo m, (densePairProbability lo m i : ℝ)

noncomputable def densePairSum (lo m : ℕ) (ω : DenseSample) : ℝ :=
  ∑ i : strictReprIndices lo m, boolIndicator (densePairPresent lo m i) ω

lemma densePairPresent_true_probability (lo m : ℕ) (i : strictReprIndices lo m) :
    denseMeasure.real {ω | densePairPresent lo m i ω = true} =
      denseProbReal i * denseProbReal (m - i) := by
  have hind := denseBit_iIndep.indepFun (strictRepr_left_ne_right lo m i)
  have h := hind.measure_inter_preimage_eq_mul {true} {true}
    (MeasurableSet.singleton true) (MeasurableSet.singleton true)
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul] at hr
  change denseMeasure.real
      (denseBit i ⁻¹' {true} ∩ denseBit (m - i) ⁻¹' {true}) =
    denseMeasure.real (denseBit i ⁻¹' {true}) *
      denseMeasure.real (denseBit (m - i) ⁻¹' {true}) at hr
  have hpi : denseMeasure.real (denseBit i ⁻¹' {true}) = denseProbReal i := by
    rw [show denseBit i ⁻¹' {true} = {ω | denseBit i ω = true} by ext ω; simp]
    exact denseBit_true_probability i
  have hpj : denseMeasure.real (denseBit (m - i) ⁻¹' {true}) =
      denseProbReal (m - i) := by
    rw [show denseBit (m - i) ⁻¹' {true} =
        {ω | denseBit (m - i) ω = true} by ext ω; simp]
    exact denseBit_true_probability (m - i)
  rw [hpi, hpj] at hr
  rw [show {ω | densePairPresent lo m i ω = true} =
      denseBit i ⁻¹' {true} ∩ denseBit (m - i) ⁻¹' {true} by
    ext ω
    simp [densePairPresent]]
  exact hr

lemma densePairPresent_map (lo m : ℕ) (i : strictReprIndices lo m) :
    denseMeasure.map (densePairPresent lo m i) =
      ProbabilityTheory.bernoulliMeasure true false (densePairProbability lo m i) := by
  letI : IsProbabilityMeasure (denseMeasure.map (densePairPresent lo m i)) :=
    Measure.isProbabilityMeasure_map (densePairPresent_measurable lo m i).aemeasurable
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (densePairPresent_measurable lo m i)
    (MeasurableSet.singleton b)]
  cases b with
  | false =>
      have hcompl : {ω | densePairPresent lo m i ω = false} =
          {ω | densePairPresent lo m i ω = true}ᶜ := by
        ext ω
        cases h : densePairPresent lo m i ω <;> simp [h]
      rw [show (densePairPresent lo m i ⁻¹' {false}) =
          {ω | densePairPresent lo m i ω = false} by rfl, hcompl,
        measureReal_compl (s := {ω | densePairPresent lo m i ω = true})
          (densePairPresent_measurable lo m i (MeasurableSet.singleton true))]
      simp [densePairProbability, densePairPresent_true_probability]
  | true =>
      rw [show (densePairPresent lo m i ⁻¹' {true}) =
          {ω | densePairPresent lo m i ω = true} by ext ω; simp]
      simpa [densePairProbability] using densePairPresent_true_probability lo m i

lemma densePairIndicator_mgf (lo m : ℕ) (i : strictReprIndices lo m) (t : ℝ) :
    mgf (boolIndicator (densePairPresent lo m i)) denseMeasure t =
      (1 - densePairProbability lo m i : ℝ) +
        (densePairProbability lo m i : ℝ) * Real.exp t := by
  unfold boolIndicator
  change mgf ((fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ densePairPresent lo m i)
    denseMeasure t = _
  rw [← mgf_map (Y := densePairPresent lo m i)
    (densePairPresent_measurable lo m i).aemeasurable (by fun_prop)]
  rw [densePairPresent_map, mgf, ProbabilityTheory.integral_bernoulliMeasure]
  simp [boolIndicator, mul_comm, add_comm]

lemma densePairIndicator_iIndep (lo m : ℕ) :
    iIndepFun (fun i ↦ boolIndicator (densePairPresent lo m i)) denseMeasure := by
  exact (densePairPresent_iIndep lo m).comp (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)

lemma densePairSum_measurable (lo m : ℕ) : Measurable (densePairSum lo m) := by
  unfold densePairSum
  apply Finset.measurable_sum Finset.univ
  intro i hi
  exact boolIndicator_measurable (densePairPresent_measurable lo m i)

lemma densePairSum_mgf_le (lo m : ℕ) (t : ℝ) :
    mgf (densePairSum lo m) denseMeasure t ≤
      Real.exp ((Real.exp t - 1) * densePairMean lo m) := by
  unfold densePairSum
  calc
    mgf (fun ω ↦ ∑ i : strictReprIndices lo m,
        boolIndicator (densePairPresent lo m i) ω) denseMeasure t =
      mgf (∑ i : strictReprIndices lo m,
        boolIndicator (densePairPresent lo m i)) denseMeasure t := by
          congr 1
          funext ω
          simp
    _ = ∏ i : strictReprIndices lo m,
        mgf (boolIndicator (densePairPresent lo m i)) denseMeasure t := by
      simpa using (densePairIndicator_iIndep lo m).mgf_sum
        (fun i ↦ boolIndicator_measurable (densePairPresent_measurable lo m i))
        Finset.univ (t := t)
    _ = ∏ i : strictReprIndices lo m,
        ((1 - densePairProbability lo m i : ℝ) +
          (densePairProbability lo m i : ℝ) * Real.exp t) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact densePairIndicator_mgf lo m i t
    _ ≤ ∏ i : strictReprIndices lo m,
        Real.exp ((densePairProbability lo m i : ℝ) * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        have hp0 := (densePairProbability lo m i).property.1
        have hp1 := (densePairProbability lo m i).property.2
        positivity
      · intro i hi
        calc
          (1 - densePairProbability lo m i : ℝ) +
              (densePairProbability lo m i : ℝ) * Real.exp t =
            1 + (densePairProbability lo m i : ℝ) * (Real.exp t - 1) := by ring
          _ ≤ _ := by simpa [add_comm] using
            Real.add_one_le_exp ((densePairProbability lo m i : ℝ) * (Real.exp t - 1))
    _ = Real.exp (∑ i : strictReprIndices lo m,
        (densePairProbability lo m i : ℝ) * (Real.exp t - 1)) := by
      rw [← Real.exp_sum]
    _ = Real.exp ((Real.exp t - 1) * densePairMean lo m) := by
      congr 1
      unfold densePairMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma densePairMean_nonneg (lo m : ℕ) : 0 ≤ densePairMean lo m := by
  unfold densePairMean
  exact Finset.sum_nonneg fun i hi ↦ (densePairProbability lo m i).property.1

lemma densePairSum_nonneg (lo m : ℕ) (ω : DenseSample) : 0 ≤ densePairSum lo m ω := by
  unfold densePairSum
  apply Finset.sum_nonneg
  intro i hi
  cases h : densePairPresent lo m i ω <;> simp [boolIndicator, h]

lemma densePairSum_le_card (lo m : ℕ) (ω : DenseSample) :
    densePairSum lo m ω ≤ Fintype.card (strictReprIndices lo m) := by
  unfold densePairSum
  calc
    (∑ i : strictReprIndices lo m, boolIndicator (densePairPresent lo m i) ω) ≤
        ∑ _i : strictReprIndices lo m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      cases h : densePairPresent lo m i ω <;> simp [boolIndicator, h]
    _ = _ := by simp

lemma densePairSum_exp_integrable (lo m : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * densePairSum lo m ω)) denseMeasure := by
  apply Integrable.of_bound ((densePairSum_measurable lo m).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * Fintype.card (strictReprIndices lo m)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h0 := densePairSum_nonneg lo m ω
  have hc := densePairSum_le_card lo m ω
  have ht : t ≤ |t| := le_abs_self t
  nlinarith [abs_nonneg t]

lemma densePairSum_lower_tail (lo m : ℕ) (a t : ℝ) (ht : t ≤ 0) :
    denseMeasure.real {ω | densePairSum lo m ω ≤ a} ≤
      Real.exp (-t * a + (Real.exp t - 1) * densePairMean lo m) := by
  calc
    denseMeasure.real {ω | densePairSum lo m ω ≤ a} ≤
        Real.exp (-t * a) * mgf (densePairSum lo m) denseMeasure t :=
      measure_le_le_exp_mul_mgf a ht (densePairSum_exp_integrable lo m t)
    _ ≤ Real.exp (-t * a) *
        Real.exp ((Real.exp t - 1) * densePairMean lo m) :=
      mul_le_mul_of_nonneg_left (densePairSum_mgf_le lo m t) (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_add]

lemma densePairSum_half_mean_tail (lo m : ℕ) :
    denseMeasure.real {ω | densePairSum lo m ω ≤ densePairMean lo m / 2} ≤
      Real.exp (-(densePairMean lo m) / 10) := by
  have hexp : Real.exp (-1) ≤ (2 / 5 : ℝ) :=
    Real.exp_neg_one_lt_d9.le.trans (by norm_num)
  calc
    denseMeasure.real {ω | densePairSum lo m ω ≤ densePairMean lo m / 2} ≤
      Real.exp (-(-1 : ℝ) * (densePairMean lo m / 2) +
        (Real.exp (-1) - 1) * densePairMean lo m) :=
      densePairSum_lower_tail lo m _ (-1) (by norm_num)
    _ ≤ Real.exp (-(densePairMean lo m) / 10) := by
      apply Real.exp_le_exp.mpr
      have hm := densePairMean_nonneg lo m
      nlinarith

lemma densePairProbability_lower_on_zBlock {k m : ℕ} (hm : m ∈ zBlock k)
    (i : strictReprIndices (m / 3) m) :
    (1 / 64 : ℝ) ^ k ≤ (densePairProbability (m / 3) m i : ℝ) := by
  have hi := Finset.mem_filter.1 i.property
  have hilo : m / 3 ≤ (i : ℕ) := (Finset.mem_Icc.1 hi.1).1
  have histrict : 2 * (i : ℕ) < m := hi.2
  have him : (i : ℕ) < Z (k + 1) :=
    (Finset.mem_Icc.1 hi.1).2.trans_lt (mem_zBlock.1 hm).2
  have hjpos : m - (i : ℕ) ≠ 0 := by omega
  have hjm : m - (i : ℕ) < Z (k + 1) :=
    (Nat.sub_le m i).trans_lt (mem_zBlock.1 hm).2
  have hpi := denseProbReal_lower_of_lt_Z_succ' him
  have hpj := denseProbReal_lower_of_lt_Z_succ hjpos hjm
  change (1 / 64 : ℝ) ^ k ≤ denseProbReal i * denseProbReal (m - i)
  calc
    (1 / 64 : ℝ) ^ k = (1 / 8 : ℝ) ^ k * (1 / 8 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    _ ≤ _ := mul_le_mul hpi hpj (by positivity) (denseProbReal_nonneg _)

lemma densePairMean_lower_on_zBlock {k m : ℕ} (hm : m ∈ zBlock k)
    (hm20 : 20 ≤ m) :
    (4 : ℝ) ^ k / 20 ≤ densePairMean (m / 3) m := by
  have hcardNat := ten_card_strictReprIndices_ge m
  have hfloor : m ≤ 20 * (m / 10) := by omega
  have hcard : (m : ℝ) / 20 ≤
      Fintype.card (strictReprIndices (m / 3) m) := by
    have hfloorR : (m : ℝ) ≤ 20 * (m / 10 : ℕ) := by exact_mod_cast hfloor
    have hc : (m / 10 : ℕ) ≤
        (Fintype.card (strictReprIndices (m / 3) m) : ℝ) := by exact_mod_cast hcardNat
    nlinarith
  have hmZ : (Z k : ℝ) ≤ m := by exact_mod_cast (mem_zBlock.1 hm).1
  have hp0 : 0 ≤ (1 / 64 : ℝ) ^ k := by positivity
  calc
    (4 : ℝ) ^ k / 20 = (Z k : ℝ) / 20 * (1 / 64 : ℝ) ^ k := by
      rw [Z, Nat.cast_pow, Nat.cast_ofNat]
      rw [div_mul_eq_mul_div, ← mul_pow]
      norm_num
    _ ≤ (m : ℝ) / 20 * (1 / 64 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmZ (by norm_num)) hp0
    _ ≤ (Fintype.card (strictReprIndices (m / 3) m) : ℝ) *
        (1 / 64 : ℝ) ^ k := mul_le_mul_of_nonneg_right hcard hp0
    _ = ∑ _i : strictReprIndices (m / 3) m, (1 / 64 : ℝ) ^ k := by simp
    _ ≤ ∑ i : strictReprIndices (m / 3) m,
        (densePairProbability (m / 3) m i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact densePairProbability_lower_on_zBlock hm i
    _ = densePairMean (m / 3) m := rfl

def denseReprBad (k m : ℕ) : Set DenseSample :=
  {ω | densePairSum (m / 3) m ω ≤ (4 : ℝ) ^ k / 40}

lemma denseReprBad_measurable (k m : ℕ) :
    MeasurableSet (denseReprBad k m) := by
  exact measurableSet_le (densePairSum_measurable (m / 3) m) measurable_const

lemma denseReprBad_measureReal_le {k m : ℕ} (hm : m ∈ zBlock k)
    (hm20 : 20 ≤ m) :
    denseMeasure.real (denseReprBad k m) ≤
      Real.exp (-((4 : ℝ) ^ k) / 200) := by
  have hmean := densePairMean_lower_on_zBlock hm hm20
  calc
    denseMeasure.real (denseReprBad k m) ≤
        denseMeasure.real
          {ω | densePairSum (m / 3) m ω ≤ densePairMean (m / 3) m / 2} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change densePairSum (m / 3) m ω ≤ (4 : ℝ) ^ k / 40 at hω
      change densePairSum (m / 3) m ω ≤ densePairMean (m / 3) m / 2
      nlinarith
    _ ≤ Real.exp (-(densePairMean (m / 3) m) / 10) :=
      densePairSum_half_mean_tail (m / 3) m
    _ ≤ Real.exp (-((4 : ℝ) ^ k) / 200) := by
      apply Real.exp_le_exp.mpr
      nlinarith

def denseReprStageBad (k : ℕ) : Set DenseSample :=
  ⋃ m ∈ zBlock k, denseReprBad k m

lemma denseReprStageBad_measurable (k : ℕ) :
    MeasurableSet (denseReprStageBad k) := by
  unfold denseReprStageBad
  exact Finset.measurableSet_biUnion (zBlock k) fun m _hm ↦
    denseReprBad_measurable k m

lemma denseReprStageBad_measureReal_le_sum (k : ℕ) :
    denseMeasure.real (denseReprStageBad k) ≤
      ∑ m ∈ zBlock k, denseMeasure.real (denseReprBad k m) := by
  exact measureReal_biUnion_finset_le (zBlock k) (denseReprBad k)

lemma zBlock_card_le_Z_succ (k : ℕ) : (zBlock k).card ≤ Z (k + 1) := by
  rw [zBlock, Nat.card_Ico]
  omega

lemma denseReprStageBad_measureReal_le {k : ℕ} (hk : 1 ≤ k) :
    denseMeasure.real (denseReprStageBad k) ≤
      (Z (k + 1) : ℝ) * Real.exp (-((4 : ℝ) ^ k) / 200) := by
  have hZ20 : 20 ≤ Z k := by
    calc
      20 ≤ Z 1 := by norm_num [Z]
      _ ≤ Z k := by
        exact Nat.pow_le_pow_right (by norm_num) hk
  calc
    denseMeasure.real (denseReprStageBad k) ≤
        ∑ m ∈ zBlock k, denseMeasure.real (denseReprBad k m) :=
      denseReprStageBad_measureReal_le_sum k
    _ ≤ ∑ _m ∈ zBlock k, Real.exp (-((4 : ℝ) ^ k) / 200) := by
      apply Finset.sum_le_sum
      intro m hm
      exact denseReprBad_measureReal_le hm
        (hZ20.trans (mem_zBlock.1 hm).1)
    _ = (zBlock k).card * Real.exp (-((4 : ℝ) ^ k) / 200) := by simp
    _ ≤ (Z (k + 1) : ℝ) * Real.exp (-((4 : ℝ) ^ k) / 200) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast zBlock_card_le_Z_succ k
      · positivity

lemma two_thousand_mul_le_four_pow {k : ℕ} (hk : 8 ≤ k) :
    2000 * k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk h =>
      calc
        2000 * (k + 1) ≤ 4 * (2000 * k) := by omega
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 h
        _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

lemma Z_cast_le_exp_eight_mul (k : ℕ) :
    (Z k : ℝ) ≤ Real.exp (8 * k) := by
  have hbase : (256 : ℝ) ≤ Real.exp 8 := by
    calc
      (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 8
      _ = Real.exp 8 := by
        rw [← Real.exp_nat_mul]
        norm_num
  rw [Z, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (256 : ℝ) ^ k ≤ (Real.exp 8) ^ k :=
      pow_le_pow_left₀ (by norm_num) hbase k
    _ = Real.exp (8 * k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

lemma denseReprStageBad_measureReal_le_exp_neg {k : ℕ} (hk : 8 ≤ k) :
    denseMeasure.real (denseReprStageBad k) ≤ Real.exp (-(k : ℝ)) := by
  have hpowNat := two_thousand_mul_le_four_pow hk
  have hpow : (2000 : ℝ) * k ≤ (4 : ℝ) ^ k := by exact_mod_cast hpowNat
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    denseMeasure.real (denseReprStageBad k) ≤
        (Z (k + 1) : ℝ) * Real.exp (-((4 : ℝ) ^ k) / 200) :=
      denseReprStageBad_measureReal_le (by omega)
    _ ≤ Real.exp (8 * (k + 1)) * Real.exp (-((4 : ℝ) ^ k) / 200) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using Z_cast_le_exp_eight_mul (k + 1)
    _ = Real.exp (8 * (k + 1) - (4 : ℝ) ^ k / 200) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma summable_denseReprStageBad_measureReal :
    Summable (fun k : ℕ ↦ denseMeasure.real (denseReprStageBad k)) := by
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 8] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact denseReprStageBad_measureReal_le_exp_neg hk

lemma tsum_denseReprStageBad_ne_top :
    (∑' k : ℕ, denseMeasure (denseReprStageBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ denseMeasure (denseReprStageBad k)) =
      (fun k ↦ ((denseMeasure (denseReprStageBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_denseReprStageBad_measureReal

lemma ae_eventually_dense_pair_lower :
    ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < densePairSum (m / 3) m ω := by
  have hae : ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ω ∉ denseReprStageBad k :=
    MeasureTheory.ae_eventually_notMem tsum_denseReprStageBad_ne_top
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  intro m hm
  have hnot : ω ∉ denseReprBad k m := by
    intro hbad
    exact hk (by
      unfold denseReprStageBad
      exact Set.mem_iUnion_of_mem m (Set.mem_iUnion_of_mem hm hbad))
  exact lt_of_not_ge hnot

/-! Dense-reservoir point-count estimates. -/

lemma denseBit_map (n : ℕ) :
    denseMeasure.map (denseBit n) = denseCoordinateMeasure n := by
  change (Measure.infinitePi denseCoordinateMeasure).map
      (fun ω : ℕ → Bool ↦ ω n) = denseCoordinateMeasure n
  exact Measure.infinitePi_map_eval denseCoordinateMeasure n

lemma densePointIndicator_mgf (n : ℕ) (t : ℝ) :
    mgf (boolIndicator (denseBit n)) denseMeasure t =
      (1 - denseProbReal n) + denseProbReal n * Real.exp t := by
  unfold boolIndicator
  change mgf ((fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ denseBit n)
    denseMeasure t = _
  rw [← mgf_map (Y := denseBit n)
    (denseBit_measurable n).aemeasurable (by fun_prop)]
  rw [denseBit_map, denseCoordinateMeasure, mgf,
    ProbabilityTheory.integral_bernoulliMeasure]
  simp [denseProb, mul_comm, add_comm]

noncomputable def densePointMean (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, denseProbReal n

noncomputable def densePointSum (S : Finset ℕ) (ω : DenseSample) : ℝ :=
  ∑ n ∈ S, boolIndicator (denseBit n) ω

lemma densePointIndicator_iIndep (S : Finset ℕ) :
    iIndepFun (fun n : S ↦ boolIndicator (denseBit n)) denseMeasure := by
  have hbits : iIndepFun (fun n : S ↦ denseBit n) denseMeasure :=
    iIndepFun.precomp Subtype.val_injective denseBit_iIndep
  exact hbits.comp (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)

lemma densePointSum_measurable (S : Finset ℕ) : Measurable (densePointSum S) := by
  unfold densePointSum
  apply Finset.measurable_sum S

  intro n _hn
  exact boolIndicator_measurable (denseBit_measurable n)

lemma densePointSum_mgf_le (S : Finset ℕ) (t : ℝ) :
    mgf (densePointSum S) denseMeasure t ≤
      Real.exp ((Real.exp t - 1) * densePointMean S) := by
  calc
    mgf (densePointSum S) denseMeasure t =
        mgf (fun ω ↦ ∑ n : S, boolIndicator (denseBit n) ω)
          denseMeasure t := by
      congr 1
      funext ω
      unfold densePointSum
      have huniv : (Finset.univ : Finset S) = S.attach := by ext n; simp
      rw [huniv]
      exact (Finset.sum_attach S
        (fun n ↦ boolIndicator (denseBit n) ω)).symm
    _ = mgf (∑ n : S, boolIndicator (denseBit n)) denseMeasure t := by
      congr 1
      funext ω
      simp
    _ = ∏ n : S, mgf (boolIndicator (denseBit n)) denseMeasure t := by
      simpa using (densePointIndicator_iIndep S).mgf_sum
        (fun n ↦ boolIndicator_measurable (denseBit_measurable n)) Finset.univ (t := t)
    _ = ∏ n : S, ((1 - denseProbReal n) + denseProbReal n * Real.exp t) := by
      apply Finset.prod_congr rfl
      intro n _hn
      exact densePointIndicator_mgf n t
    _ ≤ ∏ n : S, Real.exp (denseProbReal n * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro n _hn
        have hp0 := denseProbReal_nonneg n
        have hp1 := denseProbReal_le_one n
        positivity
      · intro n _hn
        calc
          (1 - denseProbReal n) + denseProbReal n * Real.exp t =
              1 + denseProbReal n * (Real.exp t - 1) := by ring
          _ ≤ Real.exp (denseProbReal n * (Real.exp t - 1)) :=
            by simpa [add_comm] using
              Real.add_one_le_exp (denseProbReal n * (Real.exp t - 1))
    _ = Real.exp (∑ n : S, denseProbReal n * (Real.exp t - 1)) := by
      rw [← Real.exp_sum]
    _ = Real.exp ((Real.exp t - 1) * densePointMean S) := by
      congr 1
      unfold densePointMean
      rw [Finset.mul_sum]
      rw [Finset.sum_subtype S (fun x ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

lemma densePointMean_nonneg (S : Finset ℕ) : 0 ≤ densePointMean S := by
  unfold densePointMean
  exact Finset.sum_nonneg fun n _hn ↦ denseProbReal_nonneg n

lemma densePointSum_nonneg (S : Finset ℕ) (ω : DenseSample) :
    0 ≤ densePointSum S ω := by
  unfold densePointSum
  apply Finset.sum_nonneg
  intro n _hn
  cases h : denseBit n ω <;> simp [boolIndicator, h]

lemma densePointSum_le_card (S : Finset ℕ) (ω : DenseSample) :
    densePointSum S ω ≤ S.card := by
  unfold densePointSum
  calc
    (∑ n ∈ S, boolIndicator (denseBit n) ω) ≤ ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _hn
      cases h : denseBit n ω <;> simp [boolIndicator, h]
    _ = S.card := by simp

lemma densePointSum_exp_integrable (S : Finset ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * densePointSum S ω)) denseMeasure := by
  apply Integrable.of_bound ((densePointSum_measurable S).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * S.card))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h0 := densePointSum_nonneg S ω
  have hc := densePointSum_le_card S ω
  have ht : t ≤ |t| := le_abs_self t
  nlinarith [abs_nonneg t]

lemma densePointSum_upper_tail (S : Finset ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    denseMeasure.real {ω | a ≤ densePointSum S ω} ≤
      Real.exp (-t * a + (Real.exp t - 1) * densePointMean S) := by
  calc
    denseMeasure.real {ω | a ≤ densePointSum S ω} ≤
        Real.exp (-t * a) * mgf (densePointSum S) denseMeasure t :=
      measure_ge_le_exp_mul_mgf a ht (densePointSum_exp_integrable S t)
    _ ≤ Real.exp (-t * a) *
        Real.exp ((Real.exp t - 1) * densePointMean S) :=
      mul_le_mul_of_nonneg_left (densePointSum_mgf_le S t) (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_add]

def denseInitialIndices (k : ℕ) : Finset ℕ := Finset.range (Z (k + 1))

lemma denseProbSum_zBlock_le (k : ℕ) :
    ∑ n ∈ zBlock k, denseProbReal n ≤ (256 : ℝ) * 32 ^ k := by
  calc
    ∑ n ∈ zBlock k, denseProbReal n =
        ∑ _n ∈ zBlock k, (1 / 8 : ℝ) ^ k := by
      apply Finset.sum_congr rfl
      intro n hn
      exact denseProbReal_of_mem_zBlock hn
    _ = (zBlock k).card * (1 / 8 : ℝ) ^ k := by simp
    _ ≤ (Z (k + 1) : ℝ) * (1 / 8 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast zBlock_card_le_Z_succ k
      · positivity
    _ = (256 : ℝ) * 32 ^ k := by
      rw [Z, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        (256 : ℝ) ^ k * 256 * (1 / 8 : ℝ) ^ k =
            256 * ((256 : ℝ) ^ k * (1 / 8 : ℝ) ^ k) := by ring
        _ = 256 * (((256 : ℝ) * (1 / 8 : ℝ)) ^ k) := by rw [mul_pow]
        _ = (256 : ℝ) * 32 ^ k := by norm_num

lemma densePointMean_initial_le (k : ℕ) :
    densePointMean (denseInitialIndices k) ≤ (300 : ℝ) * 32 ^ (k + 1) := by
  induction k with
  | zero =>
      unfold densePointMean denseInitialIndices
      calc
        ∑ n ∈ Finset.range (Z (0 + 1)), denseProbReal n ≤
            ∑ _n ∈ Finset.range (Z (0 + 1)), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n _hn
          exact denseProbReal_le_one n
        _ = (Z 1 : ℕ) := by simp
        _ ≤ (300 : ℝ) * 32 ^ (0 + 1) := by norm_num [Z]
  | succ k h =>
      have hZ : Z (k + 1) ≤ Z (k + 2) := by
        unfold Z
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsplit : densePointMean (denseInitialIndices (k + 1)) =
          densePointMean (denseInitialIndices k) +
            ∑ n ∈ zBlock (k + 1), denseProbReal n := by
        unfold densePointMean denseInitialIndices zBlock
        rw [Finset.sum_range_add_sum_Ico _ hZ]
      rw [hsplit]
      calc
        densePointMean (denseInitialIndices k) +
              ∑ n ∈ zBlock (k + 1), denseProbReal n ≤
            (300 : ℝ) * 32 ^ (k + 1) + 256 * 32 ^ (k + 1) :=
          add_le_add h (denseProbSum_zBlock_le (k + 1))
        _ ≤ (300 : ℝ) * 32 ^ ((k + 1) + 1) := by
          calc
            (300 : ℝ) * 32 ^ (k + 1) + 256 * 32 ^ (k + 1) =
                556 * 32 ^ (k + 1) := by ring
            _ ≤ 9600 * 32 ^ (k + 1) := by gcongr <;> norm_num
            _ = 300 * 32 ^ ((k + 1) + 1) := by rw [pow_succ]; ring

lemma densePoint_threshold_domination {k : ℕ} (hk : 10 ≤ k) :
    600 * 32 ^ (k + 1) + k ≤ 64 ^ (k + 1) := by
  have hpow : 1200 ≤ 2 ^ (k + 1) := by
    calc
      1200 ≤ 2 ^ 11 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlarge : 1200 * 32 ^ (k + 1) ≤ 64 ^ (k + 1) := by
    rw [show (64 : ℕ) = 2 * 32 by norm_num, mul_pow]
    exact Nat.mul_le_mul_right (32 ^ (k + 1)) hpow
  have hkpow : k ≤ 600 * 32 ^ (k + 1) := by
    have htwo : k < 2 ^ k := k.lt_two_pow_self
    have hbase : 2 ^ k ≤ 32 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have hstep : 32 ^ k ≤ 32 ^ (k + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

def densePointUpperBad (k : ℕ) : Set DenseSample :=
  {ω | (64 : ℝ) ^ (k + 1) ≤ densePointSum (denseInitialIndices k) ω}

lemma densePointUpperBad_measurable (k : ℕ) :
    MeasurableSet (densePointUpperBad k) := by
  exact measurableSet_le measurable_const (densePointSum_measurable _)

lemma densePointUpperBad_measureReal_le_exp_neg {k : ℕ} (hk : 10 ≤ k) :
    denseMeasure.real (densePointUpperBad k) ≤ Real.exp (-(k : ℝ)) := by
  have hmean := densePointMean_initial_le k
  have hexp : Real.exp 1 - 1 ≤ 2 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hterm : (Real.exp 1 - 1) * densePointMean (denseInitialIndices k) ≤
      600 * 32 ^ (k + 1) := by
    calc
      (Real.exp 1 - 1) * densePointMean (denseInitialIndices k) ≤
          2 * densePointMean (denseInitialIndices k) :=
        mul_le_mul_of_nonneg_right hexp (densePointMean_nonneg _)
      _ ≤ 600 * 32 ^ (k + 1) := by nlinarith
  have hdomNat := densePoint_threshold_domination hk
  have hdom : (600 : ℝ) * 32 ^ (k + 1) + k ≤ 64 ^ (k + 1) := by
    exact_mod_cast hdomNat
  calc
    denseMeasure.real (densePointUpperBad k) ≤
        Real.exp (-(1 : ℝ) * (64 : ℝ) ^ (k + 1) +
          (Real.exp 1 - 1) * densePointMean (denseInitialIndices k)) :=
      densePointSum_upper_tail _ _ 1 (by norm_num)
    _ ≤ Real.exp (-(k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma summable_densePointUpperBad_measureReal :
    Summable (fun k : ℕ ↦ denseMeasure.real (densePointUpperBad k)) := by
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 10] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact densePointUpperBad_measureReal_le_exp_neg hk

lemma tsum_densePointUpperBad_ne_top :
    (∑' k : ℕ, denseMeasure (densePointUpperBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ denseMeasure (densePointUpperBad k)) =
      (fun k ↦ ((denseMeasure (densePointUpperBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_densePointUpperBad_measureReal

lemma ae_eventually_dense_point_upper :
    ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      densePointSum (denseInitialIndices k) ω < (64 : ℝ) ^ (k + 1) := by
  have hae : ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ω ∉ densePointUpperBad k :=
    MeasureTheory.ae_eventually_notMem tsum_densePointUpperBad_ne_top
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  exact lt_of_not_ge hk

/-! Collision control for the dense reservoir. -/

def denseAllSelected {ι : Type*} [Fintype ι] (e : ι → ℕ) : Set DenseSample :=
  {ω | ∀ i, denseBit (e i) ω = true}

lemma denseAllSelected_measurable {ι : Type*} [Fintype ι] (e : ι → ℕ) :
    MeasurableSet (denseAllSelected e) := by
  rw [show denseAllSelected e = ⋂ i, denseBit (e i) ⁻¹' {true} by
    ext ω
    simp [denseAllSelected]]
  exact MeasurableSet.iInter fun i ↦
    denseBit_measurable (e i) (MeasurableSet.singleton true)

lemma denseMeasureReal_allSelected_eq_prod {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) :
    denseMeasure.real (denseAllSelected e) = ∏ i, denseProbReal (e i) := by
  have hind : iIndepFun (fun i ω ↦ denseBit (e i) ω) denseMeasure :=
    iIndepFun.precomp he denseBit_iIndep
  have h := hind.measure_inter_preimage_eq_mul (Finset.univ : Finset ι)
    (sets := fun _ ↦ {true}) (fun _ _ ↦ MeasurableSet.singleton true)
  have hr := congrArg ENNReal.toReal h
  have hset : (⋂ i ∈ (Finset.univ : Finset ι),
      (fun ω ↦ denseBit (e i) ω) ⁻¹' {true}) = denseAllSelected e := by
    ext ω
    simp [denseAllSelected]
  rw [hset] at hr
  rw [ENNReal.toReal_prod] at hr
  have hcoord : ∀ i : ι,
      (denseMeasure ((fun ω ↦ denseBit (e i) ω) ⁻¹' {true})).toReal =
        denseProbReal (e i) := by
    intro i
    change denseMeasure.real {ω | denseBit (e i) ω = true} = _
    exact denseBit_true_probability (e i)
  simp_rw [hcoord] at hr
  exact hr

lemma denseMeasureReal_allSelected_le_pow {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) (P : ℝ)
    (_hP0 : 0 ≤ P) (hprob : ∀ i, denseProbReal (e i) ≤ P) :
    denseMeasure.real (denseAllSelected e) ≤ P ^ Fintype.card ι := by
  rw [denseMeasureReal_allSelected_eq_prod e he]
  calc
    (∏ i, denseProbReal (e i)) ≤ ∏ _i : ι, P := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact denseProbReal_nonneg _
      · intro i _hi
        exact hprob i
    _ = P ^ Fintype.card ι := by simp

def denseExtendedAtScale (N x : ℕ) : Prop :=
  N / 4 ≤ x ∧ x ≤ 256 * N

abbrev DenseCollisionTuple (N : ℕ) := Fin 20 → Fin (256 * N + 1)

def denseCollisionTupleEndpoint (q r : ℕ) {N : ℕ}
    (ys : DenseCollisionTuple N) (p : Fin 20 × Fin 3) : ℕ :=
  tripleEndpoint q r (ys p.1) p.2

def denseCollisionTupleGood (N q r : ℕ) (ys : DenseCollisionTuple N) : Prop :=
  q ≠ r ∧
    (∀ i, (ys i : ℕ) ≤ q ∧ (ys i : ℕ) ≤ r) ∧
    (∀ p, denseExtendedAtScale N (denseCollisionTupleEndpoint q r ys p)) ∧
    Function.Injective (denseCollisionTupleEndpoint q r ys)

lemma denseProbReal_extended_upper {k x : ℕ} (hk : 1 ≤ k)
    (hx : denseExtendedAtScale (Z k) x) :
    denseProbReal x ≤ 8 * (1 / 8 : ℝ) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hlo : Z j ≤ x := by
    have hxlo := hx.1
    rw [Z_succ] at hxlo
    have hZpos := Z_pos j
    omega
  calc
    denseProbReal x ≤ (1 / 8 : ℝ) ^ j := denseProbReal_upper_of_Z_le hlo
    _ = 8 * (1 / 8 : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      ring

noncomputable def denseCollisionTupleEvent (N q r : ℕ) (ys : DenseCollisionTuple N) :
    Set DenseSample := by
  classical
  exact if denseCollisionTupleGood N q r ys then
      denseAllSelected (denseCollisionTupleEndpoint q r ys)
    else ∅

lemma denseCollisionTupleEvent_measurable (N q r : ℕ) (ys : DenseCollisionTuple N) :
    MeasurableSet (denseCollisionTupleEvent N q r ys) := by
  classical
  unfold denseCollisionTupleEvent
  split_ifs
  · exact denseAllSelected_measurable _
  · exact MeasurableSet.empty

lemma denseCollisionTupleEvent_measureReal_le (k q r : ℕ)
    (ys : DenseCollisionTuple (Z k)) (hk : 1 ≤ k) :
    denseMeasure.real (denseCollisionTupleEvent (Z k) q r ys) ≤
      (8 * (1 / 8 : ℝ) ^ k) ^ 60 := by
  classical
  unfold denseCollisionTupleEvent
  split_ifs with hgood
  · have hcard : Fintype.card (Fin 20 × Fin 3) = 60 := by decide
    rw [← hcard]
    exact denseMeasureReal_allSelected_le_pow _ hgood.2.2.2 _ (by positivity)
      (fun p ↦ denseProbReal_extended_upper hk (hgood.2.2.1 p))
  · simp only [measureReal_empty]
    positivity

noncomputable def denseCollisionBad (k : ℕ) : Set DenseSample :=
  ⋃ q ∈ zBlock k, ⋃ r ∈ zBlock k,
    ⋃ ys : DenseCollisionTuple (Z k), denseCollisionTupleEvent (Z k) q r ys

lemma denseCollisionBad_measurable (k : ℕ) :
    MeasurableSet (denseCollisionBad k) := by
  classical
  unfold denseCollisionBad
  exact Finset.measurableSet_biUnion (zBlock k) fun q _hq ↦
    Finset.measurableSet_biUnion (zBlock k) fun r _hr ↦
      MeasurableSet.iUnion fun ys ↦ denseCollisionTupleEvent_measurable _ _ _ _

lemma denseCollisionBad_measureReal_le_sum (k : ℕ) :
    denseMeasure.real (denseCollisionBad k) ≤
      ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        ∑ ys : DenseCollisionTuple (Z k),
          denseMeasure.real (denseCollisionTupleEvent (Z k) q r ys) := by
  classical
  unfold denseCollisionBad
  calc
    denseMeasure.real
        (⋃ q ∈ zBlock k, ⋃ r ∈ zBlock k,
          ⋃ ys : DenseCollisionTuple (Z k), denseCollisionTupleEvent (Z k) q r ys) ≤
      ∑ q ∈ zBlock k,
        denseMeasure.real
          (⋃ r ∈ zBlock k, ⋃ ys : DenseCollisionTuple (Z k),
            denseCollisionTupleEvent (Z k) q r ys) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        denseMeasure.real
          (⋃ ys : DenseCollisionTuple (Z k),
            denseCollisionTupleEvent (Z k) q r ys) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        ∑ ys : DenseCollisionTuple (Z k),
          denseMeasure.real (denseCollisionTupleEvent (Z k) q r ys) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro r _hr
      exact measureReal_iUnion_fintype_le _

lemma denseCollisionBad_measureReal_le_raw (k : ℕ) (hk : 1 ≤ k) :
    denseMeasure.real (denseCollisionBad k) ≤
      ((256 : ℝ) * Z k) ^ 2 *
        (Fintype.card (DenseCollisionTuple (Z k)) : ℝ) *
        (8 * (1 / 8 : ℝ) ^ k) ^ 60 := by
  let P : ℝ := 8 * (1 / 8 : ℝ) ^ k
  have hcard : ((zBlock k).card : ℝ) ≤ 256 * Z k := by
    have h := zBlock_card_le_Z_succ k
    rw [Z_succ] at h
    exact_mod_cast h
  calc
    denseMeasure.real (denseCollisionBad k) ≤
        ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
          ∑ ys : DenseCollisionTuple (Z k),
            denseMeasure.real (denseCollisionTupleEvent (Z k) q r ys) :=
      denseCollisionBad_measureReal_le_sum k
    _ ≤ ∑ _q ∈ zBlock k, ∑ _r ∈ zBlock k,
          ∑ _ys : DenseCollisionTuple (Z k), P ^ 60 := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro r _hr
      apply Finset.sum_le_sum
      intro ys _hys
      exact denseCollisionTupleEvent_measureReal_le k q r ys hk
    _ = ((zBlock k).card : ℝ) ^ 2 *
          (Fintype.card (DenseCollisionTuple (Z k)) : ℝ) * P ^ 60 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((256 : ℝ) * Z k) ^ 2 *
          (Fintype.card (DenseCollisionTuple (Z k)) : ℝ) * P ^ 60 := by
      have hP : 0 ≤ P ^ 60 := by positivity
      have htuple : 0 ≤ (Fintype.card (DenseCollisionTuple (Z k)) : ℝ) := by positivity
      gcongr
    _ = _ := rfl

lemma denseCollision_scale_identity (k : ℕ) :
    (Z k : ℝ) ^ 22 * (8 * (1 / 8 : ℝ) ^ k) ^ 60 =
      (8 : ℝ) ^ 60 * (1 / 16 : ℝ) ^ k := by
  rw [Z, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  rw [pow_right_comm (256 : ℝ) k 22,
    pow_right_comm (1 / 8 : ℝ) k 60]
  calc
    ((256 : ℝ) ^ 22) ^ k * (8 ^ 60 * ((1 / 8 : ℝ) ^ 60) ^ k) =
        8 ^ 60 * (((256 : ℝ) ^ 22) ^ k * ((1 / 8 : ℝ) ^ 60) ^ k) := by
      ring
    _ = 8 ^ 60 *
        (((256 : ℝ) ^ 22 * (1 / 8 : ℝ) ^ 60) ^ k) := by
      rw [mul_pow]
    _ = (8 : ℝ) ^ 60 * (1 / 16 : ℝ) ^ k := by
      norm_num

noncomputable def denseCollisionConstant : ℝ :=
  (256 : ℝ) ^ 2 * 257 ^ 20 * 8 ^ 60

lemma denseCollisionConstant_nonneg : 0 ≤ denseCollisionConstant := by
  unfold denseCollisionConstant
  positivity

lemma denseCollisionBad_measureReal_le_geometric (k : ℕ) (hk : 1 ≤ k) :
    denseMeasure.real (denseCollisionBad k) ≤
      denseCollisionConstant * (1 / 16 : ℝ) ^ k := by
  let N : ℕ := Z k
  have hNpos : 0 < N := Z_pos k
  have hbaseNat : 256 * N + 1 ≤ 257 * N := by omega
  have htupleNat : Fintype.card (DenseCollisionTuple N) ≤ (257 * N) ^ 20 := by
    simp only [DenseCollisionTuple, Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_left hbaseNat 20
  have htuple : (Fintype.card (DenseCollisionTuple N) : ℝ) ≤
      ((257 * N : ℕ) : ℝ) ^ 20 := by exact_mod_cast htupleNat
  have hraw := denseCollisionBad_measureReal_le_raw k hk
  change denseMeasure.real (denseCollisionBad k) ≤
    ((256 : ℝ) * N) ^ 2 * (Fintype.card (DenseCollisionTuple N) : ℝ) *
      (8 * (1 / 8 : ℝ) ^ k) ^ 60 at hraw
  calc
    denseMeasure.real (denseCollisionBad k) ≤
        ((256 : ℝ) * N) ^ 2 *
          (Fintype.card (DenseCollisionTuple N) : ℝ) *
          (8 * (1 / 8 : ℝ) ^ k) ^ 60 := hraw
    _ ≤ ((256 : ℝ) * N) ^ 2 * ((257 * N : ℕ) : ℝ) ^ 20 *
          (8 * (1 / 8 : ℝ) ^ k) ^ 60 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htuple (by positivity)) (by positivity)
    _ = ((256 : ℝ) ^ 2 * 257 ^ 20) *
          ((N : ℝ) ^ 22 * (8 * (1 / 8 : ℝ) ^ k) ^ 60) := by
      push_cast
      ring
    _ = denseCollisionConstant * (1 / 16 : ℝ) ^ k := by
      change ((256 : ℝ) ^ 2 * 257 ^ 20) *
          ((Z k : ℝ) ^ 22 * (8 * (1 / 8 : ℝ) ^ k) ^ 60) = _
      rw [denseCollision_scale_identity]
      unfold denseCollisionConstant
      ring

lemma summable_denseCollisionBad_measureReal :
    Summable (fun k : ℕ ↦ denseMeasure.real (denseCollisionBad k)) := by
  have hgeom : Summable (fun k : ℕ ↦
      denseCollisionConstant * (1 / 16 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact denseCollisionBad_measureReal_le_geometric k hk

lemma tsum_denseCollisionBad_ne_top :
    (∑' k : ℕ, denseMeasure (denseCollisionBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ denseMeasure (denseCollisionBad k)) =
      (fun k ↦ ((denseMeasure (denseCollisionBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_denseCollisionBad_measureReal

noncomputable def denseCommonTripleCenters
    (N q r : ℕ) (ω : DenseSample) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 (min q r)).filter (fun y ↦
      ∀ j : Fin 3, denseExtendedAtScale N (tripleEndpoint q r y j) ∧
        denseBit (tripleEndpoint q r y j) ω = true)

lemma mem_denseCommonTripleCenters {N q r y : ℕ} {ω : DenseSample} :
    y ∈ denseCommonTripleCenters N q r ω ↔
      (y ≤ q ∧ y ≤ r) ∧
        ∀ j : Fin 3, denseExtendedAtScale N (tripleEndpoint q r y j) ∧
          denseBit (tripleEndpoint q r y j) ω = true := by
  classical
  simp [denseCommonTripleCenters, le_min_iff]

lemma denseCollisionBad_of_many {k q r : ℕ} {ω : DenseSample}
    (hq : q ∈ zBlock k) (hr : r ∈ zBlock k) (hqr : q ≠ r)
    (hmany : 182 ≤ (denseCommonTripleCenters (Z k) q r ω).card) :
    ω ∈ denseCollisionBad k := by
  classical
  let S := denseCommonTripleCenters (Z k) q r ω
  have hvalid : ∀ y ∈ S, y ≤ q ∧ y ≤ r := by
    intro y hy
    exact (mem_denseCommonTripleCenters.1 hy).1
  obtain ⟨T, hTS, hTcard, hTthree, hTdisj⟩ :=
    exists_twenty_disjoint_triples hqr S hvalid hmany
  let eT : Fin 20 ≃ T := (T.equivFin.trans (finCongr hTcard)).symm
  let ys : DenseCollisionTuple (Z k) := fun i ↦
    ⟨(eT i : ℕ), by
      have hyq := (mem_denseCommonTripleCenters.1 (hTS (eT i).property)).1.1
      have hq' := (mem_zBlock.1 hq).2
      rw [Z_succ] at hq'
      have hZpos := Z_pos k
      omega⟩
  have hysT (i : Fin 20) : (ys i : ℕ) ∈ T := (eT i).property
  have hcenter (i : Fin 20) : (ys i : ℕ) ∈ S := hTS (hysT i)
  have hendpoint_inj : Function.Injective (denseCollisionTupleEndpoint q r ys) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      have hwithin : Function.Injective (tripleEndpoint q r (ys i)) := by
        have hcard := hTthree (ys i) (hysT i)
        have hinjOn : Set.InjOn (tripleEndpoint q r (ys i))
            (Finset.univ : Finset (Fin 3)) :=
          Finset.card_image_iff.mp (by simpa [tripleSet] using hcard)
        exact fun a b hab ↦ hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
      have : a = b := hwithin hab
      subst b
      rfl
    · have hdisj := hTdisj (ys i) (hysT i) (ys j) (hysT j) (by
          intro hy
          have := eT.injective (Subtype.ext hy)
          exact hij this)
      exfalso
      exact Finset.disjoint_left.1 hdisj
        (mem_tripleSet.2 ⟨a, rfl⟩)
        (mem_tripleSet.2 ⟨b, hab.symm⟩)
  have hgood : denseCollisionTupleGood (Z k) q r ys := by
    refine ⟨hqr, ?_, ?_, hendpoint_inj⟩
    · intro i
      exact (mem_denseCommonTripleCenters.1 (hcenter i)).1
    · rintro ⟨i, j⟩
      exact (mem_denseCommonTripleCenters.1 (hcenter i)).2 j |>.1
  unfold denseCollisionBad
  exact Set.mem_iUnion_of_mem q (Set.mem_iUnion_of_mem hq
    (Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hr
      (Set.mem_iUnion_of_mem ys (by
        change ω ∈ denseCollisionTupleEvent (Z k) q r ys
        rw [denseCollisionTupleEvent, if_pos hgood]
        rintro ⟨i, j⟩
        exact (mem_denseCommonTripleCenters.1 (hcenter i)).2 j |>.2)))))

lemma ae_eventually_dense_collision_bound :
    ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ∀ q ∈ zBlock k, ∀ r ∈ zBlock k, q ≠ r →
        (denseCommonTripleCenters (Z k) q r ω).card < 182 := by
  have hae : ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ω ∉ denseCollisionBad k :=
    MeasureTheory.ae_eventually_notMem tsum_denseCollisionBad_ne_top
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  intro q hq r hr hqr
  by_contra hmany
  exact hk (denseCollisionBad_of_many hq hr hqr (by omega))

/-! A weighted collision estimate without a lower cutoff on the two complementary
endpoints.  This is the form used by the deletion construction. -/

noncomputable def denseSqMean (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, (denseProbReal n) ^ 2

lemma denseProbSqSum_zBlock_le (k : ℕ) :
    denseSqMean (zBlock k) ≤ (256 : ℝ) * 4 ^ k := by
  unfold denseSqMean
  calc
    ∑ n ∈ zBlock k, denseProbReal n ^ 2 =
        ∑ _n ∈ zBlock k, (1 / 64 : ℝ) ^ k := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [denseProbReal_of_mem_zBlock hn, pow_two, ← mul_pow]
      norm_num

    _ = (zBlock k).card * (1 / 64 : ℝ) ^ k := by simp
    _ ≤ (Z (k + 1) : ℝ) * (1 / 64 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast zBlock_card_le_Z_succ k
      · positivity
    _ = (256 : ℝ) * 4 ^ k := by
      rw [Z, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        (256 : ℝ) ^ k * 256 * (1 / 64 : ℝ) ^ k =
            256 * ((256 : ℝ) ^ k * (1 / 64 : ℝ) ^ k) := by ring
        _ = 256 * (((256 : ℝ) * (1 / 64 : ℝ)) ^ k) := by rw [mul_pow]
        _ = (256 : ℝ) * 4 ^ k := by norm_num

lemma denseSqMean_initial_le (k : ℕ) :
    denseSqMean (denseInitialIndices k) ≤ (300 : ℝ) * 4 ^ (k + 1) := by
  induction k with
  | zero =>
      unfold denseSqMean denseInitialIndices
      calc
        ∑ n ∈ Finset.range (Z (0 + 1)), denseProbReal n ^ 2 ≤
            ∑ _n ∈ Finset.range (Z (0 + 1)), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n _hn
          have hp0 := denseProbReal_nonneg n
          have hp1 := denseProbReal_le_one n
          nlinarith
        _ = (Z 1 : ℕ) := by simp
        _ ≤ (300 : ℝ) * 4 ^ (0 + 1) := by norm_num [Z]
  | succ k h =>
      have hZ : Z (k + 1) ≤ Z (k + 2) := by
        unfold Z
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsplit : denseSqMean (denseInitialIndices (k + 1)) =
          denseSqMean (denseInitialIndices k) + denseSqMean (zBlock (k + 1)) := by
        unfold denseSqMean denseInitialIndices zBlock
        rw [Finset.sum_range_add_sum_Ico _ hZ]
      rw [hsplit]
      calc
        denseSqMean (denseInitialIndices k) + denseSqMean (zBlock (k + 1)) ≤
            (300 : ℝ) * 4 ^ (k + 1) + 256 * 4 ^ (k + 1) :=
          add_le_add h (denseProbSqSum_zBlock_le (k + 1))
        _ ≤ (300 : ℝ) * 4 ^ ((k + 1) + 1) := by
          calc
            (300 : ℝ) * 4 ^ (k + 1) + 256 * 4 ^ (k + 1) =
                556 * 4 ^ (k + 1) := by ring
            _ ≤ 1200 * 4 ^ (k + 1) := by gcongr <;> norm_num
            _ = 300 * 4 ^ ((k + 1) + 1) := by rw [pow_succ]; ring

def denseCenterDomain (q r : ℕ) : Finset ℕ := Finset.Icc 0 (min q r)

lemma mem_denseCenterDomain {q r y : ℕ} :
    y ∈ denseCenterDomain q r ↔ y ≤ q ∧ y ≤ r := by
  simp [denseCenterDomain]

lemma denseCenterDomain_coordinate_sq_le {k q r : ℕ}
    (hq : q ∈ zBlock k) (f : ℕ → ℕ)
    (hfmem : ∀ y ∈ denseCenterDomain q r, f y < Z (k + 1))
    (hfinj : Set.InjOn f (denseCenterDomain q r : Set ℕ)) :
    ∑ y ∈ denseCenterDomain q r, denseProbReal (f y) ^ 2 ≤
      (300 : ℝ) * 4 ^ (k + 1) := by
  classical
  have hsub : (denseCenterDomain q r).image f ⊆ denseInitialIndices k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hfmem y hy)
  calc
    ∑ y ∈ denseCenterDomain q r, denseProbReal (f y) ^ 2 =
        ∑ x ∈ (denseCenterDomain q r).image f, denseProbReal x ^ 2 := by
      symm
      exact Finset.sum_image hfinj
    _ ≤ ∑ x ∈ denseInitialIndices k, denseProbReal x ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _hi _hnot ↦ sq_nonneg (denseProbReal i))
    _ = denseSqMean (denseInitialIndices k) := rfl
    _ ≤ (300 : ℝ) * 4 ^ (k + 1) := denseSqMean_initial_le k

lemma denseProbReal_upper_of_Z_third_le {k x : ℕ} (hk : 1 ≤ k)
    (hx : Z k / 3 ≤ x) :
    denseProbReal x ≤ 8 * (1 / 8 : ℝ) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hlo : Z j ≤ x := by
    rw [Z_succ] at hx
    have hZpos := Z_pos j
    omega
  calc
    denseProbReal x ≤ (1 / 8 : ℝ) ^ j := denseProbReal_upper_of_Z_le hlo
    _ = 8 * (1 / 8 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring

noncomputable def denseTripleWeight (q r y : ℕ) : ℝ :=
  denseProbReal y * denseProbReal (q - y) * denseProbReal (r - y)

lemma denseTripleWeight_nonneg (q r y : ℕ) : 0 ≤ denseTripleWeight q r y := by
  unfold denseTripleWeight
  exact mul_nonneg
    (mul_nonneg (denseProbReal_nonneg y) (denseProbReal_nonneg (q - y)))
    (denseProbReal_nonneg (r - y))

lemma denseTripleWeightSum_le {k q r : ℕ} (hk : 1 ≤ k)
    (hq : q ∈ zBlock k) (hr : r ∈ zBlock k) :
    ∑ y ∈ denseCenterDomain q r, denseTripleWeight q r y ≤
      (28800 : ℝ) * (1 / 2 : ℝ) ^ k := by
  let M : ℝ := 300 * 4 ^ (k + 1)
  let P : ℝ := 8 * (1 / 8 : ℝ) ^ k
  have hqtop : q < Z (k + 1) := (mem_zBlock.1 hq).2
  have hrtop : r < Z (k + 1) := (mem_zBlock.1 hr).2
  have hsqY : ∑ y ∈ denseCenterDomain q r, denseProbReal y ^ 2 ≤ M := by
    exact denseCenterDomain_coordinate_sq_le hq id
      (fun y _hy ↦ by simpa using (mem_denseCenterDomain.1 _hy).1.trans_lt hqtop)
      (fun _x _hx _y _hy hxy ↦ hxy)
  have hsqQ : ∑ y ∈ denseCenterDomain q r, denseProbReal (q - y) ^ 2 ≤ M := by
    apply denseCenterDomain_coordinate_sq_le hq (fun y ↦ q - y)
    · intro y hy
      exact (Nat.sub_le q y).trans_lt hqtop
    · intro y hy z hz heq
      change q - y = q - z at heq
      have hyq := (mem_denseCenterDomain.1 hy).1
      have hzq := (mem_denseCenterDomain.1 hz).1
      omega
  have hsqR : ∑ y ∈ denseCenterDomain q r, denseProbReal (r - y) ^ 2 ≤ M := by
    apply denseCenterDomain_coordinate_sq_le hq (fun y ↦ r - y)
    · intro y hy
      exact (Nat.sub_le r y).trans_lt hrtop
    · intro y hy z hz heq
      change r - y = r - z at heq
      have hyr := (mem_denseCenterDomain.1 hy).2
      have hzr := (mem_denseCenterDomain.1 hz).2
      omega
  have hpairYQ : ∑ y ∈ denseCenterDomain q r,
      denseProbReal y * denseProbReal (q - y) ≤ M := by
    calc
      ∑ y ∈ denseCenterDomain q r, denseProbReal y * denseProbReal (q - y) ≤
          ∑ y ∈ denseCenterDomain q r,
            (denseProbReal y ^ 2 + denseProbReal (q - y) ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro y _hy
        nlinarith [sq_nonneg (denseProbReal y - denseProbReal (q - y))]
      _ = ((∑ y ∈ denseCenterDomain q r, denseProbReal y ^ 2) +
          (∑ y ∈ denseCenterDomain q r, denseProbReal (q - y) ^ 2)) / 2 := by
        simp_rw [div_eq_mul_inv, add_mul]
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ M := by linarith
  have hpairYR : ∑ y ∈ denseCenterDomain q r,
      denseProbReal y * denseProbReal (r - y) ≤ M := by
    calc
      ∑ y ∈ denseCenterDomain q r, denseProbReal y * denseProbReal (r - y) ≤
          ∑ y ∈ denseCenterDomain q r,
            (denseProbReal y ^ 2 + denseProbReal (r - y) ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro y _hy
        nlinarith [sq_nonneg (denseProbReal y - denseProbReal (r - y))]
      _ = ((∑ y ∈ denseCenterDomain q r, denseProbReal y ^ 2) +
          (∑ y ∈ denseCenterDomain q r, denseProbReal (r - y) ^ 2)) / 2 := by
        simp_rw [div_eq_mul_inv, add_mul]
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ M := by linarith
  have hpairQR : ∑ y ∈ denseCenterDomain q r,
      denseProbReal (q - y) * denseProbReal (r - y) ≤ M := by
    calc
      ∑ y ∈ denseCenterDomain q r,
          denseProbReal (q - y) * denseProbReal (r - y) ≤
          ∑ y ∈ denseCenterDomain q r,
            (denseProbReal (q - y) ^ 2 + denseProbReal (r - y) ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro y _hy
        nlinarith [sq_nonneg (denseProbReal (q - y) - denseProbReal (r - y))]
      _ = ((∑ y ∈ denseCenterDomain q r, denseProbReal (q - y) ^ 2) +
          (∑ y ∈ denseCenterDomain q r, denseProbReal (r - y) ^ 2)) / 2 := by
        simp_rw [div_eq_mul_inv, add_mul]
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ M := by linarith
  have hpoint : ∀ y ∈ denseCenterDomain q r,
      denseTripleWeight q r y ≤ P *
        (denseProbReal y * denseProbReal (q - y) +
          denseProbReal y * denseProbReal (r - y) +
          denseProbReal (q - y) * denseProbReal (r - y)) := by
    intro y hy
    have hyq := (mem_denseCenterDomain.1 hy).1
    have hqlo := (mem_zBlock.1 hq).1
    have hlarge : Z k / 3 ≤ y ∨ Z k / 3 ≤ q - y := by omega
    have ha0 := denseProbReal_nonneg y
    have hb0 := denseProbReal_nonneg (q - y)
    have hc0 := denseProbReal_nonneg (r - y)
    have hP0 : 0 ≤ P := by dsimp [P]; positivity
    rcases hlarge with hlarge | hlarge
    · have haP := denseProbReal_upper_of_Z_third_le hk hlarge
      have haP' : denseProbReal y ≤ P := by simpa [P] using haP
      unfold denseTripleWeight
      calc
        denseProbReal y * denseProbReal (q - y) * denseProbReal (r - y) =
            denseProbReal y *
              (denseProbReal (q - y) * denseProbReal (r - y)) := by ring
        _ ≤
            P * (denseProbReal (q - y) * denseProbReal (r - y)) := by
          exact mul_le_mul_of_nonneg_right haP' (mul_nonneg hb0 hc0)
        _ ≤ P *
            (denseProbReal y * denseProbReal (q - y) +
              denseProbReal y * denseProbReal (r - y) +
              denseProbReal (q - y) * denseProbReal (r - y)) := by
          apply mul_le_mul_of_nonneg_left _ hP0
          nlinarith [mul_nonneg ha0 hb0, mul_nonneg ha0 hc0]
    · have hbP := denseProbReal_upper_of_Z_third_le hk hlarge
      have hbP' : denseProbReal (q - y) ≤ P := by simpa [P] using hbP
      unfold denseTripleWeight
      calc
        denseProbReal y * denseProbReal (q - y) * denseProbReal (r - y) =
            denseProbReal (q - y) *
              (denseProbReal y * denseProbReal (r - y)) := by ring
        _ ≤ P * (denseProbReal y * denseProbReal (r - y)) := by
          exact mul_le_mul_of_nonneg_right hbP' (mul_nonneg ha0 hc0)
        _ ≤ P *
            (denseProbReal y * denseProbReal (q - y) +
              denseProbReal y * denseProbReal (r - y) +
              denseProbReal (q - y) * denseProbReal (r - y)) := by
          apply mul_le_mul_of_nonneg_left _ hP0
          nlinarith [mul_nonneg ha0 hb0, mul_nonneg hb0 hc0]
  calc
    ∑ y ∈ denseCenterDomain q r, denseTripleWeight q r y ≤
        ∑ y ∈ denseCenterDomain q r, P *
          (denseProbReal y * denseProbReal (q - y) +
            denseProbReal y * denseProbReal (r - y) +
            denseProbReal (q - y) * denseProbReal (r - y)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact hpoint y hy
    _ = P * ((∑ y ∈ denseCenterDomain q r,
          denseProbReal y * denseProbReal (q - y)) +
        (∑ y ∈ denseCenterDomain q r,
          denseProbReal y * denseProbReal (r - y)) +
        (∑ y ∈ denseCenterDomain q r,
          denseProbReal (q - y) * denseProbReal (r - y))) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ P * (3 * M) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · dsimp [P]
        positivity
    _ = (28800 : ℝ) * (1 / 2 : ℝ) ^ k := by
      dsimp [P, M]
      rw [pow_succ]
      calc
        8 * (1 / 8 : ℝ) ^ k * (3 * (300 * (4 ^ k * 4))) =
            28800 * ((1 / 8 : ℝ) ^ k * 4 ^ k) := by ring
        _ = 28800 * (1 / 2 : ℝ) ^ k := by
          rw [← mul_pow]
          norm_num

lemma sum_fun_prod_eq_pow {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (w : α → ℝ) :
    (∑ y : α, w y) ^ Fintype.card ι =
      ∑ f : ι → α, ∏ i : ι, w (f i) := by
  classical
  have h := Finset.prod_sum (Finset.univ : Finset ι)
    (fun _ ↦ (Finset.univ : Finset α)) (fun _ y ↦ w y)
  let P := (i : ι) → i ∈ (Finset.univ : Finset ι) → α
  let e : P ≃ (ι → α) :=
    { toFun := fun p i ↦ p i (Finset.mem_univ i)
      invFun := fun f i _hi ↦ f i
      left_inv := fun p ↦ by funext i hi; rfl
      right_inv := fun f ↦ by funext i; rfl }
  have h' : (∑ y : α, w y) ^ Fintype.card ι =
      ∑ p : P, ∏ i : ι, w (p i (Finset.mem_univ i)) := by
    simpa [P] using h
  rw [h']
  exact Fintype.sum_equiv e _ _ (by intro p; rfl)

abbrev DenseCenter (q r : ℕ) := {y : ℕ // y ∈ denseCenterDomain q r}

abbrev DenseGlobalCollisionTuple (q r : ℕ) := Fin 20 → DenseCenter q r

def denseGlobalTupleEndpoint (q r : ℕ) (ys : DenseGlobalCollisionTuple q r)
    (p : Fin 20 × Fin 3) : ℕ :=
  tripleEndpoint q r (ys p.1) p.2

def denseGlobalTupleGood (q r : ℕ) (ys : DenseGlobalCollisionTuple q r) : Prop :=
  q ≠ r ∧ Function.Injective (denseGlobalTupleEndpoint q r ys)

noncomputable def denseGlobalTupleEvent (q r : ℕ)
    (ys : DenseGlobalCollisionTuple q r) : Set DenseSample := by
  classical
  exact if denseGlobalTupleGood q r ys then
    denseAllSelected (denseGlobalTupleEndpoint q r ys)
  else ∅

lemma denseGlobalTupleEvent_measurable (q r : ℕ)
    (ys : DenseGlobalCollisionTuple q r) :
    MeasurableSet (denseGlobalTupleEvent q r ys) := by
  classical
  unfold denseGlobalTupleEvent
  split_ifs
  · exact denseAllSelected_measurable _
  · exact MeasurableSet.empty

lemma denseTripleWeight_eq_endpoint_prod (q r y : ℕ) :
    denseTripleWeight q r y =
      ∏ j : Fin 3, denseProbReal (tripleEndpoint q r y j) := by
  simp [denseTripleWeight, tripleEndpoint, Fin.prod_univ_succ]
  ring

lemma denseGlobalTupleEvent_measureReal_le (q r : ℕ)
    (ys : DenseGlobalCollisionTuple q r) :
    denseMeasure.real (denseGlobalTupleEvent q r ys) ≤
      ∏ i : Fin 20, denseTripleWeight q r (ys i) := by
  classical
  unfold denseGlobalTupleEvent
  split_ifs with hgood
  · rw [denseMeasureReal_allSelected_eq_prod _ hgood.2]
    rw [Fintype.prod_prod_type]
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro i _hi
    exact (denseTripleWeight_eq_endpoint_prod q r (ys i)).symm
  · simp only [measureReal_empty]
    exact Finset.prod_nonneg fun i _hi ↦ denseTripleWeight_nonneg q r (ys i)

lemma denseGlobalTupleEvent_measureReal_sum_le (q r : ℕ) :
    ∑ ys : DenseGlobalCollisionTuple q r,
        denseMeasure.real (denseGlobalTupleEvent q r ys) ≤
      (∑ y ∈ denseCenterDomain q r, denseTripleWeight q r y) ^ 20 := by
  classical
  calc
    ∑ ys : DenseGlobalCollisionTuple q r,
        denseMeasure.real (denseGlobalTupleEvent q r ys) ≤
        ∑ ys : DenseGlobalCollisionTuple q r,
          ∏ i : Fin 20, denseTripleWeight q r (ys i) := by
      apply Finset.sum_le_sum
      intro ys _hys
      exact denseGlobalTupleEvent_measureReal_le q r ys
    _ = (∑ y : DenseCenter q r, denseTripleWeight q r y) ^ 20 := by
      symm
      simpa using sum_fun_prod_eq_pow (ι := Fin 20) (α := DenseCenter q r)
        (fun y ↦ denseTripleWeight q r y)
    _ = (∑ y ∈ denseCenterDomain q r, denseTripleWeight q r y) ^ 20 := by
      congr 1
      rw [Finset.sum_subtype (denseCenterDomain q r) (fun _ ↦ Iff.rfl)]

noncomputable def denseGlobalCollisionBad (k : ℕ) : Set DenseSample :=
  ⋃ q ∈ zBlock k, ⋃ r ∈ zBlock k,
    ⋃ ys : DenseGlobalCollisionTuple q r, denseGlobalTupleEvent q r ys

lemma denseGlobalCollisionBad_measurable (k : ℕ) :
    MeasurableSet (denseGlobalCollisionBad k) := by
  classical
  unfold denseGlobalCollisionBad
  exact Finset.measurableSet_biUnion (zBlock k) fun q _hq ↦
    Finset.measurableSet_biUnion (zBlock k) fun r _hr ↦
      MeasurableSet.iUnion fun ys ↦ denseGlobalTupleEvent_measurable q r ys

lemma denseGlobalCollisionBad_measureReal_le_sum (k : ℕ) :
    denseMeasure.real (denseGlobalCollisionBad k) ≤
      ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        ∑ ys : DenseGlobalCollisionTuple q r,
          denseMeasure.real (denseGlobalTupleEvent q r ys) := by
  classical
  unfold denseGlobalCollisionBad
  calc
    denseMeasure.real
        (⋃ q ∈ zBlock k, ⋃ r ∈ zBlock k,
          ⋃ ys : DenseGlobalCollisionTuple q r, denseGlobalTupleEvent q r ys) ≤
      ∑ q ∈ zBlock k,
        denseMeasure.real
          (⋃ r ∈ zBlock k,
            ⋃ ys : DenseGlobalCollisionTuple q r, denseGlobalTupleEvent q r ys) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        denseMeasure.real
          (⋃ ys : DenseGlobalCollisionTuple q r, denseGlobalTupleEvent q r ys) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
        ∑ ys : DenseGlobalCollisionTuple q r,
          denseMeasure.real (denseGlobalTupleEvent q r ys) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro r _hr
      exact measureReal_iUnion_fintype_le _

lemma denseGlobalCollision_scale_identity (k : ℕ) :
    (Z k : ℝ) ^ 2 * (((1 / 2 : ℝ) ^ k) ^ 20) =
      (1 / 16 : ℝ) ^ k := by
  rw [Z, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_right_comm (256 : ℝ) k 2,
    pow_right_comm (1 / 2 : ℝ) k 20]
  rw [← mul_pow]
  norm_num

noncomputable def denseGlobalCollisionConstant : ℝ :=
  (256 : ℝ) ^ 2 * 28800 ^ 20

lemma denseGlobalCollisionConstant_nonneg : 0 ≤ denseGlobalCollisionConstant := by
  unfold denseGlobalCollisionConstant
  positivity

lemma denseGlobalCollisionBad_measureReal_le_geometric (k : ℕ) (hk : 1 ≤ k) :
    denseMeasure.real (denseGlobalCollisionBad k) ≤
      denseGlobalCollisionConstant * (1 / 16 : ℝ) ^ k := by
  let W : ℝ := 28800 * (1 / 2 : ℝ) ^ k
  have hcard : ((zBlock k).card : ℝ) ≤ 256 * Z k := by
    have h := zBlock_card_le_Z_succ k
    rw [Z_succ] at h
    exact_mod_cast h
  calc
    denseMeasure.real (denseGlobalCollisionBad k) ≤
        ∑ q ∈ zBlock k, ∑ r ∈ zBlock k,
          ∑ ys : DenseGlobalCollisionTuple q r,
            denseMeasure.real (denseGlobalTupleEvent q r ys) :=
      denseGlobalCollisionBad_measureReal_le_sum k
    _ ≤ ∑ _q ∈ zBlock k, ∑ _r ∈ zBlock k, W ^ 20 := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      calc
        ∑ ys : DenseGlobalCollisionTuple q r,
            denseMeasure.real (denseGlobalTupleEvent q r ys) ≤
            (∑ y ∈ denseCenterDomain q r, denseTripleWeight q r y) ^ 20 :=
          denseGlobalTupleEvent_measureReal_sum_le q r
        _ ≤ W ^ 20 := by
          apply pow_le_pow_left₀
          · exact Finset.sum_nonneg fun y _hy ↦ denseTripleWeight_nonneg q r y
          · exact denseTripleWeightSum_le hk hq hr
    _ = ((zBlock k).card : ℝ) ^ 2 * W ^ 20 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((256 : ℝ) * Z k) ^ 2 * W ^ 20 := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ (by positivity) hcard 2
      · positivity
    _ = denseGlobalCollisionConstant * (1 / 16 : ℝ) ^ k := by
      dsimp [W]
      calc
        ((256 : ℝ) * Z k) ^ 2 *
            (28800 * (1 / 2 : ℝ) ^ k) ^ 20 =
            ((256 : ℝ) ^ 2 * 28800 ^ 20) *
              ((Z k : ℝ) ^ 2 * (((1 / 2 : ℝ) ^ k) ^ 20)) := by ring
        _ = ((256 : ℝ) ^ 2 * 28800 ^ 20) * (1 / 16 : ℝ) ^ k := by
          rw [denseGlobalCollision_scale_identity]
        _ = denseGlobalCollisionConstant * (1 / 16 : ℝ) ^ k := rfl

lemma summable_denseGlobalCollisionBad_measureReal :
    Summable (fun k : ℕ ↦ denseMeasure.real (denseGlobalCollisionBad k)) := by
  have hgeom : Summable (fun k : ℕ ↦
      denseGlobalCollisionConstant * (1 / 16 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact denseGlobalCollisionBad_measureReal_le_geometric k hk

lemma tsum_denseGlobalCollisionBad_ne_top :
    (∑' k : ℕ, denseMeasure (denseGlobalCollisionBad k)) ≠ ⊤ := by
  rw [show (fun k : ℕ ↦ denseMeasure (denseGlobalCollisionBad k)) =
      (fun k ↦ ((denseMeasure (denseGlobalCollisionBad k)).toNNReal : ENNReal)) by
    funext k
    exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm]
  apply ENNReal.tsum_coe_ne_top_iff_summable_coe.2
  simpa only [Measure.real, ENNReal.coe_toNNReal_eq_toReal] using
    summable_denseGlobalCollisionBad_measureReal

noncomputable def denseGlobalCommonCenters
    (q r : ℕ) (ω : DenseSample) : Finset ℕ := by
  classical
  exact (denseCenterDomain q r).filter (fun y ↦
    ∀ j : Fin 3, denseBit (tripleEndpoint q r y j) ω = true)

lemma mem_denseGlobalCommonCenters {q r y : ℕ} {ω : DenseSample} :
    y ∈ denseGlobalCommonCenters q r ω ↔
      (y ≤ q ∧ y ≤ r) ∧
        ∀ j : Fin 3, denseBit (tripleEndpoint q r y j) ω = true := by
  classical
  simp [denseGlobalCommonCenters, mem_denseCenterDomain]

lemma denseGlobalCollisionBad_of_many {k q r : ℕ} {ω : DenseSample}
    (hq : q ∈ zBlock k) (hr : r ∈ zBlock k) (hqr : q ≠ r)
    (hmany : 182 ≤ (denseGlobalCommonCenters q r ω).card) :
    ω ∈ denseGlobalCollisionBad k := by
  classical
  let S := denseGlobalCommonCenters q r ω
  have hvalid : ∀ y ∈ S, y ≤ q ∧ y ≤ r := by
    intro y hy
    exact (mem_denseGlobalCommonCenters.1 hy).1
  obtain ⟨T, hTS, hTcard, hTthree, hTdisj⟩ :=
    exists_twenty_disjoint_triples hqr S hvalid hmany
  let eT : Fin 20 ≃ T := (T.equivFin.trans (finCongr hTcard)).symm
  let ys : DenseGlobalCollisionTuple q r := fun i ↦
    ⟨(eT i : ℕ), mem_denseCenterDomain.2
      ((mem_denseGlobalCommonCenters.1 (hTS (eT i).property)).1)⟩
  have hysT (i : Fin 20) : (ys i : ℕ) ∈ T := (eT i).property
  have hcenter (i : Fin 20) : (ys i : ℕ) ∈ S := hTS (hysT i)
  have hendpoint_inj : Function.Injective (denseGlobalTupleEndpoint q r ys) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      have hwithin : Function.Injective (tripleEndpoint q r (ys i)) := by
        have hcard := hTthree (ys i) (hysT i)
        have hinjOn : Set.InjOn (tripleEndpoint q r (ys i))
            (Finset.univ : Finset (Fin 3)) :=
          Finset.card_image_iff.mp (by simpa [tripleSet] using hcard)
        exact fun a b hab ↦ hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
      have : a = b := hwithin hab
      subst b
      rfl
    · have hdisj := hTdisj (ys i) (hysT i) (ys j) (hysT j) (by
          intro hy
          have := eT.injective (Subtype.ext hy)
          exact hij this)
      exfalso
      exact Finset.disjoint_left.1 hdisj
        (mem_tripleSet.2 ⟨a, rfl⟩)
        (mem_tripleSet.2 ⟨b, hab.symm⟩)
  have hgood : denseGlobalTupleGood q r ys := ⟨hqr, hendpoint_inj⟩
  unfold denseGlobalCollisionBad
  exact Set.mem_iUnion_of_mem q (Set.mem_iUnion_of_mem hq
    (Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hr
      (Set.mem_iUnion_of_mem ys (by
        rw [denseGlobalTupleEvent, if_pos hgood]
        rintro ⟨i, j⟩
        exact (mem_denseGlobalCommonCenters.1 (hcenter i)).2 j)))))

lemma ae_eventually_dense_global_collision_bound :
    ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ∀ q ∈ zBlock k, ∀ r ∈ zBlock k, q ≠ r →
        (denseGlobalCommonCenters q r ω).card < 182 := by
  have hae : ∀ᵐ ω ∂denseMeasure, ∀ᶠ k : ℕ in atTop,
      ω ∉ denseGlobalCollisionBad k :=
    MeasureTheory.ae_eventually_notMem tsum_denseGlobalCollisionBad_ne_top
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  intro q hq r hr hqr
  by_contra hmany
  exact hk (denseGlobalCollisionBad_of_many hq hr hqr (by omega))

def denseReservoirSet (ω : DenseSample) : Set ℕ :=
  {n | denseBit n ω = true}

noncomputable def densePresentPairs (lo m : ℕ) (ω : DenseSample) :
    Finset (strictReprIndices lo m) :=
  Finset.univ.filter (fun i ↦ densePairPresent lo m i ω = true)

lemma mem_densePresentPairs {lo m : ℕ} {ω : DenseSample}
    {i : strictReprIndices lo m} :
    i ∈ densePresentPairs lo m ω ↔
      denseBit i ω = true ∧ denseBit (m - i) ω = true := by
  classical
  simp [densePresentPairs, densePairPresent, Bool.and_eq_true]

lemma densePairSum_eq_presentPairs_card (lo m : ℕ) (ω : DenseSample) :
    densePairSum lo m ω = (densePresentPairs lo m ω).card := by
  classical
  have aux : ∀ s : Finset (strictReprIndices lo m),
      (∑ i ∈ s, boolIndicator (densePairPresent lo m i) ω) =
        ((s.filter (fun i ↦ densePairPresent lo m i ω = true)).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        cases h : densePairPresent lo m i ω <;>
          simp [Finset.sum_insert hi, Finset.filter_insert, boolIndicator, h, hi, ih] <;>
          ring
  unfold densePairSum densePresentPairs
  simpa using aux Finset.univ

noncomputable def denseSelectedInitial (k : ℕ) (ω : DenseSample) : Finset ℕ :=
  (denseInitialIndices k).filter (fun n ↦ denseBit n ω = true)

lemma mem_denseSelectedInitial {k n : ℕ} {ω : DenseSample} :
    n ∈ denseSelectedInitial k ω ↔ n < Z (k + 1) ∧ denseBit n ω = true := by
  classical
  simp [denseSelectedInitial, denseInitialIndices]

lemma densePointSum_eq_selectedInitial_card (k : ℕ) (ω : DenseSample) :
    densePointSum (denseInitialIndices k) ω = (denseSelectedInitial k ω).card := by
  classical
  have aux : ∀ s : Finset ℕ,
      (∑ n ∈ s, boolIndicator (denseBit n) ω) =
        ((s.filter (fun n ↦ denseBit n ω = true)).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
        cases h : denseBit n ω <;>
          simp [Finset.sum_insert hn, Finset.filter_insert, boolIndicator, h, hn, ih] <;>
          ring
  unfold densePointSum denseSelectedInitial
  exact aux (denseInitialIndices k)

lemma exists_dense_master_reservoir : ∃ ω : DenseSample,
    (∀ᶠ k : ℕ in atTop, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card) ∧
    (∀ᶠ k : ℕ in atTop,
      (denseSelectedInitial k ω).card < (64 : ℝ) ^ (k + 1)) ∧
    (∀ᶠ k : ℕ in atTop, ∀ q ∈ zBlock k, ∀ r ∈ zBlock k,
      q ≠ r → (denseGlobalCommonCenters q r ω).card < 182) := by
  have hall := (ae_eventually_dense_pair_lower.and ae_eventually_dense_point_upper).and
    ae_eventually_dense_global_collision_bound
  obtain ⟨ω, ⟨⟨hpair, hpoint⟩, hcollision⟩⟩ := hall.exists

  refine ⟨ω, ?_, ?_, hcollision⟩
  · filter_upwards [hpair] with k hk m hm
    rw [← densePairSum_eq_presentPairs_card]
    exact hk m hm
  · filter_upwards [hpoint] with k hk
    rw [← densePointSum_eq_selectedInitial_card]
    exact hk

/-! Finite target selection for the staged construction. -/

def targetStage (k : ℕ) : ℕ := 1000 * (k + 1)

def targetInterval (k : ℕ) : Finset ℕ :=
  Finset.Ico (20 * Z (targetStage k)) (30 * Z (targetStage k))

lemma mem_targetInterval {k b : ℕ} :
    b ∈ targetInterval k ↔
      20 * Z (targetStage k) ≤ b ∧ b < 30 * Z (targetStage k) := by
  simp [targetInterval]

lemma targetInterval_card (k : ℕ) :
    (targetInterval k).card = 10 * Z (targetStage k) := by
  rw [targetInterval, Nat.card_Ico]
  omega

lemma targetStage_strictMono : StrictMono targetStage := by
  intro a b hab
  unfold targetStage
  omega

lemma targetStage_gt (k : ℕ) : k < targetStage k := by
  unfold targetStage
  omega

lemma source_succ_le_targetStage (k : ℕ) : k + 1 ≤ targetStage k := by
  unfold targetStage
  omega

noncomputable def sumFinset (S T : Finset ℕ) : Finset ℕ :=
  (S.product T).image (fun p ↦ p.1 + p.2)

lemma mem_sumFinset {S T : Finset ℕ} {n : ℕ} :
    n ∈ sumFinset S T ↔ ∃ s ∈ S, ∃ t ∈ T, s + t = n := by
  classical
  constructor
  · rw [sumFinset, Finset.mem_image]
    rintro ⟨⟨s, t⟩, hst, rfl⟩
    exact ⟨s, (Finset.mem_product.1 hst).1,
      t, (Finset.mem_product.1 hst).2, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact Finset.mem_image.2
      ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩

lemma sumFinset_card_le (S T : Finset ℕ) :
    (sumFinset S T).card ≤ S.card * T.card := by
  classical
  calc
    (sumFinset S T).card ≤ (S.product T).card := Finset.card_image_le
    _ = S.card * T.card := Finset.card_product S T

noncomputable def diffFinset (A S : Finset ℕ) : Finset ℤ :=
  (A.product S).image (fun p ↦ (p.1 : ℤ) - (p.2 : ℤ))

lemma mem_diffFinset {A S : Finset ℕ} {e : ℤ} :
    e ∈ diffFinset A S ↔
      ∃ a ∈ A, ∃ s ∈ S, (a : ℤ) - (s : ℤ) = e := by
  classical
  constructor
  · rw [diffFinset, Finset.mem_image]
    rintro ⟨⟨a, s⟩, has, rfl⟩
    exact ⟨a, (Finset.mem_product.1 has).1,
      s, (Finset.mem_product.1 has).2, rfl⟩
  · rintro ⟨a, ha, s, hs, rfl⟩
    exact Finset.mem_image.2
      ⟨(a, s), Finset.mem_product.2 ⟨ha, hs⟩, rfl⟩

lemma sub_mem_diffFinset {A S : Finset ℕ} {a s : ℕ}
    (ha : a ∈ A) (hs : s ∈ S) :
    (a : ℤ) - (s : ℤ) ∈ diffFinset A S :=
  mem_diffFinset.2 ⟨a, ha, s, hs, rfl⟩

lemma diffFinset_card_le (A S : Finset ℕ) :
    (diffFinset A S).card ≤ A.card * S.card := by
  classical
  calc
    (diffFinset A S).card ≤ (A.product S).card := Finset.card_image_le
    _ = A.card * S.card := Finset.card_product A S

noncomputable def symmetricDiffFinset (A S : Finset ℕ) : Finset ℤ :=
  diffFinset A S ∪ (diffFinset A S).image (-·)

lemma eq_of_pairwise_symmetricDiff_avoiding
    {P : Type*} {A S : Finset ℕ} (f : P → ℕ)
    (havoid : ∀ p q, p ≠ q →
      ((f p : ℤ) - (f q : ℤ)) ∉ symmetricDiffFinset A S)
    {p q : P} {a s : ℕ} (ha : a ∈ A) (hs : s ∈ S)
    (heq : (f p : ℤ) - (f q : ℤ) = (a : ℤ) - (s : ℤ)) :
    p = q := by
  by_contra hpq
  apply havoid p q hpq
  rw [heq]
  exact Finset.mem_union.2 (Or.inl (sub_mem_diffFinset ha hs))

lemma symmetricDiffFinset_neg_mem {A S : Finset ℕ} {e : ℤ}
    (he : e ∈ symmetricDiffFinset A S) :
    -e ∈ symmetricDiffFinset A S := by
  classical
  simp only [symmetricDiffFinset, Finset.mem_union, Finset.mem_image] at he ⊢
  rcases he with he | ⟨d, hd, hde⟩
  · right
    exact ⟨e, he, rfl⟩
  · left
    subst e
    simpa using hd

lemma symmetricDiffFinset_card_le (A S : Finset ℕ) :
    (symmetricDiffFinset A S).card ≤ 2 * (A.card * S.card) := by
  classical
  calc
    (symmetricDiffFinset A S).card ≤
        (diffFinset A S).card + ((diffFinset A S).image (-·)).card :=
      Finset.card_union_le _ _
    _ ≤ (A.card * S.card) + (A.card * S.card) := by
      gcongr
      · exact diffFinset_card_le A S
      · exact Finset.card_image_le.trans (diffFinset_card_le A S)
    _ = 2 * (A.card * S.card) := by omega

noncomputable def targetConflict (A S : Finset ℕ) (x y : ℕ) : Prop :=
  x = y ∨ (x : ℤ) - (y : ℤ) ∈ symmetricDiffFinset A S

noncomputable instance targetConflict_decidable (A S : Finset ℕ) :
    DecidableRel (targetConflict A S) := Classical.decRel _

lemma targetConflict_refl (A S : Finset ℕ) (x : ℕ) :
    targetConflict A S x x := Or.inl rfl

lemma targetConflict_symm (A S : Finset ℕ) {x y : ℕ}
    (h : targetConflict A S x y) : targetConflict A S y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    have hneg := symmetricDiffFinset_neg_mem h
    convert hneg using 1 <;> ring

noncomputable def conflictNeighbor (x : ℕ) (e : ℤ) : ℕ :=
  Int.toNat ((x : ℤ) - e)

lemma targetConflict_neighbors_card_le (A S Q : Finset ℕ) (x : ℕ) :
    (Q.filter (targetConflict A S x)).card ≤ 1 + 2 * (A.card * S.card) := by
  classical
  let E := symmetricDiffFinset A S
  have hsub : Q.filter (targetConflict A S x) ⊆
      insert x (E.image (conflictNeighbor x)) := by
    intro y hy
    have hyc := (Finset.mem_filter.1 hy).2
    rcases hyc with rfl | he
    · simp
    · have hnonneg : (0 : ℤ) ≤ (x : ℤ) - ((x : ℤ) - (y : ℤ)) := by
        simp
      have hyEq : conflictNeighbor x ((x : ℤ) - (y : ℤ)) = y := by
        unfold conflictNeighbor
        have heq : (x : ℤ) - ((x : ℤ) - (y : ℤ)) = (y : ℤ) := by ring
        rw [heq]
        simp
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_image.2
        ⟨(x : ℤ) - (y : ℤ), he, hyEq⟩))
  calc
    (Q.filter (targetConflict A S x)).card ≤
        (insert x (E.image (conflictNeighbor x))).card := Finset.card_le_card hsub
    _ ≤ 1 + (E.image (conflictNeighbor x)).card := by
      simpa [Nat.add_comm] using
        (Finset.card_insert_le x (E.image (conflictNeighbor x)))
    _ ≤ 1 + E.card := Nat.add_le_add_left Finset.card_image_le 1
    _ ≤ 1 + 2 * (A.card * S.card) :=
      Nat.add_le_add_left (symmetricDiffFinset_card_le A S) 1

lemma exists_target_embedding
    {P : Type*} [Fintype P] [DecidableEq P]
    (Q A S : Finset ℕ)
    (hsize : (1 + 2 * (A.card * S.card)) * Fintype.card P ≤ Q.card) :
    ∃ f : P → ℕ, Function.Injective f ∧
      (∀ p, f p ∈ Q) ∧
      ∀ p p', p ≠ p' →
        (f p : ℤ) - (f p' : ℤ) ∉ symmetricDiffFinset A S := by
  classical
  let D := 1 + 2 * (A.card * S.card)
  obtain ⟨T, hTQ, hTcard, hTpair⟩ :=
    exists_pairwise_avoiding_of_mul_le_card (targetConflict A S)
      (@targetConflict_symm A S) D (by dsimp [D]; omega)
      (Fintype.card P) Q
      (fun x _hx ↦ targetConflict_refl A S x)
      (fun x _hx ↦ targetConflict_neighbors_card_le A S Q x)
      hsize
  have hcardP : Fintype.card P = Fintype.card T := by simpa [hTcard]
  let e : P ≃ T := Fintype.equivOfCardEq hcardP
  refine ⟨fun p ↦ e p, fun p p' h ↦ e.injective (Subtype.ext h),
    fun p ↦ hTQ (e p).property, ?_⟩
  intro p p' hpp' hmem
  have hne : (e p : ℕ) ≠ e p' := by
    intro heq
    exact hpp' (e.injective (Subtype.ext heq))
  exact hTpair (e p) (e p).property (e p') (e p').property hne (Or.inr hmem)

/-! Canonical finite truncation and the finite state of the construction. -/

noncomputable def firstN {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α) : Finset α :=
  (S.toList.take n).toFinset

lemma firstN_subset {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α) :
    firstN n S ⊆ S := by
  intro x hx
  rw [firstN, List.mem_toFinset] at hx
  exact Finset.mem_toList.1 (List.take_subset n S.toList hx)

lemma firstN_card {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α)
    (hn : n ≤ S.card) :
    (firstN n S).card = n := by
  rw [firstN, List.toFinset_card_of_nodup]
  · simp [Finset.length_toList, hn]
  · exact (Finset.nodup_toList S).sublist (List.take_sublist n S.toList)

lemma firstN_card_le {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α) :
    (firstN n S).card ≤ n := by
  rw [firstN, List.toFinset_card_of_nodup]
  · simp [Finset.length_toList]
  · exact (Finset.nodup_toList S).sublist (List.take_sublist n S.toList)

structure DenseBuildState where
  deleted : Finset ℕ
  added : Finset ℕ
  targets : Finset ℕ

def DenseBuildState.empty : DenseBuildState := ⟨∅, ∅, ∅⟩

def DenseBuildState.currentSet (ω : DenseSample) (s : DenseBuildState) : Set ℕ :=
  (denseReservoirSet ω \ (s.deleted : Set ℕ)) ∪ (s.added : Set ℕ)

noncomputable def DenseBuildState.currentPrefix
    (ω : DenseSample) (s : DenseBuildState) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range N).filter (fun x ↦ x ∈ s.currentSet ω)

lemma mem_currentPrefix {ω : DenseSample} {s : DenseBuildState} {N x : ℕ} :
    x ∈ s.currentPrefix ω N ↔ x < N ∧ x ∈ s.currentSet ω := by
  classical
  simp [DenseBuildState.currentPrefix]

noncomputable def availableDensePairs
    (ω : DenseSample) (s : DenseBuildState) (m : ℕ) :
    Finset (strictReprIndices (m / 3) m) :=
  (densePresentPairs (m / 3) m ω).filter
    (fun i ↦ (i : ℕ) ∉ s.deleted ∧ m - (i : ℕ) ∉ s.deleted)

lemma mem_availableDensePairs {ω : DenseSample} {s : DenseBuildState}
    {m : ℕ} {i : strictReprIndices (m / 3) m} :
    i ∈ availableDensePairs ω s m ↔
      i ∈ densePresentPairs (m / 3) m ω ∧
        (i : ℕ) ∉ s.deleted ∧ m - (i : ℕ) ∉ s.deleted := by
  classical
  simp [availableDensePairs]

noncomputable def chosenDensePairs
    (ω : DenseSample) (s : DenseBuildState) (k c : ℕ) :
    Finset (strictReprIndices (c / 3) c) :=
  firstN (k + 1) (availableDensePairs ω s c)

lemma chosenDensePairs_subset_available
    (ω : DenseSample) (s : DenseBuildState) (k c : ℕ) :
    chosenDensePairs ω s k c ⊆ availableDensePairs ω s c :=
  firstN_subset _ _

lemma chosenDensePairs_card (ω : DenseSample) (s : DenseBuildState) (k c : ℕ)
    (hcard : k + 1 ≤ (availableDensePairs ω s c).card) :
    (chosenDensePairs ω s k c).card = k + 1 :=
  firstN_card _ _ hcard

def stageCanaries (K k : ℕ) (s : DenseBuildState) : Finset ℕ :=
  if K ≤ k then zBlock k \ s.targets else ∅

lemma mem_stageCanaries {K k c : ℕ} {s : DenseBuildState} :
    c ∈ stageCanaries K k s ↔ K ≤ k ∧ c ∈ zBlock k ∧ c ∉ s.targets := by
  classical
  unfold stageCanaries
  by_cases hk : K ≤ k <;> simp [hk, and_assoc]

def boolFin2 (b : Bool) : Fin 2 := if b then 1 else 0

def chosenPairEndpoint {c : ℕ} (i : strictReprIndices (c / 3) c)
    (b : Bool) : ℕ :=
  if b then c - (i : ℕ) else (i : ℕ)

lemma chosenPairEndpoint_eq_reprEndpoint {c : ℕ}
    (i : strictReprIndices (c / 3) c) (b : Bool) :
    chosenPairEndpoint i b = reprEndpoint (c / 3) c ⟨i, boolFin2 b⟩ := by
  cases b <;> simp [chosenPairEndpoint, boolFin2, reprEndpoint]

lemma chosenPairEndpoint_injective {c : ℕ}
    {ι : Type*} (i : ι → strictReprIndices (c / 3) c)
    (hi : Function.Injective i) (choice : ι → Bool) :
    Function.Injective (fun x ↦ chosenPairEndpoint (i x) (choice x)) := by
  intro x y hxy
  have hp : (⟨i x, boolFin2 (choice x)⟩ :
      (a : strictReprIndices (c / 3) c) × Fin 2) =
      ⟨i y, boolFin2 (choice y)⟩ :=
    reprEndpoint_injective (c / 3) c (by
      simpa only [← chosenPairEndpoint_eq_reprEndpoint] using hxy)
  exact hi (congrArg Sigma.fst hp)

noncomputable def stageEndpointPool
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : Finset ℕ := by
  classical
  exact (stageCanaries K k s).biUnion fun c ↦
    (chosenDensePairs ω s k c).biUnion fun i ↦ {(i : ℕ), c - (i : ℕ)}

lemma mem_stageEndpointPool {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {x : ℕ} :
    x ∈ stageEndpointPool ω K k s ↔
      ∃ c ∈ stageCanaries K k s,
        ∃ i ∈ chosenDensePairs ω s k c,
          x = (i : ℕ) ∨ x = c - (i : ℕ) := by
  classical
  simp only [stageEndpointPool, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton]

abbrev ChosenPairType
    (ω : DenseSample) (s : DenseBuildState) (k c : ℕ) :=
  {i : strictReprIndices (c / 3) c // i ∈ chosenDensePairs ω s k c}

abbrev StagePattern (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :=
  Σ c : {c // c ∈ stageCanaries K k s},
    ChosenPairType ω s k c × (ChosenPairType ω s k c → Bool)

noncomputable def patternTransversal
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (p : StagePattern ω K k s) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset (ChosenPairType ω s k p.1)).filter
      (fun i ↦ i ≠ p.2.1)).image
    (fun i : ChosenPairType ω s k p.1 ↦ chosenPairEndpoint i.1 (p.2.2 i))

lemma mem_patternTransversal {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {p : StagePattern ω K k s} {x : ℕ} :
    x ∈ patternTransversal ω K k s p ↔
      ∃ i : ChosenPairType ω s k p.1,
        i ≠ p.2.1 ∧
          chosenPairEndpoint (i : strictReprIndices (p.1 / 3) p.1) (p.2.2 i) = x := by
  classical
  unfold patternTransversal
  simp

lemma patternTransversal_subset_endpointPool
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (p : StagePattern ω K k s) :
    patternTransversal ω K k s p ⊆ stageEndpointPool ω K k s := by
  intro x hx
  obtain ⟨i, _hiomit, rfl⟩ := mem_patternTransversal.1 hx
  rw [mem_stageEndpointPool]
  refine ⟨p.1, p.1.property, i, i.property, ?_⟩
  cases h : p.2.2 i <;> simp [chosenPairEndpoint, h]

lemma patternTransversal_card
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (p : StagePattern ω K k s) :
    (patternTransversal ω K k s p).card =
      (chosenDensePairs ω s k p.1).card - 1 := by
  classical
  rw [patternTransversal, Finset.card_image_iff.mpr]
  · have hfilter :
        (Finset.univ.filter (fun i : ChosenPairType ω s k p.1 ↦ i ≠ p.2.1)) =
          Finset.univ.erase p.2.1 := by
        ext i
        simp [eq_comm]
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ p.2.1)]
    simp
  · intro i hi j hj hij
    exact chosenPairEndpoint_injective (fun x :
      ChosenPairType ω s k p.1 ↦
        (x : strictReprIndices (p.1 / 3) p.1)) Subtype.val_injective p.2.2 hij

lemma stageEndpointPool_card_le
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (stageEndpointPool ω K k s).card ≤
      2 * ((stageCanaries K k s).card * (k + 1)) := by
  classical
  calc
    (stageEndpointPool ω K k s).card ≤
        ∑ c ∈ stageCanaries K k s,
          ∑ _i ∈ chosenDensePairs ω s k c, 2 := by
      unfold stageEndpointPool
      refine (Finset.card_biUnion_le).trans ?_
      apply Finset.sum_le_sum
      intro c hc
      refine (Finset.card_biUnion_le).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_insert_le (i : ℕ) {c - (i : ℕ)}).trans (by simp)
    _ = ∑ c ∈ stageCanaries K k s,
        2 * (chosenDensePairs ω s k c).card := by simp [mul_comm]
    _ ≤ ∑ _c ∈ stageCanaries K k s, 2 * (k + 1) := by
      apply Finset.sum_le_sum
      intro c hc
      gcongr
      exact firstN_card_le _ _
    _ = 2 * ((stageCanaries K k s).card * (k + 1)) := by
      simp
      ring

lemma stagePattern_card_eq
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    Fintype.card (StagePattern ω K k s) =
      ∑ c ∈ stageCanaries K k s,
        (chosenDensePairs ω s k c).card *
          2 ^ (chosenDensePairs ω s k c).card := by
  classical
  simp [StagePattern, ChosenPairType, Fintype.card_sigma]
  exact Finset.sum_attach (stageCanaries K k s)
    (fun c ↦ (chosenDensePairs ω s k c).card *
      2 ^ (chosenDensePairs ω s k c).card)

lemma stagePattern_card_le
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    Fintype.card (StagePattern ω K k s) ≤
      (stageCanaries K k s).card * ((k + 1) * 2 ^ (k + 1)) := by
  rw [stagePattern_card_eq]
  calc
    (∑ c ∈ stageCanaries K k s,
        (chosenDensePairs ω s k c).card *
          2 ^ (chosenDensePairs ω s k c).card) ≤
        ∑ _c ∈ stageCanaries K k s, (k + 1) * 2 ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro c hc
      have hcard := firstN_card_le (k + 1) (availableDensePairs ω s c)
      exact Nat.mul_le_mul hcard (Nat.pow_le_pow_right (by omega) hcard)
    _ = (stageCanaries K k s).card * ((k + 1) * 2 ^ (k + 1)) := by simp

def targetSizeCondition
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : Prop :=
  (1 + 2 * ((s.currentPrefix ω (30 * Z (targetStage k))).card *
      (stageEndpointPool ω K k s).card)) *
      Fintype.card (StagePattern ω K k s) ≤ (targetInterval k).card

noncomputable def stageTarget
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    StagePattern ω K k s → ℕ := by
  classical
  by_cases h : targetSizeCondition ω K k s
  · exact Classical.choose (exists_target_embedding
      (targetInterval k)
      (s.currentPrefix ω (30 * Z (targetStage k)))
      (stageEndpointPool ω K k s) h)
  · exact fun _ ↦ 20 * Z (targetStage k)

lemma stageTarget_spec
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (hsize : targetSizeCondition ω K k s) :
    Function.Injective (stageTarget ω K k s) ∧
      (∀ p, stageTarget ω K k s p ∈ targetInterval k) ∧
      ∀ p p', p ≠ p' →
        ((stageTarget ω K k s p : ℤ) - (stageTarget ω K k s p' : ℤ)) ∉
          symmetricDiffFinset
            (s.currentPrefix ω (30 * Z (targetStage k)))
            (stageEndpointPool ω K k s) := by
  classical
  unfold stageTarget
  rw [dif_pos hsize]
  exact Classical.choose_spec (exists_target_embedding
    (targetInterval k)
    (s.currentPrefix ω (30 * Z (targetStage k)))
    (stageEndpointPool ω K k s) hsize)

noncomputable def stageTargets
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : Finset ℕ := by
  classical
  exact Finset.univ.image (stageTarget ω K k s)

lemma mem_stageTargets {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {b : ℕ} :
    b ∈ stageTargets ω K k s ↔
      ∃ p : StagePattern ω K k s, stageTarget ω K k s p = b := by
  classical
  simp [stageTargets]

lemma stageTargets_card
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (hsize : targetSizeCondition ω K k s) :
    (stageTargets ω K k s).card = Fintype.card (StagePattern ω K k s) := by
  classical
  rw [stageTargets, Finset.card_image_of_injective _
    (stageTarget_spec ω K k s hsize).1]
  simp

lemma stageTargets_subset_targetInterval
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (hsize : targetSizeCondition ω K k s) :
    stageTargets ω K k s ⊆ targetInterval k := by
  intro b hb
  obtain ⟨p, rfl⟩ := mem_stageTargets.1 hb
  exact (stageTarget_spec ω K k s hsize).2.1 p

noncomputable def oldHighEndpoints
    (ω : DenseSample) (s : DenseBuildState) (b : ℕ) : Finset ℕ := by
  classical
  exact (unordRepr (s.currentSet ω) b).image Prod.snd

lemma mem_oldHighEndpoints {ω : DenseSample} {s : DenseBuildState} {b d : ℕ} :
    d ∈ oldHighEndpoints ω s b ↔
      ∃ p ∈ unordRepr (s.currentSet ω) b, p.2 = d := by
  classical
  simp [oldHighEndpoints]

noncomputable def stageDeleted
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : Finset ℕ :=
  (stageTargets ω K k s).biUnion (oldHighEndpoints ω s)

lemma mem_stageDeleted {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {d : ℕ} :
    d ∈ stageDeleted ω K k s ↔
      ∃ b ∈ stageTargets ω K k s,
        ∃ p ∈ unordRepr (s.currentSet ω) b, p.2 = d := by
  classical
  simp only [stageDeleted, Finset.mem_biUnion, mem_oldHighEndpoints]

noncomputable def patternAdded
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (p : StagePattern ω K k s) : Finset ℕ := by
  classical
  exact (patternTransversal ω K k s p).image
    (fun x ↦ stageTarget ω K k s p - x)

lemma mem_patternAdded {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {p : StagePattern ω K k s} {a : ℕ} :
    a ∈ patternAdded ω K k s p ↔
      ∃ x ∈ patternTransversal ω K k s p,
        stageTarget ω K k s p - x = a := by
  classical
  simp [patternAdded]

noncomputable def stageAdded
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion (patternAdded ω K k s)

lemma mem_stageAdded {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {a : ℕ} :
    a ∈ stageAdded ω K k s ↔
      ∃ p : StagePattern ω K k s,
        ∃ x ∈ patternTransversal ω K k s p,
          stageTarget ω K k s p - x = a := by
  classical
  simp only [stageAdded, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_patternAdded]

lemma patternAdded_card_le
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (p : StagePattern ω K k s) :
    (patternAdded ω K k s p).card ≤ (chosenDensePairs ω s k p.1).card - 1 := by
  exact Finset.card_image_le.trans (patternTransversal_card ω K k s p).le

lemma stageAdded_card_le
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (stageAdded ω K k s).card ≤
      Fintype.card (StagePattern ω K k s) * k := by
  classical
  calc
    (stageAdded ω K k s).card ≤
        ∑ p : StagePattern ω K k s, (patternAdded ω K k s p).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p : StagePattern ω K k s, k := by
      apply Finset.sum_le_sum
      intro p hp
      exact (patternAdded_card_le ω K k s p).trans (by
        have hchosen : (chosenDensePairs ω s k p.1).card ≤ k + 1 := by
          simpa [chosenDensePairs] using
            firstN_card_le (k + 1) (availableDensePairs ω s p.1)
        omega)
    _ = Fintype.card (StagePattern ω K k s) * k := by simp

noncomputable def denseStageStep
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) : DenseBuildState where
  deleted := s.deleted ∪ stageDeleted ω K k s
  added := (s.added \ stageDeleted ω K k s) ∪ stageAdded ω K k s
  targets := s.targets ∪ stageTargets ω K k s

noncomputable def denseBuildState (ω : DenseSample) (K : ℕ) : ℕ → DenseBuildState
  | 0 => DenseBuildState.empty
  | k + 1 => denseStageStep ω K k (denseBuildState ω K k)

@[simp] lemma denseBuildState_zero (ω : DenseSample) (K : ℕ) :
    denseBuildState ω K 0 = DenseBuildState.empty := rfl

@[simp] lemma denseBuildState_succ (ω : DenseSample) (K k : ℕ) :
    denseBuildState ω K (k + 1) =
      denseStageStep ω K k (denseBuildState ω K k) := rfl

noncomputable def buildTargets (ω : DenseSample) (K k : ℕ) : Finset ℕ :=
  stageTargets ω K k (denseBuildState ω K k)

noncomputable def buildCanaries (ω : DenseSample) (K k : ℕ) : Finset ℕ :=

  stageCanaries K k (denseBuildState ω K k)

noncomputable def buildDeleted (ω : DenseSample) (K k : ℕ) : Finset ℕ :=
  stageDeleted ω K k (denseBuildState ω K k)

noncomputable def buildAdded (ω : DenseSample) (K k : ℕ) : Finset ℕ :=
  stageAdded ω K k (denseBuildState ω K k)

def finalDeleted (ω : DenseSample) (K : ℕ) : Set ℕ :=
  stagedSet (buildDeleted ω K)

def finalAdded (ω : DenseSample) (K : ℕ) : Set ℕ :=
  stagedSet (buildAdded ω K)

def denseFinalSet (ω : DenseSample) (K : ℕ) : Set ℕ :=
  (denseReservoirSet ω \ finalDeleted ω K) ∪ finalAdded ω K

noncomputable def finalTargetBlocks (ω : DenseSample) (K : ℕ) : ℕ → Finset ℕ
  | n => if 10 ≤ n then buildTargets ω K (n - 10) else ∅

noncomputable def finalCanaryBlocks (ω : DenseSample) (K : ℕ) : ℕ → Finset ℕ :=
  buildCanaries ω K

@[simp] lemma finalTargetBlocks_add_ten (ω : DenseSample) (K n : ℕ) :
    finalTargetBlocks ω K (n + 10) = buildTargets ω K n := by
  simp [finalTargetBlocks]

lemma stageEndpointPool_lt_Z
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState} {x : ℕ}
    (hx : x ∈ stageEndpointPool ω K k s) :
    x < Z (k + 1) := by
  obtain ⟨c, hc, i, hi, hxi⟩ := mem_stageEndpointPool.1 hx
  have hcz : c < Z (k + 1) := (mem_zBlock.1 (mem_stageCanaries.1 hc).2.1).2
  rcases hxi with hxi | hxi
  · subst x
    have hii := Finset.mem_filter.1 i.property
    exact (Finset.mem_Icc.1 hii.1).2.trans_lt hcz
  · subst x
    exact (Nat.sub_le c i).trans_lt hcz

lemma patternTransversal_lt_Z
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {p : StagePattern ω K k s} {x : ℕ}
    (hx : x ∈ patternTransversal ω K k s p) :
    x < Z (k + 1) :=
  stageEndpointPool_lt_Z (patternTransversal_subset_endpointPool ω K k s p hx)

lemma stageDeleted_mem_zBlock
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {d : ℕ}
    (hd : d ∈ stageDeleted ω K k s) :
    d ∈ zBlock (targetStage k) := by
  obtain ⟨b, hb, p, hp, rfl⟩ := mem_stageDeleted.1 hd
  have hbI := stageTargets_subset_targetInterval ω K k s hsize hb
  have hbnds := mem_targetInterval.1 hbI
  have hp' := mem_unordRepr.1 hp
  have hdouble : 20 * Z (targetStage k) ≤ 2 * p.2 := by
    calc
      20 * Z (targetStage k) ≤ b := hbnds.1
      _ = p.1 + p.2 := hp'.2.2.2.symm
      _ ≤ p.2 + p.2 := Nat.add_le_add_right hp'.1 p.2
      _ = 2 * p.2 := by omega
  rw [mem_zBlock]
  constructor
  · omega
  · calc
      p.2 ≤ b := by omega
      _ < 30 * Z (targetStage k) := hbnds.2
      _ < Z (targetStage k + 1) := by
        rw [Z_succ]
        have := Z_pos (targetStage k)
        omega

lemma stageDeleted_bounds
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {d : ℕ}
    (hd : d ∈ stageDeleted ω K k s) :
    10 * Z (targetStage k) ≤ d ∧ d < 30 * Z (targetStage k) := by
  obtain ⟨b, hb, p, hp, rfl⟩ := mem_stageDeleted.1 hd
  have hbnds := mem_targetInterval.1
    (stageTargets_subset_targetInterval ω K k s hsize hb)
  have hp' := mem_unordRepr.1 hp
  constructor
  · have hdouble : 20 * Z (targetStage k) ≤ 2 * p.2 := by
      calc
        20 * Z (targetStage k) ≤ b := hbnds.1
        _ = p.1 + p.2 := hp'.2.2.2.symm
        _ ≤ p.2 + p.2 := Nat.add_le_add_right hp'.1 p.2
        _ = 2 * p.2 := by omega
    omega
  · exact (show p.2 ≤ b by omega).trans_lt hbnds.2

lemma stageAdded_mem_zBlock
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {a : ℕ}
    (ha : a ∈ stageAdded ω K k s) :
    a ∈ zBlock (targetStage k) := by
  obtain ⟨p, x, hx, rfl⟩ := mem_stageAdded.1 ha
  have hbI := (stageTarget_spec ω K k s hsize).2.1 p
  have hbnds := mem_targetInterval.1 hbI
  have hxlt := patternTransversal_lt_Z hx
  have hZle : Z (k + 1) ≤ Z (targetStage k) :=
    Z_mono (source_succ_le_targetStage k)
  rw [mem_zBlock]
  constructor
  · have hxle : x ≤ Z (targetStage k) := hxlt.le.trans hZle
    omega
  · calc
      stageTarget ω K k s p - x ≤ stageTarget ω K k s p := Nat.sub_le _ _
      _ < 30 * Z (targetStage k) := hbnds.2
      _ < Z (targetStage k + 1) := by
        rw [Z_succ]
        have := Z_pos (targetStage k)
        omega

lemma stageAdded_bounds
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {a : ℕ}
    (ha : a ∈ stageAdded ω K k s) :
    19 * Z (targetStage k) ≤ a ∧ a < 30 * Z (targetStage k) := by
  obtain ⟨p, x, hx, rfl⟩ := mem_stageAdded.1 ha
  have hbnds := mem_targetInterval.1
    ((stageTarget_spec ω K k s hsize).2.1 p)
  have hxlt := patternTransversal_lt_Z hx
  have hZle : Z (k + 1) ≤ Z (targetStage k) :=
    Z_mono (source_succ_le_targetStage k)
  constructor
  · have hxle : x ≤ Z (targetStage k) := hxlt.le.trans hZle
    omega
  · exact (Nat.sub_le _ _).trans_lt hbnds.2

lemma stageTargets_mem_zBlock
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {b : ℕ}
    (hb : b ∈ stageTargets ω K k s) :
    b ∈ zBlock (targetStage k) := by
  have hbnds := mem_targetInterval.1
    (stageTargets_subset_targetInterval ω K k s hsize hb)
  rw [mem_zBlock]
  constructor
  · have hz := Z_pos (targetStage k)
    omega
  · calc
      b < 30 * Z (targetStage k) := hbnds.2
      _ < Z (targetStage k + 1) := by
        rw [Z_succ]
        have := Z_pos (targetStage k)
        omega

lemma stageCanaries_card_le_Z
    (K k : ℕ) (s : DenseBuildState) :
    (stageCanaries K k s).card ≤ Z (k + 1) := by
  calc
    (stageCanaries K k s).card ≤ (zBlock k).card := by
      apply Finset.card_le_card
      intro c hc
      exact (mem_stageCanaries.1 hc).2.1
    _ ≤ Z (k + 1) := zBlock_card_le_Z_succ k

lemma stagePattern_card_le_two_pow
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    Fintype.card (StagePattern ω K k s) ≤ 2 ^ (10 * (k + 1)) := by
  let u := k + 1
  have hcan : (stageCanaries K k s).card ≤ 2 ^ (8 * u) := by
    simpa [u, Z_eq_two_pow] using stageCanaries_card_le_Z K k s
  have hu : u ≤ 2 ^ u := nat_le_two_pow u
  calc
    Fintype.card (StagePattern ω K k s) ≤
        (stageCanaries K k s).card * (u * 2 ^ u) := by
      simpa [u] using stagePattern_card_le ω K k s
    _ ≤ 2 ^ (8 * u) * (2 ^ u * 2 ^ u) :=
      Nat.mul_le_mul hcan (Nat.mul_le_mul hu le_rfl)
    _ = 2 ^ (10 * u) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ = 2 ^ (10 * (k + 1)) := rfl

lemma stageAdded_card_le_two_pow
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (stageAdded ω K k s).card ≤ 2 ^ (11 * (k + 1)) := by
  have hk : k ≤ 2 ^ (k + 1) :=
    (nat_le_two_pow k).trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    (stageAdded ω K k s).card ≤
        Fintype.card (StagePattern ω K k s) * k :=
      stageAdded_card_le ω K k s
    _ ≤ 2 ^ (10 * (k + 1)) * 2 ^ (k + 1) :=
      Nat.mul_le_mul (stagePattern_card_le_two_pow ω K k s) hk
    _ = 2 ^ (11 * (k + 1)) := by
      rw [← pow_add]
      congr 1
      omega

lemma denseBuildState_added_card_le
    (ω : DenseSample) (K k : ℕ) :
    (denseBuildState ω K k).added.card ≤ 2 ^ (12 * k) := by
  induction k with
  | zero => simp [DenseBuildState.empty]
  | succ k ih =>
      have hold : (denseBuildState ω K k).added.card ≤ 2 ^ (12 * k) := ih
      have hnew := stageAdded_card_le_two_pow ω K k (denseBuildState ω K k)
      have hcard :
          (((denseBuildState ω K k).added \
              stageDeleted ω K k (denseBuildState ω K k)) ∪
            stageAdded ω K k (denseBuildState ω K k)).card ≤
            (denseBuildState ω K k).added.card +
              (stageAdded ω K k (denseBuildState ω K k)).card :=
        (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right
            (Finset.card_le_card (Finset.sdiff_subset)) _)
      rw [denseBuildState_succ, denseStageStep]
      calc
        (((denseBuildState ω K k).added \
            stageDeleted ω K k (denseBuildState ω K k)) ∪
            stageAdded ω K k (denseBuildState ω K k)).card ≤
            (denseBuildState ω K k).added.card +
              (stageAdded ω K k (denseBuildState ω K k)).card := hcard
        _ ≤ 2 ^ (12 * k) + 2 ^ (11 * (k + 1)) := Nat.add_le_add hold hnew
        _ ≤ 2 ^ (12 * k + 11) + 2 ^ (12 * k + 11) := by
          apply Nat.add_le_add
          · exact Nat.pow_le_pow_right (by decide) (by omega)
          · exact Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ (12 * (k + 1)) := by
          calc
            2 ^ (12 * k + 11) + 2 ^ (12 * k + 11) =
                2 * 2 ^ (12 * k + 11) := by omega
            _ = 2 ^ ((12 * k + 11) + 1) := by
              conv_rhs => rw [pow_succ]
              exact Nat.mul_comm _ _
            _ = 2 ^ (12 * (k + 1)) := by congr 1 <;> omega

lemma stageTargets_card_le_two_pow
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (stageTargets ω K k s).card ≤ 2 ^ (10 * (k + 1)) := by
  exact Finset.card_image_le.trans (stagePattern_card_le_two_pow ω K k s)

lemma denseBuildState_targets_card_le
    (ω : DenseSample) (K k : ℕ) :
    (denseBuildState ω K k).targets.card ≤ 2 ^ (12 * k) := by
  induction k with
  | zero => simp [DenseBuildState.empty]
  | succ k ih =>
      have hnew := stageTargets_card_le_two_pow ω K k (denseBuildState ω K k)
      rw [denseBuildState_succ, denseStageStep]
      calc
        ((denseBuildState ω K k).targets ∪
            stageTargets ω K k (denseBuildState ω K k)).card ≤
            (denseBuildState ω K k).targets.card +
              (stageTargets ω K k (denseBuildState ω K k)).card :=
          Finset.card_union_le _ _
        _ ≤ 2 ^ (12 * k) + 2 ^ (10 * (k + 1)) := Nat.add_le_add ih hnew
        _ ≤ 2 ^ (12 * k + 11) + 2 ^ (12 * k + 11) := by
          apply Nat.add_le_add
          · exact Nat.pow_le_pow_right (by decide) (by omega)
          · exact Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ (12 * (k + 1)) := by
          calc
            2 ^ (12 * k + 11) + 2 ^ (12 * k + 11) =
                2 * 2 ^ (12 * k + 11) := by omega
            _ = 2 ^ ((12 * k + 11) + 1) := by
              conv_rhs => rw [pow_succ]
              exact Nat.mul_comm _ _
            _ = 2 ^ (12 * (k + 1)) := by congr 1 <;> omega

lemma currentPrefix_card_le_selected_add
    (ω : DenseSample) (s : DenseBuildState) (t N : ℕ)
    (hN : N ≤ Z (t + 1)) :
    (s.currentPrefix ω N).card ≤
      (denseSelectedInitial t ω).card + s.added.card := by
  classical
  have hsub : s.currentPrefix ω N ⊆ denseSelectedInitial t ω ∪ s.added := by
    intro x hx
    have hx' := mem_currentPrefix.1 hx
    rcases hx'.2 with hxR | hxadd
    · exact Finset.mem_union.2 (Or.inl (mem_denseSelectedInitial.2
        ⟨hx'.1.trans_le hN, hxR.1⟩))
    · exact Finset.mem_union.2 (Or.inr hxadd)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma endpointPool_card_le_two_pow
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (stageEndpointPool ω K k s).card ≤ 2 ^ (10 * (k + 1)) := by
  let u := k + 1
  have hcan : (stageCanaries K k s).card ≤ 2 ^ (8 * u) := by
    simpa [u, Z_eq_two_pow] using stageCanaries_card_le_Z K k s
  have hu : u ≤ 2 ^ u := nat_le_two_pow u
  calc
    (stageEndpointPool ω K k s).card ≤
        2 * ((stageCanaries K k s).card * u) := by
      simpa [u] using stageEndpointPool_card_le ω K k s
    _ ≤ 2 ^ 1 * (2 ^ (8 * u) * 2 ^ u) := by
      exact Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hcan hu)
    _ = 2 ^ (9 * u + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (10 * u) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ (10 * (k + 1)) := rfl

lemma currentPrefix_target_card_le_two_pow
    (ω : DenseSample) (K k : ℕ)
    (hpoint : (denseSelectedInitial (targetStage k) ω).card ≤
      64 ^ (targetStage k + 1)) :
    ((denseBuildState ω K k).currentPrefix ω
      (30 * Z (targetStage k))).card ≤ 2 ^ (7000 * (k + 1)) := by
  let u := k + 1
  let t := targetStage k
  have ht : t = 1000 * u := rfl
  have hN : 30 * Z t ≤ Z (t + 1) := by
    rw [Z_succ]
    have := Z_pos t
    omega
  have hprefix := currentPrefix_card_le_selected_add ω
    (denseBuildState ω K k) t (30 * Z t) hN
  have hselected : (denseSelectedInitial t ω).card ≤ 2 ^ (6999 * u) := by
    calc
      (denseSelectedInitial t ω).card ≤ 64 ^ (t + 1) := hpoint
      _ = 2 ^ (6 * (t + 1)) := by
        rw [show 64 = 2 ^ 6 by norm_num, ← pow_mul]
      _ ≤ 2 ^ (6999 * u) := Nat.pow_le_pow_right (by decide) (by
        rw [ht]
        omega)
  have hadd : (denseBuildState ω K k).added.card ≤ 2 ^ (6999 * u) :=
    (denseBuildState_added_card_le ω K k).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [u]; omega))
  calc
    ((denseBuildState ω K k).currentPrefix ω (30 * Z t)).card ≤
        (denseSelectedInitial t ω).card +
          (denseBuildState ω K k).added.card := hprefix
    _ ≤ 2 ^ (6999 * u) + 2 ^ (6999 * u) := Nat.add_le_add hselected hadd
    _ = 2 ^ (6999 * u + 1) := by
      calc
        2 ^ (6999 * u) + 2 ^ (6999 * u) = 2 * 2 ^ (6999 * u) := by omega
        _ = 2 ^ (6999 * u + 1) := by
          conv_rhs => rw [pow_succ]
          exact Nat.mul_comm _ _
    _ ≤ 2 ^ (7000 * u) := Nat.pow_le_pow_right (by decide) (by omega)

lemma targetSizeCondition_of_point_bound
    (ω : DenseSample) (K k : ℕ)
    (hpoint : (denseSelectedInitial (targetStage k) ω).card ≤
      64 ^ (targetStage k + 1)) :
    targetSizeCondition ω K k (denseBuildState ω K k) := by
  let u := k + 1
  let A := ((denseBuildState ω K k).currentPrefix ω
    (30 * Z (targetStage k))).card
  let S := (stageEndpointPool ω K k (denseBuildState ω K k)).card
  let P := Fintype.card (StagePattern ω K k (denseBuildState ω K k))
  have hA : A ≤ 2 ^ (7000 * u) := by
    simpa [A, u] using currentPrefix_target_card_le_two_pow ω K k hpoint
  have hS : S ≤ 2 ^ (10 * u) := by
    simpa [S, u] using endpointPool_card_le_two_pow ω K k (denseBuildState ω K k)
  have hP : P ≤ 2 ^ (10 * u) := by
    simpa [P, u] using stagePattern_card_le_two_pow ω K k (denseBuildState ω K k)
  have hAS : A * S ≤ 2 ^ (7010 * u) := by
    calc
      A * S ≤ 2 ^ (7000 * u) * 2 ^ (10 * u) := Nat.mul_le_mul hA hS
      _ = 2 ^ (7010 * u) := by
        rw [← pow_add]
        congr 1
        omega
  have hD : 1 + 2 * (A * S) ≤ 2 ^ (7020 * u) := by
    have hbase : 1 ≤ 2 ^ (7011 * u) := by
      have hp : 0 < 2 ^ (7011 * u) := pow_pos (by decide) _
      omega
    have htwo : 2 * (A * S) ≤ 2 ^ (7011 * u) := by
      calc
        2 * (A * S) ≤ 2 * 2 ^ (7010 * u) := Nat.mul_le_mul_left 2 hAS
        _ = 2 ^ (7010 * u + 1) := by
          conv_rhs => rw [pow_succ]
          exact Nat.mul_comm _ _
        _ ≤ 2 ^ (7011 * u) := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1 + 2 * (A * S) ≤ 2 ^ (7011 * u) + 2 ^ (7011 * u) :=
        Nat.add_le_add hbase htwo
      _ = 2 ^ (7011 * u + 1) := by
        calc
          2 ^ (7011 * u) + 2 ^ (7011 * u) = 2 * 2 ^ (7011 * u) := by omega
          _ = 2 ^ (7011 * u + 1) := by
            conv_rhs => rw [pow_succ]
            exact Nat.mul_comm _ _
      _ ≤ 2 ^ (7020 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have hDP : (1 + 2 * (A * S)) * P ≤ 2 ^ (7030 * u) := by
    calc
      (1 + 2 * (A * S)) * P ≤ 2 ^ (7020 * u) * 2 ^ (10 * u) :=
        Nat.mul_le_mul hD hP
      _ = 2 ^ (7030 * u) := by
        rw [← pow_add]
        congr 1
        omega
  have hQ : 2 ^ (7030 * u) ≤ (targetInterval k).card := by
    rw [targetInterval_card, Z_eq_two_pow]
    calc
      2 ^ (7030 * u) ≤ 2 ^ (8000 * u) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 10 * 2 ^ (8 * targetStage k) := by
        have ht : 8 * targetStage k = 8000 * u := by
          dsimp [targetStage, u]
          omega
        rw [ht]
        have hp : 0 < 2 ^ (8000 * u) := pow_pos (by decide) _
        omega
  exact hDP.trans hQ

lemma denseStageStep_currentSet
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) :
    (denseStageStep ω K k s).currentSet ω =
      (s.currentSet ω \ (stageDeleted ω K k s : Set ℕ)) ∪
        (stageAdded ω K k s : Set ℕ) := by
  ext x
  simp only [DenseBuildState.currentSet, denseStageStep, Set.mem_union,
    Set.mem_diff, Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff]
  aesop

lemma stageTarget_ne_of_ne
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (hsize : targetSizeCondition ω K k s)
    {p q : StagePattern ω K k s} (hpq : p ≠ q) :
    stageTarget ω K k s p ≠ stageTarget ω K k s q :=
  (stageTarget_spec ω K k s hsize).1.ne hpq

lemma stageTarget_difference_forbidden
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState)
    (hsize : targetSizeCondition ω K k s)
    {p q : StagePattern ω K k s} (hpq : p ≠ q) :
    ((stageTarget ω K k s p : ℤ) - (stageTarget ω K k s q : ℤ)) ∉
      symmetricDiffFinset
        (s.currentPrefix ω (30 * Z (targetStage k)))
        (stageEndpointPool ω K k s) :=
  (stageTarget_spec ω K k s hsize).2.2 p q hpq

lemma stageAdded_decompose
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s) {a : ℕ}
    (ha : a ∈ stageAdded ω K k s) :
    ∃ p : StagePattern ω K k s,
      ∃ x ∈ patternTransversal ω K k s p,
        a + x = stageTarget ω K k s p := by
  obtain ⟨p, x, hx, hax⟩ := mem_stageAdded.1 ha
  refine ⟨p, x, hx, ?_⟩
  have hbnds := mem_targetInterval.1
    ((stageTarget_spec ω K k s hsize).2.1 p)
  have hxlt := patternTransversal_lt_Z hx
  have hZle : Z (k + 1) ≤ Z (targetStage k) :=
    Z_mono (source_succ_le_targetStage k)
  have hxb : x ≤ stageTarget ω K k s p := by omega
  omega

lemma two_stageAdded_sum_gt_target
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s)
    {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ stageAdded ω K k s)
    (ha₂ : a₂ ∈ stageAdded ω K k s)
    (p : StagePattern ω K k s) :
    stageTarget ω K k s p < a₁ + a₂ := by
  have h₁ := (stageAdded_bounds hsize ha₁).1
  have h₂ := (stageAdded_bounds hsize ha₂).1
  have hb := (mem_targetInterval.1
    ((stageTarget_spec ω K k s hsize).2.1 p)).2
  have hz := Z_pos (targetStage k)
  omega

lemma cross_stageAdded_eq_source
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s)
    {p q : StagePattern ω K k s} {a z x : ℕ}
    (ha : a + x = stageTarget ω K k s q)
    (hx : x ∈ patternTransversal ω K k s q)
    (hz : z ∈ s.currentSet ω)
    (hsum : z + a = stageTarget ω K k s p) :
    q = p ∧ z = x := by
  have hpb := (mem_targetInterval.1
    ((stageTarget_spec ω K k s hsize).2.1 p)).2
  have hzlt : z < 30 * Z (targetStage k) := by omega
  have hzpre : z ∈ s.currentPrefix ω (30 * Z (targetStage k)) :=
    mem_currentPrefix.2 ⟨hzlt, hz⟩
  have hxpool := patternTransversal_subset_endpointPool ω K k s q hx
  have haZ : (a : ℤ) + (x : ℤ) = (stageTarget ω K k s q : ℤ) := by
    exact_mod_cast ha
  have hsumZ : (z : ℤ) + (a : ℤ) = (stageTarget ω K k s p : ℤ) := by
    exact_mod_cast hsum
  have heq :
      (stageTarget ω K k s p : ℤ) - (stageTarget ω K k s q : ℤ) =
        (z : ℤ) - (x : ℤ) := by
    omega
  have hpq : p = q := eq_of_pairwise_symmetricDiff_avoiding
    (stageTarget ω K k s) (stageTarget_spec ω K k s hsize).2.2
    hzpre hxpool heq
  have hqp : q = p := hpq.symm
  subst q
  exact ⟨rfl, by omega⟩

lemma stageTarget_representation_hits_transversal
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s)
    (p : StagePattern ω K k s) {r : ℕ × ℕ}
    (hr : r ∈ unordRepr ((denseStageStep ω K k s).currentSet ω)
      (stageTarget ω K k s p)) :
    r.1 ∈ patternTransversal ω K k s p ∨
      r.2 ∈ patternTransversal ω K k s p := by
  have hr' := mem_unordRepr.1 hr
  have hr1 := hr'.2.1
  have hr2 := hr'.2.2.1
  rw [denseStageStep_currentSet] at hr1 hr2
  rcases hr1 with hr1old | hr1add
  · rcases hr2 with hr2old | hr2add
    · exfalso
      have hrold : r ∈ unordRepr (s.currentSet ω)
          (stageTarget ω K k s p) :=
        mem_unordRepr.2 ⟨hr'.1, hr1old.1, hr2old.1, hr'.2.2.2⟩
      have hb : stageTarget ω K k s p ∈ stageTargets ω K k s :=
        mem_stageTargets.2 ⟨p, rfl⟩
      have hd : r.2 ∈ stageDeleted ω K k s :=
        mem_stageDeleted.2 ⟨stageTarget ω K k s p, hb, r, hrold, rfl⟩
      exact hr2old.2 hd
    · obtain ⟨q, x, hx, hax⟩ := stageAdded_decompose hsize hr2add
      have hcross := cross_stageAdded_eq_source hsize hax hx hr1old.1
        (by simpa [add_comm] using hr'.2.2.2)
      rcases hcross with ⟨rfl, hzx⟩
      exact Or.inl (hzx ▸ hx)
  · rcases hr2 with hr2old | hr2add
    · obtain ⟨q, x, hx, hax⟩ := stageAdded_decompose hsize hr1add
      have hcross := cross_stageAdded_eq_source hsize hax hx hr2old.1
        (by simpa [add_comm] using hr'.2.2.2)
      rcases hcross with ⟨rfl, hzx⟩
      exact Or.inr (hzx ▸ hx)
    · exfalso
      have htoo := two_stageAdded_sum_gt_target hsize hr1add hr2add p
      omega

lemma mem_denseBuildState_deleted_iff
    {ω : DenseSample} {K n x : ℕ} :
    x ∈ (denseBuildState ω K n).deleted ↔
      ∃ j < n, x ∈ buildDeleted ω K j := by
  induction n with
  | zero => simp [DenseBuildState.empty]
  | succ n ih =>
      rw [denseBuildState_succ]
      simp only [denseStageStep, Finset.mem_union, ih, buildDeleted]
      constructor
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, hj.trans (Nat.lt_succ_self n), hx⟩
        · exact ⟨n, Nat.lt_succ_self n, hx⟩
      · rintro ⟨j, hj, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl ⟨j, hj, hx⟩
        · exact Or.inr hx

lemma mem_denseBuildState_targets_iff
    {ω : DenseSample} {K n x : ℕ} :
    x ∈ (denseBuildState ω K n).targets ↔
      ∃ j < n, x ∈ buildTargets ω K j := by
  induction n with
  | zero => simp [DenseBuildState.empty]
  | succ n ih =>
      rw [denseBuildState_succ]
      simp only [denseStageStep, Finset.mem_union, ih, buildTargets]
      constructor
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, hj.trans (Nat.lt_succ_self n), hx⟩
        · exact ⟨n, Nat.lt_succ_self n, hx⟩
      · rintro ⟨j, hj, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl ⟨j, hj, hx⟩
        · exact Or.inr hx

lemma denseBuildState_added_mem_stage
    {ω : DenseSample} {K n x : ℕ}
    (hx : x ∈ (denseBuildState ω K n).added) :
    ∃ j < n, x ∈ buildAdded ω K j := by
  induction n with
  | zero => simpa [DenseBuildState.empty] using hx
  | succ n ih =>
      rw [denseBuildState_succ] at hx
      simp only [denseStageStep, Finset.mem_union, Finset.mem_sdiff] at hx
      rcases hx with hx | hx
      · obtain ⟨j, hj, hxj⟩ := ih hx.1
        exact ⟨j, hj.trans (Nat.lt_succ_self n), hxj⟩
      · exact ⟨n, Nat.lt_succ_self n, hx⟩

lemma targetStage_lt_of_lt {i j : ℕ} (hij : i < j) :
    targetStage i < targetStage j := targetStage_strictMono hij

lemma zBlock_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (zBlock i) (zBlock j) := by
  apply Finset.disjoint_left.2
  intro x hxi hxj
  have hi := mem_zBlock.1 hxi
  have hj := mem_zBlock.1 hxj
  have hsucc : i + 1 ≤ j := Nat.succ_le_iff.2 hij
  have hZ := Z_mono hsucc
  omega

lemma buildAdded_disjoint_buildDeleted
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (buildAdded ω K i) (buildDeleted ω K j) := by
  apply Finset.disjoint_left.2

  intro x hxi hxj
  have hi : x ∈ zBlock (targetStage i) :=
    stageAdded_mem_zBlock (hsize i) hxi
  have hj : x ∈ zBlock (targetStage j) :=
    stageDeleted_mem_zBlock (hsize j) hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Finset.disjoint_left.1
      (zBlock_disjoint_of_lt (targetStage_lt_of_lt hij)) hi hj
  · exact Finset.disjoint_left.1
      (zBlock_disjoint_of_lt (targetStage_lt_of_lt hji)) hj hi

lemma mem_denseBuildState_added_iff
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n x : ℕ} :
    x ∈ (denseBuildState ω K n).added ↔
      ∃ j < n, x ∈ buildAdded ω K j := by
  constructor
  · exact denseBuildState_added_mem_stage
  · rintro ⟨j, hj, hxj⟩
    induction n with
    | zero => omega
    | succ n ih =>
        rw [denseBuildState_succ]
        simp only [denseStageStep, Finset.mem_union, Finset.mem_sdiff]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · left
          refine ⟨ih hj, ?_⟩
          intro hdel
          exact Finset.disjoint_left.1
            (buildAdded_disjoint_buildDeleted ω K hsize (by omega : j ≠ n)) hxj hdel
        · exact Or.inr hxj

lemma future_buildDeleted_not_mem
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n j x : ℕ} (hnj : n ≤ j) (hxlt : x < Z (targetStage n)) :
    x ∉ buildDeleted ω K j := by
  intro hx
  have hxblock : x ∈ zBlock (targetStage j) :=
    stageDeleted_mem_zBlock (hsize j) hx
  have hxlow := (mem_zBlock.1 hxblock).1
  have hstage : targetStage n ≤ targetStage j := targetStage_strictMono.monotone hnj
  have hZ := Z_mono hstage
  omega

lemma future_buildAdded_not_mem
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n j x : ℕ} (hnj : n ≤ j) (hxlt : x < Z (targetStage n)) :
    x ∉ buildAdded ω K j := by
  intro hx
  have hxblock : x ∈ zBlock (targetStage j) :=
    stageAdded_mem_zBlock (hsize j) hx
  have hxlow := (mem_zBlock.1 hxblock).1
  have hstage : targetStage n ≤ targetStage j := targetStage_strictMono.monotone hnj
  have hZ := Z_mono hstage
  omega

lemma mem_finalDeleted_iff_state
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n x : ℕ} (hxlt : x < Z (targetStage n)) :
    x ∈ finalDeleted ω K ↔ x ∈ (denseBuildState ω K n).deleted := by
  constructor
  · rintro ⟨j, hxj⟩
    by_cases hj : j < n
    · exact mem_denseBuildState_deleted_iff.2 ⟨j, hj, hxj⟩
    · exact False.elim
        ((future_buildDeleted_not_mem ω K hsize (Nat.le_of_not_gt hj) hxlt) hxj)
  · intro hx
    obtain ⟨j, hj, hxj⟩ := mem_denseBuildState_deleted_iff.1 hx
    exact ⟨j, hxj⟩

lemma mem_finalAdded_iff_state
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n x : ℕ} (hxlt : x < Z (targetStage n)) :
    x ∈ finalAdded ω K ↔ x ∈ (denseBuildState ω K n).added := by
  constructor
  · rintro ⟨j, hxj⟩
    by_cases hj : j < n
    · exact (mem_denseBuildState_added_iff ω K hsize).2 ⟨j, hj, hxj⟩
    · exact False.elim
        ((future_buildAdded_not_mem ω K hsize (Nat.le_of_not_gt hj) hxlt) hxj)
  · intro hx
    obtain ⟨j, hj, hxj⟩ :=
      (mem_denseBuildState_added_iff ω K hsize).1 hx
    exact ⟨j, hxj⟩

lemma mem_denseFinalSet_iff_state
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {n x : ℕ} (hxlt : x < Z (targetStage n)) :
    x ∈ denseFinalSet ω K ↔ x ∈ (denseBuildState ω K n).currentSet ω := by
  rw [denseFinalSet, DenseBuildState.currentSet]
  simp only [Set.mem_union, Set.mem_diff, Finset.mem_coe]
  rw [mem_finalDeleted_iff_state ω K hsize hxlt,
    mem_finalAdded_iff_state ω K hsize hxlt]

lemma target_lt_next_stage
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    (hsize : targetSizeCondition ω K k s)
    (p : StagePattern ω K k s) :
    stageTarget ω K k s p < Z (targetStage (k + 1)) := by
  have hb := (mem_targetInterval.1
    ((stageTarget_spec ω K k s hsize).2.1 p)).2
  have hstage : targetStage k + 1 ≤ targetStage (k + 1) := by
    unfold targetStage
    omega
  calc
    stageTarget ω K k s p < 30 * Z (targetStage k) := hb
    _ < Z (targetStage k + 1) := by
      rw [Z_succ]
      have := Z_pos (targetStage k)
      omega
    _ ≤ Z (targetStage (k + 1)) := Z_mono hstage

lemma finalTarget_representation_hits_transversal
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    (k : ℕ)
    (p : StagePattern ω K k (denseBuildState ω K k))
    {r : ℕ × ℕ}
    (hr : r ∈ unordRepr (denseFinalSet ω K)
      (stageTarget ω K k (denseBuildState ω K k) p)) :
    r.1 ∈ patternTransversal ω K k (denseBuildState ω K k) p ∨
      r.2 ∈ patternTransversal ω K k (denseBuildState ω K k) p := by
  let s := denseBuildState ω K k
  have hb := target_lt_next_stage (hsize k) p
  have hr' := mem_unordRepr.1 hr
  have hr1lt : r.1 < Z (targetStage (k + 1)) := by omega
  have hr2lt : r.2 < Z (targetStage (k + 1)) := by omega
  have hr1state := (mem_denseFinalSet_iff_state ω K hsize hr1lt).1 hr'.2.1
  have hr2state := (mem_denseFinalSet_iff_state ω K hsize hr2lt).1 hr'.2.2.1
  have hrstep : r ∈ unordRepr
      ((denseStageStep ω K k s).currentSet ω)
      (stageTarget ω K k s p) := by
    apply mem_unordRepr.2
    simpa [s] using ⟨hr'.1, hr1state, hr2state, hr'.2.2.2⟩
  exact stageTarget_representation_hits_transversal (hsize k) p hrstep

noncomputable def pairsKilledBy
    (ω : DenseSample) (m : ℕ) (E : Finset ℕ) :
    Finset (strictReprIndices (m / 3) m) :=
  (densePresentPairs (m / 3) m ω).filter
    (fun i ↦ (i : ℕ) ∈ E ∨ m - (i : ℕ) ∈ E)

lemma mem_pairsKilledBy {ω : DenseSample} {m : ℕ} {E : Finset ℕ}
    {i : strictReprIndices (m / 3) m} :
    i ∈ pairsKilledBy ω m E ↔
      i ∈ densePresentPairs (m / 3) m ω ∧
        ((i : ℕ) ∈ E ∨ m - (i : ℕ) ∈ E) := by
  classical
  simp [pairsKilledBy]

noncomputable def deletionBaseCandidates
    (ω : DenseSample) (s : DenseBuildState) (b m : ℕ) : Finset ℕ :=
  by
    classical
    exact (oldHighEndpoints ω s b).filter fun d ↦
      d ∈ denseReservoirSet ω ∧ d ≤ m ∧ m - d ∈ denseReservoirSet ω

lemma mem_deletionBaseCandidates
    {ω : DenseSample} {s : DenseBuildState} {b m d : ℕ} :
    d ∈ deletionBaseCandidates ω s b m ↔
      d ∈ oldHighEndpoints ω s b ∧
        d ∈ denseReservoirSet ω ∧ d ≤ m ∧ m - d ∈ denseReservoirSet ω := by
  classical
  simp [deletionBaseCandidates]

lemma pairsKilledBy_oldHigh_card_le
    (ω : DenseSample) (s : DenseBuildState) (b m : ℕ) :
    (pairsKilledBy ω m (oldHighEndpoints ω s b)).card ≤
      2 * (deletionBaseCandidates ω s b m).card := by
  classical
  let L : Finset (strictReprIndices (m / 3) m) :=
    (densePresentPairs (m / 3) m ω).filter
      (fun i : strictReprIndices (m / 3) m ↦
        (i : ℕ) ∈ oldHighEndpoints ω s b)
  let H : Finset (strictReprIndices (m / 3) m) :=
    (densePresentPairs (m / 3) m ω).filter
      (fun i : strictReprIndices (m / 3) m ↦
        m - (i : ℕ) ∈ oldHighEndpoints ω s b)
  have hsub : pairsKilledBy ω m (oldHighEndpoints ω s b) ⊆ L ∪ H := by
    intro i hi
    have hi' := mem_pairsKilledBy.1 hi
    rcases hi'.2 with hlo | hhi
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hi'.1, hlo⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hi'.1, hhi⟩))
  have hL : L.card ≤ (deletionBaseCandidates ω s b m).card := by
    apply Finset.card_le_card_of_injOn (fun i : strictReprIndices (m / 3) m ↦ (i : ℕ))
    · intro i hi
      have hi' := Finset.mem_filter.1 hi
      have hp := mem_densePresentPairs.1 hi'.1
      have him : (i : ℕ) ≤ m := by
        have hii := Finset.mem_filter.1 i.property
        exact (Finset.mem_Icc.1 hii.1).2
      exact mem_deletionBaseCandidates.2
        ⟨hi'.2, hp.1, him, hp.2⟩
    · intro i hi j hj hij
      exact Subtype.ext hij
  have hH : H.card ≤ (deletionBaseCandidates ω s b m).card := by
    apply Finset.card_le_card_of_injOn
      (fun i : strictReprIndices (m / 3) m ↦ m - (i : ℕ))
    · intro i hi
      have hi' := Finset.mem_filter.1 hi
      have hp := mem_densePresentPairs.1 hi'.1
      have him : (i : ℕ) ≤ m := by
        have hii := Finset.mem_filter.1 i.property
        exact (Finset.mem_Icc.1 hii.1).2
      apply mem_deletionBaseCandidates.2
      refine ⟨hi'.2, hp.2, Nat.sub_le _ _, ?_⟩
      rw [Nat.sub_sub_self him]
      change denseBit (i : ℕ) ω = true
      exact hp.1
    · intro i hi j hj hij
      apply Subtype.ext
      have hii := Finset.mem_filter.1 i.property
      have hjj := Finset.mem_filter.1 j.property
      have him := (Finset.mem_Icc.1 hii.1).2
      have hjm := (Finset.mem_Icc.1 hjj.1).2
      change m - (i : ℕ) = m - (j : ℕ) at hij
      omega
  calc
    (pairsKilledBy ω m (oldHighEndpoints ω s b)).card ≤ (L ∪ H).card :=
      Finset.card_le_card hsub
    _ ≤ L.card + H.card := Finset.card_union_le _ _
    _ ≤ (deletionBaseCandidates ω s b m).card +
        (deletionBaseCandidates ω s b m).card := Nat.add_le_add hL hH
    _ = 2 * (deletionBaseCandidates ω s b m).card := by omega

lemma deletionBaseCandidates_subset_centers_union_added
    (ω : DenseSample) (s : DenseBuildState) (b m : ℕ) :
    deletionBaseCandidates ω s b m ⊆
      denseGlobalCommonCenters b m ω ∪ s.added.image (fun a ↦ b - a) := by
  classical
  intro d hd
  have hd' := mem_deletionBaseCandidates.1 hd
  obtain ⟨p, hp, hpd⟩ := mem_oldHighEndpoints.1 hd'.1
  subst d
  have hp' := mem_unordRepr.1 hp
  have hp1eq : p.1 = b - p.2 := by omega
  rcases hp'.2.1 with hp1R | hp1add
  · apply Finset.mem_union.2 (Or.inl ?_)
    rw [mem_denseGlobalCommonCenters]
    refine ⟨⟨by omega, hd'.2.2.1⟩, ?_⟩
    intro j
    fin_cases j
    · simpa [tripleEndpoint, denseReservoirSet] using hd'.2.1
    · simpa [tripleEndpoint, hp1eq, denseReservoirSet] using hp1R.1
    · simpa [tripleEndpoint, denseReservoirSet] using hd'.2.2.2
  · apply Finset.mem_union.2 (Or.inr ?_)
    exact Finset.mem_image.2 ⟨p.1, hp1add, by simp [hp1eq]; omega⟩

lemma deletionBaseCandidates_card_le
    (ω : DenseSample) (s : DenseBuildState) (b m : ℕ) :
    (deletionBaseCandidates ω s b m).card ≤
      (denseGlobalCommonCenters b m ω).card + s.added.card := by
  calc
    (deletionBaseCandidates ω s b m).card ≤
        (denseGlobalCommonCenters b m ω ∪
          s.added.image (fun a ↦ b - a)).card :=
      Finset.card_le_card (deletionBaseCandidates_subset_centers_union_added ω s b m)
    _ ≤ (denseGlobalCommonCenters b m ω).card +
        (s.added.image (fun a ↦ b - a)).card := Finset.card_union_le _ _
    _ ≤ (denseGlobalCommonCenters b m ω).card + s.added.card :=
      Nat.add_le_add_left Finset.card_image_le _

lemma pairsKilledBy_stageDeleted_card_le
    (ω : DenseSample) (K k : ℕ) (s : DenseBuildState) (m : ℕ)
    (hnotTarget : m ∉ stageTargets ω K k s)
    (hcollision : ∀ b ∈ stageTargets ω K k s, b ≠ m →
      (denseGlobalCommonCenters b m ω).card < 182) :
    (pairsKilledBy ω m (stageDeleted ω K k s)).card ≤
      (stageTargets ω K k s).card * (2 * (181 + s.added.card)) := by
  classical
  have hsub : pairsKilledBy ω m (stageDeleted ω K k s) ⊆
      (stageTargets ω K k s).biUnion
        (fun b ↦ pairsKilledBy ω m (oldHighEndpoints ω s b)) := by
    intro i hi
    have hi' := mem_pairsKilledBy.1 hi
    rcases hi'.2 with hlo | hhi
    · obtain ⟨b, hb, p, hp, hpd⟩ := mem_stageDeleted.1 hlo
      apply Finset.mem_biUnion.2
      exact ⟨b, hb, mem_pairsKilledBy.2 ⟨hi'.1, Or.inl (hpd ▸
        (mem_oldHighEndpoints.2 ⟨p, hp, rfl⟩))⟩⟩
    · obtain ⟨b, hb, p, hp, hpd⟩ := mem_stageDeleted.1 hhi
      apply Finset.mem_biUnion.2
      exact ⟨b, hb, mem_pairsKilledBy.2 ⟨hi'.1, Or.inr (hpd ▸
        (mem_oldHighEndpoints.2 ⟨p, hp, rfl⟩))⟩⟩
  calc
    (pairsKilledBy ω m (stageDeleted ω K k s)).card ≤
        ((stageTargets ω K k s).biUnion
          (fun b ↦ pairsKilledBy ω m (oldHighEndpoints ω s b))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ stageTargets ω K k s,
        (pairsKilledBy ω m (oldHighEndpoints ω s b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ stageTargets ω K k s, 2 * (181 + s.added.card) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbm : b ≠ m := by
        intro h
        subst b
        exact hnotTarget hb
      calc
        (pairsKilledBy ω m (oldHighEndpoints ω s b)).card ≤
            2 * (deletionBaseCandidates ω s b m).card :=
          pairsKilledBy_oldHigh_card_le ω s b m
        _ ≤ 2 * ((denseGlobalCommonCenters b m ω).card + s.added.card) :=
          Nat.mul_le_mul_left 2 (deletionBaseCandidates_card_le ω s b m)
        _ ≤ 2 * (181 + s.added.card) := by
          gcongr
          exact Nat.le_pred_of_lt (hcollision b hb hbm)
    _ = (stageTargets ω K k s).card * (2 * (181 + s.added.card)) := by simp

lemma strictPair_endpoint_bounds
    {k m : ℕ} (hm : m ∈ zBlock k)
    (i : strictReprIndices (m / 3) m) :
    m / 3 ≤ (i : ℕ) ∧ m / 3 ≤ m - (i : ℕ) ∧
      (i : ℕ) < Z (k + 1) ∧ m - (i : ℕ) < Z (k + 1) := by
  have hi := Finset.mem_filter.1 i.property
  have him := (Finset.mem_Icc.1 hi.1).2
  have hilow := (Finset.mem_Icc.1 hi.1).1
  have histrict := hi.2
  have hmhi := (mem_zBlock.1 hm).2
  constructor
  · exact hilow
  constructor
  · omega
  constructor
  · exact him.trans_lt hmhi
  · exact (Nat.sub_le m i).trans_lt hmhi

lemma deletion_stage_eq_block_of_endpoint
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {j k m : ℕ} (hm : m ∈ zBlock k)
    (i : strictReprIndices (m / 3) m)
    (hj : (i : ℕ) ∈ buildDeleted ω K j ∨
      m - (i : ℕ) ∈ buildDeleted ω K j) :
    targetStage j = k := by
  let d := if (i : ℕ) ∈ buildDeleted ω K j then (i : ℕ) else m - (i : ℕ)
  have hd : d ∈ buildDeleted ω K j := by
    dsimp [d]
    split_ifs with h
    · exact h
    · exact hj.resolve_left h
  have hdb := stageDeleted_bounds (hsize j) hd
  have hib := strictPair_endpoint_bounds hm i
  have hdlow : m / 3 ≤ d := by
    dsimp [d]
    split_ifs
    · exact hib.1
    · exact hib.2.1
  have hdhigh : d < Z (k + 1) := by
    dsimp [d]
    split_ifs
    · exact hib.2.2.1
    · exact hib.2.2.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with ht | ht
  · have ht' : targetStage j + 1 ≤ k := Nat.succ_le_iff.2 ht
    have hZ : Z (targetStage j + 1) ≤ Z k := Z_mono ht'
    rw [Z_succ] at hZ
    have hmlo := (mem_zBlock.1 hm).1
    have hz := Z_pos (targetStage j)
    omega
  · have hk' : k + 1 ≤ targetStage j := Nat.succ_le_iff.2 ht
    have hZ : Z (k + 1) ≤ Z (targetStage j) := Z_mono hk'
    omega

lemma pairsKilledBy_state_subset_matching_stage
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {j k m : ℕ} (hj : j < k) (ht : targetStage j = k)
    (hm : m ∈ zBlock k) :
    pairsKilledBy ω m (denseBuildState ω K k).deleted ⊆
      pairsKilledBy ω m (buildDeleted ω K j) := by
  intro i hi
  have hi' := mem_pairsKilledBy.1 hi
  rcases hi'.2 with hlo | hhi
  · obtain ⟨j', hj'k, hdj'⟩ := mem_denseBuildState_deleted_iff.1 hlo
    have ht' := deletion_stage_eq_block_of_endpoint ω K hsize hm i (Or.inl hdj')
    have hj'eq : j' = j := targetStage_strictMono.injective (ht'.trans ht.symm)
    subst j'
    exact mem_pairsKilledBy.2 ⟨hi'.1, Or.inl hdj'⟩
  · obtain ⟨j', hj'k, hdj'⟩ := mem_denseBuildState_deleted_iff.1 hhi
    have ht' := deletion_stage_eq_block_of_endpoint ω K hsize hm i (Or.inr hdj')
    have hj'eq : j' = j := targetStage_strictMono.injective (ht'.trans ht.symm)
    subst j'
    exact mem_pairsKilledBy.2 ⟨hi'.1, Or.inr hdj'⟩

lemma pairsKilledBy_state_empty_of_no_matching_stage
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k m : ℕ} (hm : m ∈ zBlock k)
    (hnone : ¬∃ j < k, targetStage j = k) :
    pairsKilledBy ω m (denseBuildState ω K k).deleted = ∅ := by
  ext i
  constructor
  · intro hi
    exfalso
    have hi' := mem_pairsKilledBy.1 hi
    rcases hi'.2 with hlo | hhi
    · obtain ⟨j, hj, hd⟩ := mem_denseBuildState_deleted_iff.1 hlo
      exact hnone ⟨j, hj,
        deletion_stage_eq_block_of_endpoint ω K hsize hm i (Or.inl hd)⟩
    · obtain ⟨j, hj, hd⟩ := mem_denseBuildState_deleted_iff.1 hhi
      exact hnone ⟨j, hj,
        deletion_stage_eq_block_of_endpoint ω K hsize hm i (Or.inr hd)⟩
  · simp

lemma densePresentPairs_card_le_available_add_killed
    (ω : DenseSample) (s : DenseBuildState) (m : ℕ) :
    (densePresentPairs (m / 3) m ω).card ≤
      (availableDensePairs ω s m).card +
        (pairsKilledBy ω m s.deleted).card := by
  classical
  have hsub : densePresentPairs (m / 3) m ω ⊆
      availableDensePairs ω s m ∪ pairsKilledBy ω m s.deleted := by
    intro i hi
    by_cases hlo : (i : ℕ) ∈ s.deleted
    · exact Finset.mem_union.2 (Or.inr
        (mem_pairsKilledBy.2 ⟨hi, Or.inl hlo⟩))
    · by_cases hhi : m - (i : ℕ) ∈ s.deleted
      · exact Finset.mem_union.2 (Or.inr
          (mem_pairsKilledBy.2 ⟨hi, Or.inr hhi⟩))
      · exact Finset.mem_union.2 (Or.inl
          (mem_availableDensePairs.2 ⟨hi, hlo, hhi⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma matched_stage_loss_le_two_pow
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    {j k m : ℕ} (hkK : K ≤ k) (hj : j < k) (ht : targetStage j = k)
    (hm : m ∈ zBlock k) (hmnot : m ∉ (denseBuildState ω K k).targets) :
    (pairsKilledBy ω m (denseBuildState ω K k).deleted).card ≤
      2 ^ (24 * (j + 1)) := by
  let s := denseBuildState ω K j
  have hnotStage : m ∉ stageTargets ω K j s := by
    intro hmj
    exact hmnot (mem_denseBuildState_targets_iff.2 ⟨j, hj, by simpa [s, buildTargets]⟩)
  have hcoll : ∀ b ∈ stageTargets ω K j s, b ≠ m →
      (denseGlobalCommonCenters b m ω).card < 182 := by
    intro b hb hbm
    have hbblock : b ∈ zBlock k := by
      rw [← ht]
      exact stageTargets_mem_zBlock (hsize j) hb
    exact hcollision k hkK b hbblock m hm hbm
  have hstage := pairsKilledBy_stageDeleted_card_le ω K j s m hnotStage hcoll
  have hsub := Finset.card_le_card
    (pairsKilledBy_state_subset_matching_stage ω K hsize hj ht hm)
  have hraw :
      (pairsKilledBy ω m (denseBuildState ω K k).deleted).card ≤
        (stageTargets ω K j s).card * (2 * (181 + s.added.card)) :=
    hsub.trans hstage
  let u := j + 1
  have htargets : (stageTargets ω K j s).card ≤ 2 ^ (10 * u) := by
    simpa [u, s] using stageTargets_card_le_two_pow ω K j s
  have hadd : s.added.card ≤ 2 ^ (12 * u) := by
    have h := denseBuildState_added_card_le ω K j
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [u]; omega))
  have h181 : 181 ≤ 2 ^ (12 * u) := by
    have hu : 1 ≤ u := by dsimp [u]; omega
    calc
      181 ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ (12 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    (pairsKilledBy ω m (denseBuildState ω K k).deleted).card ≤
        (stageTargets ω K j s).card * (2 * (181 + s.added.card)) := hraw
    _ ≤ 2 ^ (10 * u) * (2 * (2 ^ (12 * u) + 2 ^ (12 * u))) := by
      exact Nat.mul_le_mul htargets (Nat.mul_le_mul_left 2 (Nat.add_le_add h181 hadd))
    _ = 2 ^ (22 * u + 2) := by
      calc
        2 ^ (10 * u) * (2 * (2 ^ (12 * u) + 2 ^ (12 * u))) =
            2 ^ (10 * u) * (2 ^ 2 * 2 ^ (12 * u)) := by
          congr 1
          have hp : 2 ^ (12 * u) + 2 ^ (12 * u) = 2 * 2 ^ (12 * u) := by omega
          rw [hp]
          norm_num
          ring
        _ = 2 ^ (22 * u + 2) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
    _ ≤ 2 ^ (24 * u) := Nat.pow_le_pow_right (by decide) (by
      dsimp [u]
      omega)

lemma targetStage_succ_le_two_pow (j : ℕ) :
    targetStage j + 1 ≤ 2 ^ (24 * (j + 1)) := by
  let u := j + 1
  have hu : u ≤ 2 ^ u := nat_le_two_pow u
  have hu1 : 1 ≤ u := by dsimp [u]; omega
  calc
    targetStage j + 1 = 1000 * u + 1 := rfl
    _ ≤ 2 ^ 11 * 2 ^ u := by
      norm_num
      have hp : 0 < 2 ^ u := pow_pos (by decide) _
      omega
    _ = 2 ^ (u + 11) := by rw [← pow_add]; congr 1 <;> omega
    _ ≤ 2 ^ (24 * u) := Nat.pow_le_pow_right (by decide) (by omega)

lemma linear_block_room {k : ℕ} (hk : 10 ≤ k) :
    (k + 1 : ℝ) < (4 : ℝ) ^ k / 40 := by
  have hlin : k + 1 ≤ 2 ^ (k + 1) := nat_le_two_pow (k + 1)
  have hpow : 40 * 2 ^ (k + 1) < (4 : ℕ) ^ k := by
    calc
      40 * 2 ^ (k + 1) < 2 ^ 6 * 2 ^ (k + 1) := by
        have hp : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
        norm_num
      _ = 2 ^ (k + 7) := by rw [← pow_add]; congr 1 <;> omega
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 4 ^ k := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
  have hnat : 40 * (k + 1) < (4 : ℕ) ^ k :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 40 hlin) hpow
  have hreal : (40 : ℝ) * (k + 1 : ℝ) < (4 : ℝ) ^ k := by
    exact_mod_cast hnat
  nlinarith

lemma matched_sum_le_power (j : ℕ) :
    2 ^ (24 * (j + 1)) + (targetStage j + 1) ≤
      2 ^ (24 * (j + 1) + 1) := by
  have hlin := targetStage_succ_le_two_pow j
  calc
    2 ^ (24 * (j + 1)) + (targetStage j + 1) ≤
        2 ^ (24 * (j + 1)) + 2 ^ (24 * (j + 1)) :=
      Nat.add_le_add_left hlin _
    _ = 2 ^ (24 * (j + 1) + 1) := by
      calc
        2 ^ (24 * (j + 1)) + 2 ^ (24 * (j + 1)) =
            2 * 2 ^ (24 * (j + 1)) := by omega
        _ = 2 ^ (24 * (j + 1) + 1) := by
          conv_rhs => rw [pow_succ]
          exact Nat.mul_comm _ _

lemma matched_scaled_power_lt (j : ℕ) :
    40 * 2 ^ (24 * (j + 1) + 1) < (4 : ℕ) ^ (targetStage j) := by
  let u := j + 1
  have hu : 1 ≤ u := by dsimp [u]; omega
  calc
    40 * 2 ^ (24 * (j + 1) + 1) = 40 * 2 ^ (24 * u + 1) := rfl
    _ < 2 ^ 6 * 2 ^ (24 * u + 1) := by
      have hp : 0 < 2 ^ (24 * u + 1) := pow_pos (by decide) _
      norm_num
    _ = 2 ^ (24 * u + 7) := by rw [← pow_add]; congr 1 <;> omega
    _ ≤ 2 ^ (2000 * u) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ (targetStage j) := by
      have hexp : 2 * targetStage j = 2000 * u := by
        dsimp [targetStage, u]
        omega
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, hexp]

lemma matched_block_room_nat (j : ℕ) :
    40 * (2 ^ (24 * (j + 1)) + (targetStage j + 1)) <
      (4 : ℕ) ^ (targetStage j) :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 40 (matched_sum_le_power j))
    (matched_scaled_power_lt j)

lemma matched_block_room (j : ℕ) :
    ((2 ^ (24 * (j + 1)) + (targetStage j + 1) : ℕ) : ℝ) <
      (4 : ℝ) ^ (targetStage j) / 40 := by
  have hreal : (40 : ℝ) *
      (2 ^ (24 * (j + 1)) + (targetStage j + 1) : ℕ) <
      (4 : ℝ) ^ (targetStage j) := by
    exact_mod_cast matched_block_room_nat j
  nlinarith

lemma natCast_le_natCast_of_le {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  exact_mod_cast h

lemma nat_lt_of_natCast_lt {a b : ℕ} (h : (a : ℝ) < (b : ℝ)) : a < b := by
  exact_mod_cast h

lemma available_card_of_real_loss_room {present available loss quota : ℕ}
    (hdecomp : present ≤ available + loss)
    (hroom : ((loss + quota : ℕ) : ℝ) < (present : ℝ)) :
    quota ≤ available := by
  have hnat : loss + quota < present := nat_lt_of_natCast_lt hroom
  omega

lemma stageCanary_available_pairs
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k m : ℕ} (hm : m ∈ buildCanaries ω K k) :
    k + 1 ≤ (availableDensePairs ω (denseBuildState ω K k) m).card := by
  have hm' := mem_stageCanaries.1 hm
  have hkK := hm'.1
  have hmblock := hm'.2.1
  have hmnot := hm'.2.2
  have hpresent := hpair k hkK m hmblock

  have hdecomp := densePresentPairs_card_le_available_add_killed
    ω (denseBuildState ω K k) m
  by_cases hmatch : ∃ j < k, targetStage j = k
  · obtain ⟨j, hj, ht⟩ := hmatch
    have hloss := matched_stage_loss_le_two_pow ω K hsize hcollision
      hkK hj ht hmblock hmnot
    have hroom :
        (((2 ^ (24 * (j + 1)) + (k + 1) : ℕ) : ℝ)) <
          (4 : ℝ) ^ k / 40 := by
      have h := matched_block_room j
      rw [ht] at h
      exact h
    have hleNat :
        (pairsKilledBy ω m (denseBuildState ω K k).deleted).card + (k + 1) ≤
          2 ^ (24 * (j + 1)) + (k + 1) := Nat.add_le_add_right hloss _
    have hleReal := natCast_le_natCast_of_le hleNat
    have hltReal :
        (((pairsKilledBy ω m (denseBuildState ω K k).deleted).card +
          (k + 1) : ℕ) : ℝ) <
            ((densePresentPairs (m / 3) m ω).card : ℝ) :=
      hleReal.trans_lt (hroom.trans hpresent)
    exact available_card_of_real_loss_room hdecomp hltReal
  · have hk10 : 10 ≤ k := hK.trans hkK
    have hroom := linear_block_room hk10
    have hkill :
        pairsKilledBy ω m (denseBuildState ω K k).deleted = ∅ :=
      pairsKilledBy_state_empty_of_no_matching_stage ω K hsize hmblock hmatch
    have hltReal : (k + 1 : ℝ) <
        ((densePresentPairs (m / 3) m ω).card : ℝ) := hroom.trans hpresent
    rw [hkill] at hdecomp
    simp only [Finset.card_empty, add_zero] at hdecomp
    have hroom0 : (((0 : ℕ) + (k + 1) : ℕ) : ℝ) <
        ((densePresentPairs (m / 3) m ω).card : ℝ) := by simpa using hltReal
    exact available_card_of_real_loss_room hdecomp hroom0

lemma buildCanary_chosenPairs_card
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k m : ℕ} (hm : m ∈ buildCanaries ω K k) :
    (chosenDensePairs ω (denseBuildState ω K k) k m).card = k + 1 :=
  chosenDensePairs_card _ _ _ _
    (stageCanary_available_pairs ω K hK hpair hcollision hsize hm)

lemma chosenDensePair_endpoint_mem_final
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k c : ℕ} (hc : c ∈ buildCanaries ω K k)
    (i : ChosenPairType ω (denseBuildState ω K k) k c) (b : Bool) :
    chosenPairEndpoint
        (i : strictReprIndices (c / 3) c) b ∈ denseFinalSet ω K := by
  have hiavail := chosenDensePairs_subset_available
    ω (denseBuildState ω K k) k c i.property
  have hi := mem_availableDensePairs.1 hiavail
  have hpresent := mem_densePresentPairs.1 hi.1
  have hcblock := (mem_stageCanaries.1 hc).2.1
  have hclt := (mem_zBlock.1 hcblock).2
  have hi_le_c : (i : ℕ) ≤ c := by
    exact Finset.mem_Icc.1
      (Finset.mem_filter.1
        ((i : strictReprIndices (c / 3) c).property)).1 |>.2
  have hxlt : chosenPairEndpoint
      (i : strictReprIndices (c / 3) c) b < Z (k + 1) := by
    cases b with
    | false =>
        simpa [chosenPairEndpoint] using
          (show (i : ℕ) < Z (k + 1) from hi_le_c.trans_lt hclt)
    | true =>
        simpa [chosenPairEndpoint] using
          (show c - (i : ℕ) < Z (k + 1) from (Nat.sub_le c i).trans_lt hclt)
  have hsource : k + 1 ≤ targetStage k := source_succ_le_targetStage k
  have hxltTarget : chosenPairEndpoint
      (i : strictReprIndices (c / 3) c) b < Z (targetStage k) :=
    hxlt.trans_le (Z_mono hsource)
  rw [denseFinalSet]
  left
  constructor
  · cases b with
    | false => simpa [chosenPairEndpoint, denseReservoirSet] using hpresent.1
    | true => simpa [chosenPairEndpoint, denseReservoirSet] using hpresent.2
  · intro hdeleted
    have hstate := (mem_finalDeleted_iff_state ω K hsize hxltTarget).1 hdeleted
    cases b with
    | false => simpa [chosenPairEndpoint] using hi.2.1 hstate
    | true => simpa [chosenPairEndpoint] using hi.2.2 hstate

lemma patternTransversal_subset_denseFinalSet
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k : ℕ}
    (p : StagePattern ω K k (denseBuildState ω K k)) :
    (patternTransversal ω K k (denseBuildState ω K k) p : Set ℕ) ⊆
      denseFinalSet ω K := by
  intro x hx
  obtain ⟨i, _hiomit, rfl⟩ := mem_patternTransversal.1 hx
  exact chosenDensePair_endpoint_mem_final ω K hsize p.1.property i (p.2.2 i)

lemma patternComplement_mem_finalAdded
    (ω : DenseSample) (K : ℕ) {k : ℕ}
    (p : StagePattern ω K k (denseBuildState ω K k))
    {x : ℕ} (hx : x ∈ patternTransversal ω K k (denseBuildState ω K k) p) :
    stageTarget ω K k (denseBuildState ω K k) p - x ∈ finalAdded ω K := by
  refine ⟨k, ?_⟩
  exact mem_stageAdded.2 ⟨p, x, hx, rfl⟩

lemma patternComplement_mem_denseFinalSet
    (ω : DenseSample) (K : ℕ) {k : ℕ}
    (p : StagePattern ω K k (denseBuildState ω K k))
    {x : ℕ} (hx : x ∈ patternTransversal ω K k (denseBuildState ω K k) p) :
    stageTarget ω K k (denseBuildState ω K k) p - x ∈
      denseFinalSet ω K := by
  rw [denseFinalSet]
  exact Or.inr (patternComplement_mem_finalAdded ω K p hx)

lemma strictPair_mem_unordRepr
    {D : Set ℕ} {c : ℕ} (i : strictReprIndices (c / 3) c)
    (hlo : (i : ℕ) ∈ D) (hhi : c - (i : ℕ) ∈ D) :
    presentPairToUnord c i ∈ unordRepr D c := by
  have hstrict : 2 * (i : ℕ) < c := (Finset.mem_filter.1 i.property).2
  have hic : (i : ℕ) ≤ c := by omega
  rw [mem_unordRepr]
  change (i : ℕ) ≤ c - (i : ℕ) ∧ (i : ℕ) ∈ D ∧
    c - (i : ℕ) ∈ D ∧ (i : ℕ) + (c - (i : ℕ)) = c
  exact ⟨by omega, hlo, hhi, Nat.add_sub_of_le hic⟩

lemma fullChosenPair_unique
    {ω : DenseSample} {k c : ℕ} {D : Set ℕ}
    {s : DenseBuildState}
    (hone : (unordRepr D c).card ≤ 1)
    (i j : ChosenPairType ω s k c)
    (hi : (i : ℕ) ∈ D ∧ c - (i : ℕ) ∈ D)
    (hj : (j : ℕ) ∈ D ∧ c - (j : ℕ) ∈ D) :
    i = j := by
  have hip := strictPair_mem_unordRepr
    (i : strictReprIndices (c / 3) c) hi.1 hi.2
  have hjp := strictPair_mem_unordRepr
    (j : strictReprIndices (c / 3) c) hj.1 hj.2
  have hpairs : presentPairToUnord c (i : ℕ) =
      presentPairToUnord c (j : ℕ) :=
    (Finset.card_le_one.mp hone) _ hip _ hjp
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Prod.fst hpairs

lemma exists_omitted_chosenPair
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {D : Set ℕ} {k c : ℕ} (hc : c ∈ buildCanaries ω K k)
    (hone : (unordRepr D c).card ≤ 1) :
    ∃ o : ChosenPairType ω (denseBuildState ω K k) k c,
      ∀ i : ChosenPairType ω (denseBuildState ω K k) k c,
        i ≠ o → ¬((i : ℕ) ∈ D ∧ c - (i : ℕ) ∈ D) := by
  classical
  by_cases hfull : ∃ i : ChosenPairType ω (denseBuildState ω K k) k c,
      (i : ℕ) ∈ D ∧ c - (i : ℕ) ∈ D
  · obtain ⟨o, ho⟩ := hfull
    refine ⟨o, ?_⟩
    intro i hio hi
    exact hio (fullChosenPair_unique hone i o hi ho)
  · have hcard := buildCanary_chosenPairs_card
      ω K hK hpair hcollision hsize hc
    have hne : (chosenDensePairs ω (denseBuildState ω K k) k c).Nonempty :=
      Finset.card_pos.1 (by rw [hcard]; omega)
    obtain ⟨o, ho⟩ := hne
    refine ⟨⟨o, ho⟩, ?_⟩
    intro i _hio hi
    exact hfull ⟨i, hi⟩

lemma dense_canary_trap
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    (D : Set ℕ) (_hDA : D ⊆ denseFinalSet ω K)
    (k c : ℕ) (hc : c ∈ finalCanaryBlocks ω K k)
    (hone : (unordRepr D c).card ≤ 1) :
    ∃ b ∈ finalTargetBlocks ω K (k + 10), c ≤ b ∧ b ∉ 2 • D := by
  classical
  let s := denseBuildState ω K k
  obtain ⟨o, ho⟩ := exists_omitted_chosenPair
    ω K hK hpair hcollision hsize hc hone
  have hendpoint : ∀ i : ChosenPairType ω s k c, i ≠ o →
      ∃ e : Bool,
        chosenPairEndpoint (i : strictReprIndices (c / 3) c) e ∉ D := by
    intro i hio
    have hnot := ho i hio
    by_cases hlo : (i : ℕ) ∈ D
    · refine ⟨true, ?_⟩
      simpa [chosenPairEndpoint] using (fun hhi ↦ hnot ⟨hlo, hhi⟩)
    · exact ⟨false, by simpa [chosenPairEndpoint] using hlo⟩
  let choice : ChosenPairType ω s k c → Bool := fun i ↦
    if h : i = o then false else Classical.choose (hendpoint i h)
  have hchoice : ∀ i : ChosenPairType ω s k c, i ≠ o →
      chosenPairEndpoint (i : strictReprIndices (c / 3) c) (choice i) ∉ D := by
    intro i hio
    rw [show choice i = Classical.choose (hendpoint i hio) by simp [choice, hio]]
    exact Classical.choose_spec (hendpoint i hio)
  let p : StagePattern ω K k s := ⟨⟨c, hc⟩, ⟨o, choice⟩⟩
  let b := stageTarget ω K k s p
  have hbtarget : b ∈ buildTargets ω K k := by
    exact mem_stageTargets.2 ⟨p, rfl⟩
  have hcb : c ≤ b := by
    have hcblock := (mem_stageCanaries.1 hc).2.1
    have hclt := (mem_zBlock.1 hcblock).2
    have hZmono := Z_mono (source_succ_le_targetStage k)
    have hbI := (stageTarget_spec ω K k s (hsize k)).2.1 p
    have hblow := (mem_targetInterval.1 hbI).1
    have hzpos := Z_pos (targetStage k)
    dsimp [b]
    omega
  have htransOutside : ∀ x ∈ patternTransversal ω K k s p, x ∉ D := by
    intro x hx
    obtain ⟨i, hio, hix⟩ := mem_patternTransversal.1 hx
    have hout := hchoice i hio
    simpa [p] using hix ▸ hout
  have hbmiss : b ∉ 2 • D := by
    intro hbD
    have hbDD : b ∈ D + D := by simpa [two_nsmul] using hbD
    obtain ⟨x, hxD, y, hyD, hxy⟩ := hbDD
    by_cases hxyord : x ≤ y
    · have hr : (x, y) ∈ unordRepr (denseFinalSet ω K) b := by
        rw [mem_unordRepr]
        exact ⟨hxyord, _hDA hxD, _hDA hyD, hxy⟩
      rcases finalTarget_representation_hits_transversal ω K hsize k p hr with hx | hy
      · exact htransOutside x hx hxD
      · exact htransOutside y hy hyD
    · have hyx : y ≤ x := Nat.le_of_not_ge hxyord
      have hr : (y, x) ∈ unordRepr (denseFinalSet ω K) b := by
        rw [mem_unordRepr]
        exact ⟨hyx, _hDA hyD, _hDA hxD, by simpa [add_comm] using hxy⟩
      rcases finalTarget_representation_hits_transversal ω K hsize k p hr with hy | hx
      · exact htransOutside y hy hyD
      · exact htransOutside x hx hxD
  refine ⟨b, ?_, hcb, hbmiss⟩
  simpa using hbtarget

lemma patternTransversal_bounds
    {ω : DenseSample} {K k : ℕ} {s : DenseBuildState}
    {p : StagePattern ω K k s} {x : ℕ}
    (hx : x ∈ patternTransversal ω K k s p) :
    Z k / 3 ≤ x ∧ x < Z (k + 1) := by
  obtain ⟨i, _hiomit, hix⟩ := mem_patternTransversal.1 hx
  have hcblock := (mem_stageCanaries.1 p.1.property).2.1
  have hclow := (mem_zBlock.1 hcblock).1
  have hiIcc := Finset.mem_Icc.1
    (Finset.mem_filter.1
      ((i : strictReprIndices ((p.1 : ℕ) / 3) p.1).property)).1
  have hstrict : 2 * (i : ℕ) < p.1 :=
    (Finset.mem_filter.1
      ((i : strictReprIndices ((p.1 : ℕ) / 3) p.1).property)).2
  have hendpoint : (p.1 : ℕ) / 3 ≤
      chosenPairEndpoint
        (i : strictReprIndices ((p.1 : ℕ) / 3) p.1) (p.2.2 i) := by
    cases hchoice : p.2.2 i with
    | false => simpa [chosenPairEndpoint, hchoice] using hiIcc.1
    | true =>
        simp only [chosenPairEndpoint, hchoice, Bool.true_eq, ↓reduceIte]
        omega
  constructor
  · rw [← hix]
    exact (Nat.div_le_div_right hclow).trans hendpoint
  · exact patternTransversal_lt_Z hx

lemma dense_staged_cover (ω : DenseSample) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      n ∈ stagedSet (finalTargetBlocks ω K) ∨
        n ∈ stagedSet (finalCanaryBlocks ω K) := by
  filter_upwards [Filter.eventually_ge_atTop (Z K)] with n hn
  have hn0 : n ≠ 0 := by
    have := Z_pos K
    omega
  let k := Nat.log 256 n
  have hnblock : n ∈ zBlock k := by
    rw [mem_zBlock]
    exact ⟨Nat.pow_log_le_self 256 hn0,
      by simpa [Z, k, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 256) n⟩
  have hkK : K ≤ k := by
    apply (Nat.le_log_iff_pow_le (by norm_num : 1 < 256) hn0).2
    simpa [Z] using hn
  by_cases ht : n ∈ (denseBuildState ω K k).targets
  · left
    obtain ⟨j, hjk, hj⟩ := mem_denseBuildState_targets_iff.1 ht
    exact ⟨j + 10, by simpa using hj⟩
  · right
    refine ⟨k, ?_⟩
    exact mem_stageCanaries.2 ⟨hkK, hnblock, ht⟩

lemma dense_target_summands_escape
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    (d : ℕ) (hdA : d ∈ denseFinalSet ω K) :
    ∃ N, ∀ n ≥ N, ∀ b ∈ finalTargetBlocks ω K n,
      ¬∃ a ∈ denseFinalSet ω K, d + a = b := by
  refine ⟨3 * (d + 1) + 10, ?_⟩
  intro n hn b hb
  have hn10 : 10 ≤ n := by omega
  let j := n - 10
  have hj : 3 * (d + 1) ≤ j := by
    dsimp [j]
    omega
  have hjpow : j ≤ 2 ^ j := nat_le_two_pow j
  have htwoZ : 2 ^ j ≤ Z j := by
    unfold Z
    exact Nat.pow_le_pow_left (by norm_num) j
  have hZd : 3 * (d + 1) ≤ Z j := hj.trans (hjpow.trans htwoZ)
  have hdlt : d < Z j / 3 := by omega
  have hb' : b ∈ buildTargets ω K j := by
    simpa [finalTargetBlocks, hn10, j] using hb
  obtain ⟨p, rfl⟩ := mem_stageTargets.1 hb'
  intro haexists
  obtain ⟨a, haA, hda⟩ := haexists
  let s := denseBuildState ω K j
  change d + a = stageTarget ω K j s p at hda
  have hsource : Z j ≤ Z (targetStage j) :=
    Z_mono (Nat.le_of_lt (targetStage_gt j))
  have hdltTarget : d < Z (targetStage j) := hdlt.trans_le
    ((Nat.div_le_self (Z j) 3).trans hsource)
  have hdold : d ∈ s.currentSet ω := by
    exact (mem_denseFinalSet_iff_state ω K hsize hdltTarget).1 hdA
  have hbnext : stageTarget ω K j s p < Z (targetStage (j + 1)) :=
    target_lt_next_stage (hsize j) p
  have halt : a < Z (targetStage (j + 1)) := by omega
  have hanext := (mem_denseFinalSet_iff_state ω K hsize halt).1 haA
  have hastep : a ∈ (denseStageStep ω K j s).currentSet ω := by
    simpa [s] using hanext
  rw [denseStageStep_currentSet] at hastep
  rcases hastep with haold | haadded
  · have hbI := (stageTarget_spec ω K j s (hsize j)).2.1 p
    have hblow := (mem_targetInterval.1 hbI).1
    have hdle : d ≤ a := by
      have hz := Z_pos (targetStage j)
      omega
    have hr : (d, a) ∈ unordRepr (s.currentSet ω)
        (stageTarget ω K j s p) := by
      rw [mem_unordRepr]
      exact ⟨hdle, hdold, haold.1, hda⟩
    have hadeleted : a ∈ stageDeleted ω K j s := by
      apply mem_stageDeleted.2
      refine ⟨stageTarget ω K j s p, mem_stageTargets.2 ⟨p, rfl⟩,
        (d, a), hr, rfl⟩
    exact haold.2 hadeleted
  · obtain ⟨q, x, hx, hax⟩ := stageAdded_decompose (hsize j) haadded
    have hcross := cross_stageAdded_eq_source (hsize j) hax hx hdold hda
    have hdx : d = x := hcross.2
    have hxlow := (patternTransversal_bounds hx).1
    rw [← hdx] at hxlow
    exact (Nat.not_le_of_gt hdlt) hxlow

lemma chosenDensePairs_card_le_final_unordRepr
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k c : ℕ} (hc : c ∈ buildCanaries ω K k) :
    (chosenDensePairs ω (denseBuildState ω K k) k c).card ≤
      (unordRepr (denseFinalSet ω K) c).card := by
  classical
  apply Finset.card_le_card_of_injOn
      (fun i : strictReprIndices (c / 3) c ↦ presentPairToUnord c i)
  · intro i hi
    let i' : ChosenPairType ω (denseBuildState ω K k) k c := ⟨i, hi⟩
    apply strictPair_mem_unordRepr (D := denseFinalSet ω K) i
    · simpa [i', chosenPairEndpoint] using
        chosenDensePair_endpoint_mem_final ω K hsize hc i' false
    · simpa [i', chosenPairEndpoint] using
        chosenDensePair_endpoint_mem_final ω K hsize hc i' true
  · intro i _hi j _hj hij
    exact Subtype.ext ((presentPairToUnord_injective c) hij)

lemma canary_unordRepr_lower
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k c : ℕ} (hc : c ∈ buildCanaries ω K k) :
    k + 1 ≤ (unordRepr (denseFinalSet ω K) c).card := by
  rw [← buildCanary_chosenPairs_card ω K hK hpair hcollision hsize hc]
  exact chosenDensePairs_card_le_final_unordRepr ω K hsize hc

lemma patternTransversal_card_eq_source
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k : ℕ} (p : StagePattern ω K k (denseBuildState ω K k)) :
    (patternTransversal ω K k (denseBuildState ω K k) p).card = k := by
  rw [patternTransversal_card,
    buildCanary_chosenPairs_card ω K hK hpair hcollision hsize p.1.property]
  omega

lemma patternTransversal_card_le_final_unordRepr
    (ω : DenseSample) (K : ℕ)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k : ℕ} (p : StagePattern ω K k (denseBuildState ω K k)) :
    (patternTransversal ω K k (denseBuildState ω K k) p).card ≤
      (unordRepr (denseFinalSet ω K)
        (stageTarget ω K k (denseBuildState ω K k) p)).card := by
  classical
  let s := denseBuildState ω K k
  let b := stageTarget ω K k s p
  apply Finset.card_le_card_of_injOn
      (fun x : ℕ ↦ (x, b - x))
  · intro x hx
    have hxlt := patternTransversal_lt_Z hx
    have hxTarget : x < Z (targetStage k) := hxlt.trans_le
      (Z_mono (source_succ_le_targetStage k))
    have hbI := (stageTarget_spec ω K k s (hsize k)).2.1 p
    have hblow := (mem_targetInterval.1 hbI).1
    have hxb : x ≤ b := by
      have hz := Z_pos (targetStage k)
      omega
    change (x, b - x) ∈ unordRepr (denseFinalSet ω K) b
    rw [mem_unordRepr]
    refine ⟨?_, patternTransversal_subset_denseFinalSet ω K hsize p hx,
      patternComplement_mem_denseFinalSet ω K p hx, Nat.add_sub_of_le hxb⟩
    have hz := Z_pos (targetStage k)
    omega
  · intro x _hx y _hy hxy
    exact congrArg Prod.fst hxy

lemma target_unordRepr_lower
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k : ℕ} (p : StagePattern ω K k (denseBuildState ω K k)) :
    k ≤ (unordRepr (denseFinalSet ω K)
      (stageTarget ω K k (denseBuildState ω K k) p)).card := by
  calc
    k = (patternTransversal ω K k (denseBuildState ω K k) p).card :=
      (patternTransversal_card_eq_source ω K hK hpair hcollision hsize p).symm
    _ ≤ (unordRepr (denseFinalSet ω K)
        (stageTarget ω K k (denseBuildState ω K k) p)).card :=
      patternTransversal_card_le_final_unordRepr ω K hsize p

lemma dense_block_unordRepr_lower
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j))
    {k m : ℕ} (hk : K ≤ k) (hm : m ∈ zBlock k) :
    k + 1 ≤ (unordRepr (denseFinalSet ω K) m).card ∨
      ∃ j, K ≤ j ∧ targetStage j = k ∧
        j ≤ (unordRepr (denseFinalSet ω K) m).card := by
  by_cases ht : m ∈ (denseBuildState ω K k).targets
  · obtain ⟨j, hjk, hjtarget⟩ := mem_denseBuildState_targets_iff.1 ht
    obtain ⟨p, hp⟩ := mem_stageTargets.1 hjtarget
    have hmj : m ∈ zBlock (targetStage j) :=
      stageTargets_mem_zBlock (hsize j) hjtarget
    have hstage : targetStage j = k := by
      rw [← nat_log_256_eq_of_mem_zBlock hmj,
        nat_log_256_eq_of_mem_zBlock hm]
    have hjK : K ≤ j := (mem_stageCanaries.1 p.1.property).1
    right
    refine ⟨j, hjK, hstage, ?_⟩
    rw [← hp]
    exact target_unordRepr_lower ω K hK hpair hcollision hsize p
  · left
    exact canary_unordRepr_lower ω K hK hpair hcollision hsize
      (mem_stageCanaries.2 ⟨hk, hm, ht⟩)

lemma real_log_le_block_scale {k n : ℕ} (hn : n ∈ zBlock k) :
    Real.log n ≤ 256 * (k + 1 : ℕ) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (Z_pos k) (mem_zBlock.1 hn).1)
  have hZpos : (0 : ℝ) < Z (k + 1) := by
    exact_mod_cast Z_pos (k + 1)
  have hnle : (n : ℝ) ≤ Z (k + 1) := by
    exact_mod_cast (mem_zBlock.1 hn).2.le
  have hlogmono := Real.strictMonoOn_log.monotoneOn hnpos hZpos hnle
  have hlog256 : Real.log (256 : ℝ) ≤ 255 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256)
    norm_num at h ⊢
    exact h
  calc
    Real.log n ≤ Real.log (Z (k + 1) : ℕ) := hlogmono
    _ = (k + 1 : ℕ) * Real.log 256 := by
      rw [Z, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ (k + 1 : ℕ) * 255 := by gcongr
    _ ≤ 256 * (k + 1 : ℕ) := by
      push_cast
      have hk0 : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
      nlinarith

lemma dense_logarithmic_representations
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 1000000 : ℝ) * Real.log n <
        ncard_add_repr (denseFinalSet ω K) 2 n := by
  filter_upwards [Filter.eventually_ge_atTop (Z K)] with n hn
  have hn0 : n ≠ 0 := by
    have := Z_pos K
    omega
  let k := Nat.log 256 n
  have hm : n ∈ zBlock k := by
    rw [mem_zBlock]
    exact ⟨Nat.pow_log_le_self 256 hn0,
      by simpa [Z, k, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 256) n⟩
  have hk : K ≤ k := by
    apply (Nat.le_log_iff_pow_le (by norm_num : 1 < 256) hn0).2
    simpa [Z] using hn
  have hlog := real_log_le_block_scale hm
  have hcount := dense_block_unordRepr_lower
    ω K hK hpair hcollision hsize hk hm
  have hunord := unordRepr_card_le_ncard_add_repr (denseFinalSet ω K) n
  rcases hcount with hcanary | ⟨j, hjK, hjstage, hjcount⟩
  · have hnat : k + 1 ≤ ncard_add_repr (denseFinalSet ω K) 2 n :=
      hcanary.trans hunord
    have hkpos : (0 : ℝ) < k + 1 := by positivity
    calc
      (1 / 1000000 : ℝ) * Real.log n ≤
          (1 / 1000000 : ℝ) * (256 * (k + 1 : ℕ)) := by gcongr
      _ < (k + 1 : ℕ) := by
        push_cast
        nlinarith
      _ ≤ ncard_add_repr (denseFinalSet ω K) 2 n := by exact_mod_cast hnat
  · have hnat : j ≤ ncard_add_repr (denseFinalSet ω K) 2 n :=
      hjcount.trans hunord
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) hjK)
    have hscale : k + 1 = 1000 * (j + 1) + 1 := by
      rw [← hjstage]
      rfl
    calc
      (1 / 1000000 : ℝ) * Real.log n ≤
          (1 / 1000000 : ℝ) * (256 * (k + 1 : ℕ)) := by gcongr
      _ < (j : ℕ) := by
        rw [hscale]
        push_cast
        have hjten : (10 : ℝ) ≤ j := by exact_mod_cast hK.trans hjK
        nlinarith
      _ ≤ ncard_add_repr (denseFinalSet ω K) 2 n := by exact_mod_cast hnat

lemma dense_basis
    (ω : DenseSample) (K : ℕ) (hK : 10 ≤ K)
    (hpair : ∀ k ≥ K, ∀ m ∈ zBlock k,
      (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card)
    (hcollision : ∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
      (denseGlobalCommonCenters q r ω).card < 182)
    (hsize : ∀ j, targetSizeCondition ω K j (denseBuildState ω K j)) :
    (denseFinalSet ω K).IsAsymptoticAddBasisOfOrder 2 := by
  rw [isAsymptoticAddBasisOfOrder_iff_repr_pos]
  filter_upwards [dense_logarithmic_representations
    ω K hK hpair hcollision hsize,
    Filter.eventually_ge_atTop 2] with n hn hntwo
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by
    have hn1 : 1 ≤ n := by omega
    exact_mod_cast hn1)
  have hposReal : (0 : ℝ) < ncard_add_repr (denseFinalSet ω K) 2 n := by
    exact lt_of_le_of_lt (mul_nonneg (by norm_num) hlog) hn
  exact_mod_cast hposReal

lemma targetSizeCondition_of_lt_start
    (ω : DenseSample) (K j : ℕ) (hj : j < K) :
    targetSizeCondition ω K j (denseBuildState ω K j) := by
  have hnot : ¬K ≤ j := Nat.not_le_of_gt hj
  have hcan : stageCanaries K j (denseBuildState ω K j) = ∅ := by
    simp [stageCanaries, hnot]
  have hcard : Fintype.card
      (StagePattern ω K j (denseBuildState ω K j)) = 0 := by
    rw [stagePattern_card_eq, hcan]
    simp
  unfold targetSizeCondition
  rw [hcard]
  simp

lemma exists_dense_construction_data :
    ∃ ω : DenseSample, ∃ K : ℕ,
      10 ≤ K ∧
      (∀ k ≥ K, ∀ m ∈ zBlock k,
        (4 : ℝ) ^ k / 40 < (densePresentPairs (m / 3) m ω).card) ∧
      (∀ k ≥ K, ∀ q, q ∈ zBlock k → ∀ r, r ∈ zBlock k → q ≠ r →
        (denseGlobalCommonCenters q r ω).card < 182) ∧
      (∀ j, targetSizeCondition ω K j (denseBuildState ω K j)) := by
  obtain ⟨ω, hpairEv, hpointEv, hcollisionEv⟩ := exists_dense_master_reservoir
  obtain ⟨Npair, hpairN⟩ := Filter.eventually_atTop.1 hpairEv
  obtain ⟨Npoint, hpointN⟩ := Filter.eventually_atTop.1 hpointEv
  obtain ⟨Ncollision, hcollisionN⟩ := Filter.eventually_atTop.1 hcollisionEv
  let K := max 10 (max Npair (max Npoint Ncollision))
  have hK10 : 10 ≤ K := le_max_left _ _
  have hKpair : Npair ≤ K :=
    (le_max_left Npair (max Npoint Ncollision)).trans (le_max_right 10 _)
  have hKpoint : Npoint ≤ K :=
    (le_max_left Npoint Ncollision).trans
      ((le_max_right Npair (max Npoint Ncollision)).trans (le_max_right 10 _))
  have hKcollision : Ncollision ≤ K :=
    (le_max_right Npoint Ncollision).trans
      ((le_max_right Npair (max Npoint Ncollision)).trans (le_max_right 10 _))
  refine ⟨ω, K, hK10, ?_, ?_, ?_⟩
  · intro k hk m hm
    exact hpairN k (hKpair.trans hk) m hm
  · intro k hk q hq r hr hqr
    exact hcollisionN k (hKcollision.trans hk) q hq r hr hqr
  · intro j
    by_cases hj : j < K
    · exact targetSizeCondition_of_lt_start ω K j hj
    · have hjK : K ≤ j := Nat.le_of_not_gt hj
      have hpointReal := hpointN (targetStage j)
        (hKpoint.trans (hjK.trans (Nat.le_of_lt (targetStage_gt j))))
      have hpointNat : (denseSelectedInitial (targetStage j) ω).card ≤
          64 ^ (targetStage j + 1) := by
        exact_mod_cast hpointReal.le
      exact targetSizeCondition_of_point_bound ω K j hpointNat

lemma exists_dense_stagedTrapCertificate : ∃ c : StagedTrapCertificate,
    c.epsilon = (1 / 1000000 : ℝ) := by
  obtain ⟨ω, K, hK, hpair, hcollision, hsize⟩ := exists_dense_construction_data
  let c : StagedTrapCertificate :=
    { A := denseFinalSet ω K
      Bn := finalTargetBlocks ω K
      Cn := finalCanaryBlocks ω K
      epsilon := (1 / 1000000 : ℝ)
      epsilon_pos := by norm_num
      basis := dense_basis ω K hK hpair hcollision hsize
      logarithmic_representations :=
        dense_logarithmic_representations ω K hK hpair hcollision hsize
      cover := dense_staged_cover ω K
      canary_trap := by
        intro D hDA n canary hcanary hone
        exact dense_canary_trap ω K hK hpair hcollision hsize
          D hDA n canary hcanary hone
      target_summands_escape := by
        intro d hdA
        exact dense_target_summands_escape ω K hsize d hdA }
  exact ⟨c, rfl⟩

lemma exists_robustCounterexample : ∃ c : RobustCounterexample,
    c.epsilon = (1 / 1000000 : ℝ) := by
  obtain ⟨c, hc⟩ := exists_dense_stagedTrapCertificate
  exact ⟨c.toTrapCertificate.toConstructionCertificate.toRobustCounterexample, hc⟩

theorem erdos_868.parts.i :
    ¬ ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      atTop.Tendsto (fun n ↦ ncard_add_repr A 2 n) atTop → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  obtain ⟨c, _hc⟩ := exists_robustCounterexample
  exact parts_i_of_robustCounterexample c

theorem erdos_868.parts.ii :
    ¬ ∀ᵉ (A : Set ℕ) (ε > 0), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  obtain ⟨c, _hc⟩ := exists_robustCounterexample
  exact parts_ii_of_robustCounterexample c

end Erdos868

#print axioms Erdos868.erdos_868.parts.i
#print axioms Erdos868.erdos_868.parts.ii
