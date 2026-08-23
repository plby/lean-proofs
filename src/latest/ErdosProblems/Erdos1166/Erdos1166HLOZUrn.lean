/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card

/-!
Elementary negative-binomial and urn estimates used in the upper-bound
argument of Hao--Li--Okada--Zheng for planar favorite sites.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace Erdos1166.HLOZUrn

/-- The negative-binomial mass `p(i,j)` from HLOZ equation (2.15). -/
noncomputable def negBinMass (i j : ℕ) : ℝ :=
  (Nat.choose (i + j - 1) j : ℝ) * 15 ^ i / 16 ^ (i + j)

lemma negBinMass_nonneg (i j : ℕ) : 0 ≤ negBinMass i j := by
  unfold negBinMass
  positivity

/-- Exact adjacent-point ratio identity for the mass in HLOZ (2.15), in a
division-free form. -/
lemma negBinMass_adjacent (i j : ℕ) (hi : 1 ≤ i) :
    16 * (j + 1) * negBinMass i (j + 1) = (i + j) * negBinMass i j := by
  have hindex : i + j - 1 + 1 = i + j := by omega
  have hchooseNat :
      (i + j) * Nat.choose (i + j - 1) j =
        Nat.choose (i + j) (j + 1) * (j + 1) := by
    simpa only [hindex] using Nat.add_one_mul_choose_eq (i + j - 1) j
  have hchoose :
      (i + j : ℝ) * (Nat.choose (i + j - 1) j : ℝ) =
        (Nat.choose (i + j) (j + 1) : ℝ) * (j + 1 : ℝ) := by
    exact_mod_cast hchooseNat
  unfold negBinMass
  have hpow : (16 : ℝ) ^ (i + (j + 1)) = 16 * 16 ^ (i + j) := by
    rw [show i + (j + 1) = (i + j) + 1 by omega, pow_succ]
    ring
  rw [show i + (j + 1) - 1 = i + j by omega, hpow]
  field_simp
  nlinarith

lemma negBinMass_adjacent_ratio (i j : ℕ) (hi : 1 ≤ i) :
    negBinMass i (j + 1) =
      ((i + j : ℝ) / (16 * (j + 1))) * negBinMass i j := by
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity : (16 : ℝ) * (j + 1) ≠ 0)]
  simpa only [mul_comm] using negBinMass_adjacent i j hi

/-- Past the integer mode, the HLOZ negative-binomial point masses decrease. -/
lemma negBinMass_decreasing_after_mode (i j : ℕ) (hi : 1 ≤ i)
    (hmode : i ≤ 15 * j + 16) :
    negBinMass i (j + 1) ≤ negBinMass i j := by
  apply le_of_mul_le_mul_left (a := (16 : ℝ) * (j + 1)) _ (by positivity)
  · rw [negBinMass_adjacent i j hi]
    apply mul_le_mul_of_nonneg_right _ (negBinMass_nonneg i j)
    exact_mod_cast (show i + j ≤ 16 * (j + 1) by omega)

/-- Before the mode, the same exact ratio identity shows that the point
masses increase. -/
lemma negBinMass_increasing_before_mode (i j : ℕ) (hi : 1 ≤ i)
    (hmode : 16 * (j + 1) ≤ i + j) :
    negBinMass i j ≤ negBinMass i (j + 1) := by
  apply le_of_mul_le_mul_left (a := (16 : ℝ) * (j + 1)) _ (by positivity)
  · rw [negBinMass_adjacent i j hi]
    apply mul_le_mul_of_nonneg_right _ (negBinMass_nonneg i j)
    exact_mod_cast hmode

/-! ### The geometric-sum law behind HLOZ equation (2.15) -/

/-- The success parameter `15/16` of one geometric run. -/
noncomputable def runParameter : unitInterval :=
  ⟨15 / 16, by norm_num⟩

lemma runParameter_ne_zero : runParameter ≠ 0 := by
  intro h
  have h' := congrArg ((↑·) : unitInterval → ℝ) h
  norm_num [runParameter] at h'

/-- The number of failures before a success of probability `15/16`. -/
noncomputable def runMeasure : Measure ℕ :=
  geometricMeasure runParameter

instance : IsProbabilityMeasure runMeasure := by
  dsimp [runMeasure]
  infer_instance

lemma runMeasure_real_singleton (j : ℕ) :
    runMeasure.real {j} = (1 / 16 : ℝ) ^ j * (15 / 16) := by
  rw [runMeasure, geometricMeasure_real_singleton runParameter_ne_zero]
  norm_num [runParameter]

/-- The product law of `i` independent geometric runs. -/
noncomputable def runVectorMeasure (i : ℕ) : Measure (Fin i → ℕ) :=
  Measure.pi (fun _ ↦ runMeasure)

instance (i : ℕ) : IsProbabilityMeasure (runVectorMeasure i) := by
  dsimp [runVectorMeasure]
  infer_instance

private lemma singleton_pi (i : ℕ) (g : Fin i → ℕ) :
    ({g} : Set (Fin i → ℕ)) = Set.pi Set.univ (fun k ↦ {g k}) := by
  ext x
  simp [funext_iff]

lemma runVectorMeasure_singleton (i : ℕ) (g : Fin i → ℕ) :
    runVectorMeasure i {g} = ∏ k, runMeasure {g k} := by
  rw [singleton_pi]
  exact Measure.pi_pi (fun _ ↦ runMeasure) (fun k ↦ {g k})

/-- Exact mass of one vector of independent geometric runs. -/
lemma runVectorMeasure_real_singleton (i : ℕ) (g : Fin i → ℕ) :
    (runVectorMeasure i).real {g} =
      15 ^ i / 16 ^ (i + ∑ k, g k) := by
  rw [measureReal_def, runVectorMeasure_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, runMeasure_real_singleton]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [div_pow, div_pow]
  norm_num
  rw [pow_add]
  ring

/-- Stars-and-bars equivalence between weak compositions and multisets. -/
noncomputable def antidiagonalTupleEquivSym (i j : ℕ) :
    (Finset.Nat.antidiagonalTuple i j) ≃ Sym (Fin i) j where
  toFun g := (Sym.equivNatSumOfFintype (Fin i) j).symm
    ⟨g.1, Finset.Nat.mem_antidiagonalTuple.mp g.2⟩
  invFun s :=
    ⟨(Sym.equivNatSumOfFintype (Fin i) j s).1,
      Finset.Nat.mem_antidiagonalTuple.mpr
        (Sym.equivNatSumOfFintype (Fin i) j s).2⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv s := by
    simp

/-- The number of weak compositions of `j` into `i` parts. -/
lemma card_antidiagonalTuple (i j : ℕ) :
    (Finset.Nat.antidiagonalTuple i j).card = Nat.choose (i + j - 1) j := by
  calc
    (Finset.Nat.antidiagonalTuple i j).card =
        Fintype.card (Finset.Nat.antidiagonalTuple i j) := by
      rw [Fintype.card_coe]
    _ = Fintype.card (Sym (Fin i) j) :=
      Fintype.card_congr (antidiagonalTupleEquivSym i j)
    _ = Nat.multichoose i j := by
      rw [Sym.card_sym_eq_multichoose, Fintype.card_fin]
    _ = Nat.choose (i + j - 1) j := Nat.multichoose_eq i j

/-- The stars-and-bars convolution identity for the negative-binomial
coefficient. This is the combinatorial identity used when one more
geometric run is convolved into the sum. -/
lemma negBin_choose_convolution (i j : ℕ) :
    ∑ k ∈ Finset.range (j + 1), Nat.choose (i + (j - k) - 1) (j - k) =
      Nat.choose (i + j) j := by
  simp_rw [← Nat.multichoose_eq i]
  rw [Finset.sum_flip, Nat.sum_range_multichoose]
  simpa only [Nat.add_comm] using
    (Nat.choose_symm_of_eq_add (n := i + j) (a := j) (b := i)
      (Nat.add_comm i j)).symm

lemma negBinMass_mul_runMeasure (i j k : ℕ) (hk : k ≤ j) :
    negBinMass i (j - k) * runMeasure.real {k} =
      (Nat.choose (i + (j - k) - 1) (j - k) : ℝ) *
        ((15 : ℝ) ^ (i + 1) / 16 ^ (i + j + 1)) := by
  rw [negBinMass, runMeasure_real_singleton]
  rw [div_pow]
  norm_num
  field_simp
  have h16 : (16 : ℝ) ^ (i + j + 1) =
      16 ^ (i + (j - k)) * 16 ^ k * 16 := by
    rw [show i + j + 1 = (i + (j - k) + k) + 1 by omega,
      pow_succ, pow_add]
  rw [h16, pow_succ]
  ring

/-- Convolution of the `i`-run mass with one geometric run gives the
`i+1`-run mass, in exactly the normalization of HLOZ (2.15). -/
lemma negBinMass_succ_convolution (i j : ℕ) :
    ∑ k ∈ Finset.range (j + 1),
        negBinMass i (j - k) * runMeasure.real {k} =
      negBinMass (i + 1) j := by
  have hchooseR :
      (∑ k ∈ Finset.range (j + 1),
        (Nat.choose (i + (j - k) - 1) (j - k) : ℝ)) =
          (Nat.choose (i + j) j : ℝ) := by
    exact_mod_cast negBin_choose_convolution i j
  calc
    ∑ k ∈ Finset.range (j + 1),
        negBinMass i (j - k) * runMeasure.real {k} =
        ∑ k ∈ Finset.range (j + 1),
          (Nat.choose (i + (j - k) - 1) (j - k) : ℝ) *
            ((15 : ℝ) ^ (i + 1) / 16 ^ (i + j + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply negBinMass_mul_runMeasure
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    _ = (Nat.choose (i + j) j : ℝ) *
          ((15 : ℝ) ^ (i + 1) / 16 ^ (i + j + 1)) := by
      rw [← Finset.sum_mul, hchooseR]
    _ = negBinMass (i + 1) j := by
      unfold negBinMass
      rw [show i + 1 + j - 1 = i + j by omega,
        show i + 1 + j = i + j + 1 by omega]
      ring

/-- Sum of a finite vector of run lengths. -/
def runSum (i : ℕ) (g : Fin i → ℕ) : ℕ :=
  ∑ k, g k

lemma measurable_runSum (i : ℕ) : Measurable (runSum i) :=
  measurable_of_countable _

/-- The law of the sum of `i` independent geometric runs. -/
noncomputable def negBinMeasure (i : ℕ) : Measure ℕ :=
  (runVectorMeasure i).map (runSum i)

instance (i : ℕ) : IsProbabilityMeasure (negBinMeasure i) := by
  dsimp [negBinMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_runSum i).aemeasurable

/-- Exact singleton mass of the geometric-sum law, HLOZ equation (2.15). -/
lemma negBinMeasure_real_singleton (i j : ℕ) :
    (negBinMeasure i).real {j} = negBinMass i j := by
  rw [negBinMeasure, measureReal_def,
    Measure.map_apply (measurable_runSum i) (measurableSet_singleton j)]
  change (runVectorMeasure i).real ((runSum i) ⁻¹' {j}) = _
  have hevent : (runSum i) ⁻¹' {j} =
      (↑(Finset.Nat.antidiagonalTuple i j) : Set (Fin i → ℕ)) := by
    ext g
    simp [runSum, Finset.Nat.mem_antidiagonalTuple]
  rw [hevent, ← sum_measureReal_singleton]
  calc
    ∑ g ∈ Finset.Nat.antidiagonalTuple i j, (runVectorMeasure i).real {g} =
        ∑ _g ∈ Finset.Nat.antidiagonalTuple i j,
          (15 : ℝ) ^ i / 16 ^ (i + j) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [runVectorMeasure_real_singleton]
      rw [Finset.Nat.mem_antidiagonalTuple.mp hg]
    _ = (Finset.Nat.antidiagonalTuple i j).card *
          ((15 : ℝ) ^ i / 16 ^ (i + j)) := by simp
    _ = negBinMass i j := by
      rw [card_antidiagonalTuple]
      unfold negBinMass
      ring

theorem runSum_hasLaw :
    HasLaw (runSum i) (negBinMeasure i) (runVectorMeasure i) := by
  exact ⟨(measurable_runSum i).aemeasurable, rfl⟩

/-- A usable iid formulation of HLOZ equation (2.15): any finite random
vector with the product geometric law has a sum whose law has singleton
mass `negBinMass i j`. -/
theorem HasLaw.sum_iid_run_lengths
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → Fin i → ℕ) (hX : HasLaw X (runVectorMeasure i) μ) :
    HasLaw (fun ω ↦ ∑ k, X ω k) (negBinMeasure i) μ := by
  simpa only [runSum] using runSum_hasLaw.fun_comp hX

theorem HasLaw.sum_iid_run_lengths_real_singleton
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → Fin i → ℕ) (hX : HasLaw X (runVectorMeasure i) μ)
    (j : ℕ) :
    μ.real {ω | (∑ k, X ω k) = j} = negBinMass i j := by
  calc
    μ.real {ω | (∑ k, X ω k) = j} = (negBinMeasure i).real {j} := by
      simpa only [Set.ofPred_eq_eq_singleton] using
        (HasLaw.sum_iid_run_lengths X hX).measureReal_eq
          (p := fun n : ℕ ↦ n = j) (measurableSet_singleton j)
    _ = negBinMass i j := negBinMeasure_real_singleton i j

/-- The conditional success parameter for two adjacent urns. -/
noncomputable def adjacentUrnParameter (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    unitInterval :=
  ⟨p / (p + q), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by linarith)⟩

@[simp]
lemma coe_adjacentUrnParameter (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    (adjacentUrnParameter p q hp hq : ℝ) = p / (p + q) := rfl

/-- If `p ≤ Cq`, the conditional chance of choosing the `p`-urn is at most
`C/(C+1)`. -/
lemma adjacentUrnParameter_le
    {p q C : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hC : 0 ≤ C) (hpq : p ≤ C * q) :
    (adjacentUrnParameter p q hp hq : ℝ) ≤ C / (C + 1) := by
  rw [coe_adjacentUrnParameter]
  apply (div_le_div_iff₀ (by positivity : 0 < p + q)
    (by positivity : 0 < C + 1)).2
  nlinarith

/-- The explicit exponential estimate at the end of HLOZ Lemma 2.7.  One
may take the source's constant `c(C)` to be `1/(C+1)`. -/
lemma adjacentUrnParameter_pow_le_exp
    {p q C : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hC : 0 ≤ C) (hpq : p ≤ C * q)
    (h : ℕ) :
    (adjacentUrnParameter p q hp hq : ℝ) ^ h ≤
      Real.exp (-((h : ℝ) / (C + 1))) := by
  have hratio_nonneg : 0 ≤ C / (C + 1) := by positivity
  have hratio_exp : C / (C + 1) ≤ Real.exp (-(1 / (C + 1))) := by
    calc
      C / (C + 1) = 1 - 1 / (C + 1) := by field_simp; ring
      _ ≤ Real.exp (-(1 / (C + 1))) := Real.one_sub_le_exp_neg _
  calc
    (adjacentUrnParameter p q hp hq : ℝ) ^ h ≤ (C / (C + 1)) ^ h := by
      exact pow_le_pow_left₀ (adjacentUrnParameter p q hp hq).property.1
        (adjacentUrnParameter_le hp hq hC hpq) h
    _ ≤ (Real.exp (-(1 / (C + 1)))) ^ h := by gcongr
    _ = Real.exp (-((h : ℝ) / (C + 1))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The conditional-binomial core of HLOZ Lemma 2.7.  Here `B` is the event
`Xₙ ≤ m+1, Fₘ+Fₘ₊₁=h`, while `A` is `Fₘ=h, Xₙ=m`. -/
theorem urn_local_bound_of_conditional_binomial
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (F : Ω → ℕ) (h : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hAh : A ⊆ F ⁻¹' {h})
    (hLaw : ProbabilityTheory.HasLaw F
      (ProbabilityTheory.binomial h (adjacentUrnParameter p q hp hq)) μ[|B]) :
    μ.real A ≤ (p / (p + q)) ^ h := by
  have hcond_le : μ[|B].real A ≤ μ[|B].real (F ⁻¹' {h}) :=
    measureReal_mono hAh
  have hbin : μ[|B].real (F ⁻¹' {h}) =
      (adjacentUrnParameter p q hp hq : ℝ) ^ h := by
    calc
      μ[|B].real (F ⁻¹' {h}) =
          (ProbabilityTheory.binomial h
            (adjacentUrnParameter p q hp hq)).real {h} := by
        have hlaw := hLaw.measureReal_eq (p := fun x : ℕ => x = h)
          (by simpa only [Set.ofPred_eq_eq_singleton] using measurableSet_singleton h)
        rw [Set.ofPred_eq_eq_singleton] at hlaw
        have hpre : F ⁻¹' {h} = {ω | F ω = h} := by ext x; simp
        rw [hpre]
        exact hlaw
      _ = (adjacentUrnParameter p q hp hq : ℝ) ^ h := by simp
  have hmul := ProbabilityTheory.cond_mul_eq_inter hB A μ
  have hinter : B ∩ A = A := Set.inter_eq_right.mpr hAB
  rw [hinter] at hmul
  have hmul_real : μ[|B].real A * μ.real B = μ.real A := by
    simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal hmul
  calc
    μ.real A = μ[|B].real A * μ.real B := hmul_real.symm
    _ ≤ μ[|B].real A * 1 := by
      gcongr
      exact measureReal_le_one
    _ = μ[|B].real A := mul_one _
    _ ≤ (adjacentUrnParameter p q hp hq : ℝ) ^ h := hcond_le.trans_eq hbin
    _ = (p / (p + q)) ^ h := rfl

/-- HLOZ Lemma 2.7's exponential conclusion, with explicit constant. -/
theorem urn_local_exp_tail_of_conditional_binomial
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (F : Ω → ℕ) (h : ℕ)
    (p q C : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hC : 0 ≤ C) (hpq : p ≤ C * q)
    (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hAh : A ⊆ F ⁻¹' {h})
    (hLaw : ProbabilityTheory.HasLaw F
      (ProbabilityTheory.binomial h (adjacentUrnParameter p q hp hq)) μ[|B]) :
    μ.real A ≤ Real.exp (-((h : ℝ) / (C + 1))) := by
  exact (urn_local_bound_of_conditional_binomial μ A B F h p q hp hq
    hB hAB hAh hLaw).trans (adjacentUrnParameter_pow_le_exp hp hq hC hpq h)

/-! ### A finite-iid realization of HLOZ Lemma 2.7 -/

/-- Under the set-valued Bernoulli product measure, the probability that a
fixed finite set `U` is contained in the random set is `p ^ |U|`. -/
lemma setBernoulli_apply_superset
    {ι : Type*} [Countable ι] {u U : Set ι} (p : unitInterval)
    (hU : U ⊆ u) (hUf : U.Finite) :
    setBer(u, p) {V | U ⊆ V} = ENNReal.ofReal ((p : ℝ) ^ U.ncard) := by
  rw [setBernoulli_apply']
  have hevent :
      (fun b : ι → Prop => {i | b i}) ⁻¹' {V | U ⊆ V} =
        MeasureTheory.cylinder hUf.toFinset
          ({fun _ : hUf.toFinset => True} : Set (hUf.toFinset → Prop)) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, MeasureTheory.mem_cylinder,
      Set.mem_singleton_iff]
    constructor
    · intro hb
      funext i
      exact propext ⟨fun _ => True.intro,
        fun _ => hb (hUf.mem_toFinset.mp i.property)⟩
    · intro hb i hi
      have hfun := congrFun hb ⟨i, hUf.mem_toFinset.mpr hi⟩
      change b i
      change b i = True at hfun
      exact hfun.symm ▸ True.intro
  rw [hevent]
  change (Measure.infinitePi fun i => bernoulliMeasure (i ∈ u) False p)
      (MeasureTheory.cylinder hUf.toFinset
        ({fun _ : hUf.toFinset => True} : Set (hUf.toFinset → Prop))) = _
  rw [MeasureTheory.Measure.infinitePi_cylinder
      (μ := fun i => bernoulliMeasure (i ∈ u) False p)
      (s := hUf.toFinset)
      (S := ({fun _ : hUf.toFinset => True} : Set (hUf.toFinset → Prop)))
      (measurableSet_singleton _), Measure.pi_singleton]
  have hmem : ∀ i : hUf.toFinset, (i : ι) ∈ u :=
    fun i => hU (hUf.mem_toFinset.mp i.property)
  simp only [bernoulliMeasure_apply p (measurableSet_singleton True),
    Set.mem_singleton_iff, hmem, if_pos, false_ne_true, if_false]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    ← Set.ncard_eq_toFinset_card U hUf, ENNReal.ofReal_pow p.property.1]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- Intersecting a random set with a fixed set is measurable. -/
lemma measurable_inter_left {ι : Type*} (U : Set ι) :
    Measurable (fun V : Set ι => U ∩ V) := by
  exact MeasurableEquiv.setOfPred.measurable.comp
    (measurable_pi_lambda _ fun _ =>
      measurable_const.and (MeasurableEquiv.setOfPred.symm.measurable.eval))

/-- Restricting a set-valued Bernoulli sample to `U ⊆ u` again gives a
set-valued Bernoulli sample, now supported on `U`. -/
lemma map_inter_setBernoulli
    {ι : Type*} [Countable ι] {u U : Set ι} (p : unitInterval) (hU : U ⊆ u) :
    (setBer(u, p)).map (fun V => U ∩ V) = setBer(U, p) := by
  rw [setBernoulli_eq_map, setBernoulli_eq_map]
  rw [Measure.map_map (measurable_inter_left U) (by fun_prop)]
  have hcomp :
      (fun V : Set ι => U ∩ V) ∘ (fun b : ι → Prop => {i | b i}) =
        (fun b : ι → Prop => {i | i ∈ U ∧ b i}) := by
    funext b
    ext i
    simp
  rw [hcomp]
  have hset :
      (fun b : ι → Prop => {i | i ∈ U ∧ b i}) =
        (fun b => {i | b i}) ∘ (fun b i => i ∈ U ∧ b i) := by rfl
  rw [hset, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.infinitePi_map_pi _ (fun _ => by fun_prop)]
  apply congrArg (Measure.map (fun b : ι → Prop => {i | b i}))
  apply congrArg Measure.infinitePi
  funext i
  change Measure.map (fun b : Prop => i ∈ U ∧ b)
      (bernoulliMeasure (i ∈ u) False p) = bernoulliMeasure (i ∈ U) False p
  rw [map_bernoulliMeasure]
  by_cases hi : i ∈ U
  · simp [hi, hU hi]
  · simp [hi]

/-- The cardinality of a finite set-valued Bernoulli sample has the usual
binomial law. -/
lemma map_ncard_setBernoulli_eq_binomial
    {ι : Type*} [Countable ι] {U : Set ι} (hUf : U.Finite) (p : unitInterval) :
    (setBer(U, p)).map Set.ncard = Bin(U.ncard, p) := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton hUf, binomial_real_singleton]

/-- The number of selected labels in a fixed finite subset `U` has the
binomial law, even when the ambient set of labels is larger. -/
theorem contributingUrnCount_hasLaw_binomial
    {ι : Type*} [Countable ι] {u U : Set ι} (p : unitInterval)
    (hU : U ⊆ u) (hUf : U.Finite) :
    HasLaw (fun V : Set ι => (U ∩ V).ncard) Bin(U.ncard, p) setBer(u, p) := by
  refine ⟨(measurable_ncard.comp (measurable_inter_left U)).aemeasurable, ?_⟩
  change Measure.map (Set.ncard ∘ fun V : Set ι => U ∩ V) setBer(u, p) = _
  rw [← Measure.map_map measurable_ncard (measurable_inter_left U),
    map_inter_setBernoulli p hU, map_ncard_setBernoulli_eq_binomial hUf p]

theorem contributingUrnCount_hasLaw_binomial_of_ncard
    {ι : Type*} [Countable ι] {u U : Set ι} (p : unitInterval)
    (hU : U ⊆ u) (hUf : U.Finite) {h : ℕ} (hcard : U.ncard = h) :
    HasLaw (fun V : Set ι => (U ∩ V).ncard) Bin(h, p) setBer(u, p) := by
  simpa only [hcard] using contributingUrnCount_hasLaw_binomial p hU hUf

/-- In the two-stage finite iid urn model, this is the bad event that exactly
`h` labels are active and every active label chooses the first urn. -/
def finiteIidUrnBad (n h : ℕ) : Set (Set ℕ × Set ℕ) :=
  ⋃ s ∈ (Finset.range n).powersetCard h,
    ({(↑s : Set ℕ)} : Set (Set ℕ)) ×ˢ {V | (↑s : Set ℕ) ⊆ V}

/-- The bad event in the finite iid realization has probability at most the
`h`-th power of the conditional first-urn parameter. -/
theorem finiteIidUrnBad_measure_le
    (n h : ℕ) (active first : unitInterval) :
    (setBer(Set.Iio n, active).prod setBer(Set.Iio n, first))
        (finiteIidUrnBad n h) ≤ ENNReal.ofReal ((first : ℝ) ^ h) := by
  let cand : Finset (Finset ℕ) := (Finset.range n).powersetCard h
  let μa : Measure (Set ℕ) := setBer(Set.Iio n, active)
  let μf : Measure (Set ℕ) := setBer(Set.Iio n, first)
  have hdisj : (↑cand : Set (Finset ℕ)).PairwiseDisjoint
      (fun s => ({(↑s : Set ℕ)} : Set (Set ℕ))) := by
    intro s _ t _ hst
    change Disjoint ({(↑s : Set ℕ)} : Set (Set ℕ)) ({(↑t : Set ℕ)} : Set (Set ℕ))
    rw [Set.disjoint_singleton]
    exact fun hco => hst (Finset.coe_injective hco)
  have hsum : (∑ s ∈ cand, μa ({(↑s : Set ℕ)} : Set (Set ℕ))) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj (fun _ _ => measurableSet_singleton _)]
    calc
      μa (⋃ s ∈ cand, ({(↑s : Set ℕ)} : Set (Set ℕ))) ≤ μa Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := by simp [μa]
  change (μa.prod μf) (finiteIidUrnBad n h) ≤ _
  unfold finiteIidUrnBad
  change (μa.prod μf)
      (⋃ s ∈ cand, ({(↑s : Set ℕ)} : Set (Set ℕ)) ×ˢ {V | (↑s : Set ℕ) ⊆ V}) ≤ _
  refine (measure_biUnion_finset_le cand
    (fun s => ({(↑s : Set ℕ)} : Set (Set ℕ)) ×ˢ {V | (↑s : Set ℕ) ⊆ V})).trans ?_
  calc
    (∑ s ∈ cand, (μa.prod μf)
        (({(↑s : Set ℕ)} : Set (Set ℕ)) ×ˢ {V | (↑s : Set ℕ) ⊆ V})) =
        ∑ s ∈ cand, μa ({(↑s : Set ℕ)} : Set (Set ℕ)) *
          ENNReal.ofReal ((first : ℝ) ^ h) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Measure.prod_prod]
      have hsc := (Finset.mem_powersetCard.mp hs).2
      have hss : (↑s : Set ℕ) ⊆ Set.Iio n := by
        intro i hi
        have hi' : i ∈ Finset.range n :=
          (Finset.mem_powersetCard.mp hs).1 (by simpa using hi)
        simpa using hi'
      rw [setBernoulli_apply_superset first hss s.finite_toSet]
      rw [Set.ncard_coe_finset, hsc]
    _ = (∑ s ∈ cand, μa ({(↑s : Set ℕ)} : Set (Set ℕ))) *
          ENNReal.ofReal ((first : ℝ) ^ h) := by rw [Finset.sum_mul]
    _ ≤ 1 * ENNReal.ofReal ((first : ℝ) ^ h) := by gcongr
    _ = ENNReal.ofReal ((first : ℝ) ^ h) := one_mul _

/-- The probability that a label falls into either of the two adjacent urns. -/
noncomputable def pairActiveParameter (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) : unitInterval :=
  ⟨p + q, by exact ⟨add_nonneg hp hq, hpq⟩⟩

/-- Conditional on a prescribed `h`-element set of active labels, the
number choosing the first urn is binomial with parameter `p/(p+q)`. -/
theorem pairUrnCount_hasLaw_binomial
    (n h : ℕ) (s : Finset ℕ) (hs : s ∈ (Finset.range n).powersetCard h)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    HasLaw (fun V : Set ℕ => ((↑s : Set ℕ) ∩ V).ncard)
      Bin(h, adjacentUrnParameter p q hp hq)
      setBer(Set.Iio n, adjacentUrnParameter p q hp hq) := by
  have hsub : (↑s : Set ℕ) ⊆ Set.Iio n := by
    intro i hi
    have : i ∈ Finset.range n :=
      (Finset.mem_powersetCard.mp hs).1 (by simpa using hi)
    simpa using this
  apply contributingUrnCount_hasLaw_binomial_of_ncard
    (adjacentUrnParameter p q hp hq) hsub s.finite_toSet
  simpa [Set.ncard_coe_finset] using (Finset.mem_powersetCard.mp hs).2

/-- Source-accurate finite-iid form of HLOZ Lemma 2.7. Labels independently
enter the adjacent pair with probability `p+q`; conditional on entry they
choose the first urn with probability `p/(p+q)`. The probability that all
`h` active labels choose the first urn has the claimed exponential tail. -/
theorem hloz_lemma_2_7_finite_iid
    (n h : ℕ) (p q C : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hpq_one : p + q ≤ 1)
    (hC : 0 ≤ C) (hpq : p ≤ C * q) :
    (setBer(Set.Iio n, pairActiveParameter p q hp hq.le hpq_one).prod
      setBer(Set.Iio n, adjacentUrnParameter p q hp hq))
        (finiteIidUrnBad n h) ≤
      ENNReal.ofReal (Real.exp (-((h : ℝ) / (C + 1)))) := by
  exact (finiteIidUrnBad_measure_le n h
    (pairActiveParameter p q hp hq.le hpq_one)
    (adjacentUrnParameter p q hp hq)).trans
      (ENNReal.ofReal_le_ofReal (adjacentUrnParameter_pow_le_exp hp hq hC hpq h))

/-! ### The finite core of HLOZ Lemma 2.8 -/

/-- The elementary counting estimate used in HLOZ Lemma 2.8: a binomial
coefficient is at most the corresponding power of the number of trials. -/
theorem binomial_term_le_trial_pow
    {l j J : ℕ} {q K r : ℝ}
    (hlJ : l ≤ J) (hq0 : 0 ≤ q) (hqK : q ≤ K)
    (hK0 : 0 ≤ K) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Nat.choose l j : ℝ) * q ^ j * r ^ (l - j) ≤
      (K * (J : ℝ)) ^ j := by
  have hchoose : (Nat.choose l j : ℝ) ≤ (l : ℝ) ^ j := by
    exact_mod_cast Nat.choose_le_pow l j
  have hlJ' : (l : ℝ) ≤ J := by exact_mod_cast hlJ
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hqpow : q ^ j ≤ K ^ j := pow_le_pow_left₀ hq0 hqK j
  have hlpow : (l : ℝ) ^ j ≤ (J : ℝ) ^ j := pow_le_pow_left₀ hl0 hlJ' j
  have hrpow : r ^ (l - j) ≤ 1 := by
    exact pow_le_one₀ hr0 hr1
  calc
    (Nat.choose l j : ℝ) * q ^ j * r ^ (l - j)
        ≤ ((l : ℝ) ^ j * K ^ j) * 1 := by
          gcongr
    _ ≤ ((J : ℝ) ^ j * K ^ j) * 1 := by
          gcongr
    _ = (K * (J : ℝ)) ^ j := by ring

/-- Exact probability version of the finite estimate: an atom of a binomial
law with at most `J` trials is bounded by `(K J)^j` whenever its success
probability is at most `K`. -/
theorem binomial_atom_le
    {l j J : ℕ} (q : I) {K : ℝ}
    (hlJ : l ≤ J) (hqK : (q : ℝ) ≤ K) (hK0 : 0 ≤ K) :
    Bin(l, q).real {j} ≤ (K * (J : ℝ)) ^ j := by
  rw [binomial_real_singleton]
  exact binomial_term_le_trial_pow hlJ q.2.1 hqK hK0
    (sub_nonneg.mpr q.2.2) (sub_le_self 1 q.2.1)

/-- Mixtures preserve the HLOZ finite counting bound. This is the abstract
form needed after conditioning on the total number `l ≤ J` of balls in the
two bands: `w l` is the conditional law of that total. -/
theorem binomial_mixture_le
    (L : Finset ℕ) (w : ℕ → ℝ) {j J : ℕ} (q : I) {K : ℝ}
    (hL : ∀ l ∈ L, l ≤ J)
    (hw0 : ∀ l ∈ L, 0 ≤ w l)
    (hw : ∑ l ∈ L, w l ≤ 1)
    (hqK : (q : ℝ) ≤ K) (hK0 : 0 ≤ K) :
    ∑ l ∈ L, w l * Bin(l, q).real {j} ≤ (K * (J : ℝ)) ^ j := by
  let D : ℝ := (K * (J : ℝ)) ^ j
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  calc
    ∑ l ∈ L, w l * Bin(l, q).real {j}
        ≤ ∑ l ∈ L, w l * D := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_left
            (binomial_atom_le q (hL l hl) hqK hK0) (hw0 l hl)
    _ = (∑ l ∈ L, w l) * D := by rw [Finset.sum_mul]
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hw hD0
    _ = (K * (J : ℝ)) ^ j := one_mul D

/-- The algebraic ratio reduction behind HLOZ (2.22), deliberately stated
without division. If the top band has `g` labels among `f` total labels and
every top weight is at most `C` times every lower-band weight, its total
weight is at most `max C 1 * g/f` of the total weight. -/
theorem band_mass_cross_mul
    {α : Type*} [DecidableEq α] (A B : Finset α) (p : α → ℝ) {C : ℝ}
    (hdisj : Disjoint A B) (hp0 : ∀ x ∈ A ∪ B, 0 ≤ p x)
    (hp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b) :
    ((A ∪ B).card : ℝ) * (∑ a ∈ A, p a) ≤
      max C 1 * (A.card : ℝ) * (∑ x ∈ A ∪ B, p x) := by
  have hA0 : 0 ≤ ∑ a ∈ A, p a :=
    Finset.sum_nonneg fun a ha ↦ hp0 a (by simp [ha])
  have hB0 : 0 ≤ ∑ b ∈ B, p b :=
    Finset.sum_nonneg fun b hb ↦ hp0 b (by simp [hb])
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have h1max : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hpair : (B.card : ℝ) * (∑ a ∈ A, p a) ≤
      C * (A.card : ℝ) * (∑ b ∈ B, p b) := by
    calc
      (B.card : ℝ) * (∑ a ∈ A, p a)
          = ∑ a ∈ A, ∑ b ∈ B, p a := by
              simp [Finset.mul_sum]
      _ ≤ ∑ a ∈ A, ∑ b ∈ B, C * p b := by
              gcongr with a ha b hb
              exact hp a ha b hb
      _ = C * (A.card : ℝ) * (∑ b ∈ B, p b) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              rw [← Finset.mul_sum]
              ring
  rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add,
    Finset.sum_union hdisj]
  nlinarith [mul_nonneg (sub_nonneg.mpr hCmax) hB0,
    mul_nonneg (sub_nonneg.mpr h1max) hA0]

/-- Division-form consequence of `band_mass_cross_mul`, matching the ratio
of the two probability masses in HLOZ (2.22). -/
theorem band_mass_ratio
    {α : Type*} [DecidableEq α] (A B : Finset α) (p : α → ℝ) {C : ℝ}
    (hdisj : Disjoint A B) (hp0 : ∀ x ∈ A ∪ B, 0 ≤ p x)
    (hp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b)
    (hmass : 0 < ∑ x ∈ A ∪ B, p x) :
    (∑ a ∈ A, p a) / (∑ x ∈ A ∪ B, p x) ≤
      max C 1 * (A.card : ℝ) / ((A ∪ B).card : ℝ) := by
  have hunion : (A ∪ B).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hmass
    simp at hmass
  have hcard : (0 : ℝ) < ((A ∪ B).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hunion
  apply (div_le_iff₀ hmass).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hcard).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    band_mass_cross_mul A B p hdisj hp0 hp

/-- End-to-end finite core of HLOZ Lemma 2.8. The parameter `q` is the
conditional probability that a ball known to lie in the union of the two
bands lies in the top band. After the mandatory ball in the maximal urn is
singled out, the remaining top-band count is a binomial atom at `j`. -/
theorem hloz_lemma_2_8_core
    {α : Type*} [DecidableEq α] (A B : Finset α) (p : α → ℝ) {C : ℝ}
    (hdisj : Disjoint A B) (hp0 : ∀ x ∈ A ∪ B, 0 ≤ p x)
    (hp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b)
    (hmass : 0 < ∑ x ∈ A ∪ B, p x)
    (q : I)
    (hq : (q : ℝ) = (∑ a ∈ A, p a) / (∑ x ∈ A ∪ B, p x))
    {l j J : ℕ} (hlJ : l ≤ J) :
    Bin(l, q).real {j} ≤
      ((max C 1 * (A.card : ℝ) / ((A ∪ B).card : ℝ)) * (J : ℝ)) ^ j := by
  have hqK : (q : ℝ) ≤
      max C 1 * (A.card : ℝ) / ((A ∪ B).card : ℝ) := by
    rw [hq]
    exact band_mass_ratio A B p hdisj hp0 hp hmass
  apply binomial_atom_le q hlJ hqK
  have hmax : (0 : ℝ) ≤ max C 1 := (le_max_right C 1).trans' zero_le_one
  positivity

/-! ## Negative-binomial moderate deviations

The following exact moment-generating function calculation and Chernoff
bounds supply the moderate-deviation input for the HLOZ urn argument. -/

lemma exp_le_one_add_add_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + t + t ^ 2 := by
  have hb := Real.exp_bound (x := t) (n := 2) (by simpa [abs_of_nonneg ht0] using ht1)
    (by norm_num)
  norm_num [Finset.sum_range_succ, abs_of_nonneg ht0] at hb
  have hdiff := (le_abs_self (Real.exp t - (1 + t))).trans hb
  nlinarith [sq_nonneg t]

lemma negBin_base_le_exp {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    15 / (16 - Real.exp t) ≤ Real.exp (t / 15 + t ^ 2) := by
  let x : ℝ := (Real.exp t - 1) / 15
  have hexpLower : 1 ≤ Real.exp t := Real.one_le_exp ht0
  have hexpUpper : Real.exp t ≤ 1 + t + (3 / 4 : ℝ) * t ^ 2 := by
    have hb := Real.exp_bound (x := t) (n := 2)
      (by rw [abs_of_nonneg ht0]; linarith) (by norm_num)
    norm_num [Finset.sum_range_succ, abs_of_nonneg ht0] at hb
    have hdiff := (le_abs_self (Real.exp t - (1 + t))).trans hb
    linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have htSq : t ^ 2 ≤ t / 2 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht)]
  have hxlin : x ≤ t / 15 + t ^ 2 / 20 := by
    dsimp [x]
    linarith
  have hxtenth : x ≤ t / 10 := by nlinarith
  have hxsmall : x ≤ 1 / 20 := by nlinarith
  have hden : 0 < 1 - x := by nlinarith
  have hxsq : x ^ 2 ≤ t ^ 2 / 100 := by nlinarith [sq_nonneg (t / 10 - x)]
  have hquad : x ^ 2 / (1 - x) ≤ t ^ 2 / 95 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hxsmall), hxsq]
  have hfrac : x / (1 - x) ≤ t / 15 + t ^ 2 := by
    calc
      x / (1 - x) = x + x ^ 2 / (1 - x) := by
        field_simp
        ring
      _ ≤ (t / 15 + t ^ 2 / 20) + t ^ 2 / 95 := add_le_add hxlin hquad
      _ ≤ t / 15 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hbase : 15 / (16 - Real.exp t) = 1 + x / (1 - x) := by
    have hdEq : 16 - Real.exp t = 15 * (1 - x) := by
      dsimp [x]
      ring
    rw [hdEq]
    field_simp
    ring
  rw [hbase]
  simpa only [add_comm] using
    (add_le_add_left hfrac 1).trans (Real.add_one_le_exp _)

lemma negBin_base_neg_le_exp {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    15 / (16 - Real.exp (-t)) ≤ Real.exp (-t / 15 + t ^ 2) := by
  let y : ℝ := (Real.exp (-t) - 1) / 15
  have hexpLower : 1 - t ≤ Real.exp (-t) := by
    nlinarith [Real.add_one_le_exp (-t)]
  have hexpUpper : Real.exp (-t) ≤ 1 - t + (3 / 4 : ℝ) * t ^ 2 := by
    have hb := Real.exp_bound (x := -t) (n := 2)
      (by rw [abs_neg, abs_of_nonneg ht0]; linarith) (by norm_num)
    norm_num [Finset.sum_range_succ, abs_of_nonneg ht0] at hb
    have hdiff := (le_abs_self (Real.exp (-t) - (1 - t))).trans hb
    nlinarith [sq_nonneg t]
  have hy0 : y ≤ 0 := by
    dsimp [y]
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0)
    linarith
  have hylower : -t / 15 ≤ y := by dsimp [y]; linarith
  have hyupper : y ≤ -t / 15 + t ^ 2 / 20 := by dsimp [y]; linarith
  have hden : 0 < 1 - y := by linarith
  have hysq : y ^ 2 ≤ t ^ 2 / 225 := by
    have hp : 0 ≤ (y + t / 15) * (t / 15 - y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hquad : y ^ 2 / (1 - y) ≤ t ^ 2 / 225 := by
    calc
      y ^ 2 / (1 - y) ≤ y ^ 2 := by
        apply (div_le_iff₀ hden).2
        nlinarith [mul_nonneg (sq_nonneg y) (neg_nonneg.mpr hy0)]
      _ ≤ t ^ 2 / 225 := hysq
  have hfrac : y / (1 - y) ≤ -t / 15 + t ^ 2 := by
    calc
      y / (1 - y) = y + y ^ 2 / (1 - y) := by
        field_simp
        ring
      _ ≤ (-t / 15 + t ^ 2 / 20) + t ^ 2 / 225 := add_le_add hyupper hquad
      _ ≤ -t / 15 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hbase : 15 / (16 - Real.exp (-t)) = 1 + y / (1 - y) := by
    have hdEq : 16 - Real.exp (-t) = 15 * (1 - y) := by
      dsimp [y]
      ring
    rw [hdEq]
    field_simp
    ring
  rw [hbase]
  simpa only [add_comm] using
    (add_le_add_left hfrac 1).trans (Real.add_one_le_exp _)

lemma hasSum_negBinMass_mul_exp (i : ℕ) (hi : 1 ≤ i) {t : ℝ}
    (ht : Real.exp t < 16) :
    HasSum (fun j : ℕ ↦ negBinMass i j * Real.exp (t * j))
      ((15 / (16 - Real.exp t)) ^ i) := by
  have hr : ‖Real.exp t / (16 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.exp t / (16 : ℝ))]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 16)).2 ht
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (i - 1) hr).mul_left
    ((15 / 16 : ℝ) ^ i)
  have hfun :
      (fun j : ℕ ↦ negBinMass i j * Real.exp (t * j)) =
        (fun j : ℕ ↦ (15 / 16 : ℝ) ^ i *
          ((Nat.choose (j + (i - 1)) (i - 1) : ℝ) * (Real.exp t / 16) ^ j)) := by
    funext j
    have htop : i + j - 1 = j + (i - 1) := by omega
    have hchoose : Nat.choose (i + j - 1) j = Nat.choose (j + (i - 1)) (i - 1) := by
      rw [htop]
      exact Nat.choose_symm_add
    rw [negBinMass, hchoose, mul_comm t (j : ℝ), Real.exp_nat_mul]
    rw [pow_add]
    simp only [div_pow]
    field_simp
  have hs' : HasSum (fun j : ℕ ↦ negBinMass i j * Real.exp (t * j))
      ((15 / 16 : ℝ) ^ i * (1 / (1 - Real.exp t / 16) ^ (i - 1 + 1))) := by
    rw [hfun]
    exact hs
  have hiSub : i - 1 + 1 = i := by omega
  have hvalue :
      (15 / 16 : ℝ) ^ i * (1 / (1 - Real.exp t / 16) ^ (i - 1 + 1)) =
        (15 / (16 - Real.exp t)) ^ i := by
    rw [hiSub]
    have hd : 1 - Real.exp t / 16 = (16 - Real.exp t) / 16 := by ring
    rw [hd, div_pow, div_pow]
    field_simp
    ring
  rw [hvalue] at hs'
  exact hs'

noncomputable def negBinUpperTail (i : ℕ) (b : ℝ) : ℝ :=
  ∑' j : ℕ, if b ≤ (j : ℝ) then negBinMass i j else 0

noncomputable def negBinLowerTail (i : ℕ) (b : ℝ) : ℝ :=
  ∑' j : ℕ, if (j : ℝ) ≤ b then negBinMass i j else 0

lemma negBinMass_summable (i : ℕ) (hi : 1 ≤ i) :
    Summable (negBinMass i) := by
  have h := hasSum_negBinMass_mul_exp i hi (t := 0) (by norm_num)
  simpa using h.summable

/-- Chernoff moderate-deviation bound above the mean `i / 15`. -/
theorem negBinUpperTail_le_exp (i : ℕ) (hi : 1 ≤ i) (a : ℝ)
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    negBinUpperTail i ((i : ℝ) / 15 + a) ≤
      Real.exp (-(a ^ 2 / (4 * (i : ℝ)))) := by
  let t : ℝ := a / (2 * (i : ℝ))
  let b : ℝ := (i : ℝ) / 15 + a
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htHalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * i)).2
    nlinarith
  have hexp16 : Real.exp t < 16 := by
    have he := exp_le_one_add_add_sq ht0 (by linarith : t ≤ 1)
    have htsq : t ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    nlinarith
  have hm := hasSum_negBinMass_mul_exp i hi hexp16
  have hbase := negBin_base_le_exp ht0 htHalf
  have hbase0 : 0 ≤ 15 / (16 - Real.exp t) := by positivity
  have hpow : (15 / (16 - Real.exp t)) ^ i ≤
      (Real.exp (t / 15 + t ^ 2)) ^ i :=
    pow_le_pow_left₀ hbase0 hbase i
  have hweighted : Summable (fun j : ℕ ↦
      Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j))) :=
    hm.summable.mul_left _
  have htailSummable : Summable (fun j : ℕ ↦
      if b ≤ (j : ℝ) then negBinMass i j else 0) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ by
        split_ifs
        · exact negBinMass_nonneg i j
        · exact le_rfl)
      (fun j ↦ ?_) hweighted
    split_ifs with hj
    · have hweight : 1 ≤ Real.exp (-t * b) * Real.exp (t * j) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      calc
        negBinMass i j = negBinMass i j * 1 := by ring
        _ ≤ negBinMass i j *
            (Real.exp (-t * b) * Real.exp (t * j)) :=
          mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
        _ = Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by ring
    · exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
  calc
    negBinUpperTail i ((i : ℝ) / 15 + a) =
        ∑' j : ℕ, if b ≤ (j : ℝ) then negBinMass i j else 0 := by rfl
    _ ≤ ∑' j : ℕ,
        Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by
      apply Summable.tsum_le_tsum
        (fun j ↦ ?_) htailSummable hweighted
      split_ifs with hj
      · have hweight : 1 ≤ Real.exp (-t * b) * Real.exp (t * j) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        calc
          negBinMass i j = negBinMass i j * 1 := by ring
          _ ≤ negBinMass i j *
              (Real.exp (-t * b) * Real.exp (t * j)) :=
            mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
          _ = Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by ring
      · exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
    _ = Real.exp (-t * b) * (15 / (16 - Real.exp t)) ^ i :=
      (hm.mul_left _).tsum_eq
    _ ≤ Real.exp (-t * b) * (Real.exp (t / 15 + t ^ 2)) ^ i :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-(a ^ 2 / (4 * (i : ℝ)))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp [t, b]
      field_simp
      ring

/-- Chernoff moderate-deviation bound below the mean `i / 15`. -/
theorem negBinLowerTail_le_exp (i : ℕ) (hi : 1 ≤ i) (a : ℝ)
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    negBinLowerTail i ((i : ℝ) / 15 - a) ≤
      Real.exp (-(a ^ 2 / (4 * (i : ℝ)))) := by
  let t : ℝ := a / (2 * (i : ℝ))
  let b : ℝ := (i : ℝ) / 15 - a
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htHalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * i)).2
    nlinarith
  have hexp16 : Real.exp (-t) < 16 := by
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0)
    linarith
  have hm := hasSum_negBinMass_mul_exp i hi hexp16
  have hbase := negBin_base_neg_le_exp ht0 htHalf
  have hbase0 : 0 ≤ 15 / (16 - Real.exp (-t)) := by positivity
  have hpow : (15 / (16 - Real.exp (-t))) ^ i ≤
      (Real.exp (-t / 15 + t ^ 2)) ^ i :=
    pow_le_pow_left₀ hbase0 hbase i
  have hweighted : Summable (fun j : ℕ ↦
      Real.exp (t * b) * (negBinMass i j * Real.exp ((-t) * j))) :=
    hm.summable.mul_left _
  have htailSummable : Summable (fun j : ℕ ↦
      if (j : ℝ) ≤ b then negBinMass i j else 0) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ by
        split_ifs
        · exact negBinMass_nonneg i j
        · exact le_rfl)
      (fun j ↦ ?_) hweighted
    split_ifs with hj
    · have hweight : 1 ≤ Real.exp (t * b) * Real.exp ((-t) * j) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      calc
        negBinMass i j = negBinMass i j * 1 := by ring
        _ ≤ negBinMass i j *
            (Real.exp (t * b) * Real.exp ((-t) * j)) :=
          mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
        _ = Real.exp (t * b) * (negBinMass i j * Real.exp ((-t) * j)) := by ring
    · exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
  calc
    negBinLowerTail i ((i : ℝ) / 15 - a) =
        ∑' j : ℕ, if (j : ℝ) ≤ b then negBinMass i j else 0 := by rfl
    _ ≤ ∑' j : ℕ,
        Real.exp (t * b) * (negBinMass i j * Real.exp ((-t) * j)) := by
      apply Summable.tsum_le_tsum
        (fun j ↦ ?_) htailSummable hweighted
      split_ifs with hj
      · have hweight : 1 ≤ Real.exp (t * b) * Real.exp ((-t) * j) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        calc
          negBinMass i j = negBinMass i j * 1 := by ring
          _ ≤ negBinMass i j *
              (Real.exp (t * b) * Real.exp ((-t) * j)) :=
            mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
          _ = Real.exp (t * b) * (negBinMass i j * Real.exp ((-t) * j)) := by ring
      · exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
    _ = Real.exp (t * b) * (15 / (16 - Real.exp (-t))) ^ i :=
      (hm.mul_left _).tsum_eq
    _ ≤ Real.exp (t * b) * (Real.exp (-t / 15 + t ^ 2)) ^ i :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-(a ^ 2 / (4 * (i : ℝ)))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp [t, b]
      field_simp
      ring

/-- Two-sided form used for moderate deviations: outside the real interval
`[i/15-a, i/15+a]`, the sum of the two tail masses is exponentially small. -/
theorem negBin_twoSidedTail_le_two_mul_exp (i : ℕ) (hi : 1 ≤ i) (a : ℝ)
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    negBinLowerTail i ((i : ℝ) / 15 - a) +
        negBinUpperTail i ((i : ℝ) / 15 + a) ≤
      2 * Real.exp (-(a ^ 2 / (4 * (i : ℝ)))) := by
  nlinarith [negBinLowerTail_le_exp i hi a ha0 hai,
    negBinUpperTail_le_exp i hi a ha0 hai]

end Erdos1166.HLOZUrn
