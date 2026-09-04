/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of the negative resolution of Erdős Problem 664.

The construction is the random half-line construction of Alon, Kalai,
Matoušek, and Meshulam.  We use the affine part of a Desarguesian projective
plane; this has the same linear-size, codegree-one, and incidence-regularity
properties needed by the argument.
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Erdos664

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A set meeting every member of a finite set family. -/
def HitsAll {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (B : Finset α) : Prop :=
  ∀ i, (B ∩ A i).Nonempty

/-- A family is linear when two distinct members meet in at most one point. -/
def LinearFamily {ι α : Type*} [DecidableEq α]
    (A : ι → Finset α) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → #(A i ∩ A j) ≤ 1

/-- The precise fixed-bound counterexample assertion used to negate the question. -/
def CounterexampleAt (K : ℕ) : Prop :=
  ∃ n m : ℕ, ∃ A : Fin m → Finset (Fin n),
    (∀ i, (2 / 5 : ℝ) * Real.sqrt n < #(A i)) ∧
    LinearFamily A ∧
    ∀ B : Finset (Fin n), HitsAll A B → ∃ i, K < #(B ∩ A i)

/-- The positive assertion in Problem 664, with an explicit uniform bound. -/
def HasUniformTransversalBound (c : ℝ) (K : ℕ) : Prop :=
  ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
    (∀ i, c * Real.sqrt n < #(A i)) →
    LinearFamily A →
    ∃ B : Finset (Fin n), HitsAll A B ∧ ∀ i, #(B ∩ A i) ≤ K

/-- Lines in an affine plane: a slope/intercept pair, or a vertical coordinate. -/
abbrev AffineLine (F : Type*) := (F × F) ⊕ F

/-- The points on an affine line over a finite field. -/
noncomputable def affineLinePoints {F : Type*} [Field F] [Fintype F]
    (l : AffineLine F) : Finset (F × F) :=
  match l with
  | Sum.inl (a, b) => Finset.univ.image fun x => (x, a * x + b)
  | Sum.inr c => Finset.univ.image fun y => (c, y)

@[simp] lemma mem_affineLinePoints_nonvertical {F : Type*} [Field F] [Fintype F]
    (a b x y : F) :
    (x, y) ∈ affineLinePoints (Sum.inl (a, b) : AffineLine F) ↔ y = a * x + b := by
  simp [affineLinePoints, eq_comm]

@[simp] lemma mem_affineLinePoints_vertical {F : Type*} [Field F] [Fintype F]
    (c x y : F) :
    (x, y) ∈ affineLinePoints (Sum.inr c : AffineLine F) ↔ x = c := by
  simp [affineLinePoints, eq_comm]

lemma card_affineLinePoints {F : Type*} [Field F] [Fintype F]
    (l : AffineLine F) : #(affineLinePoints l) = Fintype.card F := by
  cases l with
  | inl ab =>
      rcases ab with ⟨a, b⟩
      rw [affineLinePoints, Finset.card_image_of_injective]
      · simp
      · intro x y h
        exact congr_arg Prod.fst h
  | inr c =>
      rw [affineLinePoints, Finset.card_image_of_injective]
      · simp
      · intro x y h
        exact congr_arg Prod.snd h

/-- Distinct affine lines contain at most one common point. -/
lemma affineLinePoints_inter_card_le_one {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    {l k : AffineLine F} (hlk : l ≠ k) :
    #(affineLinePoints l ∩ affineLinePoints k) ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  rcases l with (⟨a, b⟩ | c) <;> rcases k with (⟨a', b'⟩ | c')
  · simp only [Finset.mem_inter, mem_affineLinePoints_nonvertical] at hp hq
    have hx : x₁ = x₂ := by
      by_contra hne
      have hmul : (a - a') * (x₁ - x₂) = 0 := by
        rcases hp with ⟨h11, h12⟩
        rcases hq with ⟨h21, h22⟩
        linear_combination -h11 + h12 + h21 - h22
      have haa : a = a' := sub_eq_zero.mp
        ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hne))
      have hbb : b = b' := by
        rcases hp with ⟨h11, h12⟩
        rw [← haa] at h12
        linear_combination -h11 + h12
      exact hlk (by simp [haa, hbb])
    rcases hp with ⟨h11, -⟩
    rcases hq with ⟨h21, -⟩
    apply Prod.ext hx
    rw [h11, h21, hx]
  · simp only [Finset.mem_inter, mem_affineLinePoints_nonvertical,
      mem_affineLinePoints_vertical] at hp hq
    apply Prod.ext (hp.2.trans hq.2.symm)
    rw [hp.1, hq.1, hp.2, hq.2]
  · simp only [Finset.mem_inter, mem_affineLinePoints_vertical,
      mem_affineLinePoints_nonvertical] at hp hq
    apply Prod.ext (hp.1.trans hq.1.symm)
    rw [hp.2, hq.2, hp.1, hq.1]
  · simp only [Finset.mem_inter, mem_affineLinePoints_vertical] at hp hq
    have hcc : c = c' := hp.1.symm.trans hp.2
    exact False.elim (hlk (by simp [hcc]))

/-- The affine lines through a point, explicitly parametrized by slope plus the vertical line. -/
noncomputable def affineLinesThrough {F : Type*} [Field F] [Fintype F]
    (p : F × F) : Finset (AffineLine F) :=
  (Finset.univ.image fun a => Sum.inl (a, p.2 - a * p.1)) ∪ {Sum.inr p.1}

@[simp] lemma mem_affineLinesThrough_iff {F : Type*} [Field F] [Fintype F]
    (p : F × F) (l : AffineLine F) :
    l ∈ affineLinesThrough p ↔ p ∈ affineLinePoints l := by
  rcases p with ⟨x, y⟩
  rcases l with (⟨a, b⟩ | c)
  · rw [mem_affineLinePoints_nonvertical, affineLinesThrough, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨a', _, ha'⟩ := Finset.mem_image.mp h
        simp only [Sum.inl.injEq, Prod.mk.injEq] at ha'
        rcases ha' with ⟨rfl, hb⟩
        linear_combination hb
      · exact (Sum.inl_ne_inr (Finset.mem_singleton.mp h)).elim
    · intro h
      apply Or.inl
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
      simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]
      linear_combination h
  · simp [affineLinesThrough, eq_comm]

lemma card_affineLinesThrough {F : Type*} [Field F] [Fintype F]
    (p : F × F) : #(affineLinesThrough p) = Fintype.card F + 1 := by
  rw [affineLinesThrough, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      simpa using congr_arg (fun z : AffineLine F => z.elim Prod.fst id) h
  · rw [Finset.disjoint_left]
    intro l hl hsingle
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hl
    simp at hsingle
    obtain ⟨a, rfl⟩ := hl
    contradiction

lemma card_affinePointType (F : Type*) [Fintype F] :
    Fintype.card (F × F) = Fintype.card F ^ 2 := by
  simp [pow_two]

lemma card_affineLineType (F : Type*) [Fintype F] :
    Fintype.card (AffineLine F) = Fintype.card F ^ 2 + Fintype.card F := by
  simp [pow_two]

noncomputable def incidenceSet {L P : Type*} [Fintype L] [DecidableEq P]
    (A : L → Finset P) (p : P) : Finset L :=
  Finset.univ.filter fun l => p ∈ A l

lemma sum_card_inter_eq_sum_degrees {L P : Type*} [Fintype L]
    [DecidableEq P] (A : L → Finset P) (T : Finset P) :
    ∑ l, #(T ∩ A l) =
      ∑ p ∈ T, #(Finset.univ.filter fun l => p ∈ A l) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp

lemma incidenceSet_affineLinePoints {F : Type*} [Field F] [Fintype F]
    (p : F × F) :
    incidenceSet (fun l : AffineLine F => affineLinePoints l) p =
      affineLinesThrough p := by
  ext l
  simp [incidenceSet, mem_affineLinesThrough_iff]

lemma sum_affineLine_inter_card {F : Type*} [Field F] [Fintype F]
    (T : Finset (F × F)) :
    ∑ l : AffineLine F, #(T ∩ affineLinePoints l) =
      (Fintype.card F + 1) * T.card := by
  rw [sum_card_inter_eq_sum_degrees]
  calc
    (∑ p ∈ T, #(Finset.univ.filter fun l : AffineLine F =>
        p ∈ affineLinePoints l)) =
        ∑ p ∈ T, #(affineLinesThrough p) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext l
      simp [mem_affineLinesThrough_iff]
    _ = _ := by simp [card_affineLinesThrough, Nat.mul_comm]

noncomputable def sparseAffineLines {F : Type*} [Field F] [Fintype F]
    (T : Finset (F × F)) (u : ℕ) : Finset (AffineLine F) :=
  Finset.univ.filter fun l => #(T ∩ affineLinePoints l) ≤ 16 * u

lemma sparseAffineLines_many {F : Type*} [Field F] [Fintype F]
    (T : Finset (F × F)) (u : ℕ)
    (hT : T.card ≤ 4 * Fintype.card F * u) :
    Fintype.card (AffineLine F) ≤ 2 * #(sparseAffineLines T u) := by
  let q := Fintype.card F
  let S := sparseAffineLines T u
  let D : Finset (AffineLine F) :=
    Finset.univ.filter fun l => 16 * u < #(T ∩ affineLinePoints l)
  have hpart : S.card + D.card = Fintype.card (AffineLine F) := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext l
      simp [S, D, sparseAffineLines]
      omega
    · rw [Finset.disjoint_left]
      intro l hlS hlD
      simp [S, D, sparseAffineLines] at hlS hlD
      omega
  have hDsum : (16 * u + 1) * D.card ≤
      ∑ l : AffineLine F, #(T ∩ affineLinePoints l) := by
    calc
      (16 * u + 1) * D.card = ∑ _l ∈ D, (16 * u + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ l ∈ D, #(T ∩ affineLinePoints l) := by
        apply Finset.sum_le_sum
        intro l hl
        simp [D] at hl
        omega
      _ ≤ ∑ l : AffineLine F, #(T ∩ affineLinePoints l) := by
        exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have htotal :
      ∑ l : AffineLine F, #(T ∩ affineLinePoints l) ≤ 4 * q * (q + 1) * u := by
    rw [sum_affineLine_inter_card]
    dsimp [q] at hT ⊢
    nlinarith
  have hm : Fintype.card (AffineLine F) = q * (q + 1) := by
    simp [q]
    ring
  by_contra hSsmall
  change ¬Fintype.card (AffineLine F) ≤ 2 * S.card at hSsmall
  have hDlarge : Fintype.card (AffineLine F) < 2 * D.card := by omega
  have hq : 0 < q := Fintype.card_pos
  have hu : 0 < 16 * u + 1 := by omega
  have hDr : (Fintype.card (AffineLine F) : ℝ) < 2 * D.card := by exact_mod_cast hDlarge
  have hDs : ((16 * u + 1) * D.card : ℕ) ≤ 4 * q * (q + 1) * u :=
    hDsum.trans htotal
  have hDsr : ((16 * u + 1) * D.card : ℝ) ≤ 4 * q * (q + 1) * u := by
    exact_mod_cast hDs
  have hmr : (Fintype.card (AffineLine F) : ℝ) = q * (q + 1) := by
    exact_mod_cast hm
  nlinarith

/-! ### Fair product measures and a reusable lower-tail estimate -/

noncomputable def fairBitMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairBitMeasure := by
  rw [fairBitMeasure]
  infer_instance

noncomputable def fairVectorMeasure (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ : ι => fairBitMeasure

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (fairVectorMeasure ι) := by
  rw [fairVectorMeasure]
  infer_instance

@[simp] lemma fairBitMeasure_singleton (b : Bool) :
    fairBitMeasure {b} = (1 : ℝ≥0∞) / 2 := by
  rw [fairBitMeasure,
    PMF.toMeasure_apply (PMF.uniformOfFintype Bool) (MeasurableSet.singleton b)]
  simp [PMF.uniformOfFintype_apply]

lemma fairVectorMeasure_coord {ι : Type*} [Fintype ι] (i : ι) (b : Bool) :
    fairVectorMeasure ι {ω | ω i = b} = (1 : ℝ≥0∞) / 2 := by
  change fairVectorMeasure ι (Function.eval i ⁻¹' {b}) = _
  calc
    fairVectorMeasure ι (Function.eval i ⁻¹' {b}) =
        (fairVectorMeasure ι).map (Function.eval i) {b} := by
      rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton b)]
    _ = fairBitMeasure {b} := by
      rw [fairVectorMeasure,
        (measurePreserving_eval (μ := fun _ : ι => fairBitMeasure) i).map_eq]
    _ = _ := fairBitMeasure_singleton b

lemma fairVector_iIndep_eval {ι : Type*} [Fintype ι] :
    iIndepFun (fun i : ι => Function.eval i) (fairVectorMeasure ι) := by
  rw [fairVectorMeasure]
  exact iIndepFun_pi (μ := fun _ : ι => fairBitMeasure)
    (X := fun _ b => b) (by fun_prop)

/-- The probability that all coordinates in `s` are false is exactly `2⁻ˢ`. -/
lemma fairVector_measure_all_false {ι : Type*} [Fintype ι] (s : Finset ι) :
    fairVectorMeasure ι (⋂ i ∈ s, Function.eval i ⁻¹' ({false} : Set Bool)) =
      ((1 : ℝ≥0∞) / 2) ^ s.card := by
  rw [(fairVector_iIndep_eval (ι := ι)).measure_inter_preimage_eq_mul s
    (sets := fun _ => ({false} : Set Bool)) (by simp)]
  calc
    (∏ i ∈ s, fairVectorMeasure ι (Function.eval i ⁻¹' ({false} : Set Bool))) =
        ∏ _i ∈ s, ((1 : ℝ≥0∞) / 2) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact fairVectorMeasure_coord i false
    _ = _ := by simp

def rowHits {ι : Type*} (s : Finset ι) (ω : ι → Bool) : Prop :=
  ∃ i ∈ s, ω i = true

lemma rowHits_compl {ι : Type*} (s : Finset ι) :
    {ω : ι → Bool | rowHits s ω}ᶜ =
      ⋂ i ∈ s, Function.eval i ⁻¹' ({false} : Set Bool) := by
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, rowHits, Set.mem_iInter,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h i hi
    by_contra hfalse
    have htrue : ω i = true := Bool.eq_true_of_not_eq_false hfalse
    exact h ⟨i, hi, htrue⟩
  · intro h hhit
    obtain ⟨i, hi, htrue⟩ := hhit
    simpa [htrue] using h i hi

lemma fairVector_measure_rowHits {ι : Type*} [Fintype ι] (s : Finset ι) :
    (fairVectorMeasure ι).real {ω | rowHits s ω} =
      1 - ((1 : ℝ) / 2) ^ s.card := by
  have hmeas : MeasurableSet {ω : ι → Bool | rowHits s ω} :=
    MeasurableSet.of_discrete
  have hc := measureReal_compl (μ := fairVectorMeasure ι) hmeas
  have hfalse : (fairVectorMeasure ι).real {ω : ι → Bool | rowHits s ω}ᶜ =
      ((1 : ℝ) / 2) ^ s.card := by
    rw [rowHits_compl, Measure.real, fairVector_measure_all_false]
    norm_num
  rw [hfalse] at hc
  have huniv : (fairVectorMeasure ι).real Set.univ = 1 := by simp
  rw [huniv] at hc
  linarith

def rademacher {ι : Type*} (i : ι) (ω : ι → Bool) : ℝ :=
  if ω i = true then 1 else -1

lemma fairBit_integral_rademacher :
    ∫ b : Bool, (if b then (1 : ℝ) else -1) ∂fairBitMeasure = 0 := by
  rw [fairBitMeasure, PMF.integral_eq_sum]
  norm_num [PMF.uniformOfFintype_apply]

lemma fairVector_integral_rademacher {ι : Type*} [Fintype ι] (i : ι) :
    ∫ ω, rademacher i ω ∂fairVectorMeasure ι = 0 := by
  rw [fairVectorMeasure]
  exact (MeasureTheory.integral_comp_eval (i := i) (μ := fun _ : ι => fairBitMeasure)
    (f := fun b : Bool => if b then (1 : ℝ) else -1) (by fun_prop)).trans
      fairBit_integral_rademacher

lemma fairVector_iIndep_rademacher {ι : Type*} [Fintype ι] :
    iIndepFun (fun i : ι => rademacher i) (fairVectorMeasure ι) := by
  rw [fairVectorMeasure]
  change iIndepFun (fun i ω => if ω i = true then (1 : ℝ) else -1)
    (Measure.pi fun _ : ι => fairBitMeasure)
  exact iIndepFun_pi (μ := fun _ : ι => fairBitMeasure)
    (X := fun _ b => if b = true then (1 : ℝ) else -1) (by fun_prop)

lemma fairVector_subgaussian_rademacher {ι : Type*} [Fintype ι] (i : ι) :
    HasSubgaussianMGF (rademacher i) 1 (fairVectorMeasure ι) := by
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := fairVectorMeasure ι) (X := rademacher i) (a := (-1 : ℝ)) (b := 1)
    (by fun_prop) (Filter.Eventually.of_forall fun ω => by
      simp only [rademacher]
      split <;> norm_num) (fairVector_integral_rademacher i) using 1; norm_num

lemma fairVector_sum_le_neg {ι : Type*} [Fintype ι] (s : Finset ι)
    (t : ℝ) (ht : 0 ≤ t) :
    (fairVectorMeasure ι).real {ω | ∑ i ∈ s, rademacher i ω ≤ -t} ≤
      Real.exp (-t ^ 2 / (2 * s.card)) := by
  let X : ι → (ι → Bool) → ℝ := fun i ω => -rademacher i ω
  have h_indep : iIndepFun X (fairVectorMeasure ι) := by
    have h := (fairVector_iIndep_rademacher (ι := ι)).comp
      (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
    exact h.congr (fun i => Filter.Eventually.of_forall fun ω => by rfl)
  have h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) 1 (fairVectorMeasure ι) := by
    intro i hi
    exact (fairVector_subgaussian_rademacher (ι := ι) i).neg.congr
      (Filter.Eventually.of_forall fun ω => by rfl)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun h_indep
    (c := fun _ => (1 : ℝ≥0)) (s := s) h_subG
  have h := hsum.measure_ge_le ht
  have hevent :
      {ω | ∑ i ∈ s, rademacher i ω ≤ -t} =
        {ω | t ≤ ∑ i ∈ s, X i ω} := by
    ext ω
    change (∑ i ∈ s, rademacher i ω) ≤ -t ↔ t ≤ ∑ i ∈ s, X i ω
    rw [show (∑ i ∈ s, X i ω) = -(∑ i ∈ s, rademacher i ω) by simp [X]]
    constructor <;> intro hω <;> linarith
  rw [hevent]
  convert h using 1; norm_num

lemma sum_rademacher_eq_two_card_sub_card {ι : Type*}
    (s : Finset ι) (ω : ι → Bool) :
    ∑ i ∈ s, rademacher i ω =
      2 * (#(s.filter fun i => ω i = true) : ℝ) - s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hω : ω a = true
      · have hf : (insert a s).filter (fun i => ω i = true) =
            insert a (s.filter fun i => ω i = true) := by
          ext i
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨hi, hit⟩
            exact hi.imp_right fun his => ⟨his, hit⟩
          · rintro (rfl | ⟨his, hit⟩)
            · exact ⟨Or.inl rfl, hω⟩
            · exact ⟨Or.inr his, hit⟩
        have haf : a ∉ s.filter (fun i => ω i = true) := by simp [ha]
        rw [sum_insert ha, rademacher, if_pos hω, ih, hf,
          Finset.card_insert_of_notMem haf, Finset.card_insert_of_notMem ha]
        push_cast
        ring
      · have hf : (insert a s).filter (fun i => ω i = true) =
            s.filter fun i => ω i = true := by
          ext i
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨hi, hit⟩
            rcases hi with rfl | his
            · exact False.elim (hω hit)
            · exact ⟨his, hit⟩
          · rintro ⟨his, hit⟩
            exact ⟨Or.inr his, hit⟩
        rw [sum_insert ha, rademacher, if_neg hω, ih, hf,
          Finset.card_insert_of_notMem ha]
        push_cast
        ring

lemma fairVector_card_filter_lower_tail {ι : Type*} [Fintype ι]
    (s : Finset ι) :
    (fairVectorMeasure ι).real
        {ω | (#(s.filter fun i => ω i = true) : ℝ) ≤ (2 / 5 : ℝ) * s.card} ≤
      Real.exp (-(s.card : ℝ) / 50) := by
  have hsub :
      {ω | (#(s.filter fun i => ω i = true) : ℝ) ≤ (2 / 5 : ℝ) * s.card} ⊆
        {ω | ∑ i ∈ s, rademacher i ω ≤ -((s.card : ℝ) / 5)} := by
    intro ω hω
    change (#(s.filter fun i => ω i = true) : ℝ) ≤ (2 / 5 : ℝ) * s.card at hω
    change (∑ i ∈ s, rademacher i ω) ≤ -((s.card : ℝ) / 5)
    rw [sum_rademacher_eq_two_card_sub_card]
    linarith
  refine (measureReal_mono hsub).trans ?_
  refine (fairVector_sum_le_neg s ((s.card : ℝ) / 5) (by positivity)).trans_eq ?_
  by_cases hs : s.card = 0
  · simp [hs]
  · field_simp
    ring_nf

/-! ### Random subfamilies of a finite incidence structure -/

noncomputable def fairMatrixMeasure (L P : Type*) [Fintype L] [Fintype P] :
    Measure (L → P → Bool) :=
  Measure.pi fun _ : L => fairVectorMeasure P

instance (L P : Type*) [Fintype L] [Fintype P] :
    IsProbabilityMeasure (fairMatrixMeasure L P) := by
  rw [fairMatrixMeasure]
  infer_instance

lemma fairMatrix_iIndep_rows (L P : Type*) [Fintype L] [Fintype P] :
    iIndepFun (fun l : L => Function.eval l) (fairMatrixMeasure L P) := by
  rw [fairMatrixMeasure]
  exact iIndepFun_pi (μ := fun _ : L => fairVectorMeasure P)
    (X := fun _ row => row) (by fun_prop)

lemma fairMatrixMeasure_row {L P : Type*} [Fintype L] [Fintype P]
    (l : L) {E : Set (P → Bool)} (hE : MeasurableSet E) :
    fairMatrixMeasure L P (Function.eval l ⁻¹' E) = fairVectorMeasure P E := by
  calc
    fairMatrixMeasure L P (Function.eval l ⁻¹' E) =
        (fairMatrixMeasure L P).map (Function.eval l) E := by
      rw [Measure.map_apply (by fun_prop) hE]
    _ = fairVectorMeasure P E := by
      rw [fairMatrixMeasure,
        (measurePreserving_eval (μ := fun _ : L => fairVectorMeasure P) l).map_eq]

def matrixRademacher {L P : Type*} (p : P) (l : L)
    (ω : L → P → Bool) : ℝ :=
  rademacher p (ω l)

lemma fairMatrix_iIndep_rademacher {L P : Type*} [Fintype L] [Fintype P]
    (p : P) :
    iIndepFun (fun l : L => matrixRademacher p l) (fairMatrixMeasure L P) := by
  have h := (fairMatrix_iIndep_rows L P).comp
    (mγ := fun _ => Real.measurableSpace)
    (fun _ : L => (rademacher p : (P → Bool) → ℝ)) (fun _ => by fun_prop)
  exact h.congr (fun l => Filter.Eventually.of_forall fun ω => by rfl)

lemma fairMatrix_integral_rademacher {L P : Type*} [Fintype L] [Fintype P]
    (p : P) (l : L) :
    ∫ ω, matrixRademacher p l ω ∂fairMatrixMeasure L P = 0 := by
  rw [fairMatrixMeasure]
  exact (MeasureTheory.integral_comp_eval (i := l)
    (μ := fun _ : L => fairVectorMeasure P) (f := rademacher p)
    (by fun_prop)).trans (fairVector_integral_rademacher p)

lemma fairMatrix_subgaussian_rademacher {L P : Type*} [Fintype L] [Fintype P]
    (p : P) (l : L) :
    HasSubgaussianMGF (matrixRademacher p l) 1 (fairMatrixMeasure L P) := by
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := fairMatrixMeasure L P) (X := matrixRademacher p l)
    (a := (-1 : ℝ)) (b := 1) (by fun_prop)
    (Filter.Eventually.of_forall fun ω => by
      simp only [matrixRademacher, rademacher]
      split <;> norm_num)
    (fairMatrix_integral_rademacher p l) using 1; norm_num

lemma fairMatrix_sum_le_neg {L P : Type*} [Fintype L] [Fintype P]
    (p : P) (s : Finset L) (t : ℝ) (ht : 0 ≤ t) :
    (fairMatrixMeasure L P).real
        {ω | ∑ l ∈ s, matrixRademacher p l ω ≤ -t} ≤
      Real.exp (-t ^ 2 / (2 * s.card)) := by
  let X : L → (L → P → Bool) → ℝ := fun l ω => -matrixRademacher p l ω
  have h_indep : iIndepFun X (fairMatrixMeasure L P) := by
    have h := (fairMatrix_iIndep_rademacher (L := L) p).comp
      (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
    exact h.congr (fun l => Filter.Eventually.of_forall fun ω => by rfl)
  have h_subG : ∀ l ∈ s, HasSubgaussianMGF (X l) 1 (fairMatrixMeasure L P) := by
    intro l hl
    exact (fairMatrix_subgaussian_rademacher p l).neg.congr
      (Filter.Eventually.of_forall fun ω => by rfl)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun h_indep
    (c := fun _ => (1 : ℝ≥0)) (s := s) h_subG
  have h := hsum.measure_ge_le ht
  have hevent :
      {ω | ∑ l ∈ s, matrixRademacher p l ω ≤ -t} =
        {ω | t ≤ ∑ l ∈ s, X l ω} := by
    ext ω
    change (∑ l ∈ s, matrixRademacher p l ω) ≤ -t ↔ t ≤ ∑ l ∈ s, X l ω
    rw [show (∑ l ∈ s, X l ω) = -(∑ l ∈ s, matrixRademacher p l ω) by
      simp [X]]
    constructor <;> intro hω <;> linarith
  rw [hevent]
  convert h using 1; norm_num

lemma fairMatrix_card_filter_lower_tail {L P : Type*} [Fintype L] [Fintype P]
    (p : P) (s : Finset L) :
    (fairMatrixMeasure L P).real
        {ω | (#(s.filter fun l => ω l p = true) : ℝ) ≤ (1 / 4 : ℝ) * s.card} ≤
      Real.exp (-(s.card : ℝ) / 8) := by
  have hsub :
      {ω | (#(s.filter fun l => ω l p = true) : ℝ) ≤ (1 / 4 : ℝ) * s.card} ⊆
        {ω | ∑ l ∈ s, matrixRademacher p l ω ≤ -((s.card : ℝ) / 2)} := by
    intro ω hω
    change (#(s.filter fun l => ω l p = true) : ℝ) ≤ (1 / 4 : ℝ) * s.card at hω
    change (∑ l ∈ s, rademacher l (fun l => ω l p)) ≤ -((s.card : ℝ) / 2)
    rw [sum_rademacher_eq_two_card_sub_card]
    linarith
  refine (measureReal_mono hsub).trans ?_
  refine (fairMatrix_sum_le_neg p s ((s.card : ℝ) / 2) (by positivity)).trans_eq ?_
  by_cases hs : s.card = 0
  · simp [hs]
  · field_simp
    ring_nf

def rowsHit {L P : Type*} (A : L → Finset P) (T : Finset P)
    (S : Finset L) (ω : L → P → Bool) : Prop :=
  ∀ l ∈ S, rowHits (T ∩ A l) (ω l)

lemma rowsHit_event_eq {L P : Type*} (A : L → Finset P) (T : Finset P)
    (S : Finset L) :
    {ω : L → P → Bool | rowsHit A T S ω} =
      ⋂ l ∈ S, Function.eval l ⁻¹' {row | rowHits (T ∩ A l) row} := by
  ext ω
  simp [rowsHit]

lemma fairMatrix_measure_rowsHit {L P : Type*} [Fintype L] [Fintype P]
    (A : L → Finset P) (T : Finset P) (S : Finset L) :
    (fairMatrixMeasure L P).real {ω | rowsHit A T S ω} =
      ∏ l ∈ S, (1 - ((1 : ℝ) / 2) ^ #(T ∩ A l)) := by
  have hprod := (fairMatrix_iIndep_rows L P).measure_inter_preimage_eq_mul S
    (sets := fun l => {row | rowHits (T ∩ A l) row})
    (by intro l hl; exact MeasurableSet.of_discrete)
  rw [rowsHit_event_eq, Measure.real, hprod]
  simp only [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro l hl
  rw [fairMatrixMeasure_row l MeasurableSet.of_discrete]
  exact fairVector_measure_rowHits (T ∩ A l)

lemma half_pow_antitone {d r : ℕ} (hdr : d ≤ r) :
    ((1 : ℝ) / 2) ^ r ≤ ((1 : ℝ) / 2) ^ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdr
  rw [pow_add]
  have hk0 : 0 ≤ ((1 : ℝ) / 2) ^ k := by positivity
  have hk1 : ((1 : ℝ) / 2) ^ k ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd0 : 0 ≤ ((1 : ℝ) / 2) ^ d := by positivity
  nlinarith

lemma fairMatrix_affine_rowsHit_bound {F : Type*} [Field F] [Fintype F]
    (T : Finset (F × F)) (u : ℕ)
    (hT : T.card ≤ 4 * Fintype.card F * u) :
    (fairMatrixMeasure (AffineLine F) (F × F)).real
        {ω | rowsHit (fun l : AffineLine F => affineLinePoints l) T Finset.univ ω} ≤
      Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
        ((Fintype.card (AffineLine F) : ℝ) / 2)) := by
  let A : AffineLine F → Finset (F × F) := affineLinePoints
  let S := sparseAffineLines T u
  let a : ℝ := ((1 : ℝ) / 2) ^ (16 * u)
  let d₀ : AffineLine F → ℕ := fun l => #(T ∩ A l)
  let : DecidableEq (F × F) := Classical.decEq _
  let d : AffineLine F → ℕ := fun l => #(T ∩ A l)
  have hsubset :
      {ω | rowsHit A T Finset.univ ω} ⊆ {ω | rowsHit A T S ω} := by
    intro ω hω l hl
    exact hω l (by simp)
  calc
    (fairMatrixMeasure (AffineLine F) (F × F)).real
        {ω | rowsHit A T Finset.univ ω}
        ≤ (fairMatrixMeasure (AffineLine F) (F × F)).real
            {ω | rowsHit A T S ω} := measureReal_mono hsubset
    _ = ∏ l ∈ S, (1 - ((1 : ℝ) / 2) ^ d l) :=
      fairMatrix_measure_rowsHit A T S
    _ ≤ ∏ _l ∈ S, Real.exp (-a) := by
      apply Finset.prod_le_prod
      · intro l hl
        exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
      · intro l hl
        have hd : d l = d₀ l := by
          dsimp [d, d₀]
          congr 1
          ext x
          simp
        have hcard : d l ≤ 16 * u := by
          rw [hd]
          simpa [d₀, S, sparseAffineLines, A] using hl
        have hp := half_pow_antitone hcard
        have hexp := Real.add_one_le_exp (-a)
        dsimp [a] at hexp ⊢
        linarith
    _ = Real.exp (-a * S.card) := by
      simp only [Finset.prod_const]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-a * ((Fintype.card (AffineLine F) : ℝ) / 2)) := by
      apply Real.exp_le_exp.mpr
      have hmany := sparseAffineLines_many T u hT
      have hmanyR : (Fintype.card (AffineLine F) : ℝ) ≤ 2 * S.card := by
        exact_mod_cast hmany
      have ha : 0 ≤ a := by positivity
      nlinarith

noncomputable def functionRangeFinset {P : Type*} [DecidableEq P] {s : ℕ}
    (f : Fin s → P) : Finset P :=
  Finset.univ.image f

lemma card_functionRangeFinset_le {P : Type*} [DecidableEq P] {s : ℕ}
    (f : Fin s → P) : #(functionRangeFinset f) ≤ s := by
  rw [functionRangeFinset]
  exact (Finset.card_image_le.trans_eq (by simp))

lemma exists_subset_functionRangeFinset {P : Type*} [DecidableEq P] [Nonempty P]
    (T : Finset P) {s : ℕ} (hT : T.card ≤ s) :
    ∃ f : Fin s → P, T ⊆ functionRangeFinset f := by
  have hcard : Fintype.card T ≤ s := by simpa using hT
  let e : T ↪ Fin s :=
    (Fintype.equivFin T).toEmbedding.trans (Fin.castLEEmb hcard)
  let p₀ : P := Classical.choice ‹Nonempty P›
  let f : Fin s → P := fun k =>
    if h : ∃ x : T, e x = k then (Classical.choose h : T).1 else p₀
  refine ⟨f, ?_⟩
  intro p hp
  rw [functionRangeFinset, Finset.mem_image]
  let x : T := ⟨p, hp⟩
  refine ⟨e x, by simp, ?_⟩
  have hex : ∃ y : T, e y = e x := ⟨x, rfl⟩
  have hey : e (Classical.choose hex) = e x := Classical.choose_spec hex
  have hyx : Classical.choose hex = x := e.injective hey
  simp only [f, dif_pos hex, hyx, x]

lemma rowHits_mono {P : Type*} {S T : Finset P} (hST : S ⊆ T)
    {ω : P → Bool} (h : rowHits S ω) : rowHits T ω := by
  obtain ⟨p, hp, hω⟩ := h
  exact ⟨p, hST hp, hω⟩

def HasSmallTransversal {L P : Type*} [Fintype L] (A : L → Finset P) (s : ℕ)
    (ω : L → P → Bool) : Prop :=
  ∃ T : Finset P, T.card ≤ s ∧ rowsHit A T Finset.univ ω

lemma fairMatrix_affine_hasSmallTransversal_bound
    {F : Type*} [Field F] [Fintype F] (u : ℕ) :
    (fairMatrixMeasure (AffineLine F) (F × F)).real
        {ω | HasSmallTransversal (fun l : AffineLine F => affineLinePoints l)
          (4 * Fintype.card F * u) ω} ≤
      (Fintype.card (F × F) : ℝ) ^ (4 * Fintype.card F * u) *
        Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
          ((Fintype.card (AffineLine F) : ℝ) / 2)) := by
  let : DecidableEq (F × F) := Classical.decEq _
  let s := 4 * Fintype.card F * u
  let A : AffineLine F → Finset (F × F) := affineLinePoints
  have hsubset :
      {ω | HasSmallTransversal A s ω} ⊆
        ⋃ f : Fin s → F × F,
          {ω | rowsHit A (functionRangeFinset f) Finset.univ ω} := by
    intro ω hω
    obtain ⟨T, hTs, hhit⟩ := hω
    obtain ⟨f, hTf⟩ := exists_subset_functionRangeFinset T hTs
    simp only [Set.mem_iUnion]
    refine ⟨f, ?_⟩
    intro l hl
    obtain ⟨p, hp, hbit⟩ := hhit l hl
    refine ⟨p, ?_, hbit⟩
    simp only [Finset.mem_inter] at hp ⊢
    exact ⟨hTf hp.1, hp.2⟩
  calc
    (fairMatrixMeasure (AffineLine F) (F × F)).real
        {ω | HasSmallTransversal A s ω}
        ≤ (fairMatrixMeasure (AffineLine F) (F × F)).real
            (⋃ f : Fin s → F × F,
              {ω | rowsHit A (functionRangeFinset f) Finset.univ ω}) :=
          measureReal_mono hsubset
    _ ≤ ∑ _f : Fin s → F × F,
          Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
            ((Fintype.card (AffineLine F) : ℝ) / 2)) := by
      refine (measureReal_iUnion_fintype_le _).trans ?_
      apply Finset.sum_le_sum
      intro f hf
      apply fairMatrix_affine_rowsHit_bound (functionRangeFinset f) u
      simpa [s] using card_functionRangeFinset_le f
    _ = (Fintype.card (F × F) : ℝ) ^ s *
          Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
            ((Fintype.card (AffineLine F) : ℝ) / 2)) := by
      simp
    _ = _ := by rfl

end Erdos664
