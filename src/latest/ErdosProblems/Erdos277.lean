/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 277

Haight proved that integers with arbitrarily large abundancy can be chosen so
that their nontrivial divisors cannot be the distinct moduli of a covering
system.  The proof below uses the finite residual-density estimate of
Filaseta--Ford--Konyagin--Pomerance--Yu.

The mathematical proof and a map from its lemmas to this formalization are in
`tex/277.tex`.
-/

open scoped ArithmeticFunction.sigma BigOperators Pointwise

syntax (name := answerSyntax277) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- A finite covering system over a commutative semiring. -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = Set.univ
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

attribute [instance] CoveringSystem.fintypeIndex

/-- A covering system whose modulus ideals are pairwise distinct. -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R]
    extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace Erdos277

noncomputable section

open MeasureTheory ProbabilityTheory Set

attribute [local instance] Classical.propDecidable

/-! ## The finite residual-density inequality -/

/-- The complement of the union of a finite family of events. -/
def residual {Ω ι : Type*} (s : Finset ι) (E : ι → Set Ω) : Set Ω :=
  (⋃ i ∈ s, E i)ᶜ

@[simp]
lemma residual_empty {Ω ι : Type*} (E : ι → Set Ω) : residual (∅ : Finset ι) E = Set.univ := by
  simp [residual]

lemma residual_insert {Ω ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (E : ι → Set Ω) :
    residual (insert a s) E = residual s E \ E a := by
  ext x
  simp [residual, and_comm]

/-- A finite family of events with a finite coordinate support for each event. -/
structure CylinderFamily (Ω κ ι : Type*) where
  event : ι → Set Ω
  support : ι → Finset κ

/-- The sum of products of probabilities over dependent unordered pairs. -/
def dependencyError {Ω κ ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] [DecidableEq κ]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) (s : Finset ι) : ℝ :=
  ∑ t ∈ s.powersetCard 2,
    if ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ ¬Disjoint (C.support i) (C.support j) then
      ∏ i ∈ t, μ.real (C.event i)
    else 0

/-- Product of the individual residual probabilities. -/
def independentResidual {Ω κ ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) (s : Finset ι) : ℝ :=
  ∏ i ∈ s, (1 - μ.real (C.event i))

/-- Recursive version of the dependency error, convenient for induction. -/
def dependencyErrorList {Ω κ ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) : List ι → ℝ
  | [] => 0
  | a :: l =>
      dependencyErrorList C μ l +
        μ.real (C.event a) *
          ∑ b ∈ l.toFinset.filter (fun b => ¬Disjoint (C.support b) (C.support a)),
            μ.real (C.event b)

/-- Recursive version of the product of individual residual probabilities. -/
def independentResidualList {Ω κ ι : Type*} [MeasurableSpace Ω]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) : List ι → ℝ
  | [] => 1
  | a :: l => (1 - μ.real (C.event a)) * independentResidualList C μ l

lemma residual_mono {Ω ι : Type*} [DecidableEq ι] {s t : Finset ι}
    (E : ι → Set Ω) (hst : s ⊆ t) : residual t E ⊆ residual s E := by
  intro x hx
  simp only [residual, mem_compl_iff, mem_iUnion, not_exists] at hx ⊢
  intro i hi
  exact hx i (hst hi)

lemma residual_subset_union_bad {Ω κ ι : Type*} [DecidableEq ι] [DecidableEq κ]
    (C : CylinderFamily Ω κ ι) (a : ι) (s : Finset ι) :
    residual (s.filter fun i => Disjoint (C.support i) (C.support a)) C.event ⊆
      residual s C.event ∪
        ⋃ i ∈ s.filter (fun i => ¬Disjoint (C.support i) (C.support a)), C.event i := by
  intro x hx
  by_cases hs : x ∈ residual s C.event
  · exact Or.inl hs
  · right
    simp only [residual, mem_compl_iff, mem_iUnion, not_exists] at hs
    push Not at hs
    obtain ⟨i, hi, hxi⟩ := hs
    refine mem_iUnion₂.mpr ⟨i, ?_, hxi⟩
    simp only [Finset.mem_filter, hi, true_and]
    intro hdis
    have := hx
    simp only [residual, mem_compl_iff, mem_iUnion, not_exists] at this
    exact this i (by simp [hi, hdis]) hxi

lemma independentResidualList_nonneg {Ω κ ι : Type*} [MeasurableSpace Ω]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ l : List ι, 0 ≤ independentResidualList C μ l := by
  intro l
  induction l with
  | nil => simp [independentResidualList]
  | cons a l ih =>
      simp only [independentResidualList]
      exact mul_nonneg
        (sub_nonneg.mpr (by simpa using measureReal_le_one (μ := μ) (C.event a))) ih

lemma dependencyErrorList_nonneg {Ω κ ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ]
    (C : CylinderFamily Ω κ ι) (μ : Measure Ω) :
    ∀ l : List ι, 0 ≤ dependencyErrorList C μ l := by
  intro l
  induction l with
  | nil => simp [dependencyErrorList]
  | cons a l ih =>
      simp only [dependencyErrorList]
      positivity

/--
The finite residual-density lemma of Filaseta--Ford--Konyagin--Pomerance--Yu.
The independence premise says that an event is independent of every residual
built from events supported on coordinates disjoint from its support.
-/
lemma residualDensity_list {Ω κ ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ] (C : CylinderFamily Ω κ ι)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hmeas : ∀ i, MeasurableSet (C.event i))
    (hindep : ∀ (a : ι) (s : Finset ι),
      (∀ i ∈ s, Disjoint (C.support i) (C.support a)) →
      μ.real (residual s C.event ∩ C.event a) =
        μ.real (residual s C.event) * μ.real (C.event a)) :
    ∀ l : List ι, l.Nodup →
      μ.real (residual l.toFinset C.event) ≥
        independentResidualList C μ l - dependencyErrorList C μ l := by
  intro l
  induction l with
  | nil =>
      intro _
      simp [independentResidualList, dependencyErrorList, residual]
  | cons a l ih =>
      intro hnodup
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hih := ih hlnodup
      let good := l.toFinset.filter (fun i => Disjoint (C.support i) (C.support a))
      let bad := l.toFinset.filter (fun i => ¬Disjoint (C.support i) (C.support a))
      have hgood_subset : good ⊆ l.toFinset := Finset.filter_subset _ _
      have hres_subset : residual l.toFinset C.event ⊆ residual good C.event :=
        residual_mono C.event hgood_subset
      have hgood_bound :
          μ.real (residual good C.event) ≤
            μ.real (residual l.toFinset C.event) +
              ∑ i ∈ bad, μ.real (C.event i) := by
        calc
          μ.real (residual good C.event) ≤
              μ.real (residual l.toFinset C.event ∪ ⋃ i ∈ bad, C.event i) :=
            measureReal_mono (by simpa [good, bad] using residual_subset_union_bad C a l.toFinset)
          _ ≤ μ.real (residual l.toFinset C.event) +
              μ.real (⋃ i ∈ bad, C.event i) := measureReal_union_le _ _
          _ ≤ μ.real (residual l.toFinset C.event) +
              ∑ i ∈ bad, μ.real (C.event i) := by
            gcongr
            exact measureReal_biUnion_finset_le bad C.event
      have hgood_indep :
          μ.real (residual good C.event ∩ C.event a) =
            μ.real (residual good C.event) * μ.real (C.event a) := by
        apply hindep
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hinter_mono :
          μ.real (residual l.toFinset C.event ∩ C.event a) ≤
            μ.real (residual good C.event ∩ C.event a) :=
        measureReal_mono (inter_subset_inter_left _ hres_subset)
      have hwa_nonneg : 0 ≤ μ.real (C.event a) := measureReal_nonneg
      have hinter_bound :
          μ.real (residual l.toFinset C.event ∩ C.event a) ≤
            (μ.real (residual l.toFinset C.event) +
              ∑ i ∈ bad, μ.real (C.event i)) * μ.real (C.event a) := by
        calc
          _ ≤ μ.real (residual good C.event ∩ C.event a) := hinter_mono
          _ = μ.real (residual good C.event) * μ.real (C.event a) := hgood_indep
          _ ≤ _ := mul_le_mul_of_nonneg_right hgood_bound hwa_nonneg
      have hdiff :
          μ.real (residual l.toFinset C.event \ C.event a) +
              μ.real (residual l.toFinset C.event ∩ C.event a) =
            μ.real (residual l.toFinset C.event) :=
        measureReal_sdiff_add_inter (hmeas a)
      have hwa_le : μ.real (C.event a) ≤ 1 := by
        simpa using measureReal_le_one (μ := μ) (C.event a)
      have hprod_nonneg : 0 ≤ independentResidualList C μ l :=
        independentResidualList_nonneg C μ l
      have herror_nonneg : 0 ≤ dependencyErrorList C μ l :=
        dependencyErrorList_nonneg C μ l
      rw [List.toFinset_cons, residual_insert, independentResidualList, dependencyErrorList]
      change μ.real (residual l.toFinset C.event \ C.event a) ≥ _
      dsimp only [bad] at hinter_bound ⊢
      nlinarith

/-! ## Cylinders in a product of prime residue fields -/

instance zmodMeasurableSpace277 (n : ℕ) : MeasurableSpace (ZMod n) := ⊤

instance zmodMeasurableSingletonClass277 (n : ℕ) : MeasurableSingletonClass (ZMod n) where
  measurableSet_singleton _ := by simp

/-- The product of residue fields indexed by a finite set of natural numbers. -/
abbrev PrimeSpace (P : Finset ℕ) := (p : P) → ZMod (p : ℕ)

/-- The uniform probability measure on one residue field. -/
def residueMeasure (p : ℕ) : Measure (ZMod p) :=
  uniformOn Set.univ

instance residueMeasure_isProbability (p : ℕ) [NeZero p] :
    IsProbabilityMeasure (residueMeasure p) := by
  unfold residueMeasure
  infer_instance

/-- The product of the uniform coordinate measures. -/
def primeMeasure (P : Finset ℕ) : Measure (PrimeSpace P) :=
  Measure.pi (fun p : P => residueMeasure p)

/-- A cylinder fixes one residue-field coordinate on every member of `support`. -/
structure PrimeCylinder (P : Finset ℕ) where
  support : Finset P
  value : (p : P) → ZMod (p : ℕ)

/-- The event represented by a prime cylinder. -/
def PrimeCylinder.event {P : Finset ℕ} (C : PrimeCylinder P) : Set (PrimeSpace P) :=
  {x | ∀ p ∈ C.support, x p = C.value p}

lemma measurableSet_primeCylinder_event {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (C : PrimeCylinder P) :
    MeasurableSet C.event := by
  letI (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  exact Set.toFinite C.event |>.measurableSet

/-- All coordinates used by cylinders in a finite index set. -/
def cylinderUnionSupport {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (s : Finset ι) : Finset P :=
  s.biUnion fun i => (C i).support

lemma mem_cylinderUnionSupport {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (s : Finset ι) (p : P) :
    p ∈ cylinderUnionSupport C s ↔ ∃ i ∈ s, p ∈ (C i).support := by
  simp [cylinderUnionSupport]

lemma disjoint_cylinderUnionSupport {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (a : ι) (s : Finset ι)
    (h : ∀ i ∈ s, Disjoint (C i).support (C a).support) :
    Disjoint (cylinderUnionSupport C s) (C a).support := by
  rw [Finset.disjoint_left]
  intro p hp hpa
  obtain ⟨i, hi, hpi⟩ := (mem_cylinderUnionSupport C s p).mp hp
  exact Finset.disjoint_left.mp (h i hi) hpi hpa

/-- Restriction of a point to a finite coordinate set. -/
def restrictCoordinates {P : Finset ℕ} (s : Finset P) (x : PrimeSpace P) :
    (p : s) → ZMod (p : ℕ) := fun p => x p

lemma measurable_restrictCoordinates {P : Finset ℕ} (s : Finset P) :
    Measurable (restrictCoordinates s : PrimeSpace P → ((p : s) → ZMod (p : ℕ))) := by
  unfold restrictCoordinates
  exact measurable_pi_lambda _ fun p : s => measurable_pi_apply (p : P)

/-- Predicate on restricted coordinates describing a residual event. -/
def residualCoordinateSet {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (s : Finset ι) :
    Set ((p : cylinderUnionSupport C s) → ZMod (p : ℕ)) :=
  {y | ∀ (i : ι) (hi : i ∈ s), ¬∀ (p : P) (hp : p ∈ (C i).support),
    y ⟨p, (mem_cylinderUnionSupport C s p).2 ⟨i, hi, hp⟩⟩ = (C i).value p}

lemma residual_eq_preimage_coordinates {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (s : Finset ι) :
    residual s (fun i => (C i).event) =
      restrictCoordinates (cylinderUnionSupport C s) ⁻¹' residualCoordinateSet C s := by
  ext x
  simp only [residual, PrimeCylinder.event, mem_compl_iff, mem_iUnion, mem_ofPred_eq,
    mem_preimage, residualCoordinateSet, restrictCoordinates, not_exists]

lemma event_eq_preimage_coordinates {P : Finset ℕ} (C : PrimeCylinder P) :
    C.event = restrictCoordinates C.support ⁻¹' {fun p : C.support => C.value p} := by
  ext x
  simp only [PrimeCylinder.event, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  constructor
  · intro h
    funext p
    exact h p p.property
  · intro h p hp
    exact congrFun h ⟨p, hp⟩

lemma coordinate_iIndep {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    iIndepFun (fun (p : P) (x : PrimeSpace P) => x p) (primeMeasure P) := by
  letI (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  exact iIndepFun_pi (X := fun _ => id) (μ := fun p : P => residueMeasure p)
    (fun _ => aemeasurable_id)

lemma residual_independent_primeCylinder {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {ι : Type*} [DecidableEq ι] (C : ι → PrimeCylinder P) (a : ι) (s : Finset ι)
    (hdis : ∀ i ∈ s, Disjoint (C i).support (C a).support) :
    (primeMeasure P).real
        (residual s (fun i => (C i).event) ∩ (C a).event) =
      (primeMeasure P).real (residual s (fun i => (C i).event)) *
        (primeMeasure P).real (C a).event := by
  letI (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  letI : IsProbabilityMeasure (primeMeasure P) := by
    unfold primeMeasure
    infer_instance
  let U := cylinderUnionSupport C s
  let V := (C a).support
  have hUV : Disjoint U V := disjoint_cylinderUnionSupport C a s hdis
  have hi := iIndepFun.indepFun_finset U V hUV (coordinate_iIndep hP)
    (fun p => measurable_pi_apply p)
  have hmeasure := hi.measure_inter_preimage_eq_mul
      (residualCoordinateSet C s) ({fun p : V => (C a).value p})
      (Set.toFinite (residualCoordinateSet C s) |>.measurableSet)
      (Set.finite_singleton _ |>.measurableSet)
  rw [residual_eq_preimage_coordinates C s, event_eq_preimage_coordinates (C a)]
  change
    ENNReal.toReal ((primeMeasure P)
      ((fun (x : PrimeSpace P) (p : cylinderUnionSupport C s) => x (p : P)) ⁻¹'
          residualCoordinateSet C s ∩
        (fun (x : PrimeSpace P) (p : V) => x (p : P)) ⁻¹'
          {fun p : V => (C a).value p})) =
      ENNReal.toReal ((primeMeasure P)
        ((fun (x : PrimeSpace P) (p : cylinderUnionSupport C s) => x (p : P)) ⁻¹'
          residualCoordinateSet C s)) *
      ENNReal.toReal ((primeMeasure P)
        ((fun (x : PrimeSpace P) (p : V) => x (p : P)) ⁻¹'
          {fun p : V => (C a).value p}))
  simpa only [U, V, Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hmeasure

lemma residueMeasure_singleton_real {p : ℕ} (hp : 0 < p) (z : ZMod p) :
    (residueMeasure p).real {z} = ((p : ℝ)⁻¹) := by
  letI : NeZero p := ⟨hp.ne'⟩
  simp [residueMeasure, Measure.real, uniformOn_univ, ZMod.card, ENNReal.div_eq_inv_mul]

lemma primeMeasure_eval_singleton_real {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (p : P) (z : ZMod (p : ℕ)) :
    (primeMeasure P).real {x | x p = z} = (((p : ℕ) : ℝ)⁻¹) := by
  letI (q : P) : NeZero (q : ℕ) := ⟨(hP q q.property).ne_zero⟩
  have hmap := (measurePreserving_eval (fun q : P => residueMeasure q) p).map_eq
  have happ := congrArg (fun ν : Measure (ZMod (p : ℕ)) => ν {z}) hmap
  rw [Measure.map_apply (measurable_pi_apply p) (measurableSet_singleton z)] at happ
  change ENNReal.toReal ((Measure.pi fun q : P => residueMeasure q)
    ((fun x : PrimeSpace P => x p) ⁻¹' {z})) = _
  rw [happ]
  exact residueMeasure_singleton_real (hP p p.property).pos z

lemma primeCylinder_event_measureReal {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (C : PrimeCylinder P) :
    (primeMeasure P).real C.event = ∏ p ∈ C.support, ((((p : P) : ℕ) : ℝ)⁻¹) := by
  letI (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  let sets : (p : P) → Set (ZMod (p : ℕ)) := fun p => {C.value p}
  have hprod := (coordinate_iIndep hP).measure_inter_preimage_eq_mul C.support
    (sets := sets) (fun _ _ => measurableSet_singleton _)
  have hevent : C.event = ⋂ p ∈ C.support, (fun x : PrimeSpace P => x p) ⁻¹' sets p := by
    ext x
    simp [PrimeCylinder.event, sets]
  rw [hevent]
  change ENNReal.toReal ((primeMeasure P)
      (⋂ p ∈ C.support, (fun x : PrimeSpace P => x p) ⁻¹' sets p)) = _
  rw [hprod, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  change (primeMeasure P).real {x | x p = C.value p} = _
  exact primeMeasure_eval_singleton_real hP p (C.value p)

/-! ## A controlled finite tail of reciprocal primes -/

lemma exists_prime_finset_sum_gt (A : ℝ) (Q : ℕ) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∈ S, Q < (p : ℕ)) ∧ A < ∑ p ∈ S, (((p : ℕ) : ℝ)⁻¹) := by
  by_contra h
  push Not at h
  have htail : ∀ S : Finset Nat.Primes,
      (∀ p ∈ S, Q < (p : ℕ)) →
        ∑ p ∈ S, (((p : ℕ) : ℝ)⁻¹) ≤ A := by
    intro S hS
    exact h S hS
  have hbound : ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, (((p : ℕ) : ℝ)⁻¹) ≤ A + (Q + 1 : ℕ) := by
    intro S
    let T : Finset Nat.Primes := S.filter fun p : Nat.Primes => Q < (p : ℕ)
    let H : Finset Nat.Primes := S.filter fun p : Nat.Primes => (p : ℕ) ≤ Q
    have hsplit : S = T ∪ H := by
      ext p
      simp only [T, H, Finset.mem_union, Finset.mem_filter]
      by_cases hp : p ∈ S
      · simp only [hp, true_and, true_iff]
        omega
      · simp [hp]
    have hdis : Disjoint T H := by
      rw [Finset.disjoint_left]
      intro p hpT hpH
      simp only [T, Finset.mem_filter] at hpT
      simp only [H, Finset.mem_filter] at hpH
      omega
    have hT : ∑ p ∈ T, (((p : ℕ) : ℝ)⁻¹) ≤ A := by
      apply htail T
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hterm : ∀ p ∈ H, (((p : ℕ) : ℝ)⁻¹) ≤ 1 := by
      intro p _
      exact inv_le_one_of_one_le₀ (by exact_mod_cast p.property.one_le)
    have hHcard : H.card ≤ Q + 1 := by
      have himage : H.image (fun p : Nat.Primes => (p : ℕ)) ⊆ Finset.range (Q + 1) := by
        intro n hn
        obtain ⟨p, hpH, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hpH).2)
      calc
        H.card = (H.image fun p : Nat.Primes => (p : ℕ)).card :=
          (Finset.card_image_of_injective H Subtype.val_injective).symm
        _ ≤ (Finset.range (Q + 1)).card := Finset.card_le_card himage
        _ = Q + 1 := Finset.card_range _
    rw [hsplit, Finset.sum_union hdis]
    calc
      (∑ p ∈ T, (((p : ℕ) : ℝ)⁻¹)) + ∑ p ∈ H, (((p : ℕ) : ℝ)⁻¹)
          ≤ A + ∑ _p ∈ H, (1 : ℝ) := add_le_add hT (Finset.sum_le_sum hterm)
      _ = A + H.card := by simp
      _ ≤ A + (Q + 1 : ℕ) := by
        gcongr
  apply Nat.Primes.not_summable_one_div
  simpa only [one_div] using
    (summable_of_sum_le (f := fun p : Nat.Primes => (((p : ℕ) : ℝ)⁻¹))
      (fun _ => inv_nonneg.mpr (by positivity)) hbound)

lemma exists_prime_finset_sum_between (A : ℝ) (hA : 0 ≤ A) (Q : ℕ) :
    ∃ P : Finset Nat.Primes,
      (∀ p ∈ P, Q < (p : ℕ)) ∧
      A < ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) ∧
      ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) ≤ A + 1 := by
  obtain ⟨S, hStail, hSsum⟩ := exists_prime_finset_sum_gt A Q
  let candidates : Finset (Finset Nat.Primes) :=
    S.powerset.filter fun T : Finset Nat.Primes => A < ∑ p ∈ T, (((p : ℕ) : ℝ)⁻¹)
  have hcandidates : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp [candidates, hSsum]
  obtain ⟨P, hPcand, hPmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hPS : P ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hPcand).1
  have hPtail : ∀ p ∈ P, Q < (p : ℕ) := fun p hp => hStail p (hPS hp)
  have hPsum : A < ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) := (Finset.mem_filter.mp hPcand).2
  refine ⟨P, hPtail, hPsum, ?_⟩
  by_cases hPempty : P = ∅
  · subst P
    simp at hPsum
    linarith
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hPempty
    have herase_le : ∑ q ∈ P.erase p, ((((q : Nat.Primes) : ℕ) : ℝ)⁻¹) ≤ A := by
      by_contra herase
      have herase_gt : A < ∑ q ∈ P.erase p, ((((q : Nat.Primes) : ℕ) : ℝ)⁻¹) := lt_of_not_ge herase
      have herase_cand : P.erase p ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨(Finset.erase_subset p P).trans hPS, herase_gt⟩
      have hcard := hPmin (P.erase p) herase_cand
      exact (not_le_of_gt (Finset.card_erase_lt_of_mem hp)) hcard
    rw [← Finset.sum_erase_add _ _ hp]
    calc
      (∑ q ∈ P.erase p, ((((q : Nat.Primes) : ℕ) : ℝ)⁻¹)) + (((p : ℕ) : ℝ)⁻¹)
          ≤ A + 1 := add_le_add herase_le
            (inv_le_one_of_one_le₀ (by exact_mod_cast p.property.one_le))

lemma exists_nat_prime_finset_sum_between (A : ℝ) (hA : 0 ≤ A) (Q : ℕ) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      A < ∑ p ∈ P, ((p : ℝ)⁻¹) ∧
      ∑ p ∈ P, ((p : ℝ)⁻¹) ≤ A + 1 := by
  obtain ⟨S, hStail, hSlow, hSup⟩ := exists_prime_finset_sum_between A hA Q
  let P : Finset ℕ := S.image fun p : Nat.Primes => (p : ℕ)
  have hsum : ∑ p ∈ P, ((p : ℝ)⁻¹) = ∑ p ∈ S, (((p : ℕ) : ℝ)⁻¹) := by
    simp only [P]
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Subtype.ext h
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q.property, hStail q hqS⟩
  · rw [hsum]
    exact hSlow
  · rw [hsum]
    exact hSup

/-- The integer constructed from a finite set of primes. -/
def primeProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

/-- Its real reciprocal-divisor product. -/
def abundancyProduct (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 + (p : ℝ)⁻¹)

lemma sigma_one_prime {p : ℕ} (hp : Nat.Prime p) : σ 1 p = p + 1 := by
  rw [← pow_one p, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  norm_num [Finset.sum_range_succ]
  omega

lemma sigma_primeProduct (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    σ 1 (primeProduct P) = ∏ p ∈ P, (p + 1) := by
  rw [primeProduct, ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime P hP]
  apply Finset.prod_congr rfl
  intro p hp
  exact sigma_one_prime (hP p hp)

lemma sigma_primeProduct_cast (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ((σ 1 (primeProduct P) : ℕ) : ℝ) =
      abundancyProduct P * (primeProduct P : ℝ) := by
  rw [sigma_primeProduct P hP, abundancyProduct, primeProduct]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

lemma primeProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    0 < primeProduct P := by
  apply Finset.prod_pos
  intro p hp
  exact (hP p hp).pos

lemma one_add_sum_inv_le_abundancyProduct (P : Finset ℕ) :
    1 + ∑ p ∈ P, (p : ℝ)⁻¹ ≤ abundancyProduct P := by
  induction P using Finset.induction_on with
  | empty => simp [abundancyProduct]
  | @insert p P hp ih =>
      rw [abundancyProduct, Finset.prod_insert hp, Finset.sum_insert hp]
      change 1 + ((p : ℝ)⁻¹ + ∑ q ∈ P, (q : ℝ)⁻¹) ≤
        (1 + (p : ℝ)⁻¹) * ∏ q ∈ P, (1 + (q : ℝ)⁻¹)
      have hprod : 1 + ∑ q ∈ P, (q : ℝ)⁻¹ ≤
          ∏ q ∈ P, (1 + (q : ℝ)⁻¹) := by simpa [abundancyProduct] using ih
      have hsum_nonneg : 0 ≤ ∑ q ∈ P, (q : ℝ)⁻¹ := by positivity
      have hinv_nonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
      nlinarith [mul_nonneg hinv_nonneg hsum_nonneg]

lemma abundancyProduct_le_exp_sum (P : Finset ℕ) :
    abundancyProduct P ≤ Real.exp (∑ p ∈ P, (p : ℝ)⁻¹) := by
  exact Real.prod_one_add_le_exp_sum P (fun p => by positivity)

/-! ## Finite subset weights -/

/-- The probability of the cylinder supported on `U`. -/
def supportWeight {P : Finset ℕ} (U : Finset P) : ℝ :=
  ∏ p ∈ U, ((((p : P) : ℕ) : ℝ)⁻¹)

lemma supportWeight_nonneg {P : Finset ℕ} (U : Finset P) : 0 ≤ supportWeight U := by
  rw [supportWeight]
  exact Finset.prod_nonneg fun p _ => inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le (p : ℕ)))

lemma supportWeight_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (U : Finset P) : supportWeight U ≤ 1 := by
  rw [supportWeight]
  apply Finset.prod_le_one
  · intro p hp
    positivity
  · intro p hp
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (hP p p.property).one_le)

lemma supportWeight_le_half {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {U : Finset P} (hU : U.Nonempty) : supportWeight U ≤ (1 / 2 : ℝ) := by
  obtain ⟨p, hpU⟩ := hU
  rw [supportWeight, ← Finset.prod_erase_mul _ _ hpU]
  have hrest : ∏ q ∈ U.erase p, ((((q : P) : ℕ) : ℝ)⁻¹) ≤ 1 := by
    simpa [supportWeight] using supportWeight_le_one hP (U.erase p)
  have hp_inv : ((((p : P) : ℕ) : ℝ)⁻¹) ≤ (1 / 2 : ℝ) := by
    have hp0 : (0 : ℝ) < ((p : P) : ℕ) := by exact_mod_cast (hP p p.property).pos
    have hp2 : (2 : ℝ) ≤ ((p : P) : ℕ) := by exact_mod_cast (hP p p.property).two_le
    simpa only [one_div] using (one_div_le_one_div hp0 (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hp_nonneg : 0 ≤ ((((p : P) : ℕ) : ℝ)⁻¹) := by positivity
  calc
    (∏ q ∈ U.erase p, ((((q : P) : ℕ) : ℝ)⁻¹)) * ((((p : P) : ℕ) : ℝ)⁻¹)
        ≤ 1 * ((((p : P) : ℕ) : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hrest hp_nonneg
    _ ≤ 1 / 2 := by simpa using hp_inv

lemma sum_supportWeight_powerset (P : Finset ℕ) :
    ∑ U ∈ (Finset.univ : Finset P).powerset, supportWeight U = abundancyProduct P := by
  have h := Finset.prod_add
    (fun p : P => ((((p : P) : ℕ) : ℝ)⁻¹)) (fun _p : P => (1 : ℝ))
    (Finset.univ : Finset P)
  have hatt : P.attach = (Finset.univ : Finset P) := by ext; simp
  rw [abundancyProduct, ← Finset.prod_attach, hatt]
  simpa only [supportWeight, Finset.prod_const_one, mul_one, add_comm] using h.symm

lemma sum_supportWeight_le_abundancy {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (C : ι → PrimeCylinder P)
    (hinj : Set.InjOn (fun i => (C i).support) I) :
    ∑ i ∈ I, supportWeight (C i).support ≤ abundancyProduct P := by
  let supports := I.image fun i => (C i).support
  have hsum : ∑ i ∈ I, supportWeight (C i).support =
      ∑ U ∈ supports, supportWeight U := by
    simp only [supports]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  rw [hsum, ← sum_supportWeight_powerset P]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro U hU
    simp only [supports, Finset.mem_image] at hU
    obtain ⟨i, hi, rfl⟩ := hU
    exact Finset.mem_powerset.mpr fun p hp => Finset.mem_attach P p
  · intro U hU hUns
    exact supportWeight_nonneg U

lemma supportWeight_erase_mul {P : Finset ℕ} {U : Finset P} {p : P} (hp : p ∈ U) :
    supportWeight U = supportWeight (U.erase p) * ((((p : P) : ℕ) : ℝ)⁻¹) := by
  simp only [supportWeight]
  exact (Finset.prod_erase_mul U (fun q : P => (((q : ℕ) : ℝ)⁻¹)) hp).symm

lemma sum_supportWeight_powerset_containing_le {P : Finset ℕ} (p : P) :
    ∑ U ∈ (Finset.univ : Finset P).powerset.filter (fun U => p ∈ U), supportWeight U ≤
      ((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P := by
  let F := (Finset.univ : Finset P).powerset.filter (fun U => p ∈ U)
  let E := F.image fun U : Finset P => U.erase p
  have herase_inj : Set.InjOn (fun U : Finset P => U.erase p) F := by
    intro U hUF V hVF hUV
    have hpU : p ∈ U := (Finset.mem_filter.mp hUF).2
    have hpV : p ∈ V := (Finset.mem_filter.mp hVF).2
    change U.erase p = V.erase p at hUV
    calc
      U = insert p (U.erase p) := (Finset.insert_erase hpU).symm
      _ = insert p (V.erase p) := by rw [hUV]
      _ = V := Finset.insert_erase hpV
  have hsum_image : ∑ U ∈ F, supportWeight (U.erase p) = ∑ V ∈ E, supportWeight V := by
    simp only [E]
    rw [Finset.sum_image]
    intro U hUF V hVF hUV
    exact herase_inj hUF hVF hUV
  have hEsub : E ⊆ (Finset.univ : Finset P).powerset := by
    intro V hV
    obtain ⟨U, hUF, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.mem_powerset.mpr fun q hq => Finset.mem_univ q
  change ∑ U ∈ F, supportWeight U ≤ _
  calc
    ∑ U ∈ F, supportWeight U =
        ∑ U ∈ F, supportWeight (U.erase p) * ((((p : P) : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro U hUF
      exact supportWeight_erase_mul (Finset.mem_filter.mp hUF).2
    _ = ((((p : P) : ℕ) : ℝ)⁻¹) * ∑ U ∈ F, supportWeight (U.erase p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ = ((((p : P) : ℕ) : ℝ)⁻¹) * ∑ V ∈ E, supportWeight V := by rw [hsum_image]
    _ ≤ ((((p : P) : ℕ) : ℝ)⁻¹) *
        ∑ V ∈ (Finset.univ : Finset P).powerset, supportWeight V := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hEsub
        intro V hV hVE
        exact supportWeight_nonneg V
      · positivity
    _ = ((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P := by
      rw [sum_supportWeight_powerset]

lemma sum_supportWeight_containing_le {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (C : ι → PrimeCylinder P)
    (hinj : Set.InjOn (fun i => (C i).support) I) (p : P) :
    ∑ i ∈ I.filter (fun i => p ∈ (C i).support), supportWeight (C i).support ≤
      ((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P := by
  let J := I.filter fun i => p ∈ (C i).support
  let supports := J.image fun i => (C i).support
  have hsum : ∑ i ∈ J, supportWeight (C i).support =
      ∑ U ∈ supports, supportWeight U := by
    simp only [supports]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb) hab
  have hsub : supports ⊆ (Finset.univ : Finset P).powerset.filter (fun U => p ∈ U) := by
    intro U hU
    obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp hU
    have hip := (Finset.mem_filter.mp hiJ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun q hq => Finset.mem_univ q), hip⟩
  change ∑ i ∈ J, supportWeight (C i).support ≤ _
  rw [hsum]
  calc
    ∑ U ∈ supports, supportWeight U ≤
        ∑ U ∈ (Finset.univ : Finset P).powerset.filter (fun U => p ∈ U), supportWeight U := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro U hU hUs
      exact supportWeight_nonneg U
    _ ≤ _ := sum_supportWeight_powerset_containing_le p

lemma primeCylinder_event_measureReal_eq_weight {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (C : PrimeCylinder P) :
    (primeMeasure P).real C.event = supportWeight C.support := by
  exact primeCylinder_event_measureReal hP C

lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hsub : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hsub]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr (by linarith : 0 ≤ 1 - 2 * x))]
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hmain : (1 - x)⁻¹ ≤ Real.exp (2 * x) := hinv.trans hexp
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have hposinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hsub
  have := (inv_le_inv₀ (Real.exp_pos (2 * x)) hposinv).2 hmain
  simpa [inv_inv] using this

lemma dependent_weight_sum_le {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (a : ι) (I : Finset ι) :
    ∑ b ∈ I.filter (fun b => ¬Disjoint (C b).support (C a).support),
        supportWeight (C b).support ≤
      ∑ p ∈ (C a).support,
        ∑ b ∈ I.filter (fun b => p ∈ (C b).support), supportWeight (C b).support := by
  rw [Finset.sum_filter]
  calc
    ∑ b ∈ I, (if (¬Disjoint (C b).support (C a).support)
        then supportWeight (C b).support else 0) ≤
      ∑ b ∈ I, ∑ p ∈ (C a).support,
        if p ∈ (C b).support then supportWeight (C b).support else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hdep : ¬Disjoint (C b).support (C a).support
      · simp only [if_pos hdep]
        obtain ⟨p, hpb, hpa⟩ := Finset.not_disjoint_iff.mp hdep
        have hsingle := Finset.single_le_sum
          (s := (C a).support)
          (f := fun q => if q ∈ (C b).support then supportWeight (C b).support else 0)
          (fun q hq => by
            split_ifs
            · exact supportWeight_nonneg _
            · exact le_rfl)
          hpa
        simpa [hpb] using hsingle
      · simp only [if_neg hdep]
        exact Finset.sum_nonneg fun p hp => by
          split_ifs
          · exact supportWeight_nonneg _
          · exact le_rfl
    _ = ∑ p ∈ (C a).support,
        ∑ b ∈ I.filter (fun b => p ∈ (C b).support), supportWeight (C b).support := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp [Finset.sum_filter]

/-- A separable upper bound for the accumulated dependency error. -/
def simpleDependencyBound {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (I : Finset ι) : ℝ :=
  ∑ a ∈ I, supportWeight (C a).support *
    (abundancyProduct P * ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹))

lemma dependencyErrorList_le_simple {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {ι : Type*} [DecidableEq ι] (C : ι → PrimeCylinder P)
    (hinj : Function.Injective fun i => (C i).support) :
    ∀ l : List ι, l.Nodup →
      dependencyErrorList
          { event := fun i => (C i).event, support := fun i => (C i).support }
          (primeMeasure P) l ≤ simpleDependencyBound C l.toFinset := by
  intro l
  induction l with
  | nil => simp [dependencyErrorList, simpleDependencyBound]
  | cons a l ih =>
      intro hnodup
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hih := ih hlnodup
      have hbad := dependent_weight_sum_le C a l.toFinset
      have hinj_l : Set.InjOn (fun i => (C i).support) l.toFinset :=
        hinj.injOn
      have hinner :
          ∑ p ∈ (C a).support,
              ∑ b ∈ l.toFinset.filter (fun b => p ∈ (C b).support),
                supportWeight (C b).support ≤
            ∑ p ∈ (C a).support,
              ((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P := by
        apply Finset.sum_le_sum
        intro p hp
        exact sum_supportWeight_containing_le l.toFinset C hinj_l p
      have hbad' :
          ∑ b ∈ l.toFinset.filter (fun b => ¬Disjoint (C b).support (C a).support),
              supportWeight (C b).support ≤
            abundancyProduct P *
              ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹) := by
        calc
          _ ≤ ∑ p ∈ (C a).support,
              ∑ b ∈ l.toFinset.filter (fun b => p ∈ (C b).support),
                supportWeight (C b).support := hbad
          _ ≤ ∑ p ∈ (C a).support,
              ((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P := hinner
          _ = abundancyProduct P *
              ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
      have hwa : 0 ≤ supportWeight (C a).support := supportWeight_nonneg _
      simp only [dependencyErrorList]
      simp_rw [primeCylinder_event_measureReal_eq_weight hP]
      rw [List.toFinset_cons, simpleDependencyBound, Finset.sum_insert (by simpa using hal)]
      simpa only [simpleDependencyBound, add_comm] using
        add_le_add hih (mul_le_mul_of_nonneg_left hbad' hwa)

lemma simpleDependencyBound_le {P : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (I : Finset ι)
    (hinj : Set.InjOn (fun i => (C i).support) I) :
    simpleDependencyBound C I ≤
      (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) := by
  have hrow (a : ι) :
      supportWeight (C a).support *
          (abundancyProduct P * ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹)) =
        abundancyProduct P *
          ∑ p ∈ (Finset.univ : Finset P),
            if p ∈ (C a).support then
              supportWeight (C a).support * ((((p : P) : ℕ) : ℝ)⁻¹)
            else 0 := by
    calc
      supportWeight (C a).support *
          (abundancyProduct P * ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹)) =
        abundancyProduct P *
          (supportWeight (C a).support *
            ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹)) := by ring
      _ = abundancyProduct P *
          ∑ p ∈ (C a).support,
            supportWeight (C a).support * ((((p : P) : ℕ) : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        rw [← Finset.sum_filter]
        congr 1
        ext p
        simp
  have hrearrange : simpleDependencyBound C I =
      abundancyProduct P *
        ∑ p ∈ (Finset.univ : Finset P),
          ((((p : P) : ℕ) : ℝ)⁻¹) *
            ∑ a ∈ I.filter (fun a => p ∈ (C a).support), supportWeight (C a).support := by
    rw [simpleDependencyBound]
    calc
      ∑ a ∈ I, supportWeight (C a).support *
          (abundancyProduct P * ∑ p ∈ (C a).support, ((((p : P) : ℕ) : ℝ)⁻¹)) =
        ∑ a ∈ I, abundancyProduct P *
          ∑ p ∈ (Finset.univ : Finset P),
            if p ∈ (C a).support then
              supportWeight (C a).support * ((((p : P) : ℕ) : ℝ)⁻¹)
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hrow a
      _ = abundancyProduct P *
          ∑ a ∈ I, ∑ p ∈ (Finset.univ : Finset P),
            if p ∈ (C a).support then
              supportWeight (C a).support * ((((p : P) : ℕ) : ℝ)⁻¹)
            else 0 := by rw [Finset.mul_sum]
      _ = abundancyProduct P *
          ∑ p ∈ (Finset.univ : Finset P), ∑ a ∈ I,
            if p ∈ (C a).support then
              supportWeight (C a).support * ((((p : P) : ℕ) : ℝ)⁻¹)
            else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        simp [Finset.sum_filter, mul_comm]
  rw [hrearrange]
  have hab_nonneg : 0 ≤ abundancyProduct P := by
    rw [abundancyProduct]
    exact Finset.prod_nonneg fun p hp => add_nonneg zero_le_one (inv_nonneg.mpr (by positivity))
  calc
    abundancyProduct P *
        ∑ p ∈ (Finset.univ : Finset P),
          ((((p : P) : ℕ) : ℝ)⁻¹) *
            ∑ a ∈ I.filter (fun a => p ∈ (C a).support), supportWeight (C a).support ≤
      abundancyProduct P *
        ∑ p ∈ (Finset.univ : Finset P),
          ((((p : P) : ℕ) : ℝ)⁻¹) *
            (((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P) := by
      apply mul_le_mul_of_nonneg_left _ hab_nonneg
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · exact sum_supportWeight_containing_le I C hinj p
      · positivity
    _ = (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) := by
      calc
        abundancyProduct P *
            ∑ p ∈ (Finset.univ : Finset P),
              ((((p : P) : ℕ) : ℝ)⁻¹) *
                (((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P) =
          ∑ p ∈ (Finset.univ : Finset P), abundancyProduct P *
            (((((p : P) : ℕ) : ℝ)⁻¹) *
              (((((p : P) : ℕ) : ℝ)⁻¹) * abundancyProduct P)) := by
            rw [Finset.mul_sum]
        _ = ∑ p ∈ (Finset.univ : Finset P),
            (abundancyProduct P) ^ 2 * (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := (Finset.mul_sum (Finset.univ : Finset P)
          (fun p : P => (((p : ℕ) : ℝ)⁻¹) ^ 2) (abundancyProduct P ^ 2)).symm

lemma independentResidualList_eq_finset {Ω κ ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (C : CylinderFamily Ω κ ι) (μ : Measure Ω) :
    ∀ (l : List ι), l.Nodup →
      independentResidualList C μ l =
        ∏ i ∈ l.toFinset, (1 - μ.real (C.event i)) := by
  intro l
  induction l with
  | nil => simp [independentResidualList]
  | cons a l ih =>
      intro hnodup
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      rw [independentResidualList, List.toFinset_cons,
        Finset.prod_insert (by simpa using hal), ih hlnodup]

lemma independentResidualList_lower {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {ι : Type*} [DecidableEq ι] (C : ι → PrimeCylinder P)
    (hinj : Function.Injective fun i => (C i).support)
    (hnonempty : ∀ i, (C i).support.Nonempty) (l : List ι) (hnodup : l.Nodup) :
    Real.exp (-2 * abundancyProduct P) ≤
      independentResidualList
        { event := fun i => (C i).event, support := fun i => (C i).support }
        (primeMeasure P) l := by
  let CF : CylinderFamily (PrimeSpace P) P ι :=
    { event := fun i => (C i).event, support := fun i => (C i).support }
  let I := l.toFinset
  have hind_eq := independentResidualList_eq_finset CF (primeMeasure P) l hnodup
  have hsum : ∑ i ∈ I, supportWeight (C i).support ≤ abundancyProduct P :=
    sum_supportWeight_le_abundancy I C hinj.injOn
  have hterm : ∀ i ∈ I,
      Real.exp (-2 * supportWeight (C i).support) ≤ 1 - supportWeight (C i).support := by
    intro i hi
    exact exp_neg_two_mul_le_one_sub (supportWeight_nonneg _)
      (supportWeight_le_half hP (hnonempty i))
  have hprod :
      Real.exp (-2 * ∑ i ∈ I, supportWeight (C i).support) ≤
        ∏ i ∈ I, (1 - supportWeight (C i).support) := by
    calc
      Real.exp (-2 * ∑ i ∈ I, supportWeight (C i).support) =
          ∏ i ∈ I, Real.exp (-2 * supportWeight (C i).support) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
      _ ≤ _ := Finset.prod_le_prod
        (fun i hi => (Real.exp_pos _).le) (fun i hi => hterm i hi)
  have hmono :
      Real.exp (-2 * abundancyProduct P) ≤
        Real.exp (-2 * ∑ i ∈ I, supportWeight (C i).support) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    Real.exp (-2 * abundancyProduct P) ≤
        Real.exp (-2 * ∑ i ∈ I, supportWeight (C i).support) := hmono
    _ ≤ ∏ i ∈ I, (1 - supportWeight (C i).support) := hprod
    _ = independentResidualList CF (primeMeasure P) l := by
      rw [hind_eq]
      simp only [CF]
      simp_rw [primeCylinder_event_measureReal_eq_weight hP]
      rfl

/-! ## Positivity of the residual set -/

/-- The analytic estimate above implies that a finite injective family of
nonempty prime cylinders cannot cover the whole product space whenever the
displayed numerical error bound holds. -/
lemma primeCylinder_residual_measureReal_pos {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (hinj : Function.Injective fun i => (C i).support)
    (hnonempty : ∀ i, (C i).support.Nonempty) (l : List ι) (hnodup : l.Nodup)
    (hsmall : (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) <
          Real.exp (-2 * abundancyProduct P)) :
    0 < (primeMeasure P).real (residual l.toFinset fun i => (C i).event) := by
  letI (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  letI : IsProbabilityMeasure (primeMeasure P) := by
    unfold primeMeasure
    infer_instance
  let CF : CylinderFamily (PrimeSpace P) P ι :=
    { event := fun i => (C i).event, support := fun i => (C i).support }
  have hdensity := residualDensity_list CF (primeMeasure P)
    (fun i => measurableSet_primeCylinder_event hP (C i))
    (fun a s hs => residual_independent_primeCylinder hP C a s hs) l hnodup
  have halpha : Real.exp (-2 * abundancyProduct P) ≤
      independentResidualList CF (primeMeasure P) l :=
    independentResidualList_lower hP C hinj hnonempty l hnodup
  have herror : dependencyErrorList CF (primeMeasure P) l ≤
      (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) := by
    exact (dependencyErrorList_le_simple hP C hinj l hnodup).trans
      (simpleDependencyBound_le C l.toFinset hinj.injOn)
  nlinarith

lemma primeCylinder_residual_nonempty {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {ι : Type*} [DecidableEq ι]
    (C : ι → PrimeCylinder P) (hinj : Function.Injective fun i => (C i).support)
    (hnonempty : ∀ i, (C i).support.Nonempty) (l : List ι) (hnodup : l.Nodup)
    (hsmall : (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) <
          Real.exp (-2 * abundancyProduct P)) :
    (residual l.toFinset fun i => (C i).event).Nonempty := by
  have hpos := primeCylinder_residual_measureReal_pos hP C hinj hnonempty l hnodup hsmall
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty.mp h] at hpos
  simpa using hpos

/-- If every selected prime is larger than `Q`, its inverse-square tail is at
most `Q⁻¹` times its inverse tail. -/
lemma sum_prime_inv_sq_le {P : Finset ℕ} {Q : ℕ} (hQpos : 0 < Q)
    (hlarge : ∀ p ∈ P, Q < p) :
    ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) ≤
      ((Q : ℝ)⁻¹) * ∑ p ∈ P, ((p : ℝ)⁻¹) := by
  calc
    ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) ≤
        ∑ p ∈ (Finset.univ : Finset P),
          ((Q : ℝ)⁻¹) * ((((p : P) : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpQ : (Q : ℝ) ≤ (p : ℕ) := by
        exact_mod_cast (Nat.le_of_lt (hlarge p p.property))
      have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
      have hinv : ((((p : P) : ℕ) : ℝ)⁻¹) ≤ (Q : ℝ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hQreal hpQ
      have hpnonneg : 0 ≤ ((((p : P) : ℕ) : ℝ)⁻¹) := by positivity
      simpa [pow_two, mul_comm] using mul_le_mul_of_nonneg_right hinv hpnonneg
    _ = ((Q : ℝ)⁻¹) * ∑ p ∈ P, ((p : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach P (fun p : ℕ => (Q : ℝ)⁻¹ * (p : ℝ)⁻¹))

/-! ## Divisor ideals and their prime-coordinate supports -/

/-- The selected primes which divide a natural number. -/
def divisorSupport (P : Finset ℕ) (d : ℕ) : Finset P :=
  (Finset.univ : Finset P).filter fun p => (p : ℕ) ∣ d

@[simp]
lemma mem_divisorSupport {P : Finset ℕ} {d : ℕ} (p : P) :
    p ∈ divisorSupport P d ↔ (p : ℕ) ∣ d := by
  simp [divisorSupport]

lemma primeProduct_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (primeProduct P) := by
  rw [primeProduct]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hP p hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq

lemma primeFactors_primeProduct (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (primeProduct P).primeFactors = P := by
  simpa only [primeProduct] using Nat.primeFactors_prod hP

lemma image_divisorSupport_eq_primeFactors {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {d : ℕ} (hd0 : d ≠ 0)
    (hdvd : d ∣ primeProduct P) :
    (divisorSupport P d).image (fun p : P => (p : ℕ)) = d.primeFactors := by
  have hprod0 : primeProduct P ≠ 0 := (primeProduct_pos P hP).ne'
  have hsubset : d.primeFactors ⊆ P := by
    rw [← primeFactors_primeProduct P hP]
    exact Nat.primeFactors_mono hdvd hprod0
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨hP q q.property, (mem_divisorSupport q).mp hq, hd0⟩
  · intro hp
    have hpP : p ∈ P := hsubset hp
    refine Finset.mem_image.mpr ⟨⟨p, hpP⟩, ?_, rfl⟩
    exact (mem_divisorSupport ⟨p, hpP⟩).mpr (Nat.dvd_of_mem_primeFactors hp)

lemma prod_divisorSupport_eq {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : ℕ} (hd0 : d ≠ 0) (hdvd : d ∣ primeProduct P) :
    ∏ p ∈ divisorSupport P d, (p : ℕ) = d := by
  have hsq : Squarefree d :=
    (primeProduct_squarefree P hP).squarefree_of_dvd hdvd
  calc
    ∏ p ∈ divisorSupport P d, (p : ℕ) =
        ∏ p ∈ (divisorSupport P d).image (fun p : P => (p : ℕ)), p := by
      rw [Finset.prod_image]
      intro p hp q hq hpq
      exact Subtype.ext hpq
    _ = ∏ p ∈ d.primeFactors, p := by
      rw [image_divisorSupport_eq_primeFactors hP hd0 hdvd]
    _ = d := Nat.prod_primeFactors_of_squarefree hsq

/-- Absolute norm turns membership in an integer ideal into divisibility. -/
lemma absNorm_dvd_of_mem {I : Ideal ℤ} {z : ℤ} (hz : z ∈ I) :
    (Ideal.absNorm I : ℤ) ∣ z := by
  rw [← Int.ideal_span_absNorm_eq_self I, Ideal.mem_span_singleton] at hz
  exact hz

lemma absNorm_dvd_primeProduct_of_mem {P : Finset ℕ} {I : Ideal ℤ}
    (hmem : (primeProduct P : ℤ) ∈ I) :
    Ideal.absNorm I ∣ primeProduct P := by
  exact_mod_cast absNorm_dvd_of_mem hmem

lemma two_le_absNorm {I : Ideal ℤ} (hbot : I ≠ ⊥) (htop : I ≠ ⊤) :
    2 ≤ Ideal.absNorm I := by
  have h0 : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
  have h1 : Ideal.absNorm I ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr htop
  omega

/-- The cylinder attached to one congruence class modulo an integer ideal. -/
def idealCylinder (P : Finset ℕ) (m : StrictCoveringSystem ℤ) (i : m.ι) :
    PrimeCylinder P where
  support := divisorSupport P (Ideal.absNorm (m.moduli i))
  value := fun p => (m.residue i : ZMod (p : ℕ))

lemma idealCylinder_support_nonempty {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (m : StrictCoveringSystem ℤ)
    (hmem : ∀ i, (primeProduct P : ℤ) ∈ m.moduli i) (i : m.ι) :
    (idealCylinder P m i).support.Nonempty := by
  have hd0 : Ideal.absNorm (m.moduli i) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (m.ne_bot i)
  have hprod := prod_divisorSupport_eq hP hd0
    (absNorm_dvd_primeProduct_of_mem (hmem i))
  by_contra hempty
  have heq : divisorSupport P (Ideal.absNorm (m.moduli i)) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    simpa only [idealCylinder] using hempty
  rw [heq] at hprod
  simp only [Finset.prod_empty] at hprod
  have htwo := two_le_absNorm (m.ne_bot i) (m.ne_top i)
  omega

lemma idealCylinder_support_injective {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (m : StrictCoveringSystem ℤ)
    (hmem : ∀ i, (primeProduct P : ℤ) ∈ m.moduli i) :
    Function.Injective fun i => (idealCylinder P m i).support := by
  intro i j hij
  have hi0 : Ideal.absNorm (m.moduli i) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (m.ne_bot i)
  have hj0 : Ideal.absNorm (m.moduli j) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (m.ne_bot j)
  have hi := prod_divisorSupport_eq hP hi0
    (absNorm_dvd_primeProduct_of_mem (hmem i))
  have hj := prod_divisorSupport_eq hP hj0
    (absNorm_dvd_primeProduct_of_mem (hmem j))
  have hnorm : Ideal.absNorm (m.moduli i) = Ideal.absNorm (m.moduli j) := by
    change divisorSupport P (Ideal.absNorm (m.moduli i)) =
      divisorSupport P (Ideal.absNorm (m.moduli j)) at hij
    rw [← hi, ← hj, hij]
  apply m.injective_moduli
  rw [← Int.ideal_span_absNorm_eq_self (m.moduli i),
    ← Int.ideal_span_absNorm_eq_self (m.moduli j), hnorm]

/-! ## Chinese remaindering and exclusion of covering systems -/

lemma exists_int_with_prime_residues {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (x : PrimeSpace P) :
    ∃ z : ℤ, ∀ p : P, (z : ZMod (p : ℕ)) = x p := by
  have hcop : Pairwise fun p q : P => Nat.Coprime (p : ℕ) (q : ℕ) := by
    intro p q hpq
    apply (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
    intro hpqval
    exact hpq (Subtype.ext hpqval)
  let e := ZMod.prodEquivPi (fun p : P => (p : ℕ)) hcop
  obtain ⟨y, hy⟩ := e.surjective x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective y
  refine ⟨z, ?_⟩
  intro p
  have hp := congrFun hy p
  rw [ZMod.prodEquivPi_apply] at hp
  rw [← hz] at hp
  rw [map_intCast] at hp
  exact hp

lemma int_mem_ideal_implies_idealCylinder_event {P : Finset ℕ}
    (m : StrictCoveringSystem ℤ) (i : m.ι) (z : ℤ)
    (hz : z - m.residue i ∈ m.moduli i) :
    (fun p : P => (z : ZMod (p : ℕ))) ∈ (idealCylinder P m i).event := by
  intro p hp
  have hpNorm : (p : ℕ) ∣ Ideal.absNorm (m.moduli i) := by
    exact (mem_divisorSupport p).mp (by simpa only [idealCylinder] using hp)
  have hpNormInt : ((p : ℕ) : ℤ) ∣ (Ideal.absNorm (m.moduli i) : ℤ) := by
    exact_mod_cast hpNorm
  have hpdiff : ((p : ℕ) : ℤ) ∣ z - m.residue i :=
    hpNormInt.trans (absNorm_dvd_of_mem hz)
  have heq : (m.residue i : ZMod (p : ℕ)) = (z : ZMod (p : ℕ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (m.residue i) z (p : ℕ)).mpr hpdiff
  exact heq.symm

/-- The quantitative cylinder estimate rules out a strict covering system all
of whose modulus ideals contain the constructed squarefree integer. -/
lemma exists_modulus_not_containing_primeProduct {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hsmall : (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) <
          Real.exp (-2 * abundancyProduct P))
    (m : StrictCoveringSystem ℤ) :
    ∃ i, (primeProduct P : ℤ) ∉ m.moduli i := by
  by_contra hcontra
  push Not at hcontra
  let C : m.ι → PrimeCylinder P := idealCylinder P m
  let l : List m.ι := (Finset.univ : Finset m.ι).toList
  have hnodup : l.Nodup := Finset.nodup_toList _
  have hinj : Function.Injective fun i => (C i).support := by
    exact idealCylinder_support_injective hP m hcontra
  have hnonempty : ∀ i, (C i).support.Nonempty := by
    exact fun i => idealCylinder_support_nonempty hP m hcontra i
  obtain ⟨x, hx⟩ := primeCylinder_residual_nonempty hP C hinj hnonempty l hnodup hsmall
  have hxnot : ∀ i, x ∉ (C i).event := by
    intro i hxi
    apply hx
    apply Set.mem_iUnion.mpr
    have hi : i ∈ l.toFinset := by simp [l]
    exact ⟨i, Set.mem_iUnion.mpr ⟨hi, hxi⟩⟩
  obtain ⟨z, hz⟩ := exists_int_with_prime_residues hP x
  have hzcover : z ∈ ⋃ i, ({m.residue i} : Set ℤ) + (m.moduli i : Set ℤ) := by
    rw [m.unionCovers]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzcover
  obtain ⟨a, ha, b, hb, hab⟩ := hi
  have haeq : a = m.residue i := by simpa using ha
  subst a
  have hzsub : z - m.residue i ∈ m.moduli i := by
    rw [← hab]
    simpa using hb
  have hzEvent := int_mem_ideal_implies_idealCylinder_event (P := P) m i z hzsub
  have hxEvent : x ∈ (C i).event := by
    rw [← show (fun p : P => (z : ZMod (p : ℕ))) = x from funext hz]
    simpa only [C] using hzEvent
  exact hxnot i hxEvent

/-! ## Choice of the prime set and the main theorem -/

lemma exists_nat_mul_inv_lt {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ x * (Q : ℝ)⁻¹ < ε := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (x / ε)
  have hquot : 0 ≤ x / ε := div_nonneg hx hε.le
  have hQreal : (0 : ℝ) < Q := hquot.trans_lt hQ
  have hQpos : 0 < Q := by exact_mod_cast hQreal
  refine ⟨Q, hQpos, ?_⟩
  rw [← div_eq_mul_inv, div_lt_iff₀ hQreal]
  have hxlt : x < (Q : ℝ) * ε := (div_lt_iff₀ hε).mp hQ
  simpa only [mul_comm] using hxlt

/-- **Erdős Problem 277 (Haight).**  For every real constant `c` there is
an integer of abundancy greater than `c` which cannot supply all the distinct
nontrivial moduli of any covering system of the integers. -/
theorem erdos_277 :
    answer(True) ↔ ∀ c : ℝ, ∃ n : ℕ, (σ 1 n : ℝ) > c * n ∧
      ∀ (m : StrictCoveringSystem ℤ), ∃ i, (n : ℤ) ∉ m.moduli i := by
  constructor
  · intro _ c
    let A : ℝ := max c 0 + 1
    have hA : 0 ≤ A := by
      dsimp only [A]
      linarith [le_max_right c 0]
    let B : ℝ := Real.exp (A + 1)
    have hBpos : 0 < B := by simp only [B, Real.exp_pos]
    have hxnonneg : 0 ≤ B ^ 2 * (A + 1) :=
      mul_nonneg (sq_nonneg B) (by linarith)
    obtain ⟨Q, hQpos, hQsmall⟩ := exists_nat_mul_inv_lt hxnonneg
      (Real.exp_pos (-2 * B))
    obtain ⟨P, hPtail, hsum_low, hsum_high⟩ :=
      exists_nat_prime_finset_sum_between A hA Q
    have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => (hPtail p hp).1
    have hlarge : ∀ p ∈ P, Q < p := fun p hp => (hPtail p hp).2
    have hab_nonneg : 0 ≤ abundancyProduct P := by
      rw [abundancyProduct]
      exact Finset.prod_nonneg fun p hp =>
        add_nonneg zero_le_one (inv_nonneg.mpr (by positivity))
    have hab_le_B : abundancyProduct P ≤ B := by
      calc
        abundancyProduct P ≤ Real.exp (∑ p ∈ P, (p : ℝ)⁻¹) :=
          abundancyProduct_le_exp_sum P
        _ ≤ Real.exp (A + 1) := Real.exp_le_exp.mpr hsum_high
        _ = B := rfl
    have hab_sq_le : (abundancyProduct P) ^ 2 ≤ B ^ 2 := by
      nlinarith
    have hinv_sq := sum_prime_inv_sq_le hQpos hlarge
    have hsmall : (abundancyProduct P) ^ 2 *
        ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) <
          Real.exp (-2 * abundancyProduct P) := by
      calc
        (abundancyProduct P) ^ 2 *
              ∑ p ∈ (Finset.univ : Finset P), (((((p : P) : ℕ) : ℝ)⁻¹) ^ 2) ≤
            (abundancyProduct P) ^ 2 *
              ((Q : ℝ)⁻¹ * ∑ p ∈ P, (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv_sq (sq_nonneg _)
        _ ≤ B ^ 2 * ((Q : ℝ)⁻¹ * ∑ p ∈ P, (p : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_right hab_sq_le
          positivity
        _ ≤ B ^ 2 * ((Q : ℝ)⁻¹ * (A + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
          exact mul_le_mul_of_nonneg_left hsum_high (inv_nonneg.mpr (by positivity))
        _ = (B ^ 2 * (A + 1)) * (Q : ℝ)⁻¹ := by ring
        _ < Real.exp (-2 * B) := hQsmall
        _ ≤ Real.exp (-2 * abundancyProduct P) := by
          apply Real.exp_le_exp.mpr
          nlinarith
    refine ⟨primeProduct P, ?_, ?_⟩
    · rw [sigma_primeProduct_cast P hP]
      have hsum_nonneg : 0 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by positivity
      have hab_lower := one_add_sum_inv_le_abundancyProduct P
      have hcA : c < A := by
        dsimp only [A]
        linarith [le_max_left c 0]
      have hc_hab : c < abundancyProduct P := by
        nlinarith
      have hnpos : (0 : ℝ) < primeProduct P := by
        exact_mod_cast primeProduct_pos P hP
      exact mul_lt_mul_of_pos_right hc_hab hnpos
    · intro m
      exact exists_modulus_not_containing_primeProduct hP hsmall m
  · intro _
    trivial

end

end Erdos277

#print axioms Erdos277.erdos_277
