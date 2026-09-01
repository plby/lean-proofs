/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos797
import ErdosProblems.Erdos228.GaussianWalk
import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos989.GlobalSelection
import ErdosProblems.Erdos989.FixedRadiusUpper
import Mathlib.Probability.Distributions.Uniform

/-!
# The fixed-radius upper construction for Erdős Problem 989

Beck's upper construction is a fixed-scale minimax statement: after the
radius is fixed, a periodic jittered set is chosen which works uniformly over
all centers.  The selected set may depend on the radius.  This file develops
the finite product, dependency, local-lemma, and compactness infrastructure
for that source-faithful quantifier order.
-/

namespace Erdos989

namespace GlobalSelection

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

universe u v w

section FiniteConstraintModel

variable {Cell : Type u} {Candidate : Type v} {Constraint : Type w}
variable [DecidableEq Cell] [DecidableEq Constraint]

/-- Cardinality factorization for two predicates which inspect complementary
sets of coordinates in a finite product.  This is the counting form of
independence used by `Erdos797.finite_local_lemma`. -/
theorem coordinate_split_cardinality
    {I Q : Type*} [Finite I] [Finite Q]
    (p : I → Prop) (P : ({i // p i} → Q) → Prop)
    (R : ({i // ¬p i} → Q) → Prop) :
    Nat.card {x : I → Q // P (fun i ↦ x i) ∧ R (fun i ↦ x i)} *
        Nat.card (I → Q) =
      Nat.card {x : I → Q // P (fun i ↦ x i)} *
        Nat.card {x : I → Q // R (fun i ↦ x i)} := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype Q := Fintype.ofFinite Q
  let A := {i // p i} → Q
  let B := {i // ¬p i} → Q
  let e : (I → Q) ≃ A × B :=
    Equiv.piEquivPiSubtypeProd p (fun _ ↦ Q)
  let eBoth :
      {x : I → Q // P (fun i ↦ x i) ∧ R (fun i ↦ x i)} ≃
        {a : A // P a} × {b : B // R b} :=
    (e.subtypeEquiv (fun _ ↦ Iff.rfl)).trans Equiv.subtypeProdEquivProd
  let eP : {x : I → Q // P (fun i ↦ x i)} ≃ {a : A // P a} × B :=
    (e.subtypeEquiv (fun _ ↦ Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  let secondSubtype : {z : A × B // R z.2} ≃ A × {b : B // R b} :=
    { toFun := fun z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      invFun := fun z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩ }
  let eR : {x : I → Q // R (fun i ↦ x i)} ≃ A × {b : B // R b} :=
    (e.subtypeEquiv (fun _ ↦ Iff.rfl)).trans secondSubtype
  have hBoth :
      Fintype.card {x : I → Q // P (fun i ↦ x i) ∧ R (fun i ↦ x i)} =
        Fintype.card {a : A // P a} * Fintype.card {b : B // R b} := by
    rw [Fintype.card_congr eBoth, Fintype.card_prod]
  have hP : Fintype.card {x : I → Q // P (fun i ↦ x i)} =
      Fintype.card {a : A // P a} * Fintype.card B := by
    rw [Fintype.card_congr eP, Fintype.card_prod]
  have hR : Fintype.card {x : I → Q // R (fun i ↦ x i)} =
      Fintype.card A * Fintype.card {b : B // R b} := by
    rw [Fintype.card_congr eR, Fintype.card_prod]
  have hAll : Fintype.card (I → Q) = Fintype.card A * Fintype.card B := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  simp only [Nat.card_eq_fintype_card]
  rw [hBoth, hP, hR, hAll]
  ring

/-- The finite set of cells inspected by a finite family of local constraints. -/
def supportUnion (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) : Finset Cell :=
  s.biUnion fun k ↦ (c k).support

omit [DecidableEq Constraint] in
@[simp] theorem mem_supportUnion (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) (i : Cell) :
    i ∈ supportUnion c s ↔ ∃ k ∈ s, i ∈ (c k).support := by
  classical
  simp [supportUnion]

/-- A finite assignment contains only the coordinates inspected by the chosen
finite constraint family. -/
abbrev FiniteAssignment (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) := supportUnion c s → Candidate

/-- Restrict a finite assignment to the support of one of the constraints in
the family. -/
def restrictFinite (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) (k : ↑s) (x : FiniteAssignment c s) :
    (c k.1).support → Candidate :=
  fun i ↦ x ⟨i.1, mem_supportUnion c s i.1 |>.2 ⟨k.1, k.2, i.2⟩⟩

/-- The bad event attached to a constraint is failure of its predicate on the
coordinates contained in the finite union of supports. -/
def finiteBad (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) (k : ↑s) (x : FiniteAssignment c s) : Prop :=
  ¬(c k.1).accepts (restrictFinite c s k x)

omit [DecidableEq Constraint] in
/-- Two finite assignments which agree on the support of a constraint either
both trigger its bad event or both avoid it. -/
theorem finiteBad_congr_on_support
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint)
    (k : ↑s) (x y : FiniteAssignment c s)
    (hxy : ∀ i : (c k.1).support,
      x ⟨i.1, mem_supportUnion c s i.1 |>.2 ⟨k.1, k.2, i.2⟩⟩ =
        y ⟨i.1, mem_supportUnion c s i.1 |>.2 ⟨k.1, k.2, i.2⟩⟩) :
    finiteBad c s k x ↔ finiteBad c s k y := by
  classical
  unfold finiteBad
  have hres : restrictFinite c s k x = restrictFinite c s k y := by
    funext i
    exact hxy i
  rw [hres]

/-- The natural dependency neighborhood: two constraints are adjacent when
their finite supports overlap.  Every event is also declared adjacent to
itself, including the degenerate empty-support case. -/
def supportNeighbor (c : Constraint → LocalConstraint Cell Candidate)
    (s : Finset Constraint) (k : ↑s) : Finset ↑s := by
  classical
  exact insert k (Finset.univ.filter fun j ↦
    ¬Disjoint (c k.1).support (c j.1).support)

theorem disjoint_support_of_not_mem_supportNeighbor
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint)
    (k j : ↑s) (hj : j ∉ supportNeighbor c s k) :
    Disjoint (c k.1).support (c j.1).support := by
  classical
  simp only [supportNeighbor, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, not_or, not_not] at hj
  exact hj.2

/-- Events whose supports are disjoint are independent in the exact finite
cardinality sense required by the local lemma. -/
theorem finiteBad_independent_of_nonNeighbors
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint)
    (k : ↑s) (T : Finset ↑s)
    (hT : ∀ j ∈ T, j ∉ supportNeighbor c s k) :
    ((Erdos797.restricted (finiteBad c s) k T).card : ℝ) *
        Fintype.card (FiniteAssignment c s) =
      ((Erdos797.restricted (finiteBad c s) k ∅).card : ℝ) *
        (Erdos797.avoid (finiteBad c s) T).card := by
  classical
  let q₀ : Candidate := Classical.choice inferInstance
  let p : supportUnion c s → Prop := fun i ↦ i.1 ∈ (c k.1).support
  let onlyP : ({i // p i} → Candidate) → FiniteAssignment c s := fun a i ↦
    if hi : p i then a ⟨i, hi⟩ else q₀
  let onlyCompl : ({i // ¬p i} → Candidate) → FiniteAssignment c s := fun b i ↦
    if hi : p i then q₀ else b ⟨i, hi⟩
  let P : ({i // p i} → Candidate) → Prop := fun a ↦
    finiteBad c s k (onlyP a)
  let R : ({i // ¬p i} → Candidate) → Prop := fun b ↦
    ∀ j ∈ T, ¬finiteBad c s j (onlyCompl b)
  have hcardFilter (Q : FiniteAssignment c s → Prop) :
      (Finset.univ.filter Q).card =
        Nat.card {x : FiniteAssignment c s // Q x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hbad (x : FiniteAssignment c s) :
      finiteBad c s k x ↔ P (fun i ↦ x i) := by
    apply finiteBad_congr_on_support c s k x
    intro i
    simp only [onlyP, p]
    rw [dif_pos i.2]
  have hav (x : FiniteAssignment c s) :
      (∀ j ∈ T, ¬finiteBad c s j x) ↔ R (fun i ↦ x i) := by
    constructor
    · intro hx j hj
      have hdis := disjoint_support_of_not_mem_supportNeighbor c s k j (hT j hj)
      have heq : finiteBad c s j x ↔
          finiteBad c s j (onlyCompl (fun i ↦ x i)) := by
        apply finiteBad_congr_on_support c s j x
        intro i
        have hip : ¬p ⟨i.1, mem_supportUnion c s i.1 |>.2
            ⟨j.1, j.2, i.2⟩⟩ := by
          intro hik
          exact (Finset.disjoint_left.mp hdis) hik i.2
        simp only [onlyCompl]
        rw [dif_neg hip]
      exact fun hbad' ↦ hx j hj (heq.mpr hbad')
    · intro hx j hj
      have hdis := disjoint_support_of_not_mem_supportNeighbor c s k j (hT j hj)
      have heq : finiteBad c s j x ↔
          finiteBad c s j (onlyCompl (fun i ↦ x i)) := by
        apply finiteBad_congr_on_support c s j x
        intro i
        have hip : ¬p ⟨i.1, mem_supportUnion c s i.1 |>.2
            ⟨j.1, j.2, i.2⟩⟩ := by
          intro hik
          exact (Finset.disjoint_left.mp hdis) hik i.2
        simp only [onlyCompl]
        rw [dif_neg hip]
      exact fun hbad' ↦ hx j hj (heq.mp hbad')
  have hrestrictedT :
      (Erdos797.restricted (finiteBad c s) k T).card =
        Nat.card {x : FiniteAssignment c s //
          P (fun i ↦ x i) ∧ R (fun i ↦ x i)} := by
    let Q : FiniteAssignment c s → Prop := fun x ↦
      P (fun i ↦ x i) ∧ R (fun i ↦ x i)
    have hset : Erdos797.restricted (finiteBad c s) k T =
        Finset.univ.filter Q := by
      ext x
      simp only [Erdos797.mem_restricted, Finset.mem_filter, Finset.mem_univ,
        true_and, Q]
      exact and_congr (hbad x) (hav x)
    calc
      _ = (Finset.univ.filter Q).card := congrArg Finset.card hset
      _ = _ := by convert hcardFilter Q
  have hrestrictedEmpty :
      (Erdos797.restricted (finiteBad c s) k ∅).card =
        Nat.card {x : FiniteAssignment c s // P (fun i ↦ x i)} := by
    let Q : FiniteAssignment c s → Prop := fun x ↦ P (fun i ↦ x i)
    have hset : Erdos797.restricted (finiteBad c s) k ∅ =
        Finset.univ.filter Q := by
      ext x
      simp only [Erdos797.mem_restricted, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Q]
      simpa only [and_true] using hbad x
    calc
      _ = (Finset.univ.filter Q).card := congrArg Finset.card hset
      _ = _ := by convert hcardFilter Q
  have havoid :
      (Erdos797.avoid (finiteBad c s) T).card =
        Nat.card {x : FiniteAssignment c s // R (fun i ↦ x i)} := by
    let Q : FiniteAssignment c s → Prop := fun x ↦ R (fun i ↦ x i)
    have hset : Erdos797.avoid (finiteBad c s) T =
        Finset.univ.filter Q := by
      ext x
      simp only [Erdos797.mem_avoid, Finset.mem_filter, Finset.mem_univ,
        true_and, Q]
      exact hav x
    calc
      _ = (Finset.univ.filter Q).card := congrArg Finset.card hset
      _ = _ := by convert hcardFilter Q
  rw [hrestrictedT, hrestrictedEmpty, havoid]
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast coordinate_split_cardinality p P R

/-- The exact certificate required to apply the finite local lemma to a finite
family of local constraints.  This separates the finite combinatorial estimate
from the compactness argument without assuming finite satisfiability. -/
structure FiniteLLLCertificate
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint) where
  neighbor : ↑s → Finset ↑s
  weight : ↑s → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  weight_lt_one : ∀ k, weight k < 1
  mass : ∀ k,
    ((Erdos797.restricted (finiteBad c s) k ∅).card : ℝ) ≤
      weight k * (∏ j ∈ neighbor k, (1 - weight j)) *
        Fintype.card (FiniteAssignment c s)
  independent : ∀ k T, (∀ j ∈ T, j ∉ neighbor k) →
    ((Erdos797.restricted (finiteBad c s) k T).card : ℝ) *
        Fintype.card (FiniteAssignment c s) =
      ((Erdos797.restricted (finiteBad c s) k ∅).card : ℝ) *
        (Erdos797.avoid (finiteBad c s) T).card

/-- For finite-support constraints, only the local-lemma mass inequality and
weights remain to be supplied: independence follows from disjoint supports. -/
structure FiniteSupportLLLWeights
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint) where
  weight : ↑s → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  weight_lt_one : ∀ k, weight k < 1
  mass : ∀ k,
    ((Erdos797.restricted (finiteBad c s) k ∅).card : ℝ) ≤
      weight k * (∏ j ∈ supportNeighbor c s k, (1 - weight j)) *
        Fintype.card (FiniteAssignment c s)

/-- Promote the weight-and-mass data to the full certificate by the coordinate
factorization theorem above. -/
def FiniteSupportLLLWeights.toCertificate
    [Fintype Candidate] [Nonempty Candidate]
    {c : Constraint → LocalConstraint Cell Candidate} {s : Finset Constraint}
    (h : FiniteSupportLLLWeights c s) : FiniteLLLCertificate c s where
  neighbor := supportNeighbor c s
  weight := h.weight
  weight_nonneg := h.weight_nonneg
  weight_lt_one := h.weight_lt_one
  mass := h.mass
  independent := finiteBad_independent_of_nonNeighbors c s

/-- A local-lemma certificate for a finite constraint family produces a full
assignment satisfying that family.  Outside the union of supports, the
assignment is filled by an arbitrary candidate. -/
theorem finite_satisfiable_of_lllCertificate
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate) (s : Finset Constraint)
    (cert : FiniteLLLCertificate c s) :
    ∃ x : Cell → Candidate, ∀ k ∈ s, (c k).Satisfied x := by
  classical
  obtain ⟨ω, hω⟩ := Erdos797.finite_local_lemma
    (finiteBad c s) cert.neighbor cert.weight cert.weight_nonneg
      cert.weight_lt_one cert.mass cert.independent
  let q₀ : Candidate := Classical.choice inferInstance
  let x : Cell → Candidate := fun i ↦
    if hi : i ∈ supportUnion c s then ω ⟨i, hi⟩ else q₀
  refine ⟨x, ?_⟩
  intro k hk
  let k' : ↑s := ⟨k, hk⟩
  have hgood : (c k).accepts (restrictFinite c s k' ω) := by
    exact not_not.mp (hω k')
  change (c k).accepts (fun i ↦ x i)
  convert hgood using 1
  funext i
  simp only [restrictFinite, x]
  rw [dif_pos]

/-- Finite local-lemma certificates for all finite subfamilies imply one
global assignment satisfying all constraints. -/
theorem exists_global_assignment_of_lllCertificates
    [TopologicalSpace Candidate] [DiscreteTopology Candidate]
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate)
    (hcert : ∀ s : Finset Constraint, FiniteLLLCertificate c s) :
    ∃ x : Cell → Candidate, ∀ k, (c k).Satisfied x := by
  apply exists_global_assignment_of_finitely_satisfiable c
  intro s
  exact finite_satisfiable_of_lllCertificate c s (hcert s)

/-- The usable compactness-plus-LLL theorem for finite-support events. -/
theorem exists_global_assignment_of_finiteSupportLLLWeights
    [TopologicalSpace Candidate] [DiscreteTopology Candidate]
    [Fintype Candidate] [Nonempty Candidate]
    (c : Constraint → LocalConstraint Cell Candidate)
    (hmass : ∀ s : Finset Constraint, FiniteSupportLLLWeights c s) :
    ∃ x : Cell → Candidate, ∀ k, (c k).Satisfied x := by
  apply exists_global_assignment_of_lllCertificates c
  intro s
  exact (hmass s).toCertificate

/-! ## Concentration on a finite product -/

/-- Hoeffding's two-sided inequality for sums of indicator variables on a
finite product of uniform finite alphabets. -/
theorem finiteProduct_indicator_hoeffding
    {I Q : Type*} [Fintype I] [Fintype Q] [Nonempty Q]
    (active : Finset I) (hit : I → Q → Bool) (t : ℝ) (ht : 0 ≤ t) :
    letI : MeasurableSpace Q := ⊤
    let ν : I → MeasureTheory.Measure Q := fun _ ↦
      (PMF.uniformOfFintype Q).toMeasure
    let μ : MeasureTheory.Measure (I → Q) := MeasureTheory.Measure.pi ν
    μ.real {ω | t ≤
        |(∑ i ∈ active, if hit i (ω i) then (1 : ℝ) else 0) -
          ∑ i ∈ active,
            ∫ q, (if hit i q then (1 : ℝ) else 0) ∂ν i|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((active.card : ℝ) / 4))) := by
  let : MeasurableSpace Q := ⊤
  let ν : I → MeasureTheory.Measure Q := fun _ ↦
    (PMF.uniformOfFintype Q).toMeasure
  let μ : MeasureTheory.Measure (I → Q) := MeasureTheory.Measure.pi ν
  let Y : I → (I → Q) → ℝ := fun i ω ↦ if hit i (ω i) then 1 else 0
  let m : I → ℝ := fun i ↦
    ∫ q, (if hit i q then (1 : ℝ) else 0) ∂ν i
  let Z : I → (I → Q) → ℝ := fun i ω ↦ Y i ω - μ[Y i]
  have hν : ∀ i, MeasureTheory.IsProbabilityMeasure (ν i) := by
    intro i
    dsimp [ν]
    infer_instance
  let (i : I) : MeasureTheory.IsProbabilityMeasure (ν i) := hν i
  have hcoord : ProbabilityTheory.iIndepFun (fun i ω ↦ ω i) μ := by
    exact ProbabilityTheory.iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hYmeas : ∀ i,
      Measurable (fun q : Q ↦ if hit i q then (1 : ℝ) else 0) := by
    intro i
    exact measurable_of_finite _
  have hindep : ProbabilityTheory.iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hcoord.comp (fun i q ↦ if hit i q then (1 : ℝ) else 0) hYmeas
  have hindepZ : ProbabilityTheory.iIndepFun Z μ := by
    apply hindep.comp (fun i y ↦ y - μ[Y i])
    intro i
    fun_prop
  have hsub : ∀ i ∈ active,
      ProbabilityTheory.HasSubgaussianMGF (Z i) (1 / 4 : ℝ≥0) μ := by
    intro i hi
    have hYi : AEMeasurable (Y i) μ := by
      simpa [Y, Function.comp_def] using
        (hYmeas i).comp_aemeasurable
          (measurable_pi_apply i).aemeasurable
    have hb : ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with ω
      simp only [Y]
      split_ifs <;> norm_num
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := μ) (X := Y i) (a := (0 : ℝ)) (b := 1) hYi hb
    convert h using 1
    all_goals norm_num [Z]
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hindepZ
    (c := fun _ ↦ (1 / 4 : ℝ≥0)) hsub
  have htail :=
    Erdos228.GaussianWalk.measureReal_abs_ge_le_of_hasSubgaussianMGF hsum ht
  have hmean (i : I) : μ[Y i] = m i := by
    let g : Q → ℝ := fun q ↦ if hit i q then 1 else 0
    have heval : AEMeasurable (fun ω : I → Q ↦ ω i) μ :=
      (measurable_pi_apply i).aemeasurable
    have hg : AEStronglyMeasurable g
        (Measure.map (fun ω : I → Q ↦ ω i) μ) :=
      (measurable_of_finite g).aestronglyMeasurable
    have hi := integral_map heval hg
    rw [(measurePreserving_eval ν i).map_eq] at hi
    simpa [Y, m, g, Function.comp_def] using hi.symm
  simpa [Z, Y, m, hmean, μ, ν, Finset.sum_sub_distrib,
    div_eq_mul_inv] using htail

/-- A finite union bound in the form used by the periodic construction: if
the sum of upper bounds for all bad-event probabilities is below one, some
outcome avoids every event. -/
theorem exists_avoiding_finite_events
    {Ω E : Type*} [Fintype E] [Nonempty Ω]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad : E → Set Ω) (p : E → ℝ)
    (hbad : ∀ e, μ.real (bad e) ≤ p e) (hsum : (∑ e, p e) < 1) :
    ∃ ω : Ω, ∀ e, ω ∉ bad e := by
  classical
  by_contra h
  push Not at h
  have hunion : (⋃ e, bad e) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨e, he⟩ := h ω
    exact Set.mem_iUnion.mpr ⟨e, he⟩
  have hle := MeasureTheory.measureReal_iUnion_fintype_le (μ := μ) bad
  rw [hunion] at hle
  have hone : μ.real Set.univ = 1 := by simp
  rw [hone] at hle
  exact (not_lt_of_ge (hle.trans (Finset.sum_le_sum fun e _ ↦ hbad e))) hsum

end FiniteConstraintModel

end

end GlobalSelection
end Erdos989

namespace Erdos989
namespace FixedRadiusUpper

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
open GlobalSelection

/-! ## The finite periodic jitter model -/

/-- Cells in one square period of side length `L`. -/
abbrev PeriodCell (L : ℕ) := ZMod L × ZMod L

/-- The `q × q` candidate grid inside a unit cell. -/
abbrev GridCandidate (q : ℕ) := Fin q × Fin q

/-- Midpoints of the `q × q` equal subsquares of the unit square. -/
def midpointOffset (q : ℕ) (u : GridCandidate q) : ℝ × ℝ :=
  (((u.1 : ℝ) + 1 / 2) / q, ((u.2 : ℝ) + 1 / 2) / q)

theorem midpointOffset_in_halfOpenUnitSquare {q : ℕ} (hq : 0 < q) :
    OffsetsInHalfOpenUnitSquare (midpointOffset q) := by
  intro u
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hu1lo : 0 ≤ (u.1 : ℝ) := by positivity
  have hu2lo : 0 ≤ (u.2 : ℝ) := by positivity
  have hu1lt : (u.1 : ℝ) < q := by exact_mod_cast u.1.isLt
  have hu2lt : (u.2 : ℝ) < q := by exact_mod_cast u.2.isLt
  have hu1succ : (u.1 : ℝ) + 1 ≤ q := by
    exact_mod_cast (Nat.succ_le_iff.mpr u.1.isLt)
  have hu2succ : (u.2 : ℝ) + 1 ≤ q := by
    exact_mod_cast (Nat.succ_le_iff.mpr u.2.isLt)
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [midpointOffset]
    positivity
  · dsimp [midpointOffset]
    apply (div_lt_one hqR).2
    linarith
  · dsimp [midpointOffset]
    positivity
  · dsimp [midpointOffset]
    apply (div_lt_one hqR).2
    linarith

/-- Reduction of an integer-grid cell modulo a square period. -/
def periodClass (L : ℕ) (cell : PlaneCell) : PeriodCell L :=
  ((cell.1 : ZMod L), (cell.2 : ZMod L))

/-- Extend an assignment on one period to all integer-grid cells. -/
def periodicSelection (L q : ℕ)
    (ω : PeriodCell L → GridCandidate q) : JitteredSelection (GridCandidate q) :=
  fun cell ↦ ω (periodClass L cell)

@[simp] theorem periodicSelection_apply (L q : ℕ)
    (ω : PeriodCell L → GridCandidate q) (cell : PlaneCell) :
    periodicSelection L q ω cell = ω (periodClass L cell) := rfl

end

end FixedRadiusUpper
end Erdos989
