import Wikipedia.SzemeredisTheorem.Hypergraph.Regularity
import Wikipedia.SzemeredisTheorem.Transference.BooleanCutReduction

/-!
# Weak regularity against lower-face cut tests

For a function on `Fin r → G`, the hypergraph cut tests are products of
`r` functions, with the `i`th factor omitting coordinate `i`.  A Boolean
cut-test family has a support in the full tuple space.  This file connects
those supports to the abstract energy-increment machinery and proves a
genuine finite weak-regularity lemma:

* the output refines the input partition;
* its complexity grows by an ambient-size-independent power of two;
* the residual is small against every `[0,1]`-valued lower-face cut test.

The passage from Boolean to bounded tests is an exact finite Bernoulli
mixture, not an approximation.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The full-tuple support of a Boolean lower-face cut-test family. -/
noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true

@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]

/-- The indicator of a Boolean cut support is exactly the corresponding
product of Boolean lower-face tests. -/
theorem booleanFaceCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, eraseCoordinate i x⟩ = true
  · have hx : x ∈ booleanFaceCutSupport b := by
      simp [booleanFaceCutSupport, h]
    rw [BooleanCutTest.eval_of_mem _ hx]
    unfold cutTestProduct
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [cutTestFamilyOfBooleanAssignment, booleanValue, h i]
  · have hx : x ∉ booleanFaceCutSupport b := by
      simpa [booleanFaceCutSupport] using h
    rw [BooleanCutTest.eval_of_not_mem _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, eraseCoordinate i x⟩ with
    | false =>
        unfold cutTestProduct
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [cutTestFamilyOfBooleanAssignment,
          booleanValue, hb]
    | true =>
        exact (hi hb).elim

/-- The finite family of all Boolean lower-face cut supports. -/
noncomputable def booleanFaceCutSupports
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ) :
    Finset (BooleanCutTest (Fin r → G)) := by
  classical
  exact Finset.univ.image booleanFaceCutSupport

theorem booleanFaceCutSupport_mem_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    booleanFaceCutSupport b ∈ booleanFaceCutSupports G r := by
  classical
  exact Finset.mem_image.mpr
    ⟨b, Finset.mem_univ b, rfl⟩

/-- At positive arity, the constantly false assignment has empty full-tuple
support. -/
theorem booleanFaceCutSupport_false
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ} (hr : 0 < r) :
    booleanFaceCutSupport
        (fun _ : CutTestCoordinate G r => false) =
      ∅ := by
  classical
  ext x
  constructor
  · intro hx
    have hall :=
      (mem_booleanFaceCutSupport
        (fun _ : CutTestCoordinate G r => false) x).1 hx
    have hfalse := hall ⟨0, hr⟩
    simp at hfalse
  · intro hx
    simp at hx

/-- Hence the finite family of Boolean face-cut supports contains the empty
cut whenever at least one face coordinate is present. -/
theorem empty_mem_booleanFaceCutSupports
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ} (hr : 0 < r) :
    (∅ : BooleanCutTest (Fin r → G)) ∈
      booleanFaceCutSupports G r := by
  classical
  apply Finset.mem_image.mpr
  refine
    ⟨(fun _ : CutTestCoordinate G r => false),
      Finset.mem_univ _, ?_⟩
  exact booleanFaceCutSupport_false hr

namespace FaceRegularityState

/-- Correlation of a regularity residual with a lower-face product test. -/
noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x

/-- On Boolean tests, face-cut correlation is the existing Boolean support
correlation used by the energy increment. -/
theorem faceCutCorrelation_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : BooleanCutAssignment G r) :
    S.faceCutCorrelation f
        (cutTestFamilyOfBooleanAssignment b) =
      S.booleanCutCorrelation f (booleanFaceCutSupport b) := by
  unfold faceCutCorrelation booleanCutCorrelation
  apply congrArg mean
  funext x
  rw [booleanFaceCutSupport_eval]

/-- Exact Bernoulli-mixture formula for one face-cut correlation. -/
theorem faceCutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold faceCutCorrelation
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cutTestProduct u x) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      rw [cutTestProduct_eq_sum_boolean u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : BooleanCutAssignment G r,
          mean (fun x : Fin r → G =>
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

/-- Weak cut regularity of one face function. -/
def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε

/-- Controlling the finite Boolean-support family controls every bounded
lower-face product test. -/
theorem isFaceCutRegular_of_regularAgainst_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) {ε : ℝ}
    (hregular :
      S.IsRegularAgainst f (booleanFaceCutSupports G r) ε) :
    S.IsFaceCutRegular f ε := by
  intro u hu
  rw [faceCutCorrelation_eq_sum_boolean]
  calc
    |∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b)| ≤
        ∑ b : BooleanCutAssignment G r,
          |bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            S.faceCutCorrelation f
              (cutTestFamilyOfBooleanAssignment b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw :
          0 ≤ bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b :=
        bernoulliAssignmentWeight_nonneg
          (p := cutTestCoordinateValue u)
          (fun q => hu.nonneg q.1 q.2)
          (fun q => hu.le_one q.1 q.2) b
      rw [abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      rw [faceCutCorrelation_boolean]
      exact hregular (booleanFaceCutSupport b)
        (booleanFaceCutSupport_mem_supports b)
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_bernoulliAssignmentWeight, one_mul]

/-- **Finite weak hypergraph regularity.**  A bounded function on an
`r`-fold finite product has a bounded-complexity partition refinement whose
residual is small against every lower-face product cut. -/
theorem exists_faceCutRegular_refinement
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState (Fin r → G),
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsFaceCutRegular f ε ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement f
      (booleanFaceCutSupports G r) hf0 hf1 hε
  exact
    ⟨m, i, T, hlong, hi, hTS,
      T.isFaceCutRegular_of_regularAgainst_supports f hregular,
      hcomplexity⟩

/-- Fixed-budget, generator-retaining weak regularity.  The prescribed
budget is essential when this construction is iterated: it keeps every
complexity bound independent of the ambient finite set and of the function
being regularized. -/
theorem exists_faceCutRegular_refinement_with_generators_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        i < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ i ∧
        T.IsFaceCutRegular f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ i * FacePartition.complexity S.partition := by
  let cuts := booleanFaceCutSupports G r
  obtain ⟨i, hi, hregular⟩ :=
    S.exists_regular_run_index_before f cuts
      hf0 hf1 hε hlong
  let T := S.regularityRun f cuts ε i
  let F := S.regularityRunCuts f cuts ε i
  have hpart :
      T.partition =
        FacePartition.join S.partition
          (FacePartition.generatedBy F) :=
    S.regularityRun_partition_eq_join_generatedBy
      f cuts ε i
  have hsubset :
      F ⊆ booleanFaceCutSupports G r := by
    exact S.regularityRunCuts_subset f cuts ε
      (by
        dsimp [cuts]
        exact empty_mem_booleanFaceCutSupports hr)
      i
  have hcard : F.card ≤ i := by
    unfold F regularityRunCuts
    exact Finset.card_image_le.trans_eq (Finset.card_range i)
  have hface : T.IsFaceCutRegular f ε :=
    T.isFaceCutRegular_of_regularAgainst_supports
      f hregular
  have hcomplexity :
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition :=
    S.regularityRun_complexity_le f cuts ε i
  exact
    ⟨i, T, F, hi, hpart, hsubset,
      hcard, hface, hcomplexity⟩

/-- Generator-retaining form of weak regularity.  At positive arity the
output partition is explicitly the input partition refined by at most `i`
Boolean lower-face cut supports, each drawn from the canonical finite support
family. -/
theorem exists_faceCutRegular_refinement_with_generators
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        1 < (m : ℝ) * ε ^ 2 ∧
        i < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ i ∧
        T.IsFaceCutRegular f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ i * FacePartition.complexity S.partition := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε ^ 2)
  have hlong : 1 < (m : ℝ) * ε ^ 2 := by
    calc
      1 = (1 / ε ^ 2) * ε ^ 2 := by
        field_simp
      _ < (m : ℝ) * ε ^ 2 :=
        mul_lt_mul_of_pos_right hm hεsq
  obtain ⟨i, T, F, hi, hpart, hsubset, hcard,
      hface, hcomplexity⟩ :=
    S.exists_faceCutRegular_refinement_with_generators_before
      hr f hf0 hf1 hε.le hlong
  exact
    ⟨m, i, T, F, hlong, hi, hpart, hsubset,
      hcard, hface, hcomplexity⟩

end FaceRegularityState

end Wikipedia.SzemeredisTheorem
