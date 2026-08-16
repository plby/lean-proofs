import Wikipedia.SzemeredisTheorem.Hypergraph.Energy

/-!
# A finite energy-increment regularity step

This file isolates the quantitative part of finite hypergraph regularity which
is independent of the eventual removal argument.  A state consists of a
partition of one finite face space.  For a hypergraph with several face
spaces, such states are simply assembled into a dependent family
(`FaceRegularitySystem` below).

A Boolean cut test is represented by its support `A : Finset Ω`, and hence by
the `{0,1}`-valued function `finsetIndicator A`.  Refining a state by `A`
means adjoining its membership bit to the current partition.  The central
result, `energy_increment_of_booleanCut`, says

`ε ≤ |𝔼 x, residual x * 1_A x|`

implies an energy gain of at least `ε ^ 2`.  The proof is the exact finite
conditional-expectation proof: the new partition makes `1_A` measurable,
Cauchy--Schwarz bounds the correlation by the squared norm of the new
projection, and the Pythagorean identity identifies that norm with the energy
increment.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A canonical finite `{0,1}`-valued cut test, represented by its support. -/
abbrev BooleanCutTest (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω

namespace BooleanCutTest

/-- Evaluation of a Boolean cut test as a real-valued function. -/
def eval (A : BooleanCutTest Ω) : Ω → ℝ :=
  finsetIndicator A

omit [Fintype Ω] in
@[simp]
theorem eval_of_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  finsetIndicator_of_mem hx

omit [Fintype Ω] in
@[simp]
theorem eval_of_not_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  finsetIndicator_of_not_mem hx

omit [Fintype Ω] in
theorem eval_sq (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_nonneg (A : BooleanCutTest Ω) (x : Ω) :
    0 ≤ A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_le_one (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

end BooleanCutTest

/-- A real-valued function is measurable with respect to `P` when it is
constant on every atom of `P`. -/
def IsPartitionMeasurable (P : FacePartition Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x

namespace IsPartitionMeasurable

/-- Measurability is preserved when the partition is refined. -/
theorem of_le {P Q : FacePartition Ω} {g : Ω → ℝ}
    (hPQ : P ≤ Q) (hg : IsPartitionMeasurable Q g) :
    IsPartitionMeasurable P g := by
  intro x y hy
  exact hg x y (FacePartition.part_subset_of_le hPQ x hy)

/-- Conditional averaging fixes measurable functions pointwise. -/
theorem conditionalMean_eq {P : FacePartition Ω} {g : Ω → ℝ}
    (hg : IsPartitionMeasurable P g) (x : Ω) :
    conditionalMean P g x = g x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) g =
        Finset.expect (P.part x) (fun _ => g x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact hg x y hy
    _ = g x := Finset.expect_const (by simp) _

/-- Every conditional average is measurable for its partition. -/
theorem conditionalMean (P : FacePartition Ω) (f : Ω → ℝ) :
    IsPartitionMeasurable P (conditionalMean P f) := by
  intro x y hy
  exact conditionalMean_eq_of_mem_part P f hy

end IsPartitionMeasurable

/-- The indicator of a generator is measurable for the partition generated
by that cut. -/
theorem booleanCut_measurable_generatedBy (A : BooleanCutTest Ω) :
    IsPartitionMeasurable
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have hxy : x ∈ A ↔ y ∈ A := by
    have hsignature :=
      (FacePartition.mem_part_generatedBy_iff
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact hsignature A (by simp)
  by_cases hx : x ∈ A
  · have hyA : y ∈ A := hxy.mp hx
    simp [hx, hyA]
  · have hyA : y ∉ A := by
      intro hy
      exact hx (hxy.mpr hy)
    simp [hx, hyA]

/-- Minimal regularity state for one finite face space. -/
structure FaceRegularityState (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : FacePartition Ω

/-- A collection of per-edge (or per-face-type) regularity states. -/
abbrev FaceRegularitySystem
    (ι : Type*) (face : ι → Type*)
    [∀ i, Fintype (face i)] [∀ i, DecidableEq (face i)] :=
  ∀ i, FaceRegularityState (face i)

namespace FaceRegularityState

/-- The structured component at the current state. -/
noncomputable def structured (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  conditionalMean S.partition f

/-- The residual after removing the current structured component. -/
noncomputable def residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x

/-- The `L²` energy visible at the current state. -/
noncomputable def energy (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : ℝ :=
  partitionEnergy S.partition f

/-- Residual correlation with a Boolean cut test. -/
noncomputable def booleanCutCorrelation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x

/-- Adjoin one cut-membership bit to the current partition. -/
def refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) : FaceRegularityState Ω where
  partition :=
    FacePartition.join S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω)))

@[simp]
theorem partition_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy ({A} : Finset (Finset Ω))) :=
  rfl

/-- Refining by a cut really refines the old partition. -/
theorem refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition ≤ S.partition :=
  FacePartition.join_le_left _ _

/-- The adjoined cut is measurable for the refined partition. -/
theorem booleanCut_measurable_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    IsPartitionMeasurable (S.refineBy A).partition A.eval := by
  apply IsPartitionMeasurable.of_le
    (FacePartition.join_le_right S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))))
  exact booleanCut_measurable_generatedBy A

/-- One Boolean refinement multiplies partition complexity by at most two. -/
theorem complexity_refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    FacePartition.complexity (S.refineBy A).partition ≤
      2 * FacePartition.complexity S.partition := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy ({A} : Finset (Finset Ω))) ≤ 2 := by
    simpa using
      FacePartition.complexity_generatedBy_le
        ({A} : Finset (Finset Ω))
  calc
    FacePartition.complexity (S.refineBy A).partition ≤
        FacePartition.complexity S.partition *
          FacePartition.complexity
            (FacePartition.generatedBy
              ({A} : Finset (Finset Ω))) :=
      FacePartition.complexity_join_le _ _
    _ ≤ FacePartition.complexity S.partition * 2 :=
      Nat.mul_le_mul_left _ hgenerated
    _ = 2 * FacePartition.complexity S.partition := by
      omega

/-- The structured component of a `[0,1]`-valued function remains
nonnegative. -/
theorem structured_nonneg (S : FaceRegularityState Ω)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ S.structured f x :=
  conditionalMean_nonneg S.partition hf x

/-- The structured component of a `[0,1]`-valued function is at most one. -/
theorem structured_le_one (S : FaceRegularityState Ω)
    {f : Ω → ℝ} (hf : ∀ x, f x ≤ 1) (x : Ω) :
    S.structured f x ≤ 1 :=
  conditionalMean_le_one S.partition hf x

/-- The residual has conditional mean zero on every current atom. -/
@[simp]
theorem conditionalMean_residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean S.partition (S.residual f) x = 0 := by
  change
    conditionalMean S.partition
      (fun y => f y - conditionalMean S.partition f y) x = 0
  rw [conditionalMean_sub]
  rw [conditionalMean_idem]
  ring

/-- The residual has global mean zero. -/
@[simp]
theorem mean_residual (S : FaceRegularityState Ω) (f : Ω → ℝ) :
    mean (S.residual f) = 0 := by
  change
    mean (fun x => f x - conditionalMean S.partition f x) = 0
  rw [mean_sub]
  rw [mean_conditionalMean]
  ring

/-- Projecting the old residual onto a refinement gives exactly the change
in structured components. -/
theorem conditionalMean_residual_refineBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) (x : Ω) :
    conditionalMean (S.refineBy A).partition (S.residual f) x =
      (S.refineBy A).structured f x - S.structured f x := by
  change
    conditionalMean (S.refineBy A).partition
        (fun y => f y - conditionalMean S.partition f y) x =
      conditionalMean (S.refineBy A).partition f x -
        conditionalMean S.partition f x
  rw [conditionalMean_sub]
  rw [conditionalMean_reverse_tower_of_le
    (S.refineBy A).partition S.partition (S.refineBy_le A)]

/-- A measurable factor may be pulled through a conditional projection in a
global pairing. -/
theorem mean_mul_eq_mean_conditionalMean_mul
    (P : FacePartition Ω) (u v : Ω → ℝ)
    (hv : IsPartitionMeasurable P v) :
    mean (fun x => u x * v x) =
      mean (fun x => conditionalMean P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (conditionalMean P (fun x => u x * v x)) :=
      (mean_conditionalMean P _).symm
    _ = mean (fun x => conditionalMean P u x * v x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_right_of_constant_on_part
        P u v x (hv x)

/-- The residual/cut pairing is the pairing of the new structured increment
with the same cut. -/
theorem booleanCutCorrelation_eq_projection
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [booleanCutCorrelation]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          conditionalMean (S.refineBy A).partition (S.residual f) x *
            A.eval x) :=
      mean_mul_eq_mean_conditionalMean_mul
        (S.refineBy A).partition (S.residual f) A.eval
        (S.booleanCut_measurable_refineBy A)
    _ = mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.conditionalMean_residual_refineBy f A x]

omit [DecidableEq Ω] in
/-- Global finite Cauchy--Schwarz for the normalized mean. -/
theorem mean_mul_sq_le_sq_mul_sq (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

/-- A Boolean cut test has squared `L²` norm at most one. -/
theorem mean_booleanCut_sq_le_one [Nonempty Ω]
    (A : BooleanCutTest Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  rw [A.eval_sq x]
  exact A.eval_le_one x

/-- Pythagoras identifies the energy increment under one cut refinement. -/
theorem energy_refineBy_sub_eq_mean_sq
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).energy f - S.energy f =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      (S.refineBy A).partition S.partition (S.refineBy_le A) f

/-- Squared residual correlation with a Boolean cut is bounded by the exact
energy gained after adjoining that cut. -/
theorem booleanCutCorrelation_sq_le_energyIncrement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A ^ 2 ≤
      (S.refineBy A).energy f - S.energy f := by
  rw [S.booleanCutCorrelation_eq_projection f A]
  let d : Ω → ℝ :=
    fun x => (S.refineBy A).structured f x - S.structured f x
  have hcs :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    mean_mul_sq_le_sq_mul_sq d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hA := mean_booleanCut_sq_le_one A
  calc
    mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := hcs
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.refineBy A).energy f - S.energy f := by
      exact (S.energy_refineBy_sub_eq_mean_sq f A).symm

/-- **Quantitative energy increment.**  Residual correlation at least `ε`
in absolute value against a `{0,1}` cut test forces energy gain at least
`ε ^ 2` after adjoining that test. -/
theorem energy_increment_of_booleanCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcorrelation : ε ≤ |S.booleanCutCorrelation f A|) :
    S.energy f + ε ^ 2 ≤ (S.refineBy A).energy f := by
  have hsquare :
      ε ^ 2 ≤ S.booleanCutCorrelation f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hcorrelation
  have hincrement :=
    S.booleanCutCorrelation_sq_le_energyIncrement f A
  linarith

/-- A state is regular against a finite family of Boolean cuts if every
residual correlation is at most `ε` in absolute value. -/
def IsRegularAgainst (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    (ε : ℝ) : Prop :=
  ∀ A ∈ cuts, |S.booleanCutCorrelation f A| ≤ ε

/-- Failure of regularity supplies a cut whose correlation is strictly above
the threshold. -/
theorem exists_booleanCut_of_not_regular
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬ S.IsRegularAgainst f cuts ε) :
    ∃ A ∈ cuts, ε < |S.booleanCutCorrelation f A| := by
  classical
  by_contra hnone
  apply h
  intro A hA
  by_contra hle
  apply hnone
  exact ⟨A, hA, lt_of_not_ge hle⟩

/-- Telescoping form of the bounded-energy argument.  A `[0,1]`-valued
target cannot support more than unit total energy gain. -/
theorem energy_increment_budget [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (f : Ω → ℝ) {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hgain : ∀ i, i < m →
      (states i).energy f + ε ^ 2 ≤ (states (i + 1)).energy f) :
    (m : ℝ) * ε ^ 2 ≤ 1 := by
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          (states i).energy f + ε ^ 2 ≤
            (states (i + 1)).energy f) →
        (states 0).energy f + (n : ℝ) * ε ^ 2 ≤
          (states n).energy f := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious := ih (fun i hi =>
          hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          (states 0).energy f + (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              ((states 0).energy f + (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤ (states n).energy f + ε ^ 2 :=
            by linarith
          _ ≤ (states (Nat.succ n)).energy f := by
            simpa [Nat.succ_eq_add_one] using hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤ (states 0).energy f :=
    partitionEnergy_nonneg (states 0).partition f
  have hupper :
      (states m).energy f ≤ 1 :=
    partitionEnergy_le_one (states m).partition hf0 hf1
  linarith

/-- Explicit finite termination certificate: once
`1 < m * ε^2`, a run of `m` consecutive `ε^2` energy increments is
impossible for a `[0,1]`-valued target. -/
theorem no_long_energy_increment_run [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (f : Ω → ℝ) {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hlong : 1 < (m : ℝ) * ε ^ 2)
    (hgain : ∀ i, i < m →
      (states i).energy f + ε ^ 2 ≤
        (states (i + 1)).energy f) :
    False := by
  have hbudget :=
    energy_increment_budget states f hf0 hf1 hgain
  linarith

/-- A regularity loop which refines by a correlated Boolean witness must
encounter a regular state before its energy budget is exhausted. -/
theorem exists_regular_state_in_refinement_run [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (witness : ℕ → BooleanCutTest Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2)
    (hrefine : ∀ i, i < m →
      states (i + 1) = (states i).refineBy (witness i))
    (hchoose : ∀ i, i < m →
      ¬(states i).IsRegularAgainst f cuts ε →
      witness i ∈ cuts ∧
        ε ≤ |(states i).booleanCutCorrelation f (witness i)|) :
    ∃ i, i < m ∧ (states i).IsRegularAgainst f cuts ε := by
  by_contra hregular
  have hnotregular :
      ∀ i, i < m →
        ¬(states i).IsRegularAgainst f cuts ε := by
    intro i hi hisRegular
    exact hregular ⟨i, hi, hisRegular⟩
  have hgain :
      ∀ i, i < m →
        (states i).energy f + ε ^ 2 ≤
          (states (i + 1)).energy f := by
    intro i hi
    have hcorrelation :=
      (hchoose i hi (hnotregular i hi)).2
    have hincrement :=
      (states i).energy_increment_of_booleanCut
        f (witness i) hε hcorrelation
    rw [hrefine i hi]
    exact hincrement
  exact no_long_energy_increment_run
    states f hf0 hf1 hlong hgain

/-- Select a violating Boolean cut when the current state is irregular.
At a regular state the empty cut is used, so iteration remains total. -/
noncomputable def chosenIrregularCut
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsRegularAgainst f cuts ε then ∅
    else
      Classical.choose
        (S.exists_booleanCut_of_not_regular f cuts h)

theorem chosenIrregularCut_mem
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsRegularAgainst f cuts ε) :
    S.chosenIrregularCut f cuts ε ∈ cuts := by
  simp only [chosenIrregularCut, dif_neg h]
  exact
    (Classical.choose_spec
      (S.exists_booleanCut_of_not_regular f cuts h)).1

theorem chosenIrregularCut_correlation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsRegularAgainst f cuts ε) :
    ε <
      |S.booleanCutCorrelation f
        (S.chosenIrregularCut f cuts ε)| := by
  simp only [chosenIrregularCut, dif_neg h]
  exact
    (Classical.choose_spec
      (S.exists_booleanCut_of_not_regular f cuts h)).2

/-- The actual weak-regularity refinement run obtained by repeatedly
adjoining the selected violating cut. -/
noncomputable def regularityRun
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := regularityRun S f cuts ε n
      T.refineBy (T.chosenIrregularCut f cuts ε)

@[simp]
theorem regularityRun_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem regularityRun_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRun f cuts ε (n + 1) =
      (S.regularityRun f cuts ε n).refineBy
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε) :=
  rfl

/-- Every state in the canonical run refines the initial partition. -/
theorem regularityRun_partition_le
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    (S.regularityRun f cuts ε n).partition ≤ S.partition := by
  induction n with
  | zero =>
      exact le_rfl
  | succ n ih =>
      exact
        le_trans
          ((S.regularityRun f cuts ε n).refineBy_le
            ((S.regularityRun f cuts ε n).chosenIrregularCut
              f cuts ε))
          ih

/-- After `n` Boolean refinements, complexity has grown by at most `2^n`. -/
theorem regularityRun_complexity_le
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    FacePartition.complexity
        (S.regularityRun f cuts ε n).partition ≤
      2 ^ n * FacePartition.complexity S.partition := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (S.regularityRun f cuts ε (n + 1)).partition ≤
            2 * FacePartition.complexity
              (S.regularityRun f cuts ε n).partition := by
          rw [regularityRun_succ]
          exact
            (S.regularityRun f cuts ε n).complexity_refineBy_le
              ((S.regularityRun f cuts ε n).chosenIrregularCut
                f cuts ε)
        _ ≤ 2 * (2 ^ n *
              FacePartition.complexity S.partition) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) *
              FacePartition.complexity S.partition := by
          rw [pow_succ]
          ring

/-- The finite family of Boolean cuts adjoined during the first `n` steps
of the canonical run. -/
noncomputable def regularityRunCuts
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.regularityRun f cuts ε i).chosenIrregularCut
      f cuts ε

@[simp]
theorem regularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRunCuts f cuts ε 0 = ∅ := by
  simp [regularityRunCuts]

@[simp]
theorem regularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
        (S.regularityRunCuts f cuts ε n) := by
  classical
  simp [regularityRunCuts, Finset.range_add_one]

/-- If the allowed family contains the empty cut, the canonical selector
always remains inside that family, including after regularity is reached. -/
theorem chosenIrregularCut_mem_of_empty_mem
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    S.chosenIrregularCut f cuts ε ∈ cuts := by
  by_cases hregular : S.IsRegularAgainst f cuts ε
  · simpa [chosenIrregularCut, hregular] using hempty
  · exact S.chosenIrregularCut_mem f cuts ε hregular

/-- Every cut recorded by a run belongs to the allowed cut family when that
family contains the empty cut. -/
theorem regularityRunCuts_subset
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε n ⊆ cuts := by
  classical
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact chosenIrregularCut_mem_of_empty_mem
    (S.regularityRun f cuts ε i) f cuts ε hempty

/-- The current run partition is exactly the input partition refined by the
finite list of cuts recorded so far.  This retains the lower-face generator
certificate needed by recursive removal. -/
theorem regularityRun_partition_eq_join_generatedBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    (S.regularityRun f cuts ε n).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy
          (S.regularityRunCuts f cuts ε n)) := by
  induction n with
  | zero =>
      rw [regularityRun_zero, regularityRunCuts_zero,
        FacePartition.generatedBy_empty]
      change S.partition = S.partition ⊓ ⊤
      exact (inf_top_eq S.partition).symm
  | succ n ih =>
      let A : BooleanCutTest Ω :=
        (S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε
      calc
        (S.regularityRun f cuts ε (n + 1)).partition =
            FacePartition.join
              (S.regularityRun f cuts ε n).partition
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rfl
        _ =
            FacePartition.join
              (FacePartition.join S.partition
                (FacePartition.generatedBy
                  (S.regularityRunCuts f cuts ε n)))
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rw [ih]
        _ =
            FacePartition.join S.partition
              (FacePartition.join
                (FacePartition.generatedBy
                  (S.regularityRunCuts f cuts ε n))
                (FacePartition.generatedBy
                  ({A} : Finset (Finset Ω)))) := by
          exact inf_assoc _ _ _
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (insert A
                  (S.regularityRunCuts f cuts ε n))) := by
          rw [FacePartition.generatedBy_insert]
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (S.regularityRunCuts f cuts ε (n + 1))) := by
          rw [regularityRunCuts_succ]

/-- The canonical run itself reaches a regular index before the prescribed
energy-budget cutoff. -/
theorem exists_regular_run_index_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ, i < m ∧
      (S.regularityRun f cuts ε i).IsRegularAgainst
        f cuts ε := by
  exact
    exists_regular_state_in_refinement_run
      (S.regularityRun f cuts ε)
      (fun n =>
        (S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
      f cuts hf0 hf1 hε hlong
      (fun n _ => S.regularityRun_succ f cuts ε n)
      (fun n _ hn =>
        ⟨(S.regularityRun f cuts ε n).chosenIrregularCut_mem
            f cuts ε hn,
          le_of_lt
            (chosenIrregularCut_correlation
              (S.regularityRun f cuts ε n) f cuts ε hn)⟩)

/-- The canonical run encounters a regular refinement before any prescribed
energy-budget cutoff. -/
theorem exists_regular_refinement_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ, ∃ T : FaceRegularityState Ω,
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsRegularAgainst f cuts ε ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  obtain ⟨i, hi, hregular⟩ :=
    S.exists_regular_run_index_before f cuts
      hf0 hf1 hε hlong
  exact
    ⟨i, S.regularityRun f cuts ε i, hi,
      S.regularityRun_partition_le f cuts ε i,
      hregular,
      S.regularityRun_complexity_le f cuts ε i⟩

/-- A positive regularity threshold admits a finite, ambient-size-independent
energy budget and hence a regular refinement. -/
theorem exists_regular_refinement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState Ω,
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsRegularAgainst f cuts ε ∧
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
  obtain ⟨i, T, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement_before f cuts
      hf0 hf1 hε.le hlong
  exact
    ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩

/-- In particular, one may regularize simultaneously against every Boolean
cut on the finite face space. -/
theorem exists_regular_refinement_allCuts [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState Ω,
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      (∀ A : BooleanCutTest Ω,
        |T.booleanCutCorrelation f A| ≤ ε) ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  classical
  obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement f
      (Finset.univ : Finset (BooleanCutTest Ω))
      hf0 hf1 hε
  refine ⟨m, i, T, hlong, hi, hTS, ?_, hcomplexity⟩
  intro A
  exact hregular A (Finset.mem_univ A)

end FaceRegularityState

end Wikipedia.SzemeredisTheorem
