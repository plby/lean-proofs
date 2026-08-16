import Wikipedia.SzemeredisTheorem.Hypergraph.WeakRegularity

/-!
# Simultaneous weak regularity for a finite family

The all-rank hypergraph regularity argument must regularize every atom of a
bounded-complexity partition, not merely the original edge indicator.  This
file supplies the finite-family energy-increment engine needed for that step.

For a family `f : ι → Ω → ℝ`, the potential is the sum of the partition
energies of all `f i`.  It lies between zero and `Fintype.card ι` when every
target is `[0,1]`-valued.  If any target has a Boolean-cut correlation larger
than `ε`, adjoining that cut increases its energy by at least `ε ^ 2`, while
monotonicity shows that every other summand can only increase.  Thus a common
refinement regular for the whole family is reached in fewer than any `m`
with

`Fintype.card ι < m * ε ^ 2`.

As in `Regularity.lean`, the canonical run records its actual generators.
The last theorem specializes the abstract result to lower-face product tests,
which is the form used by the forthcoming shared-skeleton regularity system.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]
  [Fintype ι] [DecidableEq ι]

namespace FaceRegularityState

/-- Total energy of a finite family of functions in one common partition. -/
noncomputable def familyEnergy
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ) : ℝ :=
  ∑ i, S.energy (f i)

/-- One state is regular for a family when it is regular for every member. -/
def IsFamilyRegularAgainst
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) : Prop :=
  ∀ i, S.IsRegularAgainst (f i) cuts ε

/-- Total family energy is nonnegative. -/
theorem familyEnergy_nonneg
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ) :
    0 ≤ S.familyEnergy f := by
  unfold familyEnergy
  exact Finset.sum_nonneg fun i _ =>
    partitionEnergy_nonneg S.partition (f i)

/-- A finite family of `[0,1]`-valued functions has total energy at most its
cardinality. -/
theorem familyEnergy_le_card [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1) :
    S.familyEnergy f ≤ (Fintype.card ι : ℝ) := by
  unfold familyEnergy
  calc
    (∑ i, S.energy (f i)) ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact partitionEnergy_le_one S.partition
        (hf0 i) (hf1 i)
    _ = (Fintype.card ι : ℝ) := by simp

/-- Refining the common partition can only increase total family energy. -/
theorem familyEnergy_mono
    (S T : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (hTS : T.partition ≤ S.partition) :
    S.familyEnergy f ≤ T.familyEnergy f := by
  unfold familyEnergy
  apply Finset.sum_le_sum
  intro i _
  exact partitionEnergy_mono T.partition S.partition
    hTS (f i)

/-- If one member of the family gains `ε²` under a refinement, then the
whole family potential gains `ε²`; all other summands are charged only by
monotonicity. -/
theorem familyEnergy_refineBy_increment
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (i : ι) (A : BooleanCutTest Ω) {ε : ℝ}
    (hgain :
      S.energy (f i) + ε ^ 2 ≤
        (S.refineBy A).energy (f i)) :
    S.familyEnergy f + ε ^ 2 ≤
      (S.refineBy A).familyEnergy f := by
  classical
  let U : Finset ι := Finset.univ
  have hiU : i ∈ U := by simp [U]
  have hother :
      ∑ j ∈ U.erase i, S.energy (f j) ≤
        ∑ j ∈ U.erase i, (S.refineBy A).energy (f j) := by
    apply Finset.sum_le_sum
    intro j _
    exact partitionEnergy_mono
      (S.refineBy A).partition S.partition
      (S.refineBy_le A) (f j)
  unfold familyEnergy
  change
    (∑ j ∈ U, S.energy (f j)) + ε ^ 2 ≤
      ∑ j ∈ U, (S.refineBy A).energy (f j)
  calc
    (∑ j ∈ U, S.energy (f j)) + ε ^ 2 =
        (∑ j ∈ U.erase i, S.energy (f j)) +
          (S.energy (f i) + ε ^ 2) := by
      rw [← Finset.sum_erase_add U
        (fun j => S.energy (f j)) hiU]
      ring
    _ ≤
        (∑ j ∈ U.erase i, (S.refineBy A).energy (f j)) +
          (S.refineBy A).energy (f i) :=
      add_le_add hother hgain
    _ = ∑ j ∈ U, (S.refineBy A).energy (f j) := by
      exact Finset.sum_erase_add U
        (fun j => (S.refineBy A).energy (f j)) hiU

/-- Failure of family regularity identifies both a target and a violating
Boolean cut. -/
theorem exists_index_booleanCut_of_not_familyRegular
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι, ∃ A ∈ cuts,
      ε < |S.booleanCutCorrelation (f i) A| := by
  classical
  unfold IsFamilyRegularAgainst at h
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨A, hA, hcorr⟩ :=
    S.exists_booleanCut_of_not_regular (f i) cuts hi
  exact ⟨i, A, hA, hcorr⟩

/-- Data attached to a failure of simultaneous regularity. -/
structure FamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) where
  index : ι
  cut : BooleanCutTest Ω
  mem_cuts : cut ∈ cuts
  correlation :
    ε < |S.booleanCutCorrelation (f index) cut|

/-- Choose one violating target/cut pair from a failed family-regularity
statement. -/
noncomputable def chosenFamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.FamilyIrregularWitness f cuts ε := by
  classical
  let hex :=
    S.exists_index_booleanCut_of_not_familyRegular f cuts h
  let i : ι := Classical.choose hex
  let hi := Classical.choose_spec hex
  let A : BooleanCutTest Ω := Classical.choose hi
  have hA :=
    (Classical.choose_spec hi).1
  have hcorr :=
    (Classical.choose_spec hi).2
  exact ⟨i, A, hA, hcorr⟩

/-- Select a violating cut for the family.  Once regularity has been reached,
the empty cut is used so that the iteration remains total. -/
noncomputable def chosenFamilyIrregularCut
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsFamilyRegularAgainst f cuts ε then ∅
    else (S.chosenFamilyIrregularWitness f cuts ε h).cut

theorem chosenFamilyIrregularCut_mem
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.chosenFamilyIrregularCut f cuts ε ∈ cuts := by
  simp only [chosenFamilyIrregularCut, dif_neg h]
  exact
    (S.chosenFamilyIrregularWitness f cuts ε h).mem_cuts

/-- At an irregular state, the selected cut witnesses a violation for some
member of the family. -/
theorem exists_chosenFamilyIrregularCut_correlation
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι,
      ε <
        |S.booleanCutCorrelation (f i)
          (S.chosenFamilyIrregularCut f cuts ε)| := by
  let W := S.chosenFamilyIrregularWitness f cuts ε h
  refine ⟨W.index, ?_⟩
  simp only [chosenFamilyIrregularCut, dif_neg h]
  exact W.correlation

/-- The selected violating cut raises total family energy by at least
`ε²`. -/
theorem familyEnergy_increment_chosenFamilyCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.familyEnergy f + ε ^ 2 ≤
      (S.refineBy
        (S.chosenFamilyIrregularCut f cuts ε)).familyEnergy f := by
  obtain ⟨i, hcorr⟩ :=
    S.exists_chosenFamilyIrregularCut_correlation f cuts ε h
  apply S.familyEnergy_refineBy_increment f i
  exact S.energy_increment_of_booleanCut
    (f i) (S.chosenFamilyIrregularCut f cuts ε)
    hε (le_of_lt hcorr)

/-- Canonical common refinement run for a finite family. -/
noncomputable def familyRegularityRun
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := familyRegularityRun S f cuts ε n
      T.refineBy (T.chosenFamilyIrregularCut f cuts ε)

@[simp]
theorem familyRegularityRun_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem familyRegularityRun_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRun f cuts ε (n + 1) =
      (S.familyRegularityRun f cuts ε n).refineBy
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε) :=
  rfl

/-- Every state of the family run refines the input partition. -/
theorem familyRegularityRun_partition_le
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    (S.familyRegularityRun f cuts ε n).partition ≤
      S.partition := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact le_trans
        ((S.familyRegularityRun f cuts ε n).refineBy_le
          ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
            f cuts ε))
        ih

/-- Complexity grows by at most a factor of two at each family step. -/
theorem familyRegularityRun_complexity_le
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    FacePartition.complexity
        (S.familyRegularityRun f cuts ε n).partition ≤
      2 ^ n * FacePartition.complexity S.partition := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (S.familyRegularityRun f cuts ε (n + 1)).partition ≤
            2 * FacePartition.complexity
              (S.familyRegularityRun f cuts ε n).partition := by
          rw [familyRegularityRun_succ]
          exact
            (S.familyRegularityRun f cuts ε n).complexity_refineBy_le
              ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
                f cuts ε)
        _ ≤ 2 * (2 ^ n *
              FacePartition.complexity S.partition) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) *
              FacePartition.complexity S.partition := by
          rw [pow_succ]
          ring

/-- The finite set of cuts adjoined during the first `n` family steps. -/
noncomputable def familyRegularityRunCuts
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.familyRegularityRun f cuts ε i).chosenFamilyIrregularCut
      f cuts ε

@[simp]
theorem familyRegularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRunCuts f cuts ε 0 = ∅ := by
  simp [familyRegularityRunCuts]

@[simp]
theorem familyRegularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε)
        (S.familyRegularityRunCuts f cuts ε n) := by
  classical
  simp [familyRegularityRunCuts, Finset.range_add_one]

/-- If the allowed family contains the empty cut, every selected cut belongs
to it, including the stationary choices after regularity. -/
theorem chosenFamilyIrregularCut_mem_of_empty_mem
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    S.chosenFamilyIrregularCut f cuts ε ∈ cuts := by
  by_cases hregular :
      S.IsFamilyRegularAgainst f cuts ε
  · simpa [chosenFamilyIrregularCut, hregular] using hempty
  · exact S.chosenFamilyIrregularCut_mem f cuts ε hregular

theorem familyRegularityRunCuts_subset
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε n ⊆ cuts := by
  classical
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact chosenFamilyIrregularCut_mem_of_empty_mem
    (S.familyRegularityRun f cuts ε i) f cuts ε hempty

/-- The run partition is exactly the initial partition joined with the
partition generated by the recorded family cuts. -/
theorem familyRegularityRun_partition_eq_join_generatedBy
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    (S.familyRegularityRun f cuts ε n).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy
          (S.familyRegularityRunCuts f cuts ε n)) := by
  induction n with
  | zero =>
      rw [familyRegularityRun_zero, familyRegularityRunCuts_zero,
        FacePartition.generatedBy_empty]
      change S.partition = S.partition ⊓ ⊤
      exact (inf_top_eq S.partition).symm
  | succ n ih =>
      let A : BooleanCutTest Ω :=
        (S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε
      calc
        (S.familyRegularityRun f cuts ε (n + 1)).partition =
            FacePartition.join
              (S.familyRegularityRun f cuts ε n).partition
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rfl
        _ =
            FacePartition.join
              (FacePartition.join S.partition
                (FacePartition.generatedBy
                  (S.familyRegularityRunCuts f cuts ε n)))
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rw [ih]
        _ =
            FacePartition.join S.partition
              (FacePartition.join
                (FacePartition.generatedBy
                  (S.familyRegularityRunCuts f cuts ε n))
                (FacePartition.generatedBy
                  ({A} : Finset (Finset Ω)))) := by
          exact inf_assoc _ _ _
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (insert A
                  (S.familyRegularityRunCuts f cuts ε n))) := by
          rw [FacePartition.generatedBy_insert]
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (S.familyRegularityRunCuts f cuts ε (n + 1))) := by
          rw [familyRegularityRunCuts_succ]

/-- A run with more steps than the total energy budget must meet a state
regular for every target. -/
theorem exists_familyRegular_run_index_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      (S.familyRegularityRun f cuts ε n).IsFamilyRegularAgainst
        f cuts ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬(S.familyRegularityRun f cuts ε n).IsFamilyRegularAgainst
          f cuts ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        (S.familyRegularityRun f cuts ε n).familyEnergy f +
            ε ^ 2 ≤
          (S.familyRegularityRun f cuts ε (n + 1)).familyEnergy
            f := by
    intro n hn
    rw [familyRegularityRun_succ]
    exact
      familyEnergy_increment_chosenFamilyCut
        (S.familyRegularityRun f cuts ε n)
        f cuts hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          (S.familyRegularityRun f cuts ε i).familyEnergy f +
              ε ^ 2 ≤
            (S.familyRegularityRun f cuts ε (i + 1)).familyEnergy f) →
          (S.familyRegularityRun f cuts ε 0).familyEnergy f +
              (n : ℝ) * ε ^ 2 ≤
            (S.familyRegularityRun f cuts ε n).familyEnergy f := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          (S.familyRegularityRun f cuts ε 0).familyEnergy f +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              ((S.familyRegularityRun f cuts ε 0).familyEnergy f +
                (n : ℝ) * ε ^ 2) + ε ^ 2 := by
            push_cast
            ring
          _ ≤
              (S.familyRegularityRun f cuts ε n).familyEnergy f +
                ε ^ 2 := by linarith
          _ ≤
              (S.familyRegularityRun f cuts ε (n + 1)).familyEnergy
                f := hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤ (S.familyRegularityRun f cuts ε 0).familyEnergy f :=
    (S.familyRegularityRun f cuts ε 0).familyEnergy_nonneg f
  have hupper :
      (S.familyRegularityRun f cuts ε m).familyEnergy f ≤
        (Fintype.card ι : ℝ) :=
    (S.familyRegularityRun f cuts ε m).familyEnergy_le_card
      f hf0 hf1
  linarith

/-- Fixed-budget simultaneous regularity, retaining every actual generator.
The bound depends only on the finite family size and the requested
regularity threshold, never on `Fintype.card Ω`. -/
theorem exists_familyRegular_refinement_with_generators_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    ∃ n : ℕ, ∃ T : FaceRegularityState Ω,
      ∃ F : Finset (BooleanCutTest Ω),
        n < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ cuts ∧
        F.card ≤ n ∧
        T.IsFamilyRegularAgainst f cuts ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ n * FacePartition.complexity S.partition := by
  obtain ⟨n, hn, hregular⟩ :=
    S.exists_familyRegular_run_index_before f cuts
      hf0 hf1 hε hlong
  let T := S.familyRegularityRun f cuts ε n
  let F := S.familyRegularityRunCuts f cuts ε n
  refine ⟨n, T, F, hn, ?_, ?_, ?_, hregular, ?_⟩
  · exact S.familyRegularityRun_partition_eq_join_generatedBy
      f cuts ε n
  · exact S.familyRegularityRunCuts_subset f cuts ε hempty n
  · unfold F familyRegularityRunCuts
    exact Finset.card_image_le.trans_eq (Finset.card_range n)
  · exact S.familyRegularityRun_complexity_le f cuts ε n

/-- Simultaneous lower-face cut regularity for a finite family. -/
def IsFaceCutRegularFamily
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ i, S.IsFaceCutRegular (f i) ε

/-- Boolean support regularity of the family controls all bounded
lower-face product tests for every target. -/
theorem isFaceCutRegularFamily_of_familyRegularAgainst_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ) {ε : ℝ}
    (hregular :
      S.IsFamilyRegularAgainst f
        (booleanFaceCutSupports G r) ε) :
    S.IsFaceCutRegularFamily f ε := by
  intro i
  exact S.isFaceCutRegular_of_regularAgainst_supports
    (f i) (hregular i)

/-- Fixed-budget, generator-retaining simultaneous weak hypergraph
regularity.  This is the finite-family kernel used when the targets are the
indicators of all atoms in one bounded-complexity upper partition. -/
theorem exists_faceCutRegularFamily_refinement_with_generators_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ)
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        n < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ n ∧
        T.IsFaceCutRegularFamily f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ n * FacePartition.complexity S.partition := by
  obtain ⟨n, T, F, hn, hpart, hsubset, hcard,
      hregular, hcomplexity⟩ :=
    S.exists_familyRegular_refinement_with_generators_before
      f (booleanFaceCutSupports G r)
      hf0 hf1 hε hlong
      (empty_mem_booleanFaceCutSupports hr)
  exact
    ⟨n, T, F, hn, hpart, hsubset, hcard,
      T.isFaceCutRegularFamily_of_familyRegularAgainst_supports
        f hregular,
      hcomplexity⟩

end FaceRegularityState

end Wikipedia.SzemeredisTheorem
