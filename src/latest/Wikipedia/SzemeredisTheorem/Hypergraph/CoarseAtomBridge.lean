import Mathlib.Algebra.Order.Chebyshev
import Wikipedia.SzemeredisTheorem.Finite.Bonferroni
import Wikipedia.SzemeredisTheorem.Hypergraph.BoundaryBernoulli
import Wikipedia.SzemeredisTheorem.Hypergraph.FullOrderedRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedGoodAtoms

/-!
# Passing from fine upper atoms to coarse upper atoms

Strong ordered regularity naturally controls every atom of a fine upper
partition, while the removal argument benefits from choosing its closed
configuration in a fixed coarse complex.  This file supplies the finite
bridge between those two choices.

For a refinement `fineUpper ≤ coarseUpper`, every coarse atom is the
disjoint union of the fine atoms which it contains.  Consequently its
indicator is their sum.  Linearity then transfers cut regularity, with the
number of contained fine atoms as the exact loss.  The same decomposition,
followed by finite Cauchy--Schwarz and a fiberwise sum, controls the
coarse-upper atom-energy gap by the fine-upper gap with only one fine
complexity factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse fibers of fine atoms -/

/-- The coarse atom containing the canonical representative of a fine
atom.  Under `fineUpper ≤ coarseUpper`, the whole fine atom lies in this
coarse atom. -/
noncomputable def coarseAtomOfFineAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (b : fineUpper.parts) :
    coarseUpper.parts :=
  partitionAtomAt coarseUpper
    (fineUpper.representative b)

/-- The fiber of fine atoms assigned to one coarse atom. -/
noncomputable def fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) :
    Finset fineUpper.parts := by
  classical
  exact
    (Finset.univ : Finset fineUpper.parts).filter fun b =>
      coarseAtomOfFineAtom fineUpper coarseUpper b = a

@[simp]
theorem mem_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) (b : fineUpper.parts) :
    b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a ↔
      coarseAtomOfFineAtom fineUpper coarseUpper b = a := by
  classical
  simp [fineAtomsInCoarseAtom]

/-- Refinement puts every point of a fine atom in the coarse atom selected
by its representative. -/
theorem fineAtom_subset_coarseAtomOfFineAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (b : fineUpper.parts) :
    b.1 ⊆
      (coarseAtomOfFineAtom fineUpper coarseUpper b).1 := by
  have hsubset :=
    FacePartition.part_subset_of_le hupper
      (fineUpper.representative b)
  rw [fineUpper.part_representative b] at hsubset
  exact hsubset

/-- Taking the fine atom at a point and then passing to its coarse atom is
the same as taking the coarse atom at that point. -/
theorem coarseAtomOfFineAtom_partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (x : Ω) :
    coarseAtomOfFineAtom fineUpper coarseUpper
        (partitionAtomAt fineUpper x) =
      partitionAtomAt coarseUpper x := by
  apply Subtype.ext
  have hrepresentative :
      fineUpper.representative
          (partitionAtomAt fineUpper x) ∈
        coarseUpper.part x := by
    apply FacePartition.part_subset_of_le hupper x
    exact fineUpper.representative_mem
      (partitionAtomAt fineUpper x)
  exact coarseUpper.part_eq_of_mem
    (coarseUpper.part_mem.2 (Finset.mem_univ x))
    hrepresentative

/-- A coarse atom is exactly the union of its contained fine atoms. -/
theorem partitionAtomUnion_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) :
    partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) =
      a.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, hxb⟩ :=
      (mem_partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) x).1 hx
    have hba :
        coarseAtomOfFineAtom fineUpper coarseUpper b = a :=
      (mem_fineAtomsInCoarseAtom
        fineUpper coarseUpper a b).1 hb
    rw [← hba]
    exact fineAtom_subset_coarseAtomOfFineAtom
      hupper b hxb
  · intro hx
    apply
      (mem_partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) x).2
    refine ⟨partitionAtomAt fineUpper x, ?_, ?_⟩
    · apply
        (mem_fineAtomsInCoarseAtom
          fineUpper coarseUpper a
          (partitionAtomAt fineUpper x)).2
      rw [coarseAtomOfFineAtom_partitionAtomAt
        hupper x]
      exact
        (partitionAtomAt_eq_iff_mem
          coarseUpper x a).2 hx
    · exact fineUpper.mem_part (Finset.mem_univ x)

/-- The indicator of a coarse atom is the sum of the indicators of its
contained fine atoms. -/
theorem partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) (x : Ω) :
    partitionAtomIndicator coarseUpper a x =
      ∑ b ∈ fineAtomsInCoarseAtom
          fineUpper coarseUpper a,
        partitionAtomIndicator fineUpper b x := by
  rw [← finsetIndicator_partitionAtomUnion
    fineUpper
    (fineAtomsInCoarseAtom fineUpper coarseUpper a) x]
  unfold partitionAtomIndicator
  rw [partitionAtomUnion_fineAtomsInCoarseAtom
    hupper a]

/-- Function-valued form of the coarse-atom indicator decomposition. -/
theorem partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) :
    partitionAtomIndicator coarseUpper a =
      fun x =>
        ∑ b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a,
          partitionAtomIndicator fineUpper b x := by
  funext x
  exact partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom
    hupper a x

/-- A coarse fiber contains no more atoms than the whole fine
partition. -/
theorem card_fineAtomsInCoarseAtom_le_complexity
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) :
    (fineAtomsInCoarseAtom fineUpper coarseUpper a).card ≤
      FacePartition.complexity fineUpper := by
  classical
  calc
    (fineAtomsInCoarseAtom
        fineUpper coarseUpper a).card ≤
        (Finset.univ : Finset fineUpper.parts).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = FacePartition.complexity fineUpper := by
      simp [FacePartition.complexity]

/-! ## Linear transfer of cut regularity -/

/-- Conditional averaging commutes with a sum over an arbitrary finite
index set. -/
theorem conditionalMean_finset_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    (P : FacePartition Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, conditionalMean P (f i) x := by
  unfold conditionalMean
  exact Finset.expect_sum_comm (P.part x) s
    (fun y i => f i y)

/-- Face-cut correlation is linear over a finite sum of target
functions. -/
theorem FaceRegularityState.faceCutCorrelation_finset_sum
    {G ι : Type*} [Fintype G] [DecidableEq G]
    [Fintype ι] [DecidableEq ι]
    {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (s : Finset ι)
    (f : ι → (Fin r → G) → ℝ)
    (u : CutTestFamily G r) :
    S.faceCutCorrelation
        (fun x => ∑ i ∈ s, f i x) u =
      ∑ i ∈ s, S.faceCutCorrelation (f i) u := by
  unfold FaceRegularityState.faceCutCorrelation
  calc
    mean (fun x =>
        S.residual (fun y => ∑ i ∈ s, f i y) x *
          cutTestProduct u x) =
        mean (fun x =>
          ∑ i ∈ s,
            S.residual (f i) x *
              cutTestProduct u x) := by
      apply congrArg mean
      funext x
      unfold FaceRegularityState.residual
        FaceRegularityState.structured
      rw [conditionalMean_finset_sum]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    _ =
        ∑ i ∈ s,
          mean (fun x =>
            S.residual (f i) x *
              cutTestProduct u x) :=
      mean_finset_sum s
        (fun i x =>
          S.residual (f i) x *
            cutTestProduct u x)
    _ = ∑ i ∈ s, S.faceCutCorrelation (f i) u := by
      rfl

/-- Boolean-cut correlation is linear over a finite sum of target
functions. -/
theorem FaceRegularityState.booleanCutCorrelation_finset_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    (S : FaceRegularityState Ω)
    (s : Finset ι) (f : ι → Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation
        (fun x => ∑ i ∈ s, f i x) A =
      ∑ i ∈ s, S.booleanCutCorrelation (f i) A := by
  unfold FaceRegularityState.booleanCutCorrelation
  calc
    mean (fun x =>
        S.residual (fun y => ∑ i ∈ s, f i y) x *
          A.eval x) =
        mean (fun x =>
          ∑ i ∈ s,
            S.residual (f i) x * A.eval x) := by
      apply congrArg mean
      funext x
      unfold FaceRegularityState.residual
        FaceRegularityState.structured
      rw [conditionalMean_finset_sum]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    _ =
        ∑ i ∈ s,
          mean (fun x =>
            S.residual (f i) x * A.eval x) :=
      mean_finset_sum s
        (fun i x => S.residual (f i) x * A.eval x)
    _ =
        ∑ i ∈ s,
          S.booleanCutCorrelation (f i) A := by
      rfl

/-- If every contained fine atom is face-cut regular with error `ε`, then
the containing coarse atom has error at most the number of contained atoms
times `ε`. -/
theorem FaceRegularityState.abs_coarseAtom_faceCutCorrelation_le_card_mul
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    {fineUpper coarseUpper :
      FacePartition (Fin r → G)}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts)
    {ε : ℝ}
    (hregular :
      ∀ b : fineUpper.parts,
        S.IsFaceCutRegular
          (partitionAtomIndicator fineUpper b) ε)
    (u : CutTestFamily G r)
    (hu : IsBoundedCutTest u) :
    |S.faceCutCorrelation
        (partitionAtomIndicator coarseUpper a) u| ≤
      ((fineAtomsInCoarseAtom
        fineUpper coarseUpper a).card : ℝ) * ε := by
  rw [partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    hupper a,
    S.faceCutCorrelation_finset_sum]
  calc
    |∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
        S.faceCutCorrelation
          (partitionAtomIndicator fineUpper b) u| ≤
        ∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
          |S.faceCutCorrelation
            (partitionAtomIndicator fineUpper b) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a, ε := by
      apply Finset.sum_le_sum
      intro b _
      exact hregular b u hu
    _ =
        ((fineAtomsInCoarseAtom
          fineUpper coarseUpper a).card : ℝ) * ε := by
      simp

/-- Boolean-cut version of the coarse-atom regularity transfer. -/
theorem FaceRegularityState.abs_coarseAtom_booleanCutCorrelation_le_card_mul
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts)
    (A : BooleanCutTest Ω)
    {ε : ℝ}
    (hregular :
      ∀ b : fineUpper.parts,
        |S.booleanCutCorrelation
          (partitionAtomIndicator fineUpper b) A| ≤ ε)
    :
    |S.booleanCutCorrelation
        (partitionAtomIndicator coarseUpper a) A| ≤
      ((fineAtomsInCoarseAtom
        fineUpper coarseUpper a).card : ℝ) * ε := by
  rw [partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    hupper a,
    S.booleanCutCorrelation_finset_sum]
  calc
    |∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
        S.booleanCutCorrelation
          (partitionAtomIndicator fineUpper b) A| ≤
        ∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
          |S.booleanCutCorrelation
            (partitionAtomIndicator fineUpper b) A| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a, ε := by
      apply Finset.sum_le_sum
      intro b _
      exact hregular b
    _ =
        ((fineAtomsInCoarseAtom
          fineUpper coarseUpper a).card : ℝ) * ε := by
      simp

/-- Preliminary regularity for all fine upper atoms controls every bounded
cut correlation of a coarse upper atom, with the exact coarse-fiber
cardinality loss. -/
theorem abs_orderedCoarseUpperAtom_faceCutCorrelation_le_card_mul
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (fineUpper coarseUpper :
      OrderedFacePartitionSystem G k (j + 1))
    (hupper :
      OrderedFacePartitionRefines fineUpper coarseUpper)
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower fineUpper ε)
    (e : OrderedFace k (j + 1))
    (a : (coarseUpper e).parts)
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u) :
    |(⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G)).faceCutCorrelation
        (partitionAtomIndicator (coarseUpper e) a) u| ≤
      ((fineAtomsInCoarseAtom
        (fineUpper e) (coarseUpper e) a).card : ℝ) * ε := by
  apply
    FaceRegularityState.abs_coarseAtom_faceCutCorrelation_le_card_mul
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (hupper e) a
  · intro b
    exact (hregular.toBounded) e b
  · exact hu

/-- Complexity-only form of the bounded coarse-upper cut estimate. -/
theorem abs_orderedCoarseUpperAtom_faceCutCorrelation_le_complexity_mul
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (fineUpper coarseUpper :
      OrderedFacePartitionSystem G k (j + 1))
    (hupper :
      OrderedFacePartitionRefines fineUpper coarseUpper)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hregular :
      IsPreliminaryOrderedRegular lower fineUpper ε)
    (e : OrderedFace k (j + 1))
    (a : (coarseUpper e).parts)
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u) :
    |(⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G)).faceCutCorrelation
        (partitionAtomIndicator (coarseUpper e) a) u| ≤
      (FacePartition.complexity (fineUpper e) : ℝ) * ε := by
  exact le_trans
    (abs_orderedCoarseUpperAtom_faceCutCorrelation_le_card_mul
      lower fineUpper coarseUpper hupper hregular e a u hu)
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr
        (card_fineAtomsInCoarseAtom_le_complexity
          (fineUpper e) (coarseUpper e) a))
      hε)

/-- A uniform bound on fine-upper complexity transfers preliminary
regularity itself from the fine upper system to the coarse upper system. -/
theorem IsPreliminaryOrderedRegular.coarseUpper
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (fineUpper coarseUpper :
      OrderedFacePartitionSystem G k (j + 1))
    (hupper :
      OrderedFacePartitionRefines fineUpper coarseUpper)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hregular :
      IsPreliminaryOrderedRegular lower fineUpper ε)
    (M : ℕ)
    (hcomplexity :
      ∀ e, FacePartition.complexity (fineUpper e) ≤ M) :
    IsPreliminaryOrderedRegular
      lower coarseUpper ((M : ℝ) * ε) := by
  intro e a b
  have hcard :=
    FaceRegularityState.abs_coarseAtom_booleanCutCorrelation_le_card_mul
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (hupper e) a
      (boundaryBooleanCutSupport b)
      (fun c => hregular e c b)
  exact le_trans hcard
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr
        ((card_fineAtomsInCoarseAtom_le_complexity
          (fineUpper e) (coarseUpper e) a).trans
          (hcomplexity e)))
      hε)

/-! ## Coarse-upper atom-energy gaps -/

/-- The coarse-upper boundary defect is the sum of the boundary defects of
the fine atoms in its fiber. -/
theorem atomBoundaryDefect_coarseAtom_eq_sum_fineAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineBoundary coarseBoundary :
      FacePartition Ω)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) (x : Ω) :
    atomBoundaryDefect
        fineBoundary coarseBoundary coarseUpper a x =
      ∑ b ∈ fineAtomsInCoarseAtom
          fineUpper coarseUpper a,
        atomBoundaryDefect
          fineBoundary coarseBoundary fineUpper b x := by
  unfold atomBoundaryDefect
  rw [partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    hupper a]
  rw [conditionalMean_finset_sum,
    conditionalMean_finset_sum,
    ← Finset.sum_sub_distrib]

/-- Pointwise finite Cauchy--Schwarz for the defect of one coarse upper
atom. -/
theorem atomBoundaryDefect_coarseAtom_sq_le_card_mul_sum
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineBoundary coarseBoundary :
      FacePartition Ω)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) (x : Ω) :
    atomBoundaryDefect
          fineBoundary coarseBoundary coarseUpper a x ^ 2 ≤
      ((fineAtomsInCoarseAtom
          fineUpper coarseUpper a).card : ℝ) *
        ∑ b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a,
          atomBoundaryDefect
            fineBoundary coarseBoundary fineUpper b x ^ 2 := by
  rw [atomBoundaryDefect_coarseAtom_eq_sum_fineAtoms
    fineBoundary coarseBoundary hupper a x]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := fineAtomsInCoarseAtom
        fineUpper coarseUpper a)
      (f := fun b =>
        atomBoundaryDefect
          fineBoundary coarseBoundary fineUpper b x))

/-- Averaged square-defect bound for one coarse upper atom, retaining the
exact fiber cardinality. -/
theorem mean_atomBoundaryDefect_coarseAtom_sq_le_card_mul_sum
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineBoundary coarseBoundary :
      FacePartition Ω)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) :
    mean (fun x =>
        atomBoundaryDefect
          fineBoundary coarseBoundary coarseUpper a x ^ 2) ≤
      ((fineAtomsInCoarseAtom
          fineUpper coarseUpper a).card : ℝ) *
        ∑ b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a,
          mean (fun x =>
            atomBoundaryDefect
              fineBoundary coarseBoundary fineUpper b x ^ 2) := by
  calc
    mean (fun x =>
        atomBoundaryDefect
          fineBoundary coarseBoundary coarseUpper a x ^ 2) ≤
        mean (fun x =>
          ((fineAtomsInCoarseAtom
              fineUpper coarseUpper a).card : ℝ) *
            ∑ b ∈ fineAtomsInCoarseAtom
                fineUpper coarseUpper a,
              atomBoundaryDefect
                fineBoundary coarseBoundary fineUpper b x ^ 2) :=
      mean_mono fun x =>
        atomBoundaryDefect_coarseAtom_sq_le_card_mul_sum
          fineBoundary coarseBoundary hupper a x
    _ =
        ((fineAtomsInCoarseAtom
            fineUpper coarseUpper a).card : ℝ) *
          mean (fun x =>
            ∑ b ∈ fineAtomsInCoarseAtom
                fineUpper coarseUpper a,
              atomBoundaryDefect
                fineBoundary coarseBoundary fineUpper b x ^ 2) :=
      mean_smul _ _
    _ =
        ((fineAtomsInCoarseAtom
            fineUpper coarseUpper a).card : ℝ) *
          ∑ b ∈ fineAtomsInCoarseAtom
              fineUpper coarseUpper a,
            mean (fun x =>
              atomBoundaryDefect
                fineBoundary coarseBoundary fineUpper b x ^ 2) := by
      rw [mean_finset_sum]

/-- The coarse fibers partition all fine atoms, so a fiberwise double sum
counts each fine atom exactly once. -/
theorem sum_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (F : fineUpper.parts → ℝ) :
    ∑ a : coarseUpper.parts,
        ∑ b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a, F b =
      ∑ b : fineUpper.parts, F b := by
  classical
  simpa [fineAtomsInCoarseAtom] using
    (Finset.sum_fiberwise
      (Finset.univ : Finset fineUpper.parts)
      (coarseAtomOfFineAtom fineUpper coarseUpper) F)

/-- **Coarse-upper atom-energy bridge.**  For fixed fine and coarse
observing partitions, replacing a fine upper partition by a coarser upper
partition increases the atom-energy gap by at most one factor of the fine
upper complexity. -/
theorem partitionAtomEnergy_sub_coarseUpper_le_complexity_mul_fineUpper
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineBoundary coarseBoundary :
      FacePartition Ω}
    (hboundary : fineBoundary ≤ coarseBoundary)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper) :
    partitionAtomEnergy fineBoundary coarseUpper -
        partitionAtomEnergy coarseBoundary coarseUpper ≤
      (FacePartition.complexity fineUpper : ℝ) *
        (partitionAtomEnergy fineBoundary fineUpper -
          partitionAtomEnergy coarseBoundary fineUpper) := by
  rw [partitionAtomEnergy_sub_eq_sum_mean_sq
    hboundary coarseUpper,
    partitionAtomEnergy_sub_eq_sum_mean_sq
      hboundary fineUpper]
  change
    (∑ a : coarseUpper.parts,
      mean (fun x =>
        atomBoundaryDefect
          fineBoundary coarseBoundary coarseUpper a x ^ 2)) ≤
      (FacePartition.complexity fineUpper : ℝ) *
        ∑ b : fineUpper.parts,
          mean (fun x =>
            atomBoundaryDefect
              fineBoundary coarseBoundary fineUpper b x ^ 2)
  calc
    (∑ a : coarseUpper.parts,
        mean (fun x =>
          atomBoundaryDefect
            fineBoundary coarseBoundary coarseUpper a x ^ 2)) ≤
        ∑ a : coarseUpper.parts,
          (FacePartition.complexity fineUpper : ℝ) *
            ∑ b ∈ fineAtomsInCoarseAtom
                fineUpper coarseUpper a,
              mean (fun x =>
                atomBoundaryDefect
                  fineBoundary coarseBoundary fineUpper b x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact le_trans
        (mean_atomBoundaryDefect_coarseAtom_sq_le_card_mul_sum
          fineBoundary coarseBoundary hupper a)
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (card_fineAtomsInCoarseAtom_le_complexity
              fineUpper coarseUpper a))
          (Finset.sum_nonneg fun b _ =>
            mean_nonneg fun x => sq_nonneg _))
    _ =
        (FacePartition.complexity fineUpper : ℝ) *
          ∑ a : coarseUpper.parts,
            ∑ b ∈ fineAtomsInCoarseAtom
                fineUpper coarseUpper a,
              mean (fun x =>
                atomBoundaryDefect
                  fineBoundary coarseBoundary fineUpper b x ^ 2) := by
      rw [Finset.mul_sum]
    _ =
        (FacePartition.complexity fineUpper : ℝ) *
          ∑ b : fineUpper.parts,
            mean (fun x =>
              atomBoundaryDefect
                fineBoundary coarseBoundary fineUpper b x ^ 2) := by
      rw [sum_fineAtomsInCoarseAtom]

/-- Ordered-face specialization of the coarse-upper atom-energy bridge. -/
theorem orderedAtomEnergy_sub_coarseUpper_le_complexity_mul_fineUpper
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fineLower coarseLower :
      OrderedFacePartitionSystem G k j}
    (hlower :
      OrderedFacePartitionRefines fineLower coarseLower)
    (e : OrderedFace k (j + 1))
    {fineUpper coarseUpper :
      FacePartition (Fin (j + 1) → G)}
    (hupper : fineUpper ≤ coarseUpper) :
    orderedAtomEnergy fineLower e coarseUpper -
        orderedAtomEnergy coarseLower e coarseUpper ≤
      (FacePartition.complexity fineUpper : ℝ) *
        (orderedAtomEnergy fineLower e fineUpper -
          orderedAtomEnergy coarseLower e fineUpper) := by
  exact
    partitionAtomEnergy_sub_coarseUpper_le_complexity_mul_fineUpper
      (orderedBoundaryPartition_mono hlower e) hupper

namespace OrderedCoarseFineComplex

/-- The lower-boundary energy gap measured against the atoms of the
*coarse* upper face partition. -/
noncomputable def coarseUpperFaceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.coarse.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.coarse.partition j.succ e)

/-- Coarse-upper local gaps are nonnegative. -/
theorem coarseUpperFaceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.coarseUpperFaceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.coarse.partition j.succ e)

/-- The coarse-upper local gap is controlled by the existing frozen
fine-upper gap with one fine-upper complexity factor. -/
theorem coarseUpperFaceAtomEnergyGap_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.coarseUpperFaceAtomEnergyGap j e ≤
      (FacePartition.complexity
          (P.fine.partition j.succ e) : ℝ) *
        P.faceAtomEnergyGap j e := by
  exact
    orderedAtomEnergy_sub_coarseUpper_le_complexity_mul_fineUpper
      (fun f => P.refines j.castSucc f) e
      (P.refines j.succ e)

/-- The rank-`j` coarse-upper gap, summed over all ordered upper faces. -/
noncomputable def coarseUpperLayerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.coarse.partition j.succ)

/-- A coarse-upper layer gap is the sum of its local face gaps. -/
theorem coarseUpperLayerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.coarseUpperLayerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.coarseUpperFaceAtomEnergyGap j e := by
  unfold coarseUpperLayerAtomEnergyGap
    coarseUpperFaceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl

/-- Sharp facewise-complexity form of the coarse-upper layer-gap
comparison. -/
theorem coarseUpperLayerAtomEnergyGap_le_sum_complexity_mul
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.coarseUpperLayerAtomEnergyGap j ≤
      ∑ e : OrderedFace k (j.1 + 1),
        (FacePartition.complexity
            (P.fine.partition j.succ e) : ℝ) *
          P.faceAtomEnergyGap j e := by
  rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face j]
  exact Finset.sum_le_sum fun e _ =>
    P.coarseUpperFaceAtomEnergyGap_le j e

/-- Uniform-complexity form of the coarse-upper layer-gap comparison. -/
theorem coarseUpperLayerAtomEnergyGap_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (M : ℕ)
    (hcomplexity :
      ∀ e : OrderedFace k (j.1 + 1),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M) :
    P.coarseUpperLayerAtomEnergyGap j ≤
      (M : ℝ) * P.layerAtomEnergyGap j := by
  rw [P.layerAtomEnergyGap_eq_sum_face j]
  calc
    P.coarseUpperLayerAtomEnergyGap j ≤
        ∑ e : OrderedFace k (j.1 + 1),
          (FacePartition.complexity
              (P.fine.partition j.succ e) : ℝ) *
            P.faceAtomEnergyGap j e :=
      P.coarseUpperLayerAtomEnergyGap_le_sum_complexity_mul j
    _ ≤
        ∑ e : OrderedFace k (j.1 + 1),
          (M : ℝ) * P.faceAtomEnergyGap j e := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (hcomplexity e))
        (P.faceAtomEnergyGap_nonneg j e)
    _ =
        (M : ℝ) *
          ∑ e : OrderedFace k (j.1 + 1),
            P.faceAtomEnergyGap j e := by
      rw [Finset.mul_sum]

/-- Full preliminary regularity of the fine complex transfers at one rank
to the coarse upper layer, with a preassigned fine-upper complexity
bound.  The observing lower boundary remains the fine lower layer. -/
theorem preliminaryRegular_coarseUpper
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (j : Fin r) (M : ℕ)
    (hε : 0 ≤ ε j)
    (hcomplexity :
      ∀ e : OrderedFace k (j.1 + 1),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M) :
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      ((M : ℝ) * ε j) := by
  exact (hregular j).coarseUpper
    (P.fine.partition j.castSucc)
    (P.fine.partition j.succ)
    (P.coarse.partition j.succ)
    (fun e => P.refines j.succ e)
    hε M hcomplexity

end OrderedCoarseFineComplex

end Wikipedia.SzemeredisTheorem
