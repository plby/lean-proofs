import Wikipedia.SzemeredisTheorem.Hypergraph.FamilyRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedBoundaryPartition

/-!
# Atom-family energy on shared ordered boundaries

Full hypergraph regularity simultaneously controls the indicators of every
atom in an upper-face partition.  Because those atoms are disjoint and
exhaust the tuple space, their aggregate conditional-expectation energy is
at most one.  This is substantially sharper than treating them as an
arbitrary family, whose naive energy budget is the number of targets.

This file first proves the generic finite-partition atom identities, then
specializes the energy to the shared ordered-boundary partitions from
`OrderedBoundaryPartition.lean`.  The final Pythagorean identity is the exact
coarse/fine defect budget used to show that most closed atom configurations
are good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Indicators of genuine partition atoms -/

/-- Indicator of one genuine atom of a finite partition. -/
def partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) :
    Ω → ℝ :=
  finsetIndicator a.1

@[simp]
theorem partitionAtomIndicator_of_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    partitionAtomIndicator Q a x = 1 :=
  finsetIndicator_of_mem hx

@[simp]
theorem partitionAtomIndicator_of_not_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    partitionAtomIndicator Q a x = 0 :=
  finsetIndicator_of_not_mem hx

theorem partitionAtomIndicator_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    0 ≤ partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ^ 2 =
      partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

/-- The genuine partition atoms form an exact pointwise partition of
unity. -/
theorem sum_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts, partitionAtomIndicator Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact partitionAtomIndicator_of_mem Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb hba
    apply partitionAtomIndicator_of_not_mem
    intro hxb
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 hxb
        (Q.mem_part (Finset.mem_univ x))
    exact hba heq
  · intro hax
    exact (hax (Finset.mem_univ ax)).elim

/-- Conditional averaging commutes with a finite sum of functions. -/
theorem conditionalMean_fintype_sum
    {Ω κ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype κ]
    (P : FacePartition Ω) (f : κ → Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => ∑ i : κ, f i y) x =
      ∑ i : κ, conditionalMean P (f i) x := by
  unfold conditionalMean
  exact Finset.expect_sum_comm
    (P.part x) (Finset.univ : Finset κ)
    (fun y i => f i y)

/-- The conditional probabilities of all genuine atoms sum to one at every
point. -/
theorem sum_conditionalMean_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts,
        conditionalMean P (partitionAtomIndicator Q a) x =
      1 := by
  rw [← conditionalMean_fintype_sum]
  convert conditionalMean_const P 1 x using 2
  funext y
  exact sum_partitionAtomIndicator Q y

/-- Aggregate energy of all genuine atoms of `Q`, observed through `P`. -/
noncomputable def partitionAtomEnergy
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) : ℝ :=
  ∑ a : Q.parts,
    Wikipedia.SzemeredisTheorem.partitionEnergy P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) :
    0 ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  exact Finset.sum_nonneg fun a _ =>
    Wikipedia.SzemeredisTheorem.partitionEnergy_nonneg P
      (partitionAtomIndicator Q a)

/-- Disjointness improves the aggregate atom-energy budget from the number
of atoms to one. -/
theorem partitionAtomEnergy_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : FacePartition Ω) :
    partitionAtomEnergy P Q ≤ 1 := by
  unfold partitionAtomEnergy
  calc
    (∑ a : Q.parts,
        Wikipedia.SzemeredisTheorem.partitionEnergy P
          (partitionAtomIndicator Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            partitionAtomIndicator Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact partitionEnergy_le_mean_sq P
        (partitionAtomIndicator Q a)
    _ =
        ∑ a : Q.parts,
          mean (partitionAtomIndicator Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact partitionAtomIndicator_sq Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, partitionAtomIndicator Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => partitionAtomIndicator Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact sum_partitionAtomIndicator Q x
    _ = 1 := mean_const 1

/-- Refinement of the observing partition increases aggregate atom
energy. -/
theorem partitionAtomEnergy_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy R Q ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  apply Finset.sum_le_sum
  intro a _
  exact partitionEnergy_mono P R hPR
    (partitionAtomIndicator Q a)

/-- Exact aggregate Pythagorean identity for all upper atoms. -/
theorem partitionAtomEnergy_sub_eq_sum_mean_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy P Q - partitionAtomEnergy R Q =
      ∑ a : Q.parts,
        mean (fun x =>
          (conditionalMean P (partitionAtomIndicator Q a) x -
            conditionalMean R (partitionAtomIndicator Q a) x) ^ 2) := by
  unfold partitionAtomEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact partitionEnergy_sub_eq_mean_sq P R hPR
    (partitionAtomIndicator Q a)

/-! ## Ordered shared-boundary atom energy -/

/-- Aggregate energy of an upper-face partition, observed through the
shared partitions on its immediate lower faces. -/
noncomputable def orderedAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) : ℝ :=
  partitionAtomEnergy (orderedBoundaryPartition lower e) upper

theorem orderedAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    0 ≤ orderedAtomEnergy lower e upper :=
  partitionAtomEnergy_nonneg _ _

theorem orderedAtomEnergy_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy lower e upper ≤ 1 :=
  partitionAtomEnergy_le_one _ _

/-- Refining the shared lower layer increases every upper-face atom
energy. -/
theorem orderedAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy coarse e upper ≤
      orderedAtomEnergy fine e upper := by
  exact partitionAtomEnergy_mono
    (orderedBoundaryPartition_mono hfc e) upper

/-- The coarse/fine gap is the sum, over genuine upper atoms, of the exact
mean-square changes in their boundary conditional densities. -/
theorem orderedAtomEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy fine e upper -
        orderedAtomEnergy coarse e upper =
      ∑ a : upper.parts,
        mean (fun x =>
          (orderedBoundaryStructured fine e
                (partitionAtomIndicator upper a) x -
            orderedBoundaryStructured coarse e
                (partitionAtomIndicator upper a) x) ^ 2) := by
  exact partitionAtomEnergy_sub_eq_sum_mean_sq
    (orderedBoundaryPartition_mono hfc e) upper

end Wikipedia.SzemeredisTheorem
