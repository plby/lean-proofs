import ErdosProblems.Erdos888.Foundations
import ErdosProblems.Erdos888.LargestPrimes
import ErdosProblems.Erdos888.BlockEncoding
import ErdosProblems.Erdos888.ColoredGraph
import ErdosProblems.Erdos888.SmoothCore

/-!
# The squarefree dyadic-block cover for Erdős problem 888

This file turns the arithmetic two-largest-prime decomposition into the
finite coloured graphs to which `ColoredGraph.sum_edgeCount_le` applies.
All choices below are canonical only in the harmless `Classical.choose`
sense; `TwoLargestPrimeDecomposition.unique` proves that the coordinates do
not depend on the witness chosen.
-/

open scoped BigOperators

namespace Erdos888

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The hypotheses under which an integer has two distinguished largest
prime factors. -/
def HasTwoPrimeFactors (a : ℕ) : Prop :=
  0 < a ∧ Squarefree a ∧ 2 ≤ a.primeFactors.card

/-- The core and the two endpoint primes attached to a nonexceptional
squarefree integer. -/
@[ext] structure BlockCoordinates where
  core : ℕ
  left : ℕ
  right : ℕ
deriving DecidableEq

private theorem exists_blockCoordinates {a : ℕ} (ha : HasTwoPrimeFactors a) :
    ∃ z : BlockCoordinates,
      TwoLargestPrimeDecomposition a z.core z.left z.right := by
  obtain ⟨c, p, q, h⟩ :=
    exists_twoLargestPrimeDecomposition ha.1 ha.2.1 ha.2.2
  exact ⟨⟨c, p, q⟩, h⟩

/-- Chosen two-largest-prime coordinates.  The default branch is never used
for a member of the rich part of a squarefree admissible set. -/
noncomputable def blockCoordinates (a : ℕ) : BlockCoordinates :=
  if ha : HasTwoPrimeFactors a then Classical.choose (exists_blockCoordinates ha)
  else ⟨1, 2, 3⟩

theorem blockCoordinates_spec {a : ℕ} (ha : HasTwoPrimeFactors a) :
    TwoLargestPrimeDecomposition a (blockCoordinates a).core
      (blockCoordinates a).left (blockCoordinates a).right := by
  rw [blockCoordinates, dif_pos ha]
  exact Classical.choose_spec (exists_blockCoordinates ha)

theorem blockCoordinates_value {a : ℕ} (ha : HasTwoPrimeFactors a) :
    a = (blockCoordinates a).core * (blockCoordinates a).left *
      (blockCoordinates a).right :=
  (blockCoordinates_spec ha).1

theorem blockCoordinates_injective {a b : ℕ}
    (ha : HasTwoPrimeFactors a) (hb : HasTwoPrimeFactors b)
    (h : blockCoordinates a = blockCoordinates b) : a = b := by
  rw [blockCoordinates_value ha, blockCoordinates_value hb, h]

/-- Elements with at most one prime factor (within a positive squarefree
set these are exactly `1` and the primes). -/
def exceptionalPart (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ a.primeFactors.card < 2

/-- The part represented by a core and two largest primes. -/
def richPart (A : Finset ℕ) : Finset ℕ :=
  A.filter HasTwoPrimeFactors

@[simp] theorem mem_exceptionalPart {A : Finset ℕ} {a : ℕ} :
    a ∈ exceptionalPart A ↔ a ∈ A ∧ a.primeFactors.card < 2 := by
  simp [exceptionalPart]

@[simp] theorem mem_richPart {A : Finset ℕ} {a : ℕ} :
    a ∈ richPart A ↔ a ∈ A ∧ HasTwoPrimeFactors a := by
  simp [richPart]

/-- In a positive squarefree set the exceptional and rich parts partition
the set exactly. -/
theorem card_exceptionalPart_add_card_richPart {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hsf : ∀ a ∈ A, Squarefree a) :
    (exceptionalPart A).card + (richPart A).card = A.card := by
  classical
  let E := exceptionalPart A
  let R := richPart A
  have hdisj : Disjoint E R := by
    rw [Finset.disjoint_left]
    intro a haE haR
    have he := (mem_exceptionalPart.1 (by simpa [E] using haE)).2
    have hr := (mem_richPart.1 (by simpa [R] using haR)).2.2.2
    omega
  have hunion : E ∪ R = A := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.1 ha with haE | haR
      · exact (mem_exceptionalPart.1 (by simpa [E] using haE)).1
      · exact (mem_richPart.1 (by simpa [R] using haR)).1
    · intro ha
      by_cases hc : a.primeFactors.card < 2
      · exact Finset.mem_union_left R
          (by simpa [E] using (mem_exceptionalPart.2 ⟨ha, hc⟩))
      · have hc' : 2 ≤ a.primeFactors.card := by omega
        exact Finset.mem_union_right E (by
          simpa [R] using (mem_richPart.2
            ⟨ha, hpos a ha, hsf a ha, hc'⟩))
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- The two dyadic indices of a represented element. -/
def blockIndex (a : ℕ) : ℕ × ℕ :=
  (dyadicIndex (blockCoordinates a).left,
    dyadicIndex (blockCoordinates a).right)

/-- The nonexceptional elements in one dyadic block. -/
def squarefreeBlock (A : Finset ℕ) (i j : ℕ) : Finset ℕ :=
  (richPart A).filter fun a ↦ blockIndex a = (i, j)

/-- The finite set of cores actually occurring in a block. -/
def squarefreeBlockCoreSet (A : Finset ℕ) (i j : ℕ) : Finset ℕ :=
  (squarefreeBlock A i j).image fun a ↦ (blockCoordinates a).core

@[simp] theorem mem_squarefreeBlock {A : Finset ℕ} {i j a : ℕ} :
    a ∈ squarefreeBlock A i j ↔
      a ∈ A ∧ HasTwoPrimeFactors a ∧ blockIndex a = (i, j) := by
  simp [squarefreeBlock, and_assoc]

theorem blockCoordinates_left_mem {a : ℕ} (ha : HasTwoPrimeFactors a) :
    (blockCoordinates a).left ∈
      dyadicPrimeBlock (dyadicIndex (blockCoordinates a).left) :=
  prime_mem_dyadicPrimeBlock (blockCoordinates_spec ha).2.1

theorem blockCoordinates_right_mem {a : ℕ} (ha : HasTwoPrimeFactors a) :
    (blockCoordinates a).right ∈
      dyadicPrimeBlock (dyadicIndex (blockCoordinates a).right) :=
  prime_mem_dyadicPrimeBlock (blockCoordinates_spec ha).2.2.1

/-- The left block index never exceeds the right block index. -/
theorem blockIndex_fst_le_snd {a : ℕ} (ha : HasTwoPrimeFactors a) :
    (blockIndex a).1 ≤ (blockIndex a).2 := by
  have hp := blockCoordinates_left_mem ha
  have hq := blockCoordinates_right_mem ha
  by_contra h
  have hpow : 2 ^ ((blockIndex a).2 + 1) ≤ 2 ^ (blockIndex a).1 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpq := (blockCoordinates_spec ha).2.2.2.1
  have hp_low := lower_lt_of_mem_dyadicPrimeBlock hp
  have hq_up := le_upper_of_mem_dyadicPrimeBlock hq
  simp only [blockIndex] at hpow hp_low hq_up
  omega

/-- The chosen coordinates really form an arithmetic core edge. -/
theorem blockCoordinates_coreGraph {A : Finset ℕ} {a : ℕ}
    (haA : a ∈ A) (ha : HasTwoPrimeFactors a) :
    CoreGraph A (blockCoordinates a).core (blockCoordinates a).left
      (blockCoordinates a).right := by
  let z := blockCoordinates a
  have hz := blockCoordinates_spec ha
  have hcore_ne : z.core ≠ 0 := by
    intro hc
    change (blockCoordinates a).core = 0 at hc
    have haz : a = 0 := by simpa [hc] using hz.1
    exact (Nat.ne_of_gt ha.1) haz
  have hleft : PrimeAboveCore z.core z.left := by
    refine ⟨hz.2.1, ?_⟩
    intro r hrp hrd
    apply hz.2.2.2.2.2 r
    exact Nat.mem_primeFactors.mpr ⟨hrp, hrd, hcore_ne⟩
  have hright : PrimeAboveCore z.core z.right := by
    refine ⟨hz.2.2.1, ?_⟩
    intro r hrp hrd
    exact (hleft.2 r hrp hrd).trans hz.2.2.2.1
  exact {
    core_pos := Nat.pos_of_ne_zero hcore_ne
    left_above := hleft
    right_above := hright
    endpoint_ne := ne_of_lt hz.2.2.2.1
    mem := by rw [← hz.1]; exact haA }

/-- The graph on two dyadic prime blocks, with the core as colour. -/
noncomputable def blockCoreGraph (A : Finset ℕ) (i j : ℕ) :
    squarefreeBlockCoreSet A i j → dyadicPrimeBlock i → dyadicPrimeBlock j → Prop :=
  fun c p q ↦ CoreGraph A c.1 p.1 q.1

/-- Admissibility prevents a rectangle from appearing in two distinct
core colours. -/
theorem blockCoreGraph_noRepeatedRectangle {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) :
    ColoredGraph.NoRepeatedRectangle (blockCoreGraph A i j) := by
  intro c d hcd p q r s hc hd
  apply hcd
  apply Subtype.ext
  apply coreGraph_no_double_rectangle hA
  · exact {
      left_ne := fun hpq ↦ hc.1 (Subtype.ext hpq)
      right_ne := fun hrs ↦ hc.2.1 (Subtype.ext hrs)
      nw := hc.2.2.1
      ne := hc.2.2.2.2.1
      sw := hc.2.2.2.1
      se := hc.2.2.2.2.2 }
  · exact {
      left_ne := fun hpq ↦ hd.1 (Subtype.ext hpq)
      right_ne := fun hrs ↦ hd.2.1 (Subtype.ext hrs)
      nw := hd.2.2.1
      ne := hd.2.2.2.2.1
      sw := hd.2.2.2.1
      se := hd.2.2.2.2.2 }

/-- Edges of a finite bipartite graph, with the right coordinate placed
first to match the summation order in `ColoredGraph.edgeCount`. -/
def FiniteGraphEdge {L R : Type*} (G : L → R → Prop) :=
  {e : R × L // G e.2 e.1}

noncomputable instance {L R : Type*} [Fintype L] [Fintype R]
    (G : L → R → Prop) : Fintype (FiniteGraphEdge G) := by
  classical
  exact Subtype.fintype _

theorem edgeCount_eq_card_finiteGraphEdge {L R : Type*}
    [Fintype L] [Fintype R] (G : L → R → Prop) :
    ColoredGraph.edgeCount G = (Fintype.card (FiniteGraphEdge G) : ℝ) := by
  classical
  let s : Finset (R × L) :=
    ((Finset.univ : Finset R).product Finset.univ).filter
      (fun e ↦ G e.2 e.1)
  let e : FiniteGraphEdge G ≃ s := {
    toFun := fun z ↦ ⟨z.1, by simp [s, z.2]⟩
    invFun := fun z ↦ ⟨z.1, by simpa [s] using z.2⟩
    left_inv := fun z ↦ by cases z; rfl
    right_inv := fun z ↦ by cases z; rfl }
  have hcard : Fintype.card (FiniteGraphEdge G) = s.card := by
    simpa using Fintype.card_congr e
  rw [hcard]
  calc
    ColoredGraph.edgeCount G =
        ∑ z ∈ (Finset.univ : Finset R).product (Finset.univ : Finset L),
          if G z.2 z.1 then (1 : ℝ) else 0 := by
      simpa [ColoredGraph.edgeCount, ColoredGraph.edgeIndicator] using
        (Finset.sum_product (Finset.univ : Finset R) (Finset.univ : Finset L)
          (fun z : R × L ↦ if G z.2 z.1 then (1 : ℝ) else 0)).symm
    _ = (s.card : ℝ) := by
      simp [s]

/-- The finite type of all edges in the core-coloured graph of a block. -/
def BlockGraphEdge (A : Finset ℕ) (i j : ℕ) :=
  {e : squarefreeBlockCoreSet A i j ×
      (dyadicPrimeBlock i × dyadicPrimeBlock j) //
    blockCoreGraph A i j e.1 e.2.1 e.2.2}

noncomputable instance (A : Finset ℕ) (i j : ℕ) :
    Fintype (BlockGraphEdge A i j) := by
  classical
  exact Subtype.fintype _

/-- Splitting a coloured edge into its colour and its underlying graph
edge. -/
noncomputable def blockGraphEdgeEquivSigma (A : Finset ℕ) (i j : ℕ) :
    BlockGraphEdge A i j ≃
      Σ c : squarefreeBlockCoreSet A i j, FiniteGraphEdge (blockCoreGraph A i j c) where
  toFun e := ⟨e.1.1, ⟨(e.1.2.2, e.1.2.1), e.2⟩⟩
  invFun e := ⟨(e.1, (e.2.1.2, e.2.1.1)), e.2.2⟩
  left_inv e := by cases e with | mk e he => cases e; rfl
  right_inv e := by cases e with | mk c e => cases e with | mk e he => cases e; rfl

/-- A member of a block, sent to its core-coloured graph edge. -/
noncomputable def blockToGraphEdge (A : Finset ℕ) (i j : ℕ)
    (a : squarefreeBlock A i j) : BlockGraphEdge A i j := by
  have ha := (mem_squarefreeBlock.1 a.property).2.1
  have hidx := (mem_squarefreeBlock.1 a.property).2.2
  let z := blockCoordinates a.1
  have hc : z.core ∈ squarefreeBlockCoreSet A i j := by
    refine Finset.mem_image.2 ⟨a.1, a.property, ?_⟩
    rfl
  have hpidx : dyadicIndex z.left = i := by
    simpa [blockIndex, z] using congrArg Prod.fst hidx
  have hqidx : dyadicIndex z.right = j := by
    simpa [blockIndex, z] using congrArg Prod.snd hidx
  have hp : z.left ∈ dyadicPrimeBlock i := by
    rw [← hpidx]
    exact blockCoordinates_left_mem ha
  have hq : z.right ∈ dyadicPrimeBlock j := by
    rw [← hqidx]
    exact blockCoordinates_right_mem ha
  exact ⟨⟨⟨z.core, hc⟩, ⟨⟨z.left, hp⟩, ⟨z.right, hq⟩⟩⟩,
    blockCoordinates_coreGraph (mem_squarefreeBlock.1 a.property).1 ha⟩

/-- The block-to-edge map is injective; uniqueness of the two-largest-prime
decomposition is the key point. -/
theorem blockToGraphEdge_injective (A : Finset ℕ) (i j : ℕ) :
    Function.Injective (blockToGraphEdge A i j) := by
  intro a b hab
  apply Subtype.ext
  have ha := (mem_squarefreeBlock.1 a.property).2.1
  have hb := (mem_squarefreeBlock.1 b.property).2.1
  apply blockCoordinates_injective ha hb
  apply BlockCoordinates.ext
  · exact congrArg (fun e : BlockGraphEdge A i j ↦ e.1.1.1) hab
  · exact congrArg (fun e : BlockGraphEdge A i j ↦ e.1.2.1.1) hab
  · exact congrArg (fun e : BlockGraphEdge A i j ↦ e.1.2.2.1) hab

/-- The cardinality of the edge subtype is the analytic `edgeCount`, summed
over all cores. -/
theorem card_blockGraphEdge_eq_sum_edgeCount (A : Finset ℕ) (i j : ℕ) :
    (Fintype.card (BlockGraphEdge A i j) : ℝ) =
      ∑ c : squarefreeBlockCoreSet A i j,
        ColoredGraph.edgeCount (blockCoreGraph A i j c) := by
  classical
  rw [Fintype.card_congr (blockGraphEdgeEquivSigma A i j),
    Fintype.card_sigma]
  push_cast
  apply Finset.sum_congr rfl
  intro c hc
  rw [edgeCount_eq_card_finiteGraphEdge]

/-- Every represented element supplies a distinct edge.  We deliberately
allow the graph to contain additional arithmetic edges; monotonicity is all
that the upper bound needs. -/
theorem card_squarefreeBlock_le_sum_edgeCount (A : Finset ℕ) (i j : ℕ) :
    ((squarefreeBlock A i j).card : ℝ) ≤
      ∑ c : squarefreeBlockCoreSet A i j,
        ColoredGraph.edgeCount (blockCoreGraph A i j c) := by
  rw [← card_blockGraphEdge_eq_sum_edgeCount]
  have h := Fintype.card_le_of_injective
    (f := blockToGraphEdge A i j) (blockToGraphEdge_injective A i j)
  have h' : (squarefreeBlock A i j).card ≤
      Fintype.card (BlockGraphEdge A i j) := by simpa using h
  exact_mod_cast h'

/-- The radical form of `T^(3/4)`, kept separate from the upper-bound
assembly to avoid real powers in finite estimates. -/
noncomputable def blockThreeQuarterRoot (x : ℝ) : ℝ :=
  Real.sqrt (x * Real.sqrt x)

private theorem coloredKST_block_radical_eq {T M N : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    Real.sqrt (M * N) * Real.sqrt (T * Real.sqrt (T * M ^ 2 * N ^ 2)) =
      blockThreeQuarterRoot T * (M * N) := by
  have hMN : 0 ≤ M * N := mul_nonneg hM hN
  have hinner : Real.sqrt (T * M ^ 2 * N ^ 2) =
      Real.sqrt T * (M * N) := by
    rw [show T * M ^ 2 * N ^ 2 = T * (M * N) ^ 2 by ring]
    rw [Real.sqrt_mul hT, Real.sqrt_sq hMN]
  have hleft : 0 ≤ Real.sqrt (M * N) *
      Real.sqrt (T * Real.sqrt (T * M ^ 2 * N ^ 2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ blockThreeQuarterRoot T * (M * N) :=
    mul_nonneg (Real.sqrt_nonneg _) hMN
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, Real.sq_sqrt hMN]
  rw [Real.sq_sqrt (mul_nonneg hT (Real.sqrt_nonneg _))]
  rw [blockThreeQuarterRoot, mul_pow,
    Real.sq_sqrt (mul_nonneg hT (Real.sqrt_nonneg T)), hinner]
  ring

/-- The explicit three terms furnished by coloured KST for one block. -/
noncomputable def squarefreeBlockBound (A : Finset ℕ) (i j : ℕ) : ℝ :=
  let T := (squarefreeBlockCoreSet A i j).card
  let M := (dyadicPrimeBlock i).card
  let N := (dyadicPrimeBlock j).card
  2 * (T : ℝ) * N +
    2 * (T : ℝ) * M * Real.sqrt (N : ℝ) +
    2 * blockThreeQuarterRoot (T : ℝ) * M * N

/-- Coloured KST, specialized to a single arithmetic block and written as
`T N + T M sqrt N + T^(3/4) M N` with explicit constant two. -/
theorem sum_blockCoreGraph_edgeCount_le {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) :
    (∑ c : squarefreeBlockCoreSet A i j,
        ColoredGraph.edgeCount (blockCoreGraph A i j c)) ≤
      squarefreeBlockBound A i j := by
  calc
    (∑ c : squarefreeBlockCoreSet A i j,
        ColoredGraph.edgeCount (blockCoreGraph A i j c)) ≤
        2 * ((squarefreeBlockCoreSet A i j).card : ℝ) * (dyadicPrimeBlock j).card +
          2 * ((squarefreeBlockCoreSet A i j).card : ℝ) *
            (dyadicPrimeBlock i).card *
              Real.sqrt ((dyadicPrimeBlock j).card : ℝ) +
          2 * Real.sqrt (((dyadicPrimeBlock i).card : ℝ) *
              (dyadicPrimeBlock j).card) *
            Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
              Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
                ((dyadicPrimeBlock i).card : ℝ) ^ 2 *
                ((dyadicPrimeBlock j).card : ℝ) ^ 2)) :=
      by simpa only [Fintype.card_coe] using
        (ColoredGraph.sum_edgeCount_le (blockCoreGraph A i j)
          (blockCoreGraph_noRepeatedRectangle hA))
    _ = squarefreeBlockBound A i j := by
      have hrad := coloredKST_block_radical_eq
        (Nat.cast_nonneg (squarefreeBlockCoreSet A i j).card)
        (Nat.cast_nonneg (dyadicPrimeBlock i).card)
        (Nat.cast_nonneg (dyadicPrimeBlock j).card)
      rw [show 2 * Real.sqrt (((dyadicPrimeBlock i).card : ℝ) *
              (dyadicPrimeBlock j).card) *
            Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
              Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
                ((dyadicPrimeBlock i).card : ℝ) ^ 2 *
                ((dyadicPrimeBlock j).card : ℝ) ^ 2)) =
          2 * (Real.sqrt (((dyadicPrimeBlock i).card : ℝ) *
              (dyadicPrimeBlock j).card) *
            Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
              Real.sqrt (((squarefreeBlockCoreSet A i j).card : ℝ) *
                ((dyadicPrimeBlock i).card : ℝ) ^ 2 *
                ((dyadicPrimeBlock j).card : ℝ) ^ 2))) by ring,
        hrad]
      simp only [squarefreeBlockBound]
      ring

/-- The resulting blockwise cardinality estimate. -/
theorem card_squarefreeBlock_le_bound {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) :
    ((squarefreeBlock A i j).card : ℝ) ≤ squarefreeBlockBound A i j :=
  (card_squarefreeBlock_le_sum_edgeCount A i j).trans
    (sum_blockCoreGraph_edgeCount_le hA)

/-- The finite set of dyadic index pairs actually occupied by represented
elements. -/
def occupiedBlockIndices (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (richPart A).image blockIndex

@[simp] theorem mem_occupiedBlockIndices {A : Finset ℕ} {ij : ℕ × ℕ} :
    ij ∈ occupiedBlockIndices A ↔ ∃ a ∈ richPart A, blockIndex a = ij := by
  simp [occupiedBlockIndices]

/-- Exact partition of the rich part into its occupied dyadic blocks. -/
theorem sum_card_squarefreeBlock (A : Finset ℕ) :
    ∑ ij ∈ occupiedBlockIndices A,
      (squarefreeBlock A ij.1 ij.2).card = (richPart A).card := by
  classical
  have hmap : ∀ a ∈ richPart A, blockIndex a ∈ occupiedBlockIndices A := by
    intro a ha
    exact Finset.mem_image.2 ⟨a, ha, rfl⟩
  simpa [squarefreeBlock] using
    (Finset.sum_fiberwise_of_maps_to hmap (fun _a ↦ (1 : ℕ)))

/-- Every occupied block has ordered indices. -/
theorem occupiedBlockIndices_fst_le_snd {A : Finset ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ occupiedBlockIndices A) : ij.1 ≤ ij.2 := by
  obtain ⟨a, ha, rfl⟩ := mem_occupiedBlockIndices.1 hij
  exact blockIndex_fst_le_snd (mem_richPart.1 ha).2

theorem mem_squarefreeBlockCoreSet {A : Finset ℕ} {i j c : ℕ} :
    c ∈ squarefreeBlockCoreSet A i j ↔
      ∃ a ∈ squarefreeBlock A i j, (blockCoordinates a).core = c := by
  simp [squarefreeBlockCoreSet]

/-- Arithmetic data carried by every core which occurs in a block. -/
theorem squarefreeBlockCoreSet_spec {A : Finset ℕ} {n i j c : ℕ}
    (hA : RequiredCondition A n) (hc : c ∈ squarefreeBlockCoreSet A i j) :
    0 < c ∧ Squarefree c ∧ c * 2 ^ i * 2 ^ j ≤ n ∧
      ∀ r ∈ c.primeFactors, r < 2 ^ (i + 1) := by
  obtain ⟨a, haBlock, hca⟩ := mem_squarefreeBlockCoreSet.1 hc
  have haData := (mem_squarefreeBlock.1 haBlock).2.1
  have hidx := (mem_squarefreeBlock.1 haBlock).2.2
  have hz := blockCoordinates_spec haData
  have hgraph := blockCoordinates_coreGraph
    (mem_squarefreeBlock.1 haBlock).1 haData
  have hpidx : dyadicIndex (blockCoordinates a).left = i := by
    simpa [blockIndex] using congrArg Prod.fst hidx
  have hqidx : dyadicIndex (blockCoordinates a).right = j := by
    simpa [blockIndex] using congrArg Prod.snd hidx
  have hp := blockCoordinates_left_mem haData
  have hq := blockCoordinates_right_mem haData
  rw [hpidx] at hp
  rw [hqidx] at hq
  have ha_le : a ≤ n := (Finset.mem_Ioc.1
    (hA.1 (mem_squarefreeBlock.1 haBlock).1)).2
  subst c
  refine ⟨hgraph.core_pos, hz.2.2.2.2.1, ?_, ?_⟩
  · calc
      (blockCoordinates a).core * 2 ^ i * 2 ^ j ≤
          (blockCoordinates a).core * (blockCoordinates a).left *
            (blockCoordinates a).right := by
        gcongr
        · exact (lower_lt_of_mem_dyadicPrimeBlock hp).le
        · exact (lower_lt_of_mem_dyadicPrimeBlock hq).le
      _ = a := hz.1.symm
      _ ≤ n := ha_le
  · intro r hr
    exact (hz.2.2.2.2.2 r hr).trans_le
      (le_upper_of_mem_dyadicPrimeBlock hp)

/-- The coarse product constraint gives the uniform core-count bound
`T ≤ n/(2^i 2^j)`. -/
theorem squarefreeBlockCoreSet_card_le_div {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) :
    (squarefreeBlockCoreSet A i j).card ≤ n / (2 ^ i * 2 ^ j) := by
  have hsub : squarefreeBlockCoreSet A i j ⊆
      Finset.Ioc 0 (n / (2 ^ i * 2 ^ j)) := by
    intro c hc
    have hs := squarefreeBlockCoreSet_spec hA hc
    rw [Finset.mem_Ioc]
    refine ⟨hs.1, (Nat.le_div_iff_mul_le (by positivity)).2 ?_⟩
    simpa [mul_assoc] using hs.2.2.1
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- For ordered blocks every occurring core belongs to the smooth-core set
at scale `X=2^i`. -/
theorem squarefreeBlockCoreSet_subset_smoothCoreSet {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) (hij : i ≤ j) :
    squarefreeBlockCoreSet A i j ⊆ smoothCoreSet n (2 ^ i) := by
  intro c hc
  have hs := squarefreeBlockCoreSet_spec hA hc
  rw [mem_smoothCoreSet]
  refine ⟨hs.1, ?_, hs.2.1, ?_, ?_⟩
  · have hpowpos : 0 < 2 ^ i * 2 ^ j := by positivity
    calc
      c ≤ c * (2 ^ i * 2 ^ j) := by
        nth_rewrite 1 [← mul_one c]
        exact Nat.mul_le_mul_left c (by omega)
      _ ≤ n := by simpa [mul_assoc] using hs.2.2.1
  · have hpow : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    calc
      c * (2 ^ i) ^ 2 = c * 2 ^ i * 2 ^ i := by ring
      _ ≤ c * 2 ^ i * 2 ^ j := Nat.mul_le_mul_left (c * 2 ^ i) hpow
      _ ≤ n := hs.2.2.1
  · intro r hr
    simpa [pow_succ, Nat.mul_comm] using hs.2.2.2 r hr

/-- The smooth-core cardinal bound `T≤T₀(X)`. -/
theorem squarefreeBlockCoreSet_card_le_T0 {A : Finset ℕ} {n i j : ℕ}
    (hA : RequiredCondition A n) (hij : i ≤ j) :
    (squarefreeBlockCoreSet A i j).card ≤ T0 n (2 ^ i) := by
  exact Finset.card_le_card (squarefreeBlockCoreSet_subset_smoothCoreSet hA hij)

/-- On an equal-scale block a maximum cut captures at least half the
represented edge objects.  This is the precise constant-two loss used when
one insists that the two copies of the prime block come from disjoint vertex
classes.  The main cardinal cover below may instead use two labelled copies
of the same block, which is a stronger counting device. -/
theorem exists_sameScale_bipartition (A : Finset ℕ) (i : ℕ) :
    ∃ χ : dyadicPrimeBlock i → Bool,
      (squarefreeBlock A i i).card ≤
        2 * (crossingItems
          (Finset.univ : Finset (squarefreeBlock A i i))
          (fun a ↦ (blockToGraphEdge A i i a).1.2.1)
          (fun a ↦ (blockToGraphEdge A i i a).1.2.2) χ).card := by
  have hloop : ∀ a ∈ (Finset.univ : Finset (squarefreeBlock A i i)),
      (blockToGraphEdge A i i a).1.2.1 ≠
        (blockToGraphEdge A i i a).1.2.2 := by
    intro a ha heq
    exact (blockToGraphEdge A i i a).2.endpoint_ne
      (congrArg Subtype.val heq)
  simpa using exists_bipartition_half_crossing
    (Finset.univ : Finset (squarefreeBlock A i i))
    (fun a ↦ (blockToGraphEdge A i i a).1.2.1)
    (fun a ↦ (blockToGraphEdge A i i a).1.2.2) hloop

/-- The unconditional finite squarefree cover over the actually occupied
dyadic blocks.  Its summand is exactly the three-term coloured-KST bound. -/
theorem card_le_exceptional_add_sum_squarefreeBlockBound
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (A.card : ℝ) ≤ (exceptionalPart A).card +
      ∑ ij ∈ occupiedBlockIndices A,
        squarefreeBlockBound A ij.1 ij.2 := by
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha
    exact (Finset.mem_Ioc.1 (hA.1 ha)).1
  have hpart := card_exceptionalPart_add_card_richPart hpos hsf
  have hfiber := sum_card_squarefreeBlock A
  calc
    (A.card : ℝ) =
        (exceptionalPart A).card + (richPart A).card := by
      exact_mod_cast hpart.symm
    _ = (exceptionalPart A).card +
        ∑ ij ∈ occupiedBlockIndices A,
          ((squarefreeBlock A ij.1 ij.2).card : ℝ) := by
      rw [← Nat.cast_sum, hfiber]
    _ ≤ (exceptionalPart A).card +
        ∑ ij ∈ occupiedBlockIndices A,
          squarefreeBlockBound A ij.1 ij.2 := by
      gcongr with ij hij
      exact card_squarefreeBlock_le_bound hA

/-- A positive squarefree integer with fewer than two prime factors is
either `1` or prime. -/
theorem eq_one_or_prime_of_squarefree_card_primeFactors_lt_two {a : ℕ}
    (hsf : Squarefree a) (hcard : a.primeFactors.card < 2) :
    a = 1 ∨ a.Prime := by
  have hc : a.primeFactors.card = 0 ∨ a.primeFactors.card = 1 := by omega
  rcases hc with hc | hc
  · left
    have hempty : a.primeFactors = ∅ := Finset.card_eq_zero.mp hc
    have hp := Nat.prod_primeFactors_of_squarefree hsf
    simpa [hempty] using hp.symm
  · right
    exact Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsf, isPrimePow_iff_card_primeFactors_eq_one.mpr hc⟩

/-- The exceptional set consists of `1` and primes, and hence costs at most
`1+π(n)`. -/
theorem exceptionalPart_card_le_one_add_primeCounting
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (exceptionalPart A).card ≤ 1 + Nat.primeCounting n := by
  have hsub : exceptionalPart A ⊆ insert 1 n.primesLE := by
    intro a ha
    have hm := mem_exceptionalPart.1 ha
    have hIoc := Finset.mem_Ioc.1 (hA.1 hm.1)
    rcases eq_one_or_prime_of_squarefree_card_primeFactors_lt_two
        (hsf a hm.1) hm.2 with rfl | hp
    · simp
    · simp [Nat.mem_primesLE, hp, hIoc.2]
  calc
    (exceptionalPart A).card ≤ (insert 1 n.primesLE).card :=
      Finset.card_le_card hsub
    _ ≤ 1 + n.primesLE.card := by
      simpa [Nat.add_comm] using Finset.card_insert_le 1 n.primesLE
    _ = 1 + Nat.primeCounting n := by rw [Nat.primesLE_card_eq_primeCounting]

/-- The KST summand is nonnegative. -/
theorem squarefreeBlockBound_nonneg (A : Finset ℕ) (i j : ℕ) :
    0 ≤ squarefreeBlockBound A i j := by
  dsimp [squarefreeBlockBound]
  have hroot : 0 ≤ blockThreeQuarterRoot
      ((squarefreeBlockCoreSet A i j).card : ℝ) := by
    exact Real.sqrt_nonneg _
  positivity

/-- The right endpoint of every occupied block is at most `n`, hence its
dyadic index is at most `log₂ n`. -/
theorem occupiedBlockIndices_snd_le_log {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) {ij : ℕ × ℕ}
    (hij : ij ∈ occupiedBlockIndices A) : ij.2 ≤ Nat.log 2 n := by
  obtain ⟨a, haRich, hindex⟩ := mem_occupiedBlockIndices.1 hij
  have haA := (mem_richPart.1 haRich).1
  have haData := (mem_richPart.1 haRich).2
  let q := (blockCoordinates a).right
  have hqmem := blockCoordinates_right_mem haData
  have hqidx : dyadicIndex q = ij.2 := by
    simpa [blockIndex, q] using congrArg Prod.snd hindex
  rw [hqidx] at hqmem
  have hq_dvd : q ∣ a := by
    refine ⟨(blockCoordinates a).core * (blockCoordinates a).left, ?_⟩
    calc
      a = (blockCoordinates a).core * (blockCoordinates a).left * q :=
        blockCoordinates_value haData
      _ = q * ((blockCoordinates a).core * (blockCoordinates a).left) := by
        ring
  have hq_le_a : q ≤ a := Nat.le_of_dvd haData.1 hq_dvd
  have ha_le_n : a ≤ n := (Finset.mem_Ioc.1 (hA.1 haA)).2
  have hn : n ≠ 0 := by
    have hqpos := (prime_of_mem_dyadicPrimeBlock hqmem).pos
    omega
  apply (Nat.le_log_iff_pow_le (by norm_num) hn).2
  exact (lower_lt_of_mem_dyadicPrimeBlock hqmem).le.trans
    (hq_le_a.trans ha_le_n)

/-- Both indices of an occupied pair lie in the explicit logarithmic range. -/
theorem occupiedBlockIndices_lt_log_add_one {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) {ij : ℕ × ℕ}
    (hij : ij ∈ occupiedBlockIndices A) :
    ij.1 < Nat.log 2 n + 1 ∧ ij.2 < Nat.log 2 n + 1 := by
  have hord := occupiedBlockIndices_fst_le_snd hij
  have hj := occupiedBlockIndices_snd_le_log hA hij
  omega

/-- The product of the lower dyadic endpoints is strictly smaller than the
ambient parameter on every occupied block. -/
theorem occupiedBlockIndices_pow_add_lt {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) {ij : ℕ × ℕ}
    (hij : ij ∈ occupiedBlockIndices A) :
    2 ^ (ij.1 + ij.2) < n := by
  obtain ⟨a, haRich, hindex⟩ := mem_occupiedBlockIndices.1 hij
  have haA := (mem_richPart.1 haRich).1
  have haData := (mem_richPart.1 haRich).2
  let z := blockCoordinates a
  have hp := blockCoordinates_left_mem haData
  have hq := blockCoordinates_right_mem haData
  have hpidx : dyadicIndex z.left = ij.1 := by
    simpa [blockIndex, z] using congrArg Prod.fst hindex
  have hqidx : dyadicIndex z.right = ij.2 := by
    simpa [blockIndex, z] using congrArg Prod.snd hindex
  rw [hpidx] at hp
  rw [hqidx] at hq
  have hz := blockCoordinates_spec haData
  have hcpos := (blockCoordinates_coreGraph haA haData).core_pos
  have hpq_lt : 2 ^ ij.1 * 2 ^ ij.2 < z.left * z.right := by
    calc
      2 ^ ij.1 * 2 ^ ij.2 < z.left * 2 ^ ij.2 :=
        (Nat.mul_lt_mul_right (show 0 < 2 ^ ij.2 by positivity)).2
          (lower_lt_of_mem_dyadicPrimeBlock hp)
      _ < z.left * z.right :=
        (Nat.mul_lt_mul_left (prime_of_mem_dyadicPrimeBlock hp).pos).2
          (lower_lt_of_mem_dyadicPrimeBlock hq)
  have hpq_le_a : z.left * z.right ≤ a := by
    calc
      z.left * z.right = 1 * (z.left * z.right) := by simp
      _ ≤ z.core * (z.left * z.right) :=
        Nat.mul_le_mul_right _ hcpos
      _ = a := by rw [hz.1]; ring
  have ha_le_n : a ≤ n := (Finset.mem_Ioc.1 (hA.1 haA)).2
  rw [pow_add]
  exact hpq_lt.trans_le (hpq_le_a.trans ha_le_n)

/-- The explicit triangular range of dyadic exponent pairs. -/
def dyadicIndexPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Nat.log 2 n + 1)).product
    (Finset.range (Nat.log 2 n + 1))).filter fun ij ↦ ij.1 ≤ ij.2

@[simp] theorem mem_dyadicIndexPairs {n i j : ℕ} :
    (i, j) ∈ dyadicIndexPairs n ↔ i ≤ j ∧ j ≤ Nat.log 2 n := by
  simp [dyadicIndexPairs]
  omega

/-- Occupied blocks embed in the explicit triangular logarithmic range. -/
theorem occupiedBlockIndices_subset_dyadicIndexPairs
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    occupiedBlockIndices A ⊆ dyadicIndexPairs n := by
  intro ij hij
  rcases ij with ⟨i, j⟩
  rw [mem_dyadicIndexPairs]
  exact ⟨occupiedBlockIndices_fst_le_snd hij,
    occupiedBlockIndices_snd_le_log hA hij⟩

/-- Nonnegative block summands may be extended from the occupied pairs to
the whole explicit triangular range. -/
theorem sum_occupiedBlockIndices_le_sum_dyadicIndexPairs
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    (∑ ij ∈ occupiedBlockIndices A,
        squarefreeBlockBound A ij.1 ij.2) ≤
      ∑ ij ∈ dyadicIndexPairs n,
        squarefreeBlockBound A ij.1 ij.2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (occupiedBlockIndices_subset_dyadicIndexPairs hA)
  intro ij hijRange hijOccupied
  exact squarefreeBlockBound_nonneg A ij.1 ij.2

/-- Final finite squarefree block cover in an `A`-independent exponent
range.  The only remaining set dependence is the actual core cardinality
inside each of the three KST terms. -/
theorem card_le_one_add_primeCounting_add_sum_dyadicIndexPairs
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (A.card : ℝ) ≤ 1 + Nat.primeCounting n +
      ∑ ij ∈ dyadicIndexPairs n,
        squarefreeBlockBound A ij.1 ij.2 := by
  have hcover := card_le_exceptional_add_sum_squarefreeBlockBound hA hsf
  have hexc := exceptionalPart_card_le_one_add_primeCounting hA hsf
  have hsum := sum_occupiedBlockIndices_le_sum_dyadicIndexPairs hA
  exact hcover.trans (by
    exact add_le_add (by exact_mod_cast hexc) hsum)

end

end Erdos888
