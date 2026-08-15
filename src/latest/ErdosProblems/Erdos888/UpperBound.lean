import ErdosProblems.Erdos888.BlockEncoding
import ErdosProblems.Erdos888.BlockMajorant
import ErdosProblems.Erdos888.ColoredGraph
import ErdosProblems.Erdos888.Asymptotic
import ErdosProblems.Erdos888.CoreBridge
import ErdosProblems.Erdos888.PrimeEstimates
import ErdosProblems.Erdos888.RectangleBridge
import ErdosProblems.Erdos888.SmoothMajorant
import ErdosProblems.Erdos888.SquarefreeBlocks
import ErdosProblems.Erdos888.SquarefreeReduction

/-!
# Erdős Problem 888: upper-bound assembly

This file is the interface between the block estimates and the extremal
functions.  The four terms in `SquarefreeBlockEstimate` correspond to the
exceptional (one or fewer prime factors), rectangle (`S₁`), core (`S₂`),
and smooth-core (`S₃`) contributions in the mathematical proof.

There are no number-theoretic assumptions hidden in this interface: a block
estimate has to bound every squarefree admissible set, and each of its four
explicit terms has to satisfy the asserted asymptotic estimate.  The theorem
below merely performs the finite-maximum and Big-O assembly.  The separate
square-part reduction then turns the squarefree estimate into the unrestricted
one.
-/

open Filter Asymptotics

namespace Erdos888

open scoped BigOperators

/-! ## The arithmetic core graphs satisfy the generic coloured-KST API -/

/-- The finite family of core-coloured graphs on specified endpoint sets. -/
noncomputable def finiteCoreGraph (A C L R : Finset ℕ) :
    C → L → R → Prop := fun c u v ↦ CoreGraph A c.1 u.1 v.1

/-- Forget the endpoint-membership proofs on a pair of finite-subtype
vertices. -/
def subtypePairEmbedding (L R : Finset ℕ) : L × R ↪ ℕ × ℕ where
  toFun z := (z.1.1, z.2.1)
  inj' := by
    intro z w h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg Prod.snd h

/-- The generic graph edge finset is exactly the arithmetic `coreEdges`
finset after forgetting endpoint-membership proofs. -/
theorem map_edgeFinset_finiteCoreGraph (A C L R : Finset ℕ) (c : C) :
    (ColoredGraph.edgeFinset (finiteCoreGraph A C L R c)).map
        (subtypePairEmbedding L R) = coreEdges A c.1 L R := by
  classical
  ext e
  rcases e with ⟨u, v⟩
  simp only [Finset.mem_map, mem_coreEdges]
  constructor
  · rintro ⟨⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩, hG, heq⟩
    change (u', v') = (u, v) at heq
    injection heq with huu hvv
    subst u'
    subst v'
    refine ⟨hu', hv', ?_⟩
    simpa [finiteCoreGraph] using
      ((ColoredGraph.mem_edgeFinset (finiteCoreGraph A C L R c)
        (⟨u, hu'⟩ : L) (⟨v, hv'⟩ : R)).mp hG)
  · rintro ⟨hu, hv, hG⟩
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_, ?_⟩
    · exact (ColoredGraph.mem_edgeFinset (finiteCoreGraph A C L R c)
        (⟨u, hu⟩ : L) (⟨v, hv⟩ : R)).mpr (by
          simpa [finiteCoreGraph] using hG)
    · rfl

/-- Consequently the real generic edge count equals the ordinary cardinality
of the arithmetic edge finset. -/
theorem edgeCount_finiteCoreGraph (A C L R : Finset ℕ) (c : C) :
    ColoredGraph.edgeCount (finiteCoreGraph A C L R c) =
      (coreEdges A c.1 L R).card := by
  rw [ColoredGraph.edgeCount_eq_card_edgeFinset]
  norm_cast
  rw [← map_edgeFinset_finiteCoreGraph A C L R c, Finset.card_map]

/-- Cores which actually support an edge in a fixed dyadic block.  Using
active cores (rather than all `c ≤ n`) is essential: its cardinality is the
colour parameter `T(X,Y)` in the analytic estimates. -/
noncomputable def fullBlockCoreSet (A : Finset ℕ) (n i j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun c ↦
    (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).Nonempty

@[simp] theorem mem_fullBlockCoreSet {A : Finset ℕ} {n i j c : ℕ} :
    c ∈ fullBlockCoreSet A n i j ↔ 1 ≤ c ∧ c ≤ n ∧
      (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).Nonempty := by
  simp [fullBlockCoreSet, and_assoc]

/-- Every active colour satisfies the squarefree, size, and smoothness
conditions of the analytic core majorant. -/
theorem fullBlockCoreSet_subset_blockCoreCandidates
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) (hij : i ≤ j) :
    fullBlockCoreSet A n i j ⊆ blockCoreCandidates n i j := by
  intro c hc
  obtain ⟨hc1, hcn, hedge⟩ := mem_fullBlockCoreSet.mp hc
  obtain ⟨⟨u, v⟩, huv⟩ := hedge
  have he := mem_coreEdges.mp huv
  have hcuvioc := Finset.mem_Ioc.mp (hA.1 he.2.2.mem)
  have hcsf : Squarefree c := (hsf _ he.2.2.mem).squarefree_of_dvd
    ⟨u * v, by ring⟩
  have hi := lower_lt_of_mem_dyadicPrimeBlock he.1
  have hj := lower_lt_of_mem_dyadicPrimeBlock he.2.1
  have hcXi : c * 2 ^ i < c * u :=
    Nat.mul_lt_mul_of_pos_left hi he.2.2.core_pos
  have hcXiY : (c * 2 ^ i) * 2 ^ j < (c * u) * 2 ^ j :=
    Nat.mul_lt_mul_of_pos_right hcXi (pow_pos (by omega) _)
  have hcuY : (c * u) * 2 ^ j < (c * u) * v :=
    Nat.mul_lt_mul_of_pos_left hj
      (mul_pos he.2.2.core_pos he.2.2.left_prime.pos)
  have hprod : c * 2 ^ i * 2 ^ j ≤ n :=
    (hcXiY.trans hcuY).le.trans hcuvioc.2
  apply mem_blockCoreCandidates.mpr
  refine ⟨hc1, hcn, hij, hcsf, hprod, ?_⟩
  intro r hr
  have hrdata := Nat.mem_primeFactors.mp hr
  exact (he.2.2.left_above.2 r hrdata.1 hrdata.2.1).trans_le
    (le_upper_of_mem_dyadicPrimeBlock he.1)

/-- Removing inactive colours does not change the sum of edge cardinalities. -/
theorem sum_fullBlockCoreSet_card_coreEdges (A : Finset ℕ) (n i j : ℕ) :
    (∑ c : fullBlockCoreSet A n i j,
        (coreEdges A c.1 (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card) =
      ∑ c ∈ Finset.Icc 1 n,
        (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card := by
  classical
  calc
    (∑ c : fullBlockCoreSet A n i j,
        (coreEdges A c.1 (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card) =
        ∑ c ∈ fullBlockCoreSet A n i j,
          (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card :=
      Finset.sum_coe_sort (fullBlockCoreSet A n i j)
        (fun c ↦ (coreEdges A c (dyadicPrimeBlock i)
          (dyadicPrimeBlock j)).card)
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c hc hnot
      have hempty : coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        apply hnot
        simp [hc, hne]
      simp [hempty]

/-- The exact canonical block cover, regrouped first by the two dyadic scales
and then by the active core colours of that block. -/
theorem card_nonexceptional_le_sum_fullBlockCoreSet
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) :
    (nonexceptionalElements A).card ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ c : fullBlockCoreSet A n i j,
          (coreEdges A c.1 (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card := by
  have h := card_nonexceptional_le_sum_coreEdges hA hsf
  rw [finiteDyadicCoreKeys] at h
  change (nonexceptionalElements A).card ≤
    ∑ k ∈ (Finset.range (n + 1) ×ˢ
      (Finset.range (n + 1) ×ˢ Finset.Icc 1 n)),
      (coreEdges A k.2.2 (dyadicPrimeBlock k.1)
        (dyadicPrimeBlock k.2.1)).card at h
  rw [Finset.sum_product] at h
  simp_rw [Finset.sum_product] at h
  calc
    (nonexceptionalElements A).card ≤
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ c ∈ Finset.Icc 1 n,
            (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (sum_fullBlockCoreSet_card_coreEdges A n i j).symm

/-- Real-valued form of the block cover, with every finite edge cardinality
identified with the generic graph-library edge count. -/
theorem card_nonexceptional_cast_le_sum_edgeCount
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) :
    ((nonexceptionalElements A).card : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ c : fullBlockCoreSet A n i j,
          ColoredGraph.edgeCount
            (finiteCoreGraph A (fullBlockCoreSet A n i j)
              (dyadicPrimeBlock i) (dyadicPrimeBlock j) c) := by
  have h := card_nonexceptional_le_sum_fullBlockCoreSet hA hsf
  simp_rw [edgeCount_finiteCoreGraph]
  exact_mod_cast h

/-- Admissibility supplies exactly the no-repeated-rectangle hypothesis used
by the generic coloured graph estimate. -/
theorem finiteCoreGraph_noRepeatedRectangle {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (C L R : Finset ℕ) :
    ColoredGraph.NoRepeatedRectangle (finiteCoreGraph A C L R) := by
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

/-- Algebraic normalization of the nested square roots in the coloured KST
theorem. -/
theorem coloredKST_radical_eq {T M N : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    Real.sqrt (M * N) * Real.sqrt (T * Real.sqrt (T * M ^ 2 * N ^ 2)) =
      threeQuarterRoot T * (M * N) := by
  have hMN : 0 ≤ M * N := mul_nonneg hM hN
  have hinner : Real.sqrt (T * M ^ 2 * N ^ 2) =
      Real.sqrt T * (M * N) := by
    rw [show T * M ^ 2 * N ^ 2 = T * (M * N) ^ 2 by ring]
    rw [Real.sqrt_mul hT, Real.sqrt_sq hMN]
  have hleft : 0 ≤ Real.sqrt (M * N) *
      Real.sqrt (T * Real.sqrt (T * M ^ 2 * N ^ 2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ threeQuarterRoot T * (M * N) :=
    mul_nonneg (Real.sqrt_nonneg _) hMN
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, Real.sq_sqrt hMN]
  rw [Real.sq_sqrt (mul_nonneg hT (Real.sqrt_nonneg _))]
  rw [threeQuarterRoot, mul_pow,
    Real.sq_sqrt (mul_nonneg hT (Real.sqrt_nonneg T)), hinner]
  ring

/-- The generic coloured KST theorem, specialized to the arithmetic core
graphs and normalized to the `T^(3/4) M N` form used by the block sums. -/
theorem sum_finiteCoreGraph_edgeCount_le {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (C L R : Finset ℕ) :
    (∑ c : C, ColoredGraph.edgeCount (finiteCoreGraph A C L R c)) ≤
      2 * (C.card : ℝ) * R.card +
      2 * (C.card : ℝ) * L.card * Real.sqrt (R.card : ℝ) +
      2 * threeQuarterRoot (C.card : ℝ) * L.card * R.card := by
  calc
    (∑ c : C, ColoredGraph.edgeCount (finiteCoreGraph A C L R c)) ≤
        2 * (C.card : ℝ) * R.card +
        2 * (C.card : ℝ) * L.card * Real.sqrt (R.card : ℝ) +
        2 * Real.sqrt ((L.card : ℝ) * R.card) *
          Real.sqrt ((C.card : ℝ) *
            Real.sqrt ((C.card : ℝ) * (L.card : ℝ) ^ 2 *
              (R.card : ℝ) ^ 2)) :=
      by
        simpa only [Fintype.card_coe] using
          ColoredGraph.sum_edgeCount_le (finiteCoreGraph A C L R)
            (finiteCoreGraph_noRepeatedRectangle hA C L R)
    _ = _ := by
      have hrad := coloredKST_radical_eq (Nat.cast_nonneg C.card)
        (Nat.cast_nonneg L.card) (Nat.cast_nonneg R.card)
      calc
        2 * (C.card : ℝ) * R.card +
            2 * (C.card : ℝ) * L.card * Real.sqrt (R.card : ℝ) +
            2 * Real.sqrt ((L.card : ℝ) * R.card) *
              Real.sqrt ((C.card : ℝ) *
                Real.sqrt ((C.card : ℝ) * (L.card : ℝ) ^ 2 *
                  (R.card : ℝ) ^ 2)) =
            2 * (C.card : ℝ) * R.card +
            2 * (C.card : ℝ) * L.card * Real.sqrt (R.card : ℝ) +
            2 * (Real.sqrt ((L.card : ℝ) * R.card) *
              Real.sqrt ((C.card : ℝ) *
                Real.sqrt ((C.card : ℝ) * (L.card : ℝ) ^ 2 *
                  (R.card : ℝ) ^ 2))) := by ring
        _ = 2 * (C.card : ℝ) * R.card +
            2 * (C.card : ℝ) * L.card * Real.sqrt (R.card : ℝ) +
            2 * (threeQuarterRoot (C.card : ℝ) *
              ((L.card : ℝ) * R.card)) := by rw [hrad]
        _ = _ := by ring

/-- The explicit output of coloured KST for one dyadic block. -/
noncomputable def blockKSTBound (A : Finset ℕ) (n i j : ℕ) : ℝ :=
  let T := ((fullBlockCoreSet A n i j).card : ℝ)
  let M := ((dyadicPrimeBlock i).card : ℝ)
  let N := ((dyadicPrimeBlock j).card : ℝ)
  2 * T * N + 2 * T * M * Real.sqrt N + 2 * threeQuarterRoot T * M * N

theorem blockKSTBound_le_universalBlockKSTBound
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) (hij : i ≤ j) :
    blockKSTBound A n i j ≤ universalBlockKSTBound n i j := by
  have hcard := Finset.card_le_card
    (fullBlockCoreSet_subset_blockCoreCandidates (i := i) (j := j) hA hsf hij)
  have hT : ((fullBlockCoreSet A n i j).card : ℝ) ≤
      (blockCoreCandidates n i j).card := by
    exact_mod_cast hcard
  unfold blockKSTBound universalBlockKSTBound
  dsimp
  have htq := threeQuarterRoot_mono (Nat.cast_nonneg _) hT
  gcongr

/-- Canonical cores occurring in an occupied block lie in the corresponding
set-independent arithmetic candidate set. -/
theorem squarefreeBlockCoreSet_subset_blockCoreCandidates
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hij : i ≤ j) :
    squarefreeBlockCoreSet A i j ⊆ blockCoreCandidates n i j := by
  intro c hc
  have hs := squarefreeBlockCoreSet_spec hA hc
  have hcn : c ≤ n := by
    calc
      c = c * 1 * 1 := by simp
      _ ≤ c * 2 ^ i * 2 ^ j :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c Nat.one_le_two_pow)
          Nat.one_le_two_pow
      _ ≤ n := hs.2.2.1
  exact mem_blockCoreCandidates.mpr
    ⟨hs.1, hcn, hij, hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- The actual KST bound of a canonical occupied block is bounded by the
set-independent candidate-core expression. -/
theorem squarefreeBlockBound_le_universalBlockKSTBound
    {A : Finset ℕ} {n i j : ℕ} (hA : RequiredCondition A n)
    (hij : i ≤ j) :
    squarefreeBlockBound A i j ≤ universalBlockKSTBound n i j := by
  have hcard := Finset.card_le_card
    (squarefreeBlockCoreSet_subset_blockCoreCandidates hA hij)
  have hT : ((squarefreeBlockCoreSet A i j).card : ℝ) ≤
      (blockCoreCandidates n i j).card := by exact_mod_cast hcard
  have htq := threeQuarterRoot_mono (Nat.cast_nonneg _) hT
  unfold squarefreeBlockBound universalBlockKSTBound
  dsimp
  simpa [blockThreeQuarterRoot, threeQuarterRoot] using (show
    2 * ((squarefreeBlockCoreSet A i j).card : ℝ) *
          ((dyadicPrimeBlock j).card : ℝ) +
        2 * ((squarefreeBlockCoreSet A i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ) +
        2 * threeQuarterRoot
          ((squarefreeBlockCoreSet A i j).card : ℝ) *
            ((dyadicPrimeBlock i).card : ℝ) *
              ((dyadicPrimeBlock j).card : ℝ) ≤
      2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock j).card : ℝ) +
        2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ) +
        2 * threeQuarterRoot ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            ((dyadicPrimeBlock j).card : ℝ) by gcongr)

/-- Every nonexceptional squarefree admissible element is controlled by the
sum of the three coloured-KST terms over the finite dyadic block range. -/
theorem card_nonexceptional_cast_le_sum_blockKSTBound
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) :
    ((nonexceptionalElements A).card : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        blockKSTBound A n i j := by
  calc
    ((nonexceptionalElements A).card : ℝ) ≤
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ c : fullBlockCoreSet A n i j,
            ColoredGraph.edgeCount
              (finiteCoreGraph A (fullBlockCoreSet A n i j)
                (dyadicPrimeBlock i) (dyadicPrimeBlock j) c) :=
      card_nonexceptional_cast_le_sum_edgeCount hA hsf
    _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        blockKSTBound A n i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa [blockKSTBound] using
        sum_finiteCoreGraph_edgeCount_le hA (fullBlockCoreSet A n i j)
          (dyadicPrimeBlock i) (dyadicPrimeBlock j)

theorem occupiedBlockIndices_subset_triangularBlockIndices
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    occupiedBlockIndices A ⊆ triangularBlockIndices n := by
  intro ij hij
  have hlog := occupiedBlockIndices_lt_log_add_one hA hij
  have hord := occupiedBlockIndices_fst_le_snd hij
  exact mem_triangularBlockIndices.mpr ⟨hlog.1, hlog.2, hord⟩

/-- The sum of the actual canonical block bounds is controlled by the
universal triangular majorant. -/
theorem sum_squarefreeBlockBound_le_universalNonexceptionalTerm
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n) :
    (∑ ij ∈ occupiedBlockIndices A,
      squarefreeBlockBound A ij.1 ij.2) ≤ universalNonexceptionalTerm n := by
  rw [← sum_universalBlockKSTBound_eq n]
  calc
    (∑ ij ∈ occupiedBlockIndices A,
        squarefreeBlockBound A ij.1 ij.2) ≤
        ∑ ij ∈ occupiedBlockIndices A,
          universalBlockKSTBound n ij.1 ij.2 := by
      apply Finset.sum_le_sum
      intro ij hij
      exact squarefreeBlockBound_le_universalBlockKSTBound hA
        (occupiedBlockIndices_fst_le_snd hij)
    _ ≤ ∑ ij ∈ triangularBlockIndices n,
        universalBlockKSTBound n ij.1 ij.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (occupiedBlockIndices_subset_triangularBlockIndices hA)
      intro ij hij hnot
      exact universalBlockKSTBound_nonneg n ij.1 ij.2

/-! ## Exceptional elements and the unconditional finite block estimate -/

/-- Members with fewer than two distinct prime factors.  In a positive
squarefree set these are precisely `1` and the primes. -/
noncomputable def exceptionalElements (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ a.primeFactors.card < 2

@[simp] theorem mem_exceptionalElements {A : Finset ℕ} {a : ℕ} :
    a ∈ exceptionalElements A ↔
      a ∈ A ∧ a.primeFactors.card < 2 := by
  simp [exceptionalElements]

theorem exceptionalElements_subset {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : IsSquarefreeSet A) :
    exceptionalElements A ⊆ {1} ∪ primesUpTo n := by
  intro a ha
  have hea := mem_exceptionalElements.mp ha
  have haIoc := Finset.mem_Ioc.mp (hA.1 hea.1)
  by_cases hzero : a.primeFactors.card = 0
  · have hempty : a.primeFactors = ∅ := Finset.card_eq_zero.mp hzero
    have ha01 : a = 0 ∨ a = 1 := Nat.primeFactors_eq_empty.mp hempty
    have ha1 : a = 1 := ha01.resolve_left haIoc.1.ne'
    simp [ha1]
  · have hone : a.primeFactors.card = 1 := by omega
    have hpp : IsPrimePow a := isPrimePow_iff_card_primeFactors_eq_one.mpr hone
    have hp : a.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsf a hea.1, hpp⟩
    simp [mem_primesUpTo, hp, haIoc.2]

/-- The exceptional contribution is at most one plus the prime-counting
function. -/
theorem exceptionalElements_card_le {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : IsSquarefreeSet A) :
    (exceptionalElements A).card ≤ 1 + Nat.primeCounting n := by
  calc
    (exceptionalElements A).card ≤ ({1} ∪ primesUpTo n).card :=
      Finset.card_le_card (exceptionalElements_subset hA hsf)
    _ ≤ ({1} : Finset ℕ).card + (primesUpTo n).card :=
      Finset.card_union_le _ _
    _ = 1 + Nat.primeCounting n := by simp

/-- Exceptional and nonexceptional elements partition the original set. -/
theorem card_eq_card_exceptional_add_card_nonexceptional (A : Finset ℕ) :
    A.card = (exceptionalElements A).card +
      (nonexceptionalElements A).card := by
  have h := A.card_filter_add_card_filter_not
    (p := fun a ↦ 2 ≤ a.primeFactors.card)
  simpa [exceptionalElements, nonexceptionalElements, Nat.not_le, Nat.add_comm]
    using h.symm

/-- The concrete right-hand side obtained from the exceptional estimate and
the coloured KST bound in every finite dyadic block. -/
noncomputable def squarefreeFiniteBlockBound (A : Finset ℕ) (n : ℕ) : ℝ :=
  1 + Nat.primeCounting n +
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      blockKSTBound A n i j

/-- Unconditional finite upper bound for every squarefree admissible set.
All remaining work in the analytic layer is to estimate the displayed
finite sum uniformly in `A`. -/
theorem card_cast_le_squarefreeFiniteBlockBound
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) :
    (A.card : ℝ) ≤ squarefreeFiniteBlockBound A n := by
  rw [card_eq_card_exceptional_add_card_nonexceptional]
  push_cast
  unfold squarefreeFiniteBlockBound
  exact add_le_add
    (by exact_mod_cast exceptionalElements_card_le hA hsf)
    (card_nonexceptional_cast_le_sum_blockKSTBound hA hsf)

/-- Set-independent finite majorant for the whole squarefree admissible set. -/
noncomputable def universalExceptionalTerm (n : ℕ) : ℝ :=
  1 + Nat.primeCounting n

noncomputable def universalSquarefreeBlockBound (n : ℕ) : ℝ :=
  universalExceptionalTerm n + universalNonexceptionalTerm n

theorem card_cast_le_universalSquarefreeBlockBound
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : IsSquarefreeSet A) :
    (A.card : ℝ) ≤ universalSquarefreeBlockBound n := by
  calc
    (A.card : ℝ) ≤ (exceptionalPart A).card +
        ∑ ij ∈ occupiedBlockIndices A,
          squarefreeBlockBound A ij.1 ij.2 :=
      card_le_exceptional_add_sum_squarefreeBlockBound hA hsf
    _ ≤ (1 + Nat.primeCounting n : ℕ) +
        universalNonexceptionalTerm n := by
      gcongr
      · exact_mod_cast exceptionalPart_card_le_one_add_primeCounting hA hsf
      · exact sum_squarefreeBlockBound_le_universalNonexceptionalTerm hA
    _ = universalSquarefreeBlockBound n := by
      simp [universalSquarefreeBlockBound, universalExceptionalTerm]

theorem natDivLambda_isBigO_scale :
    (fun n : ℕ ↦ (n : ℝ) / lambda (n : ℝ)) =O[atTop] scale := by
  refine IsBigO.of_bound 2 ?_
  have hlog := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hloglog := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  filter_upwards [hlog, hloglog, eventually_ge_atTop 1] with n hnlog hnloglog hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlam : 0 < lambda (n : ℝ) := lambda_pos (by exact_mod_cast hn)
  have hrealLog : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hnlog
  have hlam_ge : Real.log (n : ℝ) ≤ lambda (n : ℝ) := by
    rw [lambda_eq_one_add_log hnpos.ne']
    linarith
  have hleft : 0 ≤ (n : ℝ) / lambda (n : ℝ) :=
    div_nonneg hnpos.le hlam.le
  have hright : 0 ≤ scale n := by
    rw [scale]
    positivity
  rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright]
  calc
    (n : ℝ) / lambda (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_left hnpos.le hrealLog hlam_ge
    _ ≤ scale n := by
      rw [scale]
      calc
        (n : ℝ) / Real.log (n : ℝ) =
            ((n : ℝ) / Real.log (n : ℝ)) * 1 := by ring
        _ ≤ ((n : ℝ) / Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hnloglog
            (div_nonneg hnpos.le hrealLog.le)
        _ = (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ) := by ring
    _ ≤ 2 * scale n := by linarith

theorem universalExceptionalTerm_isBigO_scale :
    universalExceptionalTerm =O[atTop] scale := by
  have hone : (fun _n : ℕ ↦ (1 : ℝ)) =O[atTop] scale := by
    apply IsBigO.of_bound 1
    filter_upwards [scale_tendsto_atTop.eventually_ge_atTop 1] with n hn
    rw [norm_one, Real.norm_of_nonneg (zero_le_one.trans hn)]
    simpa using hn
  have hpi : (fun n : ℕ ↦ (Nat.primeCounting n : ℝ)) =O[atTop] scale :=
    primeCounting_isBigO_scale.trans natDivLambda_isBigO_scale
  change (fun n : ℕ ↦ (1 : ℝ) + (Nat.primeCounting n : ℝ)) =O[atTop] scale
  exact hone.add hpi

theorem universalSquarefreeBlockBound_nonneg (n : ℕ) :
    0 ≤ universalSquarefreeBlockBound n := by
  unfold universalSquarefreeBlockBound universalNonexceptionalTerm
  have hc := universalCoreTerm_nonneg n
  have hs := universalSmoothCoreTerm_nonneg n
  have hr := universalRectangleTerm_nonneg n
  have he : 0 ≤ universalExceptionalTerm n := by
    unfold universalExceptionalTerm
    positivity
  positivity

/-- Final assembly once the two remaining analytic bridge theorems are
available.  The rectangle bridge is already unconditional. -/
theorem universalSquarefreeBlockBound_isBigO_scale_of_core_smooth
    (hcore : universalCoreTerm =O[atTop] scale)
    (hsmooth : universalSmoothCoreTerm =O[atTop] scale) :
    universalSquarefreeBlockBound =O[atTop] scale := by
  have hnonexceptional : universalNonexceptionalTerm =O[atTop] scale := by
    change (fun n ↦ universalCoreTerm n + universalSmoothCoreTerm n +
      universalRectangleTerm n) =O[atTop] scale
    exact (hcore.add hsmooth).add
      RectangleBridge.universalRectangleTerm_isBigO_scale
  change (fun n ↦ universalExceptionalTerm n + universalNonexceptionalTerm n)
    =O[atTop] scale
  exact universalExceptionalTerm_isBigO_scale.add hnonexceptional

theorem squarefreeExtremalSize_isBigO_scale_of_core_smooth
    (hcore : universalCoreTerm =O[atTop] scale)
    (hsmooth : universalSmoothCoreTerm =O[atTop] scale) :
    (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ)) =O[atTop] scale := by
  have hdom : (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ))
      =O[atTop] universalSquarefreeBlockBound := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    obtain ⟨A, hA, hsf, hcard⟩ := squarefreeP_squarefreeExtremalSize n
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (universalSquarefreeBlockBound_nonneg n), one_mul]
    simpa [hcard] using card_cast_le_universalSquarefreeBlockBound hA hsf
  exact hdom.trans
    (universalSquarefreeBlockBound_isBigO_scale_of_core_smooth hcore hsmooth)

theorem extremalSize_isBigO_scale_of_core_smooth
    (hcore : universalCoreTerm =O[atTop] scale)
    (hsmooth : universalSmoothCoreTerm =O[atTop] scale) :
    (fun n : ℕ ↦ (extremalSize n : ℝ)) =O[atTop] scale :=
  extremalSize_isBigO_of_squarefreeExtremalSize_isBigO
    (squarefreeExtremalSize_isBigO_scale_of_core_smooth hcore hsmooth)

/-- Unconditional squarefree upper bound. -/
theorem squarefreeExtremalSize_isBigO_scale :
    (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ)) =O[atTop] scale :=
  squarefreeExtremalSize_isBigO_scale_of_core_smooth
    CoreBridge.universalCoreTerm_isBigO_scale
    universalSmoothCoreTerm_isBigO_scale

/-- The full upper bound after summing over exact square-part fibres. -/
theorem extremalSize_isBigO_scale :
    (fun n : ℕ ↦ (extremalSize n : ℝ)) =O[atTop] scale :=
  extremalSize_isBigO_of_squarefreeExtremalSize_isBigO
    squarefreeExtremalSize_isBigO_scale

/-- The real-valued sum appearing in the exact square-part reduction. -/
noncomputable def squarefreeReductionSum (n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 n, (squarefreeExtremalSize (n / q ^ 2) : ℝ)

theorem squarefreeReductionSum_nonneg (n : ℕ) :
    0 ≤ squarefreeReductionSum n := by
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- The natural-valued reduction theorem, coerced to the real numbers used by
Mathlib's asymptotics API. -/
theorem extremalSize_cast_le_squarefreeReductionSum (n : ℕ) :
    (extremalSize n : ℝ) ≤ squarefreeReductionSum n := by
  unfold squarefreeReductionSum
  exact_mod_cast extremalSize_le_sum_squarefreeExtremalSize n

/-- Any asymptotic estimate for the exact square-part sum is automatically an
upper estimate for the unrestricted extremal function. -/
theorem extremalSize_isBigO_of_squarefreeReductionSum_isBigO
    (h : squarefreeReductionSum =O[atTop] scale) :
    (fun n : ℕ ↦ (extremalSize n : ℝ)) =O[atTop] scale := by
  apply (IsBigO.of_bound 1 ?_).trans h
  filter_upwards with n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (squarefreeReductionSum_nonneg n), one_mul]
  exact extremalSize_cast_le_squarefreeReductionSum n

/-- The four contributions in the squarefree upper-bound argument.

The eventual pointwise estimate is stated for every admissible squarefree
set, rather than only for a chosen extremizer.  This is the form naturally
produced by the block encoding and makes the maximum step completely
transparent. -/
structure SquarefreeBlockEstimate where
  exceptionalTerm : ℕ → ℝ
  rectangleTerm : ℕ → ℝ
  coreTerm : ℕ → ℝ
  smoothCoreTerm : ℕ → ℝ
  eventually_terms_nonneg : ∀ᶠ n : ℕ in atTop,
    0 ≤ exceptionalTerm n + rectangleTerm n + coreTerm n + smoothCoreTerm n
  eventually_card_le : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
    RequiredCondition A n → IsSquarefreeSet A →
      (A.card : ℝ) ≤
        exceptionalTerm n + rectangleTerm n + coreTerm n + smoothCoreTerm n
  exceptional_isBigO : exceptionalTerm =O[atTop] scale
  rectangle_isBigO : rectangleTerm =O[atTop] scale
  core_isBigO : coreTerm =O[atTop] scale
  smoothCore_isBigO : smoothCoreTerm =O[atTop] scale

/-- Assembly of the exceptional, `S₁`, `S₂`, and `S₃` estimates into
the squarefree extremal upper bound. -/
theorem squarefreeExtremalSize_isBigO_of_blockEstimate
    (h : SquarefreeBlockEstimate) :
    (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ)) =O[atTop] scale := by
  let total : ℕ → ℝ := fun n ↦
    h.exceptionalTerm n + h.rectangleTerm n + h.coreTerm n + h.smoothCoreTerm n
  have htotal : total =O[atTop] scale :=
    ((h.exceptional_isBigO.add h.rectangle_isBigO).add h.core_isBigO).add
      h.smoothCore_isBigO
  have hdom : (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ)) =O[atTop] total := by
    apply IsBigO.of_bound 1
    filter_upwards [h.eventually_terms_nonneg, h.eventually_card_le]
      with n hn hcard
    obtain ⟨A, hA, hsf, hAcard⟩ := squarefreeP_squarefreeExtremalSize n
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (show 0 ≤ total n by exact hn), one_mul]
    simpa [total, hAcard] using hcard A hA hsf
  exact hdom.trans htotal

end Erdos888
