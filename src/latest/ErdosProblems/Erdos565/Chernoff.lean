import ErdosProblems.Erdos426
import ErdosProblems.Erdos565.RandomGraph

/-!
# A row-wise Chernoff estimate for Erdős problem 565

This file packages the elementary concentration estimate used for the random
edges between two fixed vertex sets.  The sample space is deliberately kept
as a finite set of Boolean matrices, so the statement can be used by cardinal
counting without introducing a probability space.
-/

open scoped BigOperators

namespace Erdos565
namespace Chernoff

open Finset

/-- The number of `true` entries in one Boolean row. -/
abbrev rowDegree {u : ℕ} (row : Fin u → Bool) : ℕ :=
  (Finset.univ.filter fun j ↦ row j = true).card

/-- A row is low when it has at most one quarter of its entries equal to
`true`. -/
def LowRow (u : ℕ) (row : Fin u → Bool) : Prop :=
  4 * rowDegree row ≤ u

/-- The finite set of low Boolean rows. -/
noncomputable def lowRows (u : ℕ) : Finset (Fin u → Bool) := by
  classical
  exact Finset.univ.filter (LowRow u)

/-- The number of non-low rows of a Boolean matrix. -/
noncomputable def highRowCount (s u : ℕ) (M : Fin s → Fin u → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ ¬ LowRow u (M i)).card

/-- The number of low rows of a Boolean matrix. -/
noncomputable def lowRowCount (s u : ℕ) (M : Fin s → Fin u → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ LowRow u (M i)).card

/-- Boolean matrices having at least `k` low rows. -/
noncomputable def manyLowRows (s u k : ℕ) :
    Finset (Fin s → Fin u → Bool) := by
  classical
  exact Finset.univ.filter fun M ↦ k ≤ lowRowCount s u M

/-- The exceptional matrices in which at most one quarter of the rows are
non-low.  This slightly enlarges the “fewer than one quarter” event used in
the paper and hence gives a stronger estimate. -/
noncomputable def fewHighRows (s u : ℕ) :
    Finset (Fin s → Fin u → Bool) := by
  classical
  exact Finset.univ.filter fun M ↦ 4 * highRowCount s u M ≤ s

/-- Matrices for which every row indexed by `A` is low. -/
noncomputable def fixedLowRows (s u : ℕ) (A : Finset (Fin s)) :
    Finset (Fin s → Fin u → Bool) := by
  classical
  exact Finset.univ.filter fun M ↦ ∀ i ∈ A, LowRow u (M i)

/-- A single fair Boolean row has at most the stated number of outcomes with
degree at most one quarter of the row length.  For positive row length this is
the usual Hoeffding exponent `-u / 8`; the separate zero case removes the
division-by-zero artefact from the generic bound. -/
theorem lowRow_card_le (u : ℕ) :
    (lowRows u).card ≤
      (2 : ℝ) ^ u * Real.exp (-(u : ℝ) / 8) := by
  classical
  by_cases hu : u = 0
  · subst u
    have hrows : lowRows 0 = Finset.univ := by
      ext row
      simp [lowRows, LowRow, rowDegree]
    rw [hrows]
    norm_num
  · have htail := Erdos426.ChernoffBound.lower_tail_bound u ((u : ℝ) / 4) (by positivity)
    have hevents :
        lowRows u =
          Finset.univ.filter (fun row : Fin u → Bool ↦
            (rowDegree row : ℝ) ≤ (u : ℝ) / 2 - (u : ℝ) / 4) := by
      ext row
      simp only [lowRows]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold LowRow
      constructor <;> intro h
      · have hc : (4 * rowDegree row : ℕ) ≤ u := h
        have hc' : (4 : ℝ) * rowDegree row ≤ u := by exact_mod_cast hc
        linarith
      · have hc' : (4 : ℝ) * rowDegree row ≤ u := by
          linarith
        exact_mod_cast hc'
    rw [hevents]
    convert htail using 1
    field_simp [hu]
    ring_nf

/-- Fixing a set `A` of rows to be low costs one factor `lowRows u` for
each member of `A`; all other rows remain arbitrary. -/
theorem fixedLowRows_card_le (s u : ℕ) (A : Finset (Fin s)) :
    (fixedLowRows s u A).card ≤
      (lowRows u).card ^ A.card * (2 ^ u) ^ (s - A.card) := by
  classical
  let encode : ↥(fixedLowRows s u A) →
      ((i : ↥A) → ↥(lowRows u)) ×
        ((i : {i : Fin s // i ∉ A}) → Fin u → Bool) := fun M ↦
    (fun i ↦ ⟨M.1 i.1, by
      simp only [lowRows, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp M.2).2 i.1 i.2⟩,
     fun i ↦ M.1 i.1)
  have hencode : Function.Injective encode := by
    intro M N h
    apply Subtype.ext
    funext i j
    by_cases hi : i ∈ A
    · have hfirst := congr_fun (congr_arg Prod.fst h) (⟨i, hi⟩ : ↥A)
      exact congr_fun (congr_arg Subtype.val hfirst) j
    · have hsecond := congr_fun (congr_arg Prod.snd h)
          (⟨i, hi⟩ : {i : Fin s // i ∉ A})
      exact congr_fun hsecond j
  rw [← Fintype.card_coe]
  refine le_trans (Fintype.card_le_of_injective encode hencode) ?_
  have hcomp : Fintype.card {i : Fin s // i ∉ A} = s - A.card := by
    simpa using Fintype.card_subtype_compl (fun i : Fin s ↦ i ∈ A)
  simp [Fintype.card_pi, hcomp]

/-- Union bound over the choice of `k` low rows.  This is the product-counting
form of independence needed below. -/
theorem manyLowRows_card_le (s u k : ℕ) :
    (manyLowRows s u k).card ≤
      2 ^ s * (lowRows u).card ^ k * (2 ^ u) ^ (s - k) := by
  classical
  let choices : Finset (Finset (Fin s)) := Finset.univ.powersetCard k
  let cover : Finset (Fin s → Fin u → Bool) :=
    choices.biUnion (fixedLowRows s u)
  have hsubset : manyLowRows s u k ⊆ cover := by
    intro M hM
    have hk : k ≤ lowRowCount s u M :=
      (Finset.mem_filter.mp hM).2
    let L : Finset (Fin s) := Finset.univ.filter fun i ↦ LowRow u (M i)
    have hLcard : L.card = lowRowCount s u M := by
      rfl
    obtain ⟨A, hAL, hAcard⟩ := Finset.exists_subset_card_eq (hLcard ▸ hk)
    have hAchoices : A ∈ choices := by
      simp only [choices, Finset.mem_powersetCard]
      exact ⟨fun _ _ ↦ Finset.mem_univ _, hAcard⟩
    simp only [cover, Finset.mem_biUnion]
    refine ⟨A, hAchoices, ?_⟩
    simp only [fixedLowRows, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    exact (Finset.mem_filter.mp (hAL hi)).2
  calc
    (manyLowRows s u k).card ≤ cover.card := Finset.card_le_card hsubset
    _ ≤ ∑ A ∈ choices, (fixedLowRows s u A).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ choices,
        (lowRows u).card ^ k * (2 ^ u) ^ (s - k) := by
      apply Finset.sum_le_sum
      intro A hA
      have hAcard : A.card = k :=
        (Finset.mem_powersetCard.mp hA).2
      simpa [hAcard] using fixedLowRows_card_le s u A
    _ = choices.card *
        ((lowRows u).card ^ k * (2 ^ u) ^ (s - k)) := by simp
    _ ≤ 2 ^ s * ((lowRows u).card ^ k * (2 ^ u) ^ (s - k)) := by
      gcongr
      simpa [choices] using Nat.choose_le_two_pow s k
    _ = 2 ^ s * (lowRows u).card ^ k * (2 ^ u) ^ (s - k) := by ring

/-- Low and non-low rows partition all rows. -/
theorem lowRowCount_add_highRowCount (s u : ℕ)
    (M : Fin s → Fin u → Bool) :
    lowRowCount s u M + highRowCount s u M = s := by
  classical
  simpa [lowRowCount, highRowCount] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s))) (fun i ↦ LowRow u (M i)))

/-- If at most one quarter of the rows are high, at least
`⌊3s/4⌋` rows are low. -/
theorem fewHighRows_subset_manyLowRows (s u : ℕ) :
    fewHighRows s u ⊆ manyLowRows s u (3 * s / 4) := by
  classical
  intro M hM
  simp only [manyLowRows, Finset.mem_filter, Finset.mem_univ, true_and]
  have hhigh : 4 * highRowCount s u M ≤ s :=
    (Finset.mem_filter.mp hM).2
  have hpartition := lowRowCount_add_highRowCount s u M
  omega

/-- The direct product estimate obtained from one-row Hoeffding and a union
bound over the choice of `⌊3s/4⌋` low rows.  This form deliberately keeps all
rounding in natural numbers and is often more convenient than the normalized
probability statement. -/
theorem fewHighRows_card_le_product (s u : ℕ) :
    ((fewHighRows s u).card : ℝ) ≤
      (2 : ℝ) ^ s *
        ((2 : ℝ) ^ u * Real.exp (-(u : ℝ) / 8)) ^ (3 * s / 4) *
        ((2 : ℝ) ^ u) ^ (s - 3 * s / 4) := by
  let k := 3 * s / 4
  have hsubset := fewHighRows_subset_manyLowRows s u
  have hmany := manyLowRows_card_le s u k
  have hcardNat : (fewHighRows s u).card ≤
      2 ^ s * (lowRows u).card ^ k * (2 ^ u) ^ (s - k) :=
    le_trans (Finset.card_le_card hsubset) hmany
  have hcardReal : ((fewHighRows s u).card : ℝ) ≤
      (2 : ℝ) ^ s * ((lowRows u).card : ℝ) ^ k *
        ((2 : ℝ) ^ u) ^ (s - k) := by
    exact_mod_cast hcardNat
  refine le_trans hcardReal ?_
  gcongr
  exact lowRow_card_le u

/-- Paper-facing form of the star-degree estimate.  Once there are at least
two rows and at least twenty-two possible neighbours per row, the proportion
of matrices in which fewer than a quarter of the rows have degree greater
than `u / 4` is at most `exp (-u*s/64)`.

The numerical lower bound `22` is intentionally coarse.  It is far below the
set sizes in the induced-Ramsey application and lets the proof absorb the
`2^s` choices in the union bound using only `2 ≤ exp 1`. -/
theorem fewHighRows_card_le_exp (s u : ℕ) (hs : 2 ≤ s) (hu : 22 ≤ u) :
    ((fewHighRows s u).card : ℝ) ≤
      (2 : ℝ) ^ (s * u) * Real.exp (-((s : ℝ) * u) / 64) := by
  let k : ℕ := 3 * s / 4
  have hk : k ≤ s := by
    dsimp [k]
    omega
  have hkhalfNat : s ≤ 2 * k := by
    dsimp [k]
    omega
  have hkhalf : (s : ℝ) / 2 ≤ k := by
    have hc : (s : ℝ) ≤ 2 * k := by exact_mod_cast hkhalfNat
    linarith
  have hcollapse :
      (((2 : ℝ) ^ u) ^ k) * (((2 : ℝ) ^ u) ^ (s - k)) =
        ((2 : ℝ) ^ u) ^ s := by
    rw [← pow_add]
    congr
    omega
  have hexppow :
      Real.exp (-(u : ℝ) / 8) ^ k =
        Real.exp (-((u : ℝ) * k) / 8) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hrewrite :
      (2 : ℝ) ^ s *
          ((2 : ℝ) ^ u * Real.exp (-(u : ℝ) / 8)) ^ k *
          ((2 : ℝ) ^ u) ^ (s - k) =
        (2 : ℝ) ^ (s * u) *
          ((2 : ℝ) ^ s * Real.exp (-((u : ℝ) * k) / 8)) := by
    rw [mul_pow, hexppow]
    calc
      (2 : ℝ) ^ s *
            (((2 : ℝ) ^ u) ^ k * Real.exp (-((u : ℝ) * k) / 8)) *
            ((2 : ℝ) ^ u) ^ (s - k) =
          (2 : ℝ) ^ s *
            ((((2 : ℝ) ^ u) ^ k * ((2 : ℝ) ^ u) ^ (s - k)) *
              Real.exp (-((u : ℝ) * k) / 8)) := by ring
      _ = (2 : ℝ) ^ s *
            (((2 : ℝ) ^ u) ^ s * Real.exp (-((u : ℝ) * k) / 8)) := by
          rw [hcollapse]
      _ = (2 : ℝ) ^ (s * u) *
            ((2 : ℝ) ^ s * Real.exp (-((u : ℝ) * k) / 8)) := by
          rw [← pow_mul]
          rw [Nat.mul_comm u s]
          ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have htwoPow : (2 : ℝ) ^ s ≤ Real.exp (s : ℝ) := by
    calc
      (2 : ℝ) ^ s ≤ Real.exp 1 ^ s :=
        pow_le_pow_left₀ (by positivity) htwo s
      _ = Real.exp (s : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have huReal : (22 : ℝ) ≤ u := by exact_mod_cast hu
  have hu3 : (64 : ℝ) ≤ 3 * u := by linarith
  have hus : (64 : ℝ) * s ≤ 3 * u * s :=
    mul_le_mul_of_nonneg_right hu3 (by positivity)
  have huk : (u : ℝ) * (s / 2) ≤ u * k :=
    mul_le_mul_of_nonneg_left hkhalf (by positivity)
  have hexponent :
      (s : ℝ) - (u : ℝ) * k / 8 ≤ -((s : ℝ) * u) / 64 := by
    nlinarith
  have hinner :
      (2 : ℝ) ^ s * Real.exp (-((u : ℝ) * k) / 8) ≤
        Real.exp (-((s : ℝ) * u) / 64) := by
    calc
      (2 : ℝ) ^ s * Real.exp (-((u : ℝ) * k) / 8) ≤
          Real.exp (s : ℝ) * Real.exp (-((u : ℝ) * k) / 8) := by
            exact mul_le_mul_of_nonneg_right htwoPow (Real.exp_nonneg _)
      _ = Real.exp ((s : ℝ) - (u : ℝ) * k / 8) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (-((s : ℝ) * u) / 64) :=
            Real.exp_le_exp.mpr hexponent
  calc
    ((fewHighRows s u).card : ℝ) ≤
        (2 : ℝ) ^ s *
          ((2 : ℝ) ^ u * Real.exp (-(u : ℝ) / 8)) ^ k *
          ((2 : ℝ) ^ u) ^ (s - k) := fewHighRows_card_le_product s u
    _ = (2 : ℝ) ^ (s * u) *
          ((2 : ℝ) ^ s * Real.exp (-((u : ℝ) * k) / 8)) := hrewrite
    _ ≤ (2 : ℝ) ^ (s * u) * Real.exp (-((s : ℝ) * u) / 64) := by
          exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-! ## Transfer to graph coordinates -/

section GraphCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The possible edge determined by an oriented pair in two disjoint sets.
The orientation is used only to enumerate the cross-edge coordinates; the
underlying edge remains unordered. -/
private def crossEdge (U S : Finset V) (hUS : Disjoint U S)
    (x : ↥S × ↥U) : RandomGraph.Edge V :=
  ⟨s(x.1.1, x.2.1), by
    rw [Sym2.mk_isDiag_iff]
    intro h
    exact Finset.disjoint_left.1 hUS x.2.2 (h ▸ x.1.2)⟩

/-- All graph coordinates running between two disjoint vertex sets. -/
noncomputable def crossEdges (U S : Finset V) (hUS : Disjoint U S) :
    Finset (RandomGraph.Edge V) := by
  classical
  exact (S.attach.product U.attach).image fun x ↦ crossEdge U S hUS x

theorem mem_crossEdges_iff {U S : Finset V} {hUS : Disjoint U S}
    {e : RandomGraph.Edge V} :
    e ∈ crossEdges U S hUS ↔
      ∃ v ∈ S, ∃ u ∈ U, e.1 = s(v, u) := by
  classical
  constructor
  · intro he
    rcases Finset.mem_image.1 he with ⟨x, _hx, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩
  · rintro ⟨v, hv, u, hu, he⟩
    apply Finset.mem_image.2
    refine ⟨(⟨v, hv⟩, ⟨u, hu⟩), by simp, ?_⟩
    apply Subtype.ext
    exact he.symm

@[simp] theorem card_crossEdges (U S : Finset V) (hUS : Disjoint U S) :
    (crossEdges U S hUS).card = S.card * U.card := by
  classical
  rw [crossEdges, Finset.card_image_iff.mpr]
  · simp
  · intro x _ y _ hxy
    rcases Sym2.eq_iff.1 (congrArg Subtype.val hxy) with h | h
    · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · exfalso
      exact Finset.disjoint_left.1 hUS y.2.2 (h.1 ▸ x.1.2)

/-- The Boolean cross-edge matrix of a graph, with rows indexed by `S` and
columns indexed by `U`. -/
noncomputable def graphCrossMatrix (G : SimpleGraph V)
    (U S : Finset V) (hUS : Disjoint U S) :
    Fin S.card → Fin U.card → Bool := by
  classical
  exact fun i j ↦
    decide (G.Adj ((S.equivFin).symm i).1 ((U.equivFin).symm j).1)

/-- Number of vertices of `S` whose degree into `U` is strictly greater than
one quarter of `|U|`, expressed through the independent cross coordinates. -/
noncomputable def graphHighCount (G : SimpleGraph V)
    (U S : Finset V) (hUS : Disjoint U S) : ℕ :=
  highRowCount S.card U.card (graphCrossMatrix G U S hUS)

/-- Graphs for which at most one quarter of `S` have cross-degree greater
than one quarter of `|U|`. -/
noncomputable def fewHighGraphs (U S : Finset V) (hUS : Disjoint U S) :
    Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun G ↦ 4 * graphHighCount G U S hUS ≤ S.card

/-- Degree of `v` into a finite vertex set, with classical decidability hidden
from downstream statements. -/
noncomputable def degreeInto (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ := by
  classical
  exact (U.filter fun u ↦ G.Adj v u).card

/-- Vertices in `S` with more than one quarter of `U` as neighbours. -/
noncomputable def highDegreeVertices (G : SimpleGraph V)
    (U S : Finset V) : Finset V := by
  classical
  exact S.filter fun v ↦ U.card < 4 * degreeInto G U v

@[simp] theorem rowDegree_graphCrossMatrix (G : SimpleGraph V)
    (U S : Finset V) (hUS : Disjoint U S) (i : Fin S.card) :
    rowDegree (graphCrossMatrix G U S hUS i) =
      degreeInto G U ((S.equivFin).symm i).1 := by
  classical
  unfold degreeInto
  let f : Fin U.card → V := fun j ↦ ((U.equivFin).symm j).1
  apply Finset.card_bij (fun j _ ↦ f j)
  · intro j hj
    have hjAdj : G.Adj ((S.equivFin).symm i).1 (f j) := by
      simpa [rowDegree, graphCrossMatrix, f] using
        (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.2 ⟨((U.equivFin).symm j).2, hjAdj⟩
  · intro a ha b hb hab
    exact (U.equivFin.symm.injective (Subtype.ext hab))
  · intro u hu
    refine ⟨U.equivFin ⟨u, (Finset.mem_filter.mp hu).1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [graphCrossMatrix] using (Finset.mem_filter.mp hu).2
    · simp [f]

@[simp] theorem graphHighCount_eq_card_highDegreeVertices (G : SimpleGraph V)
    (U S : Finset V) (hUS : Disjoint U S) :
    graphHighCount G U S hUS = (highDegreeVertices G U S).card := by
  classical
  unfold graphHighCount highRowCount
  let f : Fin S.card → V := fun i ↦ ((S.equivFin).symm i).1
  apply Finset.card_bij (fun i _ ↦ f i)
  · intro i hi
    have hiHigh : U.card < 4 * degreeInto G U (f i) := by
      have hiNotLow := (Finset.mem_filter.mp hi).2
      simp only [LowRow, rowDegree_graphCrossMatrix] at hiNotLow
      simpa [f] using (Nat.lt_of_not_ge hiNotLow)
    exact Finset.mem_filter.2 ⟨((S.equivFin).symm i).2, hiHigh⟩
  · intro a ha b hb hab
    exact S.equivFin.symm.injective (Subtype.ext hab)
  · intro v hv
    refine ⟨S.equivFin ⟨v, (Finset.mem_filter.mp hv).1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, LowRow,
        rowDegree_graphCrossMatrix]
      have hvHigh := (Finset.mem_filter.mp hv).2
      simp only [Equiv.symm_apply_apply, not_le, gt_iff_lt]
      exact hvHigh
    · simp [f]

@[simp] theorem mem_fewHighGraphs_iff (G : SimpleGraph V)
    (U S : Finset V) (hUS : Disjoint U S) :
    G ∈ fewHighGraphs U S hUS ↔
      4 * (highDegreeVertices G U S).card ≤ S.card := by
  classical
  simp [fewHighGraphs, graphHighCount_eq_card_highDegreeVertices]

/-- Compatibility with Mathlib's `neighborFinset` notation. -/
theorem degreeInto_eq_card_neighborFinset (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) (v : V) :
    degreeInto G U v = (G.neighborFinset v ∩ U).card := by
  classical
  unfold degreeInto
  congr 1
  ext u
  simp [and_comm]

/-- Fully expanded membership criterion used by the key-lemma layer. -/
theorem mem_fewHighGraphs_iff_neighborFinset (G : SimpleGraph V)
    [DecidableRel G.Adj] (U S : Finset V) (hUS : Disjoint U S) :
    G ∈ fewHighGraphs U S hUS ↔
      4 * (S.filter fun v ↦
        U.card < 4 * (G.neighborFinset v ∩ U).card).card ≤ S.card := by
  classical
  rw [mem_fewHighGraphs_iff]
  have hfilter : highDegreeVertices G U S =
      S.filter (fun v ↦ U.card < 4 * (G.neighborFinset v ∩ U).card) := by
    unfold highDegreeVertices
    apply Finset.filter_congr
    intro v _
    rw [degreeInto_eq_card_neighborFinset]
  rw [hfilter]

/-- Exact transfer from graph coordinates to the Boolean-matrix exceptional
set.  The second factor counts all edge coordinates not running between
`S` and `U`. -/
theorem fewHighGraphs_card_le (U S : Finset V) (hUS : Disjoint U S) :
    (fewHighGraphs U S hUS).card ≤
      (fewHighRows S.card U.card).card *
        2 ^ ((Fintype.card V).choose 2 - S.card * U.card) := by
  classical
  let R : Finset (RandomGraph.Edge V) :=
    RandomGraph.edgeUniverse V \ crossEdges U S hUS
  let encode : ↥(fewHighGraphs U S hUS) →
      ↥(fewHighRows S.card U.card) × ↥R.powerset := fun G ↦
    (⟨graphCrossMatrix G.1 U S hUS, by
      simpa [fewHighRows, fewHighGraphs, graphHighCount] using
        (Finset.mem_filter.mp G.2).2⟩,
     ⟨RandomGraph.edgesOfGraph G.1 \ crossEdges U S hUS, by
      apply Finset.mem_powerset.2
      intro e he
      have he' := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.2 ⟨by simp [RandomGraph.edgeUniverse], he'.2⟩⟩)
  have hencode : Function.Injective encode := by
    intro G H h
    apply Subtype.ext
    have hmat : graphCrossMatrix G.1 U S hUS =
        graphCrossMatrix H.1 U S hUS := congrArg (fun z ↦ z.1.1) h
    have hres : RandomGraph.edgesOfGraph G.1 \ crossEdges U S hUS =
        RandomGraph.edgesOfGraph H.1 \ crossEdges U S hUS :=
      congrArg (fun z ↦ z.2.1) h
    have hedge : RandomGraph.edgesOfGraph G.1 = RandomGraph.edgesOfGraph H.1 := by
      ext e
      by_cases he : e ∈ crossEdges U S hUS
      · rcases mem_crossEdges_iff.mp he with ⟨v, hv, u, hu, heu⟩
        let i : Fin S.card := S.equivFin ⟨v, hv⟩
        let j : Fin U.card := U.equivFin ⟨u, hu⟩
        have hij := congr_fun (congr_fun hmat i) j
        have hadj : G.1.Adj v u ↔ H.1.Adj v u := by
          have hi : (S.equivFin.symm i).1 = v := by simp [i]
          have hj : (U.equivFin.symm j).1 = u := by simp [j]
          simpa [graphCrossMatrix, hi, hj] using hij
        simpa [RandomGraph.mem_edgesOfGraph, SimpleGraph.mem_edgeSet, heu] using hadj
      · have hm := congrArg (fun T : Finset (RandomGraph.Edge V) ↦ e ∈ T) hres
        simpa [he] using hm
    calc
      G.1 = RandomGraph.graphOfEdges (RandomGraph.edgesOfGraph G.1) :=
        (RandomGraph.graphOfEdges_edgesOfGraph G.1).symm
      _ = RandomGraph.graphOfEdges (RandomGraph.edgesOfGraph H.1) :=
        congrArg RandomGraph.graphOfEdges hedge
      _ = H.1 := RandomGraph.graphOfEdges_edgesOfGraph H.1
  rw [← Fintype.card_coe]
  refine le_trans (Fintype.card_le_of_injective encode hencode) ?_
  have hcross : crossEdges U S hUS ⊆ RandomGraph.edgeUniverse V := by
    simp [RandomGraph.edgeUniverse]
  have hR : R.card = (Fintype.card V).choose 2 - S.card * U.card := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hcross, RandomGraph.card_edgeUniverse,
      card_crossEdges]
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_powerset, hR]

/-- Graph-coordinate form of the concentration estimate.  The left side is
an actual count of labelled graphs, and the leading factor on the right is
the total number of labelled graphs on `V`. -/
theorem fewHighGraphs_card_le_exp (U S : Finset V) (hUS : Disjoint U S)
    (hS : 2 ≤ S.card) (hU : 22 ≤ U.card) :
    ((fewHighGraphs U S hUS).card : ℝ) ≤
      (Fintype.card (SimpleGraph V) : ℝ) *
        Real.exp (-((S.card : ℝ) * U.card) / 64) := by
  have hnat := fewHighGraphs_card_le U S hUS
  have hreal : ((fewHighGraphs U S hUS).card : ℝ) ≤
      ((fewHighRows S.card U.card).card : ℝ) *
        (2 : ℝ) ^ ((Fintype.card V).choose 2 - S.card * U.card) := by
    exact_mod_cast hnat
  have hmatrix := fewHighRows_card_le_exp S.card U.card hS hU
  have hcross : S.card * U.card ≤ (Fintype.card V).choose 2 := by
    rw [← card_crossEdges U S hUS, ← RandomGraph.card_edgeUniverse (V := V)]
    exact Finset.card_le_card (by simp [RandomGraph.edgeUniverse])
  calc
    ((fewHighGraphs U S hUS).card : ℝ) ≤
        ((fewHighRows S.card U.card).card : ℝ) *
          (2 : ℝ) ^ ((Fintype.card V).choose 2 - S.card * U.card) := hreal
    _ ≤ ((2 : ℝ) ^ (S.card * U.card) *
          Real.exp (-((S.card : ℝ) * U.card) / 64)) *
          (2 : ℝ) ^ ((Fintype.card V).choose 2 - S.card * U.card) := by
        exact mul_le_mul_of_nonneg_right hmatrix (by positivity)
    _ = (2 : ℝ) ^ (Fintype.card V).choose 2 *
          Real.exp (-((S.card : ℝ) * U.card) / 64) := by
        rw [mul_assoc]
        calc
          (2 : ℝ) ^ (S.card * U.card) *
                (Real.exp (-((S.card : ℝ) * U.card) / 64) *
                  (2 : ℝ) ^ ((Fintype.card V).choose 2 - S.card * U.card)) =
              ((2 : ℝ) ^ (S.card * U.card) *
                (2 : ℝ) ^ ((Fintype.card V).choose 2 - S.card * U.card)) *
                Real.exp (-((S.card : ℝ) * U.card) / 64) := by ring
          _ = (2 : ℝ) ^ (Fintype.card V).choose 2 *
                Real.exp (-((S.card : ℝ) * U.card) / 64) := by
              rw [← pow_add]
              congr 2
              omega
    _ = (Fintype.card (SimpleGraph V) : ℝ) *
          Real.exp (-((S.card : ℝ) * U.card) / 64) := by
        rw [RandomGraph.card_simpleGraph]
        norm_cast

end GraphCoordinates

end Chernoff
end Erdos565
