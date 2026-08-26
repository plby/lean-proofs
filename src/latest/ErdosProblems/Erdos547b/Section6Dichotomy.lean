/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.Structures
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.Regularity

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoSection6Dichotomy

open Finset SimpleGraph
open ZhaoStability

/-!
This file isolates the last, completely finite, reduced-to-host step in
Section 6 of Zhao's proof.  Unlike an abstract "stability certificate", all
hypotheses below are statements about the actual host graph, cleaned graph,
cluster assignment, and reduced graph.
-/

/-- Noncontainment rules out every concrete forest-gluing witness.  This is
the logically correct way to use "failure of all embedding configurations":
each sufficient configuration must first construct this finite object. -/
theorem no_forestGluingCertificate_of_not_isContained
    {τ V : Type*} {T : SimpleGraph τ} {G : SimpleGraph V}
    (hnot : ¬ T.IsContained G) :
    ¬ Nonempty (ForestGluingCertificate T G) := by
  rintro ⟨C⟩
  exact hnot ⟨C.toCopy⟩

/-- The ordinary vertices carried by a set of cluster indices. -/
def clusterUnion {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) : Finset V :=
  I.biUnion (clusterVertices P)

@[simp] theorem mem_clusterUnion {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) (v : V) :
    v ∈ clusterUnion P I ↔ ∃ i ∈ I, P v = some i := by
  unfold clusterUnion
  simp

theorem clusterVertices_disjoint {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) {i j : ι} (hij : i ≠ j) :
    Disjoint (clusterVertices P i) (clusterVertices P j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hi : P v = some i := (mem_clusterVertices P i v).mp hvi
  have hj : P v = some j := (mem_clusterVertices P j v).mp hvj
  exact hij (Option.some.inj (hi.symm.trans hj))

theorem exceptional_disjoint_clusterUnion {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) :
    Disjoint (exceptionalVertices P) (clusterUnion P I) := by
  rw [Finset.disjoint_left]
  intro v hvE hvI
  rw [mem_clusterUnion] at hvI
  obtain ⟨i, hi, hv⟩ := hvI
  have hvnone := (mem_exceptionalVertices P v).mp hvE
  simp [hvnone] at hv

theorem clusterUnion_disjoint {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) {I J : Finset ι}
    (hIJ : Disjoint I J) :
    Disjoint (clusterUnion P I) (clusterUnion P J) := by
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rw [mem_clusterUnion] at hvI hvJ
  obtain ⟨i, hiI, hvi⟩ := hvI
  obtain ⟨j, hjJ, hvj⟩ := hvJ
  have hij : i = j := Option.some.inj (hvi.symm.trans hvj)
  subst j
  exact Finset.disjoint_left.mp hIJ hiI hjJ

theorem exceptional_union_clusterUnion_univ {V ι : Type*} [Fintype V]
    [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) :
    exceptionalVertices P ∪ clusterUnion P Finset.univ = Finset.univ := by
  ext v
  cases hv : P v with
  | none => simp [hv, mem_exceptionalVertices]
  | some i => simp [hv, mem_clusterUnion]

theorem clusterUnion_union_of_union {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I J : Finset ι) :
    clusterUnion P (I ∪ J) = clusterUnion P I ∪ clusterUnion P J := by
  ext v
  simp only [mem_clusterUnion, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hPi⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨i, hi, hPi⟩
    · exact Or.inr ⟨i, hi, hPi⟩
  · rintro (⟨i, hi, hPi⟩ | ⟨i, hi, hPi⟩)
    · exact ⟨i, Or.inl hi, hPi⟩
    · exact ⟨i, Or.inr hi, hPi⟩

theorem card_clusterUnion_le {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) (m : ℕ)
    (hcluster : ∀ i ∈ I, (clusterVertices P i).card ≤ m) :
    (clusterUnion P I).card ≤ I.card * m := by
  change (I.biUnion (clusterVertices P)).card ≤ I.card * m
  exact Finset.card_biUnion_le_card_mul I (clusterVertices P) m hcluster

theorem card_clusterUnion_eq_of_equal {V ι : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) (m : ℕ)
    (hcluster : ∀ i ∈ I, (clusterVertices P i).card = m) :
    (clusterUnion P I).card = I.card * m := by
  classical
  change (I.biUnion (clusterVertices P)).card = I.card * m
  rw [Finset.card_biUnion]
  · exact Finset.sum_const_nat hcluster
  · intro i hi j hj hij
    exact clusterVertices_disjoint P hij

/-! ## Pointwise degree loss restricted to a target set -/

theorem degreeInto_le_of_le {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (v : V) (S : Finset V) :
    Erdos547EC2.degreeInto H v S ≤ Erdos547EC2.degreeInto G v S := by
  unfold Erdos547EC2.degreeInto
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, hHG hw.2⟩

/-- If `H ≤ G` and at most `loss` incident edges were deleted at every
vertex, then the same loss bound holds after restricting neighbors to any
set `S`. -/
theorem degreeInto_le_cleaned_add_loss {V : Type*} [Fintype V]
    [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (v : V) (S : Finset V) :
    Erdos547EC2.degreeInto G v S ≤
      Erdos547EC2.degreeInto H v S + loss := by
  let A := S.filter fun w => H.Adj v w
  let B := S.filter fun w => G.Adj v w
  have hAB : A ⊆ B := by
    intro w hw
    simp only [A, B, Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hHG hw.2⟩
  have hBA : B.card ≤ A.card + (B \ A).card := by
    rw [Nat.add_comm]
    exact (Finset.card_sdiff_add_card_eq_card hAB).symm.le
  have hdiff : (B \ A).card ≤ loss := by
    have hsub : B \ A ⊆ G.neighborFinset v \ H.neighborFinset v := by
      intro w hw
      simp only [B, A, Finset.mem_sdiff, Finset.mem_filter,
        mem_neighborFinset] at hw ⊢
      exact ⟨hw.1.2, fun hH => hw.2 ⟨hw.1.1, hH⟩⟩
    have hcard := Finset.card_le_card hsub
    have hHnbr : H.neighborFinset v ⊆ G.neighborFinset v := by
      intro w hw
      simpa only [mem_neighborFinset] using hHG (by simpa only [mem_neighborFinset] using hw)
    rw [Finset.card_sdiff_of_subset hHnbr,
      G.card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree] at hcard
    have := hloss v
    omega
  change B.card ≤ A.card + loss
  omega

/-! ## Exact control of rebalancing a near-half cut -/

/-- Replacing a side `X` by an exactly balanced side `W` changes at most
`q (|W \ X| + |X \ W|)` crossing pairs. -/
theorem card_interedges_rebalance_le {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y W : Finset V) (q : ℕ)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hV : Fintype.card V = 2 * q) (hW : W.card = q) :
    (G.interedges W (Finset.univ \ W)).card ≤
      (G.interedges X Y).card + q * ((W \ X).card + (X \ W).card) := by
  classical
  let A := G.interedges X Y
  let B := (W \ X).product (Finset.univ \ W)
  let C := W.product (X \ W)
  have hsub : G.interedges W (Finset.univ \ W) ⊆ A ∪ B ∪ C := by
    intro p hp
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hpW, hpWc, hpadj⟩
    by_cases hpX : p.1 ∈ X
    · by_cases hpY : p.2 ∈ Y
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hpX, hpY, hpadj⟩
      · apply Finset.mem_union_right
        have hp2X : p.2 ∈ X := by
          have : p.2 ∈ X ∪ Y := by simpa [hcover]
          exact (Finset.mem_union.mp this).resolve_right hpY
        exact Finset.mem_product.mpr ⟨hpW, Finset.mem_sdiff.mpr ⟨hp2X, hpWc⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_product.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hpW, hpX⟩,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpWc⟩⟩
  calc
    (G.interedges W (Finset.univ \ W)).card
        ≤ (A ∪ B ∪ C).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card + C.card := by
      exact (Finset.card_union_le (A ∪ B) C).trans
        (Nat.add_le_add_right (Finset.card_union_le A B) C.card)
    _ = (G.interedges X Y).card +
        (W \ X).card * (Finset.univ \ W).card +
        W.card * (X \ W).card := by
      simp [A, B, C]
    _ = (G.interedges X Y).card + q *
        ((W \ X).card + (X \ W).card) := by
      have hWc : (Finset.univ \ W).card = q := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, hV, hW]
        omega
      rw [hW, hWc]
      simp only [Nat.mul_add, Nat.mul_comm]
      ac_rfl

/-! ## Cleaned reduced cut to an original-host cut -/

theorem cleaned_interedges_le_reduced_slots
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (I J : Finset ι) (m : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m) :
    (H.interedges (clusterUnion P I) (clusterUnion P J)).card ≤
      (R.interedges I J).card * (m * m) := by
  classical
  let block : ι × ι → Finset (V × V) := fun ij =>
    H.interedges (clusterVertices P ij.1) (clusterVertices P ij.2)
  let E : Finset (ι × ι) := R.interedges I J
  have hunion : H.interedges (clusterUnion P I) (clusterUnion P J) =
      E.biUnion block := by
    rw [clusterUnion, clusterUnion, H.interedges_biUnion]
    apply Finset.Subset.antisymm
    · intro p hp
      rw [Finset.mem_biUnion] at hp ⊢
      obtain ⟨ij, hij, hp⟩ := hp
      rw [Finset.mem_product] at hij
      have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
      have hPi : P p.1 = some ij.1 :=
        (mem_clusterVertices P ij.1 p.1).mp hp'.1
      have hPj : P p.2 = some ij.2 :=
        (mem_clusterVertices P ij.2 p.2).mp hp'.2.1
      have hR : R.Adj ij.1 ij.2 := hrespect hPi hPj hp'.2.2
      exact ⟨ij, (SimpleGraph.mem_interedges_iff R).mpr
        ⟨hij.1, hij.2, hR⟩, hp⟩
    · intro p hp
      rw [Finset.mem_biUnion] at hp ⊢
      obtain ⟨ij, hij, hp⟩ := hp
      have hij' := (SimpleGraph.mem_interedges_iff R).mp hij
      exact ⟨ij, Finset.mem_product.mpr ⟨hij'.1, hij'.2.1⟩, hp⟩
  rw [hunion]
  calc
    (E.biUnion block).card ≤ ∑ ij ∈ E, (block ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ E, m * m := by
      apply Finset.sum_le_sum
      intro ij hij
      exact (H.card_interedges_le_mul _ _).trans <|
        Nat.mul_le_mul (hcluster ij.1) (hcluster ij.2)
    _ = E.card * (m * m) := by simp

/-! ## The final Claims 6.17--6.18 aggregation -/

/-- If `V₁` is covered by its small-partner and large-partner pieces,
then the crossing edges of the thresholded reduced graph split between the
two estimates furnished by Claims 6.17 and 6.18. -/
theorem thresholded_crossing_le_claim617_add_claim618
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R R' : SimpleGraph ι) [DecidableRel R.Adj] [DecidableRel R'.Adj]
    (hR'R : R' ≤ R) (V₁ V₂ S₁ L₁ : Finset ι)
    (hV₁ : V₁ ⊆ S₁ ∪ L₁) :
    (R'.interedges V₁ V₂).card ≤
      (R.interedges S₁ V₂).card + (R'.interedges L₁ V₂).card := by
  classical
  have hsub : R'.interedges V₁ V₂ ⊆
      R.interedges S₁ V₂ ∪ R'.interedges L₁ V₂ := by
    intro p hp
    have hp' := (SimpleGraph.mem_interedges_iff R').mp hp
    rcases Finset.mem_union.mp (hV₁ hp'.1) with hpS | hpL
    · exact Finset.mem_union_left _ <|
        (SimpleGraph.mem_interedges_iff R).mpr ⟨hpS, hp'.2.1, hR'R hp'.2.2⟩
    · exact Finset.mem_union_right _ <|
        (SimpleGraph.mem_interedges_iff R').mpr ⟨hpL, hp'.2.1, hp'.2.2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Numerical form of the last display combining Claims 6.17 and 6.18. -/
theorem thresholded_crossing_lt_of_claim617_claim618
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R R' : SimpleGraph ι) [DecidableRel R.Adj] [DecidableRel R'.Adj]
    (hR'R : R' ≤ R) (V₁ V₂ S₁ L₁ : Finset ι)
    (hV₁ : V₁ ⊆ S₁ ∪ L₁) (a b cross : ℕ)
    (h617 : (R.interedges S₁ V₂).card < a)
    (h618 : (R'.interedges L₁ V₂).card < b)
    (hab : a + b ≤ cross + 1) :
    (R'.interedges V₁ V₂).card ≤ cross := by
  have hsum := thresholded_crossing_le_claim617_add_claim618
    R R' hR'R V₁ V₂ S₁ L₁ hV₁
  omega

/-- Passing from the cleaned graph back to the original graph costs at most
`loss` edges at each vertex of the left side. -/
theorem original_interedges_le_cleaned_add_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (X Y : Finset V) :
    (G.interedges X Y).card ≤ (H.interedges X Y).card + X.card * loss := by
  rw [← Erdos547EC2.sum_degreeInto_eq_card_interedges,
    ← Erdos547EC2.sum_degreeInto_eq_card_interedges]
  calc
    ∑ v ∈ X, Erdos547EC2.degreeInto G v Y
        ≤ ∑ v ∈ X, (Erdos547EC2.degreeInto H v Y + loss) := by
          apply Finset.sum_le_sum
          intro v hv
          exact degreeInto_le_cleaned_add_loss G H hHG loss hloss v Y
    _ = (∑ v ∈ X, Erdos547EC2.degreeInto H v Y) + X.card * loss := by
      rw [Finset.sum_add_distrib]
      simp

/-- Equation (6.20), in integral form.  The right side contains the three
actual sources of crossing edges: positive reduced pairs, exceptional
vertices, and edges removed by degree-form regularity. -/
theorem original_clusterCut_interedges_le
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (hrespect : EdgesRespectReducedGraph P H R)
    (I J : Finset ι) (m : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m) :
    let X := clusterUnion P I
    let Y := exceptionalVertices P ∪ clusterUnion P J
    (G.interedges X Y).card ≤
      (R.interedges I J).card * (m * m) +
        X.card * ((exceptionalVertices P).card + loss) := by
  classical
  dsimp only
  let X := clusterUnion P I
  let C := clusterUnion P J
  let E := exceptionalVertices P
  have hsplit : H.interedges X (E ∪ C) =
      H.interedges X E ∪ H.interedges X C := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    aesop
  have hclean : (H.interedges X (E ∪ C)).card ≤
      X.card * E.card + (R.interedges I J).card * (m * m) := by
    rw [hsplit]
    calc
      (H.interedges X E ∪ H.interedges X C).card
          ≤ (H.interedges X E).card + (H.interedges X C).card :=
            Finset.card_union_le _ _
      _ ≤ X.card * E.card + (R.interedges I J).card * (m * m) :=
        Nat.add_le_add (H.card_interedges_le_mul X E)
          (cleaned_interedges_le_reduced_slots P H R hrespect I J m hcluster)
  have horiginal := original_interedges_le_cleaned_add_loss
    G H hHG loss hloss X (E ∪ C)
  change (G.interedges X (E ∪ C)).card ≤
    (R.interedges I J).card * (m * m) + X.card * (E.card + loss)
  calc
    (G.interedges X (E ∪ C)).card
        ≤ (H.interedges X (E ∪ C)).card + X.card * loss := horiginal
    _ ≤ (X.card * E.card + (R.interedges I J).card * (m * m)) +
        X.card * loss := Nat.add_le_add_right hclean _
    _ = (R.interedges I J).card * (m * m) + X.card * (E.card + loss) := by
      rw [Nat.mul_add]
      omega

/-- A set within `b` of half the ambient order can be changed in at most
`b` places in either direction into an exactly half-sized set. -/
theorem exists_exact_half_near {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) (q b : ℕ) (hV : Fintype.card V = 2 * q)
    (hupper : X.card ≤ q + b) (hlower : q ≤ X.card + b) :
    ∃ W : Finset V, W.card = q ∧
      (X \ W).card ≤ b ∧ (W \ X).card ≤ b := by
  classical
  rcases le_total X.card q with hXq | hqX
  · have hquniv : q ≤ (Finset.univ : Finset V).card := by
      rw [Finset.card_univ, hV]
      omega
    obtain ⟨W, hXW, hWuniv, hWcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ X) hXq hquniv
    refine ⟨W, hWcard, ?_, ?_⟩
    · simp [Finset.sdiff_eq_empty_iff_subset.mpr hXW]
    · rw [Finset.card_sdiff_of_subset hXW, hWcard]
      omega
  · obtain ⟨W, hWX, hWcard⟩ := Finset.exists_subset_card_eq hqX
    refine ⟨W, hWcard, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset hWX, hWcard]
      omega
    · simp [Finset.sdiff_eq_empty_iff_subset.mpr hWX]

/-- The exact host-level sparse-cut lift used at the end of Section 6.
Every hypothesis refers to the actual degree-form output.  In particular,
`hcross` is the conclusion obtained by combining Claims 6.17 and 6.18; it
is not an assumed EC2 conclusion. -/
theorem exists_balanced_sparse_cut_of_degreeForm
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (hrespect : EdgesRespectReducedGraph P H R)
    (I J : Finset ι) (m q b cross : ℕ)
    (hindices : Disjoint I J) (hindices_cover : I ∪ J = Finset.univ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hV : Fintype.card V = 2 * q)
    (hXupper : (clusterUnion P I).card ≤ q + b)
    (hXlower : q ≤ (clusterUnion P I).card + b)
    (hcross : (R.interedges I J).card ≤ cross) :
    ∃ W Z : Finset V,
      Disjoint W Z ∧ W ∪ Z = Finset.univ ∧
      W.card = q ∧ Z.card = q ∧
      (G.interedges W Z).card ≤
        cross * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss) +
          2 * q * b := by
  classical
  let X := clusterUnion P I
  let Y := exceptionalVertices P ∪ clusterUnion P J
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨(exceptional_disjoint_clusterUnion P I).symm,
      clusterUnion_disjoint P hindices⟩
  have hcover : X ∪ Y = Finset.univ := by
    dsimp only [X, Y]
    calc
      clusterUnion P I ∪ (exceptionalVertices P ∪ clusterUnion P J) =
          exceptionalVertices P ∪ (clusterUnion P I ∪ clusterUnion P J) := by
            ac_rfl
      _ = exceptionalVertices P ∪ clusterUnion P (I ∪ J) := by
        rw [clusterUnion_union_of_union]
      _ = exceptionalVertices P ∪ clusterUnion P Finset.univ := by
        rw [hindices_cover]
      _ = Finset.univ := exceptional_union_clusterUnion_univ P
  obtain ⟨W, hWcard, hXW, hWX⟩ :=
    exists_exact_half_near X q b hV hXupper hXlower
  let Z := Finset.univ \ W
  have hZcard : Z.card = q := by
    dsimp only [Z]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hV, hWcard]
    omega
  have hGXY := original_clusterCut_interedges_le
    P G H R hHG loss hloss hrespect I J m hcluster
  have hrebalance := card_interedges_rebalance_le G X Y W q
    hXY hcover hV hWcard
  refine ⟨W, Z, Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (Finset.subset_univ W), hWcard, hZcard, ?_⟩
  change (G.interedges W (Finset.univ \ W)).card ≤ _
  dsimp only [X, Y] at hGXY
  have hcross' : (R.interedges I J).card * (m * m) ≤ cross * (m * m) :=
    Nat.mul_le_mul_right (m * m) hcross
  have hmove : (W \ X).card + (X \ W).card ≤ 2 * b := by omega
  have hmoveq : q * ((W \ X).card + (X \ W).card) ≤ q * (2 * b) :=
    Nat.mul_le_mul_left q hmove
  calc
    (G.interedges W (Finset.univ \ W)).card
        ≤ (G.interedges X Y).card +
          q * ((W \ X).card + (X \ W).card) := hrebalance
    _ ≤ ((R.interedges I J).card * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss)) +
          q * ((W \ X).card + (X \ W).card) :=
      Nat.add_le_add hGXY (le_refl _)
    _ ≤ (cross * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss)) +
          q * (2 * b) :=
      Nat.add_le_add (Nat.add_le_add_right hcross' _) hmoveq
    _ = cross * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss) +
          2 * q * b := by
      ring

theorem edgeDensity_le_of_card_interedges_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (q : ℕ) (hq : 0 < q)
    (hA : A.card = q) (hB : B.card = q) (α : ℚ)
    (hcross : ((G.interedges A B).card : ℚ) ≤
      α * (q : ℚ) * (q : ℚ)) :
    G.edgeDensity A B ≤ α := by
  rw [G.edgeDensity_def, hA, hB]
  have hdenom : (0 : ℚ) < (q : ℚ) * (q : ℚ) := by positivity
  apply (div_le_iff₀ hdenom).2
  simpa [mul_assoc] using hcross

theorem edgeDensity_ge_of_card_interedges_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (q : ℕ) (hq : 0 < q)
    (hA : A.card = q) (hB : B.card = q) (α : ℚ)
    (hcross : α * (q : ℚ) * (q : ℚ) ≤
      ((G.interedges A B).card : ℚ)) :
    α ≤ G.edgeDensity A B := by
  rw [G.edgeDensity_def, hA, hB]
  have hdenom : (0 : ℚ) < (q : ℚ) * (q : ℚ) := by positivity
  apply (le_div_iff₀ hdenom).2
  simpa [mul_assoc] using hcross

/-- Dense counterpart of the sparse rebalancing estimate.  Here the
cluster side `X` is enlarged to an exact half `W`, as in Claim 6.1(3).
At most `2*q*b` cleaned crossing edges can stop crossing. -/
theorem exists_balanced_dense_cut_of_cleaned
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (X Y : Finset V) (q b lower : ℕ)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hV : Fintype.card V = 2 * q)
    (hXupper : X.card ≤ q) (hXlower : q ≤ X.card + b)
    (hhigh : lower ≤ (H.interedges X Y).card) :
    ∃ W Z : Finset V,
      Disjoint W Z ∧ W ∪ Z = Finset.univ ∧
      W.card = q ∧ Z.card = q ∧
      lower ≤ (G.interedges W Z).card + 2 * q * b := by
  classical
  have hquniv : q ≤ (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, hV]
    omega
  obtain ⟨W, hXW, hWuniv, hWcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ X) hXupper hquniv
  let Z := Finset.univ \ W
  have hZcard : Z.card = q := by
    dsimp only [Z]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hV, hWcard]
    omega
  have hadded : (W \ X).card ≤ b := by
    rw [Finset.card_sdiff_of_subset hXW, hWcard]
    omega
  have hsub : H.interedges X Y ⊆
      G.interedges W Z ∪ X.product (W \ X) := by
    intro p hp
    have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
    by_cases hpW : p.2 ∈ W
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨hp'.1,
        Finset.mem_sdiff.mpr ⟨hpW, fun hpX =>
          Finset.disjoint_left.mp hXY hpX hp'.2.1⟩⟩
    · apply Finset.mem_union_left
      apply (SimpleGraph.mem_interedges_iff G).mpr
      exact ⟨hXW hp'.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpW⟩,
        hHG hp'.2.2⟩
  have hcard : (H.interedges X Y).card ≤
      (G.interedges W Z).card + X.card * (W \ X).card := by
    calc
      (H.interedges X Y).card
          ≤ (G.interedges W Z ∪ X.product (W \ X)).card :=
            Finset.card_le_card hsub
      _ ≤ (G.interedges W Z).card + (X.product (W \ X)).card :=
        Finset.card_union_le _ _
      _ = (G.interedges W Z).card + X.card * (W \ X).card := by simp
  have hXtwoq : X.card ≤ 2 * q := hXupper.trans (by omega)
  have herror : X.card * (W \ X).card ≤ 2 * q * b :=
    Nat.mul_le_mul hXtwoq hadded
  refine ⟨W, Z, Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (Finset.subset_univ W), hWcard, hZcard, ?_⟩
  omega

/-- Exact specialization of the endpoint lift to Zhao's EC2 predicate on a
Ramsey-sized host.  This theorem is the final implication on p.38 of the
paper once Claims 6.17 and 6.18 have supplied `hcross` and the displayed
constant hierarchy has supplied `hnumeric`. -/
theorem zhaoExtremalCaseTwo_of_degreeForm_reducedCut
    {n : ℕ} { ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ClusterAssignment (Fin (2 * n - 2)) ι)
    (G H : SimpleGraph (Fin (2 * n - 2))) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (α : ℚ) (hn : 2 ≤ n)
    (hHG : H ≤ G) (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (hrespect : EdgesRespectReducedGraph P H R)
    (I J : Finset ι) (m b cross : ℕ)
    (hindices : Disjoint I J) (hindices_cover : I ∪ J = Finset.univ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hXupper : (clusterUnion P I).card ≤ (n - 1) + b)
    (hXlower : n - 1 ≤ (clusterUnion P I).card + b)
    (hcross : (R.interedges I J).card ≤ cross)
    (hnumeric :
      ((cross * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss) +
          2 * (n - 1) * b : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    ZhaoExtremalCaseTwo α G := by
  classical
  have hV : Fintype.card (Fin (2 * n - 2)) = 2 * (n - 1) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨W, Z, hWZ, hcover, hWcard, hZcard, hedge⟩ :=
    exists_balanced_sparse_cut_of_degreeForm P G H R hHG loss hloss
      hrespect I J m (n - 1) b cross hindices hindices_cover hcluster
      hV hXupper hXlower hcross
  refine ⟨W, Z, ⟨hWZ, hcover, hWcard, hZcard⟩, ?_⟩
  have hedgeCast : ((G.interedges W Z).card : ℚ) ≤
      ((cross * (m * m) +
          (clusterUnion P I).card * ((exceptionalVertices P).card + loss) +
          2 * (n - 1) * b : ℕ) : ℚ) := by
    exact_mod_cast hedge
  have hedgeQ : ((G.interedges W Z).card : ℚ) ≤
      α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) :=
    hedgeCast.trans hnumeric
  have hdensity := edgeDensity_le_of_card_interedges_le
    G W Z (n - 1) (by omega) hWcard hZcard α hedgeQ
  have hdec : (inferInstance : DecidableRel G.Adj) = Classical.decRel G.Adj :=
    Subsingleton.elim _ _
  cases hdec
  exact hdensity

/-- Exact EC1 endpoint of Claim 6.1(3). -/
theorem zhaoExtremalCaseOne_of_cleaned_denseCut
    {n : ℕ}
    (G H : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (α : ℚ) (hn : 2 ≤ n) (hHG : H ≤ G)
    (X Y : Finset (Fin (2 * n - 2))) (b lower : ℕ)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hXupper : X.card ≤ n - 1) (hXlower : n - 1 ≤ X.card + b)
    (hhigh : lower ≤ (H.interedges X Y).card)
    (hnumeric : (1 - α) * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) ≤
      ((lower - 2 * (n - 1) * b : ℕ) : ℚ)) :
    ZhaoExtremalCaseOne α G := by
  classical
  have hV : Fintype.card (Fin (2 * n - 2)) = 2 * (n - 1) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨W, Z, hWZ, hWZcover, hWcard, hZcard, hedge⟩ :=
    exists_balanced_dense_cut_of_cleaned G H hHG X Y (n - 1) b lower
      hXY hcover hV hXupper hXlower hhigh
  refine ⟨W, Z, ⟨hWZ, hWZcover, hWcard, hZcard⟩, ?_⟩
  have hlower : lower - 2 * (n - 1) * b ≤ (G.interedges W Z).card := by
    omega
  have hlowerCast : ((lower - 2 * (n - 1) * b : ℕ) : ℚ) ≤
      ((G.interedges W Z).card : ℚ) := by exact_mod_cast hlower
  have hdensity := edgeDensity_ge_of_card_interedges_ge G W Z (n - 1)
    (by omega) hWcard hZcard (1 - α) (hnumeric.trans hlowerCast)
  have hdec : (inferInstance : DecidableRel G.Adj) = Classical.decRel G.Adj :=
    Subsingleton.elim _ _
  cases hdec
  exact hdensity

#print axioms clusterUnion_disjoint
#print axioms no_forestGluingCertificate_of_not_isContained
#print axioms degreeInto_le_cleaned_add_loss
#print axioms cleaned_interedges_le_reduced_slots
#print axioms original_clusterCut_interedges_le
#print axioms card_interedges_rebalance_le
#print axioms exists_balanced_sparse_cut_of_degreeForm
#print axioms zhaoExtremalCaseTwo_of_degreeForm_reducedCut
#print axioms zhaoExtremalCaseOne_of_cleaned_denseCut

end Erdos547b.ZhaoSection6Dichotomy
