import ErdosProblems.Erdos88.SwitchingRichness

/-!
# A finite Halász bound for the switching matrix

This module develops the elementary binomial and finite-fibre estimates used
to specialize KSSS Theorem 13.8 to the ternary neighbourhood-difference
matrices occurring in Section 13.
-/

open Classical
open scoped BigOperators

namespace Erdos88.Switching

/-- A uniform central-binomial estimate with an explicit absolute constant.
This is the only analytic estimate needed for the finite Bernoulli fibres. -/
lemma choose_middle_le_two_mul_two_pow_div_sqrt :
    ∀ k : ℕ, 1 ≤ k →
      (Nat.choose k (k / 2) : ℝ) ≤
        2 * ((2 : ℝ) ^ k / Real.sqrt k) := by
  have hEven : ∀ m : ℕ,
      (Nat.choose (2 * m) m : ℝ) ≤
        (4 : ℝ) ^ m / Real.sqrt (3 * m + 1) := by
    intro m
    have hsq : (Nat.choose (2 * m) m : ℝ) ^ 2 ≤
        (4 : ℝ) ^ (2 * m) / (3 * m + 1) := by
      field_simp
      induction m with
      | zero =>
          norm_num [Nat.cast_succ, Nat.mul_succ, pow_succ', pow_mul'] at *
      | succ m ih =>
          norm_num [Nat.cast_succ, Nat.mul_succ, pow_succ', pow_mul'] at *
          have hsucc :
              (Nat.choose (2 * m + 2) (m + 1) : ℝ) =
                (Nat.choose (2 * m) m : ℝ) * (2 * m + 1) * 2 / (m + 1) := by
            rw [Nat.cast_choose, Nat.cast_choose] <;> try linarith
            norm_num [two_mul, add_assoc, Nat.factorial]
            ring_nf
            rw [show 2 + m * 2 - (1 + m) = m + 1 by
              rw [Nat.sub_eq_of_eq_add]
              ring]
            norm_num [Nat.factorial_succ]
            ring_nf
            field_simp
            ring
          rw [hsucc, div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀] <;>
            ring_nf at * <;> try positivity
          nlinarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 3]
    convert Real.le_sqrt_of_sq_le hsq using 1
    rw [Real.sqrt_div]
    · rw [show 2 * m = m * 2 by ring, pow_mul,
        Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity
    · positivity
  intro k hk
  rcases Nat.even_or_odd' k with ⟨c, rfl | rfl⟩ <;> norm_num at *
  · refine (hEven c).trans ?_
    ring_nf
    norm_num [pow_mul']
    field_simp
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))]
    nlinarith [
      Real.sqrt_nonneg 2,
      Real.sqrt_nonneg (1 + c * 3),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + (c : ℝ) * 3 by positivity),
      Real.sqrt_nonneg c,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ (c : ℝ) by positivity)]
  · have h := hEven (c + 1)
    norm_num [Nat.add_div, Nat.mul_succ, pow_succ', pow_mul] at *
    rw [show (2 * c + 2 : ℕ) = 2 * c + 1 + 1 by ring,
      Nat.choose_succ_succ] at h
    ring_nf at *
    norm_num at *
    refine (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (h.trans ?_)
    have hsqrt : Real.sqrt (1 + (c : ℝ) * 2) ≤
        Real.sqrt (4 + (c : ℝ) * 3) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hinv : (Real.sqrt (4 + (c : ℝ) * 3))⁻¹ ≤
        (Real.sqrt (1 + (c : ℝ) * 2))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hsqrt
    nlinarith [mul_le_mul_of_nonneg_right hinv
      (by positivity : 0 ≤ (4 : ℝ) ^ c * 4)]

/-- Every binomial coefficient satisfies the same square-root bound. -/
lemma choose_le_two_mul_two_pow_div_sqrt (k j : ℕ) (hk : 1 ≤ k) :
    (Nat.choose k j : ℝ) ≤
      2 * ((2 : ℝ) ^ k / Real.sqrt k) := by
  have hmiddle : (Nat.choose k j : ℝ) ≤
      (Nat.choose k (k / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle j k
  exact hmiddle.trans (choose_middle_le_two_mul_two_pow_div_sqrt k hk)

section FiniteFibers

variable {V R : Type*} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R]

/-- A matrix of rank at least `r` contains `r` linearly independent actual
columns. -/
lemma exists_linearIndependent_columns {I J : Type*}
    [Fintype I] [Fintype J] (A : Matrix I J ℝ) (r : ℕ)
    (hrank : r ≤ A.rank) :
    ∃ e : Fin r → J, LinearIndependent ℝ (fun i ↦ A.col (e i)) := by
  classical
  let cols : Set (I → ℝ) := Set.range A.col
  obtain ⟨T, hTsub, hTcard, _hTspan, hTind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ cols
  have hTcardRank : T.card = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    simpa only [cols] using hTcard
  have hrT : r ≤ T.card := by rw [hTcardRank]; exact hrank
  obtain ⟨T₀, hT₀T, hT₀card⟩ :=
    Finset.exists_subset_card_eq hrT
  choose idx hidx using fun x : T₀ ↦ hTsub (hT₀T x.2)
  let eT : Fin r ≃ T₀ := (Finset.equivFinOfCardEq hT₀card).symm
  let e : Fin r → J := fun i ↦ idx (eT i)
  have hT₀ind : LinearIndependent ℝ (fun x : T₀ ↦ x.1) := by
    exact hTind.mono (by
      intro x hx
      exact hT₀T hx)
  have hselected := hT₀ind.comp eT eT.injective
  refine ⟨e, ?_⟩
  have heq : (fun i ↦ A.col (e i)) = fun i ↦ (eT i).1 := by
    funext i
    exact hidx (eT i)
  rw [heq]
  simpa only [Function.comp_def] using hselected

/-- Matrix multiplication by a subset indicator is the sum of the selected
columns. -/
lemma mulVec_finsetIndicator_eq_sum_cols {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (U : Finset V) :
    A.mulVec (finsetIndicator U) = ∑ w ∈ U, A.col w := by
  funext i
  simp [Matrix.mulVec_apply, dotProduct, finsetIndicator, Matrix.col_apply]

/-- Removing coordinates whose matrix columns vanish does not change the
matrix sum. -/
lemma mulVec_finsetIndicator_sdiff_of_cols_zero {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (N U : Finset V)
    (hzero : ∀ w ∈ N, A.col w = 0) :
    A.mulVec (finsetIndicator (U \ N)) =
      A.mulVec (finsetIndicator U) := by
  rw [mulVec_finsetIndicator_eq_sum_cols,
    mulVec_finsetIndicator_eq_sum_cols]
  apply Finset.sum_subset (Finset.sdiff_subset)
  intro w hwU hwNot
  have hwN : w ∈ N := by
    by_contra hwN
    exact hwNot (Finset.mem_sdiff.mpr ⟨hwU, hwN⟩)
  rw [hzero w hwN]

/-- Regroup a selected column sum into its part outside the blocks and the
cardinality-weighted block patterns. -/
lemma sum_cols_eq_outside_add_blockCounts {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (U : Finset V) :
    (∑ w ∈ U, A.col w) =
      (∑ w ∈ U \ Finset.univ.biUnion blocks, A.col w) +
        ∑ r, ((U ∩ blocks r).card : ℝ) • patterns r := by
  classical
  let W := Finset.univ.biUnion blocks
  have hpartition : (U \ W) ∪ (U ∩ W) = U := by
    ext w
    by_cases hw : w ∈ W <;> simp [hw]
  have houtDisjoint : Disjoint (U \ W) (U ∩ W) := by
    exact Finset.disjoint_left.mpr fun w hwout hwin ↦
      (Finset.mem_sdiff.mp hwout).2 (Finset.mem_inter.mp hwin).2
  have hinter : Finset.univ.biUnion (fun r ↦ U ∩ blocks r) = U ∩ W := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, W]
    aesop
  have hblockDisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset R) : Set R) (fun r ↦ U ∩ blocks r) := by
    intro i _hi j _hj hij
    exact Finset.disjoint_left.mpr fun w hwi hwj ↦
      (Finset.disjoint_left.mp (hdisjoint (Set.mem_univ i)
        (Set.mem_univ j) hij))
          (Finset.mem_inter.mp hwi).2 (Finset.mem_inter.mp hwj).2
  have hinside : (∑ w ∈ U ∩ W, A.col w) =
      ∑ r, ((U ∩ blocks r).card : ℝ) • patterns r := by
    rw [← hinter, Finset.sum_biUnion hblockDisjoint]
    apply Finset.sum_congr rfl
    intro r _hr
    calc
      (∑ w ∈ U ∩ blocks r, A.col w) =
          ∑ _w ∈ U ∩ blocks r, patterns r := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hcols r w (Finset.mem_inter.mp hw).2
      _ = ((U ∩ blocks r).card : ℝ) • patterns r := by
        funext i
        simp
  calc
    (∑ w ∈ U, A.col w) =
        ∑ w ∈ (U \ W) ∪ (U ∩ W), A.col w := by rw [hpartition]
    _ = (∑ w ∈ U \ W, A.col w) +
        ∑ w ∈ U ∩ W, A.col w := Finset.sum_union houtDisjoint
    _ = (∑ w ∈ U \ Finset.univ.biUnion blocks, A.col w) +
        ∑ r, ((U ∩ blocks r).card : ℝ) • patterns r := by
      simpa only [W, hinside]

/-- The private-neighbour blocks diagonalize the switching equations: after
the outside assignment is fixed, the `j`th equation changes exactly by the
number of selected vertices in the `j`th private block. -/
lemma switchingDifferenceMatrix_mulVec_private_decompose
    {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ U : Finset V)
    (hp : PairEndpointsDistinct p) (j : I) :
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) j =
      (switchingDifferenceMatrix G p).mulVec
          (finsetIndicator
            (U \ Finset.univ.biUnion
              (fun i ↦ switchingPrivateNeighbors G p i S₀))) j +
        ((U ∩ switchingPrivateNeighbors G p j S₀).card : ℝ) := by
  let A := switchingDifferenceMatrix G p
  let blocks := fun i : I ↦ switchingPrivateNeighbors G p i S₀
  let patterns := fun i j : I ↦ if j = i then (1 : ℝ) else 0
  have hdisj : Set.PairwiseDisjoint Set.univ blocks := by
    intro i _hi j _hj hij
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp hij
  have hcols : ∀ i w, w ∈ blocks i → A.col w = patterns i := by
    intro i w hw
    funext j
    exact switchingDifferenceMatrix_apply_of_mem_private G p i j S₀ hw
  have hdec := sum_cols_eq_outside_add_blockCounts
    A blocks patterns hdisj hcols U
  rw [← mulVec_finsetIndicator_eq_sum_cols,
    ← mulVec_finsetIndicator_eq_sum_cols] at hdec
  have hj := congrFun hdec j
  simp only [A, blocks, patterns, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at hj
  have hsum :
      (∑ x : I, if j = x then
          ((U ∩ switchingPrivateNeighbors G p x S₀).card : ℝ) else 0) =
        ((U ∩ switchingPrivateNeighbors G p j S₀).card : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hbj
      simp [Ne.symm hbj]
    · simp
  rw [hsum] at hj
  exact hj

/-- On linearly independent constant-column blocks, the matrix sum together
with the outside part uniquely determines every block cardinality. -/
lemma blockCards_eq_of_mulVec_eq {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (hLI : LinearIndependent ℝ patterns)
    {U Z : Finset V}
    (houtside : U \ Finset.univ.biUnion blocks =
      Z \ Finset.univ.biUnion blocks)
    (hmul : A.mulVec (finsetIndicator U) =
      A.mulVec (finsetIndicator Z)) :
    ∀ r, (U ∩ blocks r).card = (Z ∩ blocks r).card := by
  have hcolsEq : (∑ w ∈ U, A.col w) = ∑ w ∈ Z, A.col w := by
    rw [← mulVec_finsetIndicator_eq_sum_cols,
      ← mulVec_finsetIndicator_eq_sum_cols, hmul]
  have hdecU :=
    sum_cols_eq_outside_add_blockCounts A blocks patterns hdisjoint hcols U
  have hdecZ :=
    sum_cols_eq_outside_add_blockCounts A blocks patterns hdisjoint hcols Z
  have hfull := hdecU.symm.trans (hcolsEq.trans hdecZ)
  rw [houtside] at hfull
  have hcomb : (∑ r, ((U ∩ blocks r).card : ℝ) • patterns r) =
      ∑ r, ((Z ∩ blocks r).card : ℝ) • patterns r :=
    add_left_cancel hfull
  let coeff : R → ℝ := fun r ↦
    ((U ∩ blocks r).card : ℝ) - ((Z ∩ blocks r).card : ℝ)
  have hzero : ∑ r, coeff r • patterns r = 0 := by
    simp only [coeff, sub_smul, Finset.sum_sub_distrib, hcomb, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp hLI coeff hzero
  intro r
  have hr := hcoeff r
  simp only [coeff] at hr
  have hcast : ((U ∩ blocks r).card : ℝ) =
      ((Z ∩ blocks r).card : ℝ) := sub_eq_zero.mp hr
  exact_mod_cast hcast

/-- Fixing a subset outside a family of blocks and fixing its cardinality in
each block leaves at most the product of the corresponding binomial
coefficients.  Disjointness is not needed for this purely fibrewise bound. -/
lemma card_subsets_with_outside_and_blockCards_le
    (blocks : R → Finset V) (outside : Finset V) (counts : R → ℕ) :
    ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = outside ∧
          ∀ i, (U ∩ blocks i).card = counts i).card ≤
      ∏ i, Nat.choose (blocks i).card (counts i) := by
  classical
  let source := (Finset.univ : Finset (Finset V)).filter fun U ↦
    U \ Finset.univ.biUnion blocks = outside ∧
      ∀ i, (U ∩ blocks i).card = counts i
  let target := Fintype.piFinset fun i : R ↦
    (blocks i).powersetCard (counts i)
  have hmaps : Set.MapsTo (fun U i ↦ U ∩ blocks i)
      (source : Set (Finset V)) (target : Set (R → Finset V)) := by
    intro U hU
    have hU' := (Finset.mem_filter.mp hU).2
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hU'.2 i⟩
  have hinj : Set.InjOn (fun U i ↦ U ∩ blocks i)
      (source : Set (Finset V)) := by
    intro U hU Z hZ hUZ
    have hU' := (Finset.mem_filter.mp hU).2
    have hZ' := (Finset.mem_filter.mp hZ).2
    ext x
    by_cases hx : x ∈ Finset.univ.biUnion blocks
    · obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
      have hi := congrFun hUZ i
      have hmem := Finset.ext_iff.mp hi x
      simpa only [Finset.mem_inter, hxi, and_true] using hmem
    · have hout : U \ Finset.univ.biUnion blocks =
          Z \ Finset.univ.biUnion blocks := hU'.1.trans hZ'.1.symm
      have hmem := Finset.ext_iff.mp hout x
      simpa [hx] using hmem
  calc
    ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = outside ∧
          ∀ i, (U ∩ blocks i).card = counts i).card = source.card := rfl
    _ ≤ target.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ∏ i, Nat.choose (blocks i).card (counts i) := by
      simp only [target, Fintype.card_piFinset, Finset.card_powersetCard]

/-- For pairwise-disjoint blocks, every independent choice of the prescribed
number of elements in each block gives a distinct subset.  Fixing a disjoint
outside part therefore leaves at least the product of the corresponding
binomial coefficients. -/
lemma prod_choose_le_card_subsets_with_outside_and_blockCards
    (blocks : R → Finset V) (outside : Finset V) (counts : R → ℕ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (houtside : Disjoint outside (Finset.univ.biUnion blocks)) :
    (∏ i, Nat.choose (blocks i).card (counts i)) ≤
      ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = outside ∧
          ∀ i, (U ∩ blocks i).card = counts i).card := by
  classical
  let W := Finset.univ.biUnion blocks
  let source := (Finset.univ : Finset (Finset V)).filter fun U ↦
    U \ W = outside ∧ ∀ i, (U ∩ blocks i).card = counts i
  let target := Fintype.piFinset fun i : R ↦
    (blocks i).powersetCard (counts i)
  let assemble : (R → Finset V) → Finset V := fun f ↦
    outside ∪ Finset.univ.biUnion f
  have hchoiceSub : ∀ f ∈ target, ∀ i, f i ⊆ blocks i := by
    intro f hf i
    exact (Finset.mem_powersetCard.mp
      (Fintype.mem_piFinset.mp hf i)).1
  have hchoiceCard : ∀ f ∈ target, ∀ i, (f i).card = counts i := by
    intro f hf i
    exact (Finset.mem_powersetCard.mp
      (Fintype.mem_piFinset.mp hf i)).2
  have hchoiceUnionSub : ∀ f ∈ target,
      Finset.univ.biUnion f ⊆ W := by
    intro f hf x hx
    obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, hchoiceSub f hf i hxi⟩
  have houtsideRecover : ∀ f ∈ target, assemble f \ W = outside := by
    intro f hf
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx'.1 with hxout | hxchoice
      · exact hxout
      · exact False.elim (hx'.2 (hchoiceUnionSub f hf hxchoice))
    · intro hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx,
        fun hxW ↦ Finset.disjoint_left.mp houtside hx hxW⟩
  have hrecover : ∀ f ∈ target, ∀ i, assemble f ∩ blocks i = f i := by
    intro f hf i
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hx'.1 with hxout | hxchoice
      · have hxW : x ∈ W := Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, hx'.2⟩
        exact False.elim (Finset.disjoint_left.mp houtside hxout hxW)
      · obtain ⟨j, _hj, hxj⟩ := Finset.mem_biUnion.mp hxchoice
        by_cases hji : j = i
        · simpa only [hji] using hxj
        · have hblocks := hdisjoint (Set.mem_univ j) (Set.mem_univ i) hji
          exact False.elim (Finset.disjoint_left.mp hblocks
            (hchoiceSub f hf j hxj) hx'.2)
    · intro hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ i, hx⟩),
          hchoiceSub f hf i hx⟩
  have hmaps : Set.MapsTo assemble
      (target : Set (R → Finset V)) (source : Set (Finset V)) := by
    intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, houtsideRecover f hf, ?_⟩
    intro i
    rw [hrecover f hf i]
    exact hchoiceCard f hf i
  have hinj : Set.InjOn assemble (target : Set (R → Finset V)) := by
    intro f hf g hg hfg
    funext i
    calc
      f i = assemble f ∩ blocks i := (hrecover f hf i).symm
      _ = assemble g ∩ blocks i := congrArg (fun U ↦ U ∩ blocks i) hfg
      _ = g i := hrecover g hg i
  calc
    (∏ i, Nat.choose (blocks i).card (counts i)) = target.card := by
      simp only [target, Fintype.card_piFinset, Finset.card_powersetCard]
    _ ≤ source.card := Finset.card_le_card_of_injOn assemble hmaps hinj
    _ = ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = outside ∧
          ∀ i, (U ∩ blocks i).card = counts i).card := rfl

/-- Exact fibre cardinality for pairwise-disjoint blocks and a fixed
outside assignment. -/
lemma card_subsets_with_outside_and_blockCards_eq
    (blocks : R → Finset V) (outside : Finset V) (counts : R → ℕ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (houtside : Disjoint outside (Finset.univ.biUnion blocks)) :
    ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = outside ∧
          ∀ i, (U ∩ blocks i).card = counts i).card =
      ∏ i, Nat.choose (blocks i).card (counts i) := by
  apply Nat.le_antisymm
  · exact card_subsets_with_outside_and_blockCards_le blocks outside counts
  · exact prod_choose_le_card_subsets_with_outside_and_blockCards
      blocks outside counts hdisjoint houtside

/-- Dependent prescribed counts: the desired count in each disjoint block
may depend on the outside assignment.  Summing the exact binomial fibre
sizes gives a lower bound for the resulting family of subsets. -/
lemma sum_prod_choose_le_card_dependent_blockCounts
    (blocks : R → Finset V) (outsides : Finset (Finset V))
    (counts : Finset V → R → ℕ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (houtside : ∀ O ∈ outsides,
      Disjoint O (Finset.univ.biUnion blocks)) :
    (∑ O ∈ outsides, ∏ i, Nat.choose (blocks i).card (counts O i)) ≤
      ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks ∈ outsides ∧
          ∀ i, (U ∩ blocks i).card =
            counts (U \ Finset.univ.biUnion blocks) i).card := by
  let event := (Finset.univ : Finset (Finset V)).filter fun U ↦
    U \ Finset.univ.biUnion blocks ∈ outsides ∧
      ∀ i, (U ∩ blocks i).card =
        counts (U \ Finset.univ.biUnion blocks) i
  have hmaps : Set.MapsTo
      (fun U : Finset V ↦ U \ Finset.univ.biUnion blocks)
      (event : Set (Finset V)) (outsides : Set (Finset V)) := by
    intro U hU
    exact (Finset.mem_filter.mp hU).2.1
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := event) (t := outsides)
    (f := fun U : Finset V ↦ U \ Finset.univ.biUnion blocks) hmaps
  rw [show ((Finset.univ : Finset (Finset V)).filter fun U ↦
      U \ Finset.univ.biUnion blocks ∈ outsides ∧
        ∀ i, (U ∩ blocks i).card =
          counts (U \ Finset.univ.biUnion blocks) i) = event by rfl]
  rw [hcard]
  apply Finset.sum_le_sum
  intro O hO
  have hfiber :
      event.filter (fun U ↦ U \ Finset.univ.biUnion blocks = O) =
        (Finset.univ : Finset (Finset V)).filter fun U ↦
          U \ Finset.univ.biUnion blocks = O ∧
            ∀ i, (U ∩ blocks i).card = counts O i := by
    ext U
    simp only [event, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨h.2, fun i ↦ by simpa only [h.2] using h.1.2 i⟩
    · intro h
      exact ⟨⟨by simpa only [h.1] using hO, fun i ↦ by
        simpa only [h.1] using h.2 i⟩, h.1⟩
  rw [hfiber, card_subsets_with_outside_and_blockCards_eq
    blocks O (counts O) hdisjoint (houtside O hO)]

/-- Exact fibre decomposition for dependent prescribed block counts, with an
additional predicate on the assembled subset.  This is the counting form
needed when only a positive fraction of each private-block fibre satisfies a
conditional-mean window. -/
lemma sum_card_dependent_blockGoodFibers_eq
    (blocks : R → Finset V) (outsides : Finset (Finset V))
    (counts : Finset V → R → ℕ) (good : Finset V → Prop) :
    (∑ O ∈ outsides,
      ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks = O ∧
          (∀ i, (U ∩ blocks i).card = counts O i) ∧ good U).card) =
      ((Finset.univ : Finset (Finset V)).filter fun U ↦
        U \ Finset.univ.biUnion blocks ∈ outsides ∧
          (∀ i, (U ∩ blocks i).card =
            counts (U \ Finset.univ.biUnion blocks) i) ∧ good U).card := by
  let event := (Finset.univ : Finset (Finset V)).filter fun U ↦
    U \ Finset.univ.biUnion blocks ∈ outsides ∧
      (∀ i, (U ∩ blocks i).card =
        counts (U \ Finset.univ.biUnion blocks) i) ∧ good U
  have hmaps : Set.MapsTo
      (fun U : Finset V ↦ U \ Finset.univ.biUnion blocks)
      (event : Set (Finset V)) (outsides : Set (Finset V)) := by
    intro U hU
    exact (Finset.mem_filter.mp hU).2.1
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := event) (t := outsides)
    (f := fun U : Finset V ↦ U \ Finset.univ.biUnion blocks) hmaps
  rw [show ((Finset.univ : Finset (Finset V)).filter fun U ↦
      U \ Finset.univ.biUnion blocks ∈ outsides ∧
        (∀ i, (U ∩ blocks i).card =
          counts (U \ Finset.univ.biUnion blocks) i) ∧ good U) = event by rfl]
  rw [hcard]
  apply Finset.sum_congr rfl
  intro O hO
  congr 1
  ext U
  simp only [event, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hEq, hCount, hGood⟩
    refine ⟨⟨?_, ?_, hGood⟩, hEq⟩
    · simpa only [hEq] using hO
    · intro i
      simpa only [hEq] using hCount i
  · rintro ⟨⟨_hOut, hCount, hGood⟩, hEq⟩
    refine ⟨hEq, ?_, hGood⟩
    intro i
    simpa only [hEq] using hCount i

/-- A fibre of the Bernoulli matrix sum is bounded by the number of outside
subsets times one central binomial coefficient for each independent constant
column block. -/
lemma card_mulVec_fiber_le {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (hLI : LinearIndependent ℝ patterns) (targetValue : I → ℝ) :
    ((Finset.univ : Finset (Finset V)).filter fun U ↦
        A.mulVec (finsetIndicator U) = targetValue).card ≤
      2 ^ (Fintype.card V - ∑ r, (blocks r).card) *
        ∏ r, Nat.choose (blocks r).card ((blocks r).card / 2) := by
  classical
  let W := Finset.univ.biUnion blocks
  let event := (Finset.univ : Finset (Finset V)).filter fun U ↦
    A.mulVec (finsetIndicator U) = targetValue
  let outsides := (Finset.univ \ W).powerset
  let central : ℕ := ∏ r, Nat.choose (blocks r).card ((blocks r).card / 2)
  have hmaps : ∀ U ∈ event, U \ W ∈ outsides := by
    intro U _hU
    exact Finset.mem_powerset.mpr fun w hw ↦
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hw).2⟩
  have hfiber : ∀ O ∈ outsides,
      (event.filter fun U ↦ U \ W = O).card ≤ central := by
    intro O hO
    by_cases hempty : (event.filter fun U ↦ U \ W = O) = ∅
    · simp [hempty]
    · obtain ⟨Z, hZ⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hZevent := (Finset.mem_filter.mp hZ).1
      have hZout := (Finset.mem_filter.mp hZ).2
      let counts : R → ℕ := fun r ↦ (Z ∩ blocks r).card
      have hsub : (event.filter fun U ↦ U \ W = O) ⊆
          (Finset.univ : Finset (Finset V)).filter fun U ↦
            U \ Finset.univ.biUnion blocks = O ∧
              ∀ r, (U ∩ blocks r).card = counts r := by
        intro U hU
        have hUevent := (Finset.mem_filter.mp hU).1
        have hUout := (Finset.mem_filter.mp hU).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ U, ?_, ?_⟩
        · simpa only [W] using hUout
        · have hout : U \ Finset.univ.biUnion blocks =
              Z \ Finset.univ.biUnion blocks := by
            simpa only [W, hUout, hZout]
          have hmul : A.mulVec (finsetIndicator U) =
              A.mulVec (finsetIndicator Z) := by
            exact (Finset.mem_filter.mp hUevent).2.trans
              (Finset.mem_filter.mp hZevent).2.symm
          exact blockCards_eq_of_mulVec_eq A blocks patterns hdisjoint
            hcols hLI hout hmul
      calc
        (event.filter fun U ↦ U \ W = O).card ≤
            ((Finset.univ : Finset (Finset V)).filter fun U ↦
              U \ Finset.univ.biUnion blocks = O ∧
                ∀ r, (U ∩ blocks r).card = counts r).card :=
          Finset.card_le_card hsub
        _ ≤ ∏ r, Nat.choose (blocks r).card (counts r) :=
          card_subsets_with_outside_and_blockCards_le blocks O counts
        _ ≤ central := by
          apply Finset.prod_le_prod
          · intro r _hr
            exact Nat.zero_le _
          · intro r _hr
            exact Nat.choose_le_middle _ _
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := event) (t := outsides) (f := fun U ↦ U \ W) hmaps
  have hsum : event.card ≤ outsides.card * central := by
    rw [hcard]
    calc
      (∑ O ∈ outsides, (event.filter fun U ↦ U \ W = O).card) ≤
          ∑ _O ∈ outsides, central :=
        Finset.sum_le_sum fun O hO ↦ hfiber O hO
      _ = outsides.card * central := by simp
  have hWcard : W.card = ∑ r, (blocks r).card := by
    exact Finset.card_biUnion (by simpa only [Finset.coe_univ] using hdisjoint)
  have houtcard : outsides.card =
      2 ^ (Fintype.card V - ∑ r, (blocks r).card) := by
    rw [show outsides.card = 2 ^ (Finset.univ \ W).card by
      simp only [outsides, Finset.card_powerset]]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ W),
      Finset.card_univ, hWcard]
  simpa only [event, central, houtcard] using hsum

/-- The same fibre bound when Bernoulli subsets are restricted to a fixed
ambient vertex set. -/
lemma card_mulVec_fiber_on_ambient_le {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (ambient : Finset V)
    (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hblockSub : ∀ r, blocks r ⊆ ambient)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (hLI : LinearIndependent ℝ patterns) (targetValue : I → ℝ) :
    (ambient.powerset.filter fun U ↦
        A.mulVec (finsetIndicator U) = targetValue).card ≤
      2 ^ (ambient.card - ∑ r, (blocks r).card) *
        ∏ r, Nat.choose (blocks r).card ((blocks r).card / 2) := by
  classical
  let W := Finset.univ.biUnion blocks
  let event := ambient.powerset.filter fun U ↦
    A.mulVec (finsetIndicator U) = targetValue
  let outsides := (ambient \ W).powerset
  let central : ℕ := ∏ r, Nat.choose (blocks r).card ((blocks r).card / 2)
  have hmaps : ∀ U ∈ event, U \ W ∈ outsides := by
    intro U hU
    have hUAmbient := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    exact Finset.mem_powerset.mpr fun w hw ↦
      Finset.mem_sdiff.mpr ⟨hUAmbient (Finset.mem_sdiff.mp hw).1,
        (Finset.mem_sdiff.mp hw).2⟩
  have hfiber : ∀ O ∈ outsides,
      (event.filter fun U ↦ U \ W = O).card ≤ central := by
    intro O hO
    by_cases hempty : (event.filter fun U ↦ U \ W = O) = ∅
    · simp [hempty]
    · obtain ⟨Z, hZ⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hZevent := (Finset.mem_filter.mp hZ).1
      have hZout := (Finset.mem_filter.mp hZ).2
      let counts : R → ℕ := fun r ↦ (Z ∩ blocks r).card
      have hsub : (event.filter fun U ↦ U \ W = O) ⊆
          (Finset.univ : Finset (Finset V)).filter fun U ↦
            U \ Finset.univ.biUnion blocks = O ∧
              ∀ r, (U ∩ blocks r).card = counts r := by
        intro U hU
        have hUevent := (Finset.mem_filter.mp hU).1
        have hUout := (Finset.mem_filter.mp hU).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ U, ?_, ?_⟩
        · simpa only [W] using hUout
        · have hout : U \ Finset.univ.biUnion blocks =
              Z \ Finset.univ.biUnion blocks := by
            simpa only [W, hUout, hZout]
          have hmul : A.mulVec (finsetIndicator U) =
              A.mulVec (finsetIndicator Z) := by
            exact (Finset.mem_filter.mp hUevent).2.trans
              (Finset.mem_filter.mp hZevent).2.symm
          exact blockCards_eq_of_mulVec_eq A blocks patterns hdisjoint
            hcols hLI hout hmul
      calc
        (event.filter fun U ↦ U \ W = O).card ≤
            ((Finset.univ : Finset (Finset V)).filter fun U ↦
              U \ Finset.univ.biUnion blocks = O ∧
                ∀ r, (U ∩ blocks r).card = counts r).card :=
          Finset.card_le_card hsub
        _ ≤ ∏ r, Nat.choose (blocks r).card (counts r) :=
          card_subsets_with_outside_and_blockCards_le blocks O counts
        _ ≤ central := by
          apply Finset.prod_le_prod
          · intro r _hr
            exact Nat.zero_le _
          · intro r _hr
            exact Nat.choose_le_middle _ _
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := event) (t := outsides) (f := fun U ↦ U \ W) hmaps
  have hsum : event.card ≤ outsides.card * central := by
    rw [hcard]
    calc
      (∑ O ∈ outsides, (event.filter fun U ↦ U \ W = O).card) ≤
          ∑ _O ∈ outsides, central :=
        Finset.sum_le_sum fun O hO ↦ hfiber O hO
      _ = outsides.card * central := by simp
  have hWcard : W.card = ∑ r, (blocks r).card := by
    exact Finset.card_biUnion (by simpa only [Finset.coe_univ] using hdisjoint)
  have hWsub : W ⊆ ambient := by
    intro w hw
    obtain ⟨r, _hr, hwr⟩ := Finset.mem_biUnion.mp hw
    exact hblockSub r hwr
  have houtcard : outsides.card =
      2 ^ (ambient.card - ∑ r, (blocks r).card) := by
    rw [show outsides.card = 2 ^ (ambient \ W).card by
      simp only [outsides, Finset.card_powerset]]
    rw [Finset.card_sdiff_of_subset hWsub, hWcard]
  simpa only [event, central, houtcard] using hsum

/-- Real-normalized ambient-set form. -/
lemma card_mulVec_fiber_on_ambient_real_le {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (ambient : Finset V)
    (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hblockSub : ∀ r, blocks r ⊆ ambient)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (hLI : LinearIndependent ℝ patterns) (m : ℕ) (hm : 1 ≤ m)
    (hcard : ∀ r, (blocks r).card = m) (targetValue : I → ℝ) :
    ((ambient.powerset.filter fun U ↦
        A.mulVec (finsetIndicator U) = targetValue).card : ℝ) ≤
      (2 : ℝ) ^ ambient.card *
        (2 : ℝ) ^ Fintype.card R / Real.sqrt m ^ Fintype.card R := by
  let event := ambient.powerset.filter fun U ↦
    A.mulVec (finsetIndicator U) = targetValue
  have hfinite := card_mulVec_fiber_on_ambient_le A ambient blocks patterns
    hblockSub hdisjoint hcols hLI targetValue
  have hsum : ∑ r, (blocks r).card = Fintype.card R * m := by
    simp_rw [hcard]
    simp
  have hcentralNat :
      (∏ r, Nat.choose (blocks r).card ((blocks r).card / 2)) =
        (Nat.choose m (m / 2)) ^ Fintype.card R := by
    simp_rw [hcard]
    simp
  have hfiniteReal : (event.card : ℝ) ≤
      (2 : ℝ) ^ (ambient.card - Fintype.card R * m) *
        (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R := by
    exact_mod_cast (by simpa only [event, hsum, hcentralNat] using hfinite)
  have hbinom := choose_middle_le_two_mul_two_pow_div_sqrt m hm
  have hcentralReal : (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R ≤
      (2 * ((2 : ℝ) ^ m / Real.sqrt m)) ^ Fintype.card R :=
    pow_le_pow_left₀ (by positivity) hbinom _
  have hWcard : (Finset.univ.biUnion blocks).card =
      Fintype.card R * m := by
    calc
      (Finset.univ.biUnion blocks).card = ∑ r, (blocks r).card :=
        Finset.card_biUnion (by simpa only [Finset.coe_univ] using hdisjoint)
      _ = Fintype.card R * m := hsum
  have hWsub : Finset.univ.biUnion blocks ⊆ ambient := by
    intro w hw
    obtain ⟨r, _hr, hwr⟩ := Finset.mem_biUnion.mp hw
    exact hblockSub r hwr
  have hroom : Fintype.card R * m ≤ ambient.card := by
    rw [← hWcard]
    exact Finset.card_le_card hWsub
  have htwo :
      (2 : ℝ) ^ (ambient.card - Fintype.card R * m) *
          ((2 : ℝ) ^ m) ^ Fintype.card R =
        (2 : ℝ) ^ ambient.card := by
    rw [← pow_mul, ← pow_add]
    rw [Nat.mul_comm m (Fintype.card R), Nat.sub_add_cancel hroom]
  calc
    (event.card : ℝ) ≤
        (2 : ℝ) ^ (ambient.card - Fintype.card R * m) *
          (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R := hfiniteReal
    _ ≤ (2 : ℝ) ^ (ambient.card - Fintype.card R * m) *
          (2 * ((2 : ℝ) ^ m / Real.sqrt m)) ^ Fintype.card R := by
      exact mul_le_mul_of_nonneg_left hcentralReal (by positivity)
    _ = (2 : ℝ) ^ ambient.card *
          (2 : ℝ) ^ Fintype.card R / Real.sqrt m ^ Fintype.card R := by
      rw [mul_pow, div_pow, div_eq_mul_inv]
      rw [div_eq_mul_inv]
      rw [← htwo]
      ring

/-- Conditional exposure: if every assignment outside a zero-column set has
at most `windowBound` extensions satisfying a window event, then imposing the
matrix equation costs only the number of admissible outside assignments. -/
lemma card_matrixFiber_and_window_le_of_conditional
    {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (N : Finset V) (targetValue : I → ℝ)
    (window : Finset V → Prop) [DecidablePred window]
    (windowBound : ℝ)
    (hzero : ∀ w ∈ N, A.col w = 0)
    (hwindow : ∀ O ∈ ((Finset.univ : Finset V) \ N).powerset,
      (((N.powerset.filter fun R ↦ window (O ∪ R)).card : ℝ) ≤ windowBound)) :
    (((Finset.univ : Finset (Finset V)).filter fun U ↦
        A.mulVec (finsetIndicator U) = targetValue ∧ window U).card : ℝ) ≤
      ((((Finset.univ : Finset V) \ N).powerset.filter fun O ↦
          A.mulVec (finsetIndicator O) = targetValue).card : ℝ) *
        windowBound := by
  classical
  let ambient := (Finset.univ : Finset V) \ N
  let outsideEvent := ambient.powerset.filter fun O ↦
    A.mulVec (finsetIndicator O) = targetValue
  let fullEvent := (Finset.univ : Finset (Finset V)).filter fun U ↦
    A.mulVec (finsetIndicator U) = targetValue ∧ window U
  have hmaps : ∀ U ∈ fullEvent, U \ N ∈ outsideEvent := by
    intro U hU
    have hU' := (Finset.mem_filter.mp hU).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro w hw
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hw).2⟩
    · rw [mulVec_finsetIndicator_sdiff_of_cols_zero A N U hzero]
      exact hU'.1
  have hfiber : ∀ O ∈ outsideEvent,
      ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) ≤ windowBound := by
    intro O hO
    let target := N.powerset.filter fun R ↦ window (O ∪ R)
    have hfiberMaps : Set.MapsTo (fun U ↦ U ∩ N)
        (↑(fullEvent.filter fun U ↦ U \ N = O) : Set (Finset V))
        (target : Set (Finset V)) := by
      intro U hU
      have hUevent := (Finset.mem_filter.mp hU).1
      have hUout := (Finset.mem_filter.mp hU).2
      have hwindowU := (Finset.mem_filter.mp hUevent).2.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      have hpartition : (U \ N) ∪ (U ∩ N) = U := by
        ext w
        by_cases hw : w ∈ N <;> simp [hw]
      simpa only [← hUout, hpartition] using hwindowU
    have hfiberInj : Set.InjOn (fun U ↦ U ∩ N)
        (↑(fullEvent.filter fun U ↦ U \ N = O) : Set (Finset V)) := by
      intro U hU Z hZ hinter
      have hUout := (Finset.mem_filter.mp hU).2
      have hZout := (Finset.mem_filter.mp hZ).2
      ext w
      by_cases hw : w ∈ N
      · have hmem := Finset.ext_iff.mp hinter w
        simpa [hw] using hmem
      · have hout : U \ N = Z \ N := hUout.trans hZout.symm
        have hmem := Finset.ext_iff.mp hout w
        simpa [hw] using hmem
    have hcard : (fullEvent.filter fun U ↦ U \ N = O).card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hfiberMaps hfiberInj
    have hcardReal : ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) ≤
        (target.card : ℝ) := by exact_mod_cast hcard
    exact hcardReal.trans (hwindow O (Finset.mem_filter.mp hO).1)
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := fullEvent) (t := outsideEvent) (f := fun U ↦ U \ N) hmaps
  calc
    (fullEvent.card : ℝ) =
        ∑ O ∈ outsideEvent,
          ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) := by
      rw [hcard, Nat.cast_sum]
    _ ≤ ∑ _O ∈ outsideEvent, windowBound :=
      Finset.sum_le_sum fun O hO ↦ hfiber O hO
    _ = (outsideEvent.card : ℝ) * windowBound := by
      simp
    _ = ((((Finset.univ : Finset V) \ N).powerset.filter fun O ↦
          A.mulVec (finsetIndicator O) = targetValue).card : ℝ) *
        windowBound := by rfl

/-- Real-normalized form for equally sized independent blocks.  Relative to
all `2^|V|` subsets, each independent block contributes one factor
`2 / √m`. -/
lemma card_mulVec_fiber_real_le {I : Type*} [Fintype I]
    (A : Matrix I V ℝ) (blocks : R → Finset V) (patterns : R → I → ℝ)
    (hdisjoint : Set.PairwiseDisjoint Set.univ blocks)
    (hcols : ∀ r w, w ∈ blocks r → A.col w = patterns r)
    (hLI : LinearIndependent ℝ patterns) (m : ℕ) (hm : 1 ≤ m)
    (hcard : ∀ r, (blocks r).card = m) (targetValue : I → ℝ) :
    (((Finset.univ : Finset (Finset V)).filter fun U ↦
        A.mulVec (finsetIndicator U) = targetValue).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card V *
        (2 : ℝ) ^ Fintype.card R / Real.sqrt m ^ Fintype.card R := by
  let event := (Finset.univ : Finset (Finset V)).filter fun U ↦
    A.mulVec (finsetIndicator U) = targetValue
  have hfinite := card_mulVec_fiber_le A blocks patterns hdisjoint hcols hLI
    targetValue
  have hsum : ∑ r, (blocks r).card = Fintype.card R * m := by
    simp_rw [hcard]
    simp
  have hcentralNat :
      (∏ r, Nat.choose (blocks r).card ((blocks r).card / 2)) =
        (Nat.choose m (m / 2)) ^ Fintype.card R := by
    simp_rw [hcard]
    simp
  have hfiniteReal : (event.card : ℝ) ≤
      (2 : ℝ) ^ (Fintype.card V - Fintype.card R * m) *
        (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R := by
    exact_mod_cast (by simpa only [event, hsum, hcentralNat] using hfinite)
  have hbinom := choose_middle_le_two_mul_two_pow_div_sqrt m hm
  have hcentralReal : (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R ≤
      (2 * ((2 : ℝ) ^ m / Real.sqrt m)) ^ Fintype.card R :=
    pow_le_pow_left₀ (by positivity) hbinom _
  have hWcard : (Finset.univ.biUnion blocks).card =
      Fintype.card R * m := by
    calc
      (Finset.univ.biUnion blocks).card = ∑ r, (blocks r).card :=
        Finset.card_biUnion (by simpa only [Finset.coe_univ] using hdisjoint)
      _ = Fintype.card R * m := hsum
  have hroom : Fintype.card R * m ≤ Fintype.card V := by
    rw [← hWcard, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have htwo :
      (2 : ℝ) ^ (Fintype.card V - Fintype.card R * m) *
          ((2 : ℝ) ^ m) ^ Fintype.card R =
        (2 : ℝ) ^ Fintype.card V := by
    rw [← pow_mul, ← pow_add]
    rw [Nat.mul_comm m (Fintype.card R), Nat.sub_add_cancel hroom]
  calc
    (event.card : ℝ) ≤
        (2 : ℝ) ^ (Fintype.card V - Fintype.card R * m) *
          (Nat.choose m (m / 2) : ℝ) ^ Fintype.card R := hfiniteReal
    _ ≤ (2 : ℝ) ^ (Fintype.card V - Fintype.card R * m) *
          (2 * ((2 : ℝ) ^ m / Real.sqrt m)) ^ Fintype.card R := by
      exact mul_le_mul_of_nonneg_left hcentralReal (by positivity)
    _ = (2 : ℝ) ^ Fintype.card V *
          (2 : ℝ) ^ Fintype.card R / Real.sqrt m ^ Fintype.card R := by
      rw [mul_pow, div_pow, div_eq_mul_inv]
      rw [div_eq_mul_inv]
      rw [← htwo]
      ring

end FiniteFibers

section SwitchingPatterns

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- Union of the full ternary column-code fibres having size less than `m`. -/
noncomputable def smallSwitchingColumnSet (G : SimpleGraph V)
    (p : I → V × V) (m : ℕ) : Finset V :=
  Finset.univ.biUnion fun t : ↥(Finset.univ : Finset I) → Fin 3 ↦
    if (switchingColumnFiber G p Finset.univ Finset.univ t).card < m then
      switchingColumnFiber G p Finset.univ Finset.univ t
    else ∅

/-- There are at most `3^s` ternary column types, so the union of fibres of
size below `m` costs at most `3^s (m-1)` columns. -/
lemma card_smallSwitchingColumnSet_le (G : SimpleGraph V)
    (p : I → V × V) (m : ℕ) :
    (smallSwitchingColumnSet G p m).card ≤
      3 ^ Fintype.card I * (m - 1) := by
  classical
  calc
    (smallSwitchingColumnSet G p m).card ≤
        ∑ t : (↥(Finset.univ : Finset I) → Fin 3),
          (if (switchingColumnFiber G p Finset.univ Finset.univ t).card < m then
            switchingColumnFiber G p Finset.univ Finset.univ t
          else ∅).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _t : (↥(Finset.univ : Finset I) → Fin 3), (m - 1) := by
      apply Finset.sum_le_sum
      intro t _ht
      by_cases hsmall :
          (switchingColumnFiber G p Finset.univ Finset.univ t).card < m
      · simp only [if_pos hsmall]
        omega
      · simp [hsmall]
    _ = 3 ^ Fintype.card I * (m - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      norm_num

/-- Every column surviving deletion of the small fibres belongs to a ternary
type occurring at least `m` times. -/
lemma large_switchingColumnFiber_of_not_mem_small
    (G : SimpleGraph V) (p : I → V × V) (m : ℕ) {w : V}
    (hw : w ∉ smallSwitchingColumnSet G p m) :
    m ≤ (switchingColumnFiber G p Finset.univ Finset.univ
      (switchingColumnCode G p Finset.univ w)).card := by
  classical
  by_contra hlt
  have hsmall : (switchingColumnFiber G p Finset.univ Finset.univ
      (switchingColumnCode G p Finset.univ w)).card < m := by omega
  apply hw
  rw [smallSwitchingColumnSet, Finset.mem_biUnion]
  refine ⟨switchingColumnCode G p Finset.univ w, Finset.mem_univ _, ?_⟩
  simp only [if_pos hsmall, mem_switchingColumnFiber,
    Finset.mem_univ, true_and]

/-- Robust rank after every permitted column deletion produces `r`
linearly independent ternary column patterns, each repeated on `m` pairwise
disjoint columns.  This is the finite-pattern specialization of the
structural input in KSSS Theorem 13.8. -/
lemma exists_large_independent_switchingColumnBlocks
    (G : SimpleGraph V) (p : I → V × V) (budget r m : ℕ)
    (hbudget : 3 ^ Fintype.card I * (m - 1) ≤ budget)
    (hrank : ∀ Q : Finset V, Q.card ≤ budget →
      r ≤ Matrix.rank ((switchingDifferenceMatrix G p).submatrix id
        (fun w : {w : V // w ∉ Q} ↦ w.1))) :
    ∃ (blocks : Fin r → Finset V) (patterns : Fin r → I → ℝ),
      Set.PairwiseDisjoint Set.univ blocks ∧
        (∀ i, (blocks i).card = m) ∧
        (∀ i w, w ∈ blocks i →
          (switchingDifferenceMatrix G p).col w = patterns i) ∧
        LinearIndependent ℝ patterns := by
  classical
  let Q := smallSwitchingColumnSet G p m
  have hQ : Q.card ≤ budget :=
    (card_smallSwitchingColumnSet_le G p m).trans hbudget
  let A := (switchingDifferenceMatrix G p).submatrix id
    (fun w : {w : V // w ∉ Q} ↦ w.1)
  obtain ⟨e, heLI⟩ := exists_linearIndependent_columns A r (hrank Q hQ)
  let selected : Fin r → V := fun i ↦ (e i).1
  let patterns : Fin r → I → ℝ := fun i ↦
    (switchingDifferenceMatrix G p).col (selected i)
  have hpatternsLI : LinearIndependent ℝ patterns := by
    have hfun : patterns = fun i ↦ A.col (e i) := by
      funext i a
      rfl
    rw [hfun]
    exact heLI
  let fiber : Fin r → Finset V := fun i ↦
    switchingColumnFiber G p Finset.univ Finset.univ
      (switchingColumnCode G p Finset.univ (selected i))
  have hfiberLarge : ∀ i, m ≤ (fiber i).card := by
    intro i
    exact large_switchingColumnFiber_of_not_mem_small G p m (e i).2
  choose blocks hblocksSub hblocksCard using fun i ↦
    Finset.exists_subset_card_eq (hfiberLarge i)
  have hblocksDisjoint : Set.PairwiseDisjoint Set.univ blocks := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hwiFiber := hblocksSub i hwi
    have hwjFiber := hblocksSub j hwj
    have hcodei := (mem_switchingColumnFiber.mp hwiFiber).2
    have hcodej := (mem_switchingColumnFiber.mp hwjFiber).2
    have hselectedCode : switchingColumnCode G p Finset.univ (selected i) =
        switchingColumnCode G p Finset.univ (selected j) :=
      hcodei.symm.trans hcodej
    have hpattern : patterns i = patterns j := by
      funext a
      exact (switchingColumnCode_eq_iff G p Finset.univ
        (selected i) (selected j)).mp hselectedCode a (Finset.mem_univ a)
    exact hij (hpatternsLI.injective hpattern)
  refine ⟨blocks, patterns, hblocksDisjoint, hblocksCard, ?_, hpatternsLI⟩
  intro i w hwi
  have hwFiber := hblocksSub i hwi
  have hcode := (mem_switchingColumnFiber.mp hwFiber).2
  funext a
  exact (switchingColumnCode_eq_iff G p Finset.univ w (selected i)).mp
    hcode a (Finset.mem_univ a)

/-- Explicit finite Halász estimate for a switching tuple that is not
`(k+1)`-degenerate.  The exponent is the surviving robust rank `s-k`. -/
lemma card_mulVec_fiber_real_le_of_not_isKDegenerate
    (G : SimpleGraph V) (p : I → V × V) (budget k m : ℕ)
    (hk : k < Fintype.card I) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card I * (m - 1) ≤ budget)
    (hnondeg : ¬ IsKDegenerate G p budget (k + 1))
    (targetValue : I → ℝ) :
    (((Finset.univ : Finset (Finset V)).filter fun U ↦
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
          targetValue).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card V *
        (2 : ℝ) ^ (Fintype.card I - k) /
          Real.sqrt m ^ (Fintype.card I - k) := by
  have hrank : ∀ Q : Finset V, Q.card ≤ budget →
      Fintype.card I - k ≤
        Matrix.rank ((switchingDifferenceMatrix G p).submatrix id
          (fun w : {w : V // w ∉ Q} ↦ w.1)) := by
    intro Q hQ
    by_contra hlt
    apply hnondeg
    refine ⟨Q, hQ, ?_⟩
    omega
  obtain ⟨blocks, patterns, hdisjoint, hcard, hcols, hLI⟩ :=
    exists_large_independent_switchingColumnBlocks G p budget
      (Fintype.card I - k) m hbudget hrank
  have h := card_mulVec_fiber_real_le (switchingDifferenceMatrix G p)
    blocks patterns hdisjoint hcols hLI m hm hcard targetValue
  simpa only [Fintype.card_fin] using h

end SwitchingPatterns

section SwitchingScoreFiber

variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- Every column indexed by a common nonneighbor of all tuple endpoints is
zero. -/
lemma switchingDifferenceMatrix_col_eq_zero_of_mem_commonNonneighbors
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) {w : Fin n}
    (hw : w ∈ switchingCommonNonneighbors G p S₀) :
    (switchingDifferenceMatrix G p).col w = 0 := by
  funext i
  change w ∈ nonneighborsOf G (switchingEndpointFinset p) S₀ at hw
  have hw' := mem_nonneighborsOf.mp hw
  have hy : ¬G.Adj (p i).1 w :=
    hw'.2.2 (p i).1 (mem_switchingEndpointFinset.mpr
      (Or.inl ⟨i, rfl⟩))
  have hz : ¬G.Adj (p i).2 w :=
    hw'.2.2 (p i).2 (mem_switchingEndpointFinset.mpr
      (Or.inr ⟨i, rfl⟩))
  simp [Matrix.col_apply, switchingDifferenceMatrix, hy, hz]

/-- For an admissible oriented switch, the corresponding row of the
neighbourhood-difference matrix is exactly the real switch increment. -/
lemma switchingDifferenceMatrix_mulVec_eq_switchIncrement_edgeScore
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (U : Finset (Fin n)) (i : I)
    (hy : (p i).1 ∈ U) (hz : (p i).2 ∉ U) :
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) i =
      (switchIncrement (edgeScore G) U (p i).1 (p i).2 : ℝ) := by
  rw [switchingDifferenceMatrix_mulVec,
    switchIncrement_edgeScore G hy hz,
    Finset.erase_eq_self.mpr hz,
    AKSGraph.degreeInto_erase_self]
  push_cast
  rfl

lemma mem_switchingTupleFinset_iff
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (U : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n) :
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ↔
      ∀ j, p j ∈ admissibleSwitches T (edgeScore G) U j.1.1 := by
  classical
  simp only [switchingTupleFinset, rawTupleFinset,
    Fintype.mem_piFinset]

/-- Converse to the matrix-sum necessity: membership in `T`, the endpoint
orientations, and the exact switching-difference vector are sufficient for
membership in the ordered switching-tuple expansion. -/
lemma mem_switchingTupleFinset_of_mulVec_eq_labels
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (U : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hy : ∀ j, (p j).1 ∈ U)
    (hz : ∀ j, (p j).2 ∉ U)
    (hmul : (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
      fun j ↦ (j.1.1 : ℝ)) :
    p ∈ switchingTupleFinset T (edgeScore G) labels a U := by
  rw [mem_switchingTupleFinset_iff]
  intro j
  simp only [admissibleSwitches, Finset.mem_filter]
  refine ⟨hpT j, hy j, hz j, ?_⟩
  have hj := congrFun hmul j
  rw [switchingDifferenceMatrix_mulVec_eq_switchIncrement_edgeScore
    G p U j (hy j) (hz j)] at hj
  exact_mod_cast hj

/-- A prescribed private-block count solves every switching equation once
the outside contribution and endpoint orientations are fixed. -/
lemma mem_switchingTupleFinset_of_private_counts
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ O U : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (hy : ∀ j, (p j).1 ∈ U) (hz : ∀ j, (p j).2 ∉ U)
    (ell : RawTupleIndex labels a → ℕ)
    (houtside : U \ Finset.univ.biUnion
      (fun i ↦ switchingPrivateNeighbors G p i S₀) = O)
    (hcounts : ∀ j,
      (U ∩ switchingPrivateNeighbors G p j S₀).card = ell j)
    (hrequired : ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j + ell j =
        (j.1.1 : ℝ)) :
    p ∈ switchingTupleFinset T (edgeScore G) labels a U := by
  apply mem_switchingTupleFinset_of_mulVec_eq_labels
    T G labels a U p hpT hy hz
  funext j
  rw [switchingDifferenceMatrix_mulVec_private_decompose G p S₀ U hp j,
    houtside, hcounts j]
  exact hrequired j

/-- Sum the exact private-block fibres over any family of admissible outside
assignments.  Endpoint orientations are imposed only on the outside part;
the endpoint/private-block disjointness then preserves them after the blocks
are filled.  Thus every prescribed fibre contributes to the fixed-tuple
window count. -/
lemma sum_private_choose_le_card_states_containing_switchingTuple_and_window
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (outsides : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (houtside : ∀ O ∈ outsides,
      Disjoint O (Finset.univ.biUnion
        (fun i ↦ switchingPrivateNeighbors G p i S₀)))
    (hy : ∀ O ∈ outsides, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ outsides, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ outsides, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ))
    (window : Finset (Fin n) → Prop)
    (hwindow : ∀ U,
      U \ Finset.univ.biUnion
          (fun i ↦ switchingPrivateNeighbors G p i S₀) ∈ outsides →
      (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
        counts (U \ Finset.univ.biUnion
          (fun j ↦ switchingPrivateNeighbors G p j S₀)) i) →
      window U) :
    (∑ O ∈ outsides, ∏ i,
        Nat.choose (switchingPrivateNeighbors G p i S₀).card (counts O i)) ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card := by
  classical
  let blocks := fun i : RawTupleIndex labels a ↦
    switchingPrivateNeighbors G p i S₀
  let source := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    U \ Finset.univ.biUnion blocks ∈ outsides ∧
      ∀ i, (U ∩ blocks i).card =
        counts (U \ Finset.univ.biUnion blocks) i
  have hdisjoint : Set.PairwiseDisjoint Set.univ blocks := by
    intro i _hi j _hj hij
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp hij
  have hcount :
      (∑ O ∈ outsides, ∏ i, Nat.choose (blocks i).card (counts O i)) ≤
        source.card := by
    exact sum_prod_choose_le_card_dependent_blockCounts blocks outsides counts
      hdisjoint (by simpa only [blocks] using houtside)
  apply hcount.trans
  apply Finset.card_le_card
  intro U hU
  have hU' := (Finset.mem_filter.mp hU).2
  let O := U \ Finset.univ.biUnion blocks
  have hO : O ∈ outsides := by simpa only [O] using hU'.1
  have hend : Disjoint (switchingEndpointFinset p)
      (Finset.univ.biUnion blocks) := by
    simpa only [blocks] using
      switchingEndpointFinset_disjoint_privateUnion G p S₀
  have hleft : ∀ j, (p j).1 ∈ U := by
    intro j
    exact (Finset.mem_sdiff.mp (hy O hO j)).1
  have hright : ∀ j, (p j).2 ∉ U := by
    intro j hjU
    apply hz O hO j
    apply Finset.mem_sdiff.mpr
    refine ⟨hjU, ?_⟩
    exact fun hjW ↦ Finset.disjoint_left.mp hend (by simp) hjW
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ U, ?_, hwindow U hU'.1 hU'.2⟩
  apply mem_switchingTupleFinset_of_private_counts
    T G labels a S₀ O U p hpT hp hleft hright (counts O)
  · rfl
  · intro j
    simpa only [blocks, O] using hU'.2 j
  · exact hrequired O hO

/-- Sum arbitrary good subfamilies of the exact private-block fibres into the
fixed-switching-tuple window event.  In contrast with the preceding binomial
fibre bound, this form retains a further property supplied by a slice
concentration theorem inside every prescribed-count fibre. -/
lemma sum_private_goodFibers_le_card_states_containingSwitchingTuple_and_window
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (outsides : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (hy : ∀ O ∈ outsides, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ outsides, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ outsides, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ))
    (good window : Finset (Fin n) → Prop)
    (hwindow : ∀ U,
      U \ Finset.univ.biUnion
          (fun i ↦ switchingPrivateNeighbors G p i S₀) ∈ outsides →
      (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
        counts (U \ Finset.univ.biUnion
          (fun j ↦ switchingPrivateNeighbors G p j S₀)) i) →
      good U → window U) :
    (∑ O ∈ outsides,
      ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        U \ Finset.univ.biUnion
            (fun i ↦ switchingPrivateNeighbors G p i S₀) = O ∧
          (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
            counts O i) ∧ good U).card) ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card := by
  classical
  let blocks := fun i : RawTupleIndex labels a ↦
    switchingPrivateNeighbors G p i S₀
  let source := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    U \ Finset.univ.biUnion blocks ∈ outsides ∧
      (∀ i, (U ∩ blocks i).card =
        counts (U \ Finset.univ.biUnion blocks) i) ∧ good U
  have hsource :
      (∑ O ∈ outsides,
        ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          U \ Finset.univ.biUnion blocks = O ∧
            (∀ i, (U ∩ blocks i).card = counts O i) ∧ good U).card) =
          source.card := by
    exact sum_card_dependent_blockGoodFibers_eq blocks outsides counts good
  rw [show (∑ O ∈ outsides,
      ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        U \ Finset.univ.biUnion
            (fun i ↦ switchingPrivateNeighbors G p i S₀) = O ∧
          (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
            counts O i) ∧ good U).card) = source.card by
      simpa only [blocks] using hsource]
  apply Finset.card_le_card
  intro U hU
  have hU' := (Finset.mem_filter.mp hU).2
  let O := U \ Finset.univ.biUnion blocks
  have hO : O ∈ outsides := by simpa only [O] using hU'.1
  have hend : Disjoint (switchingEndpointFinset p)
      (Finset.univ.biUnion blocks) := by
    simpa only [blocks] using
      switchingEndpointFinset_disjoint_privateUnion G p S₀
  have hleft : ∀ j, (p j).1 ∈ U := by
    intro j
    exact (Finset.mem_sdiff.mp (hy O hO j)).1
  have hright : ∀ j, (p j).2 ∉ U := by
    intro j hjU
    apply hz O hO j
    apply Finset.mem_sdiff.mpr
    refine ⟨hjU, ?_⟩
    exact fun hjW ↦ Finset.disjoint_left.mp hend (by simp) hjW
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ U, ?_,
    hwindow U hU'.1 hU'.2.1 hU'.2.2⟩
  apply mem_switchingTupleFinset_of_private_counts
    T G labels a S₀ O U p hpT hp hleft hright (counts O)
  · rfl
  · intro j
    simpa only [blocks, O] using hU'.2.1 j
  · exact hrequired O hO

/-- Membership in the ordered switch-tuple expansion forces one exact
matrix-sum target, namely the vector of prescribed switching labels. -/
lemma switchingTuple_mulVec_eq_labels
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (U : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hp : p ∈ switchingTupleFinset T (edgeScore G) labels a U) :
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
      fun j ↦ (j.1.1 : ℝ) := by
  funext j
  have hj := (mem_switchingTupleFinset_iff T G labels a U p).mp hp j
  have hj' : (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
      switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
    have hjfull : p j ∈ T ∧ (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
        switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
      simpa only [admissibleSwitches, Finset.mem_filter] using hj
    exact hjfull.2
  rw [switchingDifferenceMatrix_mulVec_eq_switchIncrement_edgeScore
    G p U j hj'.1 hj'.2.1, hj'.2.2]

/-- Adding or deleting common nonneighbors of all tuple endpoints preserves
membership in the ordered switching-tuple expansion.  These vertices are
outside every endpoint and their switching-matrix columns vanish. -/
lemma mem_switchingTupleFinset_sdiff_commonNonneighbors_iff
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (U S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n) :
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ↔
      p ∈ switchingTupleFinset T (edgeScore G) labels a
        (U \ switchingCommonNonneighbors G p S₀) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let A := switchingDifferenceMatrix G p
  have hzero : ∀ w ∈ N, A.col w = 0 := by
    intro w hw
    exact switchingDifferenceMatrix_col_eq_zero_of_mem_commonNonneighbors
      G p S₀ (by simpa only [N, A] using hw)
  have hnotN : ∀ j, (p j).1 ∉ N ∧ (p j).2 ∉ N := by
    intro j
    constructor <;> intro hmem
    · exact (mem_nonneighborsOf.mp hmem).2.1
        (mem_switchingEndpointFinset.mpr (Or.inl ⟨j, rfl⟩))
    · exact (mem_nonneighborsOf.mp hmem).2.1
        (mem_switchingEndpointFinset.mpr (Or.inr ⟨j, rfl⟩))
  constructor
  · intro htuple
    have hpoint := (mem_switchingTupleFinset_iff T G labels a U p).mp htuple
    apply mem_switchingTupleFinset_of_mulVec_eq_labels
    · intro j
      have hj := hpoint j
      have hj' : p j ∈ T ∧ (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
          switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hj
      exact hj'.1
    · intro j
      have hj := hpoint j
      have hj' : p j ∈ T ∧ (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
          switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hj
      exact Finset.mem_sdiff.mpr ⟨hj'.2.1, (hnotN j).1⟩
    · intro j hj
      have hjU : (p j).2 ∈ U := (Finset.mem_sdiff.mp hj).1
      have hpointj := hpoint j
      have hpointj' : p j ∈ T ∧ (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
          switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hpointj
      exact hpointj'.2.2.1 hjU
    · rw [mulVec_finsetIndicator_sdiff_of_cols_zero A N U hzero]
      exact switchingTuple_mulVec_eq_labels T G labels a U p htuple
  · intro htuple
    let U' := U \ N
    have hpoint := (mem_switchingTupleFinset_iff T G labels a U' p).mp
      (by simpa only [U', N] using htuple)
    apply mem_switchingTupleFinset_of_mulVec_eq_labels
    · intro j
      have hj := hpoint j
      have hj' : p j ∈ T ∧ (p j).1 ∈ U' ∧ (p j).2 ∉ U' ∧
          switchIncrement (edgeScore G) U' (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hj
      exact hj'.1
    · intro j
      have hj := hpoint j
      have hj' : p j ∈ T ∧ (p j).1 ∈ U' ∧ (p j).2 ∉ U' ∧
          switchIncrement (edgeScore G) U' (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hj
      exact (Finset.mem_sdiff.mp hj'.2.1).1
    · intro j hjU
      have hj' : (p j).2 ∈ U' :=
        Finset.mem_sdiff.mpr ⟨hjU, (hnotN j).2⟩
      have hpointj := hpoint j
      have hpointj' : p j ∈ T ∧ (p j).1 ∈ U' ∧ (p j).2 ∉ U' ∧
          switchIncrement (edgeScore G) U' (p j).1 (p j).2 = j.1.1 := by
        simpa only [admissibleSwitches, Finset.mem_filter] using hpointj
      exact hpointj'.2.2.1 hj'
    · have hmul := switchingTuple_mulVec_eq_labels T G labels a U' p
        (by simpa only [U', N] using htuple)
      have hsame := mulVec_finsetIndicator_sdiff_of_cols_zero A N U hzero
      rw [← hsame]
      simpa only [A, U'] using hmul

/-- Lower conditional exposure on the common-nonneighbor reservoir.  Each
outside switching configuration has at least `windowLower` extensions inside
the zero-column reservoir which satisfy the window event, and the outside
and inside pieces are recovered uniquely by difference/intersection. -/
lemma card_states_containing_switchingTuple_and_window_ge_conditional
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (window : Finset (Fin n) → Prop)
    (windowLower : ℝ)
    (hwindow : ∀ O ∈ (((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O),
      windowLower ≤
        (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ)) :
    (((((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O).card : ℝ) *
        windowLower) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let outside := (Finset.univ : Finset (Fin n)) \ N
  let outsideEvent := outside.powerset.filter fun O ↦
    p ∈ switchingTupleFinset T (edgeScore G) labels a O
  let fullEvent := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U
  have hmaps : Set.MapsTo (fun U : Finset (Fin n) ↦ U \ N)
      (fullEvent : Set (Finset (Fin n))) (outsideEvent : Set (Finset (Fin n))) := by
    intro U hU
    have hU' := (Finset.mem_filter.mp hU).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    · exact (mem_switchingTupleFinset_sdiff_commonNonneighbors_iff
        T G labels a U S₀ p).mp hU'.1
  have hfiber : ∀ O ∈ outsideEvent, windowLower ≤
      ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) := by
    intro O hO
    let target := N.powerset.filter fun R ↦ window (O ∪ R)
    have hOsub : O ⊆ outside :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hO).1
    have hON : Disjoint O N := by
      apply Finset.disjoint_left.mpr
      intro x hxO hxN
      exact (Finset.mem_sdiff.mp (hOsub hxO)).2 hxN
    have hmapsTo : Set.MapsTo (fun R : Finset (Fin n) ↦ O ∪ R)
        (target : Set (Finset (Fin n)))
        (fullEvent.filter (fun U ↦ U \ N = O) : Set (Finset (Fin n))) := by
      intro R hR
      have hR' := Finset.mem_filter.mp hR
      have hRsub : R ⊆ N := Finset.mem_powerset.mp hR'.1
      have hsdiff : (O ∪ R) \ N = O := by
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_sdiff.mp hx
          rcases Finset.mem_union.mp hx'.1 with hxO | hxR
          · exact hxO
          · exact False.elim (hx'.2 (hRsub hxR))
        · intro hxO
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_left _ hxO,
              fun hxN ↦ Finset.disjoint_left.mp hON hxO hxN⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hR'.2⟩,
        hsdiff⟩
      apply (mem_switchingTupleFinset_sdiff_commonNonneighbors_iff
        T G labels a (O ∪ R) S₀ p).mpr
      simpa only [N, hsdiff] using (Finset.mem_filter.mp hO).2
    have hinj : Set.InjOn (fun R : Finset (Fin n) ↦ O ∪ R)
        (target : Set (Finset (Fin n))) := by
      intro R hR Z hZ hEq
      have hRsub : R ⊆ N :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1
      have hZsub : Z ⊆ N :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hZ).1
      ext x
      by_cases hxN : x ∈ N
      · have hxO : x ∉ O := fun hxO ↦
          Finset.disjoint_left.mp hON hxO hxN
        have hx := Finset.ext_iff.mp hEq x
        simpa only [Finset.mem_union, hxO, false_or] using hx
      · have hxR : x ∉ R := fun hxR ↦ hxN (hRsub hxR)
        have hxZ : x ∉ Z := fun hxZ ↦ hxN (hZsub hxZ)
        simp only [hxR, hxZ]
    have hcard : target.card ≤
        (fullEvent.filter fun U ↦ U \ N = O).card :=
      Finset.card_le_card_of_injOn _ hmapsTo hinj
    have hcardReal : (target.card : ℝ) ≤
        ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) := by
      exact_mod_cast hcard
    have hwindowO : windowLower ≤ (target.card : ℝ) := by
      simpa only [target, N, outsideEvent, outside] using hwindow O hO
    exact hwindowO.trans hcardReal
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := fullEvent) (t := outsideEvent)
    (f := fun U : Finset (Fin n) ↦ U \ N) hmaps
  change (outsideEvent.card : ℝ) * windowLower ≤ (fullEvent.card : ℝ)
  calc
    (outsideEvent.card : ℝ) * windowLower =
        ∑ _O ∈ outsideEvent, windowLower := by simp
    _ ≤ ∑ O ∈ outsideEvent,
        ((fullEvent.filter fun U ↦ U \ N = O).card : ℝ) := by
      exact Finset.sum_le_sum fun O hO ↦ hfiber O hO
    _ = (fullEvent.card : ℝ) := by rw [hcard, Nat.cast_sum]

/-- Double-count the pairs `(state, ordered switching tuple)` occurring in a
windowed raw moment, with the tuple chosen first on the right-hand side. -/
lemma rawMoment_switchingCount_eq_sum_stateCounts
    (states : Finset (Finset (Fin n)))
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) :
    rawMoment states window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ)) a labels =
      ∑ p : RawTupleIndex labels a → Fin n × Fin n,
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)) := by
  classical
  let tuples := (Finset.univ :
    Finset (RawTupleIndex labels a → Fin n × Fin n))
  let rel : Finset (Fin n) →
      (RawTupleIndex labels a → Fin n × Fin n) → Prop :=
    fun U p ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := states) (t := tuples)
  have hdoubleReal := congrArg (fun z : ℕ ↦ (z : ℝ)) hdouble
  simp only [Nat.cast_sum] at hdoubleReal
  rw [rawMoment_switchingCount_eq_tupleCount]
  calc
    (∑ U ∈ states, indicator (window U) *
        ((switchingTupleFinset T (edgeScore G) labels a U).card : ℝ)) =
        ∑ U ∈ states, ((tuples.bipartiteAbove rel U).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hw : window U
      · rw [show indicator (window U) = 1 by simp [indicator, hw], one_mul]
        have heq : tuples.bipartiteAbove rel U =
            switchingTupleFinset T (edgeScore G) labels a U := by
          ext p
          simp [tuples, rel, hw]
        rw [heq]
      · rw [show indicator (window U) = 0 by simp [indicator, hw], zero_mul]
        have hempty : tuples.bipartiteAbove rel U = ∅ := by
          ext p
          simp [tuples, rel, hw]
        rw [hempty]
        simp
    _ = ∑ p ∈ tuples, ((states.bipartiteBelow rel p).card : ℝ) :=
      hdoubleReal
    _ = ∑ p : RawTupleIndex labels a → Fin n × Fin n,
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)) := by
      simp [tuples, rel, Finset.bipartiteBelow]

/-- The tuples used in the lower half of KSSS Lemma 13.4: every coordinate
is an allowed switch, all endpoints are distinct, and every private
neighbour block has the required size. -/
noncomputable def goodSwitchingTupleClass
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (privateLower : ℝ) :
    Finset (RawTupleIndex labels a → Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p ↦
    (∀ j, p j ∈ T) ∧ PairEndpointsDistinct p ∧
      ∀ i, privateLower ≤ ((switchingPrivateNeighbors G p i S₀).card : ℝ)

@[simp] lemma mem_goodSwitchingTupleClass
    {T : Finset (Fin n × Fin n)} {G : SimpleGraph (Fin n)}
    {labels : Finset ℤ} {a : ℤ → ℕ} {S₀ : Finset (Fin n)}
    {privateLower : ℝ}
    {p : RawTupleIndex labels a → Fin n × Fin n} :
    p ∈ goodSwitchingTupleClass T G labels a S₀ privateLower ↔
      (∀ j, p j ∈ T) ∧ PairEndpointsDistinct p ∧
        ∀ i, privateLower ≤
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) := by
  classical
  simp [goodSwitchingTupleClass]

/-- Sum a uniform lower bound for the number of admissible states over any
chosen class of ordered switching tuples. -/
lemma card_tupleClass_mul_stateLower_le_rawMoment
    (states : Finset (Finset (Fin n)))
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (tuples : Finset (RawTupleIndex labels a → Fin n × Fin n))
    (stateLower : ℝ) (hstateLower : 0 ≤ stateLower)
    (hstate : ∀ p ∈ tuples,
      stateLower ≤
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ))) :
    (tuples.card : ℝ) * stateLower ≤
      rawMoment states window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ)) a labels := by
  classical
  rw [rawMoment_switchingCount_eq_sum_stateCounts]
  calc
    (tuples.card : ℝ) * stateLower = ∑ _p ∈ tuples, stateLower := by
      simp
    _ ≤ ∑ p ∈ tuples,
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)) := by
      exact Finset.sum_le_sum fun p hp ↦ hstate p hp
    _ ≤ ∑ p : RawTupleIndex labels a → Fin n × Fin n,
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _p ↦ by positivity

/-- Lower-moment bookkeeping from KSSS Lemma 13.10(a).  Once its good-tuple
cardinality inequality is available and every good tuple has at least
`stateLower` admissible window states, one obtains the factor `|T|^s / 2`.
The cardinality estimate is kept as a named input here to avoid elaborating
the full richness theorem inside this finite summation lemma. -/
lemma rawMoment_switchingCount_ge_of_good_tuple_count_and_state_bound
    {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n × Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (privateLower : ℝ)
    (hgood : T.card ^ Fintype.card (RawTupleIndex labels a) ≤
      2 * (goodSwitchingTupleClass T G labels a S₀ privateLower).card)
    (window : Finset (Fin n) → Prop)
    (stateLower : ℝ) (hstateLower : 0 ≤ stateLower)
    (hstate : ∀ p ∈ goodSwitchingTupleClass
        T G labels a S₀ privateLower,
      stateLower ≤
        ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset
              T (edgeScore G) labels a U ∧ window U).card : ℝ))) :
    ((T.card : ℝ) ^
          Fintype.card (RawTupleIndex labels a) / 2) * stateLower ≤
      rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦ (switchingCount
          T (edgeScore G) ell U : ℝ))
        a labels := by
  classical
  let Good := goodSwitchingTupleClass T G labels a S₀
    privateLower
  have hgoodReal :
      (T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2 ≤
        (Good.card : ℝ) := by
    have hcast :
        ((T.card ^ Fintype.card (RawTupleIndex labels a) : ℕ) : ℝ) ≤
          ((2 * Good.card : ℕ) : ℝ) := by
      exact_mod_cast hgood
    push_cast at hcast
    linarith
  calc
    ((T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2) * stateLower ≤
        (Good.card : ℝ) * stateLower :=
      mul_le_mul_of_nonneg_right hgoodReal hstateLower
    _ ≤ rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦
          (switchingCount T (edgeScore G) ell U : ℝ)) a labels := by
      apply card_tupleClass_mul_stateLower_le_rawMoment
        (Finset.univ : Finset (Finset (Fin n))) window T G labels a Good
          stateLower hstateLower
      intro p hp
      exact hstate p (by simpa only [Good] using hp)

/-- Ordered tuples with all coordinates in `T` and with exact switching
degeneracy `k`. -/
noncomputable def exactSwitchingDegeneracyClass
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (budget k : ℕ) :
    Finset (RawTupleIndex labels a → Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p ↦
    (∀ j, p j ∈ T) ∧ switchingDegeneracy G p budget = k

@[simp] lemma mem_exactSwitchingDegeneracyClass
    {T : Finset (Fin n × Fin n)} {G : SimpleGraph (Fin n)}
    {labels : Finset ℤ} {a : ℤ → ℕ} {budget k : ℕ}
    {p : RawTupleIndex labels a → Fin n × Fin n} :
    p ∈ exactSwitchingDegeneracyClass T G labels a budget k ↔
      (∀ j, p j ∈ T) ∧ switchingDegeneracy G p budget = k := by
  classical
  simp [exactSwitchingDegeneracyClass]

/-- A tuple using a pair outside `T` is admissible in no state. -/
lemma card_states_containing_switchingTuple_eq_zero_of_not_all_mem
    (states : Finset (Finset (Fin n)))
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hp : ¬ ∀ j, p j ∈ T) :
    (states.filter fun U ↦
      p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
        window U).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro U _hU hEvent
  apply hp
  intro j
  have hj := (mem_switchingTupleFinset_iff T G labels a U p).mp hEvent.1 j
  have hj' : p j ∈ T ∧ (p j).1 ∈ U ∧ (p j).2 ∉ U ∧
      switchIncrement (edgeScore G) U (p j).1 (p j).2 = j.1.1 := by
    simpa only [admissibleSwitches, Finset.mem_filter] using hj
  exact hj'.1

/-- Exact decomposition of a windowed raw moment by the maximal switching
degeneracy of the ordered tuple.  Tuples outside `T` contribute zero. -/
lemma rawMoment_switchingCount_eq_sum_exactDegeneracy
    (states : Finset (Finset (Fin n)))
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (budget : ℕ) :
    rawMoment states window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ)) a labels =
      ∑ k ∈ Finset.range (Fintype.card (RawTupleIndex labels a) + 1),
        ∑ p ∈ exactSwitchingDegeneracyClass T G labels a budget k,
          (((states.filter fun U ↦
            p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
              window U).card : ℝ)) := by
  classical
  rw [rawMoment_switchingCount_eq_sum_stateCounts]
  let f : (RawTupleIndex labels a → Fin n × Fin n) → ℝ := fun p ↦
    ((states.filter fun U ↦
      p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
        window U).card : ℝ)
  have hmaps : ∀ p ∈ (Finset.univ :
      Finset (RawTupleIndex labels a → Fin n × Fin n)),
      switchingDegeneracy G p budget ∈
        Finset.range (Fintype.card (RawTupleIndex labels a) + 1) := by
    intro p _hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (switchingDegeneracy_le G p budget))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro k hk
  symm
  apply Finset.sum_subset
  · intro p hp
    have hp' := mem_exactSwitchingDegeneracyClass.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩
  · intro p hpLarge hpSmall
    have hpDeg := (Finset.mem_filter.mp hpLarge).2
    have hpNotAll : ¬ ∀ j, p j ∈ T := by
      intro hpAll
      apply hpSmall
      exact mem_exactSwitchingDegeneracyClass.mpr ⟨hpAll, hpDeg⟩
    rw [card_states_containing_switchingTuple_eq_zero_of_not_all_mem
      states window T G labels a p hpNotAll]
    norm_num

/-- Maximality of `switchingDegeneracy`, in the range where its successor is
still a possible row codimension. -/
lemma not_isKDegenerate_succ_of_switchingDegeneracy_lt
    {labels : Finset ℤ} {a : ℤ → ℕ}
    (G : SimpleGraph (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n) (budget : ℕ)
    (hdeg : switchingDegeneracy G p budget <
      Fintype.card (RawTupleIndex labels a)) :
    ¬ IsKDegenerate G p budget (switchingDegeneracy G p budget + 1) := by
  intro hsucc
  have hle := le_switchingDegeneracy_of_isKDegenerate
    (G := G) (p := p) (budget := budget)
    (k := switchingDegeneracy G p budget + 1) (by omega) hsucc
  omega

/-- An exact degeneracy class is contained in the cumulative class counted
by KSSS Lemma 13.10(b). -/
lemma exactSwitchingDegeneracyClass_subset_kDegenerate
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (budget k : ℕ) :
    exactSwitchingDegeneracyClass T G labels a budget k ⊆
      (Finset.univ :
        Finset (RawTupleIndex labels a → Fin n × Fin n)).filter (fun p ↦
          (∀ j, p j ∈ T) ∧ IsKDegenerate G p budget k) := by
  intro p hp
  have hp' := mem_exactSwitchingDegeneracyClass.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ p, hp'.1, ?_⟩
  rw [← hp'.2]
  exact isKDegenerate_switchingDegeneracy G p budget

lemma card_exactSwitchingDegeneracyClass_le_kDegenerate
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (budget k : ℕ) :
    (exactSwitchingDegeneracyClass T G labels a budget k).card ≤
      ((Finset.univ :
        Finset (RawTupleIndex labels a → Fin n × Fin n)).filter (fun p ↦
          (∀ j, p j ∈ T) ∧ IsKDegenerate G p budget k)).card :=
  Finset.card_le_card
    (exactSwitchingDegeneracyClass_subset_kDegenerate
      T G labels a budget k)

/-- Fixed-tuple form of the specialized Halász estimate. -/
lemma card_states_containing_nondegenerate_switchingTuple_le
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (budget k m : ℕ)
    (hk : k < Fintype.card (RawTupleIndex labels a)) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card (RawTupleIndex labels a) * (m - 1) ≤ budget)
    (hnondeg : ¬ IsKDegenerate G p budget (k + 1)) :
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U).card : ℝ) ≤
      (2 : ℝ) ^ n *
        (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
          Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) := by
  classical
  let targetValue : RawTupleIndex labels a → ℝ := fun j ↦ (j.1.1 : ℝ)
  have hsub :
      (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
            targetValue) := by
    intro U hU
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ U, ?_⟩
    exact switchingTuple_mulVec_eq_labels T G labels a U p
      (Finset.mem_filter.mp hU).2
  have hhalasz := card_mulVec_fiber_real_le_of_not_isKDegenerate
    G p budget k m hk hm hbudget hnondeg targetValue
  have hcard := Finset.card_le_card hsub
  have hcardReal :
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U).card : ℝ) ≤
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
            targetValue).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans (by simpa only [Fintype.card_fin] using hhalasz)

/-- Halász count after exposing the common-nonneighbor reservoir.  Since all
columns on that reservoir vanish, the independent repeated blocks lie in its
complement and the ambient power of two is reduced accordingly. -/
lemma card_outside_commonNonneighbors_mulVec_fiber_le
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (budget k m : ℕ)
    (hk : k < Fintype.card I) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card I * (m - 1) ≤ budget)
    (hnondeg : ¬ IsKDegenerate G p budget (k + 1))
    (targetValue : I → ℝ) :
    ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter fun U ↦
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator U) =
          targetValue).card : ℝ) ≤
      (2 : ℝ) ^ ((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).card *
        (2 : ℝ) ^ (Fintype.card I - k) /
          Real.sqrt m ^ (Fintype.card I - k) := by
  have hrank : ∀ Q : Finset (Fin n), Q.card ≤ budget →
      Fintype.card I - k ≤
        Matrix.rank ((switchingDifferenceMatrix G p).submatrix id
          (fun w : {w : Fin n // w ∉ Q} ↦ w.1)) := by
    intro Q hQ
    by_contra hlt
    apply hnondeg
    refine ⟨Q, hQ, ?_⟩
    omega
  obtain ⟨blocks, patterns, hdisjoint, hcard, hcols, hLI⟩ :=
    exists_large_independent_switchingColumnBlocks G p budget
      (Fintype.card I - k) m hbudget hrank
  let N := switchingCommonNonneighbors G p S₀
  let ambient := (Finset.univ : Finset (Fin n)) \ N
  have hblockSub : ∀ r, blocks r ⊆ ambient := by
    intro r w hw
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ w, ?_⟩
    intro hwN
    have hzero : (switchingDifferenceMatrix G p).col w = 0 :=
      switchingDifferenceMatrix_col_eq_zero_of_mem_commonNonneighbors
        G p S₀ (by simpa only [N] using hwN)
    apply hLI.ne_zero r
    rw [← hcols r w hw, hzero]
  have h := card_mulVec_fiber_on_ambient_real_le
    (switchingDifferenceMatrix G p) ambient blocks patterns hblockSub
      hdisjoint hcols hLI m hm hcard targetValue
  simpa only [ambient, N, Fintype.card_fin] using h

/-- Fixed-tuple upper bound after exposing the common-nonneighbor reservoir.
The switching equations are charged to the outside assignment by the
specialized Halasz estimate, while `hwindow` supplies the conditional window
bound for each such assignment. -/
lemma card_states_containing_nondegenerate_switchingTuple_and_window_le
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (budget k m : ℕ)
    (hk : k < Fintype.card (RawTupleIndex labels a)) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card (RawTupleIndex labels a) * (m - 1) ≤ budget)
    (hnondeg : ¬ IsKDegenerate G p budget (k + 1))
    (window : Finset (Fin n) → Prop) [DecidablePred window]
    (windowBound : ℝ) (hwindowBound : 0 ≤ windowBound)
    (hwindow : ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset,
      ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
        window (O ∪ R)).card : ℝ) ≤ windowBound)) :
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
      ((2 : ℝ) ^ ((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).card *
        (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
          Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k)) *
        windowBound := by
  classical
  let A := switchingDifferenceMatrix G p
  let targetValue : RawTupleIndex labels a → ℝ := fun j ↦ (j.1.1 : ℝ)
  let N := switchingCommonNonneighbors G p S₀
  have hsub :
      (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          A.mulVec (finsetIndicator U) = targetValue ∧ window U) := by
    intro U hU
    have hU' := (Finset.mem_filter.mp hU).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ U, ?_, hU'.2⟩
    exact switchingTuple_mulVec_eq_labels T G labels a U p hU'.1
  have hzero : ∀ w ∈ N, A.col w = 0 := by
    intro w hw
    exact switchingDifferenceMatrix_col_eq_zero_of_mem_commonNonneighbors
      G p S₀ (by simpa only [N] using hw)
  have hconditional := card_matrixFiber_and_window_le_of_conditional
    A N targetValue window windowBound hzero (by
      simpa only [N] using hwindow)
  have houtside := card_outside_commonNonneighbors_mulVec_fiber_le
    G p S₀ budget k m hk hm hbudget hnondeg targetValue
  have hcard :
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U)).card ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        A.mulVec (finsetIndicator U) = targetValue ∧ window U)).card :=
    Finset.card_le_card hsub
  have hcardReal :
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U)).card : ℝ) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        A.mulVec (finsetIndicator U) = targetValue ∧ window U)).card : ℝ) := by
    exact_mod_cast hcard
  apply hcardReal.trans
  apply hconditional.trans
  have hmul := mul_le_mul_of_nonneg_right houtside hwindowBound
  simpa only [A, N, Fintype.card_fin] using hmul

/-- Rank-zero endpoint of the preceding estimate.  Here no Halasz saving is
available outside the common-nonneighbor reservoir, so all outside subsets
are retained. -/
lemma card_states_containing_switchingTuple_and_window_le_conditional
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n))
    (window : Finset (Fin n) → Prop) [DecidablePred window]
    (windowBound : ℝ) (hwindowBound : 0 ≤ windowBound)
    (hwindow : ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset,
      ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
        window (O ∪ R)).card : ℝ) ≤ windowBound)) :
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
      (2 : ℝ) ^ ((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).card * windowBound := by
  classical
  let A := switchingDifferenceMatrix G p
  let targetValue : RawTupleIndex labels a → ℝ := fun j ↦ (j.1.1 : ℝ)
  let N := switchingCommonNonneighbors G p S₀
  let outside := (Finset.univ : Finset (Fin n)) \ N
  have hsub :
      (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
          A.mulVec (finsetIndicator U) = targetValue ∧ window U) := by
    intro U hU
    have hU' := (Finset.mem_filter.mp hU).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ U, ?_, hU'.2⟩
    exact switchingTuple_mulVec_eq_labels T G labels a U p hU'.1
  have hzero : ∀ w ∈ N, A.col w = 0 := by
    intro w hw
    exact switchingDifferenceMatrix_col_eq_zero_of_mem_commonNonneighbors
      G p S₀ (by simpa only [N] using hw)
  have hconditional := card_matrixFiber_and_window_le_of_conditional
    A N targetValue window windowBound hzero (by
      simpa only [N] using hwindow)
  have houtsideCard :
      (((outside.powerset.filter fun O ↦
          A.mulVec (finsetIndicator O) = targetValue).card : ℝ)) ≤
        (2 : ℝ) ^ outside.card := by
    have hnat := Finset.card_le_card
      (Finset.filter_subset (fun O ↦
        A.mulVec (finsetIndicator O) = targetValue) outside.powerset)
    have hreal :
        (((outside.powerset.filter fun O ↦
          A.mulVec (finsetIndicator O) = targetValue).card : ℝ)) ≤
          (outside.powerset.card : ℝ) := by
      exact_mod_cast hnat
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using hreal
  have hcard :
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U)).card ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        A.mulVec (finsetIndicator U) = targetValue ∧ window U)).card :=
    Finset.card_le_card hsub
  have hcardReal :
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U)).card : ℝ) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U ↦
        A.mulVec (finsetIndicator U) = targetValue ∧ window U)).card : ℝ) := by
    exact_mod_cast hcard
  apply hcardReal.trans
  apply hconditional.trans
  have hmul := mul_le_mul_of_nonneg_right houtsideCard hwindowBound
  simpa only [outside, A, N] using hmul

/-- Probability-normalized form of the nondegenerate fixed-tuple bound.  If
the conditional window count is `2^|N| q`, the two exposed parts recombine to
the full Boolean-cube factor `2^n`. -/
lemma card_states_containing_nondegenerate_switchingTuple_and_window_le_cube
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (budget k m : ℕ)
    (hk : k < Fintype.card (RawTupleIndex labels a)) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card (RawTupleIndex labels a) * (m - 1) ≤ budget)
    (hnondeg : ¬ IsKDegenerate G p budget (k + 1))
    (window : Finset (Fin n) → Prop) [DecidablePred window]
    (q : ℝ) (hq : 0 ≤ q)
    (hwindow : ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset,
      ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
        window (O ∪ R)).card : ℝ) ≤
          (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card * q)) :
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
      (2 : ℝ) ^ n *
        (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
          Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) * q := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let outside := (Finset.univ : Finset (Fin n)) \ N
  have hbase :=
    card_states_containing_nondegenerate_switchingTuple_and_window_le
      T G labels a p S₀ budget k m hk hm hbudget hnondeg window
        ((2 : ℝ) ^ N.card * q) (mul_nonneg (by positivity) hq) (by
          simpa only [N] using hwindow)
  have hcard : outside.card + N.card = n := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ N)
    simpa only [outside, Finset.card_univ, Fintype.card_fin] using h
  have hpow : (2 : ℝ) ^ outside.card * (2 : ℝ) ^ N.card =
      (2 : ℝ) ^ n := by
    rw [← pow_add, hcard]
  calc
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
      ((2 : ℝ) ^ outside.card *
        (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
          Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k)) *
        ((2 : ℝ) ^ N.card * q) := by
      simpa only [outside, N] using hbase
    _ = (2 : ℝ) ^ n *
        (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
          Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) * q := by
      rw [show (2 : ℝ) ^ outside.card *
          (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
            Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) *
          ((2 : ℝ) ^ N.card * q) =
        ((2 : ℝ) ^ outside.card * (2 : ℝ) ^ N.card) *
          (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
            Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) * q by
              ring]
      rw [hpow]

/-- Boolean-cube normalization of the rank-zero endpoint. -/
lemma card_states_containing_switchingTuple_and_window_le_cube
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n))
    (window : Finset (Fin n) → Prop) [DecidablePred window]
    (q : ℝ) (hq : 0 ≤ q)
    (hwindow : ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset,
      ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
        window (O ∪ R)).card : ℝ) ≤
          (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card * q)) :
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
      (2 : ℝ) ^ n * q := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let outside := (Finset.univ : Finset (Fin n)) \ N
  have hbase := card_states_containing_switchingTuple_and_window_le_conditional
    T G labels a p S₀ window ((2 : ℝ) ^ N.card * q)
      (mul_nonneg (by positivity) hq) (by simpa only [N] using hwindow)
  have hcard : outside.card + N.card = n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    simpa only [outside, Finset.card_univ, Fintype.card_fin] using h
  have hpow : (2 : ℝ) ^ outside.card * (2 : ℝ) ^ N.card =
      (2 : ℝ) ^ n := by
    rw [← pow_add, hcard]
  calc
    (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) ≤
        (2 : ℝ) ^ outside.card * ((2 : ℝ) ^ N.card * q) := by
      simpa only [outside, N] using hbase
    _ = (2 : ℝ) ^ n * q := by rw [← mul_assoc, hpow]

/-- Sum a pointwise state-count bound over the exact degeneracy classes.
This is the finite upper-moment bookkeeping in KSSS Lemma 13.4. -/
lemma rawMoment_switchingCount_le_of_exactDegeneracy_bounds
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (budget : ℕ)
    (tupleBound stateBound : ℕ → ℝ)
    (hstateNonneg : ∀ k, 0 ≤ stateBound k)
    (htuple : ∀ k, k ≤ Fintype.card (RawTupleIndex labels a) →
      ((exactSwitchingDegeneracyClass T G labels a budget k).card : ℝ) ≤
        tupleBound k)
    (hstate : ∀ k, k ≤ Fintype.card (RawTupleIndex labels a) →
      ∀ p ∈ exactSwitchingDegeneracyClass T G labels a budget k,
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ) ≤ stateBound k) :
    rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ)) a labels ≤
      ∑ k ∈ Finset.range (Fintype.card (RawTupleIndex labels a) + 1),
        tupleBound k * stateBound k := by
  classical
  rw [rawMoment_switchingCount_eq_sum_exactDegeneracy]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ Fintype.card (RawTupleIndex labels a) := by
    have := Finset.mem_range.mp hk
    omega
  calc
    (∑ p ∈ exactSwitchingDegeneracyClass T G labels a budget k,
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)) ≤
        ∑ _p ∈ exactSwitchingDegeneracyClass T G labels a budget k,
          stateBound k :=
      Finset.sum_le_sum fun p hp ↦ hstate k hk' p hp
    _ = ((exactSwitchingDegeneracyClass T G labels a budget k).card : ℝ) *
        stateBound k := by simp
    _ ≤ tupleBound k * stateBound k := by
      exact mul_le_mul_of_nonneg_right (htuple k hk') (hstateNonneg k)

/-- The complete finite upper-moment assembly from two source inputs:
the Lemma 13.10 bound on each cumulative degeneracy class, encoded by
`tupleBound`, and the conditional bounded-window estimate on every exposed
common-nonneighbor reservoir.  The Halasz factor is proved in this file. -/
lemma rawMoment_switchingCount_le_of_conditional_window
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (budget m : ℕ) (hm : 1 ≤ m)
    (hbudget : 3 ^ Fintype.card (RawTupleIndex labels a) * (m - 1) ≤ budget)
    (q : ℝ) (hq : 0 ≤ q) (tupleBound : ℕ → ℝ)
    (htuple : ∀ k, k ≤ Fintype.card (RawTupleIndex labels a) →
      ((exactSwitchingDegeneracyClass T G labels a budget k).card : ℝ) ≤
        tupleBound k)
    (hwindow : ∀ p : RawTupleIndex labels a → Fin n × Fin n,
      (∀ j, p j ∈ T) →
      ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset,
        ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ) ≤
            (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card * q)) :
    rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ)) a labels ≤
      ∑ k ∈ Finset.range (Fintype.card (RawTupleIndex labels a) + 1),
        tupleBound k *
          ((2 : ℝ) ^ n *
            (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
              Real.sqrt m ^ (Fintype.card (RawTupleIndex labels a) - k) * q) := by
  classical
  let s := Fintype.card (RawTupleIndex labels a)
  let stateBound : ℕ → ℝ := fun k ↦
    (2 : ℝ) ^ n * (2 : ℝ) ^ (s - k) /
      Real.sqrt m ^ (s - k) * q
  apply rawMoment_switchingCount_le_of_exactDegeneracy_bounds
    window T G labels a budget tupleBound stateBound
  · intro k
    dsimp only [stateBound]
    positivity
  · intro k hk
    exact htuple k (by simpa only [s] using hk)
  · intro k hk p hp
    have hp' := mem_exactSwitchingDegeneracyClass.mp hp
    have hk' : k ≤ Fintype.card (RawTupleIndex labels a) := by
      simpa only [s] using hk
    by_cases hks : k < Fintype.card (RawTupleIndex labels a)
    · have hdeglt : switchingDegeneracy G p budget <
          Fintype.card (RawTupleIndex labels a) := by
        rw [hp'.2]
        exact hks
      have hnondeg : ¬ IsKDegenerate G p budget (k + 1) := by
        have h := not_isKDegenerate_succ_of_switchingDegeneracy_lt
          G p budget hdeglt
        simpa only [hp'.2] using h
      have hbound :=
        card_states_containing_nondegenerate_switchingTuple_and_window_le_cube
          T G labels a p S₀ budget k m hks hm hbudget hnondeg window q hq
            (hwindow p hp'.1)
      simpa only [stateBound, s] using hbound
    · have hkeq : k = Fintype.card (RawTupleIndex labels a) := by omega
      have hbound := card_states_containing_switchingTuple_and_window_le_cube
        T G labels a p S₀ window q hq (hwindow p hp'.1)
      simpa only [stateBound, s, hkeq, Nat.sub_self, pow_zero, mul_one,
        div_one] using hbound

/-- Upper half of KSSS Lemma 13.4 after inserting the already-proved finite
Lemma 13.10.  The large fiber used in the richness argument and the smaller
repeated-column fiber used in the Halasz estimate are kept separate.  The
sole non-combinatorial input left is the conditional bounded-window estimate
`hwindow` on each common-nonneighbor reservoir. -/
lemma rawMoment_switchingCount_le_of_lemma1310_and_conditional_window
    {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (S S₀ : Finset (Fin n)) (δ ρ α : ℝ)
    (switchThreshold deletionBudget richFiberSize halaszFiberSize codeBound : ℕ)
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (window : Finset (Fin n) → Prop)
    (windowRate : ℝ) (hwindowRate : 0 ≤ windowRate)
    (hmRich : 0 < richFiberSize) (hmHalasz : 0 < halaszFiberSize)
    (hρ : 0 ≤ ρ)
    (hrich : RichOn G S₀ δ ρ α) (hSS₀ : S ⊆ S₀)
    (hscale : ((deletionBudget + 2 : ℕ) : ℝ) ≤ ρ * richFiberSize)
    (hsize : δ * S₀.card ≤ richFiberSize)
    (hrichBudget : (S₀.card : ℝ) ^ α ≤ codeBound)
    (hpatternBudget :
      3 ^ Fintype.card (RawTupleIndex labels a) * (halaszFiberSize - 1) ≤
        deletionBudget)
    (hsupply : ∀ k, 0 < k → k ≤ Fintype.card (RawTupleIndex labels a) →
      3 ^ (Fintype.card (RawTupleIndex labels a) - k) * richFiberSize +
          deletionBudget + 2 ≤ switchThreshold)
    (hchoice : ∀ k, 0 < k → k ≤ Fintype.card (RawTupleIndex labels a) →
      3 ^ (Fintype.card (RawTupleIndex labels a) - k) *
          (codeBound * codeBound) ≤
        (switchingPairs G S S₀ switchThreshold).card)
    (hratio : ∀ k, 0 < k → k ≤ Fintype.card (RawTupleIndex labels a) →
      ((2 ^ Fintype.card (RawTupleIndex labels a) : ℕ) : ℝ) *
          ((3 ^ (Fintype.card (RawTupleIndex labels a) - k) *
            (codeBound * codeBound) : ℕ) : ℝ) ^ k *
          Real.sqrt n ^ k ≤
        ((switchingPairs G S S₀ switchThreshold).card : ℝ) ^ k)
    (hwindow : ∀ p : RawTupleIndex labels a → Fin n × Fin n,
      (∀ j, p j ∈ switchingPairs G S S₀ switchThreshold) →
      ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset,
        ((((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ) ≤
            (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card *
              windowRate)) :
    rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦ (switchingCount
          (switchingPairs G S S₀ switchThreshold) (edgeScore G) ell U : ℝ))
        a labels ≤
      ∑ k ∈ Finset.range (Fintype.card (RawTupleIndex labels a) + 1),
        (((switchingPairs G S S₀ switchThreshold).card : ℝ) ^
            Fintype.card (RawTupleIndex labels a) / Real.sqrt n ^ k) *
          ((2 : ℝ) ^ n *
            (2 : ℝ) ^ (Fintype.card (RawTupleIndex labels a) - k) /
              Real.sqrt halaszFiberSize ^
                (Fintype.card (RawTupleIndex labels a) - k) * windowRate) := by
  classical
  let T := switchingPairs G S S₀ switchThreshold
  let s := Fintype.card (RawTupleIndex labels a)
  let tupleBound : ℕ → ℝ := fun k ↦
    (T.card : ℝ) ^ s / Real.sqrt n ^ k
  apply rawMoment_switchingCount_le_of_conditional_window
    window T G labels a S₀ deletionBudget halaszFiberSize hmHalasz
      (by simpa only [s] using hpatternBudget) windowRate hwindowRate tupleBound
  · intro k hk
    have hclassNat := card_exactSwitchingDegeneracyClass_le_kDegenerate
      T G labels a deletionBudget k
    have hclassReal :
        ((exactSwitchingDegeneracyClass T G labels a deletionBudget k).card : ℝ) ≤
          (((Finset.univ : Finset
            (RawTupleIndex labels a → Fin n × Fin n)).filter fun p ↦
              (∀ j, p j ∈ T) ∧
                IsKDegenerate G p deletionBudget k).card : ℝ) := by
      exact_mod_cast hclassNat
    by_cases hk0 : k = 0
    · subst k
      have hzero := card_zeroDegenerate_switchingTuples
        (I := RawTupleIndex labels a) G S S₀ switchThreshold deletionBudget
      have hzero' :
          (((Finset.univ : Finset
            (RawTupleIndex labels a → Fin n × Fin n)).filter fun p ↦
              (∀ j, p j ∈ T) ∧
                IsKDegenerate G p deletionBudget 0).card : ℝ) =
            (T.card : ℝ) ^ s := by
        have hzeroReal := congrArg (fun z : ℕ ↦ (z : ℝ)) hzero
        convert hzeroReal using 1
        · apply congrArg (fun z : ℕ ↦ (z : ℝ))
          apply congrArg Finset.card
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
        · simp only [T, s, Nat.cast_pow]
      calc
        ((exactSwitchingDegeneracyClass T G labels a deletionBudget 0).card : ℝ)
            ≤ (((Finset.univ : Finset
              (RawTupleIndex labels a → Fin n × Fin n)).filter fun p ↦
                (∀ j, p j ∈ T) ∧
                  IsKDegenerate G p deletionBudget 0).card : ℝ) := hclassReal
        _ = (T.card : ℝ) ^ s := hzero'
        _ = tupleBound 0 := by simp [tupleBound]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      let defaultVertex : Fin n := ⟨0, hn⟩
      let defaultPair : Fin n × Fin n := (defaultVertex, defaultVertex)
      have hcum := card_kDegenerate_switchingTuples_le_div_sqrt
        (I := RawTupleIndex labels a) G S S₀ δ ρ α switchThreshold
          deletionBudget k richFiberSize codeBound n defaultPair hk hn hmRich hρ
          hrich hSS₀ (hsupply k hkpos hk) hscale hsize hrichBudget
          (hchoice k hkpos hk) (hratio k hkpos hk)
      have hcum' :
          (((Finset.univ : Finset
            (RawTupleIndex labels a → Fin n × Fin n)).filter fun p ↦
              (∀ j, p j ∈ T) ∧
                IsKDegenerate G p deletionBudget k).card : ℝ) ≤
            tupleBound k := by
        convert hcum using 1
        apply congrArg (fun z : ℕ ↦ (z : ℝ))
        apply congrArg Finset.card
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      exact hclassReal.trans hcum'
  · intro p hp O hO
    exact hwindow p (by simpa only [T] using hp) O hO

end SwitchingScoreFiber

end Erdos88.Switching
