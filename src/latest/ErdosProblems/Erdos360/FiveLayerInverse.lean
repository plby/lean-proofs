/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.SharpFourierCore
import ErdosProblems.Erdos360.FiveLayerFinsetArithmetic

/-!
# The five-layer fibre branch

The sharp Fourier core has doubling strictly below `12/5`.  This file starts
the finite corrected Deshouillers--Freiman analysis at support cardinality
five.  In particular it proves, with no ordering assumption on the fibre
labels, that one fibre occupies more than two thirds of a subgroup coset.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-! ## Sharp coherence when the dense fibre is largest -/

/-- The endpoint arithmetic in the relative-coset layer cake at exactly
five occupied layers.  This is the `12/5` replacement for the `5/2`
inequality used when there are at least six layers. -/
lemma relative_interval_arithmetic_five
    {s r e M G D T : ℕ}
    (hs : s = 5) (he : 1 ≤ e) (hr : 1 ≤ r) (hsplit : s = r + e)
    (hD : D ≤ e * M)
    (hbasic : 3 * G ≤ 2 * r * M + 2 * T)
    (hstrong : 6 * G + (r + 1) * M ≤ 4 * r * M + 4 * T) :
    12 * (G + D) ≤ 5 * ((G + D) + (s + e - 2) * M + T) := by
  subst s
  have he4 : e ≤ 4 := by omega
  interval_cases e
  · have : r = 4 := by omega
    subst r
    norm_num at *
    omega
  · have : r = 3 := by omega
    subst r
    norm_num at *
    omega
  · have : r = 2 := by omega
    subst r
    norm_num at *
    omega
  · have : r = 1 := by omega
    subst r
    norm_num at *
    omega

/-- Sharp relative-coset diagonal weight bound for five layers. -/
lemma relative_support_diagonal_weight_bound_five
    {A : Finset ℕ} {M : ℕ} {w : ℕ → ℕ}
    {Good Bad : Finset ℕ} {base : ℕ}
    (hAcard : A.card = 5) (hMpos : 0 < M)
    (hpart : Good ∪ Bad = A) (hdisj : Disjoint Good Bad)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ i ∈ A, w i ≤ M) (hBad : Bad.Nonempty) :
    12 * (∑ i ∈ A, w i) ≤
      5 * ∑ k ∈ A + A, relativeSupportDiagonalMax A Good w k := by
  classical
  let L := relativeSupportDiagonalMax A Good w
  let G := ∑ i ∈ Good, w i
  let D := ∑ i ∈ Bad, w i
  let T := ∑ i ∈ Good, (2 * w i - M)
  have hGoodSub : Good ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_left _ hi
  have hBadSub : Bad ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_right _ hi
  have hGoodMax : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hmax i (hGoodSub hi)
  have hD : D ≤ Bad.card * M := by
    dsimp only [D]
    calc
      ∑ i ∈ Bad, w i ≤ ∑ _i ∈ Bad, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hmax i (hBadSub hi)
      _ = Bad.card * M := by simp
  have hcards : A.card = Good.card + Bad.card := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hpart] at hc
    exact hc
  obtain ⟨hbasic, hstrong⟩ :=
    good_excess_bounds Good w hbase hbasew hGoodMax
  have harith : 12 * (G + D) ≤
      5 * ((G + D) + (A.card + Bad.card - 2) * M + T) := by
    apply relative_interval_arithmetic_five hAcard
      (Finset.card_pos.mpr hBad) (Finset.card_pos.mpr ⟨base, hbase⟩)
      hcards hD hbasic hstrong
  obtain ⟨hlow, hhigh⟩ := relative_support_threshold_bounds
    (A := A) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    hMpos hpart hdisj hbase hbasew hmax hBad
  have hlayer : (G + D) + (A.card + Bad.card - 2) * M + T ≤
      ∑ k ∈ A + A, L k := by
    have hraw := relative_support_layerCake_lower A M w L Good Bad
      hMpos hBad hpart hdisj hmax
      (fun k hk ↦ relativeSupportDiagonalMax_le hmax k) hlow hhigh
    have hsum : ∑ i ∈ A, w i = G + D := by
      rw [← hpart, Finset.sum_union hdisj]
    simpa [G, D, T, L, hsum] using hraw
  have hsum : ∑ i ∈ A, w i = G + D := by
    rw [← hpart, Finset.sum_union hdisj]
  rw [hsum]
  exact harith.trans (Nat.mul_le_mul_left 5 hlayer)

/-! ## Sharp coherence when the dense fibre is not largest -/

/-- The hybrid diagonal layer cake at support size five.  The factor `24`
is the integral form of the sharp `12/5` threshold. -/
lemma hybrid_support_diagonal_weight_bound_five
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    {base top : ℕ}
    (hAcard : A.card = 5) (hGoodSub : Good ⊆ A)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (htop : top ∈ A) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hBad : (A \ Good).Nonempty) :
    24 * (∑ i ∈ A, w i) ≤
      5 * ∑ k ∈ A + A, hybridSupportDiagonalMax A M Good w k := by
  classical
  let Bad := A \ Good
  let G := ∑ i ∈ Good, hybridG K (w i)
  let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
  let T := ∑ i ∈ A, hybridT K (w i)
  let C := G + (Bad.card - 1) * hybridG K M
  let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
  let B := max C (max AA T)
  let LowSum := ∑ q ∈ Finset.range (2 * K),
    ((A + A).filter fun k =>
      q < hybridSupportDiagonalMax A M Good w k).card
  let HighSum := ∑ u ∈ Finset.range (2 * K),
    ((A + A).filter fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k).card
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hdisj : Disjoint Good Bad := Finset.disjoint_sdiff
  have hbaseA : base ∈ A := hGoodSub hbase
  have hANe : A.Nonempty := ⟨top, htop⟩
  have htopBase : ∃ i ∈ A, w i = K := ⟨top, htop, htopw⟩
  have hlow : 2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) ≤ LowSum := by
    exact support_baseline_layer_sum_lower (M := M) (Good := Good)
      hANe hmax htopBase
  have hcross : C ≤ HighSum := by
    dsimp only [C, G, Bad, HighSum]
    exact support_cross_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax hMK.le
  have hhigh : AA ≤ HighSum := by
    dsimp only [AA, G, AH, Bad, HighSum]
    exact support_high_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax htop htopw hMK hmax
  have hstar : T ≤ HighSum := by
    dsimp only [T, HighSum]
    exact support_top_star_layer_sum_lower hMK htop htopw hmax
  have hbonus : B ≤ HighSum := by
    dsimp only [B]
    exact max_le hcross (max_le hhigh hstar)
  have harith : 24 * (∑ i ∈ A, w i) ≤
      5 * (2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) + B) := by
    dsimp only [B, C, AA, G, AH, T, Bad]
    exact hybrid_five_arithmetic A Good w hAcard hGoodSub hbaseA htop
      hbase hbasew htopw hMK hmax hGoodMax
  have htoSums : 24 * (∑ i ∈ A, w i) ≤ 5 * (LowSum + HighSum) := by
    exact harith.trans (Nat.mul_le_mul_left 5 (Nat.add_le_add hlow hbonus))
  have hsplit := support_hybrid_layer_sum_split
    (A := A) (M := M) (Good := Good) hmax
  dsimp only [LowSum, HighSum] at htoSums
  rw [hsplit] at htoSums
  exact htoSums

/-- If a dense fibre is not largest, the hybrid five-layer estimate still
forces every fibre into a coset of the same subgroup. -/
theorem all_fibers_contained_of_support_five_maximal_dense
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {base top : ℕ}
    (hAcard : (firstCoordinateSet X).card = 5)
    (hsmall : 5 * (X + X).card < 12 * X.card)
    (hbase : base ∈ firstCoordinateSet X)
    (htop : top ∈ firstCoordinateSet X)
    (hbaseTop : (coordinateFiber X base).card < (coordinateFiber X top).card)
    (htopMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X top).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hGoodMax : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) →
        (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hpairHigh : ∀ i ∈ firstCoordinateSet X,
      ∀ j ∈ firstCoordinateSet X,
        (coordinateFiber X base).card <
          max (coordinateFiber X i).card (coordinateFiber X j).card →
        pairWeight (coordinateFiber X i).card (coordinateFiber X j).card ≤
          2 * (coordinateFiber X i + coordinateFiber X j).card) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let M := w base
  let K := w top
  let Good := A.filter fun a =>
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := A \ Good
  have hGoodSub : Good ⊆ A := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbase, hbaseCos⟩
  have hGood : ∀ a ∈ Good,
      ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hBadNot : ∀ a ∈ Bad,
      ¬ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha hcos
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨hBadSub ha, hcos⟩)
  intro a ha
  by_contra haNot
  have haBad : a ∈ Bad := Finset.mem_sdiff.mpr ⟨ha, by
    intro haGood
    exact haNot (hGood a haGood)⟩
  have hBadNe : Bad.Nonempty := ⟨a, haBad⟩
  have hMK : M < K := hbaseTop
  have hmax : ∀ i ∈ A, w i ≤ K := by
    intro i hi
    exact htopMax i hi
  have hGoodMax' : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hGoodMax i (hGoodSub hi) (hGood i hi)
  have hweight := hybrid_support_diagonal_weight_bound_five
    (A := A) (M := M) (K := K) (Good := Good) (w := w)
    (base := base) (top := top) (by simpa [A] using hAcard) hGoodSub
    hbaseGood rfl htop rfl hMK hmax hGoodMax' hBadNe
  let pair : {k // k ∈ A + A} → ℕ × ℕ :=
    hybridSupportMaxPair A M Good w
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ supportAntidiagonalPairs A k.1 := by
    intro k
    exact hybridSupportMaxPair_mem A M Good w k
  have hpairInA : ∀ k, (pair k).1 ∈ A ∧ (pair k).2 ∈ A := by
    intro k
    have hk := mem_supportAntidiagonalPairs.mp (hpairMem k)
    exact ⟨hk.1, hk.2.1⟩
  have hpairSum : ∀ k, (pair k).1 + (pair k).2 = k.1 := by
    intro k
    exact (mem_supportAntidiagonalPairs.mp (hpairMem k)).2.2
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    rw [← hpairSum i, ← hpairSum j, hij]
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    exact hpairInA k
  have hPinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hijVal : i.1 = j.1 := by simpa [hpairSum] using hpq
    have hij : i = j := Subtype.ext hijVal
    subst j
    rfl
  have hpoint : ∀ k : {k // k ∈ A + A},
      hybridPairWeight M Good w (pair k).1 (pair k).2 ≤
        2 * (coordinateFiber X (pair k).1 +
          coordinateFiber X (pair k).2).card := by
    intro k
    let i := (pair k).1
    let j := (pair k).2
    have hiA := (hpairInA k).1
    have hjA := (hpairInA k).2
    have hiNe := coordinateFiber_nonempty_iff.mpr hiA
    have hjNe := coordinateFiber_nonempty_iff.mpr hjA
    change hybridPairWeight M Good w i j ≤
      2 * (coordinateFiber X i + coordinateFiber X j).card
    unfold hybridPairWeight
    apply max_le
    · apply Nat.mul_le_mul_left 2
      by_cases hiG : i ∈ Good <;> by_cases hjG : j ∈ Good
      · simp only [relativeCosetPairHalf, if_pos hiG, if_pos hjG]
        exact max_le (Finset.card_le_card_add_right hjNe)
          (Finset.card_le_card_add_left hiNe)
      · rw [relativeCosetPairHalf_of_good_bad hiG hjG]
        apply max_le
        · exact two_mul_card_le_add_of_coset_and_not_coset hiNe hjNe
            (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr ⟨hjA, hjG⟩))
        · exact Finset.card_le_card_add_left hiNe
      · have htwo := two_mul_card_le_add_of_coset_and_not_coset
            hjNe hiNe (hGood j hjG)
              (hBadNot i (Finset.mem_sdiff.mpr ⟨hiA, hiG⟩))
        simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
        apply max_le
        · exact Finset.card_le_card_add_right hjNe
        · simpa [add_comm] using htwo
      · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
        exact max_le (Finset.card_le_card_add_right hjNe)
          (Finset.card_le_card_add_left hiNe)
    · split_ifs with hhigh
      · exact hpairHigh i hiA j hjA hhigh
      · omega
  have hdiagToFiber :
      (∑ k : {k // k ∈ A + A},
          hybridSupportDiagonalMax A M Good w k.1) ≤
        ∑ k : {k // k ∈ A + A},
          2 * (coordinateFiber X (pair k).1 +
            coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← hybridSupportMaxPair_realizes A M Good w k]
    exact hpoint k
  have hfinToP : (∑ k : {k // k ∈ A + A},
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card) =
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp only [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hdiag : (∑ k ∈ A + A,
        hybridSupportDiagonalMax A M Good w k) ≤ 2 * (X + X).card := by
    rw [Finset.sum_subtype (p := fun k => k ∈ A + A)
      (s := A + A) (by simp)]
    rw [← Finset.mul_sum] at hdiagToFiber
    rw [hfinToP] at hdiagToFiber
    exact hdiagToFiber.trans (Nat.mul_le_mul_left 2 hPsum)
  have hXcard : X.card = ∑ i ∈ A, w i :=
    card_eq_sum_card_coordinateFiber X
  have hlarge : 24 * X.card ≤ 10 * (X + X).card := by
    rw [hXcard]
    have hdiag' := Nat.mul_le_mul_left 5 hdiag
    exact hweight.trans (by omega)
  omega

/-- If a five-layer core has a dense coset in a largest fibre, every fibre
lies in a coset of that same subgroup. -/
theorem all_fibers_contained_of_support_five_largest
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {base : ℕ}
    (hAcard : (firstCoordinateSet X).card = 5)
    (hsmall : 5 * (X + X).card < 12 * X.card)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base)) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let w : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let M := w base
  let Good := A.filter fun a ↦
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := A \ Good
  have hGoodSub : Good ⊆ A := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbase, hbaseCos⟩
  have hpart : Good ∪ Bad = A := Finset.union_sdiff_of_subset hGoodSub
  have hdisj : Disjoint Good Bad := Finset.disjoint_sdiff
  have hGood : ∀ a ∈ Good,
      ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hBadNot : ∀ a ∈ Bad,
      ¬ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha hcos
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨hBadSub ha, hcos⟩)
  intro a ha
  by_contra haNot
  have haBad : a ∈ Bad := Finset.mem_sdiff.mpr ⟨ha, by
    intro haGood
    exact haNot (hGood a haGood)⟩
  have hBadNe : Bad.Nonempty := ⟨a, haBad⟩
  have hMpos : 0 < M := by
    dsimp only [M, w]
    exact Finset.card_pos.mpr (coordinateFiber_nonempty_iff.mpr hbase)
  have hmax : ∀ i ∈ A, w i ≤ M := by
    intro i hi
    exact hbaseMax i hi
  have hweight := relative_support_diagonal_weight_bound_five
    (A := A) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    (by simpa [A] using hAcard) hMpos hpart hdisj hbaseGood rfl hmax hBadNe
  let pair : {k // k ∈ A + A} → ℕ × ℕ := relativeSupportMaxPair A Good w
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ supportAntidiagonalPairs A k.1 := by
    intro k
    exact relativeSupportMaxPair_mem A Good w k
  have hpairInA : ∀ k, (pair k).1 ∈ A ∧ (pair k).2 ∈ A := by
    intro k
    have hk := mem_supportAntidiagonalPairs.mp (hpairMem k)
    exact ⟨hk.1, hk.2.1⟩
  have hpairSum : ∀ k, (pair k).1 + (pair k).2 = k.1 := by
    intro k
    exact (mem_supportAntidiagonalPairs.mp (hpairMem k)).2.2
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    rw [← hpairSum i, ← hpairSum j, hij]
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    exact hpairInA k
  have hPinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hijVal : i.1 = j.1 := by simpa [hpairSum] using hpq
    have hij : i = j := Subtype.ext hijVal
    subst j
    rfl
  have hpoint : ∀ k : {k // k ∈ A + A},
      relativeCosetPairHalf Good w (pair k).1 (pair k).2 ≤
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    intro k
    let i := (pair k).1
    let j := (pair k).2
    have hiA := (hpairInA k).1
    have hjA := (hpairInA k).2
    have hiNe := coordinateFiber_nonempty_iff.mpr hiA
    have hjNe := coordinateFiber_nonempty_iff.mpr hjA
    change relativeCosetPairHalf Good w i j ≤
      (coordinateFiber X i + coordinateFiber X j).card
    by_cases hiG : i ∈ Good <;> by_cases hjG : j ∈ Good
    · simp only [relativeCosetPairHalf, if_pos hiG, if_pos hjG]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
    · rw [relativeCosetPairHalf_of_good_bad hiG hjG]
      apply max_le
      · exact two_mul_card_le_add_of_coset_and_not_coset hiNe hjNe
          (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr ⟨hjA, hjG⟩))
      · exact Finset.card_le_card_add_left hiNe
    · have htwo := two_mul_card_le_add_of_coset_and_not_coset
          hjNe hiNe (hGood j hjG)
            (hBadNot i (Finset.mem_sdiff.mpr ⟨hiA, hiG⟩))
      simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
      apply max_le
      · exact Finset.card_le_card_add_right hjNe
      · simpa [add_comm] using htwo
    · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
  have hdiagToFiber :
      (∑ k : {k // k ∈ A + A},
          relativeSupportDiagonalMax A Good w k.1) ≤
        ∑ k : {k // k ∈ A + A},
          (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← relativeSupportMaxPair_realizes A Good w k]
    exact hpoint k
  have hfinToP : (∑ k : {k // k ∈ A + A},
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card) =
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp only [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hdiag : (∑ k ∈ A + A,
        relativeSupportDiagonalMax A Good w k) ≤ (X + X).card := by
    rw [Finset.sum_subtype (p := fun k ↦ k ∈ A + A)
      (s := A + A) (by simp)]
    exact hdiagToFiber.trans (hfinToP.le.trans hPsum)
  have hXcard : X.card = ∑ i ∈ A, w i := card_eq_sum_card_coordinateFiber X
  have hlarge : 12 * X.card ≤ 5 * (X + X).card := by
    rw [hXcard]
    exact hweight.trans (Nat.mul_le_mul_left 5 hdiag)
  omega

/-- A pair selection whose sharp pair weights total at least `5|X|` forces a
dense subgroup coset in one of its endpoint fibres whenever `|2X|<5|X|/2`.
-/
lemma exists_dense_fiber_coset_of_pairWeight_selection
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (P : Finset (ℕ × ℕ))
    (hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X)
    (hPinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P)
    (hPweight :
      5 * (∑ a ∈ firstCoordinateSet X,
        (coordinateFiber X a).card) ≤
      ∑ p ∈ P, pairWeight
        (coordinateFiber X p.1).card (coordinateFiber X p.2).card)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  by_contra hno
  push Not at hno
  have hpoint : ∀ p ∈ P,
      pairWeight (coordinateFiber X p.1).card
          (coordinateFiber X p.2).card ≤
        2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    intro p hp
    have hpM := hPmem p hp
    have hleft : (coordinateFiber X p.1).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.1
    have hright : (coordinateFiber X p.2).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.2
    rcases dense_coset_or_pairWeight_le hleft hright with hbad | hgood
    · obtain ⟨H, hbad | hbad⟩ := hbad
      · have hnot := hno p.1 hpM.1 H hbad.1
        omega
      · have hnot := hno p.2 hpM.2 H hbad.1
        omega
    · exact hgood
  have hweightSum :
      (∑ p ∈ P, pairWeight (coordinateFiber X p.1).card
        (coordinateFiber X p.2).card) ≤
        2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    calc
      (∑ p ∈ P, pairWeight (coordinateFiber X p.1).card
          (coordinateFiber X p.2).card) ≤
          ∑ p ∈ P,
            2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card :=
        Finset.sum_le_sum hpoint
      _ = 2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
        rw [Finset.mul_sum]
  have hpairSum :
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hXcard : X.card = ∑ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card := card_eq_sum_card_coordinateFiber X
  have hlarge : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hPweight.trans
      (hweightSum.trans (Nat.mul_le_mul_left 2 hpairSum))
  omega

/-- The only five-point `R=3` supports are `[0,5]` with one internal hole.
For each of the four holes, five diagonals and five explicitly chosen cross
pairs occupy ten distinct antidiagonals and charge every fibre at least five
times. -/
theorem exists_dense_fiber_coset_of_oneHole_support_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {h : ℕ}
    (hhpos : 0 < h) (hhfive : h < 5)
    (hsupport : firstCoordinateSet X = (Finset.range 6).erase h)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  exact exists_dense_fiber_coset_of_oneHole_support X (s := 5)
    (by omega) hhpos hhfive hsupport hsmall

/-- The interval (`R=2`) five-layer support is already covered by the
generic interval pair-selection theorem. -/
theorem exists_dense_fiber_coset_of_five_layers_R_eq_two
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hR2 : min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card = 2)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let s := A.card
  let M := A.max' hA
  have hs : s = 5 := by simpa [s, A] using hAcard
  have hAmax : s ≤ M + 1 := by
    have hsub : A ⊆ Finset.range (M + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    simpa [s, M] using Finset.card_le_card hsub
  have htwoLeft : 2 ≤ M + 3 - s := by
    have hmin := Nat.min_le_left (M + 3 - s) s
    simpa [A, M, s, hR2] using hmin
  have hleftTwo : M + 3 - s ≤ 2 := by
    by_contra hnot
    have htwoS : 2 < s := by omega
    have htwoL : 2 < M + 3 - s := Nat.lt_of_not_ge hnot
    have := lt_min htwoL htwoS
    rw [show min (M + 3 - s) s = 2 by simpa [A, M, s] using hR2] at this
    omega
  have hMs : M + 1 = s := by omega
  have hsupport : A = Finset.range s := by
    have hsub : A ⊆ Finset.range s := by
      intro a ha
      rw [← hMs]
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    apply Finset.eq_of_subset_of_card_le hsub
    simp [s]
  apply exists_dense_fiber_coset_of_interval_support X (n := s) (by omega)
  · simpa [A] using hsupport
  · exact hsmall

/-- At five layers and `R≥4`, the sharp `12/5` inequality closes the
largest-fibre Hall argument. -/
theorem exists_dense_largestFiber_coset_of_five_layers_four_le_R
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    {base : ℕ} (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hR4 : 4 ≤ min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let M := F base
  let R := min (A.max' hA + 3 - A.card) A.card
  let k := R - 1
  obtain ⟨D, hDA, hDbase, hDcard, hDle, havg⟩ :=
    exists_weighted_distinguishedLayerSet X hA hbase
  by_contra hno
  have huniform := layerHall_uniform_fiber_lower X hA hAzero
    (by simpa [A] using hAcard.ge) hgcd hbase hbaseMax hDA hDbase hDle hno
  have hhall := layerHall_weighted_fiber_lower X hA hAzero
    (by have := hAcard.ge; simpa [A] using (show 3 ≤ 5 by omega).trans this)
    hgcd hbase hDA hDbase hDle
  have hXcard : X.card = ∑ a ∈ A, F a := by
    simpa [A, F] using card_eq_sum_card_coordinateFiber X
  have hsplit : X.card = M + ∑ a ∈ A.erase base, F a := by
    rw [hXcard]
    dsimp only [M]
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  let P := ∑ a ∈ A.erase base, F a
  let Q := ∑ a ∈ D, F a
  have hR4' : 4 ≤ R := by simpa [R, A] using hR4
  have hk3 : 3 ≤ k := by dsimp only [k]; omega
  have havg' : k * P ≤ 4 * Q := by
    simpa [A, F, R, k, P, Q, hAcard] using havg
  have hpq : 3 * P ≤ 4 * Q :=
    (Nat.mul_le_mul_right P hk3).trans havg'
  have hu : 4 * X.card + 2 * Q ≤ 2 * (X + X).card := by
    simpa [A, F, M, Q, hAcard] using huniform
  have hh : 3 * M + Q + X.card ≤ (X + X).card := by
    simpa [A, F, M, Q, hAcard] using hhall
  dsimp only [P, M] at hpq hsplit
  omega

/-- Complete dense-fibre existence for a normalized five-layer core. -/
theorem exists_dense_fiber_coset_of_five_layers
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let R := min (A.max' hA + 3 - A.card) A.card
  have hAcard' : A.card = 5 := by simpa [A] using hAcard
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.range (A.max' hA + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    simpa using Finset.card_le_card hsub
  have hRge : 2 ≤ R := by
    apply Nat.le_min.mpr
    constructor <;> omega
  have hold : 2 * (X + X).card < 5 * X.card := by omega
  by_cases hR2 : R = 2
  · apply exists_dense_fiber_coset_of_five_layers_R_eq_two X hA hAcard
    · simpa [R, A] using hR2
    · exact hold
  by_cases hR3 : R = 3
  · let s := A.card
    let M := A.max' hA
    have hs : s = 5 := by simpa [s, A] using hAcard
    have hthreeLeft : 3 ≤ M + 3 - s := by
      have hmin := Nat.min_le_left (M + 3 - s) s
      rw [show min (M + 3 - s) s = 3 by simpa [R, A, M, s] using hR3] at hmin
      exact hmin
    have hleftThree : M + 3 - s ≤ 3 := by
      by_contra hnot
      have hthreeS : 3 < s := by omega
      have hthreeL : 3 < M + 3 - s := Nat.lt_of_not_ge hnot
      have := lt_min hthreeL hthreeS
      rw [show min (M + 3 - s) s = 3 by simpa [R, A, M, s] using hR3] at this
      omega
    have hMs : M = s := by omega
    have hsub : A ⊆ Finset.range (s + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    have hdiffcard : (Finset.range (s + 1) \ A).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]
      simp only [Finset.card_range]
      simp only [s]
      omega
    obtain ⟨h, hdiff⟩ := Finset.card_eq_one.mp hdiffcard
    have hhdiff : h ∈ Finset.range (s + 1) \ A := by rw [hdiff]; simp
    have hhRange : h ∈ Finset.range (s + 1) := (Finset.mem_sdiff.mp hhdiff).1
    have hhnotA : h ∉ A := (Finset.mem_sdiff.mp hhdiff).2
    have hsupport : A = (Finset.range (s + 1)).erase h := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_erase]
        refine ⟨?_, hsub hx⟩
        intro hxh
        subst x
        exact hhnotA hx
      · intro hx
        rw [Finset.mem_erase] at hx
        by_contra hxA
        have hxin : x ∈ Finset.range (s + 1) \ A :=
          Finset.mem_sdiff.mpr ⟨hx.2, hxA⟩
        rw [hdiff] at hxin
        have : x = h := by simpa using hxin
        exact hx.1 this
    have hhpos : 0 < h := by
      by_contra hnot
      have hh0 : h = 0 := Nat.eq_zero_of_not_pos hnot
      apply hhnotA
      simpa [A, hh0] using hAzero
    have hhfive : h < 5 := by
      have hhLe : h ≤ s := by simpa [Finset.mem_range] using hhRange
      have hMmem : M ∈ A := A.max'_mem hA
      have hsA : s ∈ A := by simpa [hMs] using hMmem
      have hhne : h ≠ s := by
        intro heq
        apply hhnotA
        simpa [heq] using hsA
      omega
    apply exists_dense_fiber_coset_of_oneHole_support_five X hhpos hhfive
    · simpa [A, hs] using hsupport
    · exact hold
  · obtain ⟨base, hbase, hbaseMax⟩ :=
      Finset.exists_max_image A (fun a ↦ (coordinateFiber X a).card) hA
    obtain ⟨H, hcos, hdense⟩ :=
      exists_dense_largestFiber_coset_of_five_layers_four_le_R
        X hA hAzero hAcard hgcd (by simpa [A] using hbase)
        (by simpa [A] using hbaseMax)
        (by simpa [R, A] using (show 4 ≤ R by omega)) hsmall
    exact ⟨base, by simpa [A] using hbase, H, hcos, hdense⟩

/-- Complete common-coset coherence for a normalized five-layer core. -/
theorem exists_common_dense_coset_of_small_doubling_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        ∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let Dense := A.filter fun a => ∃ H : AddSubgroup (ZMod d),
    ContainedInAddCoset H (coordinateFiber X a) ∧
      2 * Nat.card H < 3 * (coordinateFiber X a).card
  obtain ⟨a, ha, H₀, haCos, hH₀card⟩ :=
    exists_dense_fiber_coset_of_five_layers X hA hAzero hAcard hgcd hsmall
  have haDense : a ∈ Dense :=
    Finset.mem_filter.mpr ⟨ha, ⟨H₀, haCos, hH₀card⟩⟩
  have hDenseNe : Dense.Nonempty := ⟨a, haDense⟩
  obtain ⟨base, hbaseDense, hbaseMaxDense⟩ :=
    Finset.exists_max_image Dense F hDenseNe
  have hbase : base ∈ firstCoordinateSet X :=
    (Finset.mem_filter.mp hbaseDense).1
  obtain ⟨H, hbaseCos, hHcard⟩ :=
    (Finset.mem_filter.mp hbaseDense).2
  obtain ⟨top, htop, htopMax⟩ :=
    Finset.exists_max_image (firstCoordinateSet X) F hA
  have hbaseLeTop : F base ≤ F top := htopMax base hbase
  by_cases hEq : F base = F top
  · have hbaseMax : ∀ z ∈ firstCoordinateSet X, F z ≤ F base := by
      intro z hz
      exact (htopMax z hz).trans_eq hEq.symm
    refine ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, ?_⟩
    exact all_fibers_contained_of_support_five_largest X hAcard hsmall
      hbase hbaseMax hbaseCos
  · have hbaseTop : F base < F top := by omega
    have hGoodMax : ∀ z ∈ firstCoordinateSet X,
        ContainedInAddCoset H (coordinateFiber X z) → F z ≤ F base := by
      intro z hz hzCos
      by_contra hzNot
      have hbaseZ : F base < F z := Nat.lt_of_not_ge hzNot
      have hzDense : z ∈ Dense := Finset.mem_filter.mpr ⟨hz, ⟨H, hzCos, by
        have := hHcard
        dsimp only [F] at hbaseZ ⊢
        omega⟩⟩
      exact (Nat.not_lt_of_ge (hbaseMaxDense z hzDense)) hbaseZ
    have hpairHigh : ∀ i ∈ firstCoordinateSet X,
        ∀ j ∈ firstCoordinateSet X,
          F base < max (F i) (F j) →
            pairWeight (F i) (F j) ≤
              2 * (coordinateFiber X i + coordinateFiber X j).card := by
      intro i hi j hj hhigh
      have hiNe := coordinateFiber_nonempty_iff.mpr hi
      have hjNe := coordinateFiber_nonempty_iff.mpr hj
      rcases le_total (F j) (F i) with hji | hij
      · rcases small_coset_or_largestPairWeight_le hiNe hjNe hji with
          hdense | hsum
        · obtain ⟨H', hiCos, hH'card⟩ := hdense
          have hiDense : i ∈ Dense :=
            Finset.mem_filter.mpr ⟨hi, ⟨H', hiCos, by simpa [F] using hH'card⟩⟩
          have hiLe := hbaseMaxDense i hiDense
          rw [max_eq_left hji] at hhigh
          omega
        · simpa [pairWeight, max_eq_left hji, min_eq_right hji, F] using hsum
      · rcases small_coset_or_largestPairWeight_le hjNe hiNe hij with
          hdense | hsum
        · obtain ⟨H', hjCos, hH'card⟩ := hdense
          have hjDense : j ∈ Dense :=
            Finset.mem_filter.mpr ⟨hj, ⟨H', hjCos, by simpa [F] using hH'card⟩⟩
          have hjLe := hbaseMaxDense j hjDense
          rw [max_eq_right hij] at hhigh
          omega
        · simpa [pairWeight, max_eq_right hij, min_eq_left hij, F,
            add_comm] using hsum
    have hAll : ∀ z ∈ firstCoordinateSet X,
        ContainedInAddCoset H (coordinateFiber X z) := by
      apply all_fibers_contained_of_support_five_maximal_dense X hAcard hsmall
        hbase htop
      · simpa [F] using hbaseTop
      · intro z hz
        simpa [F] using htopMax z hz
      · exact hbaseCos
      · intro z hz hzCos
        simpa [F] using hGoodMax z hz hzCos
      · intro i hi j hj hhigh
        simpa [F] using hpairHigh i hi j hj (by simpa [F] using hhigh)
    have htopLe : F top ≤ F base := hGoodMax top htop (hAll top htop)
    omega

/-- The five-layer common subgroup has the same coarse mass bound used by
the high-support cyclic inverse theorem. -/
theorem exists_common_dense_coset_with_mass_bound_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        (∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a)) ∧
        (firstCoordinateSet X).card * Nat.card H ≤
          4 * ((X + X).card - X.card) := by
  classical
  obtain ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, hAll⟩ :=
    exists_common_dense_coset_of_small_doubling_five
      X hA hAzero hAcard hgcd hsmall
  have hHall := layerHall_weighted_fiber_lower X hA hAzero
    (by omega : 3 ≤ (firstCoordinateSet X).card) hgcd hbase
    (D := ∅) (by simp) (by simp) (by simp)
  have hdiff :
      ((firstCoordinateSet X).card - 2) *
          (coordinateFiber X base).card ≤ (X + X).card - X.card := by
    simpa only [Finset.sum_empty, zero_add, add_zero] using
      (Nat.le_sub_of_add_le hHall)
  have hHle : Nat.card H ≤ 2 * (coordinateFiber X base).card := by omega
  have hs : (firstCoordinateSet X).card ≤
      2 * ((firstCoordinateSet X).card - 2) := by omega
  have hmass : (firstCoordinateSet X).card * Nat.card H ≤
      4 * ((X + X).card - X.card) := by
    calc
      (firstCoordinateSet X).card * Nat.card H ≤
          (firstCoordinateSet X).card *
            (2 * (coordinateFiber X base).card) :=
        Nat.mul_le_mul_left _ hHle
      _ ≤ 4 * (((firstCoordinateSet X).card - 2) *
            (coordinateFiber X base).card) := by
        nlinarith
      _ ≤ 4 * ((X + X).card - X.card) :=
        Nat.mul_le_mul_left 4 hdiff
  exact ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, hAll, hmass⟩

/-- Sharp five-layer support-span bound. -/
theorem fiber_span_lt_three_halves_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    2 * (firstCoordinateSet X).max' hA <
      3 * (firstCoordinateSet X).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  have hAcardA : A.card = 5 := by simpa [A] using hAcard
  obtain ⟨base, hbase, hbaseMax⟩ :=
    Finset.exists_max_image A F (by simpa [A] using hA)
  by_contra hnot
  have hMlarge : 8 ≤ A.max' (by simpa [A] using hA) := by
    have hnotA : ¬2 * A.max' (by simpa [A] using hA) < 3 * A.card := by
      simpa [A] using hnot
    have : 3 * A.card ≤ 2 * A.max' (by simpa [A] using hA) := by
      exact Nat.le_of_not_gt hnotA
    omega
  let D := A.erase base
  have hDA : D ⊆ A := Finset.erase_subset _ _
  have hDbase : base ∉ D := by simp [D]
  have hDcard : D.card = 4 := by
    simp [D, Finset.card_erase_of_mem hbase, hAcardA]
  have hDle : D.card ≤ A.max' (by simpa [A] using hA) + 2 - A.card := by
    rw [hDcard, hAcardA]
    omega
  have hHall := layerHall_weighted_fiber_lower X hA hAzero
    (by omega : 3 ≤ (firstCoordinateSet X).card) hgcd
    (by simpa [A] using hbase) (by simpa [A, D] using hDA)
    (by simpa [A, D] using hDbase) (by simpa [A, D] using hDle)
  have hXcard : X.card = F base + ∑ a ∈ D, F a := by
    rw [card_eq_sum_card_coordinateFiber X]
    dsimp only [D]
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  have hP : (∑ a ∈ D, F a) ≤ 4 * F base := by
    calc
      ∑ a ∈ D, F a ≤ ∑ _a ∈ D, F base := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbaseMax a (hDA ha)
      _ = 4 * F base := by simp [hDcard]
  have hHall' : 3 * F base + (∑ a ∈ D, F a) + X.card ≤
      (X + X).card := by
    simpa [A, F, D, hAcardA] using hHall
  omega

end Erdos360

#print axioms Erdos360.exists_dense_fiber_coset_of_five_layers
