import ErdosProblems.Erdos546.Basic
import ErdosProblems.Erdos546.Numeric

/-!
# Balanced block families for Erdős Problem 546

This file isolates the finite counting part of the Fox--Sudakov
sparsification argument.  All densities are kept denominator-free.

The lemma `exists_balanced_subset` is the averaging step which is easy to
miss in a paper proof: an arbitrary subset of a sparse pair need not remain
sparse.  It chooses a prescribed number of points without increasing the
average of an arbitrary non-negative integral weight.  Applying it at the
two ends of a bipartite graph gives `exists_balanced_pair_trim`.

`EqualBlockFamily` and `familyEdgeCount` package the exact block count used
in a dyadic iteration.  The diagonal terms are the internal ordered edges
of the blocks and the off-diagonal terms are the cross-edges.  Thus
`squareEdgeCount_biUnion_eq_familyEdgeCount` has no hidden factor of two.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset SimpleGraph

/-! ## Averaging with a prescribed cardinality -/

/-- A prescribed-size subset whose integral weight is at most the ambient
average.  This is the denominator-free form of
`average(T) ≤ average(U)`.

The proof removes a point of maximum weight and uses strong induction.  In
particular, it does not claim that an arbitrary subset has this property. -/
theorem exists_balanced_subset {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℕ) {s : ℕ} (hs : s ≤ U.card) :
    ∃ T : Finset α, T ⊆ U ∧ T.card = s ∧
      U.card * (∑ x ∈ T, w x) ≤ s * (∑ x ∈ U, w x) := by
  refine Finset.strongInduction (p := fun U ↦ ∀ s, s ≤ U.card →
      ∃ T : Finset α, T ⊆ U ∧ T.card = s ∧
        U.card * (∑ x ∈ T, w x) ≤ s * (∑ x ∈ U, w x)) ?_ U s hs
  intro U ih s hs
  by_cases hs0 : s = 0
  · subst s
    exact ⟨∅, empty_subset _, by simp, by simp⟩
  by_cases hsa : s = U.card
  · subst s
    exact ⟨U, Subset.rfl, rfl, le_rfl⟩
  have hsa' : s < U.card := by omega
  have hUne : U.Nonempty := by
        rw [← card_pos]
        omega
  obtain ⟨x, hxU, hxmax⟩ := U.exists_max_image w hUne
  let V := U.erase x
  have hVcard : V.card = U.card - 1 := by
        simp [V, Finset.card_erase_of_mem hxU]
  have ha2 : 2 ≤ U.card := by omega
  have hsV : s ≤ V.card := by omega
  obtain ⟨T, hTV, hTcard, hTavg⟩ :=
        ih V (Finset.erase_ssubset hxU) s hsV
  refine ⟨T, hTV.trans (erase_subset _ _), hTcard, ?_⟩
  let W := ∑ y ∈ V, w y
  let Z := ∑ y ∈ T, w y
  have hsumU : (∑ y ∈ U, w y) = W + w x := by
    rw [← Finset.sum_erase_add _ _ hxU]
  have hsumMax : (∑ y ∈ U, w y) ≤ U.card * w x := by
        calc
          (∑ y ∈ U, w y) ≤ ∑ _y ∈ U, w x :=
            sum_le_sum fun y hy ↦ hxmax y hy
          _ = U.card * w x := by simp
  have hW : W ≤ (U.card - 1) * w x := by
        rw [hsumU] at hsumMax
        rw [show U.card = (U.card - 1) + 1 by omega,
          add_mul, one_mul] at hsumMax
        omega
  have haW : U.card * W ≤ (U.card - 1) * (∑ y ∈ U, w y) := by
        calc
          U.card * W = (U.card - 1) * W + W := by
            rw [show U.card = (U.card - 1) + 1 by omega]
            simp [add_mul]
          _ ≤ (U.card - 1) * W + (U.card - 1) * w x :=
            Nat.add_le_add_left hW _
          _ = (U.card - 1) * (∑ y ∈ U, w y) := by
            rw [hsumU]
            rw [Nat.mul_add]
  have hTZ : (U.card - 1) * Z ≤ s * W := by
        simpa [hVcard, W, Z] using hTavg
  have hmul : (U.card - 1) * (U.card * Z) ≤
          (U.card - 1) * (s * (∑ y ∈ U, w y)) := by
        calc
          (U.card - 1) * (U.card * Z) =
              U.card * ((U.card - 1) * Z) := by ring
          _ ≤ U.card * (s * W) := Nat.mul_le_mul_left U.card hTZ
          _ = s * (U.card * W) := by ring
          _ ≤ s * ((U.card - 1) * (∑ y ∈ U, w y)) :=
            Nat.mul_le_mul_left s haW
          _ = (U.card - 1) * (s * (∑ y ∈ U, w y)) := by ring
  have hcancel : U.card * Z ≤ s * (∑ y ∈ U, w y) :=
        Nat.le_of_mul_le_mul_left hmul (by omega)
  simpa [Z] using hcancel

/-! ## Converting graph edge counts to iterated sums -/

private theorem crossEdgeCount_eq_card_interedges {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y = (H.interedges X Y).card := by
  rw [crossEdgeCount]
  congr

/-- Ordered cross-edges are the sum of the `0/1` adjacency weights. -/
theorem crossEdgeCount_eq_sum {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y =
      ∑ x ∈ X, ∑ y ∈ Y, if H.Adj x y then 1 else 0 := by
  classical
  rw [crossEdgeCount_eq_card_interedges]
  rw [SimpleGraph.interedges_def, Finset.card_filter, Finset.sum_product]

/-- **Balanced two-sided trimming.**  If both sides initially have size `a`,
they can be trimmed to size `s` so that the cross-edge count drops by the
square of the cardinality ratio.  Arbitrary trimming does not satisfy this
inequality. -/
theorem exists_balanced_pair_trim {N a s : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (X Y : Finset (Fin N)) (hX : X.card = a) (hY : Y.card = a)
    (hsa : s ≤ a) :
    ∃ X' Y' : Finset (Fin N),
      X' ⊆ X ∧ Y' ⊆ Y ∧ X'.card = s ∧ Y'.card = s ∧
        a ^ 2 * crossEdgeCount H X' Y' ≤
          s ^ 2 * crossEdgeCount H X Y := by
  classical
  let wX : Fin N → ℕ := fun x ↦ ∑ y ∈ Y, if H.Adj x y then 1 else 0
  obtain ⟨X', hX'X, hX'card, hX'avg⟩ :=
    exists_balanced_subset X wX (by simpa [hX] using hsa)
  let wY : Fin N → ℕ := fun y ↦ ∑ x ∈ X', if H.Adj y x then 1 else 0
  obtain ⟨Y', hY'Y, hY'card, hY'avg⟩ :=
    exists_balanced_subset Y wY (by simpa [hY] using hsa)
  refine ⟨X', Y', hX'X, hY'Y, hX'card, hY'card, ?_⟩
  have hfirst : a * crossEdgeCount H X' Y ≤
      s * crossEdgeCount H X Y := by
    rw [crossEdgeCount_eq_sum, crossEdgeCount_eq_sum]
    simpa [hX, hX'card, wX] using hX'avg
  have hsecond : a * crossEdgeCount H X' Y' ≤
      s * crossEdgeCount H X' Y := by
    rw [crossEdgeCount_comm H X' Y', crossEdgeCount_comm H X' Y]
    rw [crossEdgeCount_eq_sum, crossEdgeCount_eq_sum]
    simpa [hY, hY'card, wY] using hY'avg
  calc
    a ^ 2 * crossEdgeCount H X' Y' =
        a * (a * crossEdgeCount H X' Y') := by ring
    _ ≤ a * (s * crossEdgeCount H X' Y) :=
      Nat.mul_le_mul_left a hsecond
    _ = s * (a * crossEdgeCount H X' Y) := by ring
    _ ≤ s * (s * crossEdgeCount H X Y) :=
      Nat.mul_le_mul_left s hfirst
    _ = s ^ 2 * crossEdgeCount H X Y := by ring

/-! ## The low-degree half used in the Fox--Sudakov composition -/

/-- Number of neighbours of `x` in `Y`. -/
def crossDegree {N : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (Y : Finset (Fin N)) (x : Fin N) : ℕ :=
  (Y.filter (H.Adj x)).card

theorem crossEdgeCount_eq_sum_crossDegree {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y = ∑ x ∈ X, crossDegree H Y x := by
  rw [crossEdgeCount_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [crossDegree, Finset.card_filter]

/-- Markov's inequality in the exact form used at a binary split.  If the
average degree is at most `|Y|/(2C)`, at least half of `X` has degree at
most `|Y|/C`; hence any requested `t ≤ |X|/2` can be retained pointwise. -/
theorem exists_lowDegree_subset {N C t : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (X Y : Finset (Fin N)) (hY : 0 < Y.card)
    (hcross : 2 * C * crossEdgeCount H X Y ≤ X.card * Y.card)
    (ht : 2 * t ≤ X.card) :
    ∃ T : Finset (Fin N), T ⊆ X ∧ T.card = t ∧
      ∀ x ∈ T, C * crossDegree H Y x ≤ Y.card := by
  classical
  let good := X.filter fun x ↦ C * crossDegree H Y x ≤ Y.card
  let bad := X.filter fun x ↦ Y.card < C * crossDegree H Y x
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro x hxg hxb
    simp only [good, bad, Finset.mem_filter] at hxg hxb
    omega
  have hunion : good ∪ bad = X := by
    ext x
    simp only [good, bad, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases h : C * crossDegree H Y x ≤ Y.card
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, Nat.lt_of_not_ge h⟩
  have hcards : good.card + bad.card = X.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hbadPoint : ∀ x ∈ bad,
      Y.card + 1 ≤ C * crossDegree H Y x := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    omega
  have hbadSum : bad.card * (Y.card + 1) ≤
      C * crossEdgeCount H X Y := by
    calc
      bad.card * (Y.card + 1) = ∑ _x ∈ bad, (Y.card + 1) := by simp
      _ ≤ ∑ x ∈ bad, C * crossDegree H Y x :=
        Finset.sum_le_sum hbadPoint
      _ = C * ∑ x ∈ bad, crossDegree H Y x := by
        rw [Finset.mul_sum]
      _ ≤ C * ∑ x ∈ X, crossDegree H Y x := by
        apply Nat.mul_le_mul_left
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ Nat.zero_le _)
      _ = C * crossEdgeCount H X Y := by
        rw [crossEdgeCount_eq_sum_crossDegree]
  have hbadMul : (2 * bad.card) * Y.card ≤ X.card * Y.card := by
    calc
      (2 * bad.card) * Y.card ≤ 2 * (bad.card * (Y.card + 1)) := by
        nlinarith
      _ ≤ 2 * (C * crossEdgeCount H X Y) :=
        Nat.mul_le_mul_left 2 hbadSum
      _ = 2 * C * crossEdgeCount H X Y := by ring
      _ ≤ X.card * Y.card := hcross
  have hbadCard : 2 * bad.card ≤ X.card :=
    Nat.le_of_mul_le_mul_right hbadMul hY
  have htgood : t ≤ good.card := by omega
  obtain ⟨T, hTgood, hTcard⟩ := Finset.exists_subset_card_eq htgood
  refine ⟨T, hTgood.trans (Finset.filter_subset _ _), hTcard, ?_⟩
  intro x hxT
  exact (Finset.mem_filter.mp (hTgood hxT)).2

/-! ## Exact equal block families -/

/-- A finite family of nonempty, pairwise-disjoint blocks of one common
cardinality. -/
structure EqualBlockFamily (α : Type*) [DecidableEq α] where
  blocks : Finset (Finset α)
  blockSize : ℕ
  blockSize_pos : 0 < blockSize
  card_eq : ∀ B ∈ blocks, B.card = blockSize
  pairwiseDisjoint : (↑blocks : Set (Finset α)).PairwiseDisjoint id

namespace EqualBlockFamily

variable {α : Type*} [DecidableEq α]

/-- The set covered by all blocks. -/
def carrier (F : EqualBlockFamily α) : Finset α := F.blocks.biUnion id

/-- The blocks as a genuine finite partition of their carrier. -/
def toFinpartition (F : EqualBlockFamily α) : Finpartition F.carrier where
  parts := F.blocks
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr F.pairwiseDisjoint
  sup_parts := by simp [carrier, Finset.sup_eq_biUnion]
  bot_notMem := by
    intro h
    have hz : 0 = F.blockSize := by simpa using F.card_eq ∅ h
    exact (Nat.ne_of_gt F.blockSize_pos) hz.symm

@[simp] theorem parts_toFinpartition (F : EqualBlockFamily α) :
    F.toFinpartition.parts = F.blocks := rfl

/-- Pairwise disjointness makes the carrier cardinality exactly the number
of blocks times the common block size. -/
theorem card_carrier (F : EqualBlockFamily α) :
    F.carrier.card = F.blocks.card * F.blockSize := by
  rw [carrier, Finset.card_biUnion F.pairwiseDisjoint]
  calc
    (∑ B ∈ F.blocks, B.card) = ∑ _B ∈ F.blocks, F.blockSize := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [F.card_eq B hB]
    _ = F.blocks.card * F.blockSize := by simp

end EqualBlockFamily

/-- The exact ordered edge count across all ordered pairs of blocks.  The
terms with `X = Y` are the internal ordered edges of `X`. -/
def familyEdgeCount {N : ℕ} (H : SimpleGraph (Fin N))
    (F : EqualBlockFamily (Fin N)) : ℕ :=
  ∑ X ∈ F.blocks, ∑ Y ∈ F.blocks, crossEdgeCount H X Y

/-- The off-diagonal part of `familyEdgeCount`. -/
def familyCrossEdgeCount {N : ℕ} (H : SimpleGraph (Fin N))
    (F : EqualBlockFamily (Fin N)) : ℕ :=
  ∑ X ∈ F.blocks, ∑ Y ∈ F.blocks,
    if X = Y then 0 else crossEdgeCount H X Y

/-- The diagonal part of `familyEdgeCount`. -/
def familyInternalEdgeCount {N : ℕ} (H : SimpleGraph (Fin N))
    (F : EqualBlockFamily (Fin N)) : ℕ :=
  ∑ X ∈ F.blocks, squareEdgeCount H X

private theorem squareEdgeCount_eq_card_interedges {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (S : Finset (Fin N)) :
    squareEdgeCount H S = (H.interedges S S).card := by
  rw [squareEdgeCount]
  congr

/-- The block double sum is literally the internal ordered edge count of
the union. -/
theorem squareEdgeCount_biUnion_eq_familyEdgeCount {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (F : EqualBlockFamily (Fin N)) :
    squareEdgeCount H F.carrier = familyEdgeCount H F := by
  classical
  rw [squareEdgeCount_eq_card_interedges]
  have hpart := Rel.card_interedges_finpartition H.Adj
      F.toFinpartition F.toFinpartition
  rw [Finset.sum_product] at hpart
  rw [familyEdgeCount]
  change (Rel.interedges H.Adj F.carrier F.carrier).card = _
  calc
    (H.interedges F.carrier F.carrier).card =
        ∑ X ∈ F.blocks, ∑ Y ∈ F.blocks, (H.interedges X Y).card := hpart
    _ = ∑ X ∈ F.blocks, ∑ Y ∈ F.blocks, crossEdgeCount H X Y := by
      apply Finset.sum_congr rfl
      intro X hX
      apply Finset.sum_congr rfl
      intro Y hY
      exact (crossEdgeCount_eq_card_interedges H X Y).symm

/-- Exact diagonal/off-diagonal decomposition. -/
theorem familyEdgeCount_eq_internal_add_cross {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (F : EqualBlockFamily (Fin N)) :
    familyEdgeCount H F =
      familyInternalEdgeCount H F + familyCrossEdgeCount H F := by
  classical
  rw [familyEdgeCount, familyInternalEdgeCount, familyCrossEdgeCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro X hX
  have hdiag : crossEdgeCount H X X = squareEdgeCount H X := by
    rw [crossEdgeCount_eq_card_interedges, squareEdgeCount_eq_card_interedges]
  rw [← hdiag]
  calc
    (∑ Y ∈ F.blocks, crossEdgeCount H X Y) =
        ∑ Y ∈ F.blocks,
          ((if X = Y then crossEdgeCount H X Y else 0) +
            (if X = Y then 0 else crossEdgeCount H X Y)) := by
      apply Finset.sum_congr rfl
      intro Y hY
      by_cases hXY : X = Y
      · simp [hXY]
      · simp [hXY]
    _ = (∑ Y ∈ F.blocks, if X = Y then crossEdgeCount H X Y else 0) +
          ∑ Y ∈ F.blocks, (if X = Y then 0 else crossEdgeCount H X Y) := by
      rw [Finset.sum_add_distrib]
    _ = crossEdgeCount H X X +
          ∑ Y ∈ F.blocks, (if X = Y then 0 else crossEdgeCount H X Y) := by
      rw [Finset.sum_ite_eq, if_pos hX]

/-- Exact ordered-edge decomposition for the disjoint union of two
nonempty sets. -/
theorem squareEdgeCount_union {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (P Z : Finset (Fin N))
    (hP : P.Nonempty) (hZ : Z.Nonempty) (hPZ : Disjoint P Z) :
    squareEdgeCount H (P ∪ Z) =
      squareEdgeCount H P + squareEdgeCount H Z +
        2 * crossEdgeCount H P Z := by
  classical
  let part : Finpartition (P ∪ Z) :=
    { parts := {P, Z}
      supIndep := by
        rw [Finset.supIndep_iff_pairwiseDisjoint]
        intro X hX Y hY hXY
        change X ∈ ({P, Z} : Finset (Finset (Fin N))) at hX
        change Y ∈ ({P, Z} : Finset (Finset (Fin N))) at hY
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        rcases hX with (rfl | rfl) <;> rcases hY with (rfl | rfl)
        · exact (hXY rfl).elim
        · exact hPZ
        · exact hPZ.symm
        · exact (hXY rfl).elim
      sup_parts := by simp
      bot_notMem := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h ↦ hP.ne_empty h.symm,
          fun h ↦ hZ.ne_empty h.symm⟩ }
  have hcount := Rel.card_interedges_finpartition H.Adj part part
  rw [squareEdgeCount_eq_card_interedges]
  change (Rel.interedges H.Adj (P ∪ Z) (P ∪ Z)).card = _
  rw [show part.parts = {P, Z} by rfl] at hcount
  have hne : P ≠ Z := by
    intro h
    subst Z
    rw [Finset.disjoint_left] at hPZ
    exact hPZ hP.choose_spec hP.choose_spec
  rw [Finset.sum_product] at hcount
  simp [hne] at hcount
  rw [hcount]
  have hPP : (Rel.interedges H.Adj P P).card = squareEdgeCount H P := by
    calc
      _ = (H.interedges P P).card := by congr
      _ = _ := (squareEdgeCount_eq_card_interedges H P).symm
  have hZZ : (Rel.interedges H.Adj Z Z).card = squareEdgeCount H Z := by
    calc
      _ = (H.interedges Z Z).card := by congr
      _ = _ := (squareEdgeCount_eq_card_interedges H Z).symm
  have hPZ' : (Rel.interedges H.Adj P Z).card = crossEdgeCount H P Z := by
    calc
      _ = (H.interedges P Z).card := by congr
      _ = _ := (crossEdgeCount_eq_card_interedges H P Z).symm
  have hZP' : (Rel.interedges H.Adj Z P).card = crossEdgeCount H P Z := by
    calc
      _ = (H.interedges Z P).card := by congr
      _ = crossEdgeCount H Z P :=
        (crossEdgeCount_eq_card_interedges H Z P).symm
      _ = crossEdgeCount H P Z := crossEdgeCount_comm H Z P
  rw [hPP, hZZ, hPZ', hZP']
  omega

/-- Denominator-free sparsity of the block union. -/
def BlockFamilySparse {N : ℕ} (q : ℕ) (H : SimpleGraph (Fin N))
    (F : EqualBlockFamily (Fin N)) : Prop :=
  2 ^ q * familyEdgeCount H F ≤
    (F.blocks.card * F.blockSize) * (F.blocks.card * F.blockSize)

/-- The exact family formulation is equivalent to `SquareSparse` on the
carrier. -/
theorem blockFamilySparse_iff_squareSparse {N q : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (F : EqualBlockFamily (Fin N)) :
    BlockFamilySparse q H F ↔ SquareSparse q H F.carrier := by
  rw [BlockFamilySparse, SquareSparse,
    squareEdgeCount_biUnion_eq_familyEdgeCount, F.card_carrier]

/-! ## The explicit iteration certificate -/

/-- A checked certificate for the combinatorial output of the dyadic
Fox--Sudakov iteration.  Keeping it as data cleanly separates the difficult
balanced choices from the final loss calculation. -/
structure SparseFamilyCertificate (N D Q : ℕ) (H : SimpleGraph (Fin N)) where
  family : EqualBlockFamily (Fin N)
  sparse : BlockFamilySparse Q H family
  cardinal_loss : N ≤ 2 ^ (8 * D * Q ^ 2) * family.carrier.card

/-- The certificate-to-subset bridge used by the later assembly.  The
result has exactly the requested Sudakov loss and no density division. -/
theorem squareSparse_of_sparseFamilyCertificate {N D Q : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (C : SparseFamilyCertificate N D Q H) :
    ∃ S : Finset (Fin N), SquareSparse Q H S ∧
      N ≤ 2 ^ (8 * D * Q ^ 2) * S.card := by
  exact ⟨C.family.carrier,
    (blockFamilySparse_iff_squareSparse H C.family).mp C.sparse,
    C.cardinal_loss⟩

/-
/-! ## Direct Fox--Sudakov low-degree recursion -/

/-- The ordinary local sparse-pair input, at relative loss `2^R`. -/
def LocalSparsePairs {N : ℕ} (n R Q : ℕ) (H : SimpleGraph (Fin N)) : Prop :=
  ∀ U : Finset (Fin N), n * 2 ^ R ≤ U.card →
    ∃ A B : Finset (Fin N),
      A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧ A.card = B.card ∧
        ceilDiv U.card (2 ^ R) ≤ A.card ∧ PairSparse (Q + 3) H A B

private theorem squareEdgeCount_le_sq_card {N : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (S : Finset (Fin N)) :
    squareEdgeCount H S ≤ S.card * S.card := by
  rw [squareEdgeCount_eq_card_interedges]
  exact H.card_interedges_le_mul S S

/-- The inductive kernel.  At depth `k` it retains exactly `2^k` leaves of
size `b`.  The first term on the right controls all cross-edges created by
the binary recursion; the second is the still-uncontrolled contribution of
the leaves. -/
theorem dyadic_sparse_core {N n R Q b k : ℕ}
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (hlocal : LocalSparsePairs n R Q H)
    (hb : 0 < b) (hn : n ≤ 2 * b)
    (U : Finset (Fin N))
    (hscale : (2 * 2 ^ R) ^ k * b ≤ U.card) :
    ∃ S : Finset (Fin N), S ⊆ U ∧ S.card = 2 ^ k * b ∧
      2 ^ (Q + 1) * squareEdgeCount H S ≤
        S.card * S.card + 2 ^ (Q + 1) * (2 ^ k * b ^ 2) := by
  induction k generalizing U with
  | zero =>
      have hbU : b ≤ U.card := by simpa using hscale
      obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hbU
      refine ⟨S, hSU, by simpa using hScard, ?_⟩
      have hedge := squareEdgeCount_le_sq_card H S
      rw [hScard]
      calc
        2 ^ (Q + 1) * squareEdgeCount H S ≤
            2 ^ (Q + 1) * (b * b) := Nat.mul_le_mul_left _ hedge
        _ ≤ b * b + 2 ^ (Q + 1) * (2 ^ 0 * b ^ 2) := by
          simp only [pow_zero, one_mul, pow_two]
          omega
  | succ k ih =>
      let L := 2 ^ R
      let T := (2 * L) ^ k * b
      let K := 2 ^ (Q + 1)
      have hL : 0 < L := by simp [L]
      have hT : 0 < T := by positivity
      have hnode : 2 * L * T ≤ U.card := by
        simpa [T, L, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hscale
      have hthreshold : n * L ≤ U.card := by
        calc
          n * L ≤ (2 * b) * L := Nat.mul_le_mul_right L hn
          _ ≤ 2 * L * T := by
            simp only [T]
            have : b ≤ (2 * L) ^ k * b := by
              exact Nat.le_mul_of_pos_left b (by positivity)
            nlinarith
          _ ≤ U.card := hnode
      obtain ⟨A, B, hAU, hBU, hAB, hcardAB, hceil, hsparse⟩ :=
        hlocal U (by simpa [L] using hthreshold)
      let a := A.card
      have haB : B.card = a := hcardAB.symm
      have ha : 0 < a := by
        have h2Tceil : 2 * T ≤ ceilDiv U.card L := by
          apply Nat.le_of_mul_le_mul_left (c := L) (hc := hL)
          calc
            L * (2 * T) = 2 * L * T := by ring
            _ ≤ U.card := hnode
            _ ≤ L * ceilDiv U.card L := le_mul_ceilDiv U.card hL
        omega
      have h2Ta : 2 * T ≤ a := by
        have h2Tceil : 2 * T ≤ ceilDiv U.card L := by
          apply Nat.le_of_mul_le_mul_left (c := L) (hc := hL)
          calc
            L * (2 * T) = 2 * L * T := by ring
            _ ≤ U.card := hnode
            _ ≤ L * ceilDiv U.card L := le_mul_ceilDiv U.card hL
        exact h2Tceil.trans hceil
      have hpair : 2 * (2 * K) * crossEdgeCount H A B ≤ A.card * B.card := by
        simpa [PairSparse, K, hcardAB, pow_succ, pow_add,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsparse
      obtain ⟨X, hXA, hXcard, hXdeg⟩ :=
        exists_lowDegree_subset H A B (by simpa [haB] using ha)
          hpair (by simpa [a] using h2Ta)
      obtain ⟨P, hPX, hPcard, hPedge⟩ :=
        ih X (by simpa [T, L, hXcard])
      have hPB : 2 * K * crossEdgeCount H P B ≤ P.card * B.card := by
        rw [crossEdgeCount_eq_sum_crossDegree]
        calc
          2 * K * (∑ x ∈ P, crossDegree H B x) =
              ∑ x ∈ P, (2 * K) * crossDegree H B x := by
                rw [Finset.mul_sum]
          _ ≤ ∑ _x ∈ P, B.card := by
            apply Finset.sum_le_sum
            intro x hxP
            exact hXdeg x (hPX hxP)
          _ = P.card * B.card := by simp
      have hPpos : 0 < P.card := by rw [hPcard]; positivity
      have hBP : 2 * K * crossEdgeCount H B P ≤ B.card * P.card := by
        rw [crossEdgeCount_comm H B P, Nat.mul_comm B.card P.card]
        exact hPB
      obtain ⟨Y, hYB, hYcard, hYdeg⟩ :=
        exists_lowDegree_subset H B P hPpos hBP (by simpa [haB, a] using h2Ta)
      obtain ⟨Z, hZY, hZcard, hZedge⟩ :=
        ih Y (by simpa [T, L, hYcard])
      have hPZ : K * crossEdgeCount H P Z ≤ P.card * Z.card := by
        rw [crossEdgeCount_comm H P Z, crossEdgeCount_eq_sum_crossDegree]
        calc
          K * (∑ z ∈ Z, crossDegree H P z) =
              ∑ z ∈ Z, K * crossDegree H P z := by
                rw [Finset.mul_sum]
          _ ≤ ∑ _z ∈ Z, P.card := by
            apply Finset.sum_le_sum
            intro z hzZ
            exact hYdeg z (hZY hzZ)
          _ = Z.card * P.card := by simp
          _ = P.card * Z.card := Nat.mul_comm _ _
      have hPZdisj : Disjoint P Z := by
        apply hAB.mono
        · exact hPX.trans hXA
        · exact hZY.trans hYB
      have hPne : P.Nonempty := Finset.card_pos.mp hPpos
      have hZpos : 0 < Z.card := by rw [hZcard]; positivity
      have hZne : Z.Nonempty := Finset.card_pos.mp hZpos
      refine ⟨P ∪ Z, ?_, ?_, ?_⟩
      · exact Finset.union_subset (hPX.trans (hXA.trans hAU))
          (hZY.trans (hYB.trans hBU))
      · rw [Finset.card_union_of_disjoint hPZdisj, hPcard, hZcard]
        simp only [T, ← two_mul, ← pow_succ]
      · rw [squareEdgeCount_union H P Z hPne hZne hPZdisj]
        have hcards : P.card = Z.card := by rw [hPcard, hZcard]
        have hcross2 : K * (2 * crossEdgeCount H P Z) ≤
            2 * (P.card * Z.card) := by
          calc
            K * (2 * crossEdgeCount H P Z) =
                2 * (K * crossEdgeCount H P Z) := by ring
            _ ≤ 2 * (P.card * Z.card) := Nat.mul_le_mul_left 2 hPZ
        rw [K] at hPedge hZedge hcross2 ⊢
        rw [Finset.card_union_of_disjoint hPZdisj]
        calc
          2 ^ (Q + 1) *
              (squareEdgeCount H P + squareEdgeCount H Z +
                2 * crossEdgeCount H P Z) =
              2 ^ (Q + 1) * squareEdgeCount H P +
                2 ^ (Q + 1) * squareEdgeCount H Z +
                  2 ^ (Q + 1) * (2 * crossEdgeCount H P Z) := by ring
          _ ≤ (P.card * P.card + 2 ^ (Q + 1) * (2 ^ k * b ^ 2)) +
                (Z.card * Z.card + 2 ^ (Q + 1) * (2 ^ k * b ^ 2)) +
                  2 * (P.card * Z.card) :=
            Nat.add_le_add (Nat.add_le_add hPedge hZedge) hcross2
          _ = (P.card + Z.card) * (P.card + Z.card) +
                2 ^ (Q + 1) * (2 ^ (k + 1) * b ^ 2) := by
            rw [pow_succ]
            ring

/-! The final numerical specialization is placed in the assembly module:
`dyadic_sparse_core` is the exact local-pairs-to-sparse-set combinatorial
bridge, while choosing `b = N / 2^((Q+1)(R+1))` is purely arithmetic. -/
-/

end Erdos546
