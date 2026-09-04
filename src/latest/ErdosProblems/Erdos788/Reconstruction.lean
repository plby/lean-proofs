import ErdosProblems.Erdos788.ShortLinearCode
import ErdosProblems.Erdos788.SuffixSlackDesign
import ErdosProblems.Erdos788.RankPruning
import ErdosProblems.Erdos788.FinitePrediction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite Trevisan reconstruction

This module carries out the strong-extractor reconstruction entirely with
`FinDist`.  Code coordinates and seed coordinates are binary, while all
symbols and all fixed-seed maps are over `ZMod p`.
-/

namespace Erdos788

open scoped BigOperators

namespace Reconstruction

local instance reconstructionFintypeCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : Fintype D.Coord :=
  D.instFintypeCoord

local instance reconstructionDecidableEqCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : DecidableEq D.Coord :=
  D.instDecidableEqCoord

/-- Assignments to the coordinates in one design row. -/
abbrev RowAssignment {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r) :=
  D.row i → Bool

/-- The cardinality equality used to identify a design-row assignment with
a binary code coordinate. -/
theorem card_binaryCoord_eq_rowAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (BinaryCoord ell) = Fintype.card (RowAssignment D i) := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  simp [BinaryCoord, RowAssignment, D.row_card i]

/-- A fixed identification between code coordinates and assignments on row
`i`. -/
noncomputable def rowAssignmentEquiv {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    BinaryCoord ell ≃ RowAssignment D i := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact Fintype.equivOfCardEq (card_binaryCoord_eq_rowAssignment D i)

/-- Restrict a full binary seed to a row and regard it as a code
coordinate. -/
noncomputable def seedCodeCoord {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (y : D.Coord → Bool) : BinaryCoord ell := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact (rowAssignmentEquiv D i).symm (fun c ↦ y c.1)

theorem seedCodeCoord_apply_equiv {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (y : D.Coord → Bool) (c : D.row i) :
    rowAssignmentEquiv D i (seedCodeCoord D i y) c = y c.1 := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  simp [seedCodeCoord]

/-- Assignments outside one distinguished design row. -/
abbrev OutsideAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :=
  {c : D.Coord // c ∉ D.row i} → Bool

/-- Combine an outside assignment and a row assignment into a full seed. -/
def combineSeed {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i) :
    D.Coord → Bool := fun c ↦
  if hc : c ∈ D.row i then z ⟨c, hc⟩ else a ⟨c, hc⟩

@[simp]
theorem combineSeed_apply_mem {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i)
    {c : D.Coord} (hc : c ∈ D.row i) :
    combineSeed D i a z c = z ⟨c, hc⟩ := by
  simp [combineSeed, hc]

@[simp]
theorem combineSeed_apply_notMem {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i)
    {c : D.Coord} (hc : c ∉ D.row i) :
    combineSeed D i a z c = a ⟨c, hc⟩ := by
  simp [combineSeed, hc]

/-- Full seeds split exactly into their outside and inside restrictions. -/
def seedSplitEquiv {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r) :
    (D.Coord → Bool) ≃ OutsideAssignment D i × RowAssignment D i where
  toFun y := (fun c ↦ y c.1, fun c ↦ y c.1)
  invFun q := combineSeed D i q.1 q.2
  left_inv y := by
    funext c
    by_cases hc : c ∈ D.row i <;> simp [combineSeed, hc]
  right_inv q := by
    apply Prod.ext <;> funext c
    · simp [combineSeed, c.2]
    · simp [combineSeed, c.2]

/-- Assignments on the overlap of row `i` with its `j`th predecessor. -/
abbrev OverlapAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) (j : Fin i.val) :=
  {c : D.Coord //
    c ∈ D.row i ∩ D.row (priorIndex i j.val)} → Bool

/-- A reconstruction description: the seed outside row `i`, together with
one table for every earlier output coordinate. -/
abbrev Description {p ell r : ℕ} [NeZero p]
    (D : SuffixDesign ell r) (i : Fin r) :=
  OutsideAssignment D i ×
    ((j : Fin i.val) → OverlapAssignment D i j → ZMod p)

theorem sum_overlap_powers_le {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    (∑ j : Fin i.val,
      2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) ≤ r - 1 := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  have hterm (j : ℕ) :
      2 ^ (D.row i ∩ D.row (priorIndex i j)).card =
        overlapCost (D.row i) (D.row (priorIndex i j)) + 1 := by
    rw [overlapCost]
    have hpos : 0 < 2 ^ (D.row i ∩ D.row (priorIndex i j)).card := by positivity
    omega
  have hsum :
      (∑ j ∈ Finset.range i.val,
          2 ^ (D.row i ∩ D.row (priorIndex i j)).card) =
        (∑ j ∈ Finset.range i.val,
          overlapCost (D.row i) (D.row (priorIndex i j))) + i.val := by
    simp_rw [hterm, Finset.sum_add_distrib]
    simp
  have hsumFin :
      (∑ j : Fin i.val,
        2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) =
        (∑ j ∈ Finset.range i.val,
          overlapCost (D.row i) (D.row (priorIndex i j))) + i.val := by
    simpa only [← Fin.sum_univ_eq_sum_range] using! hsum
  rw [hsumFin]
  have hs := D.suffix_slack i
  omega

theorem card_outsideAssignment_le {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (OutsideAssignment D i) ≤ 2 ^ D.coordCard := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  simp only [OutsideAssignment, Fintype.card_fun, Fintype.card_bool]
  apply Nat.pow_le_pow_right (by omega)
  exact Fintype.card_subtype_le _

theorem card_description_le {p ell r : ℕ} [Fact p.Prime]
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (Description (p := p) D i) ≤
      2 ^ D.coordCard * p ^ (r - 1) := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hovercard (j : Fin i.val) :
      Fintype.card (OverlapAssignment D i j) =
        2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card := by
    simp only [OverlapAssignment, Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype]
    congr 1
    ext c
    simp
  have hinner (j : Fin i.val) :
      Fintype.card (OverlapAssignment D i j → ZMod p) =
        p ^ (2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) := by
    rw [Fintype.card_fun, ZMod.card, hovercard]
  have htable :
      Fintype.card ((j : Fin i.val) →
        OverlapAssignment D i j → ZMod p) =
        p ^ (∑ j : Fin i.val,
          2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) := by
    rw [Fintype.card_pi]
    simp_rw [hinner]
    simpa using! Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin i.val))
      (fun j ↦ 2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) p
  rw [Fintype.card_prod, htable]
  exact Nat.mul_le_mul (card_outsideAssignment_le D i)
    (Nat.pow_le_pow_right hp (sum_overlap_powers_le D i))

/-- Restrict a row assignment to one of its predecessor overlaps. -/
def overlapRestriction {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (z : RowAssignment D i) :
    OverlapAssignment D i j := fun c ↦ z ⟨c.1, (Finset.mem_inter.mp c.2).1⟩

/-- Extend overlap bits to the distinguished row, using `false` away from
the predecessor row.  Values away from the overlap will not affect that
predecessor's code coordinate. -/
def extendOverlap {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (w : OverlapAssignment D i j) :
    RowAssignment D i := fun c ↦
  if hc : c.1 ∈ D.row (priorIndex i j.val) then
    w ⟨c.1, Finset.mem_inter.mpr ⟨c.2, hc⟩⟩
  else false

@[simp]
theorem extendOverlap_overlapRestriction_apply
    {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (z : RowAssignment D i)
    (c : D.row i) (hc : c.1 ∈ D.row (priorIndex i j.val)) :
    extendOverlap D i j (overlapRestriction D i j z) c = z c := by
  simp [extendOverlap, overlapRestriction, hc]

theorem seedCodeCoord_eq_of_eq_on_row {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    {y y' : D.Coord → Bool}
    (h : ∀ c ∈ D.row i, y c = y' c) :
    seedCodeCoord D i y = seedCodeCoord D i y' := by
  let := D.instFintypeCoord
  let := D.instDecidableEqCoord
  apply (rowAssignmentEquiv D i).injective
  funext c
  simp only [seedCodeCoord_apply_equiv]
  exact h c.1 c.2

/-- The genuine earlier-output table associated with `x` and a fixed
outside assignment. -/
noncomputable def actualPriorTable
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (j : Fin i.val) : OverlapAssignment D i j → ZMod p :=
  fun w ↦ C.encoder x
    (seedCodeCoord D (priorIndex i j.val)
      (combineSeed D i a (extendOverlap D i j w)))

theorem actualPriorTable_correct
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (j : Fin i.val) (z : RowAssignment D i) :
    actualPriorTable C D i x a j (overlapRestriction D i j z) =
      C.encoder x
        (seedCodeCoord D (priorIndex i j.val) (combineSeed D i a z)) := by
  apply congrArg (fun q ↦ C.encoder x q)
  apply seedCodeCoord_eq_of_eq_on_row
  intro c hcPrior
  by_cases hcI : c ∈ D.row i
  · rw [combineSeed_apply_mem D i a _ hcI,
      combineSeed_apply_mem D i a z hcI]
    exact extendOverlap_overlapRestriction_apply D i j z ⟨c, hcI⟩ hcPrior
  · rw [combineSeed_apply_notMem D i a _ hcI,
      combineSeed_apply_notMem D i a z hcI]

/-- Earlier Trevisan outputs, represented as a prefix tuple. -/
noncomputable def outputPrefix
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (y : D.Coord → Bool) :
    Fin i.val → ZMod p := fun j ↦
  C.encoder x (seedCodeCoord D (priorIndex i j.val) y)

/-- The received word decoded from one reconstruction description. -/
noncomputable def descriptionWord
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) →
      (Fin i.val → ZMod p) → ZMod p)
    (desc : Description (p := p) D i) :
    BinaryCoord C.ell → ZMod p := fun q ↦
  let z := rowAssignmentEquiv D i q
  let y := combineSeed D i desc.1 z
  predictor y (fun j ↦ desc.2 j (overlapRestriction D i j z))

theorem descriptionWord_actual
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) →
      (Fin i.val → ZMod p) → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (q : BinaryCoord C.ell) :
    descriptionWord C D i predictor
        (a, actualPriorTable C D i x a) q =
      predictor
        (combineSeed D i a (rowAssignmentEquiv D i q))
        (outputPrefix C D i x
          (combineSeed D i a (rowAssignmentEquiv D i q))) := by
  let z := rowAssignmentEquiv D i q
  let y := combineSeed D i a z
  change predictor y
      (fun j ↦ actualPriorTable C D i x a j
        (overlapRestriction D i j z)) =
    predictor y (fun j ↦
      C.encoder x (seedCodeCoord D (priorIndex i j.val) y))
  apply congrArg (predictor y)
  funext j
  exact actualPriorTable_correct C D i x a j z

/-- The fixed-seed Trevisan output map. -/
noncomputable def fixedSeedMap
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (y : D.Coord → Bool) :
    FFVec p (2 * r) →ₗ[ZMod p] FFVec p r where
  toFun x i := C.encoder x (seedCodeCoord D i y)
  map_add' x x' := by
    funext i
    exact congrFun (C.encoder.map_add x x')
      (seedCodeCoord D i y)
  map_smul' a x := by
    funext i
    exact congrFun (C.encoder.map_smul a x)
      (seedCodeCoord D i y)

end Reconstruction

end Erdos788
