import Mathlib

/-!
# Everywhere-Unbounded Lagrange Arrays (Erdős Problem 671)

We construct a triangular array of interpolation nodes in `[-1, 1]` whose Lebesgue
functions are unbounded at every point, yet such that for every `f ∈ C[-1, 1]` there is a
point `x_f` at which the full sequence of Lagrange interpolants converges to `f x_f`.  This
gives affirmative answers to both parts of Erdős Problem 671.  The packaged statement is
`erdos_671`.

For a `Row` `X` of `n` distinct nodes in `[-1, 1]` we write `fundamental X i` for the `i`-th
fundamental Lagrange polynomial `ℓ_{a,X}`, `interpolant X f` for the interpolant
`𝓛_X f = ∑ₐ f a · ℓ_{a,X}`, and `lebesgue X` for the Lebesgue function `λ_X = ∑ₐ |ℓ_{a,X}|`.

## Construction

Rows are built in finite stages indexed by `k`.  A `Level k` is a family of `branchCount k`
pairwise-disjoint `Cell`s (nondegenerate closed subintervals) whose interiors lie in the
`ProtectedZone` `(-3/4, -1/4)`.  Stage `k` turns `levels k : Level k` into `levels (k+1)`:

* `shrinkLevel` shrinks each cell so all *filler* rows are stable (`lebesgue ≤ 2`) on it.
* For every child `t` a `Collision.Data` record drives a *collision-pair* `pairRow`, whose
  Lebesgue function exceeds `k + 1` at the child centre while every other pair row stays
  stable; `preLevel` records the resulting child cells.
* An *exterior* row (`Exterior.closePairNode`) forces `lebesgue ≥ k + 1` off the cells,
  and `nextLevel` shrinks each cell once more so this exterior row is stable on it.

`arrayRow n` then selects the filler, pair, or exterior row of size `n`.  Cofinal
unboundedness everywhere is `array_lebesgue_unbounded`.  For fixed `f`, a pigeonhole choice
(`exists_pair_abs_sub_le`) of a close sample pair at each stage selects a nested sequence of
cells with a common point `selectedPoint f`, at which
`arrayRow_converges_at_selectedPoint` gives convergence.

## References

* [erdosproblems.com/671](https://www.erdosproblems.com/671)

## Conventions

`Row n` packages an `n`-element set of distinct nodes in `[-1, 1]`, so `arrayRow n` has `n`
nodes.  The final statement `erdos_671` reindexes to the one-based rows `Row (n + 1)` of the
paper.
-/

open ContinuousMap Filter Polynomial Set
open scoped BigOperators Topology

namespace Erdos671

noncomputable section

private structure TaggedIndex (n : ℕ) where
  val : Fin n
deriving Fintype

private def taggedIndexEquiv (n : ℕ) : TaggedIndex n ≃ Fin n where
  toFun := TaggedIndex.val
  invFun := TaggedIndex.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The compact interval on which Problem 671 is posed. -/
abbrev Interval := Set.Icc (-1 : ℝ) 1

private abbrev ProtectedZone := Set.Ioo (-3 / 4 : ℝ) (-1 / 4)
private abbrev FillerZone := Set.Ioo (-1 : ℝ) (-7 / 8)
private abbrev ReserveZone := Set.Ioo (1 / 4 : ℝ) (3 / 4)

private theorem exists_pair_abs_sub_le {k : ℕ} (hk : 1 ≤ k) (M : ℝ)
    (v : Fin (k ^ 2 + 1) → ℝ) (hv : ∀ i, |v i| ≤ M) :
    ∃ r s, r ≠ s ∧ |v r - v s| ≤ 2 * M / k ^ 2 := by
  let key : TaggedIndex (k ^ 2 + 1) → ℝ ×ₗ ℕ :=
    fun i ↦ toLex (v i.val, i.val.1)
  have key_injective : Function.Injective key := by
    intro i j hij
    apply (taggedIndexEquiv _).injective
    apply Fin.ext
    exact congrArg (fun z : ℝ ×ₗ ℕ ↦ (ofLex z).2) hij
  let _ : LinearOrder (TaggedIndex (k ^ 2 + 1)) := LinearOrder.lift' key key_injective
  have tagged_card : Fintype.card (TaggedIndex (k ^ 2 + 1)) = k ^ 2 + 1 :=
    (Fintype.card_congr (taggedIndexEquiv _)).trans (Fintype.card_fin _)
  let p := Finset.orderIsoOfFin
    (Finset.univ : Finset (TaggedIndex (k ^ 2 + 1))) (k := k ^ 2 + 1) (by simpa)
  let q : Fin (k ^ 2 + 1) → Fin (k ^ 2 + 1) := fun i ↦ (p i).val.val
  have q_injective : Function.Injective q := by
    intro i j hij
    apply p.injective
    apply Subtype.ext
    apply (taggedIndexEquiv _).injective
    exact hij
  let w : Fin (k ^ 2 + 1) → ℝ := fun i ↦ v (q i)
  have w_mono : Monotone w := by
    intro i j hij
    have hp := p.monotone hij
    change key (p i) ≤ key (p j) at hp
    exact Prod.Lex.monotone_fst_ofLex hp
  let w' : ℕ → ℝ := fun i ↦ if hi : i < k ^ 2 + 1 then w ⟨i, hi⟩ else 0
  have hk3 : 0 < k ^ 2 := pow_pos hk 2
  have w'_zero : w' 0 = w 0 := by simp [w']
  have w'_last : w' (k ^ 2) = w (Fin.last (k ^ 2)) := by simp [w', Fin.last]
  have hends : w' (k ^ 2) - w' 0 ≤ 2 * M := by
    rw [w'_zero, w'_last]
    have hfirst : -M ≤ w 0 := (abs_le.mp (hv (q 0))).1
    have hlast : w (Fin.last (k ^ 2)) ≤ M :=
      (abs_le.mp (hv (q (Fin.last (k ^ 2))))).2
    linarith
  have hk3r : (k ^ 2 : ℝ) ≠ 0 := by exact_mod_cast hk3.ne'
  have hsum :
      ∑ i ∈ Finset.range (k ^ 2), (w' (i + 1) - w' i) ≤
        ∑ _i ∈ Finset.range (k ^ 2), (2 * M / k ^ 2) := by
    rw [Finset.sum_range_sub]
    calc
      w' (k ^ 2) - w' 0 ≤ 2 * M := hends
      _ = ∑ _i ∈ Finset.range (k ^ 2), (2 * M / k ^ 2) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        simp only [Nat.cast_pow]
  obtain ⟨i, hi, hgap⟩ := Finset.exists_le_of_sum_le
    ⟨0, Finset.mem_range.mpr hk3⟩ hsum
  have hi3 : i < k ^ 2 := Finset.mem_range.mp hi
  let s : Fin (k ^ 2 + 1) := ⟨i, by omega⟩
  let r : Fin (k ^ 2 + 1) := ⟨i + 1, by omega⟩
  have hsr : s < r := by simp [s, r]
  have horder : w s ≤ w r := w_mono hsr.le
  have hs : w' i = w s := by
    simp only [w']
    split
    · rfl
    · omega
  have hr : w' (i + 1) = w r := by
    simp only [w']
    split
    · rfl
    · omega
  refine ⟨q r, q s, q_injective.ne hsr.ne', ?_⟩
  change |w r - w s| ≤ 2 * M / k ^ 2
  rw [abs_of_nonneg (sub_nonneg.mpr horder)]
  simpa only [hr, hs] using hgap

private abbrev Edge (k : ℕ) :=
  {e : Fin ((k + 1) ^ 2 + 1) × Fin ((k + 1) ^ 2 + 1) // e.1 < e.2}

private def firstEdge (k : ℕ) : Edge k := by
  have hk : 0 < (k + 1) ^ 2 := pow_pos (Nat.zero_lt_succ k) 2
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  exact Nat.zero_lt_one

private def edgeCard (k : ℕ) := Fintype.card (Edge k)

private theorem edgeCard_pos (k : ℕ) : 0 < edgeCard k :=
  Fintype.card_pos_iff.mpr ⟨firstEdge k⟩

private def branchCount : ℕ → ℕ
  | 0 => 1
  | k + 1 => branchCount k * edgeCard k

private theorem branchCount_pos (k : ℕ) : 0 < branchCount k := by
  induction k with
  | zero => simp [branchCount]
  | succ k ih => simpa [branchCount] using Nat.mul_pos ih (edgeCard_pos k)

private def stageBoundary : ℕ → ℕ
  | 0 => 2
  | k + 1 => max (stageBoundary k + 1) (branchCount (k + 1) + 2) + branchCount (k + 1)

private def stageStart (k : ℕ) :=
  max (stageBoundary k + 1) (branchCount (k + 1) + 2)

private theorem stageBoundary_succ (k : ℕ) :
    stageBoundary (k + 1) = stageStart k + branchCount (k + 1) := rfl

private theorem stageBoundary_lt_succ (k : ℕ) :
    stageBoundary k < stageBoundary (k + 1) := by
  rw [stageBoundary_succ]
  have := branchCount_pos (k + 1)
  dsimp [stageStart]
  omega

private theorem branchCount_le_stageBoundary (k : ℕ) : branchCount k ≤ stageBoundary k := by
  induction k with
  | zero => simp [branchCount, stageBoundary]
  | succ k _ =>
      rw [stageBoundary_succ]
      exact Nat.le_add_left _ _

private abbrev FillerIndex (k : ℕ) :=
  {n : ℕ // n ∈ Finset.Ioo (stageBoundary k) (stageStart k)}

/-- A nondegenerate closed interval contained in `[-1, 1]`. -/
structure Cell where
  /-- Left endpoint. -/
  left : ℝ
  /-- Right endpoint. -/
  right : ℝ
  left_lt_right : left < right
  subset_interval : Set.Icc left right ⊆ Interval

/-- The set underlying a protected interval. -/
def Cell.carrier (I : Cell) : Set ℝ := Set.Icc I.left I.right

theorem Cell.nonempty (I : Cell) : I.carrier.Nonempty :=
  ⟨I.left, le_rfl, I.left_lt_right.le⟩

private def splitPoint (I : Cell) (q r : ℕ) : ℝ :=
  I.left + (r : ℝ) / (4 * q) * (I.right - I.left)

private theorem splitPoint_lt (I : Cell) {q r s : ℕ} (hq : 0 < q) (hrs : r < s) :
    splitPoint I q r < splitPoint I q s := by
  have hden : (0 : ℝ) < 4 * q := by positivity
  have hfrac : (r : ℝ) / (4 * q) < (s : ℝ) / (4 * q) :=
    (div_lt_div_iff_of_pos_right hden).2 (by exact_mod_cast hrs)
  change I.left + (r : ℝ) / (4 * q) * (I.right - I.left) <
    I.left + (s : ℝ) / (4 * q) * (I.right - I.left)
  linarith [mul_lt_mul_of_pos_right hfrac (sub_pos.mpr I.left_lt_right)]

private theorem splitPoint_zero (I : Cell) (q : ℕ) : splitPoint I q 0 = I.left := by
  simp [splitPoint]

private theorem splitPoint_top (I : Cell) {q : ℕ} (hq : 0 < q) :
    splitPoint I q (4 * q) = I.right := by
  have hq' : (4 * (q : ℝ)) ≠ 0 := by positivity
  dsimp [splitPoint]
  rw [Nat.cast_mul, Nat.cast_ofNat, div_self hq']
  ring

private def splitCell (I : Cell) {q : ℕ} (hq : 0 < q) (e : Fin q) : Cell where
  left := splitPoint I q (4 * e + 1)
  right := splitPoint I q (4 * e + 3)
  left_lt_right := splitPoint_lt I hq (by omega)
  subset_interval := by
    rintro x ⟨hx₁, hx₂⟩
    apply I.subset_interval
    have hleft : I.left < splitPoint I q (4 * (e : ℕ) + 1) := by
      rw [← splitPoint_zero I q]
      exact splitPoint_lt I hq (by omega)
    have hright : splitPoint I q (4 * (e : ℕ) + 3) < I.right := by
      rw [← splitPoint_top I hq]
      exact splitPoint_lt I hq (by have := e.isLt; omega)
    constructor
    · exact hleft.le.trans hx₁
    · exact hx₂.trans hright.le

private def splitCenter (I : Cell) {q : ℕ} (e : Fin q) : ℝ :=
  splitPoint I q (4 * e + 2)

private theorem splitCenter_mem (I : Cell) {q : ℕ} (hq : 0 < q) (e : Fin q) :
    splitCenter I e ∈ Set.Ioo (splitCell I hq e).left (splitCell I hq e).right :=
  ⟨splitPoint_lt I hq (by omega), splitPoint_lt I hq (by omega)⟩

private theorem splitCell_subset (I : Cell) {q : ℕ} (hq : 0 < q) (e : Fin q) :
    (splitCell I hq e).carrier ⊆ I.carrier := by
  intro x hx
  have hleft : I.left < splitPoint I q (4 * (e : ℕ) + 1) := by
    rw [← splitPoint_zero I q]
    exact splitPoint_lt I hq (by omega)
  have hright : splitPoint I q (4 * (e : ℕ) + 3) < I.right := by
    rw [← splitPoint_top I hq]
    exact splitPoint_lt I hq (by have := e.isLt; omega)
  exact ⟨hleft.le.trans hx.1, hx.2.trans hright.le⟩

private theorem splitCell_subset_interior (I : Cell) {q : ℕ} (hq : 0 < q) (e : Fin q) :
    (splitCell I hq e).carrier ⊆ Set.Ioo I.left I.right := by
  intro x hx
  have hleft : I.left < splitPoint I q (4 * (e : ℕ) + 1) := by
    rw [← splitPoint_zero I q]
    exact splitPoint_lt I hq (by omega)
  have hright : splitPoint I q (4 * (e : ℕ) + 3) < I.right := by
    rw [← splitPoint_top I hq]
    exact splitPoint_lt I hq (by have := e.isLt; omega)
  exact ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩

private theorem splitCell_disjoint (I : Cell) {q : ℕ} (hq : 0 < q)
    {e f : Fin q} (hef : e ≠ f) :
    Disjoint (splitCell I hq e).carrier (splitCell I hq f).carrier := by
  apply Set.disjoint_left.2
  intro x he hf
  rcases lt_or_gt_of_ne hef with h | h
  · have hsep : (splitCell I hq e).right < (splitCell I hq f).left :=
      splitPoint_lt I hq (by omega)
    linarith [he.2, hf.1]
  · have hsep : (splitCell I hq f).right < (splitCell I hq e).left :=
      splitPoint_lt I hq (by omega)
    linarith [he.1, hf.2]

private theorem splitCenter_injective (I : Cell) {q : ℕ} (hq : 0 < q) :
    Function.Injective (splitCenter I : Fin q → ℝ) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (splitPoint_lt I hq (by omega)).ne h
  · exact (splitPoint_lt I hq (by omega)).ne h.symm

private def cellPointEmbedding (I : Cell) (n : ℕ) : Fin n ↪ Interval where
  toFun i :=
    let j : Fin (n + 1) := ⟨i, by omega⟩
    ⟨splitCenter I j, I.subset_interval
      (splitCell_subset I (Nat.succ_pos n) j
        (Ioo_subset_Icc_self (splitCenter_mem I (Nat.succ_pos n) j)))⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' := congrArg Subtype.val h
    change splitCenter I (⟨i, by omega⟩ : Fin (n + 1)) =
      splitCenter I (⟨j, by omega⟩ : Fin (n + 1)) at h'
    exact congrArg (fun z : Fin (n + 1) ↦ z.val)
      (splitCenter_injective I (Nat.succ_pos n) h')

private theorem cellPointEmbedding_mem (I : Cell) (n : ℕ) (i : Fin n) :
    ((cellPointEmbedding I n i : Interval) : ℝ) ∈ Set.Ioo I.left I.right :=
  splitCell_subset_interior I (Nat.succ_pos n) ⟨i, by omega⟩
    (Ioo_subset_Icc_self (splitCenter_mem I (Nat.succ_pos n) ⟨i, by omega⟩))

private def Cell.midpoint (I : Cell) : ℝ := (I.left + I.right) / 2

private theorem Cell.midpoint_mem (I : Cell) : I.midpoint ∈ Set.Ioo I.left I.right := by
  dsimp [Cell.midpoint]
  constructor <;> linarith [I.left_lt_right]

private structure Level (k : ℕ) where
  cell : Fin (branchCount k) → Cell
  disjoint : ∀ {i j}, i ≠ j → Disjoint (cell i).carrier (cell j).carrier
  interior_protected : ∀ i, Set.Ioo (cell i).left (cell i).right ⊆ ProtectedZone

private def rootLevel : Level 0 where
  cell _ := ⟨-2 / 3, -1 / 3, by norm_num, by
    rintro x ⟨hx₁, hx₂⟩
    constructor <;> linarith⟩
  disjoint := by
    intro i j h
    apply (h ?_).elim
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change i.val < 1 at hi
    change j.val < 1 at hj
    omega
  interior_protected := by
    intro _ x hx
    change x ∈ Set.Ioo (-3 / 4 : ℝ) (-1 / 4)
    constructor <;> linarith [hx.1, hx.2]

private def Level.midpointEmbedding {k : ℕ} (L : Level k) :
    Fin (branchCount k) ↪ Interval where
  toFun i := ⟨(L.cell i).midpoint,
    L.cell i |>.subset_interval (Ioo_subset_Icc_self (L.cell i).midpoint_mem)⟩
  inj' := by
    intro i j hij
    by_contra hne
    have hd := L.disjoint hne
    apply Set.disjoint_left.1 hd (Ioo_subset_Icc_self (L.cell i).midpoint_mem)
    have hval : (L.cell i).midpoint = (L.cell j).midpoint := congrArg Subtype.val hij
    rw [hval]
    exact Ioo_subset_Icc_self (L.cell j).midpoint_mem

private theorem Level.midpoint_protected {k : ℕ} (L : Level k) (i : Fin (branchCount k)) :
    ((L.midpointEmbedding i : Interval) : ℝ) ∈ ProtectedZone :=
  L.interior_protected i (L.cell i).midpoint_mem

private theorem exists_cell_subset_nhds {a : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    {s : Set ℝ} (hs : s ∈ 𝓝 a) :
    ∃ I : Cell, a ∈ Set.Ioo I.left I.right ∧ I.carrier ⊆ s := by
  have hInterval : Interval ∈ 𝓝 a := Icc_mem_nhds_iff.2 ha
  obtain ⟨l, r, _, hlr, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (inter_mem hs hInterval)
  have hinside : a ∈ Set.Ioo l r := Icc_mem_nhds_iff.1 hlr
  exact ⟨⟨l, r, hinside.1.trans hinside.2,
    hsub.trans inter_subset_right⟩, hinside, hsub.trans inter_subset_left⟩

/-- An enumerated set of exactly `n` distinct interpolation nodes in `[-1, 1]`. -/
structure Row (n : ℕ) where
  /-- Finite type indexing the row's nodes. -/
  ι : Type
  fintypeι : Fintype ι
  decidableEqι : DecidableEq ι
  card_ι : Fintype.card ι = n
  /-- Embedding of the distinct nodes into `[-1,1]`. -/
  node : ι ↪ Interval

attribute [instance] Row.fintypeι Row.decidableEqι

private def fillerZoneEmbedding : FillerZone ↪ Interval where
  toFun x := ⟨x, x.2.1.le, by linarith [x.2.2]⟩
  inj' _ _ h := Subtype.ext (congrArg (fun x : Interval ↦ (x : ℝ)) h)

private noncomputable def fillerSource (n : ℕ) : Fin n ↪ FillerZone := by
  letI : Infinite FillerZone := (Set.Ioo_infinite (by norm_num)).to_subtype
  exact Fin.valEmbedding.trans (Infinite.natEmbedding FillerZone)

private noncomputable def fillerEmbedding (n : ℕ) : Fin n ↪ Interval :=
  (fillerSource n).trans fillerZoneEmbedding

private noncomputable def prescribedSumEmbedding {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι ↪ Interval) (hz : ∀ i, (z i : ℝ) ∈ ProtectedZone) (d : ℕ) :
    ι ⊕ Fin d ↪ Interval where
  toFun := Sum.elim z (fillerEmbedding d)
  inj' := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (z.injective h)
    · have h' := congrArg Subtype.val h
      have hi := hz i
      have hj := (fillerSource d j').2
      change (z i : ℝ) = ((fillerSource d j' : FillerZone) : ℝ) at h'
      norm_num [ProtectedZone, FillerZone] at hi hj
      exfalso
      linarith
    · have h' := congrArg Subtype.val h
      have hi := (fillerSource d j).2
      have hj := hz i'
      change ((fillerSource d j : FillerZone) : ℝ) = (z i' : ℝ) at h'
      norm_num [ProtectedZone, FillerZone] at hi hj
      exfalso
      linarith
    · exact congrArg Sum.inr ((fillerEmbedding d).injective h)

private noncomputable def rowContaining {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι ↪ Interval) (hz : ∀ i, (z i : ℝ) ∈ ProtectedZone) (n : ℕ)
    (hcard : Fintype.card ι ≤ n) : Row n where
  ι := ι ⊕ Fin (n - Fintype.card ι)
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := by simp [Nat.add_sub_of_le hcard]
  node := prescribedSumEmbedding z hz _

private lemma eval_lagrangeBasis_eq_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (i : ι) (x : ℝ) :
    (Lagrange.basis s v i).eval x =
      ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  ring

private def lagrangeValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ node i).eval x

private lemma lagrangeValue_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) (x : ℝ) :
    lagrangeValue node i x =
      ∏ j ∈ Finset.univ.erase i, (x - node j) / (node i - node j) :=
  eval_lagrangeBasis_eq_prod Finset.univ node i x

/-- The fundamental Lagrange polynomial associated with node `i`, evaluated at `x`. -/
def fundamental {n : ℕ} (X : Row n) (i : X.ι) (x : ℝ) : ℝ :=
  lagrangeValue (fun j ↦ (X.node j : ℝ)) i x

/-- The Lagrange interpolant determined by a row. -/
def interpolant {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (x : ℝ) : ℝ :=
  ∑ i, f (X.node i) * fundamental X i x

/-- The Lebesgue function determined by a row. -/
def lebesgue {n : ℕ} (X : Row n) (x : ℝ) : ℝ :=
  ∑ i, |fundamental X i x|

/-- The underlying finite set of interpolation nodes. -/
def nodeSet {n : ℕ} (X : Row n) : Finset Interval := Finset.univ.map X.node

@[simp]
theorem card_nodeSet {n : ℕ} (X : Row n) : (nodeSet X).card = n := by
  simp [nodeSet, X.card_ι]

theorem fundamental_eq_prod {n : ℕ} (X : Row n) (i : X.ι) (x : ℝ) :
    fundamental X i x =
      ∏ j ∈ Finset.univ.erase i, (x - X.node j) / (X.node i - X.node j) :=
  lagrangeValue_eq_prod (fun j ↦ (X.node j : ℝ)) i x

private theorem node_injective {n : ℕ} (X : Row n) :
    Function.Injective fun i ↦ (X.node i : ℝ) :=
  fun _ _ h ↦ X.node.injective (Subtype.ext h)

@[simp]
theorem fundamental_at_node {n : ℕ} (X : Row n) (i j : X.ι) :
    fundamental X i (X.node j) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact Lagrange.eval_basis_self (node_injective X).injOn (Finset.mem_univ i)
  · simpa only [fundamental, lagrangeValue] using
      (Lagrange.eval_basis_of_ne (F := ℝ) (s := (Finset.univ : Finset X.ι))
        (v := fun j ↦ (X.node j : ℝ)) h (Finset.mem_univ j))

@[simp]
theorem interpolant_at_node {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (i : X.ι) :
    interpolant X f (X.node i) = f (X.node i) := by
  simp [interpolant]

@[simp]
theorem lebesgue_at_node {n : ℕ} (X : Row n) (i : X.ι) :
    lebesgue X (X.node i) = 1 := by
  rw [lebesgue]
  simp_rw [fundamental_at_node, abs_ite, abs_one, abs_zero]
  exact Fintype.sum_ite_eq' i fun _ : X.ι ↦ (1 : ℝ)

theorem continuous_fundamental {n : ℕ} (X : Row n) (i : X.ι) :
    Continuous (fundamental X i) :=
  (Lagrange.basis Finset.univ (fun j ↦ (X.node j : ℝ)) i).continuous

theorem continuous_lebesgue {n : ℕ} (X : Row n) : Continuous (lebesgue X) := by
  change Continuous fun x ↦ ∑ i, |fundamental X i x|
  exact continuous_finsetSum Finset.univ fun i _ ↦ (continuous_fundamental X i).abs

theorem lebesgue_lt_two_mem_nhds {n : ℕ} (X : Row n) (i : X.ι) :
    {x | lebesgue X x < 2} ∈ 𝓝 (X.node i : ℝ) :=
  (continuous_lebesgue X).continuousAt.preimage_mem_nhds
    (Iio_mem_nhds (show lebesgue X (X.node i) < 2 by simp))

private noncomputable def fillerRow {k : ℕ} (L : Level k) (r : FillerIndex k) :
    Row r.val :=
  rowContaining L.midpointEmbedding L.midpoint_protected r.val
    (by
      simpa using
        (branchCount_le_stageBoundary k).trans
          (Nat.le_of_lt (Finset.mem_Ioo.mp r.2).1))

private def fillerRowIndex {k : ℕ} (L : Level k) (r : FillerIndex k)
    (i : Fin (branchCount k)) : (fillerRow L r).ι := by
  dsimp [fillerRow, rowContaining]
  exact Sum.inl i

@[simp]
private theorem fillerRow_node {k : ℕ} (L : Level k) (r : FillerIndex k)
    (i : Fin (branchCount k)) :
    (fillerRow L r).node (fillerRowIndex L r i) = L.midpointEmbedding i := rfl

private theorem filler_stable_mem_nhds {k : ℕ} (L : Level k)
    (i : Fin (branchCount k)) :
    {x | ∀ r : FillerIndex k, lebesgue (fillerRow L r) x < 2} ∈
      𝓝 ((L.midpointEmbedding i : Interval) : ℝ) := by
  change ∀ᶠ x in 𝓝 ((L.midpointEmbedding i : Interval) : ℝ),
    ∀ r : FillerIndex k, lebesgue (fillerRow L r) x < 2
  exact Filter.eventually_all.2 fun r ↦ by
    have h := lebesgue_lt_two_mem_nhds (fillerRow L r) (fillerRowIndex L r i)
    change ∀ᶠ x in 𝓝 ((fillerRow L r).node (fillerRowIndex L r i) : ℝ),
      lebesgue (fillerRow L r) x < 2 at h
    simpa only [fillerRow_node] using h

private theorem exists_filler_shrink {k : ℕ} (L : Level k)
    (i : Fin (branchCount k)) :
    ∃ J : Cell,
      (L.cell i).midpoint ∈ Set.Ioo J.left J.right ∧
      J.carrier ⊆ Set.Ioo (L.cell i).left (L.cell i).right ∧
      ∀ x ∈ J.carrier, ∀ r : FillerIndex k, lebesgue (fillerRow L r) x ≤ 2 := by
  let stable := {x | ∀ r : FillerIndex k, lebesgue (fillerRow L r) x < 2}
  have hs : Set.Ioo (L.cell i).left (L.cell i).right ∩ stable ∈ 𝓝 (L.cell i).midpoint :=
    inter_mem (Ioo_mem_nhds (L.cell i).midpoint_mem.1 (L.cell i).midpoint_mem.2)
      (filler_stable_mem_nhds L i)
  have hdomain : (L.cell i).midpoint ∈ Set.Ioo (-1 : ℝ) 1 := by
    have hp := L.midpoint_protected i
    change (L.cell i).midpoint ∈ ProtectedZone at hp
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  obtain ⟨J, hmid, hJ⟩ := exists_cell_subset_nhds hdomain hs
  refine ⟨J, hmid, hJ.trans inter_subset_left, ?_⟩
  intro x hx r
  exact (hJ hx).2 r |>.le

private noncomputable def fillerShrink {k : ℕ} (L : Level k)
    (i : Fin (branchCount k)) : Cell := (exists_filler_shrink L i).choose

private theorem fillerShrink_subset {k : ℕ} (L : Level k) (i : Fin (branchCount k)) :
    (fillerShrink L i).carrier ⊆ Set.Ioo (L.cell i).left (L.cell i).right :=
  (exists_filler_shrink L i).choose_spec.2.1

private theorem fillerShrink_stable {k : ℕ} (L : Level k) (i : Fin (branchCount k))
    {x : ℝ} (hx : x ∈ (fillerShrink L i).carrier) (r : FillerIndex k) :
    lebesgue (fillerRow L r) x ≤ 2 :=
  (exists_filler_shrink L i).choose_spec.2.2 x hx r

private noncomputable def shrinkLevel {k : ℕ} (L : Level k) : Level k where
  cell := fillerShrink L
  disjoint := by
    intro i j h
    exact (L.disjoint h).mono
      ((fillerShrink_subset L i).trans Ioo_subset_Icc_self)
      ((fillerShrink_subset L j).trans Ioo_subset_Icc_self)
  interior_protected := by
    intro i x hx
    exact L.interior_protected i (fillerShrink_subset L i (Ioo_subset_Icc_self hx))

private def childCoordinates (k : ℕ) (t : Fin (branchCount (k + 1))) :
    Fin (branchCount k) × Fin (edgeCard k) := by
  rw [branchCount] at t
  exact finProdFinEquiv.symm t

private theorem childCoordinates_injective (k : ℕ) : Function.Injective (childCoordinates k) := by
  intro t u h
  rw [branchCount] at t u
  exact finProdFinEquiv.symm.injective h

private def childCenter {k : ℕ} (L : Level k) (t : Fin (branchCount (k + 1))) : ℝ :=
  let c := childCoordinates k t
  splitCenter ((shrinkLevel L).cell c.1) c.2

private theorem childCenter_mem_split {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) :
    childCenter L t ∈ Set.Ioo
      (splitCell ((shrinkLevel L).cell (childCoordinates k t).1) (edgeCard_pos k)
        (childCoordinates k t).2).left
      (splitCell ((shrinkLevel L).cell (childCoordinates k t).1) (edgeCard_pos k)
        (childCoordinates k t).2).right :=
  splitCenter_mem _ (edgeCard_pos k) _

private def childCenterEmbedding {k : ℕ} (L : Level k) :
    Fin (branchCount (k + 1)) ↪ Interval where
  toFun t :=
    let c := childCoordinates k t
    let I := splitCell ((shrinkLevel L).cell c.1) (edgeCard_pos k) c.2
    ⟨childCenter L t, I.subset_interval
      (Ioo_subset_Icc_self (childCenter_mem_split L t))⟩
  inj' := by
    intro t u h
    have hval : childCenter L t = childCenter L u := congrArg Subtype.val h
    have hp : (childCoordinates k t).1 = (childCoordinates k u).1 := by
      by_contra hp
      have hd := (shrinkLevel L).disjoint hp
      apply Set.disjoint_left.1 hd
      · exact splitCell_subset _ (edgeCard_pos k) (childCoordinates k t).2
          (Ioo_subset_Icc_self (childCenter_mem_split L t))
      · rw [hval]
        exact splitCell_subset _ (edgeCard_pos k) (childCoordinates k u).2
          (Ioo_subset_Icc_self (childCenter_mem_split L u))
    have he : (childCoordinates k t).2 = (childCoordinates k u).2 := by
      apply splitCenter_injective ((shrinkLevel L).cell (childCoordinates k t).1) (edgeCard_pos k)
      dsimp [childCenter] at hval
      simpa only [hp] using hval
    apply childCoordinates_injective k
    exact Prod.ext hp he

private theorem childCenter_protected {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) :
    ((childCenterEmbedding L t : Interval) : ℝ) ∈ ProtectedZone := by
  let c := childCoordinates k t
  apply (shrinkLevel L).interior_protected c.1
  exact splitCell_subset_interior _ (edgeCard_pos k) c.2
    (Ioo_subset_Icc_self (childCenter_mem_split L t))

theorem interpolant_eq_eval_interpolate {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (x : ℝ) :
    interpolant X f x =
      (Lagrange.interpolate Finset.univ (fun i ↦ (X.node i : ℝ))
        fun i ↦ f (X.node i)).eval x := by
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  simp [interpolant, fundamental, lagrangeValue]

theorem interpolant_polynomial {n : ℕ} (X : Row n) (p : ℝ[X]) (x : ℝ)
    (hp : p.degree < n) :
    interpolant X (p.toContinuousMapOn Interval) x = p.eval x := by
  rw [interpolant_eq_eval_interpolate]
  have hp' : p.degree < (Finset.univ : Finset X.ι).card := by simpa [X.card_ι] using hp
  simpa using congrArg (Polynomial.eval x)
    (Lagrange.eq_interpolate (s := Finset.univ) (v := fun i ↦ (X.node i : ℝ))
      (node_injective X).injOn hp') |>.symm

theorem lebesgue_nonneg {n : ℕ} (X : Row n) (x : ℝ) : 0 ≤ lebesgue X x := by
  change 0 ≤ ∑ i, |fundamental X i x|
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem interpolation_error_le {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (p : ℝ[X])
    {x ε : ℝ} (hx : x ∈ Interval) (hp : p.degree < n)
    (happrox : ∀ y : Interval, |p.eval (y : ℝ) - f y| ≤ ε) :
    |interpolant X f x - f ⟨x, hx⟩| ≤ (1 + lebesgue X x) * ε := by
  have hsum :
      |interpolant X f x - interpolant X (p.toContinuousMapOn Interval) x| ≤
        ε * lebesgue X x := by
    change |(∑ i, f (X.node i) * fundamental X i x) -
      ∑ i, p.eval (X.node i : ℝ) * fundamental X i x| ≤ _
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc
      |∑ i, (f (X.node i) - p.eval (X.node i : ℝ)) * fundamental X i x| ≤
          ∑ i, |(f (X.node i) - p.eval (X.node i : ℝ)) * fundamental X i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ε * |fundamental X i x| := by
        gcongr with i
        rw [abs_mul]
        gcongr
        simpa [abs_sub_comm] using happrox (X.node i)
      _ = ε * lebesgue X x := by simp [lebesgue, Finset.mul_sum]
  calc
    |interpolant X f x - f ⟨x, hx⟩| =
        |(interpolant X f x - interpolant X (p.toContinuousMapOn Interval) x) +
          (interpolant X (p.toContinuousMapOn Interval) x - f ⟨x, hx⟩)| := by ring_nf
    _ ≤ |interpolant X f x - interpolant X (p.toContinuousMapOn Interval) x| +
        |interpolant X (p.toContinuousMapOn Interval) x - f ⟨x, hx⟩| := abs_add_le _ _
    _ ≤ ε * lebesgue X x + ε := add_le_add hsum (by
      rw [interpolant_polynomial X p x hp]
      exact happrox ⟨x, hx⟩)
    _ = (1 + lebesgue X x) * ε := by ring

theorem tendsto_interpolant_of_eventually_le (X : ∀ n : ℕ, Row n)
    (f : C(Interval, ℝ)) (x : Interval) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, lebesgue (X n) x ≤ C) :
    Tendsto (fun n ↦ interpolant (X n) f x) atTop (𝓝 (f x)) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hδ : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap (-1) 1 f _ hδ
  rw [norm_lt_iff _ hδ] at hp
  refine eventually_atTop.1 ?_
  filter_upwards [hbound, eventually_gt_atTop p.natDegree] with n hn hdeg
  have hpdeg : p.degree < n :=
    lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hdeg)
  have happrox (y : Interval) : |p.eval (y : ℝ) - f y| ≤ ε / (2 * (C + 1)) := by
    simpa [Real.norm_eq_abs] using (hp y).le
  rw [Real.dist_eq]
  calc
    |interpolant (X n) f x - f x| ≤
        (1 + lebesgue (X n) x) * (ε / (2 * (C + 1))) :=
      interpolation_error_le (X n) f p x.2 hpdeg happrox
    _ ≤ (1 + C) * (ε / (2 * (C + 1))) := by gcongr
    _ = ε / 2 := by field_simp; ring
    _ < ε := half_lt_self hε

private lemma univ_erase_inl {α β : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] (a : α) :
    (Finset.univ.erase (Sum.inl a) : Finset (α ⊕ β)) =
      (Finset.univ.erase a).disjSum Finset.univ := by
  ext j; rcases j with j | b <;> simp

private lemma univ_erase_inr {α β : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] (b : β) :
    (Finset.univ.erase (Sum.inr b) : Finset (α ⊕ β)) =
      Finset.univ.disjSum (Finset.univ.erase b) := by
  ext j; rcases j with a | j <;> simp

namespace Exterior

private def rawFundamental {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι ↪ ℝ) (i : ι) (x : ℝ) : ℝ :=
  lagrangeValue node i x

private def rawLebesgue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι ↪ ℝ) (x : ℝ) : ℝ := ∑ i, |rawFundamental node i x|

private def closePairNode {B : Type*} (c δ : ℝ) (fixed : B ↪ ℝ) : Fin 2 ⊕ B → ℝ
  | .inl 0 => c
  | .inl 1 => c + δ
  | .inr b => fixed b

private lemma closePairNode_injective {B : Type*} (c δ : ℝ) (fixed : B ↪ ℝ)
    (hδ : δ ≠ 0) (hc : ∀ b, fixed b ≠ c) (hcδ : ∀ b, fixed b ≠ c + δ) :
    Function.Injective (closePairNode c δ fixed) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hδ (by simpa [closePairNode] using hij.symm)
    · exfalso
      exact hδ (by simpa [closePairNode] using hij)
    · rfl
  · fin_cases i
    · exfalso
      exact hc j (by simpa [closePairNode] using hij.symm)
    · exfalso
      exact hcδ j (by simpa [closePairNode] using hij.symm)
  · fin_cases j
    · exfalso
      exact hc i (by simpa [closePairNode] using hij)
    · exfalso
      exact hcδ i (by simpa [closePairNode] using hij)
  · exact congrArg Sum.inr (fixed.injective hij)

private lemma closePair_fundamental_zero {B : Type*} [Fintype B] [DecidableEq B]
    (c δ x : ℝ) (fixed : B ↪ ℝ)
    (hδ : δ ≠ 0) (hc : ∀ b, fixed b ≠ c) (hcδ : ∀ b, fixed b ≠ c + δ) :
    rawFundamental ⟨closePairNode c δ fixed,
      closePairNode_injective c δ fixed hδ hc hcδ⟩ (.inl 0) x =
      -(x - c - δ) / δ * ∏ b, (x - fixed b) / (c - fixed b) := by
  rw [rawFundamental, lagrangeValue_eq_prod, univ_erase_inl, Finset.prod_disjSum]
  rw [show (Finset.univ.erase 0 : Finset (Fin 2)) = {1} by decide]
  simp only [Finset.prod_singleton]
  change
    (x - (c + δ)) / (c - (c + δ)) * ∏ b, (x - fixed b) / (c - fixed b) =
      -(x - c - δ) / δ * ∏ b, (x - fixed b) / (c - fixed b)
  field_simp [hδ]
  ring

private theorem exists_closePair_blowup
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (D U : Set ℝ) (hDcompact : IsCompact D) (hDne : D.Nonempty)
    (hUopen : IsOpen U) (fixed : B ↪ ℝ) (c H : ℝ)
    (hfixedU : ∀ b, fixed b ∈ U) (hcU : c ∈ U)
    (hc : ∀ b, fixed b ≠ c)
    (hDc : ∀ x ∈ D, x ≠ c) (hDfixed : ∀ x ∈ D, ∀ b, x ≠ fixed b)
    (hH : 0 < H) :
    ∃ δ > 0, ∃ hnode : Function.Injective (closePairNode c δ fixed),
      (∀ i, closePairNode c δ fixed i ∈ U) ∧
      ∀ x ∈ D, H ≤ rawLebesgue ⟨closePairNode c δ fixed, hnode⟩ x := by
  let P : ℝ → ℝ := fun x ↦ ∏ b, |(x - fixed b) / (c - fixed b)|
  let g : ℝ → ℝ := fun x ↦ |x - c| * P x
  have P_cont : Continuous P := by
    dsimp only [P]
    fun_prop
  have g_cont : Continuous g := by
    dsimp only [g]
    fun_prop
  have P_pos : ∀ x ∈ D, 0 < P x := by
    intro x hx
    apply Finset.prod_pos
    intro b _
    exact abs_pos.mpr <| div_ne_zero (sub_ne_zero.mpr (hDfixed x hx b))
      (sub_ne_zero.mpr (hc b).symm)
  have g_pos : ∀ x ∈ D, 0 < g x := by
    intro x hx
    exact mul_pos (abs_pos.mpr (sub_ne_zero.mpr (hDc x hx))) (P_pos x hx)
  obtain ⟨xmin, hxmin, hxmin_le⟩ :=
    hDcompact.exists_isMinOn hDne g_cont.continuousOn
  obtain ⟨xmax, hxmax, hP_le⟩ :=
    hDcompact.exists_isMaxOn hDne P_cont.continuousOn
  let γ := g xmin
  let C := P xmax
  have hγ : 0 < γ := g_pos xmin hxmin
  have hC : 0 < C := P_pos xmax hxmax
  have hγ_le : ∀ x ∈ D, γ ≤ g x := fun x hx ↦ hxmin_le hx
  have hP_bound : ∀ x ∈ D, P x ≤ C := fun x hx ↦ hP_le hx
  let distances : Finset ℝ := Finset.univ.image fun b ↦ |fixed b - c|
  have distances_ne : distances.Nonempty := by
    simpa only [distances, Finset.image_nonempty] using (Finset.univ_nonempty :
      (Finset.univ : Finset B).Nonempty)
  let sep := distances.min' distances_ne
  have sep_mem : sep ∈ distances := distances.min'_mem distances_ne
  have hsep : 0 < sep := by
    rcases Finset.mem_image.mp sep_mem with ⟨b, _, hb⟩
    rw [← hb]
    exact abs_pos.mpr (sub_ne_zero.mpr (hc b))
  have sep_le (b : B) : sep ≤ |fixed b - c| :=
    distances.min'_le _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hcU)
  let bound := min ε (min sep (min (γ / (2 * C)) (γ / (2 * H))))
  have hbound : 0 < bound := by
    dsimp only [bound]
    positivity
  let δ := bound / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδε : δ < ε := by
    dsimp only [δ, bound]
    have := min_le_left ε (min sep (min (γ / (2 * C)) (γ / (2 * H))))
    linarith
  have hδsep : δ < sep := by
    dsimp only [δ, bound]
    have := (min_le_right ε (min sep (min (γ / (2 * C)) (γ / (2 * H))))).trans
      (min_le_left sep (min (γ / (2 * C)) (γ / (2 * H))))
    linarith
  have hδCquot : δ ≤ γ / (2 * C) := by
    dsimp only [δ, bound]
    have hle := (min_le_right ε (min sep (min (γ / (2 * C)) (γ / (2 * H))))).trans <|
      (min_le_right sep (min (γ / (2 * C)) (γ / (2 * H)))).trans <|
        min_le_left (γ / (2 * C)) (γ / (2 * H))
    linarith
  have hδHquot : δ ≤ γ / (2 * H) := by
    dsimp only [δ, bound]
    have hle := (min_le_right ε (min sep (min (γ / (2 * C)) (γ / (2 * H))))).trans <|
      (min_le_right sep (min (γ / (2 * C)) (γ / (2 * H)))).trans <|
        min_le_right (γ / (2 * C)) (γ / (2 * H))
    linarith
  have hδC : δ * C ≤ γ / 2 := by
    calc
      δ * C ≤ (γ / (2 * C)) * C := mul_le_mul_of_nonneg_right hδCquot hC.le
      _ = γ / 2 := by field_simp [hC.ne']
  have hδH : δ * H ≤ γ / 2 := by
    calc
      δ * H ≤ (γ / (2 * H)) * H := mul_le_mul_of_nonneg_right hδHquot hH.le
      _ = γ / 2 := by field_simp [hH.ne']
  have hcδU : c + δ ∈ U := hεU <| by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [add_sub_cancel_left, abs_of_pos hδ] using hδε
  have hcδ : ∀ b, fixed b ≠ c + δ := by
    intro b hb
    have hbsep := sep_le b
    rw [hb, add_sub_cancel_left, abs_of_pos hδ] at hbsep
    linarith
  let hnode := closePairNode_injective c δ fixed hδ.ne' hc hcδ
  refine ⟨δ, hδ, hnode, ?_, ?_⟩
  · intro i
    rcases i with i | b
    · fin_cases i
      · exact hcU
      · exact hcδU
    · exact hfixedU b
  · intro x hx
    let node : Fin 2 ⊕ B ↪ ℝ := ⟨closePairNode c δ fixed, hnode⟩
    have hP0 : 0 ≤ P x := (P_pos x hx).le
    have htriangle : |x - c| ≤ |x - c - δ| + δ := by
      calc
        |x - c| = |(x - c - δ) + δ| := by ring_nf
        _ ≤ |x - c - δ| + |δ| := abs_add_le _ _
        _ = |x - c - δ| + δ := by rw [abs_of_pos hδ]
    have hgupper : g x ≤ |x - c - δ| * P x + δ * P x := by
      dsimp only [g]
      nlinarith [mul_le_mul_of_nonneg_right htriangle hP0]
    have hδP : δ * P x ≤ γ / 2 :=
      (mul_le_mul_of_nonneg_left (hP_bound x hx) hδ.le).trans hδC
    have hhalf : γ / 2 ≤ |x - c - δ| * P x := by
      linarith [hγ_le x hx]
    have hmain : H ≤ |x - c - δ| * P x / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith [hδH]
    have hcoeff :
        |rawFundamental node (.inl 0) x| = |x - c - δ| * P x / δ := by
      rw [closePair_fundamental_zero c δ x fixed hδ.ne' hc hcδ]
      simp only [abs_mul, abs_div, abs_neg, abs_of_pos hδ, P, Finset.abs_prod]
      ring
    calc
      H ≤ |x - c - δ| * P x / δ := hmain
      _ = |rawFundamental node (.inl 0) x| := hcoeff.symm
      _ ≤ rawLebesgue node x := Finset.single_le_sum
        (fun i _ ↦ abs_nonneg (rawFundamental node i x))
        (Finset.mem_univ (Sum.inl (0 : Fin 2) : Fin 2 ⊕ B))

end Exterior

namespace Collision

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The data defining one collision pair and one distinguished background target. -/
structure Data (B : Type*) where
  /-- Fixed background-node locations. -/
  background : B → ℝ
  /-- Background index moved toward the evaluation target. -/
  target : B
  /-- Common limiting location of the colliding pair. -/
  center : ℝ
  /-- Velocity of the left sample node. -/
  leftSlope : ℝ
  /-- Velocity of the right sample node. -/
  rightSlope : ℝ
  /-- Desired limiting cardinal coefficient. -/
  amplitude : ℝ

variable (d : Data B)

/-! The following quantities encode the singular collision and its cancellation. -/

/-- Difference between the two sample velocities. -/
def Data.gap : ℝ := d.leftSlope - d.rightSlope

/-- Evaluation target before perturbation. -/
def Data.targetValue : ℝ := d.background d.target

/-- Product of the regular background factors at the collision limit. -/
def Data.backgroundProduct : ℝ :=
  ∏ b ∈ Finset.univ.erase d.target,
    (d.targetValue - d.background b) / (d.center - d.background b)

/-- Velocity assigned to the distinguished background node. -/
def Data.shift : ℝ := d.amplitude * d.gap / d.backgroundProduct

/-- Left member of the colliding sample pair. -/
def Data.leftSample (t : ℝ) : ℝ := d.center + t * d.leftSlope

/-- Right member of the colliding sample pair. -/
def Data.rightSample (t : ℝ) : ℝ := d.center + t * d.rightSlope

/-- A background node, with only the distinguished target moving. -/
def Data.backgroundNode (t : ℝ) (b : B) : ℝ :=
  if b = d.target then d.targetValue + t * d.shift else d.background b

/-- The fixed index type consists of the two colliding samples and all background nodes. -/
def Data.node (t : ℝ) : Fin 2 ⊕ B → ℝ
  | .inl 0 => d.leftSample t
  | .inl 1 => d.rightSample t
  | .inr b => d.backgroundNode t b

/-- Cardinal coefficients with the two sample factors split off. -/
def Data.cardinalCoefficient (t : ℝ) : Fin 2 ⊕ B → ℝ
  | .inl 0 =>
      (d.targetValue - d.rightSample t) / (d.leftSample t - d.rightSample t) *
        ∏ b, (d.targetValue - d.backgroundNode t b) /
          (d.leftSample t - d.backgroundNode t b)
  | .inl 1 =>
      (d.targetValue - d.leftSample t) / (d.rightSample t - d.leftSample t) *
        ∏ b, (d.targetValue - d.backgroundNode t b) /
          (d.rightSample t - d.backgroundNode t b)
  | .inr b =>
      (d.targetValue - d.leftSample t) / (d.backgroundNode t b - d.leftSample t) *
      ((d.targetValue - d.rightSample t) / (d.backgroundNode t b - d.rightSample t)) *
        ∏ b' ∈ Finset.univ.erase b,
          (d.targetValue - d.backgroundNode t b') /
            (d.backgroundNode t b - d.backgroundNode t b')

/-- Limiting coefficient vector at the target. -/
def Data.limitingCoefficient : Fin 2 ⊕ B → ℝ
  | .inl 0 => d.amplitude
  | .inl 1 => -d.amplitude
  | .inr b => if b = d.target then 1 else 0

/-- Exact Lagrange coefficient at the fixed evaluation target. -/
def Data.lagrangeCoefficient (t : ℝ) (i : Fin 2 ⊕ B) : ℝ :=
  (Lagrange.basis Finset.univ (d.node t) i).eval d.targetValue

lemma Data.backgroundProduct_ne_zero
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center) :
    d.backgroundProduct ≠ 0 := by
  rw [Data.backgroundProduct, Finset.prod_ne_zero_iff]
  intro b hb
  rcases Finset.mem_erase.mp hb with ⟨hbt, _⟩
  exact div_ne_zero (sub_ne_zero.mpr (ha.ne hbt.symm))
    (sub_ne_zero.mpr (hc b).symm)

@[simp] lemma Data.backgroundNode_zero (b : B) :
    d.backgroundNode 0 b = d.background b := by
  simp only [Data.backgroundNode, zero_mul, add_zero]
  split_ifs with h
  · subst b
    rfl
  · rfl

lemma Data.continuousAt_backgroundNode (b : B) :
    ContinuousAt (fun t : ℝ => d.backgroundNode t b) 0 := by
  by_cases hb : b = d.target
  · simp only [Data.backgroundNode, hb, if_pos]
    fun_prop
  · simp only [Data.backgroundNode, if_neg hb]
    exact continuousAt_const

omit [Fintype B] [DecidableEq B] in
lemma Data.continuousAt_leftSample :
    ContinuousAt d.leftSample 0 := by
  change ContinuousAt (fun t : ℝ => d.center + t * d.leftSlope) 0
  fun_prop

omit [Fintype B] [DecidableEq B] in
lemma Data.continuousAt_rightSample :
    ContinuousAt d.rightSample 0 := by
  change ContinuousAt (fun t : ℝ => d.center + t * d.rightSlope) 0
  fun_prop

/-- Desingularized left cardinal coefficient. -/
def Data.leftRegular (t : ℝ) : ℝ :=
  (d.targetValue - d.rightSample t) / d.gap *
  ((-d.shift) / (d.leftSample t - d.backgroundNode t d.target)) *
    ∏ b ∈ Finset.univ.erase d.target,
      (d.targetValue - d.backgroundNode t b) /
        (d.leftSample t - d.backgroundNode t b)

/-- Desingularized right cardinal coefficient. -/
def Data.rightRegular (t : ℝ) : ℝ :=
  (d.targetValue - d.leftSample t) / (-d.gap) *
  ((-d.shift) / (d.rightSample t - d.backgroundNode t d.target)) *
    ∏ b ∈ Finset.univ.erase d.target,
      (d.targetValue - d.backgroundNode t b) /
        (d.rightSample t - d.backgroundNode t b)

omit [Fintype B] [DecidableEq B] in
lemma Data.leftSample_sub_rightSample (t : ℝ) :
    d.leftSample t - d.rightSample t = t * d.gap := by
  simp only [Data.leftSample, Data.rightSample, Data.gap]
  ring

omit [Fintype B] [DecidableEq B] in
lemma Data.rightSample_sub_leftSample (t : ℝ) :
    d.rightSample t - d.leftSample t = t * (-d.gap) := by
  simp only [Data.leftSample, Data.rightSample, Data.gap]
  ring

lemma Data.targetValue_sub_targetNode (t : ℝ) :
    d.targetValue - d.backgroundNode t d.target = t * (-d.shift) := by
  simp [Data.backgroundNode]

lemma Data.cardinalCoefficient_left_eq_regular {t : ℝ} (ht : t ≠ 0) :
    d.cardinalCoefficient t (.inl 0) = d.leftRegular t := by
  rw [Data.cardinalCoefficient, ← Finset.mul_prod_erase _ _ (Finset.mem_univ d.target)]
  rw [Data.leftSample_sub_rightSample, Data.targetValue_sub_targetNode]
  simp only [Data.leftRegular]
  field_simp [ht]

lemma Data.cardinalCoefficient_right_eq_regular {t : ℝ} (ht : t ≠ 0) :
    d.cardinalCoefficient t (.inl 1) = d.rightRegular t := by
  rw [Data.cardinalCoefficient, ← Finset.mul_prod_erase _ _ (Finset.mem_univ d.target)]
  rw [Data.rightSample_sub_leftSample, Data.targetValue_sub_targetNode]
  simp only [Data.rightRegular]
  field_simp [ht]

omit [Fintype B] [DecidableEq B] in
@[simp] lemma Data.leftSample_zero : d.leftSample 0 = d.center := by
  simp [Data.leftSample]

omit [Fintype B] [DecidableEq B] in
@[simp] lemma Data.rightSample_zero : d.rightSample 0 = d.center := by
  simp [Data.rightSample]

lemma Data.continuousAt_leftFactor (b : B)
    (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt
      (fun t : ℝ => (d.targetValue - d.backgroundNode t b) /
        (d.leftSample t - d.backgroundNode t b)) 0 :=
  (continuousAt_const.sub (d.continuousAt_backgroundNode b)).div
    (d.continuousAt_leftSample.sub (d.continuousAt_backgroundNode b)) <| by
      simpa using sub_ne_zero.mpr (hc b).symm

lemma Data.continuousAt_rightFactor (b : B)
    (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt
      (fun t : ℝ => (d.targetValue - d.backgroundNode t b) /
        (d.rightSample t - d.backgroundNode t b)) 0 :=
  (continuousAt_const.sub (d.continuousAt_backgroundNode b)).div
    (d.continuousAt_rightSample.sub (d.continuousAt_backgroundNode b)) <| by
      simpa using sub_ne_zero.mpr (hc b).symm

lemma Data.continuousAt_leftProduct
    (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt
      (fun t : ℝ => ∏ b ∈ Finset.univ.erase d.target,
        (d.targetValue - d.backgroundNode t b) /
          (d.leftSample t - d.backgroundNode t b)) 0 :=
  tendsto_finsetProd _ fun b _ => d.continuousAt_leftFactor b hc

lemma Data.continuousAt_rightProduct
    (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt
      (fun t : ℝ => ∏ b ∈ Finset.univ.erase d.target,
        (d.targetValue - d.backgroundNode t b) /
          (d.rightSample t - d.backgroundNode t b)) 0 :=
  tendsto_finsetProd _ fun b _ => d.continuousAt_rightFactor b hc

lemma Data.continuousAt_leftRegular
    (hgap : d.gap ≠ 0) (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt d.leftRegular 0 := by
  rw [show d.leftRegular = fun t =>
      (d.targetValue - d.rightSample t) / d.gap *
      ((-d.shift) / (d.leftSample t - d.backgroundNode t d.target)) *
        ∏ b ∈ Finset.univ.erase d.target,
          (d.targetValue - d.backgroundNode t b) /
            (d.leftSample t - d.backgroundNode t b) from rfl]
  have h₁ : ContinuousAt
      (fun t : ℝ => (d.targetValue - d.rightSample t) / d.gap) 0 :=
    (continuousAt_const.sub d.continuousAt_rightSample).div continuousAt_const hgap
  have h₂ : ContinuousAt
      (fun t : ℝ => (-d.shift) / (d.leftSample t - d.backgroundNode t d.target)) 0 :=
    continuousAt_const.div
      (d.continuousAt_leftSample.sub (d.continuousAt_backgroundNode d.target)) <| by
        simpa using sub_ne_zero.mpr (hc d.target).symm
  exact (h₁.mul h₂).mul (d.continuousAt_leftProduct hc)

lemma Data.continuousAt_rightRegular
    (hgap : d.gap ≠ 0) (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt d.rightRegular 0 := by
  rw [show d.rightRegular = fun t =>
      (d.targetValue - d.leftSample t) / (-d.gap) *
      ((-d.shift) / (d.rightSample t - d.backgroundNode t d.target)) *
        ∏ b ∈ Finset.univ.erase d.target,
          (d.targetValue - d.backgroundNode t b) /
            (d.rightSample t - d.backgroundNode t b) from rfl]
  have h₁ : ContinuousAt
      (fun t : ℝ => (d.targetValue - d.leftSample t) / (-d.gap)) 0 :=
    (continuousAt_const.sub d.continuousAt_leftSample).div continuousAt_const
      (neg_ne_zero.mpr hgap)
  have h₂ : ContinuousAt
      (fun t : ℝ => (-d.shift) / (d.rightSample t - d.backgroundNode t d.target)) 0 :=
    continuousAt_const.div
      (d.continuousAt_rightSample.sub (d.continuousAt_backgroundNode d.target)) <| by
        simpa using sub_ne_zero.mpr (hc d.target).symm
  exact (h₁.mul h₂).mul (d.continuousAt_rightProduct hc)

lemma Data.leftRegular_zero
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    d.leftRegular 0 = d.amplitude := by
  have hQ := d.backgroundProduct_ne_zero ha hc
  have hct : d.center - d.background d.target ≠ 0 :=
    sub_ne_zero.mpr (hc d.target).symm
  rw [Data.leftRegular]
  simp only [Data.leftSample_zero, Data.rightSample_zero, Data.backgroundNode_zero]
  change
    (d.targetValue - d.center) / d.gap *
      ((-d.shift) / (d.center - d.background d.target)) *
        d.backgroundProduct = d.amplitude
  rw [Data.shift, Data.targetValue]
  field_simp [hgap, hQ, hct]
  ring

lemma Data.rightRegular_zero
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    d.rightRegular 0 = -d.amplitude := by
  have hQ := d.backgroundProduct_ne_zero ha hc
  have hct : d.center - d.background d.target ≠ 0 :=
    sub_ne_zero.mpr (hc d.target).symm
  rw [Data.rightRegular]
  simp only [Data.leftSample_zero, Data.rightSample_zero, Data.backgroundNode_zero]
  change
    (d.targetValue - d.center) / (-d.gap) *
      ((-d.shift) / (d.center - d.background d.target)) *
        d.backgroundProduct = -d.amplitude
  rw [Data.shift, Data.targetValue]
  field_simp [hgap, hQ, hct]
  ring

lemma Data.tendsto_cardinalCoefficient_left
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    Tendsto (fun t : ℝ => d.cardinalCoefficient t (.inl 0)) (𝓝[>] 0)
      (𝓝 d.amplitude) := by
  rw [← d.leftRegular_zero ha hc hgap]
  apply (d.continuousAt_leftRegular hgap hc).tendsto.mono_left
    nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (d.cardinalCoefficient_left_eq_regular (ne_of_gt ht)).symm

lemma Data.tendsto_cardinalCoefficient_right
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    Tendsto (fun t : ℝ => d.cardinalCoefficient t (.inl 1)) (𝓝[>] 0)
      (𝓝 (-d.amplitude)) := by
  rw [← d.rightRegular_zero ha hc hgap]
  apply (d.continuousAt_rightRegular hgap hc).tendsto.mono_left
    nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (d.cardinalCoefficient_right_eq_regular (ne_of_gt ht)).symm

lemma Data.continuousAt_backgroundFactor (b b' : B)
    (ha : Function.Injective d.background) (hbb' : b ≠ b') :
    ContinuousAt
      (fun t : ℝ =>
        (d.targetValue - d.backgroundNode t b') /
          (d.backgroundNode t b - d.backgroundNode t b')) 0 :=
  (continuousAt_const.sub (d.continuousAt_backgroundNode b')).div
    ((d.continuousAt_backgroundNode b).sub (d.continuousAt_backgroundNode b')) <| by
      simpa using sub_ne_zero.mpr (ha.ne hbb')

lemma Data.continuousAt_backgroundProductAt (b : B)
    (ha : Function.Injective d.background) :
    ContinuousAt
      (fun t : ℝ => ∏ b' ∈ Finset.univ.erase b,
        (d.targetValue - d.backgroundNode t b') /
          (d.backgroundNode t b - d.backgroundNode t b')) 0 :=
  tendsto_finsetProd _ fun b' hb' =>
    d.continuousAt_backgroundFactor b b' ha (Finset.mem_erase.mp hb').1.symm

lemma Data.continuousAt_cardinalCoefficient_background (b : B)
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center) :
    ContinuousAt (fun t : ℝ => d.cardinalCoefficient t (.inr b)) 0 := by
  rw [show (fun t : ℝ => d.cardinalCoefficient t (.inr b)) = fun t =>
      (d.targetValue - d.leftSample t) / (d.backgroundNode t b - d.leftSample t) *
      ((d.targetValue - d.rightSample t) / (d.backgroundNode t b - d.rightSample t)) *
        ∏ b' ∈ Finset.univ.erase b,
          (d.targetValue - d.backgroundNode t b') /
            (d.backgroundNode t b - d.backgroundNode t b') from rfl]
  have h₁ : ContinuousAt
      (fun t : ℝ =>
        (d.targetValue - d.leftSample t) / (d.backgroundNode t b - d.leftSample t)) 0 :=
    (continuousAt_const.sub d.continuousAt_leftSample).div
      ((d.continuousAt_backgroundNode b).sub d.continuousAt_leftSample) <| by
        simpa using sub_ne_zero.mpr (hc b)
  have h₂ : ContinuousAt
      (fun t : ℝ =>
        (d.targetValue - d.rightSample t) / (d.backgroundNode t b - d.rightSample t)) 0 :=
    (continuousAt_const.sub d.continuousAt_rightSample).div
      ((d.continuousAt_backgroundNode b).sub d.continuousAt_rightSample) <| by
        simpa using sub_ne_zero.mpr (hc b)
  exact (h₁.mul h₂).mul (d.continuousAt_backgroundProductAt b ha)

lemma Data.cardinalCoefficient_background_zero (b : B)
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center) :
    d.cardinalCoefficient 0 (.inr b) = if b = d.target then 1 else 0 := by
  simp only [Data.cardinalCoefficient, Data.leftSample_zero, Data.rightSample_zero,
    Data.backgroundNode_zero]
  by_cases hb : b = d.target
  · subst b
    rw [if_pos rfl]
    have htc : d.background d.target - d.center ≠ 0 :=
      sub_ne_zero.mpr (hc d.target)
    have hp :
        (∏ b' ∈ Finset.univ.erase d.target,
          (d.targetValue - d.background b') /
            (d.background d.target - d.background b')) = 1 := by
      apply Finset.prod_eq_one
      intro b' hb'
      have hne : d.background d.target - d.background b' ≠ 0 :=
        sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hb').symm)
      simpa [Data.targetValue] using div_self hne
    simp only [Data.targetValue] at hp ⊢
    rw [hp]
    simp [div_self htc]
  · rw [if_neg hb]
    have hmem : d.target ∈ Finset.univ.erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hb, Finset.mem_univ _⟩
    have hp :
        (∏ b' ∈ Finset.univ.erase b,
          (d.targetValue - d.background b') /
            (d.background b - d.background b')) = 0 := by
      apply Finset.prod_eq_zero hmem
      simp [Data.targetValue]
    rw [hp, mul_zero]

lemma Data.tendsto_cardinalCoefficient_background (b : B)
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center) :
    Tendsto (fun t : ℝ => d.cardinalCoefficient t (.inr b)) (𝓝[>] 0)
      (𝓝 (if b = d.target then 1 else 0)) := by
  rw [← d.cardinalCoefficient_background_zero b ha hc]
  exact (d.continuousAt_cardinalCoefficient_background b ha hc).tendsto.mono_left
    nhdsWithin_le_nhds

theorem Data.tendsto_cardinalCoefficient
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    Tendsto d.cardinalCoefficient (𝓝[>] 0) (𝓝 d.limitingCoefficient) := by
  rw [tendsto_pi_nhds]
  intro i
  rcases i with i | b
  · fin_cases i
    · simpa [Data.limitingCoefficient] using
        d.tendsto_cardinalCoefficient_left ha hc hgap
    · simpa [Data.limitingCoefficient] using
        d.tendsto_cardinalCoefficient_right ha hc hgap
  · simpa [Data.limitingCoefficient] using
      d.tendsto_cardinalCoefficient_background b ha hc

lemma Data.lagrangeCoefficient_left (t : ℝ) :
    d.lagrangeCoefficient t (.inl 0) = d.cardinalCoefficient t (.inl 0) := by
  rw [Data.lagrangeCoefficient, eval_lagrangeBasis_eq_prod, univ_erase_inl, Finset.prod_disjSum,
    show (Finset.univ.erase 0 : Finset (Fin 2)) = {1} by decide]
  simp only [Finset.prod_singleton, Data.node]
  rfl

lemma Data.lagrangeCoefficient_right (t : ℝ) :
    d.lagrangeCoefficient t (.inl 1) = d.cardinalCoefficient t (.inl 1) := by
  rw [Data.lagrangeCoefficient, eval_lagrangeBasis_eq_prod, univ_erase_inl, Finset.prod_disjSum,
    show (Finset.univ.erase 1 : Finset (Fin 2)) = {0} by decide]
  simp only [Finset.prod_singleton, Data.node]
  rfl

lemma Data.lagrangeCoefficient_background (t : ℝ) (b : B) :
    d.lagrangeCoefficient t (.inr b) = d.cardinalCoefficient t (.inr b) := by
  rw [Data.lagrangeCoefficient, eval_lagrangeBasis_eq_prod, univ_erase_inr, Finset.prod_disjSum,
    show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Finset.prod_pair (show (0 : Fin 2) ≠ 1 by decide)]
  simp only [Data.node]
  rfl

lemma Data.lagrangeCoefficient_eq_cardinalCoefficient (t : ℝ) :
    d.lagrangeCoefficient t = d.cardinalCoefficient t := by
  funext i
  rcases i with i | b
  · fin_cases i
    · exact d.lagrangeCoefficient_left t
    · exact d.lagrangeCoefficient_right t
  · exact d.lagrangeCoefficient_background t b

/-- The actual Mathlib Lagrange coefficient vector tends to
`(A, -A, 1, 0, …)` along positive collision parameters. -/
theorem Data.tendsto_lagrangeCoefficient
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0) :
    Tendsto d.lagrangeCoefficient (𝓝[>] 0) (𝓝 d.limitingCoefficient) := by
  apply (d.tendsto_cardinalCoefficient ha hc hgap).congr'
  exact .of_forall fun t => (d.lagrangeCoefficient_eq_cardinalCoefficient t).symm

/-- For all sufficiently small positive parameters, the collision path consists of distinct
nodes in `(-1, 1)`. -/
theorem Data.eventually_node_good
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center)
    (hgap : d.gap ≠ 0)
    (hcenter : d.center ∈ Set.Ioo (-1 : ℝ) 1)
    (hbackground : ∀ b, d.background b ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ t in 𝓝[>] 0,
      Function.Injective (d.node t) ∧
        ∀ i, d.node t i ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hleftT : Tendsto d.leftSample (𝓝[>] 0) (𝓝 d.center) := by
    simpa only [Data.leftSample_zero] using
      d.continuousAt_leftSample.tendsto.mono_left nhdsWithin_le_nhds
  have hrightT : Tendsto d.rightSample (𝓝[>] 0) (𝓝 d.center) := by
    simpa only [Data.rightSample_zero] using
      d.continuousAt_rightSample.tendsto.mono_left nhdsWithin_le_nhds
  have hsampleT (i : Fin 2) :
      Tendsto (fun t => d.node t (.inl i)) (𝓝[>] 0) (𝓝 d.center) := by
    fin_cases i
    · simpa only [Data.node] using hleftT
    · simpa only [Data.node] using hrightT
  have hbackgroundT (b : B) :
      Tendsto (fun t => d.node t (.inr b)) (𝓝[>] 0) (𝓝 (d.background b)) := by
    simpa only [Data.node, Data.backgroundNode_zero] using
      (d.continuousAt_backgroundNode b).tendsto.mono_left nhdsWithin_le_nhds
  have hsample : ∀ᶠ t in 𝓝[>] 0,
      Function.Injective (fun i => d.node t (.inl i)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · exfalso
        apply hgap
        have hz : t * d.gap = 0 := by
          rw [← d.leftSample_sub_rightSample t]
          change d.leftSample t = d.rightSample t at hij
          rw [hij, sub_self]
        exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht)
    · fin_cases j
      · exfalso
        apply hgap
        have hz : t * d.gap = 0 := by
          rw [← d.leftSample_sub_rightSample t]
          change d.rightSample t = d.leftSample t at hij
          rw [hij.symm, sub_self]
        exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht)
      · rfl
  have hbackgroundInj : ∀ᶠ t in 𝓝[>] 0,
      Function.Injective (fun b => d.node t (.inr b)) := by
    change ∀ᶠ t in 𝓝[>] 0, ∀ b b',
      d.node t (.inr b) = d.node t (.inr b') → b = b'
    rw [Filter.eventually_all]
    intro b
    rw [Filter.eventually_all]
    intro b'
    by_cases hbb : b = b'
    · exact .of_forall fun _ _ => hbb
    · have ht : Tendsto
          (fun t => d.node t (.inr b) - d.node t (.inr b'))
          (𝓝[>] 0) (𝓝 (d.background b - d.background b')) :=
        (hbackgroundT b).sub (hbackgroundT b')
      exact (ht.eventually_ne (sub_ne_zero.mpr (ha.ne hbb))).mono fun _ hne heq =>
        (hne (sub_eq_zero.mpr heq)).elim
  have hcross : ∀ᶠ t in 𝓝[>] 0, ∀ i b,
      d.node t (.inl i) ≠ d.node t (.inr b) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro b
    have ht : Tendsto
        (fun t => d.node t (.inl i) - d.node t (.inr b))
        (𝓝[>] 0) (𝓝 (d.center - d.background b)) :=
      (hsampleT i).sub (hbackgroundT b)
    exact (ht.eventually_ne (sub_ne_zero.mpr (hc b).symm)).mono fun _ hne heq =>
      (hne (sub_eq_zero.mpr heq)).elim
  have hsampleMem : ∀ᶠ t in 𝓝[>] 0, ∀ i,
      d.node t (.inl i) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (hsampleT i).eventually (Ioo_mem_nhds hcenter.1 hcenter.2)
  have hbackgroundMem : ∀ᶠ t in 𝓝[>] 0, ∀ b,
      d.node t (.inr b) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Filter.eventually_all]
    intro b
    exact (hbackgroundT b).eventually
      (Ioo_mem_nhds (hbackground b).1 (hbackground b).2)
  filter_upwards [hsample, hbackgroundInj, hcross, hsampleMem, hbackgroundMem]
    with t hs hb hsb hsI hbI
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases i with i | b <;> rcases j with j | b'
    · exact congrArg Sum.inl (hs hij)
    · exact (hsb i b' hij).elim
    · exact (hsb j b hij.symm).elim
    · exact congrArg Sum.inr (hb hij)
  · rintro (i | b)
    · exact hsI i
    · exact hbI b

end Collision

namespace Collision

variable {B : Type*} [Fintype B] [DecidableEq B] (d : Data B)

/-- Total `ℓ¹` error from the limiting coefficient vector. -/
def Data.coefficientError (t : ℝ) : ℝ :=
  ∑ i, |d.lagrangeCoefficient t i - d.limitingCoefficient i|

theorem Data.tendsto_coefficientError
    (ha : Function.Injective d.background)
    (hc : ∀ b, d.background b ≠ d.center) (hgap : d.gap ≠ 0) :
    Tendsto d.coefficientError (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_pi_nhds.1 (d.tendsto_lagrangeCoefficient ha hc hgap)
  have hi (i : Fin 2 ⊕ B) :
      Tendsto (fun t ↦ |d.lagrangeCoefficient t i - d.limitingCoefficient i|)
        (𝓝[>] 0) (𝓝 0) := by
    simpa using ((h i).sub_const (d.limitingCoefficient i)).abs
  change Tendsto (fun t ↦ ∑ i, |d.lagrangeCoefficient t i - d.limitingCoefficient i|)
    (𝓝[>] 0) (𝓝 0)
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ fun i _ ↦ hi i

end Collision

private def edgeEquiv (k : ℕ) : Edge k ≃ Fin (edgeCard k) := Fintype.equivFin _

private def childEdge {k : ℕ} (t : Fin (branchCount (k + 1))) : Edge k :=
  (edgeEquiv k).symm (childCoordinates k t).2

private def sampleSlope {n : ℕ} (i : Fin n) : ℝ := i + 1

private def pairRowSize (k : ℕ) (t : Fin (branchCount (k + 1))) : ℕ :=
  stageStart k + t

private theorem pairRowSize_bound (k : ℕ) (t : Fin (branchCount (k + 1))) :
    branchCount (k + 1) + 2 ≤ pairRowSize k t := by
  dsimp [pairRowSize, stageStart]
  omega

private abbrev PairBackground (k : ℕ) (t : Fin (branchCount (k + 1))) :=
  Fin (branchCount (k + 1)) ⊕ Fin (pairRowSize k t - (branchCount (k + 1) + 2))

private noncomputable def pairBackgroundEmbedding {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) : PairBackground k t ↪ Interval :=
  prescribedSumEmbedding (childCenterEmbedding L) (childCenter_protected L) _

private def pairData {k : ℕ} (L : Level k) (t : Fin (branchCount (k + 1))) :
    Collision.Data (PairBackground k t) where
  background b := pairBackgroundEmbedding L t b
  target := Sum.inl t
  center := 1 / 2
  leftSlope := sampleSlope (childEdge t).val.1
  rightSlope := sampleSlope (childEdge t).val.2
  amplitude := k + 1

private theorem pairBackground_injective {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) : Function.Injective (pairData L t).background := by
  intro i j h
  change (((pairBackgroundEmbedding L t) i : Interval) : ℝ) =
    (((pairBackgroundEmbedding L t) j : Interval) : ℝ) at h
  exact (pairBackgroundEmbedding L t).injective (Subtype.ext h)

private theorem pairBackground_mem {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) (b : PairBackground k t) :
    (pairData L t).background b ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases b with i | i
  · have h := childCenter_protected L i
    change (((childCenterEmbedding L) i : Interval) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := (fillerSource _ i).2
    change (((fillerEmbedding _) i : Interval) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1
    change (((fillerSource _) i : FillerZone) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1
    exact ⟨h.1, by linarith [h.2]⟩

private theorem pairBackground_ne_center {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) (b : PairBackground k t) :
    (pairData L t).background b ≠ (pairData L t).center := by
  rcases b with i | i
  · have h := childCenter_protected L i
    change (((childCenterEmbedding L) i : Interval) : ℝ) ≠ 1 / 2
    linarith [h.2]
  · have h := (fillerSource _ i).2
    change (((fillerSource _) i : FillerZone) : ℝ) ≠ 1 / 2
    linarith [h.2]

private theorem pairGap_ne_zero {k : ℕ} (L : Level k)
    (t : Fin (branchCount (k + 1))) : (pairData L t).gap ≠ 0 := by
  have h := (childEdge t).2
  dsimp [Collision.Data.gap, pairData, sampleSlope]
  apply sub_ne_zero.mpr
  intro heq
  apply h.ne
  apply Fin.ext
  exact_mod_cast (show ((childEdge t).val.1 : ℝ) = (childEdge t).val.2 by linarith)

private def stageSample (k : ℕ) (t : ℝ) (i : Fin ((k + 1) ^ 2 + 1)) : ℝ :=
  1 / 2 + t * sampleSlope i

private theorem exists_pairParameter (k : ℕ) (L : Level k) :
    ∃ t : ℝ, 0 < t ∧
      (∀ i, stageSample k t i ∈ ReserveZone) ∧
      ∀ u : Fin (branchCount (k + 1)),
        Function.Injective ((pairData L u).node t) ∧
        (∀ i, (pairData L u).node t i ∈ Set.Ioo (-1 : ℝ) 1) ∧
        (pairData L u).coefficientError t < 1 / (k + 1 : ℝ) ∧
        |t * (pairData L u).shift| < 1 / (2 * (k + 1 : ℝ)) := by
  have hsamples : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ i, stageSample k t i ∈ ReserveZone := by
    rw [Filter.eventually_all]
    intro i
    have ht : Tendsto (fun t : ℝ ↦ stageSample k t i) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
      simpa [stageSample] using
        (show ContinuousAt (fun t : ℝ ↦ 1 / 2 + t * sampleSlope i) 0 by
          fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hrows : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ u : Fin (branchCount (k + 1)),
        Function.Injective ((pairData L u).node t) ∧
        (∀ i, (pairData L u).node t i ∈ Set.Ioo (-1 : ℝ) 1) ∧
        (pairData L u).coefficientError t < 1 / (k + 1 : ℝ) ∧
        |t * (pairData L u).shift| < 1 / (2 * (k + 1 : ℝ)) := by
    rw [Filter.eventually_all]
    intro u
    have hgood := (pairData L u).eventually_node_good
      (pairBackground_injective L u) (pairBackground_ne_center L u)
      (pairGap_ne_zero L u) (by norm_num [pairData]) (pairBackground_mem L u)
    have herr := (pairData L u).tendsto_coefficientError
      (pairBackground_injective L u) (pairBackground_ne_center L u)
      (pairGap_ne_zero L u) |>.eventually
        (Iio_mem_nhds (show (0 : ℝ) < 1 / (k + 1 : ℝ) by positivity))
    have hshift : Tendsto (fun t : ℝ ↦ |t * (pairData L u).shift|)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using
        (show ContinuousAt (fun t : ℝ ↦ |t * (pairData L u).shift|) 0 by
          fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    have hshift' := hshift.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / (2 * (k + 1 : ℝ)) by positivity))
    exact hgood.and (herr.and hshift') |>.mono fun _ h ↦
      ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hs, hr⟩ := (hpos.and (hsamples.and hrows)).exists
  exact ⟨t, ht, hs, hr⟩

private noncomputable def pairParameter (k : ℕ) (L : Level k) : ℝ :=
  (exists_pairParameter k L).choose

private theorem pairParameter_pos (k : ℕ) (L : Level k) : 0 < pairParameter k L :=
  (exists_pairParameter k L).choose_spec.1

private theorem pairParameter_sample (k : ℕ) (L : Level k)
    (i : Fin ((k + 1) ^ 2 + 1)) : stageSample k (pairParameter k L) i ∈ ReserveZone :=
  (exists_pairParameter k L).choose_spec.2.1 i

private theorem pairParameter_good (k : ℕ) (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    Function.Injective ((pairData L u).node (pairParameter k L)) ∧
    (∀ i, (pairData L u).node (pairParameter k L) i ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (pairData L u).coefficientError (pairParameter k L) < 1 / (k + 1 : ℝ) ∧
    |pairParameter k L * (pairData L u).shift| < 1 / (2 * (k + 1 : ℝ)) :=
  (exists_pairParameter k L).choose_spec.2.2 u

private noncomputable def pairRow {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) : Row (pairRowSize k u) where
  ι := Fin 2 ⊕ PairBackground k u
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := by
    simp only [PairBackground, Fintype.card_sum, Fintype.card_fin]
    have := pairRowSize_bound k u
    omega
  node :=
    { toFun := fun i ↦ ⟨(pairData L u).node (pairParameter k L) i,
        Ioo_subset_Icc_self ((pairParameter_good k L u).2.1 i)⟩
      inj' := fun _ _ h ↦ (pairParameter_good k L u).1 (congrArg Subtype.val h) }

private def pairSampleIndex {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) (i : Fin 2) : (pairRow L u).ι := Sum.inl i

private def pairTargetIndex {k : ℕ} (L : Level k)
    (u v : Fin (branchCount (k + 1))) : (pairRow L u).ι := Sum.inr (Sum.inl v)

@[simp]
private theorem pairRow_node {k : ℕ} (L : Level k) (u : Fin (branchCount (k + 1)))
    (i : (pairRow L u).ι) :
    ((pairRow L u).node i : ℝ) = (pairData L u).node (pairParameter k L) i := rfl

private theorem pairRow_error {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    (∑ i, |fundamental (pairRow L u) i (childCenter L u) -
      (pairData L u).limitingCoefficient i|) < 1 / (k + 1 : ℝ) := by
  change (pairData L u).coefficientError (pairParameter k L) < 1 / (k + 1 : ℝ)
  exact (pairParameter_good k L u).2.2.1

@[simp]
private theorem pairRow_other_target {k : ℕ} (L : Level k)
    {u v : Fin (branchCount (k + 1))} (hvu : v ≠ u) :
    (pairRow L u).node (pairTargetIndex L u v) = childCenterEmbedding L v := by
  apply Subtype.ext
  have hsum : (Sum.inl v : PairBackground k u) ≠ Sum.inl u := by
    intro h
    exact hvu (Sum.inl.inj h)
  have htarget : (Sum.inl v : PairBackground k u) ≠ (pairData L u).target := by
    simpa [pairData] using hsum
  change (pairData L u).backgroundNode (pairParameter k L) (Sum.inl v) = childCenter L v
  rw [Collision.Data.backgroundNode, if_neg htarget]
  rfl

private def stageSampleEmbedding (k : ℕ) (L : Level k) :
    Fin ((k + 1) ^ 2 + 1) ↪ Interval where
  toFun i := ⟨stageSample k (pairParameter k L) i,
    Ioo_subset_Icc_self (by
      have h := pairParameter_sample k L i
      exact ⟨by linarith [h.1], by linarith [h.2]⟩)⟩
  inj' := by
    intro i j h
    have h' := congrArg Subtype.val h
    dsimp [stageSample, sampleSlope] at h'
    apply Fin.ext
    have ht := pairParameter_pos k L
    exact_mod_cast (show (i : ℝ) = j by nlinarith)

private theorem pairRow_left_sample {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    (pairRow L u).node (pairSampleIndex L u 0) =
      stageSampleEmbedding k L (childEdge u).val.1 := by
  rfl

private theorem pairRow_right_sample {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    (pairRow L u).node (pairSampleIndex L u 1) =
      stageSampleEmbedding k L (childEdge u).val.2 := by
  rfl

private theorem pairLimiting_sum_abs {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    (∑ i, |(pairData L u).limitingCoefficient i|) = 2 * (k + 1 : ℝ) + 1 := by
  have hk : 0 ≤ (k : ℝ) + 1 := by positivity
  simp only [Collision.Data.limitingCoefficient, pairData, one_div, neg_add_rev,
    Fintype.sum_sum_type, Fin.sum_univ_two, abs_of_nonneg hk, Sum.inl.injEq,
    reduceCtorEq, ↓reduceIte, abs_zero, Finset.sum_const_zero, add_zero]
  simp only [abs_ite, abs_one, abs_zero]
  rw [Fintype.sum_ite_eq' u (fun _ ↦ (1 : ℝ))]
  rw [show (-1 + -(k : ℝ)) = -(k + 1) by ring, abs_neg, abs_of_nonneg hk]
  ring

private theorem pairRow_lebesgue_gt {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    k + 1 < lebesgue (pairRow L u) (childCenter L u) := by
  have htriangle :
      (∑ i, |(pairData L u).limitingCoefficient i|) ≤
        lebesgue (pairRow L u) (childCenter L u) +
          ∑ i, |fundamental (pairRow L u) i (childCenter L u) -
            (pairData L u).limitingCoefficient i| := by
    calc
      (∑ i, |(pairData L u).limitingCoefficient i|) ≤
          ∑ i, (|fundamental (pairRow L u) i (childCenter L u)| +
            |fundamental (pairRow L u) i (childCenter L u) -
              (pairData L u).limitingCoefficient i|) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |(pairData L u).limitingCoefficient i| =
              |fundamental (pairRow L u) i (childCenter L u) +
                ((pairData L u).limitingCoefficient i -
                  fundamental (pairRow L u) i (childCenter L u))| := by ring_nf
          _ ≤ |fundamental (pairRow L u) i (childCenter L u)| +
              |(pairData L u).limitingCoefficient i -
                fundamental (pairRow L u) i (childCenter L u)| := abs_add_le _ _
          _ = |fundamental (pairRow L u) i (childCenter L u)| +
              |fundamental (pairRow L u) i (childCenter L u) -
                (pairData L u).limitingCoefficient i| := by rw [abs_sub_comm]
      _ = lebesgue (pairRow L u) (childCenter L u) +
          ∑ i, |fundamental (pairRow L u) i (childCenter L u) -
            (pairData L u).limitingCoefficient i| := by
        rw [Finset.sum_add_distrib]
        rfl
  rw [pairLimiting_sum_abs L u] at htriangle
  have herr := pairRow_error L u
  have hk1 : (1 : ℝ) ≤ k + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hinv : 1 / (k + 1 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (show (0 : ℝ) < k + 1 by positivity)]
    simpa only [one_mul] using hk1
  nlinarith

private theorem pairTarget_displacement {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    |((pairRow L u).node (pairTargetIndex L u u) : ℝ) - childCenter L u| <
      1 / (2 * (k + 1 : ℝ)) := by
  rw [pairRow_node]
  change |(pairData L u).backgroundNode (pairParameter k L) (Sum.inl u) -
    childCenter L u| < _
  rw [Collision.Data.backgroundNode,
    if_pos (show Sum.inl u = (pairData L u).target by rfl)]
  change |childCenter L u + pairParameter k L * (pairData L u).shift -
    childCenter L u| < _
  simpa only [add_sub_cancel_left] using (pairParameter_good k L u).2.2.2

private def pairCoefficientErrorAt {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) (x : ℝ) : ℝ :=
  ∑ i, |fundamental (pairRow L u) i x - (pairData L u).limitingCoefficient i|

private theorem continuous_pairCoefficientErrorAt {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) : Continuous (pairCoefficientErrorAt L u) :=
  continuous_finsetSum Finset.univ fun i _ =>
    ((continuous_fundamental (pairRow L u) i).sub continuous_const).abs

private def childSplitCell {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) : Cell :=
  splitCell ((shrinkLevel L).cell (childCoordinates k u).1) (edgeCard_pos k)
    (childCoordinates k u).2

private theorem childCenter_mem_childSplit {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) :
    childCenter L u ∈ Set.Ioo (childSplitCell L u).left (childSplitCell L u).right :=
  childCenter_mem_split L u

private theorem childSplitCell_disjoint {k : ℕ} (L : Level k)
    {u v : Fin (branchCount (k + 1))} (huv : u ≠ v) :
    Disjoint (childSplitCell L u).carrier (childSplitCell L v).carrier := by
  have hc : childCoordinates k u ≠ childCoordinates k v :=
    (childCoordinates_injective k).ne huv
  by_cases hp : (childCoordinates k u).1 = (childCoordinates k v).1
  · have he : (childCoordinates k u).2 ≠ (childCoordinates k v).2 := fun h =>
      hc (Prod.ext hp h)
    simpa only [childSplitCell, hp] using splitCell_disjoint
      ((shrinkLevel L).cell (childCoordinates k v).1) (edgeCard_pos k) he
  · exact ((shrinkLevel L).disjoint hp).mono
      (splitCell_subset _ (edgeCard_pos k) _)
      (splitCell_subset _ (edgeCard_pos k) _)

private theorem pairRow_other_lebesgue_center {k : ℕ} (L : Level k)
    {u v : Fin (branchCount (k + 1))} (huv : u ≠ v) :
    lebesgue (pairRow L u) (childCenter L v) = 1 := by
  have hnode := congrArg Subtype.val
    (pairRow_other_target (L := L) (u := u) (v := v) huv.symm)
  change ((pairRow L u).node (pairTargetIndex L u v) : ℝ) = childCenter L v at hnode
  rw [← hnode]
  exact lebesgue_at_node _ _

private theorem exists_preCell {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) :
    ∃ J : Cell,
      childCenter L v ∈ Set.Ioo J.left J.right ∧
      J.carrier ⊆ (childSplitCell L v).carrier ∧
      ∀ x ∈ J.carrier,
        k + 1 ≤ lebesgue (pairRow L v) x ∧
        pairCoefficientErrorAt L v x ≤ 1 / (k + 1 : ℝ) ∧
        |x - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| ≤
          1 / (k + 1 : ℝ) ∧
        ∀ u, u ≠ v → lebesgue (pairRow L u) x ≤ 2 := by
  have hhigh : {x | k + 1 < lebesgue (pairRow L v) x} ∈ 𝓝 (childCenter L v) :=
    (continuous_lebesgue (pairRow L v)).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (pairRow_lebesgue_gt L v))
  have herr0 : pairCoefficientErrorAt L v (childCenter L v) < 1 / (k + 1 : ℝ) :=
    pairRow_error L v
  have herr : {x | pairCoefficientErrorAt L v x < 1 / (k + 1 : ℝ)} ∈
      𝓝 (childCenter L v) :=
    (continuous_pairCoefficientErrorAt L v).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds herr0)
  have hnear : {x | |x - childCenter L v| < 1 / (2 * (k + 1 : ℝ))} ∈
      𝓝 (childCenter L v) := by
    have hcont : Continuous fun x : ℝ => |x - childCenter L v| :=
      (continuous_id.sub continuous_const).abs
    have hk : (0 : ℝ) < k + 1 := by exact_mod_cast Nat.succ_pos k
    have hradius : (0 : ℝ) < 1 / (2 * (k + 1 : ℝ)) :=
      one_div_pos.mpr (mul_pos (by norm_num) hk)
    have hzero : |childCenter L v - childCenter L v| < 1 / (2 * (k + 1 : ℝ)) := by
      simpa only [sub_self, abs_zero] using hradius
    exact hcont.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds hzero)
  have hother : {x | ∀ u, u ≠ v → lebesgue (pairRow L u) x < 2} ∈
      𝓝 (childCenter L v) := by
    change ∀ᶠ x in 𝓝 (childCenter L v), ∀ u, u ≠ v → lebesgue (pairRow L u) x < 2
    rw [Filter.eventually_all]
    intro u
    by_cases huv : u = v
    · exact .of_forall fun _ h => (h huv).elim
    · have hcenter : lebesgue (pairRow L u) (childCenter L v) < 2 := by
        rw [pairRow_other_lebesgue_center L huv]
        norm_num
      have hu := (continuous_lebesgue (pairRow L u)).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds hcenter)
      filter_upwards [hu] with x hx
      exact fun _ => hx
  have hgood : {x |
      k + 1 < lebesgue (pairRow L v) x ∧
      pairCoefficientErrorAt L v x < 1 / (k + 1 : ℝ) ∧
      |x - childCenter L v| < 1 / (2 * (k + 1 : ℝ)) ∧
      ∀ u, u ≠ v → lebesgue (pairRow L u) x < 2} ∈ 𝓝 (childCenter L v) := by
    filter_upwards [hhigh, herr, hnear, hother] with x hx₁ hx₂ hx₃ hx₄
    exact ⟨hx₁, hx₂, hx₃, hx₄⟩
  have hsplit : Set.Ioo (childSplitCell L v).left (childSplitCell L v).right ∈
      𝓝 (childCenter L v) :=
    Ioo_mem_nhds (childCenter_mem_childSplit L v).1 (childCenter_mem_childSplit L v).2
  have hdomain : childCenter L v ∈ Set.Ioo (-1 : ℝ) 1 := by
    have h := childCenter_protected L v
    change childCenter L v ∈ ProtectedZone at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨J, hcenter, hJ⟩ := exists_cell_subset_nhds hdomain (inter_mem hsplit hgood)
  refine ⟨J, hcenter, fun x hx => Ioo_subset_Icc_self (hJ hx).1, ?_⟩
  intro x hx
  have hg := (hJ hx).2
  refine ⟨hg.1.le, hg.2.1.le, ?_, fun u hu => (hg.2.2.2 u hu).le⟩
  apply le_of_lt
  calc
    |x - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| ≤
        |x - childCenter L v| +
          |childCenter L v - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| :=
      abs_sub_le _ _ _
    _ < 1 / (2 * (k + 1 : ℝ)) + 1 / (2 * (k + 1 : ℝ)) :=
      add_lt_add hg.2.2.1 (by simpa only [abs_sub_comm] using pairTarget_displacement L v)
    _ = 1 / (k + 1 : ℝ) := by
      have hk : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hk]
      norm_num

private noncomputable def preCell {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) : Cell :=
  (exists_preCell L v).choose

private theorem preCell_spec {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) :
    childCenter L v ∈ Set.Ioo (preCell L v).left (preCell L v).right ∧
    (preCell L v).carrier ⊆ (childSplitCell L v).carrier ∧
    ∀ x ∈ (preCell L v).carrier,
      k + 1 ≤ lebesgue (pairRow L v) x ∧
      pairCoefficientErrorAt L v x ≤ 1 / (k + 1 : ℝ) ∧
      |x - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| ≤
        1 / (k + 1 : ℝ) ∧
      ∀ u, u ≠ v → lebesgue (pairRow L u) x ≤ 2 :=
  (exists_preCell L v).choose_spec

private theorem preCell_subset_parent {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) :
    (preCell L v).carrier ⊆ (L.cell (childCoordinates k v).1).carrier := by
  intro x hx
  exact Ioo_subset_Icc_self (fillerShrink_subset L (childCoordinates k v).1
    (splitCell_subset _ (edgeCard_pos k) _ ((preCell_spec L v).2.1 hx)))

private noncomputable def preLevel {k : ℕ} (L : Level k) : Level (k + 1) where
  cell := preCell L
  disjoint := by
    intro u v huv
    exact (childSplitCell_disjoint L huv).mono
      (preCell_spec L u).2.1 (preCell_spec L v).2.1
  interior_protected := by
    intro v x hx
    exact (shrinkLevel L).interior_protected (childCoordinates k v).1
      (splitCell_subset_interior _ (edgeCard_pos k) _
        ((preCell_spec L v).2.1 (Ioo_subset_Icc_self hx)))

private theorem preLevel_cell_subset_parent {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) :
    ((preLevel L).cell v).carrier ⊆ (L.cell (childCoordinates k v).1).carrier :=
  preCell_subset_parent L v

private theorem preLevel_spec {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) {x : ℝ}
    (hx : x ∈ ((preLevel L).cell v).carrier) :
    k + 1 ≤ lebesgue (pairRow L v) x ∧
    pairCoefficientErrorAt L v x ≤ 1 / (k + 1 : ℝ) ∧
    |x - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| ≤
      1 / (k + 1 : ℝ) ∧
    ∀ u, u ≠ v → lebesgue (pairRow L u) x ≤ 2 :=
  (preCell_spec L v).2.2 x hx

private def firstBranch (k : ℕ) : Fin (branchCount k) := ⟨0, branchCount_pos k⟩

private def levelOpen {k : ℕ} (L : Level k) : Set ℝ :=
  ⋃ i, Set.Ioo (L.cell i).left (L.cell i).right

private theorem levelOpen_isOpen {k : ℕ} (L : Level k) : IsOpen (levelOpen L) :=
  isOpen_iUnion fun _ ↦ isOpen_Ioo

private def exteriorMark {k : ℕ} (L : Level k) (i : Fin (branchCount k)) : ℝ :=
  splitCenter (L.cell i) (3 : Fin 4)

private theorem exteriorMark_mem {k : ℕ} (L : Level k) (i : Fin (branchCount k)) :
    exteriorMark L i ∈ Set.Ioo (L.cell i).left (L.cell i).right :=
  splitCell_subset_interior (L.cell i) (by norm_num) (3 : Fin 4)
    (Ioo_subset_Icc_self (splitCenter_mem (L.cell i) (by norm_num) (3 : Fin 4)))

private def exteriorMarkEmbedding {k : ℕ} (L : Level k) :
    Fin (branchCount k) ↪ Interval where
  toFun i := ⟨exteriorMark L i, (L.cell i).subset_interval
    (Ioo_subset_Icc_self (exteriorMark_mem L i))⟩
  inj' := by
    intro i j h
    by_contra hij
    have hval : exteriorMark L i = exteriorMark L j := congrArg Subtype.val h
    apply Set.disjoint_left.1 (L.disjoint hij)
      (Ioo_subset_Icc_self (exteriorMark_mem L i))
    rw [hval]
    exact Ioo_subset_Icc_self (exteriorMark_mem L j)

private def exteriorFillerCell {k : ℕ} (L : Level k) : Cell :=
  splitCell (L.cell (firstBranch k)) (by norm_num) (0 : Fin 4)

private def exteriorCenter {k : ℕ} (L : Level k) : ℝ :=
  splitCenter (L.cell (firstBranch k)) (1 : Fin 4)

private theorem exteriorCenter_mem {k : ℕ} (L : Level k) :
    exteriorCenter L ∈ Set.Ioo (L.cell (firstBranch k)).left
      (L.cell (firstBranch k)).right :=
  splitCell_subset_interior _ (by norm_num) (1 : Fin 4)
    (Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (1 : Fin 4)))

private theorem exteriorFiller_mem {k n : ℕ} (L : Level k) (i : Fin n) :
    ((cellPointEmbedding (exteriorFillerCell L) n i : Interval) : ℝ) ∈
      Set.Ioo (L.cell (firstBranch k)).left (L.cell (firstBranch k)).right :=
  splitCell_subset_interior _ (by norm_num) (0 : Fin 4)
    (Ioo_subset_Icc_self (cellPointEmbedding_mem (exteriorFillerCell L) n i))

private theorem stageBoundary_child_bound (k : ℕ) :
    branchCount (k + 1) + 2 ≤ stageBoundary (k + 1) := by
  rw [stageBoundary_succ]
  dsimp [stageStart]
  omega

private abbrev ExteriorBackground (k : ℕ) :=
  Fin (branchCount (k + 1)) ⊕
    Fin (stageBoundary (k + 1) - (branchCount (k + 1) + 2))

private def exteriorFixedEmbedding {k : ℕ} (P : Level (k + 1)) :
    ExteriorBackground k ↪ ℝ where
  toFun := Sum.elim (fun i ↦ exteriorMark P i)
    (fun i ↦ (cellPointEmbedding (exteriorFillerCell P) _ i : ℝ))
  inj' := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl ((exteriorMarkEmbedding P).injective (Subtype.ext h))
    · exfalso
      change exteriorMark P i =
        ((cellPointEmbedding (exteriorFillerCell P) _ j : Interval) : ℝ) at h
      by_cases hi : i = firstBranch (k + 1)
      · subst i
        change splitCenter (P.cell (firstBranch (k + 1))) (3 : Fin 4) = _ at h
        apply Set.disjoint_left.1
          (splitCell_disjoint (P.cell (firstBranch (k + 1))) (by norm_num)
            (show (3 : Fin 4) ≠ 0 by decide))
          (Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (3 : Fin 4)))
        rw [h]
        exact Ioo_subset_Icc_self (cellPointEmbedding_mem (exteriorFillerCell P) _ j)
      · apply Set.disjoint_left.1 (P.disjoint hi)
          (Ioo_subset_Icc_self (exteriorMark_mem P i))
        rw [h]
        exact Ioo_subset_Icc_self (exteriorFiller_mem P j)
    · exfalso
      change ((cellPointEmbedding (exteriorFillerCell P) _ i : Interval) : ℝ) =
        exteriorMark P j at h
      by_cases hj : j = firstBranch (k + 1)
      · subst j
        change _ = splitCenter (P.cell (firstBranch (k + 1))) (3 : Fin 4) at h
        apply Set.disjoint_left.1
          (splitCell_disjoint (P.cell (firstBranch (k + 1))) (by norm_num)
            (show (0 : Fin 4) ≠ 3 by decide))
          (Ioo_subset_Icc_self (cellPointEmbedding_mem (exteriorFillerCell P) _ i))
        rw [h]
        exact Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (3 : Fin 4))
      · apply Set.disjoint_left.1 (P.disjoint (Ne.symm hj))
          (Ioo_subset_Icc_self (exteriorFiller_mem P i))
        rw [h]
        exact Ioo_subset_Icc_self (exteriorMark_mem P j)
    · exact congrArg Sum.inr ((cellPointEmbedding (exteriorFillerCell P) _).injective
        (Subtype.ext h))

private theorem exteriorFixed_mem_open {k : ℕ} (P : Level (k + 1))
    (b : ExteriorBackground k) : exteriorFixedEmbedding P b ∈ levelOpen P := by
  rcases b with i | i
  · exact Set.mem_iUnion.2 ⟨i, exteriorMark_mem P i⟩
  · exact Set.mem_iUnion.2 ⟨firstBranch (k + 1), exteriorFiller_mem P i⟩

private theorem exteriorCenter_mem_open {k : ℕ} (P : Level (k + 1)) :
    exteriorCenter P ∈ levelOpen P :=
  Set.mem_iUnion.2 ⟨firstBranch (k + 1), exteriorCenter_mem P⟩

private theorem exteriorFixed_ne_center {k : ℕ} (P : Level (k + 1))
    (b : ExteriorBackground k) : exteriorFixedEmbedding P b ≠ exteriorCenter P := by
  rcases b with i | i
  · intro h
    change exteriorMark P i = exteriorCenter P at h
    by_cases hi : i = firstBranch (k + 1)
    · subst i
      change splitCenter (P.cell (firstBranch (k + 1))) (3 : Fin 4) =
        splitCenter (P.cell (firstBranch (k + 1))) (1 : Fin 4) at h
      apply Set.disjoint_left.1
        (splitCell_disjoint (P.cell (firstBranch (k + 1))) (by norm_num)
          (show (3 : Fin 4) ≠ 1 by decide))
        (Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (3 : Fin 4)))
      rw [h]
      exact Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (1 : Fin 4))
    · apply Set.disjoint_left.1 (P.disjoint hi)
        (Ioo_subset_Icc_self (exteriorMark_mem P i))
      rw [h]
      exact Ioo_subset_Icc_self (exteriorCenter_mem P)
  · intro h
    change ((cellPointEmbedding (exteriorFillerCell P) _ i : Interval) : ℝ) =
      exteriorCenter P at h
    apply Set.disjoint_left.1
      (splitCell_disjoint (P.cell (firstBranch (k + 1))) (by norm_num)
        (show (0 : Fin 4) ≠ 1 by decide))
      (Ioo_subset_Icc_self (cellPointEmbedding_mem (exteriorFillerCell P) _ i))
    rw [h]
    exact Ioo_subset_Icc_self (splitCenter_mem _ (by norm_num) (1 : Fin 4))

private def exteriorDomain {k : ℕ} (P : Level (k + 1)) : Set ℝ :=
  Interval \ levelOpen P

private theorem exteriorDomain_isCompact {k : ℕ} (P : Level (k + 1)) :
    IsCompact (exteriorDomain P) := by
  simpa only [exteriorDomain, sdiff_eq] using
    isCompact_Icc.inter_right (levelOpen_isOpen P).isClosed_compl

private theorem exteriorDomain_nonempty {k : ℕ} (P : Level (k + 1)) :
    (exteriorDomain P).Nonempty := by
  refine ⟨1, ⟨by norm_num [Interval], ?_⟩⟩
  intro h
  rcases Set.mem_iUnion.1 h with ⟨i, hi⟩
  have hp := P.interior_protected i hi
  norm_num [ProtectedZone] at hp

private theorem exteriorDomain_ne_center {k : ℕ} (P : Level (k + 1))
    (x : ℝ) (hx : x ∈ exteriorDomain P) : x ≠ exteriorCenter P := by
  intro h
  exact hx.2 (h ▸ exteriorCenter_mem_open P)

private theorem exteriorDomain_ne_fixed {k : ℕ} (P : Level (k + 1))
    (x : ℝ) (hx : x ∈ exteriorDomain P) (b : ExteriorBackground k) :
    x ≠ exteriorFixedEmbedding P b := by
  intro h
  exact hx.2 (h ▸ exteriorFixed_mem_open P b)

private theorem exists_exteriorParameter (k : ℕ) (P : Level (k + 1)) :
    ∃ δ > 0, ∃ hnode : Function.Injective
        (Exterior.closePairNode (exteriorCenter P) δ (exteriorFixedEmbedding P)),
      (∀ i, Exterior.closePairNode (exteriorCenter P) δ (exteriorFixedEmbedding P) i ∈
        levelOpen P) ∧
      ∀ x ∈ exteriorDomain P,
        k + 1 ≤ Exterior.rawLebesgue
          ⟨Exterior.closePairNode (exteriorCenter P) δ (exteriorFixedEmbedding P), hnode⟩ x := by
  let _ : Nonempty (ExteriorBackground k) := ⟨Sum.inl (firstBranch (k + 1))⟩
  exact Exterior.exists_closePair_blowup (exteriorDomain P) (levelOpen P)
    (exteriorDomain_isCompact P) (exteriorDomain_nonempty P) (levelOpen_isOpen P)
    (exteriorFixedEmbedding P) (exteriorCenter P) (k + 1)
    (exteriorFixed_mem_open P) (exteriorCenter_mem_open P) (exteriorFixed_ne_center P)
    (exteriorDomain_ne_center P) (exteriorDomain_ne_fixed P) (by positivity)

private noncomputable def exteriorParameter (k : ℕ) (P : Level (k + 1)) : ℝ :=
  (exists_exteriorParameter k P).choose

private theorem exteriorNodeInjective (k : ℕ) (P : Level (k + 1)) :
    Function.Injective (Exterior.closePairNode (exteriorCenter P) (exteriorParameter k P)
      (exteriorFixedEmbedding P)) :=
  (exists_exteriorParameter k P).choose_spec.2.choose

private theorem exteriorNode_mem (k : ℕ) (P : Level (k + 1)) (i) :
    Exterior.closePairNode (exteriorCenter P) (exteriorParameter k P)
      (exteriorFixedEmbedding P) i ∈ levelOpen P :=
  (exists_exteriorParameter k P).choose_spec.2.choose_spec.1 i

private theorem exteriorRaw_high (k : ℕ) (P : Level (k + 1))
    {x : ℝ} (hx : x ∈ exteriorDomain P) :
    k + 1 ≤ Exterior.rawLebesgue
      ⟨Exterior.closePairNode (exteriorCenter P) (exteriorParameter k P)
        (exteriorFixedEmbedding P), exteriorNodeInjective k P⟩ x :=
  (exists_exteriorParameter k P).choose_spec.2.choose_spec.2 x hx

private theorem levelOpen_subset_interval {k : ℕ} (L : Level k) :
    levelOpen L ⊆ Interval := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  exact (L.cell i).subset_interval (Ioo_subset_Icc_self hi)

private noncomputable def exteriorRow (k : ℕ) (P : Level (k + 1)) :
    Row (stageBoundary (k + 1)) where
  ι := Fin 2 ⊕ ExteriorBackground k
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := by
    simp only [ExteriorBackground, Fintype.card_sum, Fintype.card_fin]
    have := stageBoundary_child_bound k
    omega
  node :=
    { toFun := fun i ↦
        ⟨Exterior.closePairNode (exteriorCenter P) (exteriorParameter k P)
          (exteriorFixedEmbedding P) i,
          levelOpen_subset_interval P (exteriorNode_mem k P i)⟩
      inj' := fun _ _ h ↦ exteriorNodeInjective k P (congrArg Subtype.val h) }

private def exteriorMarkIndex (k : ℕ) (P : Level (k + 1))
    (i : Fin (branchCount (k + 1))) : (exteriorRow k P).ι :=
  Sum.inr (Sum.inl i)

@[simp]
private theorem exteriorRow_mark (k : ℕ) (P : Level (k + 1))
    (i : Fin (branchCount (k + 1))) :
    ((exteriorRow k P).node (exteriorMarkIndex k P i) : ℝ) = exteriorMark P i := rfl

private theorem exteriorRow_high (k : ℕ) (P : Level (k + 1))
    {x : ℝ} (hx : x ∈ Interval) (hout : ∀ i, x ∉ (P.cell i).carrier) :
    k + 1 ≤ lebesgue (exteriorRow k P) x := by
  have hxD : x ∈ exteriorDomain P := ⟨hx, by
    intro hopen
    rcases Set.mem_iUnion.1 hopen with ⟨i, hi⟩
    exact hout i (Ioo_subset_Icc_self hi)⟩
  exact exteriorRaw_high k P hxD

private theorem exists_finalCell (k : ℕ) (P : Level (k + 1))
    (i : Fin (branchCount (k + 1))) :
    ∃ J : Cell,
      exteriorMark P i ∈ Set.Ioo J.left J.right ∧
      J.carrier ⊆ Set.Ioo (P.cell i).left (P.cell i).right ∧
      ∀ x ∈ J.carrier, lebesgue (exteriorRow k P) x ≤ 2 := by
  have hstable : {x | lebesgue (exteriorRow k P) x < 2} ∈ 𝓝 (exteriorMark P i) := by
    have h := lebesgue_lt_two_mem_nhds (exteriorRow k P) (exteriorMarkIndex k P i)
    simpa only [exteriorRow_mark] using h
  have hparent : Set.Ioo (P.cell i).left (P.cell i).right ∈ 𝓝 (exteriorMark P i) :=
    Ioo_mem_nhds (exteriorMark_mem P i).1 (exteriorMark_mem P i).2
  have hdomain : exteriorMark P i ∈ Set.Ioo (-1 : ℝ) 1 := by
    have hp := P.interior_protected i (exteriorMark_mem P i)
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  obtain ⟨J, hmark, hJ⟩ := exists_cell_subset_nhds hdomain (inter_mem hparent hstable)
  exact ⟨J, hmark, fun x hx ↦ (hJ hx).1, fun x hx ↦ (hJ hx).2.le⟩

private noncomputable def finalCell (k : ℕ) (P : Level (k + 1))
    (i : Fin (branchCount (k + 1))) : Cell := (exists_finalCell k P i).choose

private theorem finalCell_spec (k : ℕ) (P : Level (k + 1))
    (i : Fin (branchCount (k + 1))) :
    exteriorMark P i ∈ Set.Ioo (finalCell k P i).left (finalCell k P i).right ∧
    (finalCell k P i).carrier ⊆ Set.Ioo (P.cell i).left (P.cell i).right ∧
    ∀ x ∈ (finalCell k P i).carrier, lebesgue (exteriorRow k P) x ≤ 2 :=
  (exists_finalCell k P i).choose_spec

private noncomputable def finalLevel (k : ℕ) (P : Level (k + 1)) : Level (k + 1) where
  cell := finalCell k P
  disjoint := by
    intro i j hij
    exact (P.disjoint hij).mono
      ((finalCell_spec k P i).2.1.trans Ioo_subset_Icc_self)
      ((finalCell_spec k P j).2.1.trans Ioo_subset_Icc_self)
  interior_protected := by
    intro i x hx
    exact P.interior_protected i ((finalCell_spec k P i).2.1 (Ioo_subset_Icc_self hx))

private noncomputable def nextLevel {k : ℕ} (L : Level k) : Level (k + 1) :=
  finalLevel k (preLevel L)

private theorem nextLevel_subset_preLevel {k : ℕ} (L : Level k)
    (i : Fin (branchCount (k + 1))) :
    ((nextLevel L).cell i).carrier ⊆ ((preLevel L).cell i).carrier :=
  (finalCell_spec k (preLevel L) i).2.1.trans Ioo_subset_Icc_self

private theorem nextLevel_subset_parent {k : ℕ} (L : Level k)
    (i : Fin (branchCount (k + 1))) :
    ((nextLevel L).cell i).carrier ⊆ (L.cell (childCoordinates k i).1).carrier :=
  (nextLevel_subset_preLevel L i).trans (preLevel_cell_subset_parent L i)

private theorem nextLevel_exterior_stable {k : ℕ} (L : Level k)
    (i : Fin (branchCount (k + 1))) {x : ℝ} (hx : x ∈ ((nextLevel L).cell i).carrier) :
    lebesgue (exteriorRow k (preLevel L)) x ≤ 2 :=
  (finalCell_spec k (preLevel L) i).2.2 x hx

private theorem nextLevel_pair_spec {k : ℕ} (L : Level k)
    (v : Fin (branchCount (k + 1))) {x : ℝ} (hx : x ∈ ((nextLevel L).cell v).carrier) :
    k + 1 ≤ lebesgue (pairRow L v) x ∧
    pairCoefficientErrorAt L v x ≤ 1 / (k + 1 : ℝ) ∧
    |x - ((pairRow L v).node (pairTargetIndex L v v) : ℝ)| ≤
      1 / (k + 1 : ℝ) ∧
    ∀ u, u ≠ v → lebesgue (pairRow L u) x ≤ 2 :=
  preLevel_spec L v (nextLevel_subset_preLevel L v hx)

private noncomputable def levels : (k : ℕ) → Level k
  | 0 => rootLevel
  | k + 1 => nextLevel (levels k)

@[simp] private theorem levels_succ (k : ℕ) : levels (k + 1) = nextLevel (levels k) := rfl

private theorem stageBoundary_strictMono : StrictMono stageBoundary :=
  strictMono_nat_of_lt_succ stageBoundary_lt_succ

private theorem exists_stage_upper (n : ℕ) : ∃ k, n ≤ stageBoundary (k + 1) :=
  ⟨n, (Nat.le_succ n).trans (stageBoundary_strictMono.id_le (n + 1))⟩

private noncomputable def stageIndex (n : ℕ) : ℕ := Nat.find (exists_stage_upper n)

private theorem stageIndex_upper (n : ℕ) : n ≤ stageBoundary (stageIndex n + 1) :=
  Nat.find_spec (exists_stage_upper n)

private theorem stageIndex_lower {n : ℕ} (hn : 2 < n) :
    stageBoundary (stageIndex n) < n := by
  cases hindex : stageIndex n with
  | zero => simpa only [hindex, stageBoundary] using hn
  | succ k =>
      apply Nat.lt_of_not_ge
      apply Nat.find_min (exists_stage_upper n)
      change k < stageIndex n
      omega

private theorem stageIndex_eq_of_bounds {n k : ℕ}
    (hlower : stageBoundary k < n) (hupper : n ≤ stageBoundary (k + 1)) :
    stageIndex n = k := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_stage_upper n) hupper
  · by_contra hle
    have hlt : stageIndex n < k := Nat.lt_of_not_ge hle
    have hbound : stageBoundary (stageIndex n + 1) ≤ stageBoundary k :=
      stageBoundary_strictMono.monotone (Nat.succ_le_iff.mpr hlt)
    exact (not_lt_of_ge ((stageIndex_upper n).trans hbound)) hlower

private theorem tendsto_stageIndex : Tendsto stageIndex atTop atTop := by
  refine tendsto_atTop.2 fun k ↦ ?_
  filter_upwards [eventually_gt_atTop (stageBoundary k)] with n hn
  by_contra hle
  have hlt : stageIndex n < k := Nat.lt_of_not_ge hle
  have hbound : stageBoundary (stageIndex n + 1) ≤ stageBoundary k :=
    stageBoundary_strictMono.monotone (Nat.succ_le_iff.mpr hlt)
  exact (not_le_of_gt hn) ((stageIndex_upper n).trans hbound)

private noncomputable def baseRow (n : ℕ) : Row n where
  ι := Fin n
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := Fintype.card_fin n
  node := fillerEmbedding n

private noncomputable def stageRow (k n : ℕ) (hlower : stageBoundary k < n)
    (hupper : n ≤ stageBoundary (k + 1)) : Row n :=
  if hfiller : n < stageStart k then
    fillerRow (levels k) ⟨n, Finset.mem_Ioo.2 ⟨hlower, hfiller⟩⟩
  else if hpair : n < stageBoundary (k + 1) then
    let u : Fin (branchCount (k + 1)) := ⟨n - stageStart k, by
      rw [stageBoundary_succ] at hpair
      omega⟩
    have hsize : pairRowSize k u = n := by
      dsimp [pairRowSize, u]
      omega
    hsize ▸ pairRow (levels k) u
  else
    have hboundary : stageBoundary (k + 1) = n :=
      Nat.le_antisymm (Nat.le_of_not_gt hpair) hupper
    hboundary ▸ exteriorRow k (preLevel (levels k))

private noncomputable def arrayRow (n : ℕ) : Row n :=
  if hn : n ≤ stageBoundary 0 then baseRow n
  else stageRow (stageIndex n) n
    (stageIndex_lower (by simpa [stageBoundary] using hn)) (stageIndex_upper n)

private theorem two_le_stageBoundary (k : ℕ) : 2 ≤ stageBoundary k := by
  rw [show 2 = stageBoundary 0 by rfl]
  exact stageBoundary_strictMono.monotone (Nat.zero_le k)

private theorem stageStart_le_boundary_succ (k : ℕ) :
    stageStart k ≤ stageBoundary (k + 1) := by
  rw [stageBoundary_succ]
  omega

private theorem pairRowSize_gt_boundary (k : ℕ) (u : Fin (branchCount (k + 1))) :
    stageBoundary k < pairRowSize k u := by
  dsimp [pairRowSize, stageStart]
  omega

private theorem pairRowSize_lt_boundary (k : ℕ) (u : Fin (branchCount (k + 1))) :
    pairRowSize k u < stageBoundary (k + 1) := by
  rw [stageBoundary_succ]
  dsimp [pairRowSize]
  omega

private theorem arrayRow_eq_stage {k n : ℕ} (hlower : stageBoundary k < n)
    (hupper : n ≤ stageBoundary (k + 1)) :
    arrayRow n = stageRow k n hlower hupper := by
  have hn : ¬n ≤ stageBoundary 0 :=
    not_le.2 ((two_le_stageBoundary k).trans_lt hlower)
  rw [arrayRow, dif_neg hn]
  have hindex := stageIndex_eq_of_bounds hlower hupper
  cases hindex
  rfl

private theorem arrayRow_filler {k : ℕ} (r : FillerIndex k) :
    arrayRow r.val = fillerRow (levels k) r := by
  have hlower := (Finset.mem_Ioo.1 r.2).1
  have hupper := (Finset.mem_Ioo.1 r.2).2
  rw [arrayRow_eq_stage hlower
    ((Nat.le_of_lt hupper).trans (stageStart_le_boundary_succ k))]
  rw [stageRow]
  rw [dif_pos hupper]

private theorem pairRow_cast_eq {k : ℕ} (L : Level k)
    {u v : Fin (branchCount (k + 1))} (huv : u = v)
    (hsize : pairRowSize k u = pairRowSize k v) :
    hsize ▸ pairRow L u = pairRow L v := by
  subst v
  rfl

private theorem arrayRow_pair (k : ℕ) (u : Fin (branchCount (k + 1))) :
    arrayRow (pairRowSize k u) = pairRow (levels k) u := by
  have hlower := pairRowSize_gt_boundary k u
  have hupper := (pairRowSize_lt_boundary k u).le
  have hnotfill : ¬pairRowSize k u < stageStart k := by
    dsimp [pairRowSize]
    omega
  rw [arrayRow_eq_stage hlower hupper, stageRow]
  rw [dif_neg hnotfill, dif_pos (pairRowSize_lt_boundary k u)]
  have hu : (⟨pairRowSize k u - stageStart k, by
      dsimp [pairRowSize]
      omega⟩ : Fin (branchCount (k + 1))) = u := by
    apply Fin.ext
    dsimp [pairRowSize]
    omega
  exact pairRow_cast_eq (levels k) hu _

private theorem arrayRow_exterior (k : ℕ) :
    arrayRow (stageBoundary (k + 1)) = exteriorRow k (preLevel (levels k)) := by
  have hlower := stageBoundary_lt_succ k
  have hnotfill : ¬stageBoundary (k + 1) < stageStart k :=
    not_lt.2 (stageStart_le_boundary_succ k)
  rw [arrayRow_eq_stage hlower le_rfl, stageRow]
  rw [dif_neg hnotfill, dif_neg (lt_irrefl _)]

private theorem exists_high_row_in_stage (k : ℕ) (x : Interval) :
    ∃ n, stageBoundary k < n ∧ n ≤ stageBoundary (k + 1) ∧
      k + 1 ≤ lebesgue (arrayRow n) x := by
  by_cases h : ∃ v, (x : ℝ) ∈ ((preLevel (levels k)).cell v).carrier
  · obtain ⟨v, hv⟩ := h
    refine ⟨pairRowSize k v, pairRowSize_gt_boundary k v,
      (pairRowSize_lt_boundary k v).le, ?_⟩
    rw [arrayRow_pair]
    exact (preLevel_spec (levels k) v hv).1
  · refine ⟨stageBoundary (k + 1), stageBoundary_lt_succ k, le_rfl, ?_⟩
    rw [arrayRow_exterior]
    apply exteriorRow_high k (preLevel (levels k)) x.2
    intro i hi
    exact h ⟨i, hi⟩

/-- The Lebesgue functions of the constructed exact-cardinality array are cofinally
unbounded at every point of `[-1,1]`. -/
theorem array_lebesgue_unbounded (x : Interval) (A : ℝ) (N : ℕ) :
    ∃ n ≥ N, A ≤ lebesgue (arrayRow n) x := by
  obtain ⟨j, hj⟩ := exists_nat_ge A
  let k := max N j
  obtain ⟨n, hn, _, hhigh⟩ := exists_high_row_in_stage k x
  refine ⟨n, ?_, hj.trans ?_ |>.trans hhigh⟩
  · exact (le_max_left N j).trans
      ((stageBoundary_strictMono.id_le k).trans (Nat.le_of_lt hn))
  · exact_mod_cast (le_max_right N j).trans (Nat.le_succ k)

private theorem pairLimiting_apply {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) (f : C(Interval, ℝ)) :
    (∑ i, (pairData L u).limitingCoefficient i * f ((pairRow L u).node i)) =
      (k + 1 : ℝ) *
          (f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1))) +
        f ((pairRow L u).node (pairTargetIndex L u u)) := by
  rw [Fintype.sum_sum_type]
  simp only [Collision.Data.limitingCoefficient, pairData, one_div, neg_add_rev,
    Fin.sum_univ_two, Fin.isValue, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, pairSampleIndex, pairTargetIndex, add_left_inj]
  ring

private theorem pairResidual_le {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) (f : C(Interval, ℝ)) (x : ℝ) :
    |∑ i, (fundamental (pairRow L u) i x - (pairData L u).limitingCoefficient i) *
        f ((pairRow L u).node i)| ≤ pairCoefficientErrorAt L u x * ‖f‖ := by
  calc
    |∑ i, (fundamental (pairRow L u) i x - (pairData L u).limitingCoefficient i) *
        f ((pairRow L u).node i)| ≤
        ∑ i, |(fundamental (pairRow L u) i x -
          (pairData L u).limitingCoefficient i) * f ((pairRow L u).node i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |fundamental (pairRow L u) i x -
          (pairData L u).limitingCoefficient i| * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm ((pairRow L u).node i))
        (abs_nonneg _)
    _ = pairCoefficientErrorAt L u x * ‖f‖ := by
      rw [pairCoefficientErrorAt, Finset.sum_mul]

private theorem pair_interpolation_error_le {k : ℕ} (L : Level k)
    (u : Fin (branchCount (k + 1))) (f : C(Interval, ℝ)) (x : ℝ) (hx : x ∈ Interval) :
    |interpolant (pairRow L u) f x - f ⟨x, hx⟩| ≤
      (k + 1 : ℝ) *
          |f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1))| +
        pairCoefficientErrorAt L u x * ‖f‖ +
          |f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩| := by
  let R := ∑ i, (fundamental (pairRow L u) i x -
    (pairData L u).limitingCoefficient i) * f ((pairRow L u).node i)
  have hinterp : interpolant (pairRow L u) f x =
      R + ∑ i, (pairData L u).limitingCoefficient i * f ((pairRow L u).node i) := by
    rw [interpolant]
    dsimp only [R]
    change (∑ i : Fin 2 ⊕ PairBackground k u,
      f ((pairRow L u).node i) * fundamental (pairRow L u) i x) =
      (∑ i : Fin 2 ⊕ PairBackground k u,
        (fundamental (pairRow L u) i x - (pairData L u).limitingCoefficient i) *
          f ((pairRow L u).node i)) +
      ∑ i : Fin 2 ⊕ PairBackground k u,
        (pairData L u).limitingCoefficient i * f ((pairRow L u).node i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinterp, pairLimiting_apply]
  calc
    |R + ((k + 1 : ℝ) *
          (f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1))) +
        f ((pairRow L u).node (pairTargetIndex L u u))) - f ⟨x, hx⟩| =
        |R + (k + 1 : ℝ) *
          (f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1))) +
          (f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩)| := by ring_nf
    _ ≤ |R| + |(k + 1 : ℝ) *
          (f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1)))| +
          |f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩| := by
      calc
        _ ≤ |R + (k + 1 : ℝ) *
              (f ((pairRow L u).node (pairSampleIndex L u 0)) -
                f ((pairRow L u).node (pairSampleIndex L u 1)))| +
              |f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩| :=
          abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact abs_add_le _ _
    _ ≤ pairCoefficientErrorAt L u x * ‖f‖ +
          (k + 1 : ℝ) *
            |f ((pairRow L u).node (pairSampleIndex L u 0)) -
              f ((pairRow L u).node (pairSampleIndex L u 1))| +
          |f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
      gcongr
      exact pairResidual_le L u f x
    _ = (k + 1 : ℝ) *
          |f ((pairRow L u).node (pairSampleIndex L u 0)) -
            f ((pairRow L u).node (pairSampleIndex L u 1))| +
        pairCoefficientErrorAt L u x * ‖f‖ +
          |f ((pairRow L u).node (pairTargetIndex L u u)) - f ⟨x, hx⟩| := by ring

private theorem exists_sampleEdge (k : ℕ) (L : Level k) (f : C(Interval, ℝ)) :
    ∃ e : Edge k,
      |f (stageSampleEmbedding k L e.val.1) - f (stageSampleEmbedding k L e.val.2)| ≤
        2 * ‖f‖ / (k + 1 : ℝ) ^ 2 := by
  have hvalue (i : Fin ((k + 1) ^ 2 + 1)) :
      |f (stageSampleEmbedding k L i)| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (stageSampleEmbedding k L i)
  obtain ⟨r, s, hrs, hclose⟩ :=
    exists_pair_abs_sub_le (Nat.succ_le_succ (Nat.zero_le k)) ‖f‖
      (fun i ↦ f (stageSampleEmbedding k L i)) hvalue
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · refine ⟨⟨(r, s), hrs⟩, ?_⟩
    simpa only [Nat.cast_succ] using hclose
  · refine ⟨⟨(s, r), hsr⟩, ?_⟩
    simpa only [abs_sub_comm, Nat.cast_succ] using hclose

private noncomputable def sampleEdge (k : ℕ) (L : Level k) (f : C(Interval, ℝ)) :
    Edge k := (exists_sampleEdge k L f).choose

private theorem sampleEdge_close (k : ℕ) (L : Level k) (f : C(Interval, ℝ)) :
    |f (stageSampleEmbedding k L (sampleEdge k L f).val.1) -
      f (stageSampleEmbedding k L (sampleEdge k L f).val.2)| ≤
        2 * ‖f‖ / (k + 1 : ℝ) ^ 2 :=
  (exists_sampleEdge k L f).choose_spec

private def childOf (k : ℕ) (p : Fin (branchCount k)) (e : Edge k) :
    Fin (branchCount (k + 1)) := by
  rw [branchCount]
  exact finProdFinEquiv (p, edgeEquiv k e)

@[simp]
private theorem childCoordinates_childOf (k : ℕ) (p : Fin (branchCount k)) (e : Edge k) :
    childCoordinates k (childOf k p e) = (p, edgeEquiv k e) := by
  rw [childCoordinates, childOf]
  exact finProdFinEquiv.symm_apply_apply _

@[simp]
private theorem childEdge_childOf (k : ℕ) (p : Fin (branchCount k)) (e : Edge k) :
    childEdge (childOf k p e) = e := by
  rw [childEdge, childCoordinates_childOf]
  exact (edgeEquiv k).symm_apply_apply e

private noncomputable def selectedPath (f : C(Interval, ℝ)) :
    (k : ℕ) → Fin (branchCount k)
  | 0 => firstBranch 0
  | k + 1 => childOf k (selectedPath f k) (sampleEdge k (levels k) f)

@[simp]
private theorem selectedPath_succ (f : C(Interval, ℝ)) (k : ℕ) :
    selectedPath f (k + 1) =
      childOf k (selectedPath f k) (sampleEdge k (levels k) f) := rfl

private def selectedCarrier (f : C(Interval, ℝ)) (k : ℕ) : Set ℝ :=
  (levels k).cell (selectedPath f k) |>.carrier

private theorem selectedCarrier_succ_subset (f : C(Interval, ℝ)) (k : ℕ) :
    selectedCarrier f (k + 1) ⊆ selectedCarrier f k := by
  rw [selectedCarrier, selectedCarrier, levels_succ, selectedPath_succ]
  simpa only [childCoordinates_childOf] using
    nextLevel_subset_parent (levels k)
      (childOf k (selectedPath f k) (sampleEdge k (levels k) f))

private theorem selectedCarrier_nonempty (f : C(Interval, ℝ)) (k : ℕ) :
    (selectedCarrier f k).Nonempty := ((levels k).cell (selectedPath f k)).nonempty

private theorem selectedCarrier_isClosed (f : C(Interval, ℝ)) (k : ℕ) :
    IsClosed (selectedCarrier f k) := isClosed_Icc

private theorem selectedCarrier_isCompact (f : C(Interval, ℝ)) (k : ℕ) :
    IsCompact (selectedCarrier f k) := isCompact_Icc

private theorem selectedCarrier_iInter_nonempty (f : C(Interval, ℝ)) :
    (⋂ k, selectedCarrier f k).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (selectedCarrier f)
    (selectedCarrier_succ_subset f) (selectedCarrier_nonempty f)
    (selectedCarrier_isCompact f 0) (selectedCarrier_isClosed f)

private noncomputable def selectedPointReal (f : C(Interval, ℝ)) : ℝ :=
  (selectedCarrier_iInter_nonempty f).choose

private theorem selectedPointReal_mem (f : C(Interval, ℝ)) (k : ℕ) :
    selectedPointReal f ∈ selectedCarrier f k :=
  Set.mem_iInter.1 (selectedCarrier_iInter_nonempty f).choose_spec k

private noncomputable def selectedPoint (f : C(Interval, ℝ)) : Interval :=
  ⟨selectedPointReal f,
    ((levels 0).cell (selectedPath f 0)).subset_interval (selectedPointReal_mem f 0)⟩

private theorem preLevel_cell_subset_shrink {k : ℕ} (L : Level k)
    (i : Fin (branchCount (k + 1))) :
    ((preLevel L).cell i).carrier ⊆
      ((shrinkLevel L).cell (childCoordinates k i).1).carrier :=
  (preCell_spec L i).2.1.trans (splitCell_subset _ (edgeCard_pos k) _)

private theorem nextLevel_subset_shrink {k : ℕ} (L : Level k)
    (i : Fin (branchCount (k + 1))) :
    ((nextLevel L).cell i).carrier ⊆
      ((shrinkLevel L).cell (childCoordinates k i).1).carrier :=
  (nextLevel_subset_preLevel L i).trans (preLevel_cell_subset_shrink L i)

private theorem selectedPoint_mem_next (f : C(Interval, ℝ)) (k : ℕ) :
    selectedPointReal f ∈
      ((nextLevel (levels k)).cell (selectedPath f (k + 1))).carrier := by
  simpa only [selectedCarrier, levels_succ] using selectedPointReal_mem f (k + 1)

private theorem selectedPoint_filler_stable (f : C(Interval, ℝ)) (k : ℕ)
    (r : FillerIndex k) :
    lebesgue (fillerRow (levels k) r) (selectedPoint f) ≤ 2 := by
  apply fillerShrink_stable (levels k) (selectedPath f k) _ r
  have h := nextLevel_subset_shrink (levels k) (selectedPath f (k + 1))
    (selectedPoint_mem_next f k)
  change selectedPointReal f ∈ (fillerShrink (levels k) (selectedPath f k)).carrier
  simpa only [selectedPath_succ, childCoordinates_childOf, shrinkLevel] using h

private theorem selectedPoint_exterior_stable (f : C(Interval, ℝ)) (k : ℕ) :
    lebesgue (exteriorRow k (preLevel (levels k))) (selectedPoint f) ≤ 2 :=
  nextLevel_exterior_stable (levels k) (selectedPath f (k + 1))
    (selectedPoint_mem_next f k)

private def selectedChild (f : C(Interval, ℝ)) (k : ℕ) :
    Fin (branchCount (k + 1)) := selectedPath f (k + 1)

@[simp]
private theorem selectedChild_edge (f : C(Interval, ℝ)) (k : ℕ) :
    childEdge (selectedChild f k) = sampleEdge k (levels k) f := by
  change childEdge (childOf k (selectedPath f k) (sampleEdge k (levels k) f)) = _
  exact childEdge_childOf k (selectedPath f k) (sampleEdge k (levels k) f)

private theorem selectedPoint_pair_spec (f : C(Interval, ℝ)) (k : ℕ) :
    k + 1 ≤ lebesgue (pairRow (levels k) (selectedChild f k)) (selectedPoint f) ∧
    pairCoefficientErrorAt (levels k) (selectedChild f k) (selectedPoint f) ≤
      1 / (k + 1 : ℝ) ∧
    |(selectedPoint f : ℝ) -
        ((pairRow (levels k) (selectedChild f k)).node
          (pairTargetIndex (levels k) (selectedChild f k) (selectedChild f k)) : ℝ)| ≤
      1 / (k + 1 : ℝ) ∧
    ∀ u, u ≠ selectedChild f k →
      lebesgue (pairRow (levels k) u) (selectedPoint f) ≤ 2 :=
  nextLevel_pair_spec (levels k) (selectedChild f k) (selectedPoint_mem_next f k)

private theorem selectedPoint_otherPair_stable (f : C(Interval, ℝ)) (k : ℕ)
    {u : Fin (branchCount (k + 1))} (hu : u ≠ selectedChild f k) :
    lebesgue (pairRow (levels k) u) (selectedPoint f) ≤ 2 :=
  (selectedPoint_pair_spec f k).2.2.2 u hu

private theorem selectedPair_samples_close (f : C(Interval, ℝ)) (k : ℕ) :
    |f ((pairRow (levels k) (selectedChild f k)).node
          (pairSampleIndex (levels k) (selectedChild f k) 0)) -
      f ((pairRow (levels k) (selectedChild f k)).node
          (pairSampleIndex (levels k) (selectedChild f k) 1))| ≤
        2 * ‖f‖ / (k + 1 : ℝ) ^ 2 := by
  rw [pairRow_left_sample, pairRow_right_sample, selectedChild_edge]
  exact sampleEdge_close k (levels k) f

private def selectedTarget (f : C(Interval, ℝ)) (k : ℕ) : Interval :=
  (pairRow (levels k) (selectedChild f k)).node
    (pairTargetIndex (levels k) (selectedChild f k) (selectedChild f k))

private theorem selectedTarget_dist_le (f : C(Interval, ℝ)) (k : ℕ) :
    dist (selectedTarget f k) (selectedPoint f) ≤ 1 / (k + 1 : ℝ) := by
  change |(selectedTarget f k : ℝ) - (selectedPoint f : ℝ)| ≤ _
  rw [abs_sub_comm]
  exact (selectedPoint_pair_spec f k).2.2.1

private theorem tendsto_selectedTarget (f : C(Interval, ℝ)) :
    Tendsto (selectedTarget f) atTop (𝓝 (selectedPoint f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv : Tendsto (fun k : ℕ ↦ 1 / (k + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine eventually_atTop.1 ?_
  filter_upwards [hinv.eventually (Iio_mem_nhds hε)] with k hk
  exact (selectedTarget_dist_le f k).trans_lt hk

private theorem tendsto_selectedTarget_error (f : C(Interval, ℝ)) :
    Tendsto (fun k ↦ |f (selectedTarget f k) - f (selectedPoint f)|) atTop (𝓝 0) := by
  have hf : Tendsto (fun k ↦ f (selectedTarget f k)) atTop (𝓝 (f (selectedPoint f))) :=
    f.continuous.continuousAt.tendsto.comp (tendsto_selectedTarget f)
  have hc : Tendsto (fun _ : ℕ ↦ f (selectedPoint f)) atTop (𝓝 (f (selectedPoint f))) :=
    tendsto_const_nhds
  simpa using (hf.sub hc).abs

private def selectedRowIndex (f : C(Interval, ℝ)) (k : ℕ) : ℕ :=
  pairRowSize k (selectedChild f k)

private theorem selectedRow_error_le (f : C(Interval, ℝ)) (k : ℕ) :
    |interpolant (arrayRow (selectedRowIndex f k)) f (selectedPoint f) -
        f (selectedPoint f)| ≤
      2 * ‖f‖ * (1 / (k + 1 : ℝ)) +
        ‖f‖ * (1 / (k + 1 : ℝ)) +
          |f (selectedTarget f k) - f (selectedPoint f)| := by
  rw [selectedRowIndex, arrayRow_pair]
  calc
    |interpolant (pairRow (levels k) (selectedChild f k)) f (selectedPoint f) -
        f (selectedPoint f)| ≤
      (k + 1 : ℝ) *
          |f ((pairRow (levels k) (selectedChild f k)).node
              (pairSampleIndex (levels k) (selectedChild f k) 0)) -
            f ((pairRow (levels k) (selectedChild f k)).node
              (pairSampleIndex (levels k) (selectedChild f k) 1))| +
        pairCoefficientErrorAt (levels k) (selectedChild f k) (selectedPoint f) * ‖f‖ +
          |f (selectedTarget f k) - f (selectedPoint f)| :=
      pair_interpolation_error_le (levels k) (selectedChild f k) f (selectedPoint f)
        (selectedPoint f).2
    _ ≤ (k + 1 : ℝ) * (2 * ‖f‖ / (k + 1 : ℝ) ^ 2) +
        (1 / (k + 1 : ℝ)) * ‖f‖ +
          |f (selectedTarget f k) - f (selectedPoint f)| := by
      gcongr
      · exact selectedPair_samples_close f k
      · exact (selectedPoint_pair_spec f k).2.1
    _ = 2 * ‖f‖ * (1 / (k + 1 : ℝ)) +
        ‖f‖ * (1 / (k + 1 : ℝ)) +
          |f (selectedTarget f k) - f (selectedPoint f)| := by
      have hk : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hk]

private theorem tendsto_selectedRow_error (f : C(Interval, ℝ)) :
    Tendsto (fun k ↦ |interpolant (arrayRow (selectedRowIndex f k)) f (selectedPoint f) -
      f (selectedPoint f)|) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ ↦ 1 / (k + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hfirst : Tendsto (fun k : ℕ ↦ 2 * ‖f‖ * (1 / (k + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv :
      Tendsto (fun k : ℕ ↦ (2 * ‖f‖) * (1 / (k + 1 : ℝ))) atTop
        (𝓝 ((2 * ‖f‖) * 0)))
  have hsecond : Tendsto (fun k : ℕ ↦ ‖f‖ * (1 / (k + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv :
      Tendsto (fun k : ℕ ↦ ‖f‖ * (1 / (k + 1 : ℝ))) atTop (𝓝 (‖f‖ * 0)))
  have hbound := (hfirst.add hsecond).add (tendsto_selectedTarget_error f)
  exact squeeze_zero (fun _ ↦ abs_nonneg _) (selectedRow_error_le f) (by simpa using hbound)

private theorem arrayRow_stable_in_stage (f : C(Interval, ℝ)) (k n : ℕ)
    (hlower : stageBoundary k < n) (hupper : n ≤ stageBoundary (k + 1))
    (hne : n ≠ selectedRowIndex f k) :
    lebesgue (arrayRow n) (selectedPoint f) ≤ 2 := by
  by_cases hfiller : n < stageStart k
  · let r : FillerIndex k := ⟨n, Finset.mem_Ioo.2 ⟨hlower, hfiller⟩⟩
    rw [show arrayRow n = fillerRow (levels k) r from arrayRow_filler r]
    exact selectedPoint_filler_stable f k r
  by_cases hpair : n < stageBoundary (k + 1)
  · let u : Fin (branchCount (k + 1)) := ⟨n - stageStart k, by
      rw [stageBoundary_succ] at hpair
      omega⟩
    have hsize : pairRowSize k u = n := by
      dsimp [pairRowSize, u]
      omega
    have hu : u ≠ selectedChild f k := by
      intro hu
      apply hne
      rw [← hsize, selectedRowIndex, hu]
    rw [← hsize, arrayRow_pair]
    exact selectedPoint_otherPair_stable f k hu
  · have hn : n = stageBoundary (k + 1) :=
      Nat.le_antisymm hupper (Nat.le_of_not_gt hpair)
    rw [hn, arrayRow_exterior]
    exact selectedPoint_exterior_stable f k

private theorem arrayRow_dichotomy (f : C(Interval, ℝ)) {n : ℕ} (hn : 2 < n) :
    n = selectedRowIndex f (stageIndex n) ∨
      lebesgue (arrayRow n) (selectedPoint f) ≤ 2 := by
  by_cases h : n = selectedRowIndex f (stageIndex n)
  · exact Or.inl h
  · exact Or.inr (arrayRow_stable_in_stage f (stageIndex n) n
      (stageIndex_lower hn) (stageIndex_upper n) h)

private theorem arrayRow_converges_at_selectedPoint (f : C(Interval, ℝ)) :
    Tendsto (fun n ↦ interpolant (arrayRow n) f (selectedPoint f)) atTop
      (𝓝 (f (selectedPoint f))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap (-1) 1 f _ hδ
  rw [norm_lt_iff _ hδ] at hp
  have hspecial : ∀ᶠ n in atTop,
      |interpolant (arrayRow (selectedRowIndex f (stageIndex n))) f (selectedPoint f) -
        f (selectedPoint f)| < ε :=
    tendsto_stageIndex.eventually ((tendsto_selectedRow_error f).eventually (Iio_mem_nhds hε))
  refine eventually_atTop.1 ?_
  filter_upwards [hspecial, eventually_gt_atTop (max 2 p.natDegree)] with n hs hn
  rcases arrayRow_dichotomy f (lt_of_le_of_lt (le_max_left _ _) hn) with hselected | hstable
  · rw [Real.dist_eq, hselected]
    exact hs
  · rw [Real.dist_eq]
    have hnat : p.natDegree < n := lt_of_le_of_lt (le_max_right 2 p.natDegree) hn
    have hpdeg : p.degree < n :=
      lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hnat)
    have happrox (y : Interval) : |p.eval (y : ℝ) - f y| ≤ ε / 4 := by
      simpa [Real.norm_eq_abs] using (hp y).le
    calc
      |interpolant (arrayRow n) f (selectedPoint f) - f (selectedPoint f)| ≤
          (1 + lebesgue (arrayRow n) (selectedPoint f)) * (ε / 4) :=
        interpolation_error_le (arrayRow n) f p (selectedPoint f).2 hpdeg happrox
      _ ≤ (1 + 2) * (ε / 4) := by gcongr
      _ < ε := by linarith

private theorem array_lebesgue_unbounded_oneBased (x : Interval) (A : ℝ) (N : ℕ) :
    ∃ n ≥ N, A ≤ lebesgue (arrayRow (n + 1)) x := by
  obtain ⟨m, hmN, hmA⟩ := array_lebesgue_unbounded x A (N + 1)
  have hm : 1 ≤ m := (Nat.le_add_left 1 N).trans hmN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨n, by omega, ?_⟩
  rw [Nat.add_comm 1 n] at hmA
  exact hmA

/-- Erdős Problem 671 in the literal one-based indexing of `E671.tex`: an
exact-cardinality Lagrange array whose Lebesgue functions are cofinally unbounded
everywhere, although every continuous function has a point where the full
interpolation sequence converges to the function. -/
theorem source_erdos_671 :
    ∃ X : ∀ n : ℕ, Row (n + 1),
      (∀ n, (nodeSet (X n)).card = n + 1) ∧
      (∀ x : Interval, ∀ A : ℝ, ∀ N : ℕ,
        ∃ n ≥ N, A ≤ lebesgue (X n) x) ∧
      ∀ f : C(Interval, ℝ), ∃ x : Interval,
        Tendsto (fun n ↦ interpolant (X n) f x) atTop (𝓝 (f x)) ∧
        ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgue (X n) x := by
  refine ⟨fun n ↦ arrayRow (n + 1), fun n ↦ card_nodeSet (arrayRow (n + 1)),
    array_lebesgue_unbounded_oneBased, fun f ↦ ⟨selectedPoint f, ?_, ?_⟩⟩
  · exact (tendsto_add_atTop_iff_nat 1).2 (arrayRow_converges_at_selectedPoint f)
  · exact array_lebesgue_unbounded_oneBased (selectedPoint f)

#print axioms source_erdos_671

end

end Erdos671
