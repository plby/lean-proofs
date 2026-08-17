/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.AugmentationFull
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.DegreeSorting

/-!
# Deterministic state selection for the full augmentation exposure

This file contains the purely finite part of the graph-specific full
exposure.  Starting from the witnesses carried by `PartialGood`, it deletes
the degree-window exceptions, thins the equal-degree collision graph, sorts
the survivors into low and high blocks, and records a one-cell-at-a-time
path between those blocks.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationGraphFullState

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Oriented collision edges -/

/-- The increasing orientation of an unordered pair. -/
def orientedPair {A : Type*} [LinearOrder A] : Sym2 A → A × A :=
  Sym2.lift ⟨fun x y ↦ if x < y then (x, y) else (y, x), by
    intro x y
    by_cases hxy : x < y
    · have hyx : ¬ y < x := not_lt_of_ge hxy.le
      simp [hxy, hyx]
    · by_cases hyx : y < x
      · simp [hxy, hyx]
      · have hEq : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
        simp [hEq] ⟩

@[simp] lemma orientedPair_s {A : Type*} [LinearOrder A] (x y : A) :
    orientedPair s(x, y) = if x < y then (x, y) else (y, x) := rfl

/-- Forgetting the orientation recovers the original unordered pair. -/
lemma s_orientedPair {A : Type*} [LinearOrder A] (e : Sym2 A) :
    s((orientedPair e).1, (orientedPair e).2) = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : x < y
      · simp [hxy]
      · simp [hxy]

/-- Increasing orientation is injective. -/
lemma orientedPair_injective {A : Type*} [LinearOrder A] :
    Function.Injective (orientedPair : Sym2 A → A × A) := by
  intro e f hef
  rw [← s_orientedPair e, ← s_orientedPair f, hef]

/-- Relabel an oriented edge of a graph on a subtype by its ambient endpoints. -/
def orientedSubtypePair {A : Type*} [LinearOrder A] (C : Finset A) :
    Sym2 {x // x ∈ C} → A × A :=
  fun e ↦ ((orientedPair e).1.1, (orientedPair e).2.1)

lemma orientedSubtypePair_injective {A : Type*} [LinearOrder A]
    (C : Finset A) : Function.Injective (orientedSubtypePair C) := by
  intro e f hef
  apply orientedPair_injective
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hef
  · apply Subtype.ext
    exact congrArg Prod.snd hef

/-- The unordered equal-value graph has no more edges than the increasing
ordered-pair collision representation. -/
lemma valueCollisionGraph_edgeFinset_card_le_collisionEdges
    {A B : Type*} [LinearOrder A] [DecidableEq B]
    (C : Finset A) (f : A → B) :
    (AugmentationFull.valueCollisionGraph C f).edgeFinset.card ≤
      (CollisionCounting.collisionEdges C (fun x (_ : Unit) ↦ f x) ()).card := by
  classical
  apply Finset.card_le_card_of_injOn (orientedSubtypePair C)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have he' : s(x, y) ∈
            (AugmentationFull.valueCollisionGraph C f).edgeFinset := he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          AugmentationFull.valueCollisionGraph_adj] at he'
        rcases he' with ⟨hxy, hf⟩
        have hval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
        by_cases hlt : x.1 < y.1
        · have hlt' : x < y := hlt
          simp [orientedSubtypePair, hlt',
            CollisionCounting.mem_collisionEdges, x.2, y.2, hval, hf, hlt]
        · have hyx : y.1 < x.1 := lt_of_le_of_ne (le_of_not_gt hlt) hval.symm
          have hnot' : ¬ x < y := hlt
          have hyxne : y ≠ x := Ne.symm hxy
          simp [orientedSubtypePair, hnot',
            CollisionCounting.mem_collisionEdges, x.2, y.2, hyxne, hf, hyx]
  · exact (orientedSubtypePair_injective C).injOn

lemma collisionEdges_mono
    {A B Ω : Type*} [LinearOrder A] [DecidableEq B] [Fintype Ω] [Nonempty Ω]
    {C D : Finset A} (hCD : C ⊆ D) (f : A → Ω → B) (omega : Ω) :
    CollisionCounting.collisionEdges C f omega ⊆
      CollisionCounting.collisionEdges D f omega := by
  intro e he
  rw [CollisionCounting.mem_collisionEdges] at he ⊢
  exact ⟨hCD he.1, hCD he.2.1, he.2.2⟩

/-! ## A literal one-cell path -/

/-- Enumerations of two disjoint equal-sized blocks. -/
structure EnumeratedBlocks {A : Type*} [DecidableEq A]
    (low high : Finset A) (n : ℕ) where
  disjoint : Disjoint low high
  low_card : low.card = n
  high_card : high.card = n
  lowEquiv : Fin n ≃ {x // x ∈ low}
  highEquiv : Fin n ≃ {x // x ∈ high}

/-- At time `i`, coordinate `j` has switched to its high-block value exactly
when `j < i`. -/
def EnumeratedBlocks.value {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin (n + 1)) (j : Fin n) : A :=
  if j.val < i.val then (B.highEquiv j).1 else (B.lowEquiv j).1

/-- The fixed-cardinality state at time `i`. -/
def EnumeratedBlocks.state {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin (n + 1)) : Finset A :=
  Finset.univ.image (B.value i)

lemma EnumeratedBlocks.value_injective {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin (n + 1)) : Function.Injective (B.value i) := by
  intro j k hjk
  by_cases hj : j.val < i.val <;> by_cases hk : k.val < i.val
  · have hjk' : (B.highEquiv j).1 = (B.highEquiv k).1 := by
      simpa [EnumeratedBlocks.value, hj, hk] using hjk
    have hsub : B.highEquiv j = B.highEquiv k := Subtype.ext hjk'
    exact B.highEquiv.injective hsub
  · have hhigh : (B.highEquiv j).1 ∈ high := (B.highEquiv j).2
    have hlow : (B.lowEquiv k).1 ∈ low := (B.lowEquiv k).2
    have hjk' : (B.highEquiv j).1 = (B.lowEquiv k).1 := by
      simpa [EnumeratedBlocks.value, hj, hk] using hjk
    exfalso
    exact Finset.disjoint_left.mp B.disjoint hlow
      (hjk' ▸ hhigh)
  · have hlow : (B.lowEquiv j).1 ∈ low := (B.lowEquiv j).2
    have hhigh : (B.highEquiv k).1 ∈ high := (B.highEquiv k).2
    have hjk' : (B.lowEquiv j).1 = (B.highEquiv k).1 := by
      simpa [EnumeratedBlocks.value, hj, hk] using hjk
    exfalso
    exact Finset.disjoint_left.mp B.disjoint hlow
      (hjk'.symm ▸ hhigh)
  · have hjk' : (B.lowEquiv j).1 = (B.lowEquiv k).1 := by
      simpa [EnumeratedBlocks.value, hj, hk] using hjk
    have hsub : B.lowEquiv j = B.lowEquiv k := Subtype.ext hjk'
    exact B.lowEquiv.injective hsub

@[simp] lemma EnumeratedBlocks.card_state {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin (n + 1)) : (B.state i).card = n := by
  rw [EnumeratedBlocks.state, Finset.card_image_iff.mpr]
  · simp
  · exact (B.value_injective i).injOn

lemma EnumeratedBlocks.state_subset {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin (n + 1)) : B.state i ⊆ low ∪ high := by
  intro x hx
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
  by_cases h : j.val < i.val
  · simpa [EnumeratedBlocks.value, h] using
      (Finset.mem_union_right low (B.highEquiv j).2)
  · simpa [EnumeratedBlocks.value, h] using
      (Finset.mem_union_left high (B.lowEquiv j).2)

@[simp] lemma EnumeratedBlocks.state_zero {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n) :
    B.state 0 = low := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    simpa [EnumeratedBlocks.value] using (B.lowEquiv j).2
  · rw [B.card_state, B.low_card]

@[simp] lemma EnumeratedBlocks.state_last {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n) :
    B.state (Fin.last n) = high := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    simpa [EnumeratedBlocks.value] using (B.highEquiv j).2
  · rw [B.card_state, B.high_card]

lemma EnumeratedBlocks.value_succ {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i j : Fin n) :
    B.value i.succ j =
      if j = i then (B.highEquiv i).1 else B.value i.castSucc j := by
  by_cases hji : j = i
  · subst j
    simp [EnumeratedBlocks.value]
  · by_cases hjlt : j.val < i.val
    · have hjlt' : j.val < i.val + 1 := by omega
      simp [EnumeratedBlocks.value, hji, hjlt, hjlt']
    · have hjgt : i.val < j.val := lt_of_le_of_ne (le_of_not_gt hjlt)
        (fun h ↦ hji (Fin.ext h.symm))
      have hnot : ¬j.val < i.val + 1 := by omega
      simp [EnumeratedBlocks.value, hji, hjlt, hnot]

/-- Every transition erases exactly the indexed low cell and inserts the
corresponding high cell. -/
lemma EnumeratedBlocks.state_succ {A : Type*} [DecidableEq A]
    {low high : Finset A} {n : ℕ} (B : EnumeratedBlocks low high n)
    (i : Fin n) :
    B.state i.succ =
      insert (B.highEquiv i).1 (B.state i.castSucc |>.erase (B.lowEquiv i).1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_image.mp hx
    rw [B.value_succ i j] at hjx
    by_cases hji : j = i
    · subst j
      simp at hjx
      exact Finset.mem_insert.mpr (Or.inl hjx.symm)
    · have hval : B.value i.castSucc j = x := by simpa [hji] using hjx
      have hxstate : x ∈ B.state i.castSucc :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hval⟩
      have hxremove : x ≠ (B.lowEquiv i).1 := by
        intro hxi
        have hiVal : B.value i.castSucc i = (B.lowEquiv i).1 := by
          simp [EnumeratedBlocks.value]
        have heqval : B.value i.castSucc j = B.value i.castSucc i := by
          rw [hval, hxi, hiVal]
        exact hji (B.value_injective i.castSucc heqval)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxremove, hxstate⟩))
  · intro hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxadd | hxold
    · subst x
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [B.value_succ]
    · have hxold' := (Finset.mem_erase.mp hxold).2
      obtain ⟨j, _hj, hjx⟩ := Finset.mem_image.mp hxold'
      have hji : j ≠ i := by
        intro h
        subst j
        have hxremove : x = (B.lowEquiv i).1 := by
          simpa [EnumeratedBlocks.value] using hjx.symm
        exact (Finset.mem_erase.mp hxold).1 hxremove
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [B.value_succ i j]
      simpa [hji] using hjx

/-! ## Collision thinning, sorting, and path selection -/

/-- Delete the cells marked bad by a deterministic predicate. -/
def goodPart {A : Type*} [DecidableEq A] (S : Finset A) (bad : A → Prop) :
    Finset A := S.filter fun x ↦ ¬bad x

lemma goodPart_subset {A : Type*} [DecidableEq A]
    (S : Finset A) (bad : A → Prop) : goodPart S bad ⊆ S :=
  Finset.filter_subset _ _

/-- The complete deterministic output needed to define the canonical full
exposure.  The source and candidate families are disjoint; `selected` is a
collision-free degree subfamily of the good source cells; `blocks` gives the
literal one-cell path between the sorted low and high blocks. -/
structure SelectedSwitchingData {A : Type*} [DecidableEq A]
    (source candidates : Finset A) (bad : A → Prop)
    (degree : A → ℤ) (n gap badBudget : ℕ) where
  source_away_candidates : Disjoint source candidates
  bad_source_card_le : (source.filter bad).card ≤ badBudget
  bad_candidates_card_le : (candidates.filter bad).card ≤ badBudget
  selected : Finset A
  selected_subset_good : selected ⊆ goodPart source bad
  degree_inj : Set.InjOn degree (selected : Set A)
  split : DegreeSorting.OrderedThreeWaySplit selected degree n
  gap_lt : ∀ x ∈ split.low, ∀ y ∈ split.high,
    (gap : ℤ) < degree y - degree x
  blocks : EnumeratedBlocks split.low split.high n

namespace SelectedSwitchingData

variable {A : Type*} [DecidableEq A]
  {source candidates : Finset A} {bad : A → Prop}
  {degree : A → ℤ} {n gap badBudget : ℕ}

def goodCandidates
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    Finset A := goodPart candidates bad

def low (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    Finset A := D.split.low

def high (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    Finset A := D.split.high

def state (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin (n + 1)) : Finset A := D.blocks.state i

@[simp] lemma card_low
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    D.low.card = n := D.split.low_card

@[simp] lemma card_high
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    D.high.card = n := D.split.high_card

@[simp] lemma card_state
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin (n + 1)) : (D.state i).card = n :=
  D.blocks.card_state i

lemma state_subset_selected
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin (n + 1)) : D.state i ⊆ D.selected := by
  exact (D.blocks.state_subset i).trans (by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact D.split.low_subset hx
    · exact D.split.high_subset hx)

lemma state_subset_source
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin (n + 1)) : D.state i ⊆ source :=
  (D.state_subset_selected i).trans
    (D.selected_subset_good.trans (goodPart_subset source bad))

lemma state_disjoint_candidates
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin (n + 1)) : Disjoint (D.state i) candidates :=
  D.source_away_candidates.mono_left (D.state_subset_source i)

@[simp] lemma state_zero
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    D.state 0 = D.low := D.blocks.state_zero

@[simp] lemma state_last
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget) :
    D.state (Fin.last n) = D.high := D.blocks.state_last

lemma state_succ
    (D : SelectedSwitchingData source candidates bad degree n gap badBudget)
    (i : Fin n) :
    D.state i.succ = insert (D.blocks.highEquiv i).1
      (D.state i.castSucc |>.erase (D.blocks.lowEquiv i).1) :=
  D.blocks.state_succ i

end SelectedSwitchingData

/-- The graph specialization uses the fixed cell order chosen at partial
exposure, including its induced decidable equality. -/
noncomputable abbrev GraphSelectedSwitchingData
    (source candidates : Finset (Finset V)) (G : SimpleGraph V)
    (D₁ : Finset V) (center radius : ℝ) (n gap badBudget : ℕ) :=
  @SelectedSwitchingData (Finset V)
    AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source candidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood G D₁ x center radius)
    (fun x ↦ (degreeInto G D₁ x : ℤ)) n gap badBudget

/-- Explicit finite selection theorem.  The only numerical premise is the
exact Turán threshold after deleting the bad source cells. -/
theorem exists_selectedSwitchingData
    {A : Type*} [LinearOrder A]
    (source candidates : Finset A) (bad : A → Prop) (degree : A → ℤ)
    (n gap badBudget edgeBudget : ℕ)
    (haway : Disjoint source candidates)
    (hbadSource : (source.filter bad).card ≤ badBudget)
    (hbadCandidates : (candidates.filter bad).card ≤ badBudget)
    (hcollision :
      (CollisionCounting.collisionEdges source
        (fun x (_ : Unit) ↦ degree x) ()).card ≤ edgeBudget)
    (hTuran :
      (2 * n + gap + 1) *
          ((goodPart source bad).card + 2 * edgeBudget) <
        (goodPart source bad).card ^ 2) :
    Nonempty
      (SelectedSwitchingData source candidates bad degree n gap badBudget) := by
  classical
  let C := goodPart source bad
  have hcollisionC :
      (CollisionCounting.collisionEdges C
        (fun x (_ : Unit) ↦ degree x) ()).card ≤ edgeBudget := by
    exact (Finset.card_le_card (collisionEdges_mono
      (goodPart_subset source bad) _ ())).trans hcollision
  have hgraph :
      (AugmentationFull.valueCollisionGraph C degree).edgeFinset.card ≤
        edgeBudget :=
    (valueCollisionGraph_edgeFinset_card_le_collisionEdges C degree).trans hcollisionC
  obtain ⟨Y, hYC, hYinj, hYbound⟩ :=
    AugmentationFull.exists_injective_subfamily_card_sq_le_of_edges_le
      C degree edgeBudget hgraph
  have hTuran' :
      (2 * n + gap + 1) * (C.card + 2 * edgeBudget) < C.card ^ 2 := by
    simpa [C] using hTuran
  have hYlarge : 2 * n + gap + 1 < Y.card := by
    by_contra hnot
    have hle : Y.card ≤ 2 * n + gap + 1 := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_right (C.card + 2 * edgeBudget) hle
    exact (Nat.not_lt_of_ge hmul) (hTuran'.trans_le hYbound)
  have hsize : 2 * n ≤ Y.card := by omega
  have hfiber : ∀ z : ℤ, (Y.filter fun x ↦ degree x = z).card ≤ 1 := by
    intro z
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    exact hYinj hx.1 hy.1 (hx.2.trans hy.2.symm)
  have hmiddle : 1 * (gap + 1) < Y.card - 2 * n := by omega
  obtain ⟨D, hgap⟩ :=
    DegreeSorting.exists_orderedThreeWaySplit_with_gap
      Y degree n 1 gap hsize hfiber hmiddle
  let B : EnumeratedBlocks D.low D.high n :=
    { disjoint := D.low_disjoint_rest.mono_right Finset.subset_union_right
      low_card := D.low_card
      high_card := D.high_card
      lowEquiv := Fintype.equivOfCardEq (by simp [D.low_card])
      highEquiv := Fintype.equivOfCardEq (by simp [D.high_card]) }
  exact ⟨{
    source_away_candidates := haway
    bad_source_card_le := hbadSource
    bad_candidates_card_le := hbadCandidates
    selected := Y
    selected_subset_good := hYC
    degree_inj := hYinj
    split := D
    gap_lt := hgap
    blocks := B }⟩

/-- A convenient form of the selection theorem in which the numerical
Turán check is made at any certified lower bound for the number of good
source cells. -/
theorem exists_selectedSwitchingData_of_goodPart_card_lower
    {A : Type*} [LinearOrder A]
    (source candidates : Finset A) (bad : A → Prop) (degree : A → ℤ)
    (n gap badBudget edgeBudget goodLower : ℕ)
    (haway : Disjoint source candidates)
    (hbadSource : (source.filter bad).card ≤ badBudget)
    (hbadCandidates : (candidates.filter bad).card ≤ badBudget)
    (hcollision :
      (CollisionCounting.collisionEdges source
        (fun x (_ : Unit) ↦ degree x) ()).card ≤ edgeBudget)
    (hgoodLower : goodLower ≤ (goodPart source bad).card)
    (hTuran :
      (2 * n + gap + 1) * (goodLower + 2 * edgeBudget) < goodLower ^ 2) :
    Nonempty
      (SelectedSwitchingData source candidates bad degree n gap badBudget) := by
  have hRlt : 2 * n + gap + 1 < goodLower := by
    by_contra hnot
    have hle : goodLower ≤ 2 * n + gap + 1 := Nat.le_of_not_gt hnot
    have hsq : goodLower ^ 2 ≤
        (2 * n + gap + 1) * (goodLower + 2 * edgeBudget) := by
      calc
        goodLower ^ 2 = goodLower * goodLower := by rw [pow_two]
        _ ≤ (2 * n + gap + 1) * goodLower :=
          Nat.mul_le_mul_right goodLower hle
        _ ≤ (2 * n + gap + 1) * (goodLower + 2 * edgeBudget) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    exact (Nat.not_lt_of_ge hsq) hTuran
  have hmono :
      (2 * n + gap + 1) *
          ((goodPart source bad).card + 2 * edgeBudget) <
        (goodPart source bad).card ^ 2 := by
    have hfac1 : (0 : ℝ) ≤
        ((goodPart source bad).card : ℝ) - (goodLower : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hgoodLower)
    have hfac2 : (0 : ℝ) ≤
        ((goodPart source bad).card : ℝ) + (goodLower : ℝ) -
          (2 * n + gap + 1 : ℕ) := by
      exact sub_nonneg.mpr (by
        exact_mod_cast (show 2 * n + gap + 1 ≤
          (goodPart source bad).card + goodLower by omega))
    have hprod := mul_nonneg hfac1 hfac2
    have hTuranReal :
        ((2 * n + gap + 1 : ℕ) : ℝ) *
            ((goodLower : ℝ) + 2 * edgeBudget) <
          (goodLower : ℝ) ^ 2 := by
      exact_mod_cast hTuran
    have hgoal :
      ((2 * n + gap + 1 : ℕ) : ℝ) *
          (((goodPart source bad).card : ℝ) + 2 * edgeBudget) <
        ((goodPart source bad).card : ℝ) ^ 2 := by
      nlinarith
    exact_mod_cast hgoal
  exact exists_selectedSwitchingData source candidates bad degree
    n gap badBudget edgeBudget haway hbadSource hbadCandidates
      hcollision hmono

/-! ## Graph-facing wrapper -/

/-- A `PartialGood` outcome canonically supplies the collision-thinned,
degree-sorted one-cell switching path.  All real thresholds are converted
to explicit natural budgets; the final displayed inequality is the only
finite Turán-size condition. -/
theorem exists_selectedSwitchingData_of_partialGood
    (G : SimpleGraph V) (M : Finset (Finset V)) (D₁ : Finset V)
    (s₀ n gap badBudget edgeBudget : ℕ)
    (diversityThreshold center radius tS tX tCollision : ℝ)
    (hgood : AugmentationGraphPartial.PartialGood G M s₀
      diversityThreshold center radius tS tX tCollision D₁)
    (htS : tS ≤ (badBudget : ℝ) + 1)
    (htX : tX ≤ (badBudget : ℝ) + 1)
    (htCollision : tCollision ≤ (edgeBudget : ℝ) + 1)
    (hTuran :
      (2 * n + gap + 1) *
          (s₀ - badBudget + 2 * edgeBudget) <
        (s₀ - badBudget) ^ 2) :
    ∃ source candidates : Finset (Finset V),
      source ⊆ M ∧ candidates ⊆ M ∧
      Nonempty (GraphSelectedSwitchingData source candidates G D₁
        center radius n gap badBudget) := by
  classical
  letI : LinearOrder (Finset V) := AugmentationGraphPartial.cellLinearOrder
  obtain ⟨S₀, X₀, hS₀M, hX₀M, hS₀card, hX₀card, hdisjoint,
    _hdiverse, hbadS, hbadX, hcoll⟩ := hgood
  let bad : Finset V → Prop := fun x ↦
    ¬AugmentationGraphPartial.DegreeGood G D₁ x center radius
  let degree : Finset V → ℤ := fun x ↦ (degreeInto G D₁ x : ℤ)
  have hbadSNat : (S₀.filter bad).card ≤ badBudget := by
    have hlt : ((S₀.filter bad).card : ℝ) < (badBudget : ℝ) + 1 := by
      exact hbadS.trans_le htS
    have hltNat : (S₀.filter bad).card < badBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hbadXNat : (X₀.filter bad).card ≤ badBudget := by
    have hlt : ((X₀.filter bad).card : ℝ) < (badBudget : ℝ) + 1 := by
      exact hbadX.trans_le htX
    have hltNat : (X₀.filter bad).card < badBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hcollisionNat :
      (AugmentationGraphPartial.cellCollisionEdges S₀
        (degreeInto G D₁)).card ≤ edgeBudget := by
    have hlt :
        ((AugmentationGraphPartial.cellCollisionEdges S₀
          (degreeInto G D₁)).card : ℝ) < (edgeBudget : ℝ) + 1 :=
      hcoll.trans_le htCollision
    have hltNat :
        (AugmentationGraphPartial.cellCollisionEdges S₀
          (degreeInto G D₁)).card < edgeBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hcollisionEq :
      CollisionCounting.collisionEdges S₀
          (fun x (_ : Unit) ↦ degree x) () =
        AugmentationGraphPartial.cellCollisionEdges S₀ (degreeInto G D₁) := by
    unfold AugmentationGraphPartial.cellCollisionEdges
    change CollisionCounting.collisionEdges S₀
        (fun x (_ : Unit) ↦ degree x) () =
      CollisionCounting.collisionEdges S₀
        (fun x (_ : Unit) ↦ degreeInto G D₁ x) ()
    ext e
    rw [CollisionCounting.mem_collisionEdges,
      CollisionCounting.mem_collisionEdges]
    simp [degree]
  have hcollision :
      (CollisionCounting.collisionEdges S₀
        (fun x (_ : Unit) ↦ degree x) ()).card ≤ edgeBudget := by
    rw [hcollisionEq]
    exact hcollisionNat
  have hgoodCard : s₀ - badBudget ≤ (goodPart S₀ bad).card := by
    have hpartial := AugmentationGraphPartial.card_sub_lt_add_card_goodCells
      G D₁ center radius tS S₀ hbadS
    have hgoodEq : goodPart S₀ bad =
        AugmentationGraphPartial.goodCells G D₁ center radius S₀ := by
      ext x
      simp [goodPart, bad, AugmentationGraphPartial.goodCells]
    rw [hS₀card] at hpartial
    rw [hgoodEq]
    have hsreal : (s₀ : ℝ) <
        (badBudget : ℝ) + 1 +
          (AugmentationGraphPartial.goodCells G D₁ center radius S₀).card := by
      linarith
    have hsnat : s₀ < badBudget + 1 +
        (AugmentationGraphPartial.goodCells G D₁ center radius S₀).card := by
      exact_mod_cast hsreal
    omega
  have hselected := exists_selectedSwitchingData_of_goodPart_card_lower
    S₀ X₀ bad degree n gap badBudget edgeBudget (s₀ - badBudget)
      hdisjoint (by
        convert hbadSNat using 1
        exact congrArg Finset.card (Finset.filter_congr_decidable S₀ bad _))
      (by
        convert hbadXNat using 1
        exact congrArg Finset.card (Finset.filter_congr_decidable X₀ bad _))
      hcollision hgoodCard hTuran
  refine ⟨S₀, X₀, hS₀M, hX₀M, ?_⟩
  simpa [bad, degree] using hselected


end
end AugmentationGraphFullState
end Erdos636
