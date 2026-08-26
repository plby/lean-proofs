/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Part2Full
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair
import ErdosProblems.Erdos547b.Lemma58EligiblePacking
import ErdosProblems.Erdos547b.Claim616SourceBridge

/-!
# Zhao Lemma 5.8: grouped small forests

This file is the source-faithful replacement for a static, whole-pool greedy
embedding.  Lemma 5.8 may put almost all vertices of a matching endpoint into
the forest, even when the density of the matching pair is small.  It therefore
cannot require the total endpoint load to be at most
`(density - epsilon) * N`.  Instead, whole rooted branches of order at most
`small` are processed consecutively.  At a matching edge there is one live
carry branch; completed batches leave the prescribed scalar reserve.  Each
branch is embedded into the *currently unused* endpoint sets.

The first section records exact endpoint loads of an independently oriented
ordered branch forest.  The second section contains the next-fit/carry
arithmetic.  The graph realization below consumes the dynamic one-branch
regular-pair lemma, rather than a copy or continuation hypothesis.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GroupedSmallForest

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoProp57
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest
open Erdos547b.ZhaoLemma51DynamicRegularPair
open Erdos547b.ZhaoLemma58EligiblePacking
open Erdos547b.ZhaoClaim616SourceBridge

universe u v

/-! ## Exact oriented source loads -/

/-- One canonical colour class of one rooted branch. -/
def colourClass {b : ℕ} (F : OrderedRootedForest b) (i : Fin b)
    (c : Fin 2) : Finset (Fin (F.size i)) :=
  Finset.univ.filter fun a ↦
    (F.isTree i).coloringTwoOfVert (F.root i) a = c

@[simp] theorem mem_colourClass {b : ℕ} (F : OrderedRootedForest b)
    (i : Fin b) (c : Fin 2) (a : Fin (F.size i)) :
    a ∈ colourClass F i c ↔
      (F.isTree i).coloringTwoOfVert (F.root i) a = c := by
  rw [colourClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Number of vertices of branch `i` sent to physical endpoint `c`. -/
def orientedClassSize {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (i : Fin b) (c : Fin 2) : ℕ :=
  #(Finset.univ.filter fun a ↦
    orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = c)

/-- Total number of source vertices assigned to one endpoint. -/
def sideLoad {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) : ℕ :=
  ∑ i, orientedClassSize F orient i c

/-- Vertices already used on side `c` before branch `i` is embedded. -/
def sideLoadBefore {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (i : Fin b) (c : Fin 2) : ℕ :=
  ∑ j ∈ Finset.Iio i, orientedClassSize F orient j c

theorem sideLoadBefore_le_sideLoad {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) (c : Fin 2) :
    sideLoadBefore F orient i c ≤ sideLoad F orient c := by
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ (Finset.Iio i))

/-- Exact occupancy of physical side `c` on one assigned matching edge. -/
def groupSideLoad {b : ℕ} {K : Type*} [DecidableEq K]
    (F : OrderedRootedForest b) (group : Fin b → K)
    (orient : Fin b → Fin 2 ≃ Fin 2) (e : K) (c : Fin 2) : ℕ :=
  ∑ i, if group i = e then orientedClassSize F orient i c else 0

theorem orientedClassSize_zero_add_one {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) :
    orientedClassSize F orient i 0 + orientedClassSize F orient i 1 =
      F.size i := by
  classical
  let A : Finset (Fin (F.size i)) := Finset.univ.filter fun a ↦
    orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = 0
  let B : Finset (Fin (F.size i)) := Finset.univ.filter fun a ↦
    orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = 1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha0 := (Finset.mem_filter.mp ha).2
    have ha1 := (Finset.mem_filter.mp hb).2
    exact Fin.zero_ne_one (ha0.symm.trans ha1)
  have hunion : A ∪ B = Finset.univ := by
    ext a
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    rcases OrderedRootedForest.fin_two_eq_zero_or_one
      (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  change #A + #B = F.size i
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

theorem sideLoad_zero_add_one {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) :
    sideLoad F orient 0 + sideLoad F orient 1 = F.order := by
  classical
  rw [sideLoad, sideLoad, OrderedRootedForest.order, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact orientedClassSize_zero_add_one F orient i

/-- Orientation inherited by the tail after the first branch is removed. -/
def tailOrient {b : ℕ} (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) :
    Fin b → Fin 2 ≃ Fin 2 := fun i ↦ orient i.succ

@[simp] theorem orientedClassSize_tail {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) (i : Fin b) (c : Fin 2) :
    orientedClassSize F.tail (tailOrient orient) i c =
      orientedClassSize F orient i.succ c := by
  rfl

theorem sideLoad_tail_add_head {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) (c : Fin 2) :
    sideLoad F.tail (tailOrient orient) c +
        orientedClassSize F orient 0 c = sideLoad F orient c := by
  simp only [sideLoad, orientedClassSize_tail, Fin.sum_univ_succ]
  omega

@[simp] theorem sideLoadBefore_zero {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) (c : Fin 2) :
    sideLoadBefore F orient 0 c = 0 := by
  simp [sideLoadBefore]

theorem sideLoadBefore_tail_add_head {b : ℕ}
    (F : OrderedRootedForest (b + 1))
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2)
    (i : Fin b) (c : Fin 2) :
    sideLoadBefore F.tail (tailOrient orient) i c +
        orientedClassSize F orient 0 c =
      sideLoadBefore F orient i.succ c := by
  classical
  simp only [sideLoadBefore, orientedClassSize_tail]
  have hIio : Finset.Iio i.succ =
      insert (0 : Fin (b + 1))
        ((Finset.Iio i).image (fun j : Fin b ↦ j.succ)) := by
    ext j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;> simp
  rw [hIio, Finset.sum_insert (by simp)]
  rw [Finset.sum_image]
  · exact Nat.add_comm _ _
  · intro x _ y _ hxy
    exact Fin.succ_inj.mp hxy

theorem groupSideLoad_tail_add_head
    {b : ℕ} {K : Type*} [DecidableEq K]
    (F : OrderedRootedForest (b + 1)) (group : Fin (b + 1) → K)
    (orient : Fin (b + 1) → Fin 2 ≃ Fin 2) (e : K) (c : Fin 2) :
    groupSideLoad F.tail (fun i ↦ group i.succ) (tailOrient orient) e c +
        (if group 0 = e then orientedClassSize F orient 0 c else 0) =
      groupSideLoad F group orient e c := by
  simp [groupSideLoad, orientedClassSize_tail, Fin.sum_univ_succ, add_comm]

theorem groupSideLoad_zero_add_one
    {b : ℕ} {K : Type*} [DecidableEq K]
    (F : OrderedRootedForest b) (group : Fin b → K)
    (orient : Fin b → Fin 2 ≃ Fin 2) (e : K) :
    groupSideLoad F group orient e 0 + groupSideLoad F group orient e 1 =
      ∑ i, if group i = e then F.size i else 0 := by
  classical
  rw [groupSideLoad, groupSideLoad, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : group i = e
  · simp only [hi, if_pos]
    exact orientedClassSize_zero_add_one F orient i
  · simp [hi]

/-- The endpoint occupied by the root of branch `i`. -/
def branchRootSide {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (i : Fin b) : Fin 2 :=
  orient i 0

theorem root_mem_oriented_class {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (i : Fin b) :
    F.root i ∈ Finset.univ.filter (fun a ↦
      orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) =
        branchRootSide F orient i) := by
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simp [branchRootSide]⟩

theorem one_le_orientedClassSize_root {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) :
    1 ≤ orientedClassSize F orient i (branchRootSide F orient i) := by
  exact Finset.one_le_card.mpr ⟨F.root i, root_mem_oriented_class F orient i⟩

@[simp] theorem orientedClassSize_refl {b : ℕ}
    (F : OrderedRootedForest b) (i : Fin b) (c : Fin 2) :
    orientedClassSize F (fun _ ↦ Equiv.refl (Fin 2)) i c =
      #(colourClass F i c) := by
  rfl

@[simp] theorem orientedClassSize_swap_zero {b : ℕ}
    (F : OrderedRootedForest b) (i : Fin b) :
    orientedClassSize F (fun _ ↦ Equiv.swap (0 : Fin 2) 1) i 0 =
      #(colourClass F i 1) := by
  have hsets :
      (Finset.univ.filter fun a ↦
        (Equiv.swap (0 : Fin 2) 1)
          ((F.isTree i).coloringTwoOfVert (F.root i) a) = 0) =
        colourClass F i 1 := by
    ext a
    simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases OrderedRootedForest.fin_two_eq_zero_or_one
      ((F.isTree i).coloringTwoOfVert (F.root i) a) with h | h <;>
        simp [h]
  exact congrArg Finset.card hsets

@[simp] theorem orientedClassSize_swap_one {b : ℕ}
    (F : OrderedRootedForest b) (i : Fin b) :
    orientedClassSize F (fun _ ↦ Equiv.swap (0 : Fin 2) 1) i 1 =
      #(colourClass F i 0) := by
  have hsets :
      (Finset.univ.filter fun a ↦
        (Equiv.swap (0 : Fin 2) 1)
          ((F.isTree i).coloringTwoOfVert (F.root i) a) = 1) =
        colourClass F i 0 := by
    ext a
    simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases OrderedRootedForest.fin_two_eq_zero_or_one
      ((F.isTree i).coloringTwoOfVert (F.root i) a) with h | h <;>
        simp [h]
  exact congrArg Finset.card hsets

/-- Direct ordered-forest form of Zhao Lemma 5.4(1)'s balancing step. -/
theorem exists_balanced_forest_orientation
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      sideLoad F orient 0 ≤ sideLoad F orient 1 + slack ∧
      sideLoad F orient 1 ≤ sideLoad F orient 0 + slack := by
  classical
  induction b with
  | zero =>
      let orient : Fin 0 → Fin 2 ≃ Fin 2 := fun i ↦ Fin.elim0 i
      exact ⟨orient, by simp [sideLoad], by simp [sideLoad]⟩
  | succ b ih =>
      let Ftail : OrderedRootedForest b := F.tail
      have hsmallTail : ∀ i, Ftail.size i ≤ slack := by
        intro i
        exact hsmall i.succ
      obtain ⟨orientTail, htail0, htail1⟩ := ih Ftail hsmallTail
      let a := #(colourClass F 0 0)
      let d := #(colourClass F 0 1)
      have had : a + d ≤ slack := by
        have hsum := orientedClassSize_zero_add_one F
          (fun _ ↦ Equiv.refl (Fin 2)) 0
        simp only [orientedClassSize_refl] at hsum
        rw [hsum]
        exact hsmall 0
      rcases balanced_orientation_step
          (sideLoad Ftail orientTail 0) (sideLoad Ftail orientTail 1)
          a d slack htail0 htail1 had with hkeep | hswap
      · let orient : Fin (b + 1) → Fin 2 ≃ Fin 2 :=
          Fin.cases (Equiv.refl (Fin 2)) orientTail
        refine ⟨orient, ?_, ?_⟩
        · rw [← sideLoad_tail_add_head F orient 0]
          change sideLoad Ftail orientTail 0 + a ≤
            sideLoad F orient 1 + slack
          rw [← sideLoad_tail_add_head F orient 1]
          exact hkeep.1
        · rw [← sideLoad_tail_add_head F orient 1]
          change sideLoad Ftail orientTail 1 + d ≤
            sideLoad F orient 0 + slack
          rw [← sideLoad_tail_add_head F orient 0]
          exact hkeep.2
      · let orient : Fin (b + 1) → Fin 2 ≃ Fin 2 :=
          Fin.cases (Equiv.swap (0 : Fin 2) 1) orientTail
        have hhead0 : orientedClassSize F orient 0 0 = d := by
          change orientedClassSize F
            (fun _ ↦ Equiv.swap (0 : Fin 2) 1) 0 0 = d
          simpa only [d] using orientedClassSize_swap_zero F 0
        have hhead1 : orientedClassSize F orient 0 1 = a := by
          change orientedClassSize F
            (fun _ ↦ Equiv.swap (0 : Fin 2) 1) 0 1 = a
          simpa only [a] using orientedClassSize_swap_one F 0
        refine ⟨orient, ?_, ?_⟩
        · rw [← sideLoad_tail_add_head F orient 0]
          rw [hhead0]
          rw [← sideLoad_tail_add_head F orient 1]
          rw [hhead1]
          change sideLoad Ftail orientTail 0 + d ≤
            sideLoad Ftail orientTail 1 + a + slack
          exact hswap.1
        · rw [← sideLoad_tail_add_head F orient 1]
          rw [hhead1]
          rw [← sideLoad_tail_add_head F orient 0]
          rw [hhead0]
          change sideLoad Ftail orientTail 1 + a ≤
            sideLoad Ftail orientTail 0 + d + slack
          exact hswap.2

theorem exists_balanced_forest_orientation_with_capacity
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      2 * sideLoad F orient 0 ≤ F.order + slack ∧
      2 * sideLoad F orient 1 ≤ F.order + slack := by
  obtain ⟨orient, h01, h10⟩ :=
    exists_balanced_forest_orientation F slack hsmall
  have htotal := sideLoad_zero_add_one F orient
  exact ⟨orient, by omega, by omega⟩

/-- Integral ceiling of the balanced load on either endpoint. -/
def balancedSideBudget {b : ℕ} (F : OrderedRootedForest b)
    (slack : ℕ) : ℕ :=
  (F.order + slack + 1) / 2

theorem sideLoad_le_balancedSideBudget_of_two_mul_le
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2)
    (hload : 2 * sideLoad F orient c ≤ F.order + slack) :
    sideLoad F orient c ≤ balancedSideBudget F slack := by
  unfold balancedSideBudget
  omega

/-- Source-side certificate of Zhao Lemma 5.4(2)'s threshold switch.  Before
`cutoff`, both accumulated sides fit the low source-density budget.  From
`cutoff` on, every new branch root is sent to the high endpoint.  Final loads
on both endpoints fit the high budget. -/
structure ThresholdSwitchOrientation {b : ℕ}
    (F : OrderedRootedForest b) (lowSide : Fin 2)
    (lowBudget highBudget : ℕ) where
  orient : Fin b → Fin 2 ≃ Fin 2
  cutoff : Fin (b + 1)
  early_prefix : ∀ i, i.val < cutoff.val → ∀ c,
    sideLoadBefore F orient i c ≤ lowBudget
  late_root_high : ∀ i, cutoff.val ≤ i.val →
    branchRootSide F orient i ≠ lowSide
  final_load : ∀ c, sideLoad F orient c ≤ highBudget

theorem ThresholdSwitchOrientation.prefix_root_le
    {b : ℕ} {F : OrderedRootedForest b} {lowSide : Fin 2}
    {lowBudget highBudget : ℕ}
    (O : ThresholdSwitchOrientation F lowSide lowBudget highBudget)
    (hlowHigh : lowBudget ≤ highBudget) (i : Fin b) :
    sideLoadBefore F O.orient i (branchRootSide F O.orient i) ≤
      if branchRootSide F O.orient i = lowSide then lowBudget else highBudget := by
  by_cases hi : i.val < O.cutoff.val
  · by_cases hs : branchRootSide F O.orient i = lowSide
    · simpa [hs] using O.early_prefix i hi (branchRootSide F O.orient i)
    · simpa [hs] using (O.early_prefix i hi
        (branchRootSide F O.orient i)).trans hlowHigh
  · have hilate : O.cutoff.val ≤ i.val := Nat.le_of_not_gt hi
    have hs := O.late_root_high i hilate
    have hpref := sideLoadBefore_le_sideLoad F O.orient i
      (branchRootSide F O.orient i)
    simpa [hs] using hpref.trans (O.final_load (branchRootSide F O.orient i))

/-! ## Root-image-dependent eligible matching edges -/

/-- A matching edge is usable by an already prescribed original root when
that root is typical to both endpoint clusters. -/
def edgeEligible
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (z : B) (e : Fin k) : Prop :=
  ∀ c, z ∉ atypicalVertices G rho A (endpoint e c)

/-- The single Proposition-4.5 bad set used for every original forest root. -/
def endpointBadRoots
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (q : ℕ) : Finset B :=
  aggregateBadRoots G rho A
    (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) q

/-- Matching edges on which `z` is atypical to at least one endpoint.
Making this a noncomputable finite set keeps the public cardinal statements
free of an auxiliary `DecidablePred` parameter. -/
noncomputable def ineligibleEdges
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (z : B) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun e ↦ ¬edgeEligible G rho A endpoint z e

@[simp] theorem mem_ineligibleEdges
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (z : B) (e : Fin k) :
    e ∈ ineligibleEdges G rho A endpoint z ↔
      ¬edgeEligible G rho A endpoint z e := by
  classical
  simp [ineligibleEdges]

theorem endpointBadRoots_subset
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (q : ℕ) :
    endpointBadRoots G rho A endpoint q ⊆ A :=
  Finset.filter_subset _ _

theorem card_endpointBadRoots_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (q rootSlack : ℕ)
    (hq : 0 < q)
    (hunif : ∀ e c, G.IsUniform rho A (endpoint e c))
    (hrho : rho ≤ 1)
    (hslack : (((2 * k : ℕ) : ℝ) * rho * #A) / q ≤ rootSlack) :
    #(endpointBadRoots G rho A endpoint q) ≤ rootSlack := by
  have hunif' : ∀ p : Fin k × Fin 2,
      G.IsUniform rho A (endpoint p.1 p.2) := fun p ↦ hunif p.1 p.2
  have hcardReal : (#(endpointBadRoots G rho A endpoint q) : ℝ) ≤
      (((2 * k : ℕ) : ℝ) * rho * #A) / q := by
    have h := card_aggregateBadRoots_le G rho A
      (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) q hq hunif' hrho
    simpa [endpointBadRoots, Fintype.card_prod, Nat.mul_comm, mul_comm] using h
  exact_mod_cast hcardReal.trans hslack

/-- Every unusable matching edge contributes a distinct atypical endpoint.
This is the precise bridge from Proposition 4.5's endpoint count to the
number of bins which the root-dependent carry allocator may skip. -/
theorem card_ineligibleEdges_le_atypicalClusterCount
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (z : B) :
    #(ineligibleEdges G rho A endpoint z) ≤
      atypicalClusterCount G rho A
        (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) z := by
  classical
  let badSide : Fin k → Fin 2 := fun e ↦
    if z ∈ atypicalVertices G rho A (endpoint e 0) then 0 else 1
  let chooseEndpoint : Fin k → Fin k × Fin 2 := fun e ↦ ⟨e, badSide e⟩
  let badEdges : Finset (Fin k) := ineligibleEdges G rho A endpoint z
  let badEndpoints : Finset (Fin k × Fin 2) := Finset.univ.filter fun p ↦
    z ∈ atypicalVertices G rho A (endpoint p.1 p.2)
  have hmaps : Set.MapsTo chooseEndpoint (badEdges : Set (Fin k))
      (badEndpoints : Set (Fin k × Fin 2)) := by
    intro e he
    have heBad : ¬edgeEligible G rho A endpoint z e :=
      (mem_ineligibleEdges G rho A endpoint z e).mp he
    have hchosen : z ∈ atypicalVertices G rho A
        (endpoint e (badSide e)) := by
      by_cases h0 : z ∈ atypicalVertices G rho A (endpoint e 0)
      · simpa [badSide, h0] using h0
      · have h1 : z ∈ atypicalVertices G rho A (endpoint e 1) := by
          by_contra h1
          apply heBad
          intro c
          rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
          · exact h0
          · exact h1
        simpa [badSide, h0] using h1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [chooseEndpoint] using hchosen⟩
  have hinj : Set.InjOn chooseEndpoint (badEdges : Set (Fin k)) := by
    intro e _ f _ hef
    exact congrArg Prod.fst hef
  have hcard : #badEdges ≤ #badEndpoints :=
    Finset.card_le_card_of_injOn chooseEndpoint hmaps hinj
  simpa [badEdges, badEndpoints, atypicalClusterCount] using hcard

theorem card_ineligibleEdges_lt_of_goodRoot
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ} (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (q : ℕ) (z : B)
    (hzA : z ∈ A)
    (hzgood : z ∉ aggregateBadRoots G rho A
      (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) q) :
    #(ineligibleEdges G rho A endpoint z) < q := by
  have hcount : atypicalClusterCount G rho A
      (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) z < q := by
    by_contra h
    apply hzgood
    exact Finset.mem_filter.mpr ⟨hzA, Nat.le_of_not_gt h⟩
  exact (card_ineligibleEdges_le_atypicalClusterCount
    G rho A endpoint z).trans_lt hcount

/-- Root-image-dependent whole-branch assignment produced by the exact
single-skip-loss packing theorem. -/
structure EligibleBranchAssignment
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    [DecidableRel G.Adj] (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (rootImage : Fin r → B)
    (capacity : Fin k → ℕ) where
  edge : Fin b → Fin k
  edge_eligible : ∀ j,
    edgeEligible G rho A endpoint (rootImage (F.owner j)) (edge j)
  edge_load : ∀ e,
    ∑ j ∈ (Finset.univ.filter fun j ↦ edge j = e), F.branches.size j ≤
      capacity e

/-- Allocate after the adversarial root map is known.  Goodness is required
only for owners of branches which are actually present; isolated retained
roots impose no eligibility obligation. -/
theorem exists_eligibleBranchAssignment_of_goodRoots
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    [Nonempty (Fin k)]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    [DecidableRel G.Adj] (rho : ℝ) (A : Finset B)
    (endpoint : Fin k → Fin 2 → Finset B) (rootImage : Fin r → B)
    (capacity : Fin k → ℕ) (small capacityMax q : ℕ)
    (hrootMem : ∀ i, rootImage i ∈ A)
    (hrootGood : ∀ j, rootImage (F.owner j) ∉
      aggregateBadRoots G rho A
        (fun p : Fin k × Fin 2 ↦ endpoint p.1 p.2) q)
    (hsmall : ∀ j, F.branches.size j ≤ small)
    (hcapacityMax : ∀ e, capacity e ≤ capacityMax)
    (hbudget : (∑ j, F.branches.size j) + k * small +
        q * capacityMax ≤ ∑ e, capacity e) :
    Nonempty (EligibleBranchAssignment
      F G rho A endpoint rootImage capacity) := by
  classical
  let eligible : Fin b → Fin k → Prop := fun j e ↦
    edgeEligible G rho A endpoint (rootImage (F.owner j)) e
  have hpositive : ∀ j ∈ (Finset.univ : Finset (Fin b)),
      0 < F.branches.size j := by
    intro j _
    exact Nat.zero_lt_of_lt (F.branches.root j).isLt
  have hskip : ∀ j : Fin b,
      #((Finset.univ : Finset (Fin k)).filter fun e ↦ ¬eligible j e) ≤ q := by
    intro j
    have h := (card_ineligibleEdges_lt_of_goodRoot G rho A endpoint q
      (rootImage (F.owner j)) (hrootMem (F.owner j)) (hrootGood j)).le
    simpa [eligible, ineligibleEdges] using h
  obtain ⟨assign, hallowed, hload⟩ :=
    eligible_capacity_packing (Finset.univ : Finset (Fin b))
      F.branches.size capacity (fun j ↦ j) eligible small capacityMax q
      hpositive (fun j _ ↦ hsmall j) hcapacityMax hskip (by simpa using hbudget)
  exact ⟨{
    edge := assign
    edge_eligible := fun j ↦ hallowed j (Finset.mem_univ j)
    edge_load := fun e ↦ hload e
  }⟩

/-! ## Dynamic realization in one regular pair -/

/-- The vertices of a concrete tree copy which occupy physical side `c`.
Keeping this set side-specific is essential: deleting the whole previous
tree from both sides would lose twice the source mass and would not reproduce
the Lemma-5.4 carry calculation. -/
def orientedCopyImage
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (orient : Fin 2 ≃ Fin 2) (G : SimpleGraph B) (f : T.Copy G)
    (c : Fin 2) : Finset B :=
  (Finset.univ.filter fun a ↦
    orient (hT.coloringTwoOfVert root a) = c).image f

theorem card_orientedCopyImage
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (orient : Fin 2 ≃ Fin 2) (G : SimpleGraph B) (f : T.Copy G)
    (c : Fin 2) :
    #(orientedCopyImage T hT root orient G f c) =
      #(Finset.univ.filter fun a ↦
        orient (hT.coloringTwoOfVert root a) = c) := by
  rw [orientedCopyImage, Finset.card_image_iff.mpr]
  intro a _ b _ hab
  exact f.injective hab

theorem orientedCopyImage_subset
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (orient : Fin 2 ≃ Fin 2) (G : SimpleGraph B) (f : T.Copy G)
    (available : Fin 2 → Finset B)
    (hf : ∀ a, f a ∈ available (orient (hT.coloringTwoOfVert root a)))
    (c : Fin 2) :
    orientedCopyImage T hT root orient G f c ⊆ available c := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hac := (Finset.mem_filter.mp ha).2
  simpa [hac] using hf a

theorem copy_mem_orientedCopyImage
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A)
    (orient : Fin 2 ≃ Fin 2) (G : SimpleGraph B) (f : T.Copy G)
    (a : A) :
    f a ∈ orientedCopyImage T hT root orient G f
      (orient (hT.coloringTwoOfVert root a)) := by
  apply Finset.mem_image.mpr
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- A simultaneous embedding of an ordered rooted forest in one matching
pair, where each component root is chosen adjacent to its already embedded
external parent.  The membership statement includes the chosen component
roots, so it is stable under deleting the exact used image on each side. -/
structure DynamicAttachedForestEmbedding
    {m : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B)
    (externalParent : Fin m → B)
    (orient : Fin m → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) where
  embedding : F.Embedding G
  attach : ∀ i,
    G.Adj (externalParent i) (embedding.copy i (F.root i))
  map_side : ∀ i a,
    embedding.copy i a ∈
      available (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))

/-- Dynamic Lemma-5.4 engine for an ordered group of small rooted trees.

`reserve c` is an integral upper bound for the regularity loss
`rho * |whole c|`.  The hypotheses charge the *final* side load once.  At an
inductive step, the exact image on each side is deleted; the remaining tail
load plus the deleted head load is definitionally the original side load.
Thus this theorem does not impose the false static condition
`total load ≤ (density-rho)|whole|`. -/
theorem exists_dynamic_ordered_forest_embedding_of_uniform
    {m : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin m → B)
    (orient : Fin m → Fin 2 ≃ Fin 2)
    (whole available : Fin 2 → Finset B)
    (reserve : Fin 2 → ℕ) (rho density : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (havailableCapacity : ∀ c,
      sideLoad F orient c + reserve c ≤ #(available c))
    (hparent : ∀ i,
      1 + reserve (branchRootSide F orient i) +
          sideLoadBefore F orient i (branchRootSide F orient i) ≤
        #((available (branchRootSide F orient i)).filter
          (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - sideLoad F orient c)) :
    Nonempty (DynamicAttachedForestEmbedding F G externalParent orient available) := by
  classical
  induction m generalizing available with
  | zero =>
      let copies : ∀ i : Fin 0, (F.tree i).Copy G := fun i ↦ Fin.elim0 i
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩
        exact Fin.elim0 i
      exact ⟨{
        embedding := ⟨copies, hinjective⟩
        attach := fun i ↦ Fin.elim0 i
        map_side := fun i ↦ Fin.elim0 i
      }⟩
  | succ m ih =>
      let Ftail : OrderedRootedForest m := F.tail
      let parentTail : Fin m → B := fun i ↦ externalParent i.succ
      let orientTail : Fin m → Fin 2 ≃ Fin 2 := tailOrient orient
      have havailableLarge : ∀ c,
          rho * (#(whole c) : ℝ) ≤ #(available c) := by
        intro c
        have hresNat : reserve c ≤ #(available c) := by
          have hcap := havailableCapacity c
          omega
        have hresReal : (reserve c : ℝ) ≤ #(available c) := by
          exact_mod_cast hresNat
        exact (hreserve c).trans hresReal
      have hheadMargin : ∀ c,
          (F.size 0 : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
            (density - rho) * #(available c) := by
        intro c
        calc
          (F.size 0 : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
              (density - rho) *
                ((#(available c) : ℝ) - sideLoad F orient c) := hmargin 0 c
          _ ≤ (density - rho) * #(available c) := by
            apply mul_le_mul_of_nonneg_left _ hfactor
            exact sub_le_self _ (Nat.cast_nonneg _)
      have hheadParent :
          1 + rho * (#(whole (orient 0 0)) : ℝ) ≤
            (#((available (orient 0 0)).filter
              (G.Adj (externalParent 0))) : ℝ) := by
        have hp := hparent 0
        have hpReal :
            ((1 + reserve (branchRootSide F orient 0) +
              sideLoadBefore F orient 0
                (branchRootSide F orient 0) : ℕ) : ℝ) ≤
              #((available (branchRootSide F orient 0)).filter
                (G.Adj (externalParent 0))) := by
          exact_mod_cast hp
        have hr := hreserve (orient 0 0)
        have hpSimple :
            (1 : ℝ) + reserve (orient 0 0) ≤
              (#((available (orient 0 0)).filter
                (G.Adj (externalParent 0))) : ℝ) := by
          simpa only [branchRootSide, sideLoadBefore_zero, Nat.cast_add,
            Nat.cast_one, Nat.cast_zero, add_zero] using hpReal
        calc
          1 + rho * (#(whole (orient 0 0)) : ℝ) =
              rho * (#(whole (orient 0 0)) : ℝ) + 1 := by rw [add_comm]
          _ ≤ reserve (orient 0 0) + 1 := by
            simpa only [add_comm] using add_le_add_right hr 1
          _ = 1 + reserve (orient 0 0) := by rw [add_comm]
          _ ≤ (#((available (orient 0 0)).filter
                (G.Adj (externalParent 0))) : ℝ) := hpSimple
      have hheadMarginFin : ∀ c,
          (Fintype.card (Fin (F.size 0)) : ℝ) +
              rho * (#(whole c) : ℝ) + 1 ≤
            (density - rho) * #(available c) := by
        simpa only [Fintype.card_fin] using hheadMargin
      obtain ⟨fhead, hfheadAttach, hfheadMem⟩ :=
        exists_dynamic_rooted_tree_copy_of_uniform
          (F.tree 0) (F.isTree 0) (F.root 0) G (externalParent 0)
          (orient 0) whole available rho density hunif havailable
          havailableLarge hdensity hwholeDisjoint hheadParent hheadMarginFin
      let used : Fin 2 → Finset B := fun c ↦
        orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead c
      have husedSubset (c : Fin 2) : used c ⊆ available c := by
        exact orientedCopyImage_subset (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead available hfheadMem c
      have husedCard (c : Fin 2) :
          #(used c) = orientedClassSize F orient 0 c := by
        exact card_orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
          (orient 0) G fhead c
      let availableTail : Fin 2 → Finset B := fun c ↦ available c \ used c
      have htailAvailable (c : Fin 2) : availableTail c ⊆ whole c :=
        (Finset.sdiff_subset.trans (havailable c))
      have htailCapacity : ∀ c,
          sideLoad Ftail orientTail c + reserve c ≤ #(availableTail c) := by
        intro c
        rw [show #(availableTail c) = #(available c) - #(used c) by
          exact Finset.card_sdiff_of_subset (husedSubset c)]
        rw [husedCard]
        have hload := sideLoad_tail_add_head F orient c
        have hcap := havailableCapacity c
        apply Nat.le_sub_of_add_le
        calc
          (sideLoad Ftail orientTail c + reserve c) +
                orientedClassSize F orient 0 c =
              (sideLoad Ftail orientTail c +
                orientedClassSize F orient 0 c) + reserve c := by omega
          _ = sideLoad F orient c + reserve c := by rw [hload]
          _ ≤ #(available c) := hcap
      have htailParent : ∀ i,
          1 + reserve (branchRootSide Ftail orientTail i) +
              sideLoadBefore Ftail orientTail i
                (branchRootSide Ftail orientTail i) ≤
            #((availableTail (branchRootSide Ftail orientTail i)).filter
              (G.Adj (parentTail i))) := by
        intro i
        apply card_neighbors_cleaned_ge G
          (available (branchRootSide Ftail orientTail i))
          (used (branchRootSide Ftail orientTail i)) (parentTail i)
          (1 + reserve (branchRootSide Ftail orientTail i) +
            sideLoadBefore Ftail orientTail i
              (branchRootSide Ftail orientTail i))
        rw [husedCard]
        have hside : branchRootSide Ftail orientTail i =
            branchRootSide F orient i.succ := rfl
        have hload := sideLoadBefore_tail_add_head F orient i
          (branchRootSide Ftail orientTail i)
        have hp := hparent i.succ
        have hcombined :
            (1 + reserve (branchRootSide Ftail orientTail i) +
                sideLoadBefore Ftail orientTail i
                  (branchRootSide Ftail orientTail i)) +
                orientedClassSize F orient 0
                  (branchRootSide Ftail orientTail i) ≤
              #((available (branchRootSide Ftail orientTail i)).filter
                (G.Adj (externalParent i.succ))) := by
          calc
            (1 + reserve (branchRootSide Ftail orientTail i) +
                sideLoadBefore Ftail orientTail i
                  (branchRootSide Ftail orientTail i)) +
                orientedClassSize F orient 0
                  (branchRootSide Ftail orientTail i) =
              1 + reserve (branchRootSide Ftail orientTail i) +
                (sideLoadBefore Ftail orientTail i
                    (branchRootSide Ftail orientTail i) +
                  orientedClassSize F orient 0
                    (branchRootSide Ftail orientTail i)) := by omega
            _ = 1 + reserve (branchRootSide Ftail orientTail i) +
                sideLoadBefore F orient i.succ
                  (branchRootSide Ftail orientTail i) := by rw [hload]
            _ ≤ #((available (branchRootSide Ftail orientTail i)).filter
                (G.Adj (externalParent i.succ))) := by
              simpa only [hside] using hp
        simpa only [parentTail] using hcombined
      have htailMargin : ∀ i c,
          (Ftail.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
            (density - rho) *
              ((#(availableTail c) : ℝ) - sideLoad Ftail orientTail c) := by
        intro i c
        have husedLe : #(used c) ≤ #(available c) :=
          Finset.card_le_card (husedSubset c)
        have hcardTail : (#(availableTail c) : ℝ) =
            (#(available c) : ℝ) - #(used c) := by
          rw [show #(availableTail c) = #(available c) - #(used c) by
            exact Finset.card_sdiff_of_subset (husedSubset c)]
          exact Nat.cast_sub husedLe
        have hload := sideLoad_tail_add_head F orient c
        have hloadReal :
            (sideLoad Ftail orientTail c : ℝ) +
                orientedClassSize F orient 0 c = sideLoad F orient c := by
          exact_mod_cast hload
        have hm := hmargin i.succ c
        rw [← hloadReal] at hm
        rw [hcardTail, husedCard]
        change (F.size i.succ : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤ _
        simpa [Ftail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hm
      obtain ⟨Etail⟩ := ih Ftail parentTail orientTail availableTail
        htailAvailable htailCapacity htailParent htailMargin
      have hwholeDisjoint' : ∀ c d, c ≠ d → Disjoint (whole c) (whole d) := by
        intro c d hcd
        fin_cases c <;> fin_cases d
        · exact False.elim (hcd rfl)
        · exact hwholeDisjoint
        · exact hwholeDisjoint.symm
        · exact False.elim (hcd rfl)
      have hheadTailDisjoint : ∀ a i b,
          fhead a ≠ Etail.embedding.copy i b := by
        intro a i b hab
        let ca := orient 0 ((F.isTree 0).coloringTwoOfVert (F.root 0) a)
        let cb := orientTail i
          ((Ftail.isTree i).coloringTwoOfVert (Ftail.root i) b)
        have haUsed : fhead a ∈ used ca := by
          exact copy_mem_orientedCopyImage (F.tree 0) (F.isTree 0) (F.root 0)
            (orient 0) G fhead a
        have hbTail : Etail.embedding.copy i b ∈ availableTail cb :=
          Etail.map_side i b
        by_cases hcb : ca = cb
        · have hbTailCa : Etail.embedding.copy i b ∈ availableTail ca := by
            simpa only [hcb] using hbTail
          exact (Finset.mem_sdiff.mp hbTailCa).2 (hab ▸ haUsed)
        · have haWhole : fhead a ∈ whole ca :=
            havailable ca (husedSubset ca haUsed)
          have hbWhole : Etail.embedding.copy i b ∈ whole cb :=
            havailable cb ((Finset.mem_sdiff.mp hbTail).1)
          exact (Finset.disjoint_left.mp (hwholeDisjoint' ca cb hcb) haWhole)
            (hab ▸ hbWhole)
      let copies : ∀ i, (F.tree i).Copy G :=
        Fin.cases fhead (fun i ↦ Etail.embedding.copy i)
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩ ⟨k, b⟩ hab
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change fhead a = fhead b at hab
            have : a = b := fhead.injective hab
            subst b
            rfl
          · change fhead a = Etail.embedding.copy k b at hab
            exact False.elim (hheadTailDisjoint a k b hab)
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change Etail.embedding.copy i a = fhead b at hab
            exact False.elim (hheadTailDisjoint b i a hab.symm)
          · have htail :
                (⟨i, a⟩ : Σ i, Fin (Ftail.size i)) = ⟨k, b⟩ := by
                apply Etail.embedding.injective
                change Etail.embedding.copy i a = Etail.embedding.copy k b at hab
                exact hab
            cases htail
            rfl
      let E : F.Embedding G := ⟨copies, hinjective⟩
      exact ⟨{
        embedding := E
        attach := by
          intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · exact hfheadAttach
          · exact Etail.attach i
        map_side := by
          intro i a
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · exact hfheadMem a
          · exact (Finset.mem_sdiff.mp (Etail.map_side i a)).1
      }⟩

/-- A symmetric balanced-load dynamic helper.  This is useful in the equal-
density subcase, but it is deliberately not called Lemma 5.4(1)/(2): those
source statements use prefix root-degree budgets, not a common final-load
budget. -/
theorem exists_balancedDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (slack : ℕ)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (reserve : Fin 2 → ℕ) (rho density : ℝ)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (havailableCapacity : ∀ c,
      balancedSideBudget F slack + reserve c ≤ #(available c))
    (hparent : ∀ i c,
      1 + reserve c + balancedSideBudget F slack ≤
        #((available c).filter (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - balancedSideBudget F slack)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  obtain ⟨orient, hload0, hload1⟩ :=
    exists_balanced_forest_orientation_with_capacity F slack hsmall
  have hload : ∀ c, sideLoad F orient c ≤ balancedSideBudget F slack := by
    intro c
    rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · exact sideLoad_le_balancedSideBudget_of_two_mul_le
        F slack orient 0 hload0
    · exact sideLoad_le_balancedSideBudget_of_two_mul_le
        F slack orient 1 hload1
  refine ⟨orient,
    exists_dynamic_ordered_forest_embedding_of_uniform F G externalParent
      orient whole available reserve rho density hunif havailable
      hwholeDisjoint hdensity hfactor hreserve ?_ ?_ ?_⟩
  · intro c
    exact (Nat.add_le_add_right (hload c) (reserve c)).trans
      (havailableCapacity c)
  · intro i
    have hpref := (sideLoadBefore_le_sideLoad F orient i
      (branchRootSide F orient i)).trans
        (hload (branchRootSide F orient i))
    exact (Nat.add_le_add_left hpref
      (1 + reserve (branchRootSide F orient i))).trans
        (hparent i (branchRootSide F orient i))
  · intro i c
    calc
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
          (density - rho) *
            ((#(available c) : ℝ) - balancedSideBudget F slack) :=
        hmargin i c
      _ ≤ (density - rho) *
          ((#(available c) : ℝ) - sideLoad F orient c) := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        exact sub_le_sub_left (by exact_mod_cast hload c) _

/-- The preceding symmetric helper with any larger common endpoint budget.
It remains a stronger convenience theorem, not the asymmetric source
Lemma 5.4(2). -/
theorem exists_balancedDynamicGroupEmbedding_of_budget
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (slack highBudget : ℕ)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (reserve : Fin 2 → ℕ) (rho density : ℝ)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hbalancedCapacity : F.order + slack ≤ 2 * highBudget)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (havailableCapacity : ∀ c,
      highBudget + reserve c ≤ #(available c))
    (hparent : ∀ i c,
      1 + reserve c + highBudget ≤
        #((available c).filter (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) * ((#(available c) : ℝ) - highBudget)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  have hbudget : balancedSideBudget F slack ≤ highBudget := by
    unfold balancedSideBudget
    omega
  apply exists_balancedDynamicGroupEmbedding F slack G externalParent whole
    available reserve rho density hsmall hunif havailable hwholeDisjoint
    hdensity hfactor hreserve
  · intro c
    exact (Nat.add_le_add_right hbudget (reserve c)).trans
      (havailableCapacity c)
  · intro i c
    exact (Nat.add_le_add_left hbudget (1 + reserve c)).trans (hparent i c)
  · intro i c
    calc
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
          (density - rho) * ((#(available c) : ℝ) - highBudget) :=
        hmargin i c
      _ ≤ (density - rho) *
          ((#(available c) : ℝ) - balancedSideBudget F slack) := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        exact sub_le_sub_left (by exact_mod_cast hbudget) _

/-! ## The literal one-carry arithmetic -/

/-- A next-fit allocation.  The item order is preserved.  Every used bin
before the last used bin is within one item of being full; this is Zhao's
single carry forest `F'_i`. -/
structure CarryAllocation {m k : ℕ}
    (weight : Fin m → ℕ) (capacity : Fin k → ℕ) (slack : ℕ) where
  bin : Fin m → Fin k
  monotone : Monotone bin
  load_le : ∀ e : Fin k,
    ∑ i ∈ (Finset.univ.filter fun i ↦ bin i = e), weight i ≤ capacity e
  completed_near_capacity : ∀ e : Fin k,
    (∃ i, e < bin i) →
      capacity e <
        (∑ i ∈ (Finset.univ.filter fun i ↦ bin i = e), weight i) + slack

/-- The actual source-side hypotheses under which next-fit cannot run out of
matching edges.  `capacity e` is the paper weight `w(e)` after its fixed
regularity reserve has been subtracted. -/
structure CarryBudget {m k : ℕ}
    (weight : Fin m → ℕ) (capacity : Fin k → ℕ) (slack : ℕ) : Prop where
  item_pos : ∀ i, 0 < weight i
  item_small : ∀ i, weight i ≤ slack
  bin_large : ∀ e, slack ≤ capacity e
  total : (∑ i, weight i) + k * slack ≤ ∑ e, capacity e

namespace CarryAllocation

/-- The fiber on one carry edge, as a literal root-subforest retaining whole
root-deleted branches. -/
noncomputable def rootSubforest
    {r b k : ℕ} (F : OrderedBranchForest r b)
    {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation F.branches.size capacity slack) (e : Fin k) :
    OrderedBranchForest r
      #((Finset.univ : Finset (Fin b)).filter fun i ↦ C.bin i = e) :=
  ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
    ((Finset.univ : Finset (Fin b)).filter fun i ↦ C.bin i = e)

@[simp] theorem edgeDemand_rootSubforest
    {r b k : ℕ} (F : OrderedBranchForest r b)
    {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation F.branches.size capacity slack) (e : Fin k) :
    ZhaoClaim616SourceBridge.OrderedBranchForest.edgeDemand
        (rootSubforest F C e) =
      ∑ i ∈ (Finset.univ.filter fun i ↦ C.bin i = e), F.branches.size i := by
  exact ZhaoClaim616SourceBridge.OrderedBranchForest.edgeDemand_restrict F _

theorem edgeDemand_rootSubforest_le_capacity
    {r b k : ℕ} (F : OrderedBranchForest r b)
    {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation F.branches.size capacity slack) (e : Fin k) :
    ZhaoClaim616SourceBridge.OrderedBranchForest.edgeDemand
        (rootSubforest F C e) ≤ capacity e := by
  rw [edgeDemand_rootSubforest]
  exact C.load_le e

/-- The unique live carry edge after a nonempty ordered prefix: the edge of
the final branch.  Monotonicity makes every strictly earlier edge completed. -/
def carryEdge
    {m k : ℕ} {weight : Fin m → ℕ} {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation weight capacity slack) (hm : 0 < m) : Fin k :=
  C.bin ⟨m - 1, by omega⟩

theorem completed_near_capacity_of_lt_carryEdge
    {m k : ℕ} {weight : Fin m → ℕ} {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation weight capacity slack) (hm : 0 < m)
    (e : Fin k) (he : e < C.carryEdge hm) :
    capacity e <
      (∑ i ∈ (Finset.univ.filter fun i ↦ C.bin i = e), weight i) + slack := by
  apply C.completed_near_capacity e
  exact ⟨⟨m - 1, by omega⟩, he⟩

theorem completed_rootSubforest_near_capacity_of_lt_carryEdge
    {r b k : ℕ} (F : OrderedBranchForest r b)
    {capacity : Fin k → ℕ} {slack : ℕ}
    (C : CarryAllocation F.branches.size capacity slack) (hb : 0 < b)
    (e : Fin k) (he : e < C.carryEdge hb) :
    capacity e <
      ZhaoClaim616SourceBridge.OrderedBranchForest.edgeDemand
        (rootSubforest F C e) + slack := by
  rw [edgeDemand_rootSubforest]
  exact C.completed_near_capacity_of_lt_carryEdge hb e he

end CarryAllocation

/-! ## The two local capacity displays in Lemma 5.8 -/

/-- Algebraic identity behind display (5.2). -/
theorem partTwo_capacity_identity
    (c dx dy gamma epsilon N : ℝ) (hc : c ≠ 1) :
    (dx + dy - 2 * gamma - 3 * epsilon) * N +
        c / (1 - c) * (dy - dx) * N =
      (2 * dx - 2 * gamma - 3 * epsilon) * N +
        1 / (1 - c) * (dy - dx) * N := by
  have hden : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  field_simp [hden]
  ring

/-- The exceptional gap contribution in Lemma 5.8(2) is dominated by the
local Lemma-5.4(2) capacity after the low/high endpoint orientation. -/
theorem partTwo_exceptional_weight_le_local
    (c dx dy lambda gamma epsilon N : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hN : 0 ≤ N)
    (hgap : lambda ≤ dy - dx) :
    (dx + dy - 2 * gamma - 3 * epsilon) * N +
        c / (1 - c) * lambda * N ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N +
        c / (1 - c) * (dy - dx) * N := by
  have hden : 0 < 1 - c := sub_pos.mpr hc1
  have hfactor : 0 ≤ c / (1 - c) := div_nonneg hc0 hden.le
  gcongr

/-- The ratio/gap display of Lemma 5.4(2) implies that the balanced
orientation fits below the high source-density endpoint. -/
theorem partTwo_balanced_load_le_high
    (c dx dy gamma epsilon N mass slack : ℝ)
    (hc0 : 0 ≤ c) (hcHalf : c ≤ 1 / 2)
    (hxy : dx ≤ dy) (hN : 0 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hmass : mass ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N +
        c / (1 - c) * (dy - dx) * N)
    (hslack : slack ≤ epsilon * N) :
    (mass + slack) / 2 ≤ (dy - gamma) * N := by
  have hc1 : c < 1 := lt_of_le_of_lt hcHalf (by norm_num)
  have hden : 0 < 1 - c := sub_pos.mpr hc1
  have hcoef0 : 0 ≤ c / (1 - c) := div_nonneg hc0 hden.le
  have hcoef1 : c / (1 - c) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hgap : 0 ≤ dy - dx := sub_nonneg.mpr hxy
  have hweighted :
      c / (1 - c) * (dy - dx) * N ≤ (dy - dx) * N := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef1 hgap) hN
    simpa [mul_assoc] using this
  nlinarith

/-- Arithmetic core of the genuine `i₀` threshold switch.  Maximality of the
balanced prefix gives `2L < p+2s`; the source mass display then leaves less
than `gap/(1-c)-s` vertices in the suffix.  Since either forced suffix side
uses at most a `(1-c)` fraction, its load is at most the source-density gap.
-/
theorem partTwo_threshold_suffix_load_le_gap
    (c mass prefixMass low gap slack suffixLoad : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hgap : 0 ≤ gap) (hslack : 0 ≤ slack)
    (hmass : mass ≤ 2 * low - 3 * slack + gap / (1 - c))
    (hmaximal : 2 * low < prefixMass + 2 * slack)
    (hsuffix : suffixLoad ≤ (1 - c) * (mass - prefixMass)) :
    suffixLoad ≤ gap := by
  have hden : 0 < 1 - c := sub_pos.mpr hc1
  have hremain : mass - prefixMass < gap / (1 - c) - slack := by
    linarith
  have hmul : (1 - c) * (mass - prefixMass) <
      (1 - c) * (gap / (1 - c) - slack) :=
    mul_lt_mul_of_pos_left hremain hden
  have hdiv : (1 - c) * (gap / (1 - c)) = gap := by
    field_simp [hden.ne']
  have hlt : suffixLoad < gap := calc
    suffixLoad ≤ (1 - c) * (mass - prefixMass) := hsuffix
    _ < (1 - c) * (gap / (1 - c) - slack) := hmul
    _ = gap - (1 - c) * slack := by rw [mul_sub, hdiv]
    _ ≤ gap := sub_le_self _ (mul_nonneg hden.le hslack)
  exact hlt.le

/-- Local hypotheses of Lemma 5.4(2), separated from the matching carry.
They are purely source/cardinality and regular-pair facts. -/
structure PartTwoLocalData {b : ℕ} (F : OrderedRootedForest b)
    (group : Finset (Fin b)) (c dx dy gamma epsilon N : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c_le_half : c ≤ 1 / 2
  low_le_high : dx ≤ dy
  ratio_lower : ∀ i ∈ group,
    c ≤ (#(colourClass F i 0) : ℝ) / F.size i
  ratio_upper : ∀ i ∈ group,
    (#(colourClass F i 0) : ℝ) / F.size i ≤ 1 - c
  mass_le : ((∑ i ∈ group, F.size i : ℕ) : ℝ) ≤
    (dx + dy - 2 * gamma - 3 * epsilon) * N +
      c / (1 - c) * (dy - dx) * N

/-- The capacity hypotheses of Corollary A.1, written without truncated
natural subtraction.  `U₀,U₁` are the two colour-class loads and `R₀,R₁`
the numbers of prescribed roots sent to the corresponding target sets. -/
structure AppendixOneCapacity
    (U₀ U₁ R₀ R₁ X₀ X₁ P Q : ℕ) (gamma epsilon N : ℝ) : Prop where
  side_zero : (U₀ : ℝ) + (gamma + 3 * epsilon) * N ≤ X₀
  side_one : (U₁ : ℝ) + (gamma + 3 * epsilon) * N ≤ X₁
  root_zero : (R₀ : ℝ) + 3 * epsilon * N ≤ P
  root_one : (R₁ : ℝ) + 3 * epsilon * N ≤ Q

/-- The exact Appendix-A numerical input of Lemma 5.4(3).  The two displayed
bounds are Zhao's Lemma A.2, with every subtraction moved to the left so the
statement agrees with cardinal arithmetic even when a reserve is larger than
the target.  No balancing or embedding conclusion is assumed. -/
structure PartThreeAppendixData {b : ℕ}
    (F : OrderedRootedForest b) (group : Finset (Fin b))
    (P Q X₁ : ℕ) (gamma epsilon N : ℝ) : Prop where
  component_lower : ∀ i ∈ group, 2 ≤ F.size i
  component_upper : ∀ i ∈ group, (F.size i : ℝ) ≤ epsilon * N
  appendix_first :
    ((∑ i ∈ group, F.size i : ℕ) : ℝ) + 12 * epsilon * N ≤
      2 * P + 2 * Q
  appendix_second :
    ((∑ i ∈ group, F.size i : ℕ) : ℝ) +
        (2 * gamma + 7 * epsilon) * N ≤
      (Nat.min P Q : ℕ) + X₁

/-! ## Graph output of one grouped realization -/

/-- An actual simultaneous branch embedding, including every edge from an
external original root to its branch root. -/
structure RootAttachedBranchEmbedding
    {r b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (endpoint : Fin b → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2) where
  branchEmbedding : F.branches.Embedding G
  attach : ∀ i,
    G.Adj (rootImage (F.owner i))
      (branchEmbedding.copy i (F.branches.root i))
  map_branch : ∀ i a,
    branchEmbedding.copy i a ∈
      endpoint i (orient i
        ((F.branches.isTree i).coloringTwoOfVert (F.branches.root i) a))

/-- Turn an actual attached branch embedding into the literal reconstructed
ordered-forest copy. -/
def RootAttachedBranchEmbedding.toGraphCopy
    {r b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (endpoint : Fin b → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (E : RootAttachedBranchEmbedding F G rootImage endpoint orient)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q i a, rootImage q ≠ E.branchEmbedding.copy i a) :
    F.graph.Copy G :=
  F.copyOfBranchEmbedding G rootImage E.branchEmbedding hrootInjective
    hrootOutside E.attach

/-- Package an attached branch realization in Proposition 5.7's exact
full-forest output type.  No containment or copy is supplied by the caller;
the copy is the literal reconstruction above. -/
def RootAttachedBranchEmbedding.toRootedTargetEmbedding
    {r b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (endpoint : Fin b → Fin 2 → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (E : RootAttachedBranchEmbedding F G rootImage endpoint orient)
    (target : Finset B)
    (hendpoint : ∀ i c, endpoint i c ⊆ target)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q i a, rootImage q ≠ E.branchEmbedding.copy i a) :
    RootedTargetEmbedding F.graph G F.roots target
      (fun x ↦ match x with
        | Sum.inl q => rootImage q
        | Sum.inr z => E.branchEmbedding.copy z.1 z.2) := by
  let full := E.toGraphCopy F G rootImage endpoint orient
    hrootInjective hrootOutside
  refine {
    copy := full
    map_root := ?_
    map_nonroot := ?_
  }
  · intro x hx
    obtain ⟨q, rfl⟩ := (F.mem_roots_iff x).mp hx
    rfl
  · intro x hx
    rcases x with q | z
    · exact False.elim (hx ((F.mem_roots_iff (Sum.inl q)).mpr ⟨q, rfl⟩))
    · apply hendpoint z.1
        (orient z.1 ((F.branches.isTree z.1).coloringTwoOfVert
          (F.branches.root z.1) z.2))
      exact E.map_branch z.1 z.2

end Erdos547b.ZhaoLemma58GroupedSmallForest

#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.sideLoad_zero_add_one
#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.partTwo_capacity_identity
#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.partTwo_exceptional_weight_le_local
