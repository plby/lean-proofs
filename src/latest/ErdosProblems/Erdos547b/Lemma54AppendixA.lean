/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54ThresholdOrientation

/-!
# Zhao Lemma 5.4, Appendix A: the source orientation

This file contains only the finite source-side assertion of Zhao's Lemma A.2.
It does not invoke an embedding or accept a copy as input.  The graph
realization in Corollary A.1 is deliberately separate: its online proof must
reserve the prescribed root sets `P,Q` while ordinary vertices are embedded,
whereas the generic grouped engine charges the whole earlier side load to a
parent neighbourhood.

The paper suppresses integer roundings in expressions such as `3 * epsilon *
N`.  `AppendixA2NumericData` records their honest natural upper roundings.
This is the form used by the eventual hierarchy: `rootReserve` and
`sideReserve` dominate the two real margins, and the two source displays are
stated directly with these integral reserves.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma54AppendixA

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation

universe u

/-! ## Root and side loads -/

/-- Number of component roots sent to physical side `c`. -/
def rootLoad {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) : ℕ :=
  #((Finset.univ : Finset (Fin b)).filter fun i ↦
    branchRootSide F orient i = c)

theorem rootLoad_le_components {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2) :
    rootLoad F orient c ≤ b := by
  calc
    rootLoad F orient c ≤ #(Finset.univ : Finset (Fin b)) :=
      Finset.card_filter_le _ _
    _ = b := by simp

theorem rootLoad_zero_add_one {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) :
    rootLoad F orient 0 + rootLoad F orient 1 = b := by
  classical
  let Z := (Finset.univ : Finset (Fin b)).filter fun i ↦
    branchRootSide F orient i = 0
  let O := (Finset.univ : Finset (Fin b)).filter fun i ↦
    branchRootSide F orient i = 1
  have hdisj : Disjoint Z O := by
    rw [Finset.disjoint_left]
    intro i hiZ hiO
    have hi0 := (Finset.mem_filter.mp hiZ).2
    have hi1 := (Finset.mem_filter.mp hiO).2
    exact Fin.zero_ne_one (hi0.symm.trans hi1)
  have hunion : Z ∪ O = Finset.univ := by
    ext i
    simp only [Z, O, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    exact OrderedRootedForest.fin_two_eq_zero_or_one
      (branchRootSide F orient i)
  change Z.card + O.card = b
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

/-- Every physical side receives a vertex from every nontrivial tree. -/
theorem one_le_orientedClassSize_of_two_le
    {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (i : Fin b) (c : Fin 2)
    (htwo : 2 ≤ F.size i) :
    1 ≤ orientedClassSize F orient i c := by
  classical
  let : Nontrivial (Fin (F.size i)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa using (show 1 < F.size i by omega))
  let : DecidableRel (F.tree i).Adj := Classical.decRel _
  have hdegree : 0 < (F.tree i).degree (F.root i) :=
    (F.isTree i).preconnected.degree_pos_of_nontrivial (F.root i)
  obtain ⟨w, hw⟩ := ((F.tree i).degree_pos_iff_exists_adj (F.root i)).mp hdegree
  have hwColorNe :
      (F.isTree i).coloringTwoOfVert (F.root i) w ≠ 0 := by
    have hvalid := ((F.isTree i).coloringTwoOfVert (F.root i)).valid hw
    simpa using hvalid.symm
  have hwColor : (F.isTree i).coloringTwoOfVert (F.root i) w = 1 := by
    rcases OrderedRootedForest.fin_two_eq_zero_or_one
      ((F.isTree i).coloringTwoOfVert (F.root i) w) with hzero | hone
    · exact False.elim (hwColorNe hzero)
    · exact hone
  let localSide := (orient i).symm c
  rcases OrderedRootedForest.fin_two_eq_zero_or_one localSide with
      hlocal | hlocal
  · change 1 ≤ #(Finset.univ.filter fun a ↦
        orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = c)
    apply Finset.one_le_card.mpr
    refine ⟨F.root i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hc : orient i localSide = c := (orient i).apply_symm_apply c
    simpa [localSide, hlocal] using hc
  · change 1 ≤ #(Finset.univ.filter fun a ↦
        orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = c)
    apply Finset.one_le_card.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hc : orient i localSide = c := (orient i).apply_symm_apply c
    simpa [localSide, hlocal, hwColor] using hc

theorem components_le_sideLoad {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (c : Fin 2)
    (htwo : ∀ i, 2 ≤ F.size i) :
    b ≤ sideLoad F orient c := by
  calc
    b = ∑ _i : Fin b, 1 := by simp
    _ ≤ ∑ i : Fin b, orientedClassSize F orient i c := by
      exact Finset.sum_le_sum fun i _ ↦
        one_le_orientedClassSize_of_two_le F orient i c (htwo i)
    _ = sideLoad F orient c := rfl

/-! ## Two elementary orientation constructors -/

/-- Orient precisely the roots indexed by `S` toward side zero. -/
def orientationForRootSet {b : ℕ} (S : Finset (Fin b))
    (i : Fin b) : Fin 2 ≃ Fin 2 :=
  rootToSide (if i ∈ S then 0 else 1)

@[simp] theorem branchRootSide_orientationForRootSet
    {b : ℕ} (F : OrderedRootedForest b) (S : Finset (Fin b)) (i : Fin b) :
    branchRootSide F (orientationForRootSet S) i =
      if i ∈ S then 0 else 1 := by
  simp [branchRootSide, orientationForRootSet]

@[simp] theorem rootLoad_orientationForRootSet_zero
    {b : ℕ} (F : OrderedRootedForest b) (S : Finset (Fin b)) :
    rootLoad F (orientationForRootSet S) 0 = S.card := by
  classical
  have hfilter :
      (Finset.univ : Finset (Fin b)).filter (fun i ↦
        branchRootSide F (orientationForRootSet S) i = 0) = S := by
    ext i
    simp [branchRootSide_orientationForRootSet]
  exact congrArg Finset.card hfilter

@[simp] theorem rootLoad_orientationForRootSet_one
    {b : ℕ} (F : OrderedRootedForest b) (S : Finset (Fin b)) :
    rootLoad F (orientationForRootSet S) 1 = b - S.card := by
  have hsum := rootLoad_zero_add_one F (orientationForRootSet S)
  simp only [rootLoad_orientationForRootSet_zero] at hsum
  omega

/-- Swap the two physical endpoints after applying an orientation. -/
def flipOrientation {b : ℕ} (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) : Fin 2 ≃ Fin 2 :=
  (orient i).trans (Equiv.swap (0 : Fin 2) 1)

theorem orientedClassSize_flip_zero {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) :
    orientedClassSize F (flipOrientation orient) i 0 =
      orientedClassSize F orient i 1 := by
  classical
  change #(Finset.univ.filter fun a ↦
      Equiv.swap (0 : Fin 2) 1
        (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) = 0) =
    #(Finset.univ.filter fun a ↦
      orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = 1)
  apply congrArg Finset.card
  ext a
  have hswap (z : Fin 2) :
      (Equiv.swap (0 : Fin 2) 1 z = 0) ↔ z = 1 := by
    fin_cases z <;> simp [Equiv.swap_apply_def]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      hswap (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))

theorem orientedClassSize_flip_one {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (i : Fin b) :
    orientedClassSize F (flipOrientation orient) i 1 =
      orientedClassSize F orient i 0 := by
  classical
  change #(Finset.univ.filter fun a ↦
      Equiv.swap (0 : Fin 2) 1
        (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) = 1) =
    #(Finset.univ.filter fun a ↦
      orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = 0)
  apply congrArg Finset.card
  ext a
  have hswap (z : Fin 2) :
      (Equiv.swap (0 : Fin 2) 1 z = 1) ↔ z = 0 := by
    fin_cases z <;> simp [Equiv.swap_apply_def]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      hswap (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))

@[simp] theorem sideLoad_flip_zero {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2) :
    sideLoad F (flipOrientation orient) 0 = sideLoad F orient 1 := by
  simp only [sideLoad, orientedClassSize_flip_zero]

@[simp] theorem sideLoad_flip_one {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2) :
    sideLoad F (flipOrientation orient) 1 = sideLoad F orient 0 := by
  simp only [sideLoad, orientedClassSize_flip_one]

/-- The balanced orientation with the smaller load labelled side zero, as in
the proof of Lemma A.2. -/
theorem exists_ordered_balanced_orientation
    {b : ℕ} (F : OrderedRootedForest b) (small : ℕ)
    (hsmall : ∀ i, F.size i ≤ small) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      sideLoad F orient 0 ≤ sideLoad F orient 1 ∧
      sideLoad F orient 1 ≤ sideLoad F orient 0 + small := by
  obtain ⟨base, hbase01, hbase10⟩ :=
    exists_balanced_forest_orientation F small hsmall
  by_cases hle : sideLoad F base 0 ≤ sideLoad F base 1
  · exact ⟨base, hle, hbase10⟩
  · refine ⟨flipOrientation base, ?_, ?_⟩
    · have : sideLoad F base 1 ≤ sideLoad F base 0 := by omega
      simpa using this
    · simpa using hbase01

/-! ## The exact rounded Appendix-A.2 output -/

/-- Zhao's three alternatives, expressed in integer cardinalities.  The
first line is the unused-endpoint balance.  The other two say that both used
sides reach the `P`- or `Q`-threshold, including the root reserve. -/
def natAbsDiff (u v : ℕ) : ℕ := max (u - v) (v - u)

def AppendixA2Trichotomy {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (X Y P Q rootReserve small : ℕ) : Prop :=
  natAbsDiff (X - sideLoad F orient 0) (Y - sideLoad F orient 1) ≤
      max (natAbsDiff X Y) small ∨
    (P ≤ sideLoad F orient 0 + rootReserve ∧
      P ≤ sideLoad F orient 1 + rootReserve) ∨
    (Q ≤ sideLoad F orient 0 + rootReserve ∧
      Q ≤ sideLoad F orient 1 + rootReserve)

/-- Integral, rounding-safe form of the two numerical displays in Lemma
A.2.  `P ≤ X` records the source inclusion `P ⊆ X₁`; only this inclusion is
needed because `X ≤ Y` and the second display uses `min P Q`. -/
structure AppendixA2NumericData {b : ℕ} (F : OrderedRootedForest b)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N : ℝ) : Prop where
  component_lower : ∀ i, 2 ≤ F.size i
  component_upper : ∀ i, F.size i ≤ small
  X_le_Y : X ≤ Y
  P_le_X : P ≤ X
  rootReserve_le_P : rootReserve ≤ P
  rootReserve_le_Q : rootReserve ≤ Q
  rootReserve_le_sideReserve : rootReserve ≤ sideReserve
  root_slots : b + 2 * rootReserve ≤ P + Q
  side_slots : F.order + 2 * sideReserve + small ≤ Nat.min P Q + X
  root_rounding : 3 * epsilon * N ≤ rootReserve
  side_rounding : (gamma + 3 * epsilon) * N ≤ sideReserve

/-- The finite source certificate delivered to Corollary A.1. -/
structure AppendixA2Orientation {b : ℕ} (F : OrderedRootedForest b)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N : ℝ) : Type where
  orient : Fin b → Fin 2 ≃ Fin 2
  capacity : AppendixOneCapacity
    (sideLoad F orient 0) (sideLoad F orient 1)
    (rootLoad F orient 0) (rootLoad F orient 1)
    X Y P Q gamma epsilon N
  trichotomy : AppendixA2Trichotomy F orient X Y P Q rootReserve small

private theorem residual_dist_le
    {u v X Y small : ℕ}
    (huX : u ≤ X) (hvY : v ≤ Y) (hXY : X ≤ Y)
    (huv : u ≤ v) (hvu : v ≤ u + small) :
    natAbsDiff (X - u) (Y - v) ≤ max (natAbsDiff X Y) small := by
  have hXYabs : natAbsDiff X Y = Y - X := by
    simp [natAbsDiff, Nat.sub_eq_zero_of_le hXY]
  rw [hXYabs]
  have hleft : Y - X ≤ max (Y - X) small := Nat.le_max_left _ _
  have hright : small ≤ max (Y - X) small := Nat.le_max_right _ _
  by_cases hres : X - u ≤ Y - v
  · rw [show natAbsDiff (X - u) (Y - v) =
        (Y - v) - (X - u) by
      simp [natAbsDiff, Nat.sub_eq_zero_of_le hres]]
    omega
  · have hrev : Y - v ≤ X - u := by omega
    rw [show natAbsDiff (X - u) (Y - v) =
        (X - u) - (Y - v) by
      simp [natAbsDiff, Nat.sub_eq_zero_of_le hrev]]
    omega

private theorem appendix_capacity_of_nat
    {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (X Y P Q rootReserve sideReserve : ℕ)
    (gamma epsilon N : ℝ)
    (hside0 : sideLoad F orient 0 + sideReserve ≤ X)
    (hside1 : sideLoad F orient 1 + sideReserve ≤ Y)
    (hroot0 : rootLoad F orient 0 + rootReserve ≤ P)
    (hroot1 : rootLoad F orient 1 + rootReserve ≤ Q)
    (hrootRound : 3 * epsilon * N ≤ rootReserve)
    (hsideRound : (gamma + 3 * epsilon) * N ≤ sideReserve) :
    AppendixOneCapacity
      (sideLoad F orient 0) (sideLoad F orient 1)
      (rootLoad F orient 0) (rootLoad F orient 1)
      X Y P Q gamma epsilon N := by
  have hside0R : ((sideLoad F orient 0 + sideReserve : ℕ) : ℝ) ≤ X := by
    exact_mod_cast hside0
  have hside1R : ((sideLoad F orient 1 + sideReserve : ℕ) : ℝ) ≤ Y := by
    exact_mod_cast hside1
  have hroot0R : ((rootLoad F orient 0 + rootReserve : ℕ) : ℝ) ≤ P := by
    exact_mod_cast hroot0
  have hroot1R : ((rootLoad F orient 1 + rootReserve : ℕ) : ℝ) ≤ Q := by
    exact_mod_cast hroot1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> linarith

/-- Zhao Lemma A.2, in the integer-rounded form used by the formal
regularity hierarchy.  The theorem constructs the orientation and all three
conclusions; it has no graph, copy, embedding, or continuation premise. -/
theorem exists_appendixA2Orientation
    {b : ℕ} (F : OrderedRootedForest b)
    (small rootReserve sideReserve X Y P Q : ℕ)
    (gamma epsilon N : ℝ)
    (D : AppendixA2NumericData F small rootReserve sideReserve
      X Y P Q gamma epsilon N) :
    Nonempty (AppendixA2Orientation F small rootReserve sideReserve
      X Y P Q gamma epsilon N) := by
  classical
  have hloadTotal (orient : Fin b → Fin 2 ≃ Fin 2) :=
    sideLoad_zero_add_one F orient
  have hminP : Nat.min P Q ≤ P := Nat.min_le_left _ _
  have hminQ : Nat.min P Q ≤ Q := Nat.min_le_right _ _
  have hPX := D.P_le_X
  have hrootP := D.rootReserve_le_P
  have hrootQ := D.rootReserve_le_Q
  have hrootSide := D.rootReserve_le_sideReserve
  have hrootSlots := D.root_slots
  have hsideSlots := D.side_slots
  by_cases hP : P ≤ b + rootReserve
  · let r := P - rootReserve
    have hrb : r ≤ b := by omega
    obtain ⟨S, _hSuniv, hScard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin b)))
        (n := r)
        (by simpa using hrb)
    let orient := orientationForRootSet S
    have hroot0 : rootLoad F orient 0 + rootReserve ≤ P := by
      simp only [orient, rootLoad_orientationForRootSet_zero, hScard]
      omega
    have hroot1 : rootLoad F orient 1 + rootReserve ≤ Q := by
      simp only [orient, rootLoad_orientationForRootSet_one, hScard]
      omega
    have hload0b := components_le_sideLoad F orient 0 D.component_lower
    have hload1b := components_le_sideLoad F orient 1 D.component_lower
    have hside0 : sideLoad F orient 0 + sideReserve ≤ X := by
      have hsum := hloadTotal orient
      omega
    have hside1X : sideLoad F orient 1 + sideReserve ≤ X := by
      have hsum := hloadTotal orient
      omega
    have hside1 : sideLoad F orient 1 + sideReserve ≤ Y :=
      hside1X.trans D.X_le_Y
    refine ⟨{
      orient := orient
      capacity := appendix_capacity_of_nat F orient X Y P Q rootReserve
        sideReserve gamma epsilon N hside0 hside1 hroot0 hroot1
          D.root_rounding D.side_rounding
      trichotomy := ?_
    }⟩
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · have hbP : b + rootReserve ≤ P := by omega
    by_cases hQ : Q ≤ b + rootReserve
    · let q := Q - rootReserve
      have hqb : q ≤ b := by omega
      have hrb : b - q ≤ b := Nat.sub_le _ _
      obtain ⟨S, _hSuniv, hScard⟩ :=
        Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin b)))
          (n := b - q) (by
            change b - q ≤ #(Finset.univ : Finset (Fin b))
            simpa only [Finset.card_univ, Fintype.card_fin] using hrb)
      let orient := orientationForRootSet S
      have hroot0 : rootLoad F orient 0 + rootReserve ≤ P := by
        simp only [orient, rootLoad_orientationForRootSet_zero, hScard]
        omega
      have hroot1 : rootLoad F orient 1 + rootReserve ≤ Q := by
        simp only [orient, rootLoad_orientationForRootSet_one, hScard]
        omega
      have hload0b := components_le_sideLoad F orient 0 D.component_lower
      have hload1b := components_le_sideLoad F orient 1 D.component_lower
      have hside0 : sideLoad F orient 0 + sideReserve ≤ X := by
        have hsum := hloadTotal orient
        omega
      have hside1X : sideLoad F orient 1 + sideReserve ≤ X := by
        have hsum := hloadTotal orient
        omega
      have hside1 : sideLoad F orient 1 + sideReserve ≤ Y :=
        hside1X.trans D.X_le_Y
      refine ⟨{
        orient := orient
        capacity := appendix_capacity_of_nat F orient X Y P Q rootReserve
          sideReserve gamma epsilon N hside0 hside1 hroot0 hroot1
            D.root_rounding D.side_rounding
        trichotomy := ?_
      }⟩
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · have hbQ : b + rootReserve ≤ Q := by omega
      obtain ⟨orient, hordered, hbalanced⟩ :=
        exists_ordered_balanced_orientation F small D.component_upper
      have hroot0 : rootLoad F orient 0 + rootReserve ≤ P :=
        Nat.add_le_add_right (rootLoad_le_components F orient 0) _ |>.trans hbP
      have hroot1 : rootLoad F orient 1 + rootReserve ≤ Q :=
        Nat.add_le_add_right (rootLoad_le_components F orient 1) _ |>.trans hbQ
      have htwoload1 : 2 * sideLoad F orient 1 ≤ F.order + small := by
        have hsum := hloadTotal orient
        omega
      have hside1X : sideLoad F orient 1 + sideReserve ≤ X := by
        omega
      have hside0 : sideLoad F orient 0 + sideReserve ≤ X := by
        omega
      have hside1 : sideLoad F orient 1 + sideReserve ≤ Y :=
        hside1X.trans D.X_le_Y
      refine ⟨{
        orient := orient
        capacity := appendix_capacity_of_nat F orient X Y P Q rootReserve
          sideReserve gamma epsilon N hside0 hside1 hroot0 hroot1
            D.root_rounding D.side_rounding
        trichotomy := ?_
      }⟩
      exact Or.inl (residual_dist_le
        (by omega) (by omega)
        D.X_le_Y hordered hbalanced)

end Erdos547b.ZhaoLemma54AppendixA

#print axioms Erdos547b.ZhaoLemma54AppendixA.exists_appendixA2Orientation
