/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartTwoCapacity
import ErdosProblems.Erdos547b.SourceActualPartThreeStep

/-!
# Concrete capacities for threshold and Appendix source families

The ordinary case is the zero-ratio threshold kind. The Appendix kind
uses the conservative fresh capacity that pays permanent deletion before
the live-state loop. No embedding operation is part of this source data.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFamilyCapacity

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceActualPartTwoPlan
open Erdos547b.ZhaoSourcePartTwoCapacity Erdos547b.ZhaoLemma58ThresholdResidualCapacity

inductive FamilyKind where
  | threshold (ratio : ℝ)
  | appendix (lambda : ℝ)

def FamilyKind.Valid (α : ℚ) : FamilyKind → Prop
  | .threshold ratio => 0 ≤ ratio ∧ ratio ≤ 1 / 2
  | .appendix lambda => (densityCutoff α : ℝ) ≤ lambda ∧ lambda ≤ 1 / 2

def FamilyKind.BranchValid {b : ℕ} (kind : FamilyKind) (F : OrderedRootedForest b) (i : Fin b) : Prop :=
  match kind with
  | .threshold ratio => ratio ≤ (#(colourClass F i 0) : ℝ) / F.size i ∧
      (#(colourClass F i 0) : ℝ) / F.size i ≤ 1 - ratio
  | .appendix _ => 2 ≤ F.size i

/-- Every actual rooted branch belongs to the ordinary zero-ratio kind. -/
theorem ordinary_branchValid {b : ℕ} (F : OrderedRootedForest b) (i : Fin b) :
    FamilyKind.BranchValid (.threshold 0) F i := by
  have hsizeNat : 0 < F.size i := Nat.zero_lt_of_lt (F.root i).isLt
  have hsize : (0 : ℝ) < F.size i := by exact_mod_cast hsizeNat
  have hcard : #(colourClass F i 0) ≤ F.size i := by
    simpa only [colourClass, Finset.card_univ, Fintype.card_fin] using Finset.card_filter_le
      (Finset.univ : Finset (Fin (F.size i))) (fun a => (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hsize.le
  · rw [sub_zero, div_le_one hsize]
    exact_mod_cast hcard

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def capacity (S : CleanSourceWitness W Q) (C : Index W) (kind : FamilyKind)
    (e : MatchingEdge Q.claim67.M) : ℝ :=
  match kind with
  | .threshold ratio => partTwoCapacity W Q S C ratio e
  | .appendix lambda =>
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) +
        rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) + lambda -
        2 * (gamma α : ℝ) - 30 * (epsilon α : ℝ)) * W.clusterSize

def edgeValid (S : CleanSourceWitness W Q) (C : Index W) (kind : FamilyKind)
    (e : MatchingEdge Q.claim67.M) : Prop :=
  match kind with
  | .threshold _ => True
  | .appendix lambda => ∀ c,
      lambda ≤ rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ∧
      rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ≤ 1 - lambda

def initialTarget (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) (c : Fin 2) : Finset (Fin hostN) :=
  match kind with
  | .threshold _ => edgeWhole W Q e c
  | .appendix _ => residualSide (edgeWhole W Q e) (deleted W Q e) c

@[simp] theorem ordinary_capacity (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) : capacity W Q S C (.threshold 0) e = partOneCapacity W Q S C e := by
  simp only [capacity, partTwoCapacity, zero_div, zero_mul, add_zero]

/-- The same absolute bad-edge accounting applies to both concrete kinds. -/
theorem capacity_le_twice_clusterSize (hα : 0 < α)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (kind : FamilyKind) (hkind : kind.Valid α) (e : MatchingEdge Q.claim67.M)
    (he : edgeValid W Q S C kind e) : capacity W Q S C kind e ≤ 2 * W.clusterSize := by
  cases kind with
  | threshold ratio =>
      exact partTwoCapacity_le_twice_clusterSize W Q hα S C hC ratio hkind.1 hkind.2 e
  | appendix lambda =>
      have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.1
      have hlambda : 0 ≤ lambda := hd.le.trans hkind.1
      have hg : (0 : ℝ) < gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1
      have hε : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg W.clusterSize)
      linarith only [(he 0).2, (he 1).2, hlambda, hg, hε]

theorem initialTarget_subset (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    initialTarget W Q kind e c ⊆ edgeWhole W Q e c := by
  cases kind with
  | threshold _ => exact Finset.Subset.refl _
  | appendix _ => exact Finset.sdiff_subset

/-- Both kinds supply genuinely large initial incidence targets at the
existing source threshold, including the permanently cleaned Appendix pair. -/
theorem initialTarget_large (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    (epsilon α : ℝ) * W.clusterSize ≤ (initialTarget W Q kind e c).card := by
  subst hostN
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hγOne : gamma α ≤ 1 := by
    have hg := (parameter_upper_bounds hα hα1).2.2.2.2.2.1
    have hd := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
    linarith only [hg, hd]
  have hεOne : epsilon α ≤ 1 := by
    have heγ := (parameter_upper_bounds hα hα1).2.2.2.2.2.2
    linarith only [hγOne, heγ]
  cases kind with
  | threshold _ =>
      rw [initialTarget, edgeWhole_card]
      have hεOneR : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast hεOne
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hεOneR hN
  | appendix _ =>
      have hmargin := (degreeForm_fresh_chunk_gates hα hα1 W horder).2.2.1
      have hγN : (gamma α : ℝ) * W.clusterSize ≤ (W.clusterSize : ℝ) := by
        have hγOneR : (gamma α : ℝ) ≤ 1 := by exact_mod_cast hγOne
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hγOneR hN
      have hL : ((deleted W Q e c).card : ℝ) ≤ freshDeletionBudget α W.clusterSize := by
        exact_mod_cast card_deleted_le W Q hα hα1 e c
      have hsplit : ((residualSide (edgeWhole W Q e) (deleted W Q e) c).card : ℝ) +
          (deleted W Q e c).card = W.clusterSize := by
        exact_mod_cast (Finset.card_sdiff_add_card_eq_card (deleted_subset W Q e c)).trans (edgeWhole_card W Q e c)
      change (epsilon α : ℝ) * W.clusterSize ≤ (residualSide (edgeWhole W Q e) (deleted W Q e) c).card
      nlinarith only [hmargin, hγN, hL, hsplit, mul_nonneg he.le hN]

end Erdos547b.ZhaoSourceFamilyCapacity

#print axioms Erdos547b.ZhaoSourceFamilyCapacity.ordinary_branchValid
#print axioms Erdos547b.ZhaoSourceFamilyCapacity.capacity_le_twice_clusterSize
#print axioms Erdos547b.ZhaoSourceFamilyCapacity.initialTarget_large
