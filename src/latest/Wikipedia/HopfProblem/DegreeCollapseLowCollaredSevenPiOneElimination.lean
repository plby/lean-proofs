import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneSuccessor
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarFundamentalGroupFinite
import Wikipedia.HopfProblem.FundamentalGroupSimplyConnected
import Mathlib.GroupTheory.Finiteness

/-!

# Finite native circle surgery eliminates a finitely generated fundamental group

The actual step kills the first chosen generator and is surjective, so
the images of the remaining generators generate the next actual half.
Induction constructs the whole finite surgery path. Every group is based
at the same specified boundary point in its preserved native collar.
Finite generation is an explicit input here; no assumption of a supplied
surgery sequence or initial simple connectivity is made.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

theorem closure_tail_of_surjective_killing_first {G H : Type*} [Group G] [Group H]
    {n : ℕ} (g : Fin (n + 1) → G) (hg : Subgroup.closure (range g) = ⊤)
    (φ : G →* H) (hφ : Surjective φ) (hk : φ (g 0) = 1) :
    Subgroup.closure (range (fun i : Fin n ↦ φ (g i.succ))) = ⊤ := by
  let K : Subgroup H := Subgroup.closure (range (fun i : Fin n ↦ φ (g i.succ)))
  have hall : ∀ i, φ (g i) ∈ K := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [hk]
      exact K.one_mem
    · exact Subgroup.subset_closure (mem_range_self j)
  have hle : Subgroup.closure (range g) ≤ K.comap φ := by
    apply (Subgroup.closure_le (K.comap φ)).mpr
    rintro y ⟨i, rfl⟩
    exact hall i
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨x, rfl⟩ := hφ y
  exact hle (by rw [hg]; trivial)

variable {B : Type} [TopologicalSpace B]

theorem exists_simplyConnected_of_generators (n : ℕ) (b : B) :
    ∀ S : LowCollaredSevenState B, PathConnectedSpace S.PositiveHalf →
      ∀ g : Fin n → FundamentalGroup S.PositiveHalf (S.positiveBasepoint b),
        Subgroup.closure (range g) = ⊤ →
          ∃ U : LowCollaredSevenState B, S.Reachable U ∧ SimplyConnectedSpace U.PositiveHalf := by
  induction n with
  | zero =>
    intro S hS g hg
    let := hS
    have hr : range g = ∅ := by ext x; simp
    have hz : (⊥ : Subgroup (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b))) = ⊤ := by
      simpa only [hr, Subgroup.closure_empty] using hg
    have hzero (x : FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)) : x = 1 := by
      have hx : x ∈ (⊥ : Subgroup (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b))) := by
        rw [hz]
        trivial
      simpa using hx
    let : Subsingleton (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)) :=
      ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
    exact ⟨S, Relation.ReflTransGen.refl,
      simplyConnectedSpace_of_fundamentalGroup_subsingleton (S.positiveBasepoint b)⟩
  | succ n ih =>
    intro S hS g hg
    let := hS
    obtain ⟨U, hSU, hU, φ, hφ, hk⟩ := S.exists_piOne_killing_step b (g 0)
    have hgen := closure_tail_of_surjective_killing_first g hg φ hφ hk
    obtain ⟨V, hUV, hV⟩ := ih U hU (fun i : Fin n ↦ φ (g i.succ)) hgen
    exact ⟨V, (Relation.ReflTransGen.single hSU).trans hUV, hV⟩

theorem exists_simplyConnected_of_finitelyGenerated (S : LowCollaredSevenState B)
    [PathConnectedSpace S.PositiveHalf] (b : B)
    [Group.FG (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b))] :
    ∃ U : LowCollaredSevenState B, S.Reachable U ∧ SimplyConnectedSpace U.PositiveHalf := by
  classical
  obtain ⟨K, hgen, hfin⟩ := Group.fg_iff.mp
    (inferInstance : Group.FG (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)))
  let : Fintype K := hfin.fintype
  let e := Fintype.equivFin K
  let g : Fin (Fintype.card K) → FundamentalGroup S.PositiveHalf (S.positiveBasepoint b) :=
    fun i ↦ (e.symm i).val
  have hr : range g = K := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  exact exists_simplyConnected_of_generators (Fintype.card K) b S inferInstance g
    (by rw [hr]; exact hgen)

theorem exists_simplyConnected_of_connected (S : LowCollaredSevenState B)
    [PathConnectedSpace S.Space] [SimplyConnectedSpace B] :
    ∃ U : LowCollaredSevenState B, S.Reachable U ∧ SimplyConnectedSpace U.PositiveHalf := by
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 7)) S.Space
  let : PathConnectedSpace S.PositiveHalf := S.collar.half_pathConnected
  let b : B := Classical.arbitrary _
  let : Group.FG (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)) :=
    S.collar.compact_half_fundamentalGroup_finite (EuclideanSpace ℝ (Fin 7)) _
  exact exists_simplyConnected_of_finitelyGenerated S b

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
