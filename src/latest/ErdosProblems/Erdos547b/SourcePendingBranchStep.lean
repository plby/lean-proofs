/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshChunkEmbedding
import ErdosProblems.Erdos547b.Lemma58CombinedResidual
import ErdosProblems.Erdos547b.Lemma58OnlineOwnerReparent

/-!
# One genuine sequential branch step inside a pending pair

Only the current outer root is required to satisfy a degree inequality.
Earlier copies and the literal branch order are retained; no future root
images are assumed. Prefix occupancy, rather than the full endpoint load,
is subtracted from the current root's neighborhood.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingBranchStep

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest Erdos547b.ZhaoLemma51DynamicRegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58CombinedResidual Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
variable (parent : Fin b → V) (orient : Fin b → Fin 2 ≃ Fin 2)
variable (whole available : Fin 2 → Finset V)

omit [DecidableRel H.Adj] in
/-- The actual prefix image is bounded by the literal oriented prefix
load, without any re-enumeration of the selected branch indices. -/
theorem prefix_used_le (i : Fin b)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available (Finset.Iio i)) (c : Fin 2) :
    (E.used c).card ≤ sideLoadBefore F orient i c := by
  let chosen : ChosenPartialDynamicEmbedding F H parent available (Finset.Iio i) := ⟨orient, E⟩
  exact card_chosenPartial_used_le_orientedLoad chosen orient (fun _ _ _ => rfl) c

/-- Embed the next branch into the exact live pair. All degree information
concerns the current chosen root `z`, not a preassigned future root map. -/
theorem exists_next_branch_copy
    (reserve : Fin 2 → ℕ) (ρ d : ℝ) (i : Fin b)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available (Finset.Iio i))
    (z : V)
    (huniform : H.IsUniform ρ (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : d ≤ H.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ d - ρ)
    (hreserve : ∀ c, ρ * (whole c).card ≤ (reserve c : ℝ))
    (hcapacity : ∀ c, sideLoad F orient c + reserve c ≤ (available c).card)
    (hparent : 1 + reserve (branchRootSide F orient i) +
        sideLoadBefore F orient i (branchRootSide F orient i) ≤
      ((available (branchRootSide F orient i)).filter (H.Adj z)).card)
    (hmargin : ∀ c, (F.size i : ℝ) + ρ * (whole c).card + 1 ≤
      (d - ρ) * ((available c).card - (sideLoad F orient c : ℝ))) :
    ∃ f : (F.tree i).Copy H, H.Adj z (f (F.root i)) ∧
      ∀ a, f a ∈ (available (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))) \
        E.used (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) := by
  let live := fun c => available c \ E.used c
  have hused (c) := prefix_used_le F H parent orient available i E c
  have husedFinal (c) : (E.used c).card ≤ sideLoad F orient c :=
    (hused c).trans (sideLoadBefore_le_sideLoad F orient i c)
  have hcard (c) : (live c).card + (E.used c).card = (available c).card :=
    Finset.card_sdiff_add_card_eq_card (E.used_subset c)
  have hlarge (c) : ρ * (whole c).card ≤ ((live c).card : ℝ) := by
    have hn : reserve c ≤ (live c).card := by
      have hc := hcapacity c
      have hu := husedFinal c
      have hs := hcard c
      omega
    exact (hreserve c).trans (by exact_mod_cast hn)
  have hrootNat : 1 + reserve (branchRootSide F orient i) ≤
      ((live (branchRootSide F orient i)).filter (H.Adj z)).card := by
    apply residualSide_filter_card_ge_of_deleted_card_add_le H available E.used z
      (branchRootSide F orient i) (1 + reserve (branchRootSide F orient i))
    have hu := hused (branchRootSide F orient i)
    omega
  have hroot : (1 : ℝ) + ρ * (whole (orient i 0)).card ≤
      (((live (orient i 0)).filter (H.Adj z)).card : ℝ) := by
    have hn : (1 : ℝ) + reserve (orient i 0) ≤ (((live (orient i 0)).filter (H.Adj z)).card : ℝ) := by
      exact_mod_cast hrootNat
    linarith only [hn, hreserve (orient i 0)]
  have hbranch (c) : (Fintype.card (Fin (F.size i)) : ℝ) + ρ * (whole c).card + 1 ≤
      (d - ρ) * (live c).card := by
    have hc : ((live c).card : ℝ) + (E.used c).card = (available c).card := by exact_mod_cast hcard c
    have hu : ((E.used c).card : ℝ) ≤ sideLoad F orient c := by exact_mod_cast husedFinal c
    have hroom : ((available c).card : ℝ) - sideLoad F orient c ≤ (live c).card := by linarith only [hc, hu]
    simpa only [Fintype.card_fin] using
      (hmargin c).trans (mul_le_mul_of_nonneg_left hroom hfactor)
  exact exists_dynamic_rooted_tree_copy_of_uniform (F.tree i) (F.isTree i) (F.root i) H z
    (orient i) whole live ρ d huniform (fun c => Finset.sdiff_subset.trans (havailable c))
    hlarge hdensity hdisjoint hroot hbranch

private def singletonPartial (i : Fin b) (f : (F.tree i).Copy H)
    (hattach : H.Adj (parent i) (f (F.root i)))
    (hside : ∀ a, f a ∈ available (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))) :
    PartialDynamicAttachedForestEmbedding F H parent orient available {i} where
  forestCopy := {
    componentCopy := fun j hj => by
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      exact f
    disjoint_ranges := by
      intro j hj k hk hne
      have hji := Finset.mem_singleton.mp hj
      have hki := Finset.mem_singleton.mp hk
      exact False.elim (hne (hji.trans hki.symm)) }
  attach := by
    intro j hj
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact hattach
  map_side := by
    intro j hj a
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact hside a

/-- A sequential step changes only the new branch's outer-parent value,
and preserves all previously constructed branch copies exactly. -/
theorem exists_next_prefix
    (reserve : Fin 2 → ℕ) (ρ d : ℝ) (i : Fin b)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available (Finset.Iio i))
    (z : V)
    (huniform : H.IsUniform ρ (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : d ≤ H.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ d - ρ)
    (hreserve : ∀ c, ρ * (whole c).card ≤ (reserve c : ℝ))
    (hcapacity : ∀ c, sideLoad F orient c + reserve c ≤ (available c).card)
    (hparent : 1 + reserve (branchRootSide F orient i) +
        sideLoadBefore F orient i (branchRootSide F orient i) ≤
      ((available (branchRootSide F orient i)).filter (H.Adj z)).card)
    (hmargin : ∀ c, (F.size i : ℝ) + ρ * (whole c).card + 1 ≤
      (d - ρ) * ((available c).card - (sideLoad F orient c : ℝ))) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F H (Function.update parent i z) orient available
        (Finset.Iio i ∪ {i}),
      ∀ j hj, E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) =
        E.forestCopy.componentCopy j hj := by
  obtain ⟨f, hf, hside⟩ := exists_next_branch_copy F H parent orient whole available reserve ρ d i E z
    huniform havailable hdisjoint hdensity hfactor hreserve hcapacity hparent hmargin
  let parent' := Function.update parent i z
  have hagrees : ∀ j ∈ Finset.Iio i, parent' j = parent j := by
    intro j hj
    apply Function.update_of_ne
    exact ne_of_lt (Finset.mem_Iio.mp hj)
  let old := partialReparent F H parent parent' orient available (Finset.Iio i) E hagrees
  have hused (c) : old.used c = E.used c := rfl
  let one := singletonPartial F H parent' orient (fun c => available c \ old.used c) i f
    (by simpa only [parent', Function.update_self] using hf)
    (by intro a; simpa only [hused] using hside a)
  have hdisj : Disjoint (Finset.Iio i) ({i} : Finset (Fin b)) := by simp
  let out := appendPartial F H parent' orient whole available havailable hdisjoint
    (Finset.Iio i) {i} hdisj old one
  refine ⟨out, ?_⟩
  intro j hj
  simp only [out, appendPartial, dif_pos hj, old, partialReparent]

open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation

noncomputable abbrev thresholdSwitchOfData (ρ d : ℝ) (z : V)
    (D : ActualThresholdStepData F H (fun _ => z) whole available ρ d) :=
  canonicalActualThresholdSwitchOrientation F D.slack D.lowBudget D.highBudget
    D.lowSide D.highSide D.small D.sides_ne D.suffix_display

/-- The existing source threshold data supply the sequential step. Their
constant-root calculation is used only at the current branch; the actual
partial state's parent map is independent and may change later. -/
theorem exists_next_prefix_of_thresholdData
    (ρ d : ℝ) (i : Fin b) (z : V)
    (D : ActualThresholdStepData F H (fun _ => z) whole available ρ d)
    (E : PartialDynamicAttachedForestEmbedding F H parent
      (thresholdSwitchOfData F H whole available ρ d z D).orient available (Finset.Iio i)) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F H (Function.update parent i z)
        (thresholdSwitchOfData F H whole available ρ d z D).orient available (Finset.Iio i ∪ {i}),
      ∀ j hj, E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) =
        E.forestCopy.componentCopy j hj := by
  let O := thresholdSwitchOfData F H whole available ρ d z D
  refine exists_next_prefix F H parent O.orient whole available D.reserve ρ d i E z
    D.uniform D.live_subset D.whole_disjoint D.density_lower D.factor_nonneg D.reserve_regular ?_ ?_ ?_
  · intro c
    exact (Nat.add_le_add_right (O.final_load c) (D.reserve c)).trans (D.live_capacity c)
  · exact D.parent_neighbours (canonicalPrefixBalancedOrientation F D.slack D.small)
      (canonicalPrefixBalancedOrientation_spec F D.slack D.small) i
  · intro c
    have hload : (sideLoad F O.orient c : ℝ) ≤ D.highBudget := by exact_mod_cast O.final_load c
    exact (D.component_margin i c).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hload _) D.factor_nonneg)

end Erdos547b.ZhaoSourcePendingBranchStep

#print axioms Erdos547b.ZhaoSourcePendingBranchStep.prefix_used_le
#print axioms Erdos547b.ZhaoSourcePendingBranchStep.exists_next_branch_copy
#print axioms Erdos547b.ZhaoSourcePendingBranchStep.exists_next_prefix
#print axioms Erdos547b.ZhaoSourcePendingBranchStep.exists_next_prefix_of_thresholdData
