/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerForbiddenCertificate
import ErdosProblems.Erdos547b.Lemma58ThresholdResidualCapacity

/-!
# Combined residual bookkeeping for the dynamic Lemma 5.8 recursion

At one matching edge the live endpoint has three independent deletions:

1. the permanent removal from the whole regular-pair endpoint;
2. images of all previously embedded owner batches; and
3. the owner-specific cut-parent bad set.

This file packages their union as one literal deleted set.  Its residual is
definitionally the nested live set used by `Lemma58OwnerForbidden`, and its
cardinality is bounded by the sum of the three losses.  The final constructor
turns scalar bounds with that summed loss into the exact
`ResidualThresholdHostFacts` consumed by the checked threshold backend.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58CombinedResidual

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

universe v

/-- The exact used set on either endpoint is no larger than the total order
of the already embedded source components.  This deliberately forgets the
chosen orientations: the aggregate packing inequality can therefore pay for
completed owner batches before the next orientation has been chosen. -/
theorem card_chosenPartial_used_le_selectedOrder
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : Erdos547b.ZhaoLemma58ChosenOwnerBatches.ChosenPartialDynamicEmbedding
      F G externalParent available selected) (c : Fin 2) :
    #(E.used c) ≤ ∑ i ∈ selected, F.size i := by
  classical
  change #((Finset.univ : Finset {i // i ∈ selected}).biUnion
      (fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
        (F.root i.1) (E.orient i.1) G
        (E.state.forestCopy.componentCopy i.1 i.2) c)) ≤ _
  calc
    #((Finset.univ : Finset {i // i ∈ selected}).biUnion
        (fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
          (F.root i.1) (E.orient i.1) G
          (E.state.forestCopy.componentCopy i.1 i.2) c)) ≤
        ∑ i : {i // i ∈ selected},
          #(orientedCopyImage (F.tree i.1) (F.isTree i.1)
            (F.root i.1) (E.orient i.1) G
            (E.state.forestCopy.componentCopy i.1 i.2) c) := by
      simpa only [Finset.sum_const_zero, Finset.sum_attach,
        Finset.sum_filter] using
          (Finset.card_biUnion_le
            (s := (Finset.univ : Finset {i // i ∈ selected}))
            (t := fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
              (F.root i.1) (E.orient i.1) G
              (E.state.forestCopy.componentCopy i.1 i.2) c))
    _ ≤ ∑ i : {i // i ∈ selected}, F.size i.1 := by
      apply Finset.sum_le_sum
      intro i _
      rw [card_orientedCopyImage]
      calc
        #((Finset.univ : Finset (Fin (F.size i.1))).filter fun a ↦
            E.orient i.1
              ((F.isTree i.1).coloringTwoOfVert (F.root i.1) a) = c) ≤
            #(Finset.univ : Finset (Fin (F.size i.1))) :=
          Finset.card_filter_le _ _
        _ = F.size i.1 := by simp
    _ = ∑ i ∈ selected, F.size i := Finset.sum_attach selected F.size

/-- If a chosen partial state agrees pointwise with a fixed orientation on
all selected source coordinates, its actual used set on one endpoint is
bounded by the exact fixed oriented load of the selected components. -/
theorem card_chosenPartial_used_le_orientedLoad
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : Erdos547b.ZhaoLemma58ChosenOwnerBatches.ChosenPartialDynamicEmbedding
      F G externalParent available selected)
    (fixedOrient : Fin b → Fin 2 ≃ Fin 2)
    (hside : ∀ i (_hi : i ∈ selected) a,
      E.orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) =
        fixedOrient i ((F.isTree i).coloringTwoOfVert (F.root i) a))
    (c : Fin 2) :
    #(E.used c) ≤
      ∑ i ∈ selected, orientedClassSize F fixedOrient i c := by
  classical
  change #((Finset.univ : Finset {i // i ∈ selected}).biUnion
      (fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
        (F.root i.1) (E.orient i.1) G
        (E.state.forestCopy.componentCopy i.1 i.2) c)) ≤ _
  calc
    #((Finset.univ : Finset {i // i ∈ selected}).biUnion
        (fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
          (F.root i.1) (E.orient i.1) G
          (E.state.forestCopy.componentCopy i.1 i.2) c)) ≤
        ∑ i : {i // i ∈ selected},
          #(orientedCopyImage (F.tree i.1) (F.isTree i.1)
            (F.root i.1) (E.orient i.1) G
            (E.state.forestCopy.componentCopy i.1 i.2) c) := by
      simpa only [Finset.sum_const_zero, Finset.sum_attach,
        Finset.sum_filter] using
          (Finset.card_biUnion_le
            (s := (Finset.univ : Finset {i // i ∈ selected}))
            (t := fun i ↦ orientedCopyImage (F.tree i.1) (F.isTree i.1)
              (F.root i.1) (E.orient i.1) G
              (E.state.forestCopy.componentCopy i.1 i.2) c))
    _ = ∑ i : {i // i ∈ selected},
        orientedClassSize F fixedOrient i.1 c := by
      apply Finset.sum_congr rfl
      intro i _
      rw [card_orientedCopyImage, orientedClassSize]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hside i.1 i.2 a]
    _ = ∑ i ∈ selected, orientedClassSize F fixedOrient i c :=
      Finset.sum_attach selected (fun i ↦ orientedClassSize F fixedOrient i c)

/-- The permanent, prefix-image, and owner-bad deletions combined. -/
def combinedDeleted {B : Type v} [DecidableEq B]
    (whole available used bad : Fin 2 → Finset B) (c : Fin 2) : Finset B :=
  ((whole c \ available c) ∪ used c) ∪ bad c

theorem combinedDeleted_subset
    {B : Type v} [DecidableEq B]
    (whole available used bad : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hused : ∀ c, used c ⊆ available c)
    (hbad : ∀ c, bad c ⊆ available c)
    (c : Fin 2) : combinedDeleted whole available used bad c ⊆ whole c := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_sdiff.mp hx).1
    · exact havailable c (hused c hx)
  · exact havailable c (hbad c hx)

/-- Removing the combined deletion from the whole endpoint is exactly the
nested residual used by owner-specific cleaning. -/
theorem residualSide_combinedDeleted
    {B : Type v} [DecidableEq B]
    (whole available used bad : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (c : Fin 2) :
    residualSide whole (combinedDeleted whole available used bad) c =
      ownerCleanedLive (fun d ↦ available d \ used d) bad c := by
  ext x
  constructor
  · intro hx
    have hxResidual : x ∈ whole c \
        (((whole c \ available c) ∪ used c) ∪ bad c) := by
      exact hx
    have hxWhole := (Finset.mem_sdiff.mp hxResidual).1
    have hxNotDeleted := (Finset.mem_sdiff.mp hxResidual).2
    have hxNotBad : x ∉ bad c := by
      intro hxbad
      exact hxNotDeleted (Finset.mem_union_right _ hxbad)
    have hxNotFirst : x ∉ (whole c \ available c) ∪ used c := by
      intro hxfirst
      exact hxNotDeleted (Finset.mem_union_left _ hxfirst)
    have hxNotUsed : x ∉ used c := by
      intro hxused
      exact hxNotFirst (Finset.mem_union_right _ hxused)
    have hxNotPermanent : x ∉ whole c \ available c := by
      intro hxpermanent
      exact hxNotFirst (Finset.mem_union_left _ hxpermanent)
    have hxAvailable : x ∈ available c := by
      by_contra hx
      exact hxNotPermanent (Finset.mem_sdiff.mpr ⟨hxWhole, hx⟩)
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hxAvailable, hxNotUsed⟩, hxNotBad⟩
  · intro hx
    have hxClean := Finset.mem_sdiff.mp hx
    have hxAvailableUsed := Finset.mem_sdiff.mp hxClean.1
    have hxWhole := havailable c hxAvailableUsed.1
    apply Finset.mem_sdiff.mpr
    refine ⟨hxWhole, ?_⟩
    intro hxDeleted
    rcases Finset.mem_union.mp hxDeleted with hxFirst | hxBad
    · rcases Finset.mem_union.mp hxFirst with hxPermanent | hxUsed
      · exact (Finset.mem_sdiff.mp hxPermanent).2 hxAvailableUsed.1
      · exact hxAvailableUsed.2 hxUsed
    · exact hxClean.2 hxBad

/-- Union bound for the three literal losses. -/
theorem card_combinedDeleted_le
    {B : Type v} [DecidableEq B]
    (whole available used bad : Fin 2 → Finset B) (c : Fin 2) :
    #(combinedDeleted whole available used bad c) ≤
      #(whole c \ available c) + #(used c) + #(bad c) := by
  unfold combinedDeleted
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- A scalar bound on the three losses controls the exact combined deleted
cardinality. -/
theorem card_combinedDeleted_le_of_bounds
    {B : Type v} [DecidableEq B]
    (whole available used bad : Fin 2 → Finset B)
    (permanentBound usedBound badBound : Fin 2 → ℕ)
    (hpermanent : ∀ c, #(whole c \ available c) ≤ permanentBound c)
    (hused : ∀ c, #(used c) ≤ usedBound c)
    (hbad : ∀ c, #(bad c) ≤ badBound c)
    (c : Fin 2) :
    #(combinedDeleted whole available used bad c) ≤
      permanentBound c + usedBound c + badBound c := by
  exact (card_combinedDeleted_le whole available used bad c).trans
    (Nat.add_le_add (Nat.add_le_add (hpermanent c) (hused c)) (hbad c))

/-- Build the exact residual-threshold record from bounds using a common
upper loss.  `prefixLoad` remains the literal deleted cardinal; monotonicity
transfers the caller's scalar inequalities to that exact value. -/
noncomputable def residualThresholdHostFactsOfCombinedBounds
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.RegularPair.OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available used bad : Fin 2 → Finset B)
    (rho density : ℝ)
    (lowBudget highBudget : ℕ) (lowSide : Fin 2)
    (lossBound : Fin 2 → ℕ)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hfactor : 0 ≤ density - rho)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + highBudget + thresholdReserve rho #(whole c) ≤
        #(whole c))
    (heligible : ∀ i c,
      lossBound c +
          (1 + thresholdReserve rho #(whole c) +
            thresholdNeed lowBudget highBudget lowSide c) ≤
        #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c - highBudget)) :
    ResidualThresholdHostFacts F G externalParent whole
      (combinedDeleted whole available used bad) rho density lowBudget
      highBudget lowSide := by
  let exactLoss : Fin 2 → ℕ := fun c ↦
    #(combinedDeleted whole available used bad c)
  exact {
    prefixLoad := exactLoss
    deleted_subset := combinedDeleted_subset whole available used bad
      havailable husedSub hbadSub
    deleted_card := fun _ ↦ rfl
    total_capacity := by
      intro c
      calc
        exactLoss c + highBudget + thresholdReserve rho #(whole c) ≤
            lossBound c + highBudget + thresholdReserve rho #(whole c) := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (hloss c) highBudget) _
        _ ≤ #(whole c) := htotal c
    endpoint_eligible := by
      intro i c
      exact (Nat.add_le_add_right (hloss c) _).trans (heligible i c)
    component_capacity := by
      intro i c
      have hexact : (exactLoss c : ℝ) ≤ lossBound c := by
        exact_mod_cast hloss c
      calc
        (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
            (density - rho) *
              ((#(whole c) : ℝ) - lossBound c - highBudget) :=
          hcomponent i c
        _ ≤ (density - rho) *
              ((#(whole c) : ℝ) - exactLoss c - highBudget) := by
          gcongr
  }

/-- The combined-loss constructor in the exact type consumed by the
certified owner recursion.  This packages the source maximal-cutoff theorem,
the residual host estimates, and the definitional transport from one union
deletion to the nested live set. -/
noncomputable def thresholdOwnerLocalStepDataOfCombinedBounds
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available used bad : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + thresholdHighBudget dy gamma N +
          thresholdReserve rho #(whole c) ≤ #(whole c))
    (heligible : ∀ i c,
      lossBound c +
          (1 + thresholdReserve rho #(whole c) +
            thresholdNeed (thresholdLowBudget dx gamma N)
              (thresholdHighBudget dy gamma N) lowSide c) ≤
        #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c -
            thresholdHighBudget dy gamma N)) :
    OwnerLocalStepData F G externalParent whole
      (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density := by
  let Hhost := residualThresholdHostFactsOfCombinedBounds F G externalParent
    whole available used bad rho density
    (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
    lowSide lossBound havailable husedSub hbadSub hfactor hloss htotal
    heligible hcomponent
  let D := actualThresholdStepDataOfResidual F G externalParent whole
    (combinedDeleted whole available used bad) rho density ratio dx dy gamma
    epsilon N slack lowSide highSide Dsource hsides hunif hwholeDisjoint
    hdensity hfactor Hhost
  have hLive :
      residualSide whole (combinedDeleted whole available used bad) =
        ownerCleanedLive (fun c ↦ available c \ used c) bad := by
    funext c
    exact residualSide_combinedDeleted whole available used bad havailable c
  rw [← hLive]
  exact OwnerLocalStepData.threshold D

/-- Source-faithful combined-loss constructor for Zhao Lemma 5.4(1)/(2).
The parent-neighbour premise is asked only on the endpoint selected by the
literal prefix-balanced base and maximal-fitting cutoff.  In particular, a
zero low budget creates no spurious degree requirement into the low-density
endpoint. -/
noncomputable def thresholdOwnerLocalStepDataOfCanonicalCombinedBounds
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available used bad : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + thresholdHighBudget dy gamma N +
          thresholdReserve rho #(whole c) ≤ #(whole c))
    (heligible : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack),
      let O := actualThresholdSwitchOrientation F slack
        (thresholdLowBudget dx gamma N) (thresholdHighBudget dy gamma N)
        lowSide highSide Dsource.small hsides
        (Dsource.suffix_display highSide) base hbase
      ∀ i,
        let c := branchRootSide F O.orient i
        lossBound c +
            (1 + thresholdReserve rho #(whole c) +
              sideLoadBefore F O.orient i c) ≤
          #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c -
            thresholdHighBudget dy gamma N)) :
    OwnerLocalStepData F G externalParent whole
      (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density := by
  let deleted : Fin 2 → Finset B :=
    combinedDeleted whole available used bad
  let live : Fin 2 → Finset B := residualSide whole deleted
  let exactLoss : Fin 2 → ℕ := fun c ↦ #(deleted c)
  let D : ActualThresholdStepData F G externalParent whole live rho density :=
    { slack := slack
      lowBudget := thresholdLowBudget dx gamma N
      highBudget := thresholdHighBudget dy gamma N
      lowSide := lowSide
      highSide := highSide
      reserve := fun c ↦ thresholdReserve rho #(whole c)
      small := Dsource.small
      sides_ne := hsides
      suffix_display := Dsource.suffix_display highSide
      low_le_high := Dsource.lowBudget_le_highBudget
      uniform := hunif
      live_subset := residualSide_subset whole deleted
      whole_disjoint := hwholeDisjoint
      density_lower := hdensity
      factor_nonneg := hfactor
      reserve_regular := fun c ↦ thresholdReserve_covers rho #(whole c)
      live_capacity := by
        intro c
        have hdeleted : deleted c ⊆ whole c :=
          combinedDeleted_subset whole available used bad havailable
            husedSub hbadSub c
        have hcap : exactLoss c + thresholdHighBudget dy gamma N +
            thresholdReserve rho #(whole c) ≤ #(whole c) := by
          exact (Nat.add_le_add_right
            (Nat.add_le_add_right (hloss c)
              (thresholdHighBudget dy gamma N)) _).trans (htotal c)
        change thresholdHighBudget dy gamma N +
            thresholdReserve rho #(whole c) ≤ #(whole c \ deleted c)
        rw [Finset.card_sdiff_of_subset hdeleted]
        change thresholdHighBudget dy gamma N +
            thresholdReserve rho #(whole c) ≤ #(whole c) - exactLoss c
        omega
      parent_neighbours := by
        intro base hbase O i
        let c := branchRootSide F O.orient i
        have hwhole : exactLoss c +
            (1 + thresholdReserve rho #(whole c) +
              sideLoadBefore F O.orient i c) ≤
              #((whole c).filter (G.Adj (externalParent i))) := by
          exact (Nat.add_le_add_right (hloss c) _).trans
            (heligible base hbase i)
        exact residualSide_filter_card_ge_of_deleted_card_add_le
          G whole deleted (externalParent i) c
          (1 + thresholdReserve rho #(whole c) +
            sideLoadBefore F O.orient i c) hwhole
      component_margin := by
        intro i c
        have hdeleted : deleted c ⊆ whole c :=
          combinedDeleted_subset whole available used bad havailable
            husedSub hbadSub c
        have hlossWhole : lossBound c ≤ #(whole c) := by
          have := htotal c
          omega
        have hprefix : exactLoss c ≤ #(whole c) :=
          (hloss c).trans hlossWhole
        have hliveReal : (#(live c) : ℝ) =
            (#(whole c) : ℝ) - exactLoss c := by
          change (#(residualSide whole deleted c) : ℝ) = _
          rw [residualSide, Finset.card_sdiff_of_subset hdeleted,
            Nat.cast_sub hprefix]
        have hexact : (exactLoss c : ℝ) ≤ lossBound c := by
          exact_mod_cast hloss c
        rw [hliveReal]
        calc
          (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
              (density - rho) *
                ((#(whole c) : ℝ) - lossBound c -
                  thresholdHighBudget dy gamma N) := hcomponent i c
          _ ≤ (density - rho) *
                ((#(whole c) : ℝ) - exactLoss c -
                  thresholdHighBudget dy gamma N) := by
            gcongr }
  have hLive : live =
      ownerCleanedLive (fun c ↦ available c \ used c) bad := by
    funext c
    exact residualSide_combinedDeleted whole available used bad havailable c
  rw [← hLive]
  exact OwnerLocalStepData.threshold D

end Erdos547b.ZhaoLemma58CombinedResidual

#print axioms Erdos547b.ZhaoLemma58CombinedResidual.residualSide_combinedDeleted
#print axioms Erdos547b.ZhaoLemma58CombinedResidual.residualThresholdHostFactsOfCombinedBounds
#print axioms Erdos547b.ZhaoLemma58CombinedResidual.thresholdOwnerLocalStepDataOfCombinedBounds
#print axioms Erdos547b.ZhaoLemma58CombinedResidual.thresholdOwnerLocalStepDataOfCanonicalCombinedBounds
