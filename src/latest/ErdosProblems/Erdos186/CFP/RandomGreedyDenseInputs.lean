/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomGreedyDenseWitness

/-!
# Concrete dense-box inputs from random greedy reserves

This file supplies the elementary post-random bridge which is independent of
the geometric DenseBox argument.  Integer subset sums embed injectively in
the one-dimensional lattice subset sums.  A common bound for the source
integers therefore gives a common symmetric box for every greedy reserve,
while a genuine first crossing gives the required lower density.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Integer subset sums embed in the lattice subset sums of the corresponding
one-dimensional integer points. -/
theorem integerPoints_subsetSums_subset_latticeSubsetSums
    (S : Finset ℤ) :
    Stability.integerPoints (Greedy.subsetSums S) ⊆
      GAP.subsetSums (Stability.integerPoints S) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
  obtain ⟨T, hTS, hsum⟩ :=
    SubsetSumGrowth.mem_weightedSubsetSums.mp
      (show z ∈ SubsetSumGrowth.weightedSubsetSums S id by
        simpa only [Greedy.subsetSums] using hz)
  apply GAP.mem_subsetSums_iff.mpr
  refine ⟨Stability.integerPoints T, Stability.integerPoints_mono hTS, ?_⟩
  rw [Stability.integerPoints, Finset.sum_image]
  · funext i
    simpa only [Stability.integerPoint_apply, Finset.sum_apply, id_eq] using hsum
  · intro a _ha b _hb hab
    exact Stability.integerPoint_injective hab

/-- Passing from integer greedy sums to lattice subset sums cannot decrease
cardinality. -/
theorem card_greedySums_le_card_latticeSubsetSums
    (S : Finset ℤ) (steps : ℕ) :
    (Greedy.sums S steps).card ≤
      (GAP.subsetSums
        (Stability.integerPoints (Greedy.selected S steps))).card := by
  rw [← Stability.card_integerPoints (Greedy.sums S steps)]
  exact Finset.card_le_card
    (integerPoints_subsetSums_subset_latticeSubsetSums
      (Greedy.selected S steps))

/-- If every summand is bounded by `sourceRadius`, every subset sum of at
most `steps` summands lies in the common symmetric interval of radius
`steps * sourceRadius`. -/
theorem subsetSums_integerPoints_subset_symmetricAxisBox
    {S : Finset ℤ} {steps sourceRadius : ℕ}
    (hcard : S.card ≤ steps)
    (hbound : ∀ z ∈ S, |z| ≤ (sourceRadius : ℤ)) :
    GAP.subsetSums (Stability.integerPoints S) ⊆
      (symmetricAxisBox (fun _ : Fin 1 ↦ steps * sourceRadius)).carrier := by
  intro x hx
  rw [mem_symmetricAxisBox_iff]
  intro i
  obtain ⟨T, hT, hsum⟩ := GAP.mem_subsetSums_iff.mp hx
  have hterm : ∀ y ∈ T, |y i| ≤ (sourceRadius : ℤ) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Stability.mem_integerPoints_iff.mp (hT hy)
    rw [← hzy, Stability.integerPoint_apply]
    exact hbound z hz
  calc
    |x i| = |∑ y ∈ T, y i| := by
      rw [← hsum]
      simp only [Finset.sum_apply]
    _ ≤ ∑ y ∈ T, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ T, (sourceRadius : ℤ) :=
      Finset.sum_le_sum fun y hy ↦ hterm y hy
    _ = (T.card : ℤ) * sourceRadius := by simp
    _ ≤ (S.card : ℤ) * sourceRadius := by
      have hTcard : T.card ≤ S.card := by
        simpa only [Stability.card_integerPoints] using Finset.card_le_card hT
      exact_mod_cast Nat.mul_le_mul_right sourceRadius hTcard
    _ ≤ (steps : ℤ) * sourceRadius := by
      exact_mod_cast Nat.mul_le_mul_right sourceRadius hcard
    _ = (steps * sourceRadius : ℕ) := by norm_num

/-- A strict first crossing before the end of a greedy run gives a lower
bound for the terminal lattice subset-sum cardinality. -/
theorem positiveDyadicThreshold_le_card_greedyLatticeSubsetSums
    {S : Finset ℤ} {deletionBudget steps level : ℕ}
    (hsteps : steps ≤ S.card)
    (hcross : Greedy.dyadicBinStart S deletionBudget steps level < steps) :
    Greedy.positiveDyadicThreshold S deletionBudget level ≤
      (GAP.subsetSums
        (Stability.integerPoints (Greedy.selected S steps))).card := by
  calc
    Greedy.positiveDyadicThreshold S deletionBudget level ≤
        (Greedy.sums S
          (Greedy.dyadicBinStart S deletionBudget steps level)).card :=
      Greedy.threshold_le_at_firstCrossing_of_lt hcross
    _ ≤ (Greedy.sums S steps).card :=
      Greedy.card_sums_mono hcross.le hsteps
    _ ≤ (GAP.subsetSums
          (Stability.integerPoints (Greedy.selected S steps))).card :=
      card_greedySums_le_card_latticeSubsetSums S steps

/-- The displayed one-dimensional symmetric box has its expected odd
length. -/
@[simp]
theorem volume_symmetricAxisBox_finOne (radius : ℕ) :
    (symmetricAxisBox (fun _ : Fin 1 ↦ radius)).volume = 2 * radius + 1 := by
  simp [AxisBox.volume, symmetricAxisBox]

/-! ## Density transport through generator completion -/

/-- Enlarging a selected reserve to a generator-completed reserve preserves
the lower subset-sum cardinality.  Thus a lower crossing for the selected
reserve supplies the exact DenseBox density input for the completed reserve
in any common ambient box. -/
theorem denseBoxInput_of_selected_subset_completed
    {d cNum cDen threshold : ℕ} {Q : AxisBox d}
    {selected completed : Finset (LatticePoint d)}
    (hselected : selected ⊆ completed)
    (hcontain : GAP.subsetSums completed ⊆ Q.carrier)
    (hlower : threshold ≤ (GAP.subsetSums selected).card)
    (hnumeric : cNum * Q.volume ≤ cDen * threshold) :
    GAP.subsetSums completed ⊆ Q.carrier ∧
      cNum * Q.volume ≤ cDen * (GAP.subsetSums completed).card := by
  refine ⟨hcontain, hnumeric.trans ?_⟩
  apply Nat.mul_le_mul_left
  exact hlower.trans (Finset.card_le_card (subsetSums_mono hselected))

/-- Family form of `denseBoxInput_of_selected_subset_completed`, matching
the family input consumed by DenseBox. -/
theorem denseBoxFamilyInputs_of_selected_subset_completed
    {d ell cNum cDen : ℕ} (Q : AxisBox d)
    (selected completed : Fin ell → Finset (LatticePoint d))
    (threshold : Fin ell → ℕ)
    (hselected : ∀ i, selected i ⊆ completed i)
    (hcontain : ∀ i, GAP.subsetSums (completed i) ⊆ Q.carrier)
    (hlower : ∀ i, threshold i ≤ (GAP.subsetSums (selected i)).card)
    (hnumeric : ∀ i, cNum * Q.volume ≤ cDen * threshold i) :
    (∀ i, GAP.subsetSums (completed i) ⊆ Q.carrier) ∧
      (∀ i, cNum * Q.volume ≤
        cDen * (GAP.subsetSums (completed i)).card) := by
  constructor
  · exact hcontain
  · intro i
    exact (denseBoxInput_of_selected_subset_completed
      (hselected i) (hcontain i) (hlower i) (hnumeric i)).2

/-- A first crossing for the literal greedy-selected reserve gives the
selected-cardinality input needed by the completion transport. -/
theorem greedySelectedSubsetSum_lower_of_firstCrossing
    {A : Finset ℤ} {q deletionBudget steps level : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hsteps : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) deletionBudget
        steps level < steps) :
    ∀ i, Greedy.positiveDyadicThreshold
        (integerColorClass A c i) deletionBudget level ≤
      (GAP.subsetSums (greedyColorReserve A c steps i)).card := by
  intro i
  simpa only [greedyColorReserve] using
    positiveDyadicThreshold_le_card_greedyLatticeSubsetSums
      (hsteps i) (hcross i)

/-- Exact completed-reserve density transport for the actual greedy random
color family.  The geometric construction may choose any common box `Q`;
all it must supply here is containment and the numerical comparison of that
box's volume with the true crossing threshold. -/
theorem greedyCompletedReserves_denseBoxInputs_of_firstCrossing
    {A : Finset ℤ} {q deletionBudget steps level cNum cDen : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (Q : AxisBox 1)
    (completed : Fin (q + 1) → Finset (LatticePoint 1))
    (hsteps : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) deletionBudget
        steps level < steps)
    (hselected : ∀ i, greedyColorReserve A c steps i ⊆ completed i)
    (hcontain : ∀ i, GAP.subsetSums (completed i) ⊆ Q.carrier)
    (hnumeric : ∀ i, cNum * Q.volume ≤
      cDen * Greedy.positiveDyadicThreshold
        (integerColorClass A c i) deletionBudget level) :
    (∀ i, GAP.subsetSums (completed i) ⊆ Q.carrier) ∧
      (∀ i, cNum * Q.volume ≤
        cDen * (GAP.subsetSums (completed i)).card) := by
  exact denseBoxFamilyInputs_of_selected_subset_completed Q
    (greedyColorReserve A c steps) completed
    (fun i ↦ Greedy.positiveDyadicThreshold
      (integerColorClass A c i) deletionBudget level)
    hselected hcontain
    (greedySelectedSubsetSum_lower_of_firstCrossing c hsteps hcross)
    hnumeric

/-- The actual random-color greedy reserves satisfy the two quantitative
DenseBox inputs once each color has a genuine crossing of the displayed
source threshold.  The ambient interval is common to all colors. -/
theorem greedyColorReserves_denseBoxInputs_of_firstCrossing
    {A : Finset ℤ} {q deletionBudget steps level sourceRadius cNum cDen : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hsteps : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hsourceBound : ∀ z ∈ A, |z| ≤ (sourceRadius : ℤ))
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) deletionBudget
        steps level < steps)
    (hnumeric : ∀ i,
      cNum * (2 * (steps * sourceRadius) + 1) ≤
        cDen * Greedy.positiveDyadicThreshold
          (integerColorClass A c i) deletionBudget level) :
    (∀ i, GAP.subsetSums (greedyColorReserve A c steps i) ⊆
      (symmetricAxisBox
        (fun _ : Fin 1 ↦ steps * sourceRadius)).carrier) ∧
    (∀ i, cNum *
        (symmetricAxisBox
          (fun _ : Fin 1 ↦ steps * sourceRadius)).volume ≤
      cDen * (GAP.subsetSums (greedyColorReserve A c steps i)).card) := by
  constructor
  · intro i
    simpa only [greedyColorReserve] using
      subsetSums_integerPoints_subset_symmetricAxisBox
        (S := Greedy.selected (integerColorClass A c i) steps)
        (steps := steps) (sourceRadius := sourceRadius)
        (by rw [Greedy.card_selected_eq (hsteps i)])
        (by
          intro z hz
          exact hsourceBound z (integerColorClass_subset A c i
            (Greedy.selected_subset (integerColorClass A c i) steps hz)))
  · intro i
    calc
      cNum *
          (symmetricAxisBox
            (fun _ : Fin 1 ↦ steps * sourceRadius)).volume =
          cNum * (2 * (steps * sourceRadius) + 1) := by
            rw [volume_symmetricAxisBox_finOne]
      _ ≤ cDen * Greedy.positiveDyadicThreshold
            (integerColorClass A c i) deletionBudget level := hnumeric i
      _ ≤ cDen *
          (GAP.subsetSums (greedyColorReserve A c steps i)).card := by
        apply Nat.mul_le_mul_left
        simpa only [greedyColorReserve] using
          positiveDyadicThreshold_le_card_greedyLatticeSubsetSums
            (hsteps i) (hcross i)

/-- Full post-random DenseBox input package.  In addition to the common-box
containment and density furnished by the first crossing, strong span
robustness makes every reserve generate the full one-dimensional lattice;
hence its subset-sum set is reduced.

The equation at dimension one is explicit because the random-partition
stability API is coordinate-parametric. -/
theorem greedyColorReserves_denseReducedBoxInputs_of_firstCrossing
    {A : Finset ℤ} {q deletionBudget steps level sourceRadius cNum cDen : ℕ}
    {maxRank differenceBound C0 : ℕ}
    {relevant : Finset ℕ} {box : (r : ℕ) → GAP 1 r}
    {φFamily : (r : ℕ) → ℤ → LatticePoint r}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hone : 1 ∈ relevant)
    (hstable : ∀ i, Stability.StronglyStableFor
      (anchoredColorClass A c i) box deletionBudget maxRank differenceBound
        relevant φFamily C0)
    (hnear : ∀ i, (integerColorClass A c i).card ≤
      steps + deletionBudget / C0)
    (hcoordinate : φFamily 1 = Stability.integerPoint)
    (htop : ∀ i, Stability.generatedSubgroup (φFamily 1)
      (anchoredColorClass A c i) = ⊤)
    (hsteps : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hsourceBound : ∀ z ∈ A, |z| ≤ (sourceRadius : ℤ))
    (hcross : ∀ i,
      Greedy.dyadicBinStart (integerColorClass A c i) deletionBudget
        steps level < steps)
    (hnumeric : ∀ i,
      cNum * (2 * (steps * sourceRadius) + 1) ≤
        cDen * Greedy.positiveDyadicThreshold
          (integerColorClass A c i) deletionBudget level) :
    (∀ i, GAP.subsetSums (greedyColorReserve A c steps i) ⊆
      (symmetricAxisBox
        (fun _ : Fin 1 ↦ steps * sourceRadius)).carrier) ∧
    (∀ i, cNum *
        (symmetricAxisBox
          (fun _ : Fin 1 ↦ steps * sourceRadius)).volume ≤
      cDen * (GAP.subsetSums (greedyColorReserve A c steps i)).card) ∧
    (∀ i, generatedSublattice (greedyColorReserve A c steps i) = ⊤) ∧
    (∀ i, Reduced (GAP.subsetSums (greedyColorReserve A c steps i))) := by
  obtain ⟨hcontain, hdense⟩ :=
    greedyColorReserves_denseBoxInputs_of_firstCrossing c hsteps hsourceBound
      hcross hnumeric
  have hgenerate : ∀ i,
      generatedSublattice (greedyColorReserve A c steps i) = ⊤ := by
    intro i
    have hgen := coordinateGreedyReserve_generates_of_stronglyStable
      c i hone (hstable i) (hsteps i) (hnear i)
      (by rw [hcoordinate]; funext j; rfl) (htop i)
    simpa only [coordinateGreedyReserve, greedyColorReserve,
      Stability.integerPoints, hcoordinate] using hgen
  exact ⟨hcontain, hdense, hgenerate,
    fun i ↦ reduced_subsetSums_of_generatedSublattice_eq_top (hgenerate i)⟩

end RandomPartition

end

end Erdos186.CFP
