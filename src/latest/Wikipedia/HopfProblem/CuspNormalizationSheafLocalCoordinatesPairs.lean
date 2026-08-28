import Wikipedia.HopfProblem.CuspNormalizationSheafCurves
import Wikipedia.HopfProblem.CuspNormalizationGermsChartFibre

/-!
# Double curves and pairs of active coordinate branches

An actual double curve in a normalization chart is the coordinate axis
opposite its two component planes. The source orientation specifies which
of these planes receives the positive lift and which receives the negative
lift. Restricting the resulting finite equivalence identifies exactly the
double curves through the point with the pairs of active planes.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan ToricSpace ToricComponent Triangle NormalizationCurves
open CuspNormalization.Germs

/-- The coordinate plane containing the source-positive lift. -/
def plusBranch (s : Triangle) (k : Fin 3) : Fin 3 :=
  if k = 2 then s.edgeEnd (sourceEdgeIndex k) else s.edgeStart (sourceEdgeIndex k)

/-- The coordinate plane containing the source-negative lift. -/
def minusBranch (s : Triangle) (k : Fin 3) : Fin 3 :=
  if k = 2 then s.edgeStart (sourceEdgeIndex k) else s.edgeEnd (sourceEdgeIndex k)

theorem plusBranch_ne_axisIndex (s : Triangle) (k : Fin 3) :
    plusBranch s k ≠ s.axisIndex (sourceEdgeIndex k) := by
  unfold plusBranch
  split_ifs
  · exact edgeEnd_ne_axisIndex s _
  · exact edgeStart_ne_axisIndex s _

theorem minusBranch_ne_axisIndex (s : Triangle) (k : Fin 3) :
    minusBranch s k ≠ s.axisIndex (sourceEdgeIndex k) := by
  unfold minusBranch
  split_ifs
  · exact edgeStart_ne_axisIndex s _
  · exact edgeEnd_ne_axisIndex s _

theorem plusBranch_ne_minusBranch (s : Triangle) (k : Fin 3) :
    plusBranch s k ≠ minusBranch s k := by
  cases hs : s.upper <;> fin_cases k <;>
    simp [plusBranch, minusBranch, sourceEdgeIndex, edgeStart, edgeEnd, hs]

/-- The unordered pair of component planes incident to a source double curve. -/
def sourcePair (s : Triangle) (k : Fin 3) : Finset (Fin 3) :=
  Finset.univ.erase (s.axisIndex (sourceEdgeIndex k))

@[simp] theorem mem_sourcePair (s : Triangle) (k j : Fin 3) :
    j ∈ sourcePair s k ↔ j ≠ s.axisIndex (sourceEdgeIndex k) := by
  simp [sourcePair]

theorem sourcePair_card (s : Triangle) (k : Fin 3) : (sourcePair s k).card = 2 := by
  simp [sourcePair]

theorem sourcePair_eq_branches (s : Triangle) (k : Fin 3) :
    sourcePair s k = {plusBranch s k, minusBranch s k} := by
  ext j
  rw [mem_sourcePair]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold plusBranch minusBranch
  split_ifs
  · exact (axis_complement s (sourceEdgeIndex k) j).trans or_comm
  · exact axis_complement s (sourceEdgeIndex k) j

theorem sourcePair_subset_active_iff (s : Triangle) (b : CoordinateSpace 3) (k : Fin 3) :
    sourcePair s k ⊆ activeBranches b ↔
      b (plusBranch s k) = 0 ∧ b (minusBranch s k) = 0 := by
  rw [sourcePair_eq_branches]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_activeBranches]

private def coordinatePair (j : Fin 3) : {p : Finset (Fin 3) // p.card = 2} :=
  ⟨Finset.univ.erase j, by simp⟩

private theorem coordinatePair_bijective : Function.Bijective coordinatePair := by decide

/-- The three source edge labels enumerate all actual pairs of chart planes. -/
def sourcePairEquiv (s : Triangle) : Fin 3 ≃ {p : Finset (Fin 3) // p.card = 2} :=
  (Equiv.ofBijective (fun k => s.axisIndex (sourceEdgeIndex k))
    ⟨s.axisIndex_injective.comp (by decide : Function.Injective sourceEdgeIndex),
      Finite.surjective_of_injective
        (s.axisIndex_injective.comp (by decide : Function.Injective sourceEdgeIndex))⟩).trans
    (Equiv.ofBijective coordinatePair coordinatePair_bijective)

@[simp] theorem sourcePairEquiv_apply (s : Triangle) (k : Fin 3) :
    (sourcePairEquiv s k).val = sourcePair s k := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

theorem mem_doubleCurve_normalizationChart_symm (b : CoordinateSpace 3)
    (hb : b ∈ (e).target) (i : Fin 3) :
    (e).symm b ∈ doubleCurve C ε hε i ↔
      ∀ j, j ≠ s.axisIndex i → b j = 0 := by
  rw [normalizationChart_symm]
  change quotientMap C ε ((normalizationTubeChart ε a s).symm b) ∈ _ ↔ _
  rw [mem_doubleCurve_quotientMap, normalizationTubeChart_symm_coe ε a s hb.1,
    branchVertices_inclusion, chartBranches_edge_axis]

theorem mem_sourceDoubleCurve_iff_pair_active (b : CoordinateSpace 3)
    (hb : b ∈ (e).target) (k : Fin 3) :
    (e).symm b ∈ sourceDoubleCurve C ε hε k ↔ sourcePair s k ⊆ activeBranches b := by
  rw [mem_doubleCurve_normalizationChart_symm C ε hε hε1 hC hR a s b hb]
  simp only [Finset.subset_iff, mem_sourcePair, mem_activeBranches]

theorem mem_sourceDoubleCurve_iff_branches_zero (b : CoordinateSpace 3)
    (hb : b ∈ (e).target) (k : Fin 3) :
    (e).symm b ∈ sourceDoubleCurve C ε hε k ↔
      b (plusBranch s k) = 0 ∧ b (minusBranch s k) = 0 := by
  rw [mem_sourceDoubleCurve_iff_pair_active C ε hε hε1 hC hR a s b hb,
    sourcePair_subset_active_iff]

/-- Exactly the actual double curves through the chart point correspond to
the two-element subsets of its active coordinate branches. -/
def activeCurvePairEquiv (b : CoordinateSpace 3) (hb : b ∈ (e).target) :
    {k : Fin 3 // (e).symm b ∈ sourceDoubleCurve C ε hε k} ≃
      {p : {p : Finset (Fin 3) // p.card = 2} // p.val ⊆ activeBranches b} :=
  (sourcePairEquiv s).subtypeEquiv fun k =>
    mem_sourceDoubleCurve_iff_pair_active C ε hε hε1 hC hR a s b hb k

@[simp] theorem activeCurvePairEquiv_apply (b : CoordinateSpace 3) (hb : b ∈ (e).target)
    (k : {k : Fin 3 // (e).symm b ∈ sourceDoubleCurve C ε hε k}) :
    (activeCurvePairEquiv C ε hε hε1 hC hR a s b hb k).val.val = sourcePair s k := rfl

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
