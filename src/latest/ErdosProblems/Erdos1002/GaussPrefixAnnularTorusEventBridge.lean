import ErdosProblems.Erdos1002.GaussPrefixAnnularCanonicalBoxBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact real/quotient bridge for annular torus cells

The literal Gauss-prefix count records its torus mark as the canonical
real representative in `[0,1)`, whereas the canonical marked measure
takes values in `ℝ/ℤ`.  This file proves the exact compatibility of the
two conventions.  In particular, no quotient-circle arc is silently
identified with a real interval.
-/

open Set

namespace Erdos1002

noncomputable section

/-- On the fundamental domain `[0,1)`, membership of the quotient-circle
arc belonging to a nonterminal grid cell is exactly membership of the
literal real half-open grid interval. -/
theorem coe_mem_unitAddCircle_intervalGridArc_iff
    {grid : ℕ} (hgrid : 0 < grid)
    (i : IntervalGridIndex grid) (hi : i.1 < grid)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    (x : UnitAddCircle) ∈
        unitAddCircleHalfOpenArc
          (intervalGridPoint 0 1 grid i.1)
          (intervalGridPoint 0 1 grid (i.1 + 1)) ↔
      x ∈ intervalGridCell 0 1 grid i := by
  have hleft :
      intervalGridPoint 0 1 grid i.1 ∈ Icc (0 : ℝ) 1 :=
    intervalGridPoint_mem_Icc zero_le_one hgrid (Nat.le_of_lt hi)
  have hright :
      intervalGridPoint 0 1 grid (i.1 + 1) ∈ Icc (0 : ℝ) 1 :=
    intervalGridPoint_mem_Icc zero_le_one hgrid (by omega)
  unfold intervalGridCell
  rw [if_pos hi]
  unfold unitAddCircleHalfOpenArc
  constructor
  · rintro ⟨y, hy, heq⟩
    have hyFund' : y ∈ Ico (0 : ℝ) 1 :=
      ⟨hleft.1.trans hy.1, hy.2.trans_le hright.2⟩
    have hyFund : y ∈ Ico (0 : ℝ) ((0 : ℝ) + 1) := by
      simpa only [zero_add] using! hyFund'
    have hxFund : x ∈ Ico (0 : ℝ) ((0 : ℝ) + 1) := by
      simpa only [zero_add] using! hx
    have hyx : y = x :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (a := (0 : ℝ)) hyFund hxFund).mp heq
    simpa only [hyx] using! hy
  · intro hxCell
    exact ⟨x, hxCell, rfl⟩

/-- Every selected Gauss-prefix torus mark is its canonical real
representative in `[0,1)`. -/
theorem gaussSelectedPrefixTorusMark_mem_Ico
    (N n : ℕ) (x : ℝ) :
    gaussSelectedPrefixTorusMark N n x ∈ Ico (0 : ℝ) 1 := by
  unfold gaussSelectedPrefixTorusMark gaussPrefixMarkedPoint
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Exact compatibility of chronological reindexing, the labeled torus
box in `(ℝ/ℤ)^r`, and the literal real torus cells.

The active-cell hypothesis is used only to exclude the terminal singleton
at `1`; the latter cannot contain a fractional-part mark and is handled
separately by the boundary assembly. -/
theorem
    annularOrderReindex_gaussMovingUnitTorusPoint_mem_box_iff_real_cells
    {grid N : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ)
    (x : ℝ) :
    annularOrderReindex e₀ e
          (gaussMovingUnitTorusPoint N times x) ∈
        unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e₀)
          (flattenedAnnularTorusUpper e₀) ↔
      ∀ j : Fin (MixedOccurrenceCount k),
        gaussSelectedPrefixTorusMark N (times j) x ∈
          intervalGridCell 0 1 grid (e j).1.torus := by
  have hreindex :
      annularOrderReindex e₀ e
            (gaussMovingUnitTorusPoint N times x) ∈
          unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀) ↔
        gaussMovingUnitTorusPoint N times x ∈
          unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e)
            (flattenedAnnularTorusUpper e) := by
    change
      gaussMovingUnitTorusPoint N times x ∈
          annularOrderReindex e₀ e ⁻¹'
            unitTorusHalfOpenBox
              (flattenedAnnularTorusLower e₀)
              (flattenedAnnularTorusUpper e₀) ↔ _
    rw [annularOrderReindex_preimage_flattenedAnnularTorusBox e₀ e]
  rw [hreindex]
  simp only [unitTorusHalfOpenBox, Set.mem_iInter,
    flattenedAnnularTorusLower,
    flattenedAnnularTorusUpper]
  constructor
  · intro hall j
    have hactive : 0 < k (e j).1 := by
      have hj := (e j).2.isLt
      omega
    exact
      (coe_mem_unitAddCircle_intervalGridArc_iff
        hgrid (e j).1.torus (htorus (e j).1 hactive)
        (gaussSelectedPrefixTorusMark_mem_Ico N (times j) x)).mp
        (hall j)
  · intro hall j
    have hactive : 0 < k (e j).1 := by
      have hj := (e j).2.isLt
      omega
    exact
      (coe_mem_unitAddCircle_intervalGridArc_iff
        hgrid (e j).1.torus (htorus (e j).1 hactive)
        (gaussSelectedPrefixTorusMark_mem_Ico N (times j) x)).mpr
        (hall j)

/-- Real-coordinate membership formula for the canonical signed-and-torus
tuple event.  This is the exact event used when comparing the canonical
finite measure with the literal mixed factorial expansion. -/
theorem mem_canonicalAnnularSignedTorusTupleEvent_iff_real_cells
    {ε A : ℝ} {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ)
    (x : ℝ) :
    x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e times ↔
      x ∈ gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        times ∧
      ∀ j : Fin (MixedOccurrenceCount k),
        gaussSelectedPrefixTorusMark N (times j) x ∈
          intervalGridCell 0 1 grid (e j).1.torus := by
  rw [mem_canonicalAnnularSignedTorusTupleEvent_iff]
  apply and_congr_right
  intro _hsigned
  constructor
  · intro hall j
    have hactive : 0 < k (e j).1 := by
      have hj := (e j).2.isLt
      omega
    exact
      (coe_mem_unitAddCircle_intervalGridArc_iff
        hgrid (e j).1.torus (htorus (e j).1 hactive)
        (gaussSelectedPrefixTorusMark_mem_Ico N (times j) x)).mp
        (hall j)
  · intro hall j
    have hactive : 0 < k (e j).1 := by
      have hj := (e j).2.isLt
      omega
    exact
      (coe_mem_unitAddCircle_intervalGridArc_iff
        hgrid (e j).1.torus (htorus (e j).1 hactive)
        (gaussSelectedPrefixTorusMark_mem_Ico N (times j) x)).mpr
        (hall j)

end

end Erdos1002
