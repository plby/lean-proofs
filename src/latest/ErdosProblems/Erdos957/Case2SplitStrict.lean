import ErdosProblems.Erdos957.Case2SplitDegreeFive

noncomputable section

namespace Erdos957Case2SplitStrict

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957Case4SplitClassification
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- A degree-three source in a normalized two-extreme frame has a third
unit neighbour in the remaining outer sector.  We record only the scalar
consequence needed by the final split/split collision: after the incident
side is normalized to `uPrev` and the selected middle to `v`, that third
neighbour has first coordinate at least `1/2` and lies strictly below the
support line.

The proof deliberately uses only cardinality three, one-separation, and
the literal normalized coordinates.  Thus it is independent of the
private angular enumeration used to construct the middle neighbour. -/
lemma exists_third_source_neighbor_fst_ge_half
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    ∃ n : Vertex A,
      (unitDistanceGraph A).Adj (sourceIndex P W u hu).1 n ∧
      n ≠ cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side ∧
      n ≠ Q.middle ∧
      (1 / 2 : ℝ) ≤ (Q.normalized.frame.toCanonical n) 0 ∧
      (Q.normalized.frame.toCanonical n) 1 < 0 := by
  classical
  let source := sourceIndex P W u hu
  let side := cyclicSideVertex P source Q.twoExtreme.side
  let N := (unitDistanceGraph A).neighborFinset source.1
  have hcardN : N.card = 3 := by
    change ((unitDistanceGraph A).neighborFinset source.1).card = 3
    rw [← SimpleGraph.degree]
    exact (source_facts (P := P) (W := W) hu).2.2
  have hsideN : side ∈ N := by
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) side).mpr
      (by
        change dist (source.1 : Point) (side : Point) = 1
        exact Q.normalized.side_unit)
  have hmiddleN : Q.middle ∈ N := by
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) Q.middle).mpr
      (CommonPairedCase4Rows.source_adj_middle Q)
  have hnotSub : ¬ N ⊆ {side, Q.middle} := by
    intro hsub
    have hcardLe := Finset.card_le_card hsub
    have hsideNeMiddle : side ≠ Q.middle := by
      exact Q.twoExtreme.side_adjacent.ne.symm
    rw [hcardN] at hcardLe
    simp [hsideNeMiddle] at hcardLe
  rw [Finset.not_subset] at hnotSub
  obtain ⟨n, hnN, hnOutside⟩ := hnotSub
  have hnNeSide : n ≠ side := by
    have h : n ≠ side ∧ n ≠ Q.middle := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnOutside
    exact h.1
  have hnNeMiddle : n ≠ Q.middle := by
    have h : n ≠ side ∧ n ≠ Q.middle := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnOutside
    exact h.2
  have hnAdj : (unitDistanceGraph A).Adj source.1 n :=
    (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) n).mp hnN
  let z := Q.normalized.frame.toCanonical n
  have hsourceCoord : Q.normalized.frame.toCanonical source.1 =
      Erdos957Cases24.Case2.u := by
    rw [← Q.normalized.source_actual,
      Q.normalized.frame.toCanonical_actual]
  have hsideCoord : Q.normalized.frame.toCanonical side =
      Erdos957Cases24.Case2.uPrev := by
    rw [← Q.normalized.side_actual,
      Q.normalized.frame.toCanonical_actual]
  have hmiddleCoord : Q.normalized.frame.toCanonical Q.middle =
      Erdos957Cases24.Case2.v := by
    rw [← Q.normalized.middle_actual,
      Q.normalized.frame.toCanonical_actual]
  have hzMem : z ∈ Q.normalized.frame.image A := by
    exact Finset.mem_image.mpr ⟨n, n.property, rfl⟩
  have hzNeU : z ≠ Erdos957Cases24.Case2.u := by
    intro h
    have : n = source.1 := by
      apply Subtype.ext
      apply Q.normalized.frame.toCanonical.injective
      exact h.trans hsourceCoord.symm
    exact hnAdj.ne this.symm
  have hzNePrev : z ≠ Erdos957Cases24.Case2.uPrev := by
    intro h
    apply hnNeSide
    apply Subtype.ext
    apply Q.normalized.frame.toCanonical.injective
    exact h.trans hsideCoord.symm
  have hzBelow : z 1 < 0 := by
    apply Q.normalized.strict_support z hzMem
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      And.intro hzNePrev hzNeU
  have hnDist : dist (Q.normalized.frame.toCanonical source.1) z = 1 := by
    rw [Q.normalized.frame.dist_eq]
    exact hnAdj
  have hsideDist : 1 ≤ dist (Q.normalized.frame.toCanonical side) z := by
    rw [Q.normalized.frame.dist_eq]
    exact hA side side.property n n.property
      (fun h ↦ hnNeSide (Subtype.ext h.symm))
  have hmiddleDist : 1 ≤
      dist (Q.normalized.frame.toCanonical Q.middle) z := by
    rw [Q.normalized.frame.dist_eq]
    exact hA Q.middle Q.middle.property n n.property
      (fun h ↦ hnNeMiddle (Subtype.ext h.symm))
  have hnSq := Erdos957Cases24.dist_sq_eq_coordinates
    (Q.normalized.frame.toCanonical source.1) z
  have hsideSq := Erdos957Cases24.dist_sq_eq_coordinates
    (Q.normalized.frame.toCanonical side) z
  have hmiddleSq := Erdos957Cases24.dist_sq_eq_coordinates
    (Q.normalized.frame.toCanonical Q.middle) z
  rw [hnDist, hsourceCoord] at hnSq
  rw [hsideCoord] at hsideSq
  rw [hmiddleCoord] at hmiddleSq
  have hsideSqGe : 1 ≤ dist
      (Q.normalized.frame.toCanonical side) z ^ 2 := by
    nlinarith only [hsideDist,
      (dist_nonneg : 0 ≤ dist (Q.normalized.frame.toCanonical side) z)]
  have hmiddleSqGe : 1 ≤ dist
      (Q.normalized.frame.toCanonical Q.middle) z ^ 2 := by
    nlinarith only [hmiddleDist,
      (dist_nonneg : 0 ≤
        dist (Q.normalized.frame.toCanonical Q.middle) z)]
  rw [hsideCoord] at hsideSqGe
  rw [hmiddleCoord] at hmiddleSqGe
  simp only [Erdos957Cases24.Case2.u,
    Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow, sub_zero, zero_sub, neg_sq] at hnSq hsideSq hmiddleSq hsideSqGe hmiddleSqGe
  have hzNorm : z 0 ^ 2 + z 1 ^ 2 = 1 := by
    nlinarith only [hnSq]
  have hzLower : -(1 / 2 : ℝ) ≤ z 0 := by
    nlinarith only [hsideSq, hsideSqGe, hzNorm]
  have hzSlant : -1 ≤ z 0 + Erdos957Cases24.sqrtThree * z 1 := by
    nlinarith only [hmiddleSq, hmiddleSqGe, hzNorm,
      Erdos957Cases24.sqrtThree_sq]
  have hzFst : (1 / 2 : ℝ) ≤ z 0 := by
    by_contra hnot
    have hzLt : z 0 < 1 / 2 := lt_of_not_ge hnot
    have hzOnePos : 0 < 1 + z 0 := by linarith only [hzLower]
    have hsNonneg : 0 ≤ -Erdos957Cases24.sqrtThree * z 1 := by
      rw [neg_mul]
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos
          Erdos957Cases24.sqrtThree_pos.le hzBelow.le)
    have hsLe : -Erdos957Cases24.sqrtThree * z 1 ≤ 1 + z 0 := by
      linarith only [hzSlant]
    have hsSqLe :
        (-Erdos957Cases24.sqrtThree * z 1) ^ 2 ≤ (1 + z 0) ^ 2 :=
      (sq_le_sq₀ hsNonneg hzOnePos.le).2 hsLe
    nlinarith only [hsSqLe, hzNorm, hzLt, hzLower,
      Erdos957Cases24.sqrtThree_sq]
  exact ⟨n, hnAdj, hnNeSide, hnNeMiddle, hzFst, hzBelow⟩

/-- Pure coordinate core for the final split/split exclusion.  `S` is the
anchor source, `Q` is canonical `wNext`, and `B=(S+Q)/2` is the retained
Case-2 outer point, all expressed in the reflected frame of the first
Case-4 source.  Every unit vector in the remaining source-neighbour sector
lies strictly inside one of the unit disks about `S` or `B`. -/
lemma third_arc_close_to_source_or_outer
    {sx sy qx qy nx ny : ℝ}
    (hsx : (399 / 400 : ℝ) < sx)
    (hsy : sy < 0) (hshallow : -sy ≤ sx / 10)
    (hqxUpper : qx ≤ 0)
    (hqy : qy ≤ -Erdos957Cases24.sqrtThree)
    (hsq : (sx - qx) ^ 2 + (sy - qy) ^ 2 = 4)
    (hnorm : nx ^ 2 + ny ^ 2 = 1)
    (hnx : (1 / 2 : ℝ) ≤ nx) (hny : ny < 0) :
    (nx - sx) ^ 2 + (ny - sy) ^ 2 < 1 ∨
      (nx - (sx + qx) / 2) ^ 2 +
          (ny - (sy + qy) / 2) ^ 2 < 1 := by
  have hsqrtLower : (17 / 10 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith only [Erdos957Cases24.sqrtThree_sq,
      Erdos957Cases24.sqrtThree_pos,
      sq_nonneg (Erdos957Cases24.sqrtThree - 17 / 10)]
  have hsqrtUpper : Erdos957Cases24.sqrtThree < (7 / 4 : ℝ) := by
    nlinarith only [Erdos957Cases24.sqrtThree_sq,
      Erdos957Cases24.sqrtThree_pos,
      sq_nonneg (Erdos957Cases24.sqrtThree + 7 / 4)]
  have hsxPos : 0 < sx := by
    norm_num at hsx ⊢
    linarith only [hsx]
  have hdxPos : 0 < sx - qx := by linarith only [hsxPos, hqxUpper]
  have hdxSqLe : (sx - qx) ^ 2 ≤ 4 := by
    nlinarith only [hsq, sq_nonneg (sy - qy)]
  have hdxLe : sx - qx ≤ 2 := by
    nlinarith only [hdxSqLe, hdxPos, sq_nonneg (sx - qx + 2)]
  have hsxLeTwo : sx ≤ 2 := by linarith only [hqxUpper, hdxLe]
  have hdyLower : Erdos957Cases24.sqrtThree - sx / 10 ≤ sy - qy := by
    linarith only [hshallow, hqy]
  have hdyPos : 0 < sy - qy := by
    nlinarith only [hdyLower, hsxLeTwo, hsqrtLower]
  have hsxUpper : sx < (6 / 5 : ℝ) := by
    by_contra h
    have hsxGe : (6 / 5 : ℝ) ≤ sx := le_of_not_gt h
    have hsxSqLe : sx ^ 2 ≤ (sx - qx) ^ 2 :=
      (sq_le_sq₀ hsxPos.le hdxPos.le).2 (by linarith only [hqxUpper])
    have hlowPos : 0 < Erdos957Cases24.sqrtThree - sx / 10 := by
      nlinarith only [hsxLeTwo, hsqrtLower]
    have hlowSqLe : (Erdos957Cases24.sqrtThree - sx / 10) ^ 2 ≤
        (sy - qy) ^ 2 :=
      (sq_le_sq₀ hlowPos.le hdyPos.le).2 hdyLower
    have hbase : 4 <
        (6 / 5 : ℝ) ^ 2 +
          (Erdos957Cases24.sqrtThree - (6 / 5 : ℝ) / 10) ^ 2 := by
      nlinarith only [Erdos957Cases24.sqrtThree_sq, hsqrtUpper]
    have hfactor : 0 ≤
        (sx - 6 / 5) *
          ((101 / 100) * (sx + 6 / 5) -
            Erdos957Cases24.sqrtThree / 5) := by
      apply mul_nonneg
      · linarith only [hsxGe]
      · nlinarith only [hsxGe, hsqrtUpper]
    have hmono :
        (6 / 5 : ℝ) ^ 2 +
            (Erdos957Cases24.sqrtThree - (6 / 5 : ℝ) / 10) ^ 2 ≤
          sx ^ 2 + (Erdos957Cases24.sqrtThree - sx / 10) ^ 2 := by
      nlinarith only [hfactor]
    nlinarith only [hsq, hsxSqLe, hlowSqLe, hbase, hmono]
  have hsyLower : -(3 / 25 : ℝ) < sy := by
    nlinarith only [hshallow, hsxUpper]
  have hdyThreeHalves : (3 / 2 : ℝ) < sy - qy := by
    nlinarith only [hdyLower, hsxUpper, hsqrtLower]
  have hqxStrict : -(1 / 3 : ℝ) < qx := by
    by_contra h
    have hqxLe : qx ≤ -(1 / 3 : ℝ) := le_of_not_gt h
    have hdxLower : (53 / 40 : ℝ) < sx - qx := by
      nlinarith only [hsx, hqxLe]
    have hdxSq : (53 / 40 : ℝ) ^ 2 < (sx - qx) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdxPos.le).2 hdxLower
    have hdySq : (3 / 2 : ℝ) ^ 2 < (sy - qy) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdyPos.le).2 hdyThreeHalves
    nlinarith only [hsq, hdxSq, hdySq]
  have hdyUpper : sy - qy < (7 / 4 : ℝ) := by
    have hdxSq : (399 / 400 : ℝ) ^ 2 < (sx - qx) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdxPos.le).2
        (by linarith only [hsx, hqxUpper])
    have hdySq : (sy - qy) ^ 2 < (7 / 4 : ℝ) ^ 2 := by
      nlinarith only [hsq, hdxSq]
    exact (sq_lt_sq₀ hdyPos.le (by norm_num)).1 hdySq
  have hbxLower : (33 / 100 : ℝ) < (sx + qx) / 2 := by
    nlinarith only [hsx, hqxStrict]
  have hbxUpper : (sx + qx) / 2 < (3 / 5 : ℝ) := by
    nlinarith only [hsxUpper, hqxUpper]
  have hbyLower : -(1 : ℝ) < (sy + qy) / 2 := by
    have hqyEq : qy = sy - (sy - qy) := by ring
    rw [hqyEq]
    nlinarith only [hsyLower, hdyUpper]
  have hsqrtEightFifths : (8 / 5 : ℝ) <
      Erdos957Cases24.sqrtThree := by
    nlinarith only [Erdos957Cases24.sqrtThree_sq,
      Erdos957Cases24.sqrtThree_pos,
      sq_nonneg (Erdos957Cases24.sqrtThree - 8 / 5)]
  have hbyUpper : (sy + qy) / 2 < -(4 / 5 : ℝ) := by
    nlinarith only [hsy, hqy, hsqrtEightFifths]
  have hnxPos : 0 < nx := by nlinarith only [hnx]
  have hnxUpper : nx ≤ 1 := by
    have : nx ^ 2 ≤ 1 := by nlinarith only [hnorm, sq_nonneg ny]
    nlinarith only [this, hnxPos, sq_nonneg (nx + 1)]
  have hnyLower : -(9 / 10 : ℝ) < ny := by
    by_contra h
    have hnyLe : ny ≤ -(9 / 10 : ℝ) := le_of_not_gt h
    nlinarith only [hnorm, hnx, hnyLe,
      mul_nonneg (sub_nonneg.mpr hnx)
        (by linarith only [hnx] : 0 ≤ nx + 1 / 2),
      mul_nonneg (by linarith only [hnyLe] : 0 ≤ -ny - 9 / 10)
        (by linarith only [hnyLe] : 0 ≤ -ny + 9 / 10)]
  by_cases hnyHalf : -(1 / 2 : ℝ) ≤ ny
  · left
    have hxLo : -(7 / 10 : ℝ) < nx - sx := by
      nlinarith only [hnx, hsxUpper]
    have hxHi : nx - sx < (7 / 10 : ℝ) := by
      nlinarith only [hnxUpper, hsx]
    have hyLo : -(1 / 2 : ℝ) < ny - sy := by
      nlinarith only [hnyHalf, hsy]
    have hyHi : ny - sy < (1 / 2 : ℝ) := by
      nlinarith only [hny, hsyLower]
    have hxProd : 0 <
        ((7 / 10 : ℝ) - (nx - sx)) * ((7 / 10 : ℝ) + (nx - sx)) :=
      mul_pos (by linarith only [hxHi]) (by linarith only [hxLo])
    have hyProd : 0 <
        ((1 / 2 : ℝ) - (ny - sy)) * ((1 / 2 : ℝ) + (ny - sy)) :=
      mul_pos (by linarith only [hyHi]) (by linarith only [hyLo])
    nlinarith only [hxProd, hyProd]
  · right
    have hnyUpper : ny < -(1 / 2 : ℝ) := lt_of_not_ge hnyHalf
    have hxLo : -(67 / 100 : ℝ) < nx - (sx + qx) / 2 := by
      nlinarith only [hnx, hbxUpper]
    have hxHi : nx - (sx + qx) / 2 < (67 / 100 : ℝ) := by
      nlinarith only [hnxUpper, hbxLower]
    have hyLo : -(1 / 2 : ℝ) < ny - (sy + qy) / 2 := by
      nlinarith only [hnyLower, hbyUpper]
    have hyHi : ny - (sy + qy) / 2 < (1 / 2 : ℝ) := by
      nlinarith only [hnyUpper, hbyLower]
    have hxProd : 0 <
        ((67 / 100 : ℝ) - (nx - (sx + qx) / 2)) *
          ((67 / 100 : ℝ) + (nx - (sx + qx) / 2)) :=
      mul_pos (by linarith only [hxHi]) (by linarith only [hxLo])
    have hyProd : 0 <
        ((1 / 2 : ℝ) - (ny - (sy + qy) / 2)) *
          ((1 / 2 : ℝ) + (ny - (sy + qy) / 2)) :=
      mul_pos (by linarith only [hyHi]) (by linarith only [hyLo])
    nlinarith only [hxProd, hyProd]

/-- In a five-point unit neighbourhood with the canonical adjacent source
pair, the paper's farthest-below residual reaches at least the lower
`60°` latitude.  The horizontal interval `[-1,0]` puts its centered first
coordinate in `[-1/2,1/2]`; the unit-circle equation and the lower-sector
sign then force its absolute second coordinate below `-√3`. -/
lemma farthestBelowData_snd_le_neg_sqrtThree
    {B : Finset Point} (hB : Erdos957Cases24.IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData B) :
    D.point 1 ≤ -Erdos957Cases24.sqrtThree := by
  have hx := Erdos957Case4SplitClassification.farthestBelowData_fst_mem_source_interval
    hB huPrev hu hdegree D
  have hy := Erdos957Case4SplitClassification.residual_centered_snd_nonpos
    hB huPrev hu D.point_mem
  have hdist :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp D.point_mem).2.1
  have hsq := congrArg (fun r : ℝ ↦ r ^ 2) hdist
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsq
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hsq hy ⊢
  have hxSq : (D.point 0 + 1 / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith only [hx.1, hx.2,
      mul_nonneg (sub_nonneg.mpr hx.2)
        (by linarith only [hx.1] : 0 ≤ D.point 0 + 1)]
  have hySq : (Erdos957Cases24.sqrtThree / 2) ^ 2 ≤
      (D.point 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 := by
    nlinarith only [hsq, hxSq, Erdos957Cases24.sqrtThree_sq]
  nlinarith only [hy, hySq, Erdos957Cases24.sqrtThree_pos,
    Erdos957Cases24.sqrtThree_sq]

/-- A coherent low Case-4 branch pulls the sharp farthest-below latitude
back to its actual selected secondary target.  This is the source-free half
of the final strict-turn contradiction; it applies to either endpoint of the
common hull edge. -/
lemma CommonPairedCase4Rows.currentSecondary_common_snd_le_neg_sqrtThree_of_low
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    {hlow : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Q.pairBranch.farthest.point ≤ 5}
    (hbranch : Q.pairBranch.branch =
      Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) :
    (Q.commonFrame.frame.toCanonical
      Q.currentSecondaryTarget.vertex) 1 ≤
        -Erdos957Cases24.sqrtThree := by
  have huPrevA : Erdos957Cases24.Case2.uPrev ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
  have huA : Erdos957Cases24.Case2.u ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
  have hvDegree : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Erdos957Cases24.Case4.v = 5 := by
    rw [Q.commonFrame.frame.unitDegree_image_actual A,
      Erdos957Cases24.Case4.v, Q.commonFrame.middle_actual]
    rw [← ActualCase24Rows.graph_degree_eq_unitDegree]
    exact Q.middle_degree_five
  have hfar := farthestBelowData_snd_le_neg_sqrtThree
    (Q.commonFrame.frame.image_oneSeparated hA) huPrevA huA hvDegree
      Q.pairBranch.farthest
  have hcanonical : Q.commonFrame.frame.toCanonical
      Q.currentSecondaryTarget.vertex = Q.pairBranch.farthest.point := by
    rw [Q.current_secondary_vertex]
    change Q.commonFrame.frame.toCanonical
      (Q.commonFrame.frame.actual
        (Q.pairBranch.branch.sourceRecipient
          (ActualCase24Rows.case4SourceIsRight Q.twoExtreme))) = _
    rw [Q.commonFrame.frame.toCanonical_actual]
    simp [hbranch]
  rw [hcanonical]
  exact hfar

/-- Scalar strict-height kernel for the final produced turn.  The anchor
and outgoing terminal charts both reverse orientation, so the outgoing
chart height of canonical `wNext` is the displayed expression.  Diameter
control puts the two longitudinal components at most one, while the strict
turn forces the outgoing transverse component to be negative. -/
lemma wNext_outgoing_snd_gt_neg_sqrtThree
    {a b c d : ℝ}
    (ha : 0 < a) (haOne : a ≤ 1)
    (hb : b < 0)
    (hc : 0 < c) (hcOne : c ≤ 1)
    (hturn : a * d - b * c < 0) :
    -Erdos957Cases24.sqrtThree <
      c * (-Erdos957Cases24.sqrtThree - b - d) -
        d * (1 - a - c) := by
  have hbc : b * c < 0 := mul_neg_of_neg_of_pos hb hc
  have had : a * d < b * c := by linarith only [hturn]
  have hadNeg : a * d < 0 := had.trans hbc
  have hd : d < 0 := by
    rcases mul_neg_iff.mp hadNeg with h | h
    · exact h.2
    · exact (not_lt_of_ge ha.le h.1).elim
  have h₁ : 0 ≤ Erdos957Cases24.sqrtThree * (1 - c) :=
    mul_nonneg Erdos957Cases24.sqrtThree_pos.le (sub_nonneg.mpr hcOne)
  have h₂ : 0 ≤ d * (a - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hd.le (sub_nonpos.mpr haOne)
  have h₃ : 0 < -(b * c) := neg_pos.mpr hbc
  nlinarith only [h₁, h₂, h₃]

/-- A common unit neighbor of an almost-horizontal unit edge whose first
endpoint is already to the right of `399/400` has anchor-frame first
coordinate strictly larger than one. -/
private lemma common_unit_neighbor_fst_gt_one_of_flat_second_edge
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {a b m : Vertex A}
    (ha : (399 / 400 : ℝ) < (E.toCanonical a) 0)
    (habx : (399 / 400 : ℝ) <
      (E.toCanonical b) 0 - (E.toCanonical a) 0)
    (hab : (unitDistanceGraph A).Adj a b)
    (ham : (unitDistanceGraph A).Adj a m)
    (hbm : (unitDistanceGraph A).Adj b m) :
    1 < (E.toCanonical m) 0 := by
  let dx := (E.toCanonical b) 0 - (E.toCanonical a) 0
  let dy := (E.toCanonical b) 1 - (E.toCanonical a) 1
  let ex := (E.toCanonical m) 0 - (E.toCanonical a) 0
  let ey := (E.toCanonical m) 1 - (E.toCanonical a) 1
  have habDist : dist (E.toCanonical a) (E.toCanonical b) = 1 := by
    rw [E.dist_eq]
    exact hab
  have hamDist : dist (E.toCanonical a) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact ham
  have hbmDist : dist (E.toCanonical b) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact hbm
  have habSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical b)
  have hamSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical m)
  have hbmSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical b) (E.toCanonical m)
  rw [habDist] at habSq
  rw [hamDist] at hamSq
  rw [hbmDist] at hbmSq
  norm_num at habSq hamSq hbmSq
  have hedge : dx ^ 2 + dy ^ 2 = 1 := by
    dsimp [dx, dy]
    nlinarith only [habSq]
  have hmiddle : ex ^ 2 + ey ^ 2 = 1 := by
    dsimp [ex, ey]
    nlinarith only [hamSq]
  have hother : (ex - dx) ^ 2 + (ey - dy) ^ 2 = 1 := by
    dsimp [dx, dy, ex, ey]
    nlinarith only [hbmSq]
  have hdot : dx * ex + dy * ey = 1 / 2 := by
    nlinarith only [hedge, hmiddle, hother]
  have hdx : (399 / 400 : ℝ) < dx := by
    simpa only [dx] using habx
  have hdxpos : 0 < dx := by
    norm_num at hdx ⊢
    linarith only [hdx]
  have hdxSq : (399 / 400 : ℝ) ^ 2 < dx ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hdxpos.le).2 hdx
  have hdySq : dy ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    norm_num at hdxSq ⊢
    nlinarith only [hedge, hdxSq]
  have heySq : ey ^ 2 ≤ 1 := by
    nlinarith only [hmiddle, sq_nonneg ex]
  have hprodSq : (dy * ey) ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    calc
      (dy * ey) ^ 2 = dy ^ 2 * ey ^ 2 := by ring
      _ ≤ dy ^ 2 := by
        simpa only [mul_comm] using
          (mul_le_of_le_one_left (sq_nonneg dy) heySq)
      _ < (1 / 10 : ℝ) ^ 2 := hdySq
  have hprodAbsSq : |dy * ey| ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    simpa only [sq_abs] using hprodSq
  have hprodAbs : |dy * ey| < (1 / 10 : ℝ) :=
    (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).1 hprodAbsSq
  have hprodUpper : dy * ey < (1 / 10 : ℝ) := (abs_lt.mp hprodAbs).2
  have hdex : (2 / 5 : ℝ) < dx * ex := by
    nlinarith only [hdot, hprodUpper]
  have hdxSqLe : dx ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith only [hedge, sq_nonneg dy]
  have hdxLe : dx ≤ 1 :=
    (sq_le_sq₀ hdxpos.le (by norm_num)).1 hdxSqLe
  have hdexPos : 0 < dx * ex := by
    norm_num at hdex ⊢
    linarith only [hdex]
  have hexpos : 0 < ex := by
    rcases mul_pos_iff.mp hdexPos with h | h
    · exact h.2
    · exact (not_lt_of_ge hdxpos.le h.1).elim
  have hdexLe : dx * ex ≤ ex := by
    simpa only [mul_comm] using
      (mul_le_of_le_one_left hexpos.le hdxLe)
  dsimp [ex] at hexpos hdexLe ⊢
  linarith only [ha, hdex, hdexLe]

/-- The mixed `(incident, away-first)` source pattern cannot occur at a
degree-five Case-2 target.  The incident Case-2 row forces target `w`; the
away-first split row necessarily selects the outward hull edge, whose
equilateral middle lies strictly to the right of `x=1`, too far to be a
unit neighbor of `w`. -/
theorem no_case2_incident_case4_away_first_at_degree_five
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htIndex :
      let B := Classical.choice
        (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
      sourceIndex P W t.1 t.property =
        Erdos957Case2SecondaryNoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0)
    (huIndex :
      let B := Classical.choice
        (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0) : False := by
  let B := Classical.choice
    (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
  let E := Classical.choice
    (nonempty_case2SecondaryArrivalFormula T.target T.descriptor htRole)
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have hw :=
    Erdos957Case2SplitDegreeFive.target_eq_w_of_case2Secondary_at_incident_of_degree_five
      hA B.formula E.formula hdegree htIndex
  have hsideNe :=
    Erdos957Case2SplitDegreeFive.case4SplitRight_side_ne_case2_side_at_away_first
      Q S U hsRole huRole B Qu huIndex
  change sourceIndex P W u.1 u.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) B.formula.side 0 at huIndex
  have huEndpoint : cyclicSideVertex P
      (sourceIndex P W u.1 u.property) Qu.twoExtreme.side =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1 := by
    apply Subtype.ext
    have huValue := congrArg Subtype.val huIndex
    cases hB : B.formula.side <;>
      cases hQ : Qu.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        cyclicSideVertex, pow_succ]
  have ha := (Case2SecondaryFormula.away_prefix_bounds B.formula F
    (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0).2.1
  have habx := Case2SecondaryFormula.away_second_increment_gt B.formula F
    (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hab : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1
      (cyclicSideVertex P (sourceIndex P W u.1 u.property)
        Qu.twoExtreme.side) := by
    change dist ((sourceIndex P W u.1 u.property).1 : Point)
      (cyclicSideVertex P (sourceIndex P W u.1 u.property)
        Qu.twoExtreme.side : Point) = 1
    exact Qu.normalized.side_unit
  have ham :=
    Erdos957Case4SplitClassification.CommonPairedCase4Rows.source_adj_middle Qu
  have hbm := Qu.twoExtreme.side_adjacent.symm
  have hmX : 1 < (B.formula.edgeFrame.toCanonical Qu.middle) 0 := by
    apply common_unit_neighbor_fst_gt_one_of_flat_second_edge
      B.formula.edgeFrame
      (a := (sourceIndex P W u.1 u.property).1)
      (b := (cyclicSideVertex P (sourceIndex P W u.1 u.property)
        Qu.twoExtreme.side))
      (m := Qu.middle)
    · rw [huIndex]
      norm_num at ha
      exact ha
    · rw [huEndpoint, huIndex]
      exact habx
    · exact hab
    · exact ham
    · exact hbm
  have htarget : U.target.target = Qu.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← U.target.target_at_role, huRole, Qu.current_secondary_role]
  have hvSecondary : Qu.currentSecondaryTarget.vertex = v := by
    calc
      Qu.currentSecondaryTarget.vertex = U.target.target.vertex :=
        congrArg LocalTarget.vertex htarget.symm
      _ = v := U.target.vertex_eq.symm
  have hmTarget :=
    Erdos957Case4SplitClassification.CommonPairedCase4Rows.middle_adj_currentSecondary Qu
  have hdist : dist (B.formula.edgeFrame.toCanonical Qu.middle)
      Erdos957Cases24.Case2.w = 1 := by
    calc
      _ = dist (B.formula.edgeFrame.toCanonical Qu.middle)
          (B.formula.edgeFrame.toCanonical v) := by rw [hw]
      _ = dist (Qu.middle : Point) (v : Point) :=
        B.formula.edgeFrame.dist_eq _ _
      _ = 1 := by
        rw [← hvSecondary]
        exact hmTarget
  have hsq := Erdos957Cases24.dist_sq_eq_coordinates
    (B.formula.edgeFrame.toCanonical Qu.middle)
    Erdos957Cases24.Case2.w
  rw [hdist] at hsq
  simp only [Erdos957Cases24.Case2.w,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow, sub_zero,
    sub_neg_eq_add] at hsq
  nlinarith only [hsq, hmX,
    sq_nonneg ((B.formula.edgeFrame.toCanonical Qu.middle) 1 +
      Erdos957Cases24.sqrtThree)]

/-- Collision-independent end of the adjacent outward split/split branch.
The second split source is the incident partner of the first one, so
coherence forces their common selector into the low farthest-below branch.
Thus any independently established strict lower bound for the actual
recipient's common-edge height contradicts the sharp `-√3` latitude. -/
theorem no_two_split_away_first_second_of_common_snd_gt
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0)
    (huAway : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1)
    (hheight : -Erdos957Cases24.sqrtThree <
      ((Q.case4_pair t.1 t.property
        ⟨T.target.target,
          by simpa [htRole] using T.target.target_at_role⟩).commonFrame.frame.toCanonical
            v) 1) : False := by
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have hsideNe : Qt.twoExtreme.side ≠ B.formula.side :=
    Erdos957Case2SplitDegreeFive.case4SplitRight_side_ne_case2_side_at_away_first
      Q S T hsRole htRole B Qt htAway
  have huPartner : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
    apply Subtype.ext
    have htValue := congrArg Subtype.val htAway
    have huValue := congrArg Subtype.val huAway
    cases hB : B.formula.side <;>
      cases hQ : Qt.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        Erdos957Case4NoThree.incidentHullVertex,
        cyclicSideVertex, pow_succ]
  obtain ⟨hlow, hbranch⟩ :=
    Erdos957Case4SplitClassification.eq_low_of_incident_partner_split_right_collision
      Q T.target U.target htRole huRole huPartner
  have htarget : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have hvSecondary : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htarget.symm
      _ = v := T.target.vertex_eq.symm
  have hlowBound :=
    CommonPairedCase4Rows.currentSecondary_common_snd_le_neg_sqrtThree_of_low
      hA Qt hbranch
  rw [hvSecondary] at hlowBound
  exact (not_lt_of_ge hlowBound) hheight

#print axioms no_case2_incident_case4_away_first_at_degree_five
#print axioms no_two_split_away_first_second_of_common_snd_gt

end Erdos957Case2SplitStrict
