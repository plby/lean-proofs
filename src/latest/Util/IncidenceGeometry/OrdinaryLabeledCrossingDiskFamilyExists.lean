import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskFamily
import Util.IncidenceGeometry.OrdinaryCrossingLocalBranchDataExistsBelow
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskDataExistsBelow

open Classical
noncomputable section

lemma OrdinaryLabeledCrossingDiskFamilyExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) :
    Nonempty (OrdinaryLabeledCrossingDiskFamily G D) := by
  let Index := {p // p ∈ D.crossingSet}
  let upper : Index → ℝ := fun x =>
    letI : Nonempty Index := ⟨x⟩
    (Finset.univ.inf' Finset.univ_nonempty
      (fun y : Index =>
        if x = y then (1 : ℝ) else dist x.1 y.1 / 3)) / 2
  have inf_pos :
      ∀ x,
        0 < Finset.univ.inf' (by
          letI : Nonempty Index := ⟨x⟩
          exact Finset.univ_nonempty)
          (fun y : Index =>
            if x = y then (1 : ℝ) else dist x.1 y.1 / 3) := by
    intro x
    letI : Nonempty Index := ⟨x⟩
    exact (Finset.lt_inf'_iff _).2 (by
      intro y _hy
      by_cases hxy : x = y
      · simp [hxy]
      · have hval_ne : x.1 ≠ y.1 := by
          intro h
          exact hxy (Subtype.ext h)
        simp [hxy, dist_pos.mpr hval_ne])
  have upper_pos : ∀ x, 0 < upper x := by
    intro x
    dsimp [upper]
    exact half_pos (inf_pos x)
  have upper_lt :
      ∀ (x y : Index), x ≠ y → upper x < dist x.1 y.1 / 3 := by
    intro x y hxy
    dsimp [upper]
    have hhalf :
        (Finset.univ.inf' (by
          letI : Nonempty Index := ⟨x⟩
          exact Finset.univ_nonempty)
          (fun y : Index =>
            if x = y then (1 : ℝ) else dist x.1 y.1 / 3)) / 2 <
          Finset.univ.inf' (by
            letI : Nonempty Index := ⟨x⟩
            exact Finset.univ_nonempty)
            (fun y : Index =>
              if x = y then (1 : ℝ) else dist x.1 y.1 / 3) :=
      half_lt_self (inf_pos x)
    have hle :
        Finset.univ.inf' (by
          letI : Nonempty Index := ⟨x⟩
          exact Finset.univ_nonempty)
          (fun y : Index =>
            if x = y then (1 : ℝ) else dist x.1 y.1 / 3) ≤
          dist x.1 y.1 / 3 := by
      calc
        Finset.univ.inf' (by
            letI : Nonempty Index := ⟨x⟩
            exact Finset.univ_nonempty)
            (fun y : Index =>
              if x = y then (1 : ℝ) else dist x.1 y.1 / 3) ≤
            (if x = y then (1 : ℝ) else dist x.1 y.1 / 3) :=
          Finset.inf'_le
            (f := fun y : Index =>
              if x = y then (1 : ℝ) else dist x.1 y.1 / 3)
            (Finset.mem_univ y)
        _ = dist x.1 y.1 / 3 := if_neg hxy
    exact hhalf.trans_le hle
  choose disk hdisk using fun x : Index =>
    OrdinaryLabeledCrossingDiskDataExistsBelow G D x (upper x) (upper_pos x)
  refine ⟨{ disk := disk, closedBalls_pairwise_disjoint := ?_ }⟩
  intro x y hxy
  apply Metric.closedBall_disjoint_closedBall
  have hx : (disk x).radius < dist x.1 y.1 / 3 :=
    (hdisk x).trans (upper_lt x y hxy)
  have hy : (disk y).radius < dist x.1 y.1 / 3 := by
    have := (hdisk y).trans (upper_lt y x hxy.symm)
    simpa [dist_comm] using this
  have hdist_pos : 0 < dist x.1 y.1 := by
    exact dist_pos.mpr (by
      intro h
      exact hxy (Subtype.ext h))
  nlinarith
