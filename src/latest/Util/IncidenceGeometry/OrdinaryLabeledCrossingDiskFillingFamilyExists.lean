import Util.IncidenceGeometry.EndpointFixedPolygonalDiskFillingClean
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskFillingFamily

open Classical
noncomputable section

lemma OrdinaryLabeledCrossingDiskFillingFamilyExists
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D) :
    Nonempty (OrdinaryLabeledCrossingDiskFillingFamily G D F) := by
  let before :
      (x : {p // p ∈ D.crossingSet}) → Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    fun x i => Fin.cases (F.disk x).firstBranch.beforeGate
      (fun _ => (F.disk x).secondBranch.beforeGate) i
  let after :
      (x : {p // p ∈ D.crossingSet}) → Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    fun x i => Fin.cases (F.disk x).firstBranch.afterGate
      (fun _ => (F.disk x).secondBranch.afterGate) i
  have hdistinct :
      ∀ x, Function.Injective
        (fun z : Fin 2 ⊕ Fin 2 => Sum.elim (before x) (after x) z) := by
    intro x s t hst
    have hbb := (F.disk x).first_before_ne_second_before
    have hba := (F.disk x).first_before_ne_second_after
    have hab := (F.disk x).first_after_ne_second_before
    have haa := (F.disk x).first_after_ne_second_after
    have hfirst := (F.disk x).firstBranch.gates_ne
    have hsecond := (F.disk x).secondBranch.gates_ne
    rcases s with i | i
    · rcases t with j | j
      · fin_cases i
        · fin_cases j
          · rfl
          · exact (hbb hst).elim
        · fin_cases j
          · exact (hbb hst.symm).elim
          · rfl
      · fin_cases i
        · fin_cases j
          · exact (hfirst hst).elim
          · exact (hba hst).elim
        · fin_cases j
          · exact (hab hst.symm).elim
          · exact (hsecond hst).elim
    · rcases t with j | j
      · fin_cases i
        · fin_cases j
          · exact (hfirst hst.symm).elim
          · exact (hab hst).elim
        · fin_cases j
          · exact (hba hst.symm).elim
          · exact (hsecond hst.symm).elim
      · fin_cases i
        · fin_cases j
          · rfl
          · exact (haa hst).elim
        · fin_cases j
          · exact (haa hst.symm).elim
          · rfl
  have hbefore :
      ∀ x i, dist (before x i) x.1 = (F.disk x).radius := by
    intro x i
    fin_cases i
    · change dist (F.disk x).firstBranch.beforeGate x.1 =
        (F.disk x).radius
      simpa [Metric.mem_sphere, dist_eq_norm] using
        (F.disk x).firstBranch.beforeGate_on_sphere
    · change dist (F.disk x).secondBranch.beforeGate x.1 =
        (F.disk x).radius
      simpa [Metric.mem_sphere, dist_eq_norm] using
        (F.disk x).secondBranch.beforeGate_on_sphere
  have hafter :
      ∀ x i, dist (after x i) x.1 = (F.disk x).radius := by
    intro x i
    fin_cases i
    · change dist (F.disk x).firstBranch.afterGate x.1 =
        (F.disk x).radius
      simpa [Metric.mem_sphere, dist_eq_norm] using
        (F.disk x).firstBranch.afterGate_on_sphere
    · change dist (F.disk x).secondBranch.afterGate x.1 =
        (F.disk x).radius
      simpa [Metric.mem_sphere, dist_eq_norm] using
        (F.disk x).secondBranch.afterGate_on_sphere
  choose filling hbasic hnoShared hnoTriple htransverse hunique hclean using
    fun x : {p // p ∈ D.crossingSet} =>
      EndpointFixedPolygonalDiskFillingClean x.1 (F.disk x).radius
        (before x) (after x) (F.disk x).firstBranch.radius_pos
        (hbefore x) (hafter x) (hdistinct x)
  refine ⟨{
    ownerEdge := fun x i => Fin.cases (F.disk x).firstEdge
      (fun _ => (F.disk x).secondEdge) i
    fillingArc := filling
    owner_zero := ?_
    owner_one := ?_
    source_zero := ?_
    target_zero := ?_
    source_one := ?_
    target_one := ?_
    carrier_subset_closedBall := ?_
    relativeInterior_subset_ball := ?_
    no_shared_nondegenerate_subarc := ?_
    pair_meets_at_most_once := ?_
    crossing_open_segments := ?_
    clean_crossing := ?_ }⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    simpa [before] using (hbasic x 0).1
  · intro x
    simpa [after] using (hbasic x 0).2.1
  · intro x
    have h := (hbasic x (1 : Fin 2)).1
    change (filling x 1).source =
      (F.disk x).secondBranch.beforeGate at h
    exact h
  · intro x
    have h := (hbasic x (1 : Fin 2)).2.1
    change (filling x 1).target =
      (F.disk x).secondBranch.afterGate at h
    exact h
  · intro x i
    exact (hbasic x i).2.2.1
  · intro x i
    exact (hbasic x i).2.2.2
  · intro x
    exact hnoShared x (by decide : (0 : Fin 2) ≠ 1)
  · intro x p q hp0 hp1 hq0 hq1
    exact hunique x (by decide : (0 : Fin 2) ≠ 1) hp0 hp1 hq0 hq1
  · intro x p hp0 hp1
    obtain ⟨C⟩ := hclean x (by decide : (0 : Fin 2) ≠ 1) hp0 hp1
    exact ⟨C.firstIndex, C.secondIndex, C.firstIndex_valid,
      C.secondIndex_valid, C.first_open, C.second_open,
      C.directions_nonparallel⟩
  · intro x p hp0 hp1
    exact hclean x (by decide : (0 : Fin 2) ≠ 1) hp0 hp1
