import Mathlib.Dynamics.PeriodicPts.Lemmas
import Util.IncidenceGeometry.SimpleClosedPolygonalCurve

open Classical
noncomputable section

lemma SimpleClosedPolygonalCurveEdgeArcTraversalList
    (J : SimpleClosedPolygonalCurve) :
    ∃ E : List {γ : PolygonalArc // γ ∈ J.edgeArcs},
      E.Nodup ∧
        (∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ ∈ E) ∧
          0 < E.length ∧
            (∀ n (hn : n + 1 < E.length),
              J.successor (E[n]) = E[n + 1]) ∧
              (∀ (hLast : E.length - 1 < E.length) (hFirst : 0 < E.length),
                J.successor (E[E.length - 1]'hLast) = E[0]'hFirst) := by
  let α := {γ : PolygonalArc // γ ∈ J.edgeArcs}
  rcases J.edgeArcs_nonempty with ⟨γ0, hγ0⟩
  let a0 : α := ⟨γ0, hγ0⟩
  let σ : α → α := J.successor
  let E : List α := (List.range (Function.minimalPeriod σ a0)).map fun n => σ^[n] a0
  have hperiodic : a0 ∈ Function.periodicPts σ := by
    exact (J.successor.injective).mem_periodicPts a0
  have hminpos : 0 < Function.minimalPeriod σ a0 :=
    Function.minimalPeriod_pos_of_mem_periodicPts hperiodic
  have hlen : E.length = Function.minimalPeriod σ a0 := by
    simp [E]
  have hlenpos : 0 < E.length := by
    simpa [hlen] using hminpos
  refine ⟨E, ?_, ?_, hlenpos, ?_, ?_⟩
  · have hnodupCycle : (Function.periodicOrbit σ a0).Nodup :=
      Function.nodup_periodicOrbit (f := σ) (x := a0)
    exact Cycle.nodup_coe_iff.mp (by
      simpa [E, Function.periodicOrbit_def] using hnodupCycle)
  · intro γ
    obtain ⟨n, hn⟩ := J.successor_single_cycle a0 γ
    have hmemCycle : γ ∈ Function.periodicOrbit σ a0 := by
      rw [Function.mem_periodicOrbit_iff hperiodic]
      exact ⟨n, by simpa [σ] using hn⟩
    have hmemCoe : γ ∈ (E : Cycle α) := by
      simpa [E, Function.periodicOrbit_def] using hmemCycle
    exact Cycle.mem_coe_iff.mp hmemCoe
  · intro n hn
    simp [E, σ, Function.iterate_succ_apply']
  · intro hLast _hFirst
    have hlast_range :
        E.length - 1 < (List.range (Function.minimalPeriod σ a0)).length := by
      simpa [E] using hLast
    have hlast_index :
        (List.range (Function.minimalPeriod σ a0))[E.length - 1]'hlast_range =
          Function.minimalPeriod σ a0 - 1 := by
      simp [hlen]
    simp [E]
    change σ (σ^[Function.minimalPeriod σ a0 - 1] a0) = a0
    have hsucc :
        σ (σ^[Function.minimalPeriod σ a0 - 1] a0) =
          σ^[Nat.succ (Function.minimalPeriod σ a0 - 1)] a0 :=
      (Function.iterate_succ_apply' (f := σ)
        (n := Function.minimalPeriod σ a0 - 1) (x := a0)).symm
    rw [hsucc]
    have hsuccidx :
        (Function.minimalPeriod σ a0 - 1).succ =
          Function.minimalPeriod σ a0 := by
      exact Nat.succ_pred_eq_of_pos hminpos
    rw [hsuccidx]
    exact Function.iterate_minimalPeriod (f := σ) (x := a0)
