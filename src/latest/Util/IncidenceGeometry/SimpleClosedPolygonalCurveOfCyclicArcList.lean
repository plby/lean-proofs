import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open Classical
noncomputable section

lemma SimpleClosedPolygonalCurveOfCyclicArcList
    (arcs : List PolygonalArc)
    (h_nodup : arcs.Nodup)
    (h_len : 2 ≤ arcs.length)
    (h_adj_endpoint :
      ∀ γ : PolygonalArc, γ ∈ arcs → γ.target = (arcs.formPerm γ).source)
    (h_adj_intersection :
      ∀ γ : PolygonalArc, γ ∈ arcs →
        γ.carrier ∩ (arcs.formPerm γ).carrier = {γ.target})
    (h_nonadjacent :
      ∀ γ δ : PolygonalArc, γ ∈ arcs → δ ∈ arcs →
        δ ≠ γ → δ ≠ arcs.formPerm γ → arcs.formPerm δ ≠ γ →
          Disjoint γ.carrier δ.carrier) :
    ∃ J : SimpleClosedPolygonalCurve,
      J.edgeArcs = arcs.toFinset ∧
        J.carrier =
          ⋃ γ : {γ : PolygonalArc // γ ∈ arcs.toFinset}, γ.1.carrier ∧
          ∀ γ0 : PolygonalArc, arcs.head? = some γ0 →
            ∃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ.1 = γ0 := by
  classical
  have hmem_iff :
      ∀ γ : PolygonalArc, arcs.formPerm γ ∈ arcs.toFinset ↔ γ ∈ arcs.toFinset := by
    intro γ
    simp [List.formPerm_mem_iff_mem]
  let edgeArcs : Finset PolygonalArc := arcs.toFinset
  let σ : Equiv.Perm {γ : PolygonalArc // γ ∈ edgeArcs} :=
    arcs.formPerm.subtypePerm (by
      intro γ
      simp [edgeArcs, List.formPerm_mem_iff_mem])
  let carrier : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ γ : {γ : PolygonalArc // γ ∈ edgeArcs}, γ.1.carrier
  let J : SimpleClosedPolygonalCurve :=
    { carrier := carrier
      edgeArcs := edgeArcs
      edgeArcs_nonempty := by
        cases arcs with
        | nil =>
            simp at h_len
        | cons γ rest =>
            exact ⟨γ, by simp [edgeArcs]⟩
      carrier_eq := rfl
      successor := σ
      successor_single_cycle := by
        intro γ δ
        have hcycle : arcs.formPerm.IsCycle :=
          List.isCycle_formPerm h_nodup h_len
        have hγmemFin : γ.1 ∈ arcs.toFinset := by
          exact γ.2
        have hδmemFin : δ.1 ∈ arcs.toFinset := by
          exact δ.2
        have hγmem : γ.1 ∈ arcs := List.mem_toFinset.mp hγmemFin
        have hδmem : δ.1 ∈ arcs := List.mem_toFinset.mp hδmemFin
        have hγmove : arcs.formPerm γ.1 ≠ γ.1 :=
          (List.formPerm_apply_mem_ne_self_iff arcs h_nodup γ.1 hγmem).2 h_len
        have hδmove : arcs.formPerm δ.1 ≠ δ.1 :=
          (List.formPerm_apply_mem_ne_self_iff arcs h_nodup δ.1 hδmem).2 h_len
        have hsame : arcs.formPerm.SameCycle γ.1 δ.1 :=
          hcycle.sameCycle hγmove hδmove
        have hsame_sub : σ.SameCycle γ δ := by
          exact (Equiv.Perm.sameCycle_subtypePerm).2 hsame
        rcases hsame_sub.exists_nat_pow_eq with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [σ.iterate_eq_pow]
        exact hn
      adjacent_endpoint := by
        intro γ
        have hγmemFin : γ.1 ∈ arcs.toFinset := by
          exact γ.2
        have hγmem : γ.1 ∈ arcs := List.mem_toFinset.mp hγmemFin
        have h := h_adj_endpoint γ.1 hγmem
        simpa [σ, edgeArcs] using h
      adjacent_intersection := by
        intro γ
        have hγmemFin : γ.1 ∈ arcs.toFinset := by
          exact γ.2
        have hγmem : γ.1 ∈ arcs := List.mem_toFinset.mp hγmemFin
        have h := h_adj_intersection γ.1 hγmem
        simpa [σ, edgeArcs] using h
      nonadjacent_disjoint := by
        intro γ δ hδ_ne hδ_ne_succ hsuccδ_ne
        have hγmemFin : γ.1 ∈ arcs.toFinset := by
          exact γ.2
        have hδmemFin : δ.1 ∈ arcs.toFinset := by
          exact δ.2
        have hγmem : γ.1 ∈ arcs := List.mem_toFinset.mp hγmemFin
        have hδmem : δ.1 ∈ arcs := List.mem_toFinset.mp hδmemFin
        have hδ_val_ne : δ.1 ≠ γ.1 := by
          intro h
          exact hδ_ne (Subtype.ext h)
        have hδ_val_ne_succ : δ.1 ≠ arcs.formPerm γ.1 := by
          intro h
          apply hδ_ne_succ
          apply Subtype.ext
          simpa [σ, edgeArcs] using h
        have hsuccδ_val_ne : arcs.formPerm δ.1 ≠ γ.1 := by
          intro h
          apply hsuccδ_ne
          apply Subtype.ext
          simpa [σ, edgeArcs] using h
        exact h_nonadjacent γ.1 δ.1 hγmem hδmem hδ_val_ne hδ_val_ne_succ
          hsuccδ_val_ne }
  refine ⟨J, rfl, rfl, ?_⟩
  intro γ0 hhead
  have hγ0mem : γ0 ∈ arcs := by
    cases arcs with
    | nil =>
        simp at hhead
    | cons γ rest =>
        simp at hhead
        subst γ0
        simp
  have hγ0edge : γ0 ∈ J.edgeArcs := by
    simpa [J, edgeArcs] using hγ0mem
  exact ⟨⟨γ0, hγ0edge⟩, rfl⟩
