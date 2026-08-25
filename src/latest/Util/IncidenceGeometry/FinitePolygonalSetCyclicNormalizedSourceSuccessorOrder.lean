import Util.IncidenceGeometry.FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicNormalizedSourceSuccessorOrder
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (sourceOccurrenceList :
      List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (hsource_nodup : sourceOccurrenceList.Nodup)
    (hsource_covers :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ∈ sourceOccurrenceList) :
    ∃ successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      successor = sourceOccurrenceList.formPerm ∧
        (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          ∃ n : ℕ, (successor^[n]) p = q) ∧
        (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          p.1 ≠ (successor p).1) := by
  classical
  let α := {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}
  letI : Fintype α := Fintype.ofList sourceOccurrenceList hsource_covers
  have hlen_two : 2 ≤ sourceOccurrenceList.length := by
    have hpoints_two : 1 < K.points.card := by
      have htwo := FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo J K hKJ
      omega
    rcases Finset.one_lt_card.1 hpoints_two with ⟨a, ha, b, hb, hab⟩
    let pa : α := ⟨a, ha⟩
    let pb : α := ⟨b, hb⟩
    have hpane : pa ≠ pb := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hpair_subset :
        ({pa, pb} : Finset α) ⊆ sourceOccurrenceList.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using hsource_covers pa
      · simpa using hsource_covers pb
    have hpair_card : ({pa, pb} : Finset α).card = 2 := by
      simp [hpane]
    have hcard_le := Finset.card_le_card hpair_subset
    have htoFinset_card :
        sourceOccurrenceList.toFinset.card = sourceOccurrenceList.length :=
      List.toFinset_card_of_nodup hsource_nodup
    omega
  have hcycle : sourceOccurrenceList.formPerm.IsCycle :=
    List.isCycle_formPerm hsource_nodup hlen_two
  refine ⟨sourceOccurrenceList.formPerm, rfl, ?_, ?_⟩
  · intro p q
    have hp_mem : p ∈ sourceOccurrenceList := hsource_covers p
    have hq_mem : q ∈ sourceOccurrenceList := hsource_covers q
    have hp_move : sourceOccurrenceList.formPerm p ≠ p :=
      (List.formPerm_apply_mem_ne_self_iff sourceOccurrenceList hsource_nodup p hp_mem).2
        hlen_two
    have hq_move : sourceOccurrenceList.formPerm q ≠ q :=
      (List.formPerm_apply_mem_ne_self_iff sourceOccurrenceList hsource_nodup q hq_mem).2
        hlen_two
    have hsame : sourceOccurrenceList.formPerm.SameCycle p q :=
      hcycle.sameCycle hp_move hq_move
    rcases hsame.exists_nat_pow_eq with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [sourceOccurrenceList.formPerm.iterate_eq_pow]
    exact hn
  · intro p
    have hp_mem : p ∈ sourceOccurrenceList := hsource_covers p
    have hp_move : sourceOccurrenceList.formPerm p ≠ p :=
      (List.formPerm_apply_mem_ne_self_iff sourceOccurrenceList hsource_nodup p hp_mem).2
        hlen_two
    intro hval
    exact hp_move (Subtype.ext hval.symm)
