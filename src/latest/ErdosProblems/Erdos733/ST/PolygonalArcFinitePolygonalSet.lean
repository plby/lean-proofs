import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcFinitePolygonalSet]
lemma PolygonalArcFinitePolygonalSet (Γ : PolygonalArc) :
    ∃ K : FinitePolygonalSet, K.carrier = Γ.carrier := by
-- BODY
  let pts : Finset (EuclideanSpace ℝ (Fin 2)) := Γ.vertices.toFinset
  let segs : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset (Fin (Γ.vertices.length - 1))).image
      (fun i =>
        (Γ.vertices[i.1]'(by omega),
          Γ.vertices[i.1 + 1]'(by omega)))
  have vertex_mem_carrier :
      ∀ {p : EuclideanSpace ℝ (Fin 2)}, p ∈ Γ.vertices → p ∈ Γ.carrier := by
    intro p hp
    rw [Γ.carrier_eq]
    rcases List.get_of_mem hp with ⟨k, hk⟩
    by_cases hnext : k.1 + 1 < Γ.vertices.length
    · refine ⟨k.1, hnext, ?_⟩
      rw [← hk]
      exact left_mem_segment ℝ (Γ.vertices[k.1]) (Γ.vertices[k.1 + 1])
    · have hkpos : 0 < k.1 := by
        by_contra hnot
        have hkzero : k.1 = 0 := Nat.eq_zero_of_not_pos hnot
        have : k.1 + 1 < Γ.vertices.length := by
          have hlen := Γ.length_ge_two
          omega
        exact hnext this
      let m := k.1 - 1
      have hm : m + 1 < Γ.vertices.length := by
        dsimp [m]
        rw [Nat.sub_add_cancel hkpos]
        exact k.2
      have hm_succ : m + 1 = k.1 := by
        dsimp [m]
        exact Nat.sub_add_cancel hkpos
      refine ⟨m, hm, ?_⟩
      rw [← hk]
      simpa [hm_succ] using
        right_mem_segment ℝ (Γ.vertices[m]) (Γ.vertices[m + 1])
  have segment_endpoint_ne :
      ∀ ⦃i : ℕ⦄, (hi : i + 1 < Γ.vertices.length) →
        Γ.vertices[i]'(Nat.lt_of_succ_lt hi) ≠ Γ.vertices[i + 1]'hi := by
    intro i hi hEq
    have hi0 : i < Γ.vertices.length := by omega
    have hnodup := Γ.simple_vertices
    rw [List.nodup_iff_injective_getElem] at hnodup
    have hfin :
        (⟨i, hi0⟩ : Fin Γ.vertices.length) =
          ⟨i + 1, hi⟩ := by
      apply hnodup
      simpa using hEq
    have : i = i + 1 := by
      exact congrArg Fin.val hfin
    omega
  refine ⟨
    { carrier := Γ.carrier
      points := pts
      segments := segs
      segment_nondegenerate := ?_
      segment_endpoints_listed := ?_
      segment_intersections_listed := ?_
      carrier_eq := ?_ },
    rfl⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, _hi, rfl⟩
    exact segment_endpoint_ne (i := i.1) (by omega)
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, _hi, rfl⟩
    constructor
    · simp [pts]
    · simp [pts]
  · intro s t hs ht hst p hps hpt
    rcases Finset.mem_image.mp hs with ⟨i, _hi_mem, rfl⟩
    rcases Finset.mem_image.mp ht with ⟨j, _hj_mem, rfl⟩
    have hi : i.1 + 1 < Γ.vertices.length := by omega
    have hj : j.1 + 1 < Γ.vertices.length := by omega
    rcases Nat.lt_trichotomy i.1 j.1 with hij | hijeq | hji
    · have hp_inter :
          p ∈ segment ℝ Γ.vertices[i.1] Γ.vertices[i.1 + 1] ∩
              segment ℝ Γ.vertices[j.1] Γ.vertices[j.1 + 1] := ⟨hps, hpt⟩
      have hinter := Γ.segment_intersections hi hj hij
      rw [hinter] at hp_inter
      by_cases hadj : j.1 = i.1 + 1
      · have hp_eq : p = Γ.vertices[j] := by
          simpa [hadj] using hp_inter
        simp [pts, hp_eq]
      · simp [hadj] at hp_inter
    · have hfin : i = j := by exact Fin.ext hijeq
      subst j
      exact (hst rfl).elim
    · have hp_inter :
          p ∈ segment ℝ Γ.vertices[j.1] Γ.vertices[j.1 + 1] ∩
              segment ℝ Γ.vertices[i.1] Γ.vertices[i.1 + 1] := ⟨hpt, hps⟩
      have hinter := Γ.segment_intersections hj hi hji
      rw [hinter] at hp_inter
      by_cases hadj : i.1 = j.1 + 1
      · have hp_eq : p = Γ.vertices[i] := by
          simpa [hadj] using hp_inter
        simp [pts, hp_eq]
      · simp [hadj] at hp_inter
  · rw [Γ.carrier_eq]
    ext p
    constructor
    · rintro ⟨i, hi, hpseg⟩
      right
      let s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
        (Γ.vertices[i]'(Nat.lt_of_succ_lt hi), Γ.vertices[i + 1]'hi)
      have hs : s ∈ segs := by
        refine Finset.mem_image.mpr ?_
        let k : Fin (Γ.vertices.length - 1) := ⟨i, by omega⟩
        refine ⟨k, by simp, ?_⟩
        simp [k, s]
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, by simpa [s] using hpseg⟩
    · intro hp
      rcases hp with hp_pts | hp_seg
      · have hp_list : p ∈ Γ.vertices := by simpa [pts] using hp_pts
        simpa [Γ.carrier_eq] using vertex_mem_carrier hp_list
      · rw [Set.mem_iUnion] at hp_seg
        rcases hp_seg with ⟨s, hpseg⟩
        rcases Finset.mem_image.mp s.2 with ⟨i, _hi_mem, hs_eq⟩
        have hi : i.1 + 1 < Γ.vertices.length := by omega
        refine ⟨i.1, hi, ?_⟩
        simpa [← hs_eq] using hpseg
