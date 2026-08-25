import Util.IncidenceGeometry.FiniteElementarySegmentCutParameterList
import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicElementarySegmentCutList
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}) (n : ℕ)
    (hn : n + 1 < γ.1.vertices.length) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ, t ∈ L ↔
            t = 0 ∨ t = 1 ∨
              (0 ≤ t ∧ t ≤ 1 ∧
                AffineMap.lineMap
                  (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                  (γ.1.vertices[n + 1]'hn) t ∈ K.points)) ∧
            (0 : ℝ) ∈ L ∧
              (1 : ℝ) ∈ L ∧
                (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                  (∀ k (hk : k + 1 < L.length), L[k] < L[k + 1]) ∧
                    (∀ k (hk : k + 1 < L.length) t,
                      0 ≤ t → t ≤ 1 →
                        AffineMap.lineMap
                          (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                          (γ.1.vertices[n + 1]'hn) t ∈ K.points →
                          ¬ (L[k] < t ∧ t < L[k + 1])) ∧
                      (∀ k (hk : k + 1 < L.length)
                        (p : EuclideanSpace ℝ (Fin 2)), p ∈ K.points →
                          p ∉ openSegment ℝ
                            (AffineMap.lineMap
                              (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                              (γ.1.vertices[n + 1]'hn) L[k])
                            (AffineMap.lineMap
                              (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                              (γ.1.vertices[n + 1]'hn) L[k + 1])) := by
  let A : EuclideanSpace ℝ (Fin 2) := γ.1.vertices[n]'(Nat.lt_of_succ_lt hn)
  let B : EuclideanSpace ℝ (Fin 2) := γ.1.vertices[n + 1]'hn
  have hAB : A ≠ B := by
    dsimp [A, B]
    intro hEq
    have hidx : n = n + 1 := by
      exact (List.Nodup.getElem_inj_iff γ.1.simple_vertices).1 hEq
    omega
  rcases FiniteElementarySegmentCutParameterList A B hAB K.points with
    ⟨L, hnodup, hsorted, hmem, hzero, hone, hbounds, hlt, hparam_gap⟩
  refine ⟨L, hnodup, hsorted, ?_, hzero, hone, hbounds, hlt, hparam_gap, ?_⟩
  · intro t
    simpa [A, B] using hmem t
  · intro k hk p hpK hpopen
    rw [openSegment_eq_image_lineMap] at hpopen
    rcases hpopen with ⟨θ, hθ, hθp⟩
    let u : ℝ := L[k]
    let v : ℝ := L[k + 1]
    let t : ℝ := (1 - θ) * u + θ * v
    have huv : u < v := by
      simpa [u, v] using hlt k hk
    have ht_between_uv : u < t ∧ t < v := by
      constructor <;> dsimp [t] <;> nlinarith [hθ.1, hθ.2, huv]
    have hu_mem : u ∈ L := by
      dsimp [u]
      exact List.getElem_mem (l := L) (n := k) (Nat.lt_of_succ_lt hk)
    have hv_mem : v ∈ L := by
      dsimp [v]
      exact List.getElem_mem (l := L) (n := k + 1) hk
    have hu_bounds : 0 ≤ u ∧ u ≤ 1 := hbounds u hu_mem
    have hv_bounds : 0 ≤ v ∧ v ≤ 1 := hbounds v hv_mem
    have ht0 : 0 ≤ t := by
      dsimp [t]
      nlinarith [hθ.1, hθ.2, hu_bounds.1, hv_bounds.1]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      nlinarith [hθ.1, hθ.2, hu_bounds.2, hv_bounds.2]
    have hline :
        AffineMap.lineMap A B t =
          AffineMap.lineMap
            (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) θ := by
      ext j
      simp [t, AffineMap.lineMap_apply_module]
      ring
    have htK : AffineMap.lineMap A B t ∈ K.points := by
      rw [hline, hθp]
      exact hpK
    exact hparam_gap k hk t ht0 ht1 htK (by
      simpa [u, v] using ht_between_uv)
