import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.ArcCrossingEarlierPrefix
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcFiniteInteriorFirstPoint]
lemma PolygonalArcFiniteInteriorFirstPoint
    (delta : PolygonalArc)
    (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    X.Nonempty →
      (∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ X → x ∈ delta.relativeInterior) →
        ∃ x : EuclideanSpace ℝ (Fin 2),
          ∃ j : ℕ, ∃ hj : j + 1 < delta.vertices.length,
            x ∈ X ∧
              x ∈ segment ℝ delta.vertices[j] delta.vertices[j + 1] ∧
        ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ X →
                    z ∈
                        ArcCrossingEarlierPrefix delta j hj ∪
                          segment ℝ delta.vertices[j] x →
                      z = x := by
-- BODY
  intro hX hrelative
  let P : ℕ → Prop := fun j =>
    ∃ hj : j + 1 < delta.vertices.length,
      ∃ x : EuclideanSpace ℝ (Fin 2),
        x ∈ X ∧ x ∈ segment ℝ delta.vertices[j] delta.vertices[j + 1]
  have hP : ∃ j : ℕ, P j := by
    obtain ⟨x, hx⟩ := hX
    have hxcarrier : x ∈ delta.carrier :=
      (delta.relativeInterior_eq ▸ (hrelative x hx)).1
    rw [delta.carrier_eq] at hxcarrier
    obtain ⟨j, hj, hxseg⟩ := hxcarrier
    exact ⟨j, hj, x, hx, hxseg⟩
  let j : ℕ := Nat.find hP
  have hjP : P j := Nat.find_spec hP
  obtain ⟨hj, x0, hx0X, hx0seg⟩ := hjP
  let Y := X.filter (fun z => z ∈ segment ℝ delta.vertices[j] delta.vertices[j + 1])
  have hY : Y.Nonempty := by
    refine ⟨x0, ?_⟩
    simp [Y, hx0X, hx0seg]
  obtain ⟨x, hxY, hxmin⟩ :=
    Finset.exists_min_image Y (fun z => dist delta.vertices[j] z) hY
  have hxX : x ∈ X := (Finset.mem_filter.mp hxY).1
  have hxseg : x ∈ segment ℝ delta.vertices[j] delta.vertices[j + 1] :=
    (Finset.mem_filter.mp hxY).2
  refine ⟨x, j, hj, hxX, hxseg, ?_⟩
  intro z hzX hzprefix
  rcases hzprefix with hze | hzlast
  · rw [ArcCrossingEarlierPrefix] at hze
    obtain ⟨i, hzseg⟩ := Set.mem_iUnion.mp hze
    have hi : i.1 + 1 < delta.vertices.length := by omega
    have hPi : P i.1 := ⟨hi, z, hzX, hzseg⟩
    have hji : j ≤ i.1 := Nat.find_min' hP hPi
    omega
  · have hzseg : z ∈ segment ℝ delta.vertices[j] delta.vertices[j + 1] :=
      (convex_segment delta.vertices[j] delta.vertices[j + 1]).segment_subset
        (left_mem_segment ℝ delta.vertices[j] delta.vertices[j + 1]) hxseg hzlast
    have hzY : z ∈ Y := Finset.mem_filter.mpr ⟨hzX, hzseg⟩
    have hmin := hxmin z hzY
    have hzdist : dist delta.vertices[j] z ≤ dist delta.vertices[j] x := by
      have hzball : z ∈ Metric.closedBall delta.vertices[j]
          (dist delta.vertices[j] x) := by
        exact (convex_closedBall delta.vertices[j] (dist delta.vertices[j] x)).segment_subset
          (by simp [Metric.mem_closedBall])
          (by simp [Metric.mem_closedBall, dist_comm]) hzlast
      simpa [Metric.mem_closedBall, dist_comm] using hzball
    have hdist : dist delta.vertices[j] z = dist delta.vertices[j] x := by
      exact le_antisymm hzdist hmin
    have hadd := dist_add_dist_of_mem_segment hzlast
    have hzx : dist z x = 0 := by linarith
    exact dist_eq_zero.mp hzx
