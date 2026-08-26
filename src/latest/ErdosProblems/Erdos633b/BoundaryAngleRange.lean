import ErdosProblems.Erdos633b.BoundaryAngleImages

/-! Every angle from 0 to pi occurs along the two outer edges opposite an
open-side point. Connectedness avoids assuming an angular coverage predicate. -/

namespace Erdos633b.Triangle

theorem boundaryAngle_surjective (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) {t : ℝ} (ht : t ∈ Set.Icc 0 Real.pi) :
    ∃ q : Plane, q ∈ T.support ∧ q ≠ p ∧ T.boundaryAngle i p q = t := by
  let K : Set Plane := T.edge (i + 1) ∪ T.edge (i + 2)
  have h1 : i + 1 ≠ i := (by decide : ∀ i : Fin 3, i + 1 ≠ i) i
  have h2 : i + 2 ≠ i := (by decide : ∀ i : Fin 3, i + 2 ≠ i) i
  have h12 : i + 1 ≠ i + 2 := (by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i
  have hsub : K ⊆ T.support := by
    rintro q (hq | hq) <;> exact hq.1
  have hn (q : Plane) (hq : q ∈ K) : q ≠ p := by
    intro he
    rcases hq with hq | hq
    · have hz : T.coord (i + 1) q = 0 := hq.2
      rw [he] at hz
      exact (hp.2 (i + 1) h1).ne' hz
    · have hz : T.coord (i + 2) q = 0 := hq.2
      rw [he] at hz
      exact (hp.2 (i + 2) h2).ne' hz
  have hpre : IsPreconnected K := IsPreconnected.union (T.points i)
    (T.edge_vertex_mem (i + 1) i h1.symm) (T.edge_vertex_mem (i + 2) i h2.symm)
    (T.edge_convex (i + 1)).isPreconnected (T.edge_convex (i + 2)).isPreconnected
  have hcont : ContinuousOn (T.boundaryAngle i p) K := fun q hq =>
    (T.boundaryAngle_continuousAt i hp (hn q hq)).continuousWithinAt
  have hconv := (hpre.image (T.boundaryAngle i p) hcont).convex
  have hzero : (0 : ℝ) ∈ T.boundaryAngle i p '' K :=
    ⟨T.points (i + 1), Or.inr (T.edge_vertex_mem (i + 2) (i + 1) h12),
      T.boundaryAngle_first_endpoint i hp⟩
  have hpi : Real.pi ∈ T.boundaryAngle i p '' K :=
    ⟨T.points (i + 2), Or.inl (T.edge_vertex_mem (i + 1) (i + 2) h12.symm),
      T.boundaryAngle_second_endpoint i hp⟩
  have ht' : t ∈ segment ℝ 0 Real.pi := by
    rw [segment_eq_Icc Real.pi_pos.le]
    exact ht
  obtain ⟨q, hq, hqt⟩ := hconv.segment_subset hzero hpi ht'
  exact ⟨q, hsub hq, hn q hq, hqt⟩

end Erdos633b.Triangle
