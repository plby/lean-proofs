import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingFirstSegmentIndex
    (δ : PolygonalArc) (α : PolygonalPath) :
    (α.carrier ∩ δ.carrier).Nonempty →
      ∃ j : ℕ, ∃ hj : j + 1 < δ.vertices.length,
        (α.carrier ∩ segment ℝ δ.vertices[j] δ.vertices[j + 1]).Nonempty ∧
          (∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
            (α.carrier ∩ segment ℝ δ.vertices[i] δ.vertices[i + 1]).Nonempty →
              j ≤ i) ∧
            (∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
              i < j → Disjoint α.carrier (segment ℝ δ.vertices[i] δ.vertices[i + 1])) := by
  intro hXnonempty
  let P : ℕ → Prop := fun i =>
    ∃ hi : i + 1 < δ.vertices.length,
      (α.carrier ∩ segment ℝ δ.vertices[i] δ.vertices[i + 1]).Nonempty
  have hPexists : ∃ i, P i := by
    rcases hXnonempty with ⟨x, hxα, hxδ⟩
    rw [δ.carrier_eq] at hxδ
    rcases hxδ with ⟨i, hi, hxseg⟩
    exact ⟨i, hi, ⟨x, hxα, hxseg⟩⟩
  let j : ℕ := Nat.find hPexists
  have hjP : P j := Nat.find_spec hPexists
  rcases hjP with ⟨hj, hjnonempty⟩
  refine ⟨j, hj, hjnonempty, ?_, ?_⟩
  · intro i hi hnonempty
    exact Nat.find_min' hPexists ⟨hi, hnonempty⟩
  · intro i hi hij
    rw [Set.disjoint_left]
    intro x hxα hxseg
    have hji : j ≤ i := Nat.find_min' hPexists ⟨hi, ⟨x, hxα, hxseg⟩⟩
    exact (Nat.not_lt_of_ge hji) hij
