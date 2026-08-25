import Util.IncidenceGeometry.ComplementComponent

lemma ComplementComponentDisjointUnionRight
    (A B C : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent A C → Disjoint C B →
      ComplementComponent (A ∪ B) C := by
  intro hC hCB
  rcases hC with ⟨hCne, hCA, hCconn, hCmax⟩
  refine ⟨hCne, ?_, hCconn, ?_⟩
  · intro x hxC
    change x ∉ A ∪ B
    intro hxAB
    rcases hxAB with hxA | hxB
    · exact (hCA hxC) hxA
    · exact (Set.disjoint_left.mp hCB) hxC hxB
  · intro D hDne hDAB hDconn hCD
    have hDA : D ⊆ Aᶜ := by
      intro x hxD
      change x ∉ A
      intro hxA
      exact (hDAB hxD) (Or.inl hxA)
    exact hCmax D hDne hDA hDconn hCD
