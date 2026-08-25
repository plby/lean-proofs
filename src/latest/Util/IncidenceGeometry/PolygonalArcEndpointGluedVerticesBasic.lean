import Util.IncidenceGeometry.PolygonalArcEndpointGluedVertices

open Classical
noncomputable section

lemma PolygonalArcEndpointGluedVerticesBasic
    (pieces : List PolygonalArc) (hpieces : pieces ≠ []) :
    2 ≤ (PolygonalArcEndpointGluedVertices pieces).length ∧
      (∀ Γ, pieces.head? = some Γ →
        (PolygonalArcEndpointGluedVertices pieces).head? = some Γ.source) ∧
      (∀ Γ, pieces.getLast? = some Γ →
        (PolygonalArcEndpointGluedVertices pieces).getLast? = some Γ.target) := by
  have hlength :
      2 ≤ (PolygonalArcEndpointGluedVertices pieces).length := by
    cases pieces with
    | nil => contradiction
    | cons Γ rest =>
        simp [PolygonalArcEndpointGluedVertices, List.length_append]
        have hΓ := Γ.length_ge_two
        omega
  have hhead :
      ∀ Γ, pieces.head? = some Γ →
        (PolygonalArcEndpointGluedVertices pieces).head? = some Γ.source := by
    intro Γ hΓ
    cases pieces with
    | nil => contradiction
    | cons Δ rest =>
        simp at hΓ
        subst Γ
        rw [PolygonalArcEndpointGluedVertices]
        rw [List.head?_append_of_ne_nil Δ.vertices]
        · exact Δ.source_eq_head
        · intro hnil
          have hlen : Δ.vertices.length = 0 := by simp [hnil]
          have hΔ := Δ.length_ge_two
          omega
  have tailFlatten_getLast :
      ∀ qs : List PolygonalArc,
        (qs.map (fun Δ => Δ.vertices.tail)).flatten.getLast? =
          qs.getLast?.map (fun Δ => Δ.target) := by
    intro qs
    induction qs with
    | nil => simp
    | cons Γ rest ih =>
        cases rest with
        | nil =>
            simp
            rw [List.getLast?_tail]
            have hne : Γ.vertices.length ≠ 1 := by
              have hΓ := Γ.length_ge_two
              omega
            simp [hne, Γ.target_eq_last]
        | cons Δ rest =>
            have ih' := ih
            have hflat_ne :
                ((Δ :: rest).map (fun Δ => Δ.vertices.tail)).flatten ≠ [] := by
              intro hflat
              have hlen := congrArg List.length hflat
              have hΔ := Δ.length_ge_two
              simp [List.flatten_cons, List.length_append, List.length_tail] at hlen
              omega
            rw [List.map_cons, List.flatten_cons]
            rw [List.getLast?_append_of_ne_nil _ hflat_ne]
            simpa using ih'
  have hlast :
      ∀ Γ, pieces.getLast? = some Γ →
        (PolygonalArcEndpointGluedVertices pieces).getLast? = some Γ.target := by
    intro Γ hΓ
    cases pieces with
    | nil => contradiction
    | cons Δ rest =>
        cases rest with
        | nil =>
            simp [PolygonalArcEndpointGluedVertices] at hΓ ⊢
            subst Γ
            exact Δ.target_eq_last
        | cons E rest =>
            have hflat_ne :
                ((E :: rest).map (fun Δ => Δ.vertices.tail)).flatten ≠ [] := by
              intro hflat
              have hlen := congrArg List.length hflat
              have hE := E.length_ge_two
              simp [List.flatten_cons, List.length_append, List.length_tail] at hlen
              omega
            rw [PolygonalArcEndpointGluedVertices]
            rw [List.getLast?_append_of_ne_nil _ hflat_ne]
            have htail := tailFlatten_getLast (E :: rest)
            rw [htail]
            have hΓtail : (E :: rest).getLast? = some Γ := by
              simpa using hΓ
            simp [hΓtail]
  exact ⟨hlength, hhead, hlast⟩
