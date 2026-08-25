import Util.IncidenceGeometry.OrdinaryCleanLocalCrossing

open Classical
noncomputable section


lemma OrdinaryCleanLocalCrossingAffineTransport {ι : Type*}
    (Γ₀ Γ : ι → PolygonalArc)
    (Ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hΨ_inj : Function.Injective Ψ)
    (hvertices : ∀ k, (Γ k).vertices = (Γ₀ k).vertices.map Ψ)
    (hcarrier : ∀ k, (Γ k).carrier = Ψ '' (Γ₀ k).carrier)
    (hrelative : ∀ k, (Γ k).relativeInterior = Ψ '' (Γ₀ k).relativeInterior)
    (hsegment : ∀ x y,
      Ψ '' segment ℝ x y = segment ℝ (Ψ x) (Ψ y))
    (hopenSegment : ∀ x y,
      Ψ '' openSegment ℝ x y = openSegment ℝ (Ψ x) (Ψ y))
    (hdist : ∀ x y, dist (Ψ x) (Ψ y) = ρ * dist x y)
    (hreflect :
      ∀ {p q p' q' : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        Ψ q - Ψ p = t • (Ψ q' - Ψ p') →
          q - p = t • (q' - p'))
    {i j : ι} {p : EuclideanSpace ℝ (Fin 2)}
    (C : OrdinaryCleanLocalCrossing Γ₀ i j p) :
    Nonempty (OrdinaryCleanLocalCrossing Γ i j (Ψ p)) := by
  have hfirst0 : C.firstIndex < (Γ₀ i).vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) C.firstIndex_valid
  have hsecond0 : C.secondIndex < (Γ₀ j).vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) C.secondIndex_valid
  have hfirst_valid : C.firstIndex + 1 < (Γ i).vertices.length := by
    simpa [hvertices i] using C.firstIndex_valid
  have hsecond_valid : C.secondIndex + 1 < (Γ j).vertices.length := by
    simpa [hvertices j] using C.secondIndex_valid
  have hfirst_open :
      Ψ p ∈ openSegment ℝ (Γ i).vertices[C.firstIndex]
        (Γ i).vertices[C.firstIndex + 1] := by
    have himage :
        Ψ p ∈ Ψ '' openSegment ℝ
          ((Γ₀ i).vertices.get ⟨C.firstIndex, hfirst0⟩)
          ((Γ₀ i).vertices.get ⟨C.firstIndex + 1, C.firstIndex_valid⟩) :=
      ⟨p, C.first_open, rfl⟩
    rw [hopenSegment] at himage
    simpa [hvertices i] using himage
  have hsecond_open :
      Ψ p ∈ openSegment ℝ (Γ j).vertices[C.secondIndex]
        (Γ j).vertices[C.secondIndex + 1] := by
    have himage :
        Ψ p ∈ Ψ '' openSegment ℝ
          ((Γ₀ j).vertices.get ⟨C.secondIndex, hsecond0⟩)
          ((Γ₀ j).vertices.get ⟨C.secondIndex + 1, C.secondIndex_valid⟩) :=
      ⟨p, C.second_open, rfl⟩
    rw [hopenSegment] at himage
    simpa [hvertices j] using himage
  have hfirst_not_vertex : Ψ p ∉ (Γ i).vertices := by
    intro hpv
    rw [hvertices i, List.mem_map] at hpv
    rcases hpv with ⟨q, hq, hqp⟩
    exact C.first_not_vertex (by simpa [hΨ_inj hqp] using hq)
  have hsecond_not_vertex : Ψ p ∉ (Γ j).vertices := by
    intro hpv
    rw [hvertices j, List.mem_map] at hpv
    rcases hpv with ⟨q, hq, hqp⟩
    exact C.second_not_vertex (by simpa [hΨ_inj hqp] using hq)
  have hnonparallel :
      ¬ ∃ t : ℝ,
        (Γ j).vertices[C.secondIndex + 1] - (Γ j).vertices[C.secondIndex] =
          t • ((Γ i).vertices[C.firstIndex + 1] -
            (Γ i).vertices[C.firstIndex]) := by
    intro hparallel
    apply C.directions_nonparallel
    rcases hparallel with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply hreflect
    simpa [hvertices i, hvertices j] using ht
  have hpair_unique :
      ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
        q ∈ (Γ i).relativeInterior → q ∈ (Γ j).relativeInterior → q = Ψ p := by
    intro q hqi hqj
    rw [hrelative i] at hqi
    rw [hrelative j] at hqj
    rcases hqi with ⟨qi, hqi, hqi_eq⟩
    rcases hqj with ⟨qj, hqj, hqj_eq⟩
    have hqij : qi = qj := hΨ_inj (hqi_eq.trans hqj_eq.symm)
    subst qj
    have hqip : qi = p := C.pair_unique hqi hqj
    simpa [← hqi_eq, hqip]
  let ε : ℝ := ρ * C.radius
  have hεpos : 0 < ε := mul_pos hρ C.radius_pos
  have hneighborhood :
      Metric.ball (Ψ p) ε ∩ (⋃ k, (Γ k).carrier) =
        Metric.ball (Ψ p) ε ∩
          (segment ℝ (Γ i).vertices[C.firstIndex]
              (Γ i).vertices[C.firstIndex + 1] ∪
            segment ℝ (Γ j).vertices[C.secondIndex]
              (Γ j).vertices[C.secondIndex + 1]) := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨hqball, hqfamily⟩
      simp only [Set.mem_iUnion] at hqfamily
      rcases hqfamily with ⟨k, hqk⟩
      rw [hcarrier k] at hqk
      rcases hqk with ⟨x, hxcarrier, rfl⟩
      have hxball : x ∈ Metric.ball p C.radius := by
        rw [Metric.mem_ball] at hqball ⊢
        rw [hdist] at hqball
        dsimp [ε] at hqball
        nlinarith
      have hxfamily : x ∈ ⋃ k, (Γ₀ k).carrier := by
        simp only [Set.mem_iUnion]
        exact ⟨k, hxcarrier⟩
      have hx :
          x ∈ Metric.ball p C.radius ∩ (⋃ k, (Γ₀ k).carrier) :=
        ⟨hxball, hxfamily⟩
      rw [C.two_branch_neighborhood] at hx
      refine ⟨hqball, ?_⟩
      rcases hx.2 with hxi | hxj
      · left
        have himage :
            Ψ x ∈ Ψ '' segment ℝ
              ((Γ₀ i).vertices.get ⟨C.firstIndex, hfirst0⟩)
              ((Γ₀ i).vertices.get ⟨C.firstIndex + 1, C.firstIndex_valid⟩) :=
          ⟨x, hxi, rfl⟩
        rw [hsegment] at himage
        simpa [hvertices i] using himage
      · right
        have himage :
            Ψ x ∈ Ψ '' segment ℝ
              ((Γ₀ j).vertices.get ⟨C.secondIndex, hsecond0⟩)
              ((Γ₀ j).vertices.get ⟨C.secondIndex + 1, C.secondIndex_valid⟩) :=
          ⟨x, hxj, rfl⟩
        rw [hsegment] at himage
        simpa [hvertices j] using himage
    · intro hq
      rcases hq with ⟨hqball, hqseg⟩
      refine ⟨hqball, ?_⟩
      simp only [Set.mem_iUnion]
      rcases hqseg with hqi | hqj
      · refine ⟨i, ?_⟩
        rw [(Γ i).carrier_eq]
        exact ⟨C.firstIndex, hfirst_valid, hqi⟩
      · refine ⟨j, ?_⟩
        rw [(Γ j).carrier_eq]
        exact ⟨C.secondIndex, hsecond_valid, hqj⟩
  exact ⟨
    { firstIndex := C.firstIndex
      secondIndex := C.secondIndex
      firstIndex_valid := hfirst_valid
      secondIndex_valid := hsecond_valid
      first_open := hfirst_open
      second_open := hsecond_open
      first_not_vertex := hfirst_not_vertex
      second_not_vertex := hsecond_not_vertex
      directions_nonparallel := hnonparallel
      pair_unique := hpair_unique
      radius := ε
      radius_pos := hεpos
      two_branch_neighborhood := hneighborhood }⟩
