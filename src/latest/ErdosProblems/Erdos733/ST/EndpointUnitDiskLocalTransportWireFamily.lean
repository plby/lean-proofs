import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalTransportArc

open Classical
noncomputable section


-- [TABLET NODE: EndpointUnitDiskLocalTransportWireFamily]
lemma EndpointUnitDiskLocalTransportWireFamily {ι : Type*} [Fintype ι]
    (toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (L R : ι → EuclideanSpace ℝ (Fin 2)) (Γ : ι → PolygonalArc)
    (htoWorld_inj : Function.Injective toWorld)
    (hframe_closedBall : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r →
        toWorld p ∈ Metric.closedBall z r)
    (hframe_ball : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r →
        toWorld p ∈ Metric.ball z r)
    (hframe_segment : ∀ x y : EuclideanSpace ℝ (Fin 2),
      toWorld '' segment ℝ x y = segment ℝ (toWorld x) (toWorld y))
    (hframe_openSegment : ∀ x y : EuclideanSpace ℝ (Fin 2),
      toWorld '' openSegment ℝ x y = openSegment ℝ (toWorld x) (toWorld y))
    (hframe_reflect :
      ∀ {p q p' q' : EuclideanSpace ℝ (Fin 2)} {c : ℝ},
        toWorld q - toWorld p = c • (toWorld q' - toWorld p') →
          q - p = c • (q' - p'))
    (hΓ_basic : ∀ i,
      (Γ i).source = L i ∧
        (Γ i).target = R i ∧
          (Γ i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ∧
            (Γ i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)
    (hΓ_noShared :
      ∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Γ i).vertices.length)
              (hn : n + 1 < (Γ j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                      segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1])
    (hΓ_noTriple :
      ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              p ∈ (Γ k).relativeInterior → False)
    (hΓ_transverse :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Γ i).vertices.length)
                  (hn : n + 1 < (Γ j).vertices.length),
                  p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∧
                    p ∈ segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (Γ j).vertices[n + 1] - (Γ j).vertices[n] =
                          t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m]))
    (hΓ_unique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              q ∈ (Γ i).relativeInterior →
                q ∈ (Γ j).relativeInterior →
                  p = q) :
    ∃ Ω : ι → PolygonalArc,
      (∀ i : ι,
        (Ω i).vertices = (Γ i).vertices.map toWorld ∧
          (Ω i).source = toWorld (L i) ∧
            (Ω i).target = toWorld (R i) ∧
              (Ω i).carrier = toWorld '' (Γ i).carrier ∧
                (Ω i).relativeInterior = toWorld '' (Γ i).relativeInterior ∧
                  (Ω i).carrier ⊆ Metric.closedBall z r ∧
                    (Ω i).relativeInterior ⊆ Metric.ball z r) ∧
        (∀ ⦃i j : ι⦄,
          i ≠ j →
            ¬ ∃ m n : ℕ,
              ∃ (hm : m + 1 < (Ω i).vertices.length)
                (hn : n + 1 < (Ω j).vertices.length),
                ∃ p q : EuclideanSpace ℝ (Fin 2),
                  p ≠ q ∧
                    segment ℝ p q ⊆
                      segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] ∩
                        segment ℝ (Ω j).vertices[n] (Ω j).vertices[n + 1]) ∧
          (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            i ≠ j → i ≠ k → j ≠ k →
              p ∈ (Ω i).relativeInterior →
                p ∈ (Ω j).relativeInterior →
                  p ∈ (Ω k).relativeInterior → False) ∧
            (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              i ≠ j →
                p ∈ (Ω i).relativeInterior →
                  p ∈ (Ω j).relativeInterior →
                    ∃ m n : ℕ,
                      ∃ (hm : m + 1 < (Ω i).vertices.length)
                        (hn : n + 1 < (Ω j).vertices.length),
                        p ∈ segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] ∧
                          p ∈ segment ℝ (Ω j).vertices[n] (Ω j).vertices[n + 1] ∧
                            ¬ ∃ t : ℝ,
                              (Ω j).vertices[n + 1] - (Ω j).vertices[n] =
                                t • ((Ω i).vertices[m + 1] - (Ω i).vertices[m])) ∧
              (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                i ≠ j →
                  p ∈ (Ω i).relativeInterior →
                    p ∈ (Ω j).relativeInterior →
                      q ∈ (Ω i).relativeInterior →
                        q ∈ (Ω j).relativeInterior →
                          p = q) := by
-- BODY
  have htransport_one :
      ∀ i : ι,
        ∃ Ω : PolygonalArc,
          Ω.vertices = (Γ i).vertices.map toWorld ∧
            Ω.source = toWorld (L i) ∧
              Ω.target = toWorld (R i) ∧
                Ω.carrier = toWorld '' (Γ i).carrier ∧
                  Ω.relativeInterior = toWorld '' (Γ i).relativeInterior ∧
                    Ω.carrier ⊆ Metric.closedBall z r ∧
                      Ω.relativeInterior ⊆ Metric.ball z r := by
    intro i
    obtain ⟨Ω, hΩ_vertices, hΩ_source, hΩ_target, hΩ_carrier,
      hΩ_relative⟩ :=
        EndpointUnitDiskLocalTransportArc toWorld (Γ i) htoWorld_inj
          hframe_segment hframe_openSegment
    refine ⟨Ω, hΩ_vertices, ?_, ?_, hΩ_carrier, hΩ_relative, ?_, ?_⟩
    · rw [hΩ_source, (hΓ_basic i).1]
    · rw [hΩ_target, (hΓ_basic i).2.1]
    · intro p hp
      rw [hΩ_carrier] at hp
      rcases hp with ⟨q, hq, rfl⟩
      exact hframe_closedBall q ((hΓ_basic i).2.2.1 hq)
    · intro p hp
      rw [hΩ_relative] at hp
      rcases hp with ⟨q, hq, rfl⟩
      exact hframe_ball q ((hΓ_basic i).2.2.2 hq)
  choose Ω hΩ using htransport_one
  have hΩ_vertices : ∀ i : ι, (Ω i).vertices = (Γ i).vertices.map toWorld :=
    fun i => (hΩ i).1
  have hΩ_relative :
      ∀ i : ι, (Ω i).relativeInterior = toWorld '' (Γ i).relativeInterior :=
    fun i => (hΩ i).2.2.2.2.1
  refine ⟨Ω, hΩ, ?_, ?_, ?_, ?_⟩
  · intro i j hij hbad
    rcases hbad with ⟨m, n, hmΩ, hnΩ, p, q, hpq_ne, hsubset⟩
    have hmΓ : m + 1 < (Γ i).vertices.length := by
      simpa [hΩ_vertices i] using hmΩ
    have hnΓ : n + 1 < (Γ j).vertices.length := by
      simpa [hΩ_vertices j] using hnΩ
    have hpΩi :
        p ∈ segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] :=
      (hsubset (left_mem_segment ℝ p q)).1
    have hqΩi :
        q ∈ segment ℝ (Ω i).vertices[m] (Ω i).vertices[m + 1] :=
      (hsubset (right_mem_segment ℝ p q)).1
    have hp_image_i :
        p ∈ toWorld '' segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] := by
      rw [hframe_segment]
      simpa [hΩ_vertices i, List.getElem_map] using hpΩi
    have hq_image_i :
        q ∈ toWorld '' segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] := by
      rw [hframe_segment]
      simpa [hΩ_vertices i, List.getElem_map] using hqΩi
    rcases hp_image_i with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hq_image_i with ⟨q₀, hq₀_i, hq₀_eq⟩
    have hp₀q₀_ne : p₀ ≠ q₀ := by
      intro h
      apply hpq_ne
      rw [← hp₀_eq, ← hq₀_eq, h]
    apply hΓ_noShared hij
    refine ⟨m, n, hmΓ, hnΓ, p₀, q₀, hp₀q₀_ne, ?_⟩
    intro x hx
    have htx : toWorld x ∈ segment ℝ p q := by
      have himage : toWorld x ∈ toWorld '' segment ℝ p₀ q₀ := ⟨x, hx, rfl⟩
      rw [hframe_segment] at himage
      simpa [hp₀_eq, hq₀_eq] using himage
    have htxΩ := hsubset htx
    constructor
    · have htx_image :
          toWorld x ∈
            toWorld '' segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] := by
        rw [hframe_segment]
        simpa [hΩ_vertices i, List.getElem_map] using htxΩ.1
      rcases htx_image with ⟨y, hy, hy_eq⟩
      have hyx : y = x := htoWorld_inj hy_eq
      simpa [hyx] using hy
    · have htx_image :
          toWorld x ∈
            toWorld '' segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] := by
        rw [hframe_segment]
        simpa [hΩ_vertices j, List.getElem_map] using htxΩ.2
      rcases htx_image with ⟨y, hy, hy_eq⟩
      have hyx : y = x := htoWorld_inj hy_eq
      simpa [hyx] using hy
  · intro i j k p hij hik hjk hp_i hp_j hp_k
    have hp_i_image : p ∈ toWorld '' (Γ i).relativeInterior := by
      simpa [hΩ_relative i] using hp_i
    have hp_j_image : p ∈ toWorld '' (Γ j).relativeInterior := by
      simpa [hΩ_relative j] using hp_j
    have hp_k_image : p ∈ toWorld '' (Γ k).relativeInterior := by
      simpa [hΩ_relative k] using hp_k
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    rcases hp_k_image with ⟨p₂, hp₂_k, hp₂_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := htoWorld_inj (by rw [hp₁_eq, hp₀_eq])
    have hp₂_eq_p₀ : p₂ = p₀ := htoWorld_inj (by rw [hp₂_eq, hp₀_eq])
    exact hΓ_noTriple hij hik hjk hp₀_i (by simpa [hp₁_eq_p₀] using hp₁_j)
      (by simpa [hp₂_eq_p₀] using hp₂_k)
  · intro i j p hij hp_i hp_j
    have hp_i_image : p ∈ toWorld '' (Γ i).relativeInterior := by
      simpa [hΩ_relative i] using hp_i
    have hp_j_image : p ∈ toWorld '' (Γ j).relativeInterior := by
      simpa [hΩ_relative j] using hp_j
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := htoWorld_inj (by rw [hp₁_eq, hp₀_eq])
    have hp₀_j : p₀ ∈ (Γ j).relativeInterior := by
      simpa [hp₁_eq_p₀] using hp₁_j
    rcases hΓ_transverse hij hp₀_i hp₀_j with
      ⟨m, n, hmΓ, hnΓ, hpseg_i, hpseg_j, hnonparallel⟩
    have hmΩ : m + 1 < (Ω i).vertices.length := by
      simpa [hΩ_vertices i] using hmΓ
    have hnΩ : n + 1 < (Ω j).vertices.length := by
      simpa [hΩ_vertices j] using hnΓ
    refine ⟨m, n, hmΩ, hnΩ, ?_, ?_, ?_⟩
    · have himage :
          toWorld p₀ ∈
            toWorld '' segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] :=
          ⟨p₀, hpseg_i, rfl⟩
      rw [hframe_segment] at himage
      simpa [hp₀_eq, hΩ_vertices i, List.getElem_map] using himage
    · have himage :
          toWorld p₀ ∈
            toWorld '' segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] :=
          ⟨p₀, hpseg_j, rfl⟩
      rw [hframe_segment] at himage
      simpa [hp₀_eq, hΩ_vertices j, List.getElem_map] using himage
    · intro hparallel
      apply hnonparallel
      rcases hparallel with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      apply hframe_reflect
      simpa [hΩ_vertices i, hΩ_vertices j, List.getElem_map] using ht
  · intro i j p q hij hp_i hp_j hq_i hq_j
    have hp_i_image : p ∈ toWorld '' (Γ i).relativeInterior := by
      simpa [hΩ_relative i] using hp_i
    have hp_j_image : p ∈ toWorld '' (Γ j).relativeInterior := by
      simpa [hΩ_relative j] using hp_j
    have hq_i_image : q ∈ toWorld '' (Γ i).relativeInterior := by
      simpa [hΩ_relative i] using hq_i
    have hq_j_image : q ∈ toWorld '' (Γ j).relativeInterior := by
      simpa [hΩ_relative j] using hq_j
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    rcases hq_i_image with ⟨q₀, hq₀_i, hq₀_eq⟩
    rcases hq_j_image with ⟨q₁, hq₁_j, hq₁_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := htoWorld_inj (by rw [hp₁_eq, hp₀_eq])
    have hq₁_eq_q₀ : q₁ = q₀ := htoWorld_inj (by rw [hq₁_eq, hq₀_eq])
    have hp₀_j : p₀ ∈ (Γ j).relativeInterior := by
      simpa [hp₁_eq_p₀] using hp₁_j
    have hq₀_j : q₀ ∈ (Γ j).relativeInterior := by
      simpa [hq₁_eq_q₀] using hq₁_j
    have hpq₀ : p₀ = q₀ := hΓ_unique hij hp₀_i hp₀_j hq₀_i hq₀_j
    calc
      p = toWorld p₀ := hp₀_eq.symm
      _ = toWorld q₀ := by rw [hpq₀]
      _ = q := hq₀_eq
