import Util.IncidenceGeometry.EndpointUnitDiskLocalTransportArc
import Util.IncidenceGeometry.OrdinaryCleanLocalCrossingAffineTransport

open Classical
noncomputable section


lemma EndpointDiskAffineReduction {ι : Type*} [Fintype ι]
    (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < ρ)
    (ha : ∀ i, dist (a i) c = ρ)
    (hb : ∀ i, dist (b i) c = ρ)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x))
    (hUnit :
      ∀ (a₀ b₀ : ι → EuclideanSpace ℝ (Fin 2)),
        (∀ i, dist (a₀ i) (0 : EuclideanSpace ℝ (Fin 2)) = 1) →
          (∀ i, dist (b₀ i) (0 : EuclideanSpace ℝ (Fin 2)) = 1) →
            Function.Injective (fun x : ι ⊕ ι => Sum.elim a₀ b₀ x) →
              ∃ Γ : ι → PolygonalArc,
                (∀ i,
                  (Γ i).source = a₀ i ∧
                    (Γ i).target = b₀ i ∧
                      (Γ i).carrier ⊆ Metric.closedBall
                          (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
                        (Γ i).relativeInterior ⊆ Metric.ball
                          (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
                (∀ ⦃i j : ι⦄,
                  i ≠ j →
                    ¬ ∃ m n : ℕ,
                      ∃ (hm : m + 1 < (Γ i).vertices.length)
                        (hn : n + 1 < (Γ j).vertices.length),
                        ∃ p q : EuclideanSpace ℝ (Fin 2),
                          p ≠ q ∧
                            segment ℝ p q ⊆
                              segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                                segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1]) ∧
                (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j → i ≠ k → j ≠ k →
                    p ∈ (Γ i).relativeInterior →
                      p ∈ (Γ j).relativeInterior →
                        p ∈ (Γ k).relativeInterior → False) ∧
                (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
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
                                    t • ((Γ i).vertices[m + 1] -
                                      (Γ i).vertices[m])) ∧
                (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j →
                    p ∈ (Γ i).relativeInterior →
                      p ∈ (Γ j).relativeInterior →
                        q ∈ (Γ i).relativeInterior →
                          q ∈ (Γ j).relativeInterior →
                            p = q) ∧
                (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j →
                    p ∈ (Γ i).relativeInterior →
                      p ∈ (Γ j).relativeInterior →
                        Nonempty (OrdinaryCleanLocalCrossing Γ i j p))) :
    ∃ Γ : ι → PolygonalArc,
      (∀ i,
        (Γ i).source = a i ∧
          (Γ i).target = b i ∧
            (Γ i).carrier ⊆ Metric.closedBall c ρ ∧
              (Γ i).relativeInterior ⊆ Metric.ball c ρ) ∧
      (∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Γ i).vertices.length)
              (hn : n + 1 < (Γ j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                      segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1]) ∧
      (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              p ∈ (Γ k).relativeInterior → False) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
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
                          t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m])) ∧
      (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              q ∈ (Γ i).relativeInterior →
                q ∈ (Γ j).relativeInterior →
                  p = q) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              Nonempty (OrdinaryCleanLocalCrossing Γ i j p)) := by
  let Φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => (1 / ρ) • (x - c)
  let Ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => c + ρ • y
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    simp [Φ, Ψ, smul_smul, div_eq_mul_inv, hρ_ne, mul_comm]
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y
    simp [Φ, Ψ, smul_smul, div_eq_mul_inv, hρ_ne, mul_comm]
  have hΦ_dist :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        dist x c = ρ → dist (Φ x) (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
    intro x hx
    have hxnorm : ‖x - c‖ = ρ := by
      simpa [dist_eq_norm] using hx
    calc
      dist (Φ x) (0 : EuclideanSpace ℝ (Fin 2)) = ‖(1 / ρ : ℝ) • (x - c)‖ := by
        simp [Φ, dist_eq_norm]
      _ = ‖(1 / ρ : ℝ)‖ * ‖x - c‖ := by rw [norm_smul]
      _ = (1 / ρ) * ρ := by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hρ), hxnorm]
      _ = 1 := by
        field_simp [hρ_ne]
  have hΦ_inj : Function.Injective Φ := by
    intro x y hxy
    have := congrArg Ψ hxy
    simpa [hΨΦ] using this
  have hnormalized_distinct :
      Function.Injective
        (fun x : ι ⊕ ι => Sum.elim (fun i => Φ (a i)) (fun i => Φ (b i)) x) := by
    intro x y hxy
    apply hdistinct
    cases x <;> cases y <;> simp at hxy ⊢
    all_goals exact hΦ_inj hxy
  obtain ⟨Γ0, hΓ0_basic, hΓ0_noShared, hΓ0_noTriple, hΓ0_transverse,
      hΓ0_unique, hΓ0_clean⟩ :=
    hUnit (fun i => Φ (a i)) (fun i => Φ (b i))
      (fun i => hΦ_dist (a i) (ha i))
      (fun i => hΦ_dist (b i) (hb i))
      hnormalized_distinct
  have hΨ_dist :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        dist (Ψ y) c = ρ * dist y (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro y
    simp [Ψ, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  have hΨ_dist_pair :
      ∀ x y : EuclideanSpace ℝ (Fin 2), dist (Ψ x) (Ψ y) = ρ * dist x y := by
    intro x y
    calc
      dist (Ψ x) (Ψ y) = ‖ρ • (x - y)‖ := by
        rw [dist_eq_norm]
        congr 1
        simp [Ψ]
        module
      _ = ρ * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ = ρ * dist x y := by rw [dist_eq_norm]
  have hΨ_inj : Function.Injective Ψ := by
    intro x y hxy
    have := congrArg Φ hxy
    simpa [hΦΨ] using this
  let scale : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (LinearMap.lsmul ℝ (EuclideanSpace ℝ (Fin 2)) ρ).toAffineMap
  let translate : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) c
  let ΨA : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    translate.toAffineMap.comp scale
  have hΨA_apply : ∀ y : EuclideanSpace ℝ (Fin 2), ΨA y = Ψ y := by
    intro y
    simp [ΨA, translate, scale, Ψ, vadd_eq_add]
  have hΨ_segment :
      ∀ x y : EuclideanSpace ℝ (Fin 2),
        Ψ '' segment ℝ x y = segment ℝ (Ψ x) (Ψ y) := by
    intro x y
    trans ΨA '' segment ℝ x y
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, (hΨA_apply q).symm⟩
      · rintro ⟨q, hq, hpq⟩
        refine ⟨q, hq, ?_⟩
        simpa [hΨA_apply q] using hpq
    · simp [hΨA_apply x, hΨA_apply y]
  have hΨ_openSegment :
      ∀ x y : EuclideanSpace ℝ (Fin 2),
        Ψ '' openSegment ℝ x y = openSegment ℝ (Ψ x) (Ψ y) := by
    intro x y
    trans ΨA '' openSegment ℝ x y
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, (hΨA_apply q).symm⟩
      · rintro ⟨q, hq, hpq⟩
        refine ⟨q, hq, ?_⟩
        simpa [hΨA_apply q] using hpq
    · simp [hΨA_apply x, hΨA_apply y]
  have hΨ_sub :
      ∀ x y : EuclideanSpace ℝ (Fin 2), Ψ x - Ψ y = ρ • (x - y) := by
    intro x y
    simp [Ψ, sub_eq_add_neg]
    abel
  have hΨ_reflect :
      ∀ {p q p' q' : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        Ψ q - Ψ p = t • (Ψ q' - Ψ p') →
          q - p = t • (q' - p') := by
    intro p q p' q' t ht
    have hscaled :
        ρ • (q - p) = ρ • (t • (q' - p')) := by
      calc
        ρ • (q - p) = Ψ q - Ψ p := (hΨ_sub q p).symm
        _ = t • (Ψ q' - Ψ p') := ht
        _ = t • (ρ • (q' - p')) := by rw [hΨ_sub]
        _ = ρ • (t • (q' - p')) := by
          rw [smul_smul, smul_smul, mul_comm t ρ]
    exact smul_right_injective (M := EuclideanSpace ℝ (Fin 2)) hρ_ne hscaled
  have htransport_one :
      ∀ i : ι,
        ∃ Γ : PolygonalArc,
          Γ.vertices = (Γ0 i).vertices.map Ψ ∧
            Γ.source = a i ∧
              Γ.target = b i ∧
                Γ.carrier = Ψ '' (Γ0 i).carrier ∧
                  Γ.relativeInterior = Ψ '' (Γ0 i).relativeInterior ∧
                    Γ.carrier ⊆ Metric.closedBall c ρ ∧
                      Γ.relativeInterior ⊆ Metric.ball c ρ := by
    intro i
    obtain ⟨Γ, hΓ_vertices, hΓ_source, hΓ_target, hΓ_carrier,
      hΓ_relative⟩ :=
        EndpointUnitDiskLocalTransportArc Ψ (Γ0 i) hΨ_inj
          hΨ_segment hΨ_openSegment
    refine ⟨Γ, hΓ_vertices, ?_, ?_, hΓ_carrier, hΓ_relative, ?_, ?_⟩
    · rw [hΓ_source, (hΓ0_basic i).1, hΨΦ]
    · rw [hΓ_target, (hΓ0_basic i).2.1, hΨΦ]
    · intro p hp
      rw [hΓ_carrier] at hp
      rcases hp with ⟨q, hq, rfl⟩
      have hq_unit : dist q (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := by
        simpa [Metric.mem_closedBall] using (hΓ0_basic i).2.2.1 hq
      rw [Metric.mem_closedBall, hΨ_dist q]
      calc
        ρ * dist q (0 : EuclideanSpace ℝ (Fin 2)) ≤ ρ * 1 :=
          mul_le_mul_of_nonneg_left hq_unit hρ.le
        _ = ρ := by ring
    · intro p hp
      rw [hΓ_relative] at hp
      rcases hp with ⟨q, hq, rfl⟩
      have hq_unit : dist q (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using (hΓ0_basic i).2.2.2 hq
      rw [Metric.mem_ball, hΨ_dist q]
      calc
        ρ * dist q (0 : EuclideanSpace ℝ (Fin 2)) < ρ * 1 :=
          mul_lt_mul_of_pos_left hq_unit hρ
        _ = ρ := by ring
  choose Γ hΓ using htransport_one
  have hΓ_vertices : ∀ i : ι, (Γ i).vertices = (Γ0 i).vertices.map Ψ :=
    fun i => (hΓ i).1
  have hΓ_relative :
      ∀ i : ι, (Γ i).relativeInterior = Ψ '' (Γ0 i).relativeInterior :=
    fun i => (hΓ i).2.2.2.2.1
  have hΓ_carrier :
      ∀ i : ι, (Γ i).carrier = Ψ '' (Γ0 i).carrier :=
    fun i => (hΓ i).2.2.2.1
  have hΓ_basic :
      ∀ i,
        (Γ i).source = a i ∧
          (Γ i).target = b i ∧
            (Γ i).carrier ⊆ Metric.closedBall c ρ ∧
              (Γ i).relativeInterior ⊆ Metric.ball c ρ := by
    intro i
    exact ⟨(hΓ i).2.1, (hΓ i).2.2.1,
      (hΓ i).2.2.2.2.2.1, (hΓ i).2.2.2.2.2.2⟩
  refine ⟨Γ, hΓ_basic, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hbad
    rcases hbad with ⟨m, n, hmΓ, hnΓ, p, q, hpq_ne, hsubset⟩
    have hmΓ0 : m + 1 < (Γ0 i).vertices.length := by
      simpa [hΓ_vertices i] using hmΓ
    have hnΓ0 : n + 1 < (Γ0 j).vertices.length := by
      simpa [hΓ_vertices j] using hnΓ
    have hpΓi :
        p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] :=
      (hsubset (left_mem_segment ℝ p q)).1
    have hqΓi :
        q ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] :=
      (hsubset (right_mem_segment ℝ p q)).1
    have hp_image_i :
        p ∈ Ψ '' segment ℝ (Γ0 i).vertices[m] (Γ0 i).vertices[m + 1] := by
      rw [hΨ_segment]
      simpa [hΓ_vertices i, List.getElem_map] using hpΓi
    have hq_image_i :
        q ∈ Ψ '' segment ℝ (Γ0 i).vertices[m] (Γ0 i).vertices[m + 1] := by
      rw [hΨ_segment]
      simpa [hΓ_vertices i, List.getElem_map] using hqΓi
    rcases hp_image_i with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hq_image_i with ⟨q₀, hq₀_i, hq₀_eq⟩
    have hp₀q₀_ne : p₀ ≠ q₀ := by
      intro h
      apply hpq_ne
      rw [← hp₀_eq, ← hq₀_eq, h]
    apply hΓ0_noShared hij
    refine ⟨m, n, hmΓ0, hnΓ0, p₀, q₀, hp₀q₀_ne, ?_⟩
    intro x hx
    have hΨx : Ψ x ∈ segment ℝ p q := by
      have himage : Ψ x ∈ Ψ '' segment ℝ p₀ q₀ := ⟨x, hx, rfl⟩
      rw [hΨ_segment] at himage
      simpa [hp₀_eq, hq₀_eq] using himage
    have hΨxΓ := hsubset hΨx
    constructor
    · have hΨx_image :
          Ψ x ∈
            Ψ '' segment ℝ (Γ0 i).vertices[m] (Γ0 i).vertices[m + 1] := by
        rw [hΨ_segment]
        simpa [hΓ_vertices i, List.getElem_map] using hΨxΓ.1
      rcases hΨx_image with ⟨y, hy, hy_eq⟩
      have hyx : y = x := hΨ_inj hy_eq
      simpa [hyx] using hy
    · have hΨx_image :
          Ψ x ∈
            Ψ '' segment ℝ (Γ0 j).vertices[n] (Γ0 j).vertices[n + 1] := by
        rw [hΨ_segment]
        simpa [hΓ_vertices j, List.getElem_map] using hΨxΓ.2
      rcases hΨx_image with ⟨y, hy, hy_eq⟩
      have hyx : y = x := hΨ_inj hy_eq
      simpa [hyx] using hy
  · intro i j k p hij hik hjk hp_i hp_j hp_k
    have hp_i_image : p ∈ Ψ '' (Γ0 i).relativeInterior := by
      simpa [hΓ_relative i] using hp_i
    have hp_j_image : p ∈ Ψ '' (Γ0 j).relativeInterior := by
      simpa [hΓ_relative j] using hp_j
    have hp_k_image : p ∈ Ψ '' (Γ0 k).relativeInterior := by
      simpa [hΓ_relative k] using hp_k
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    rcases hp_k_image with ⟨p₂, hp₂_k, hp₂_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := hΨ_inj (by rw [hp₁_eq, hp₀_eq])
    have hp₂_eq_p₀ : p₂ = p₀ := hΨ_inj (by rw [hp₂_eq, hp₀_eq])
    exact hΓ0_noTriple hij hik hjk hp₀_i (by simpa [hp₁_eq_p₀] using hp₁_j)
      (by simpa [hp₂_eq_p₀] using hp₂_k)
  · intro i j p hij hp_i hp_j
    have hp_i_image : p ∈ Ψ '' (Γ0 i).relativeInterior := by
      simpa [hΓ_relative i] using hp_i
    have hp_j_image : p ∈ Ψ '' (Γ0 j).relativeInterior := by
      simpa [hΓ_relative j] using hp_j
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := hΨ_inj (by rw [hp₁_eq, hp₀_eq])
    have hp₀_j : p₀ ∈ (Γ0 j).relativeInterior := by
      simpa [hp₁_eq_p₀] using hp₁_j
    rcases hΓ0_transverse hij hp₀_i hp₀_j with
      ⟨m, n, hmΓ0, hnΓ0, hpseg_i, hpseg_j, hnonparallel⟩
    have hmΓ : m + 1 < (Γ i).vertices.length := by
      simpa [hΓ_vertices i] using hmΓ0
    have hnΓ : n + 1 < (Γ j).vertices.length := by
      simpa [hΓ_vertices j] using hnΓ0
    refine ⟨m, n, hmΓ, hnΓ, ?_, ?_, ?_⟩
    · have himage :
          Ψ p₀ ∈
            Ψ '' segment ℝ (Γ0 i).vertices[m] (Γ0 i).vertices[m + 1] :=
          ⟨p₀, hpseg_i, rfl⟩
      rw [hΨ_segment] at himage
      simpa [hp₀_eq, hΓ_vertices i, List.getElem_map] using himage
    · have himage :
          Ψ p₀ ∈
            Ψ '' segment ℝ (Γ0 j).vertices[n] (Γ0 j).vertices[n + 1] :=
          ⟨p₀, hpseg_j, rfl⟩
      rw [hΨ_segment] at himage
      simpa [hp₀_eq, hΓ_vertices j, List.getElem_map] using himage
    · intro hparallel
      apply hnonparallel
      rcases hparallel with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      apply hΨ_reflect
      simpa [hΓ_vertices i, hΓ_vertices j, List.getElem_map] using ht
  · intro i j p q hij hp_i hp_j hq_i hq_j
    have hp_i_image : p ∈ Ψ '' (Γ0 i).relativeInterior := by
      simpa [hΓ_relative i] using hp_i
    have hp_j_image : p ∈ Ψ '' (Γ0 j).relativeInterior := by
      simpa [hΓ_relative j] using hp_j
    have hq_i_image : q ∈ Ψ '' (Γ0 i).relativeInterior := by
      simpa [hΓ_relative i] using hq_i
    have hq_j_image : q ∈ Ψ '' (Γ0 j).relativeInterior := by
      simpa [hΓ_relative j] using hq_j
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    rcases hq_i_image with ⟨q₀, hq₀_i, hq₀_eq⟩
    rcases hq_j_image with ⟨q₁, hq₁_j, hq₁_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := hΨ_inj (by rw [hp₁_eq, hp₀_eq])
    have hq₁_eq_q₀ : q₁ = q₀ := hΨ_inj (by rw [hq₁_eq, hq₀_eq])
    have hp₀_j : p₀ ∈ (Γ0 j).relativeInterior := by
      simpa [hp₁_eq_p₀] using hp₁_j
    have hq₀_j : q₀ ∈ (Γ0 j).relativeInterior := by
      simpa [hq₁_eq_q₀] using hq₁_j
    have hpq₀ : p₀ = q₀ := hΓ0_unique hij hp₀_i hp₀_j hq₀_i hq₀_j
    calc
      p = Ψ p₀ := hp₀_eq.symm
      _ = Ψ q₀ := by rw [hpq₀]
      _ = q := hq₀_eq
  · intro i j p hij hp_i hp_j
    have hp_i_image : p ∈ Ψ '' (Γ0 i).relativeInterior := by
      simpa [hΓ_relative i] using hp_i
    have hp_j_image : p ∈ Ψ '' (Γ0 j).relativeInterior := by
      simpa [hΓ_relative j] using hp_j
    rcases hp_i_image with ⟨p₀, hp₀_i, hp₀_eq⟩
    rcases hp_j_image with ⟨p₁, hp₁_j, hp₁_eq⟩
    have hp₁_eq_p₀ : p₁ = p₀ := hΨ_inj (by rw [hp₁_eq, hp₀_eq])
    have hp₀_j : p₀ ∈ (Γ0 j).relativeInterior := by
      simpa [hp₁_eq_p₀] using hp₁_j
    let C : OrdinaryCleanLocalCrossing Γ0 i j p₀ :=
      Classical.choice (hΓ0_clean hij hp₀_i hp₀_j)
    have htransported := OrdinaryCleanLocalCrossingAffineTransport
      Γ0 Γ Ψ ρ hρ hΨ_inj hΓ_vertices hΓ_carrier hΓ_relative
      hΨ_segment hΨ_openSegment hΨ_dist_pair hΨ_reflect C
    simpa [hp₀_eq] using htransported
