import Util.IncidenceGeometry.EndpointRectangularGoodHeights
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.StraightSegmentPolygonalArc

open Classical
noncomputable section


lemma EndpointRectangularWireReplacement {ι : Type*} [Fintype ι]
    (ε H : ℝ) (L R : ι → EuclideanSpace ℝ (Fin 2))
    (hε : 0 < ε) (hH : 0 < H)
    (hLx : ∀ i, (L i) 0 = -ε)
    (hRx : ∀ i, (R i) 0 = ε)
    (hLy : ∀ i, |(L i) 1| < H)
    (hRy : ∀ i, |(R i) 1| < H)
    (hLinj : Function.Injective L)
    (hRinj : Function.Injective R)
    (horder : ∀ i j, (L i) 1 < (L j) 1 ↔ (R j) 1 < (R i) 1) :
    ∃ M : ι → EuclideanSpace ℝ (Fin 2),
      ∃ Γ : ι → PolygonalArc,
        (Function.Injective M) ∧
          (∀ i, (M i) 0 = 0 ∧ |(M i) 1| < H) ∧
            (∀ i j, (M i) 1 < (M j) 1 ↔ (L i) 1 < (L j) 1) ∧
              (∀ i,
                (Γ i).vertices = [L i, M i, R i] ∧
                  (Γ i).source = L i ∧
                    (Γ i).target = R i ∧
                      (Γ i).carrier ⊆
                        {p : EuclideanSpace ℝ (Fin 2) |
                          -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} ∧
                        (Γ i).relativeInterior ⊆
                          {p : EuclideanSpace ℝ (Fin 2) |
                            -ε < p 0 ∧ p 0 < ε ∧ -H < p 1 ∧ p 1 < H}) ∧
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
                                  p = q) := by
  let pointOnMidline : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun y => WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 0 else y)
  let middleFromHeights : (ι → ℝ) → ι → EuclideanSpace ℝ (Fin 2) :=
    fun η i => pointOnMidline (η i)
  let goodHeights (η : ι → ℝ) : Prop :=
    (∀ i, |η i| < H) ∧
      (∀ i j, η i < η j ↔ (L i) 1 < (L j) 1) ∧
        (∀ ⦃i j : ι⦄, i ≠ j →
          line[ℝ, L i, middleFromHeights η i] ≠
              line[ℝ, L j, middleFromHeights η j] ∧
            line[ℝ, L i, middleFromHeights η i] ≠
                line[ℝ, middleFromHeights η j, R j] ∧
              line[ℝ, middleFromHeights η i, R i] ≠
                  line[ℝ, L j, middleFromHeights η j] ∧
                line[ℝ, middleFromHeights η i, R i] ≠
                  line[ℝ, middleFromHeights η j, R j]) ∧
          (∀ ⦃i j : ι⦄, i ≠ j →
            ¬ ∃ t : ℝ,
              R j - middleFromHeights η j =
                t • (R i - middleFromHeights η i)) ∧
            (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
              i ≠ j → i ≠ k → j ≠ k →
                p ∈ openSegment ℝ (middleFromHeights η i) (R i) →
                  p ∈ openSegment ℝ (middleFromHeights η j) (R j) →
                    p ∈ openSegment ℝ (middleFromHeights η k) (R k) → False)
  have hη_exists : ∃ η : ι → ℝ, goodHeights η := by
    simpa [goodHeights, middleFromHeights, pointOnMidline] using
      EndpointRectangularGoodHeights ε H L R hε hH hLx hRx hLy hRy hLinj hRinj horder
  obtain ⟨η, hη_good⟩ := hη_exists
  rcases hη_good with
    ⟨hη_bound, hη_order, hη_supportLines, hη_rightNonparallel, hη_noRightTriple⟩
  let M : ι → EuclideanSpace ℝ (Fin 2) := middleFromHeights η
  let Γ : ι → PolygonalArc := fun i =>
    { vertices := [L i, M i, R i]
      length_ge_two := by norm_num
      source := L i
      target := R i
      source_eq_head := by simp
      target_eq_last := by simp
      carrier :=
        {p | ∃ n : ℕ, ∃ hn : n + 1 < [L i, M i, R i].length,
          p ∈ segment ℝ [L i, M i, R i][n] [L i, M i, R i][n + 1]}
      relativeInterior :=
        {p | ∃ n : ℕ, ∃ hn : n + 1 < [L i, M i, R i].length,
          p ∈ segment ℝ [L i, M i, R i][n] [L i, M i, R i][n + 1]} \
          ({L i, R i} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := by rfl
      relativeInterior_eq := by rfl
      simple_vertices := by
        have hLM : L i ≠ M i := by
          intro h
          have hx : (L i) 0 = (M i) 0 :=
            congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
          have hM0 : (M i) 0 = 0 := by
            simp [M, middleFromHeights, pointOnMidline]
          linarith [hLx i, hM0, hx]
        have hLR : L i ≠ R i := by
          intro h
          have hx : (L i) 0 = (R i) 0 :=
            congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
          linarith [hLx i, hRx i, hx]
        have hMR : M i ≠ R i := by
          intro h
          have hx : (M i) 0 = (R i) 0 :=
            congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
          have hM0 : (M i) 0 = 0 := by
            simp [M, middleFromHeights, pointOnMidline]
          linarith [hRx i, hM0, hx]
        simp [hLM, hLR, hMR]
      segment_intersections := by
        intro m n hm hn hmn
        have h_inter :
            segment ℝ (L i) (M i) ∩ segment ℝ (M i) (R i) = {M i} := by
          ext p
          constructor
          · rintro ⟨hpLM, hpMR⟩
            rcases hpLM with ⟨a, b, ha, hb, hab, hcombLM⟩
            rcases hpMR with ⟨c, d, hc, hd, hcd, hcombMR⟩
            have hxLM : a * (-ε) + b * 0 = p 0 := by
              have hx :=
                congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcombLM
              simpa [hLx i, M, middleFromHeights, pointOnMidline] using hx
            have hxMR : c * 0 + d * ε = p 0 := by
              have hx :=
                congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcombMR
              simpa [hRx i, M, middleFromHeights, pointOnMidline] using hx
            have ha0 : a = 0 := by
              nlinarith [ha, hd, hε, hxLM, hxMR]
            have hb1 : b = 1 := by
              linarith
            subst a
            subst b
            have hpM : M i = p := by
              simpa using hcombLM
            exact Set.mem_singleton_iff.mpr hpM.symm
          · intro hp
            rw [Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨right_mem_segment ℝ (L i) (M i), left_mem_segment ℝ (M i) (R i)⟩
        have hm' : m + 1 < 3 := by simpa using hm
        have hn' : n + 1 < 3 := by simpa using hn
        have hm0 : m = 0 := by omega
        have hn1 : n = 1 := by omega
        subst m
        subst n
        simpa using h_inter
      vertices_avoid_nonincident_interiors := by
        intro m n hm hn hnm hnmsucc
        have hR_not_left : R i ∉ openSegment ℝ (L i) (M i) := by
          intro hp
          have hpseg : R i ∈ segment ℝ (L i) (M i) :=
            openSegment_subset_segment ℝ (L i) (M i) hp
          rcases hpseg with ⟨a, b, ha, hb, hab, hcomb⟩
          have hx : a * (-ε) + b * 0 = ε := by
            have hx' :=
              congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
            simpa [hLx i, hRx i, M, middleFromHeights, pointOnMidline] using hx'
          nlinarith [ha, hε, hx]
        have hL_not_right : L i ∉ openSegment ℝ (M i) (R i) := by
          intro hp
          have hpseg : L i ∈ segment ℝ (M i) (R i) :=
            openSegment_subset_segment ℝ (M i) (R i) hp
          rcases hpseg with ⟨a, b, ha, hb, hab, hcomb⟩
          have hx : a * 0 + b * ε = -ε := by
            have hx' :=
              congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
            simpa [hLx i, hRx i, M, middleFromHeights, pointOnMidline] using hx'
          nlinarith [hb, hε, hx]
        have hm' : m + 1 < 3 := by simpa using hm
        have hn' : n < 3 := by simpa using hn
        have hm_cases : m = 0 ∨ m = 1 := by omega
        rcases hm_cases with rfl | rfl
        · have hn2 : n = 2 := by omega
          subst n
          simpa using hR_not_left
        · have hn0 : n = 0 := by omega
          subst n
          simpa using hL_not_right }
  have hM_inj : Function.Injective M := by
    intro i j hij
    apply hLinj
    have hηij : η i = η j := by
      have hcoord : (M i) 1 = (M j) 1 :=
        congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hij
      simpa [M, middleFromHeights, pointOnMidline] using hcoord
    have hLij_y : (L i) 1 = (L j) 1 := by
      rcases lt_trichotomy ((L i) 1) ((L j) 1) with hlt | heq | hgt
      · have hηlt : η i < η j := (hη_order i j).2 hlt
        exfalso
        rw [hηij] at hηlt
        exact (lt_irrefl (η j)) hηlt
      · exact heq
      · have hηlt : η j < η i := (hη_order j i).2 hgt
        exfalso
        rw [hηij] at hηlt
        exact (lt_irrefl (η j)) hηlt
    ext k
    fin_cases k
    · simp [hLx]
    · exact hLij_y
  have hM_coord : ∀ i, (M i) 0 = 0 ∧ |(M i) 1| < H := by
    intro i
    constructor
    · simp [M, middleFromHeights, pointOnMidline]
    · simpa [M, middleFromHeights, pointOnMidline] using hη_bound i
  have hM_order : ∀ i j, (M i) 1 < (M j) 1 ↔ (L i) 1 < (L j) 1 := by
    intro i j
    simpa [M, middleFromHeights, pointOnMidline] using hη_order i j
  have hclosedRect_convex :
      Convex ℝ
        {p : EuclideanSpace ℝ (Fin 2) |
          -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
    convert
      ((convex_Icc (𝕜 := ℝ) (-ε) ε).linear_preimage
          (EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin 2) 0)).inter
        ((convex_Icc (𝕜 := ℝ) (-H) H).linear_preimage
          (EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin 2) 1))
      using 1
    rfl
    apply Set.ext
    intro p
    change
      (-ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H) ↔
        ((-ε ≤ p 0 ∧ p 0 ≤ ε) ∧ (-H ≤ p 1 ∧ p 1 ≤ H))
    constructor
    · rintro ⟨hxlo, hxhi, hylo, hyhi⟩
      exact ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
    · rintro ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
      exact ⟨hxlo, hxhi, hylo, hyhi⟩
  have hΓ_basic :
      ∀ i,
        (Γ i).vertices = [L i, M i, R i] ∧
          (Γ i).source = L i ∧
            (Γ i).target = R i ∧
              (Γ i).carrier ⊆
                {p : EuclideanSpace ℝ (Fin 2) |
                  -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} ∧
                (Γ i).relativeInterior ⊆
                  {p : EuclideanSpace ℝ (Fin 2) |
                    -ε < p 0 ∧ p 0 < ε ∧ -H < p 1 ∧ p 1 < H} := by
    intro i
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro p hp
      have hLQ :
          L i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
        have hy := abs_lt.mp (hLy i)
        simp only [Set.mem_setOf_eq]
        constructor
        · linarith [hLx i]
        constructor
        · linarith [hLx i, hε]
        constructor <;> linarith
      have hMQ :
          M i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
        have hy := abs_lt.mp (hη_bound i)
        simp only [Set.mem_setOf_eq]
        constructor
        · simp [M, middleFromHeights, pointOnMidline]
          linarith [hε]
        constructor
        · simp [M, middleFromHeights, pointOnMidline]
          linarith [hε]
        constructor
        · simp [M, middleFromHeights, pointOnMidline]
          linarith
        · simp [M, middleFromHeights, pointOnMidline]
          linarith
      have hRQ :
          R i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
        have hy := abs_lt.mp (hRy i)
        simp only [Set.mem_setOf_eq]
        constructor
        · linarith [hRx i, hε]
        constructor
        · linarith [hRx i]
        constructor <;> linarith
      rcases hp with ⟨n, hn, hpseg⟩
      have hn_cases : n = 0 ∨ n = 1 := by
        have hn' : n + 1 < 3 := by simpa using hn
        omega
      rcases hn_cases with rfl | rfl
      · exact hclosedRect_convex.segment_subset hLQ hMQ (by simpa using hpseg)
      · exact hclosedRect_convex.segment_subset hMQ hRQ (by simpa using hpseg)
    · intro p hp
      have strict_y_of_combo :
          ∀ {a b y₀ y₁ y : ℝ},
            0 ≤ a → 0 ≤ b → a + b = 1 →
              -H < y₀ → y₀ < H → -H < y₁ → y₁ < H →
                a * y₀ + b * y₁ = y → -H < y ∧ y < H := by
        intro a b y₀ y₁ y ha hb hab hy₀_low hy₀_high hy₁_low hy₁_high hy
        constructor
        · have hy₀_pos : 0 < y₀ + H := by linarith
          have hy₁_pos : 0 < y₁ + H := by linarith
          have hsum_pos : 0 < a * (y₀ + H) + b * (y₁ + H) := by
            by_cases ha_zero : a = 0
            · have hb_one : b = 1 := by linarith
              nlinarith [hy₁_pos]
            · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
              have hterm₀ : 0 < a * (y₀ + H) := mul_pos ha_pos hy₀_pos
              have hterm₁ : 0 ≤ b * (y₁ + H) :=
                mul_nonneg hb (le_of_lt hy₁_pos)
              linarith
          have hrewrite : y + H = a * (y₀ + H) + b * (y₁ + H) := by
            nlinarith
          linarith
        · have hy₀_pos : 0 < H - y₀ := by linarith
          have hy₁_pos : 0 < H - y₁ := by linarith
          have hsum_pos : 0 < a * (H - y₀) + b * (H - y₁) := by
            by_cases ha_zero : a = 0
            · have hb_one : b = 1 := by linarith
              nlinarith [hy₁_pos]
            · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
              have hterm₀ : 0 < a * (H - y₀) := mul_pos ha_pos hy₀_pos
              have hterm₁ : 0 ≤ b * (H - y₁) :=
                mul_nonneg hb (le_of_lt hy₁_pos)
              linarith
          have hrewrite : H - y = a * (H - y₀) + b * (H - y₁) := by
            nlinarith
          linarith
      have hLeftOpen :
          ∀ {p : EuclideanSpace ℝ (Fin 2)},
            p ∈ segment ℝ (L i) (M i) →
              p ≠ L i →
                -ε < p 0 ∧ p 0 < ε ∧ -H < p 1 ∧ p 1 < H := by
        intro p hpseg hpneL
        rcases hpseg with ⟨a, b, ha, hb, hab, hcomb⟩
        have hx : a * (-ε) + b * 0 = p 0 := by
          have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
          simpa [hLx i, M, middleFromHeights, pointOnMidline] using hx'
        have hy : a * (L i) 1 + b * η i = p 1 := by
          have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb
          simpa [M, middleFromHeights, pointOnMidline] using hy'
        have ha_le_one : a ≤ 1 := by nlinarith
        have ha_lt_one : a < 1 := by
          refine lt_of_le_of_ne ha_le_one ?_
          intro ha_eq
          have hb_zero : b = 0 := by nlinarith
          apply hpneL
          subst a
          subst b
          simpa using hcomb.symm
        have hLy_bounds := abs_lt.mp (hLy i)
        have hη_bounds := abs_lt.mp (hη_bound i)
        have hy_bounds :=
          strict_y_of_combo ha hb hab hLy_bounds.1 hLy_bounds.2
            hη_bounds.1 hη_bounds.2 hy
        constructor
        · nlinarith [hε, hx, ha_lt_one]
        constructor
        · nlinarith [hε, hx, ha]
        exact hy_bounds
      have hRightOpen :
          ∀ {p : EuclideanSpace ℝ (Fin 2)},
            p ∈ segment ℝ (M i) (R i) →
              p ≠ R i →
                -ε < p 0 ∧ p 0 < ε ∧ -H < p 1 ∧ p 1 < H := by
        intro p hpseg hpneR
        rcases hpseg with ⟨a, b, ha, hb, hab, hcomb⟩
        have hx : a * 0 + b * ε = p 0 := by
          have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
          simpa [hRx i, M, middleFromHeights, pointOnMidline] using hx'
        have hy : a * η i + b * (R i) 1 = p 1 := by
          have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb
          simpa [M, middleFromHeights, pointOnMidline] using hy'
        have hb_le_one : b ≤ 1 := by nlinarith
        have hb_lt_one : b < 1 := by
          refine lt_of_le_of_ne hb_le_one ?_
          intro hb_eq
          have ha_zero : a = 0 := by nlinarith
          apply hpneR
          subst a
          subst b
          simpa using hcomb.symm
        have hη_bounds := abs_lt.mp (hη_bound i)
        have hRy_bounds := abs_lt.mp (hRy i)
        have hy_bounds :=
          strict_y_of_combo ha hb hab hη_bounds.1 hη_bounds.2
            hRy_bounds.1 hRy_bounds.2 hy
        constructor
        · nlinarith [hε, hx, hb]
        constructor
        · nlinarith [hε, hx, hb_lt_one]
        exact hy_bounds
      rcases hp with ⟨hpcarrier, hpnotEnds⟩
      have hpneL : p ≠ L i := by
        intro hpL
        apply hpnotEnds
        subst p
        simp
      have hpneR : p ≠ R i := by
        intro hpR
        apply hpnotEnds
        subst p
        simp
      rcases hpcarrier with ⟨n, hn, hpseg⟩
      have hn_cases : n = 0 ∨ n = 1 := by
        have hn' : n + 1 < 3 := by simpa using hn
        omega
      rcases hn_cases with rfl | rfl
      · exact hLeftOpen (by simpa using hpseg) hpneL
      · exact hRightOpen (by simpa using hpseg) hpneR
  have segment_subset_line :
      ∀ x y : EuclideanSpace ℝ (Fin 2), segment ℝ x y ⊆ line[ℝ, x, y] := by
    intro x y z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, _ht, hzt⟩
    rw [← hzt]
    exact AffineMap.lineMap_mem_affineSpan_pair t x y
  have hNoSharedSegments :
      ∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Γ i).vertices.length)
              (hn : n + 1 < (Γ j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                      segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] := by
    intro i j hij hbad
    rcases hbad with ⟨m, n, hm, hn, p, q, hpq, hsub⟩
    have hm_cases : m = 0 ∨ m = 1 := by
      have hm' : m + 1 < 3 := by simpa [Γ] using hm
      omega
    have hn_cases : n = 0 ∨ n = 1 := by
      have hn' : n + 1 < 3 := by simpa [Γ] using hn
      omega
    rcases hη_supportLines hij with ⟨hLL, hLR, hRL, hRR⟩
    rcases hm_cases with rfl | rfl <;> rcases hn_cases with rfl | rfl
    · have hp_i_seg : p ∈ segment ℝ (L i) (M i) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).1
      have hq_i_seg : q ∈ segment ℝ (L i) (M i) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).1
      have hp_j_seg : p ∈ segment ℝ (L j) (M j) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).2
      have hq_j_seg : q ∈ segment ℝ (L j) (M j) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).2
      have hline_i : line[ℝ, p, q] = line[ℝ, L i, M i] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (L i) (M i) hp_i_seg)
          (segment_subset_line (L i) (M i) hq_i_seg) hpq
      have hline_j : line[ℝ, p, q] = line[ℝ, L j, M j] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (L j) (M j) hp_j_seg)
          (segment_subset_line (L j) (M j) hq_j_seg) hpq
      exact hLL (by simpa [M] using hline_i.symm.trans hline_j)
    · have hp_i_seg : p ∈ segment ℝ (L i) (M i) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).1
      have hq_i_seg : q ∈ segment ℝ (L i) (M i) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).1
      have hp_j_seg : p ∈ segment ℝ (M j) (R j) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).2
      have hq_j_seg : q ∈ segment ℝ (M j) (R j) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).2
      have hline_i : line[ℝ, p, q] = line[ℝ, L i, M i] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (L i) (M i) hp_i_seg)
          (segment_subset_line (L i) (M i) hq_i_seg) hpq
      have hline_j : line[ℝ, p, q] = line[ℝ, M j, R j] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (M j) (R j) hp_j_seg)
          (segment_subset_line (M j) (R j) hq_j_seg) hpq
      exact hLR (by simpa [M] using hline_i.symm.trans hline_j)
    · have hp_i_seg : p ∈ segment ℝ (M i) (R i) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).1
      have hq_i_seg : q ∈ segment ℝ (M i) (R i) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).1
      have hp_j_seg : p ∈ segment ℝ (L j) (M j) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).2
      have hq_j_seg : q ∈ segment ℝ (L j) (M j) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).2
      have hline_i : line[ℝ, p, q] = line[ℝ, M i, R i] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (M i) (R i) hp_i_seg)
          (segment_subset_line (M i) (R i) hq_i_seg) hpq
      have hline_j : line[ℝ, p, q] = line[ℝ, L j, M j] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (L j) (M j) hp_j_seg)
          (segment_subset_line (L j) (M j) hq_j_seg) hpq
      exact hRL (by simpa [M] using hline_i.symm.trans hline_j)
    · have hp_i_seg : p ∈ segment ℝ (M i) (R i) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).1
      have hq_i_seg : q ∈ segment ℝ (M i) (R i) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).1
      have hp_j_seg : p ∈ segment ℝ (M j) (R j) := by
        simpa [Γ] using (hsub (left_mem_segment ℝ p q)).2
      have hq_j_seg : q ∈ segment ℝ (M j) (R j) := by
        simpa [Γ] using (hsub (right_mem_segment ℝ p q)).2
      have hline_i : line[ℝ, p, q] = line[ℝ, M i, R i] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (M i) (R i) hp_i_seg)
          (segment_subset_line (M i) (R i) hq_i_seg) hpq
      have hline_j : line[ℝ, p, q] = line[ℝ, M j, R j] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne
          (segment_subset_line (M j) (R j) hp_j_seg)
          (segment_subset_line (M j) (R j) hq_j_seg) hpq
      exact hRR (by simpa [M] using hline_i.symm.trans hline_j)
  have hleft_x_zero :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (L i) (M i) → p 0 = 0 → p = M i := by
    intro i p hp hp0
    rcases hp with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * (-ε) + b * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hLx i, M, middleFromHeights, pointOnMidline] using hx'
    have ha0 : a = 0 := by nlinarith [ha, hε, hx, hp0]
    have hb1 : b = 1 := by nlinarith
    subst a
    subst b
    simpa using hcomb.symm
  have hright_x_zero :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (M i) (R i) → p 0 = 0 → p = M i := by
    intro i p hp hp0
    rcases hp with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * 0 + b * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hRx i, M, middleFromHeights, pointOnMidline] using hx'
    have hb0 : b = 0 := by nlinarith [hb, hε, hx, hp0]
    have ha1 : a = 1 := by nlinarith
    subst a
    subst b
    simpa using hcomb.symm
  have hleft_x_nonpos :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (L i) (M i) → p 0 ≤ 0 := by
    intro i p hp
    rcases hp with ⟨a, b, ha, _hb, _hab, hcomb⟩
    have hx : a * (-ε) + b * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hLx i, M, middleFromHeights, pointOnMidline] using hx'
    nlinarith [ha, hε, hx]
  have hright_x_nonneg :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (M i) (R i) → 0 ≤ p 0 := by
    intro i p hp
    rcases hp with ⟨_a, b, _ha, hb, _hab, hcomb⟩
    have hx : _a * 0 + b * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hRx i, M, middleFromHeights, pointOnMidline] using hx'
    nlinarith [hb, hε, hx]
  have hleft_left_disjoint :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ segment ℝ (L i) (M i) →
          p ∈ segment ℝ (L j) (M j) → False := by
    intro i j p hij hpi hpj
    rcases hpi with ⟨a, b, ha, hb, hab, hcomb_i⟩
    rcases hpj with ⟨c, d, hc, hd, hcd, hcomb_j⟩
    have hx_i : a * (-ε) + b * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb_i
      simpa [hLx i, M, middleFromHeights, pointOnMidline] using hx'
    have hx_j : c * (-ε) + d * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb_j
      simpa [hLx j, M, middleFromHeights, pointOnMidline] using hx'
    have hac : a = c := by nlinarith [hε, hx_i, hx_j]
    have hbd : b = d := by nlinarith [hab, hcd, hac]
    have hy_i : a * (L i) 1 + b * η i = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb_i
      simpa [M, middleFromHeights, pointOnMidline] using hy'
    have hy_j : c * (L j) 1 + d * η j = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb_j
      simpa [M, middleFromHeights, pointOnMidline] using hy'
    have hLy_ne : (L i) 1 ≠ (L j) 1 := by
      intro hy
      apply hij
      apply hLinj
      ext k
      fin_cases k
      · simpa using (hLx i).trans (hLx j).symm
      · exact hy
    rcases lt_or_gt_of_ne hLy_ne with hlt | hgt
    · have hηlt : η i < η j := (hη_order i j).2 hlt
      have hy_lt : a * (L i) 1 + b * η i < a * (L j) 1 + b * η j := by
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith [ha0, hab]
          simpa [ha0, hb1] using hηlt
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have h₁ : 0 < a * ((L j) 1 - (L i) 1) :=
            mul_pos ha_pos (sub_pos.mpr hlt)
          have h₂ : 0 ≤ b * (η j - η i) :=
            mul_nonneg hb (sub_nonneg.mpr (le_of_lt hηlt))
          have hsum : 0 < a * ((L j) 1 - (L i) 1) + b * (η j - η i) :=
            add_pos_of_pos_of_nonneg h₁ h₂
          have hdiff :
              a * (L j) 1 + b * η j - (a * (L i) 1 + b * η i) =
                a * ((L j) 1 - (L i) 1) + b * (η j - η i) := by
            ring
          linarith [hsum, hdiff]
      have hy_j' : a * (L j) 1 + b * η j = p 1 := by
        simpa [← hac, ← hbd] using hy_j
      rw [hy_i, hy_j'] at hy_lt
      exact (lt_irrefl (p 1)) hy_lt
    · have hηlt : η j < η i := (hη_order j i).2 hgt
      have hy_lt : c * (L j) 1 + d * η j < c * (L i) 1 + d * η i := by
        by_cases hc0 : c = 0
        · have hd1 : d = 1 := by linarith [hc0, hcd]
          simpa [hc0, hd1] using hηlt
        · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
          have h₁ : 0 < c * ((L i) 1 - (L j) 1) :=
            mul_pos hc_pos (sub_pos.mpr hgt)
          have h₂ : 0 ≤ d * (η i - η j) :=
            mul_nonneg hd (sub_nonneg.mpr (le_of_lt hηlt))
          have hsum : 0 < c * ((L i) 1 - (L j) 1) + d * (η i - η j) :=
            add_pos_of_pos_of_nonneg h₁ h₂
          have hdiff :
              c * (L i) 1 + d * η i - (c * (L j) 1 + d * η j) =
                c * ((L i) 1 - (L j) 1) + d * (η i - η j) := by
            ring
          linarith [hsum, hdiff]
      have hy_i' : c * (L i) 1 + d * η i = p 1 := by
        simpa [hac, hbd] using hy_i
      rw [hy_j, hy_i'] at hy_lt
      exact (lt_irrefl (p 1)) hy_lt
  have hleft_right_disjoint :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ segment ℝ (L i) (M i) →
          p ∈ segment ℝ (M j) (R j) → False := by
    intro i j p hij hpL hpR
    have hp0 : p 0 = 0 :=
      le_antisymm (hleft_x_nonpos hpL) (hright_x_nonneg hpR)
    have hpMi : p = M i := hleft_x_zero hpL hp0
    have hpMj : p = M j := hright_x_zero hpR hp0
    exact hij (hM_inj (hpMi.symm.trans hpMj))
  have hright_left_disjoint :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ segment ℝ (M i) (R i) →
          p ∈ segment ℝ (L j) (M j) → False := by
    intro i j p hij hpR hpL
    exact hleft_right_disjoint (i := j) (j := i) (p := p) (Ne.symm hij) hpL hpR
  have hcommon_right :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              p ∈ openSegment ℝ (M i) (R i) ∧
                p ∈ openSegment ℝ (M j) (R j) := by
    intro i j p hij hpi hpj
    simp [Γ] at hpi hpj
    rcases hpi with ⟨hpi_carrier, hpneLi, hpneRi⟩
    rcases hpj with ⟨hpj_carrier, hpneLj, hpneRj⟩
    rcases hpi_carrier with ⟨m, hm, hp_i_seg⟩
    rcases hpj_carrier with ⟨n, hn, hp_j_seg⟩
    have hm_cases : m = 0 ∨ m = 1 := by
      have hm' : m + 1 < 3 := by simpa using hm
      omega
    have hn_cases : n = 0 ∨ n = 1 := by
      have hn' : n + 1 < 3 := by simpa using hn
      omega
    rcases hm_cases with rfl | rfl <;> rcases hn_cases with rfl | rfl
    · have hp_i_left : p ∈ segment ℝ (L i) (M i) := by simpa using hp_i_seg
      have hp_j_left : p ∈ segment ℝ (L j) (M j) := by simpa using hp_j_seg
      exact (hleft_left_disjoint hij hp_i_left hp_j_left).elim
    · have hp_i_left : p ∈ segment ℝ (L i) (M i) := by simpa using hp_i_seg
      have hp_j_right : p ∈ segment ℝ (M j) (R j) := by simpa using hp_j_seg
      exact (hleft_right_disjoint hij hp_i_left hp_j_right).elim
    · have hp_i_right : p ∈ segment ℝ (M i) (R i) := by simpa using hp_i_seg
      have hp_j_left : p ∈ segment ℝ (L j) (M j) := by simpa using hp_j_seg
      exact (hright_left_disjoint hij hp_i_right hp_j_left).elim
    · have hp_i_right : p ∈ segment ℝ (M i) (R i) := by simpa using hp_i_seg
      have hp_j_right : p ∈ segment ℝ (M j) (R j) := by simpa using hp_j_seg
      have hMi_ne_p : M i ≠ p := by
        intro hMip
        have hp0 : p 0 = 0 := by
          rw [← hMip]
          simp [M, middleFromHeights, pointOnMidline]
        have hpMj : p = M j := hright_x_zero hp_j_right hp0
        exact hij (hM_inj (hMip.trans hpMj))
      have hRi_ne_p : R i ≠ p := Ne.symm hpneRi
      have hMj_ne_p : M j ≠ p := by
        intro hMjp
        have hp0 : p 0 = 0 := by
          rw [← hMjp]
          simp [M, middleFromHeights, pointOnMidline]
        have hpMi : p = M i := hright_x_zero hp_i_right hp0
        exact hij (Eq.symm (hM_inj (hMjp.trans hpMi)))
      have hRj_ne_p : R j ≠ p := Ne.symm hpneRj
      exact
        ⟨mem_openSegment_of_ne_left_right hMi_ne_p hRi_ne_p hp_i_right,
          mem_openSegment_of_ne_left_right hMj_ne_p hRj_ne_p hp_j_right⟩
  refine ⟨M, Γ, hM_inj, hM_coord, hM_order, hΓ_basic, hNoSharedSegments, ?_, ?_, ?_⟩
  · intro i j k p hij hik hjk hpi hpj hpk
    have hipj_right := hcommon_right hij hpi hpj
    have hik_right := hcommon_right hik hpi hpk
    exact hη_noRightTriple hij hik hjk hipj_right.1 hipj_right.2 hik_right.2
  · intro i j p hij hpi hpj
    have hp_right := hcommon_right hij hpi hpj
    refine ⟨1, 1, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [Γ]
    · norm_num [Γ]
    · exact openSegment_subset_segment ℝ (M i) (R i) hp_right.1
    · exact openSegment_subset_segment ℝ (M j) (R j) hp_right.2
    · simpa [Γ, M] using hη_rightNonparallel hij
  · intro i j p q hij hpi hpj hqi hqj
    by_contra hpq
    have hp_right := hcommon_right hij hpi hpj
    have hq_right := hcommon_right hij hqi hqj
    have hp_i_line : p ∈ line[ℝ, M i, R i] :=
      segment_subset_line (M i) (R i)
        (openSegment_subset_segment ℝ (M i) (R i) hp_right.1)
    have hq_i_line : q ∈ line[ℝ, M i, R i] :=
      segment_subset_line (M i) (R i)
        (openSegment_subset_segment ℝ (M i) (R i) hq_right.1)
    have hp_j_line : p ∈ line[ℝ, M j, R j] :=
      segment_subset_line (M j) (R j)
        (openSegment_subset_segment ℝ (M j) (R j) hp_right.2)
    have hq_j_line : q ∈ line[ℝ, M j, R j] :=
      segment_subset_line (M j) (R j)
        (openSegment_subset_segment ℝ (M j) (R j) hq_right.2)
    have hline_i : line[ℝ, p, q] = line[ℝ, M i, R i] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_i_line hq_i_line hpq
    have hline_j : line[ℝ, p, q] = line[ℝ, M j, R j] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_j_line hq_j_line hpq
    have hline_eq : line[ℝ, M j, R j] = line[ℝ, M i, R i] :=
      hline_j.symm.trans hline_i
    have hdir_le :
        (line[ℝ, M j, R j]).direction ≤ (line[ℝ, M i, R i]).direction := by
      rw [hline_eq]
    have hparallel :
        ∃ t : ℝ, t • (R i -ᵥ M i) = R j -ᵥ M j := by
      exact
        (AffineSubspace.direction_affineSpan_pair_le_iff_exists_smul
          (k := ℝ) (p₁ := M j) (q₁ := R j) (p₂ := M i) (q₂ := R i)).1 hdir_le
    rcases hparallel with ⟨t, ht⟩
    exact (hη_rightNonparallel hij) ⟨t, by simpa [M] using ht.symm⟩
