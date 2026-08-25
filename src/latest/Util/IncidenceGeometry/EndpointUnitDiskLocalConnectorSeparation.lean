import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointUnitDiskLocalConnectorSeparation {κ : Type*}
    (toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (m α β : κ → ℝ) (ε : ℝ)
    (L R M : κ → EuclideanSpace ℝ (Fin 2))
    (htoWorld_inj : Function.Injective toWorld)
    (hframe_segment : ∀ x y : EuclideanSpace ℝ (Fin 2),
      toWorld '' segment ℝ x y = segment ℝ (toWorld x) (toWorld y))
    (hm_inj : Function.Injective m)
    (hε : 0 < ε)
    (hα : ∀ i : κ, ε < α i)
    (hβ : ∀ i : κ, ε < β i)
    (hLx : ∀ i : κ, (L i) 0 = -ε)
    (hLy : ∀ i : κ, (L i) 1 = -(m i * ε))
    (hRx : ∀ i : κ, (R i) 0 = ε)
    (hRy : ∀ i : κ, (R i) 1 = m i * ε)
    (hM0 : ∀ i : κ, (M i) 0 = 0)
    (hLinj : Function.Injective L)
    (hRinj : Function.Injective R) :
    let point : ℝ → ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun x y => WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then x else y)
    (∀ ⦃i j : κ⦄,
      i ≠ j →
        segment ℝ
            (toWorld (point (-(α i)) (-(m i * α i)))) (toWorld (L i)) ∩
          segment ℝ
            (toWorld (point (-(α j)) (-(m j * α j)))) (toWorld (L j)) =
        ∅) ∧
      (∀ i j : κ,
        segment ℝ
            (toWorld (point (-(α i)) (-(m i * α i)))) (toWorld (L i)) ∩
          segment ℝ (toWorld (R j)) (toWorld (point (β j) (m j * β j))) =
        ∅) ∧
        (∀ ⦃i j : κ⦄,
          i ≠ j →
            segment ℝ (toWorld (R i)) (toWorld (point (β i) (m i * β i))) ∩
              segment ℝ (toWorld (R j)) (toWorld (point (β j) (m j * β j))) =
            ∅) ∧
          (∀ ⦃i j : κ⦄,
            i ≠ j →
              segment ℝ
                  (toWorld (point (-(α i)) (-(m i * α i)))) (toWorld (L i)) ∩
                segment ℝ (toWorld (L j)) (toWorld (M j)) =
              ∅) ∧
            (∀ i j : κ,
              segment ℝ
                  (toWorld (point (-(α i)) (-(m i * α i)))) (toWorld (L i)) ∩
                segment ℝ (toWorld (M j)) (toWorld (R j)) =
              ∅) ∧
              (∀ i j : κ,
                segment ℝ (toWorld (R i)) (toWorld (point (β i) (m i * β i))) ∩
                  segment ℝ (toWorld (L j)) (toWorld (M j)) =
                ∅) ∧
                (∀ ⦃i j : κ⦄,
                  i ≠ j →
                    segment ℝ (toWorld (R i)) (toWorld (point (β i) (m i * β i))) ∩
                      segment ℝ (toWorld (M j)) (toWorld (R j)) =
                    ∅) := by
  intro point
  let A : κ → EuclideanSpace ℝ (Fin 2) :=
    fun i => point (-(α i)) (-(m i * α i))
  let B : κ → EuclideanSpace ℝ (Fin 2) :=
    fun i => point (β i) (m i * β i)
  have hA0 : ∀ i : κ, (A i) 0 = -(α i) := by
    intro i
    simp [A, point]
  have hA1 : ∀ i : κ, (A i) 1 = -(m i * α i) := by
    intro i
    simp [A, point]
  have hB0 : ∀ i : κ, (B i) 0 = β i := by
    intro i
    simp [B, point]
  have hB1 : ∀ i : κ, (B i) 1 = m i * β i := by
    intro i
    simp [B, point]
  have mem_segment_preimage :
      ∀ {X Y p : EuclideanSpace ℝ (Fin 2)},
        p ∈ segment ℝ (toWorld X) (toWorld Y) →
          ∃ q : EuclideanSpace ℝ (Fin 2),
            q ∈ segment ℝ X Y ∧ toWorld q = p := by
    intro X Y p hp
    have hp' : p ∈ toWorld '' segment ℝ X Y := by
      simpa [hframe_segment X Y] using hp
    exact hp'
  have segment_coord_le :
      ∀ {X Y q : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        X 0 ≤ t →
          Y 0 ≤ t →
            q ∈ segment ℝ X Y →
              q 0 ≤ t := by
    intro X Y q t hX hY hq
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * X 0 + b * Y 0 = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa using hx'
    have hXa : a * X 0 ≤ a * t := mul_le_mul_of_nonneg_left hX ha
    have hYb : b * Y 0 ≤ b * t := mul_le_mul_of_nonneg_left hY hb
    calc
      q 0 = a * X 0 + b * Y 0 := hx.symm
      _ ≤ a * t + b * t := add_le_add hXa hYb
      _ = t := by rw [← add_mul, hab, one_mul]
  have segment_coord_ge :
      ∀ {X Y q : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        t ≤ X 0 →
          t ≤ Y 0 →
            q ∈ segment ℝ X Y →
              t ≤ q 0 := by
    intro X Y q t hX hY hq
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * X 0 + b * Y 0 = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa using hx'
    have hXa : a * t ≤ a * X 0 := mul_le_mul_of_nonneg_left hX ha
    have hYb : b * t ≤ b * Y 0 := mul_le_mul_of_nonneg_left hY hb
    calc
      t = a * t + b * t := by rw [← add_mul, hab, one_mul]
      _ ≤ a * X 0 + b * Y 0 := add_le_add hXa hYb
      _ = q 0 := hx
  have eq_right_of_mem_segment_coord :
      ∀ {X Y q : EuclideanSpace ℝ (Fin 2)},
        X 0 < Y 0 →
          q ∈ segment ℝ X Y →
            q 0 = Y 0 →
              q = Y := by
    intro X Y q hXY hq hq0
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hxq : a * X 0 + b * Y 0 = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa using hx'
    have hx : a * X 0 + b * Y 0 = Y 0 := by
      rw [hxq, hq0]
    have ha0 : a = 0 := by
      by_contra ha_ne
      have ha_pos : 0 < a :=
        lt_of_le_of_ne ha (fun h0a => ha_ne h0a.symm)
      have hlt_left : a * X 0 < a * Y 0 :=
        mul_lt_mul_of_pos_left hXY ha_pos
      have hlt_sum : a * X 0 + b * Y 0 < a * Y 0 + b * Y 0 := by
        nlinarith [hlt_left]
      have hright : a * Y 0 + b * Y 0 = Y 0 := by
        rw [← add_mul, hab, one_mul]
      rw [hx, hright] at hlt_sum
      exact (lt_irrefl (Y 0)) hlt_sum
    have hb1 : b = 1 := by linarith
    have hYq : Y = q := by
      simpa [ha0, hb1] using hcomb
    exact hYq.symm
  have eq_left_of_mem_segment_coord :
      ∀ {X Y q : EuclideanSpace ℝ (Fin 2)},
        X 0 < Y 0 →
          q ∈ segment ℝ X Y →
            q 0 = X 0 →
              q = X := by
    intro X Y q hXY hq hq0
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hxq : a * X 0 + b * Y 0 = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa using hx'
    have hx : a * X 0 + b * Y 0 = X 0 := by
      rw [hxq, hq0]
    have hb0 : b = 0 := by
      by_contra hb_ne
      have hb_pos : 0 < b :=
        lt_of_le_of_ne hb (fun h0b => hb_ne h0b.symm)
      have hlt_right : b * X 0 < b * Y 0 :=
        mul_lt_mul_of_pos_left hXY hb_pos
      have hlt_sum : a * X 0 + b * X 0 < a * X 0 + b * Y 0 := by
        nlinarith [hlt_right]
      have hleft : a * X 0 + b * X 0 = X 0 := by
        rw [← add_mul, hab, one_mul]
      rw [hx, hleft] at hlt_sum
      exact (lt_irrefl (X 0)) hlt_sum
    have ha1 : a = 1 := by linarith
    have hXq : X = q := by
      simpa [ha1, hb0] using hcomb
    exact hXq.symm
  have left_slope :
      ∀ {i : κ} {q : EuclideanSpace ℝ (Fin 2)},
        q ∈ segment ℝ (A i) (L i) →
          q 1 = m i * q 0 := by
    intro i q hq
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * (-(α i)) + b * (-ε) = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa [hA0 i, hLx i] using hx'
    have hy : a * (-(m i * α i)) + b * (-(m i * ε)) = q 1 := by
      have hy' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hcomb
      simpa [hA1 i, hLy i] using hy'
    calc
      q 1 = a * (-(m i * α i)) + b * (-(m i * ε)) := hy.symm
      _ = m i * (a * (-(α i)) + b * (-ε)) := by ring
      _ = m i * q 0 := by rw [hx]
  have right_slope :
      ∀ {i : κ} {q : EuclideanSpace ℝ (Fin 2)},
        q ∈ segment ℝ (R i) (B i) →
          q 1 = m i * q 0 := by
    intro i q hq
    rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * ε + b * β i = q 0 := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
      simpa [hRx i, hB0 i] using hx'
    have hy : a * (m i * ε) + b * (m i * β i) = q 1 := by
      have hy' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hcomb
      simpa [hRy i, hB1 i] using hy'
    calc
      q 1 = a * (m i * ε) + b * (m i * β i) := hy.symm
      _ = m i * (a * ε + b * β i) := by ring
      _ = m i * q 0 := by rw [hx]
  have transported_empty_of_standard_empty :
      ∀ {X Y Z W : EuclideanSpace ℝ (Fin 2)},
        segment ℝ X Y ∩ segment ℝ Z W = ∅ →
          segment ℝ (toWorld X) (toWorld Y) ∩
              segment ℝ (toWorld Z) (toWorld W) =
            ∅ := by
    intro X Y Z W hempty
    ext p
    constructor
    · intro hp
      rcases mem_segment_preimage hp.1 with ⟨q₁, hq₁, hq₁eq⟩
      rcases mem_segment_preimage hp.2 with ⟨q₂, hq₂, hq₂eq⟩
      have hq₂_eq_q₁ : q₂ = q₁ := htoWorld_inj (by rw [hq₂eq, hq₁eq])
      have hq₁_both : q₁ ∈ segment ℝ X Y ∩ segment ℝ Z W :=
        ⟨hq₁, by simpa [hq₂_eq_q₁] using hq₂⟩
      rw [hempty] at hq₁_both
      exact hq₁_both
    · intro hp
      cases hp
  have left_left_standard :
      ∀ ⦃i j : κ⦄,
        i ≠ j →
          segment ℝ (A i) (L i) ∩ segment ℝ (A j) (L j) = ∅ := by
    intro i j hij
    ext q
    constructor
    · intro hq
      have hq_le : q 0 ≤ -ε :=
        segment_coord_le (by linarith [hA0 i, hα i]) (by linarith [hLx i]) hq.1
      have hq0_ne : q 0 ≠ 0 := by linarith [hε, hq_le]
      have hqi := left_slope (i := i) hq.1
      have hqj := left_slope (i := j) hq.2
      have hm_eq : m i = m j := by
        have hmul : m i * q 0 = m j * q 0 := by linarith
        exact mul_right_cancel₀ hq0_ne hmul
      exact hij (hm_inj hm_eq)
    · intro hp
      cases hp
  have left_right_standard :
      ∀ i j : κ,
        segment ℝ (A i) (L i) ∩ segment ℝ (R j) (B j) = ∅ := by
    intro i j
    ext q
    constructor
    · intro hq
      have hleft : q 0 ≤ -ε :=
        segment_coord_le (by linarith [hA0 i, hα i]) (by linarith [hLx i]) hq.1
      have hright : ε ≤ q 0 :=
        segment_coord_ge (by linarith [hRx j]) (by linarith [hB0 j, hβ j]) hq.2
      linarith
    · intro hp
      cases hp
  have right_right_standard :
      ∀ ⦃i j : κ⦄,
        i ≠ j →
          segment ℝ (R i) (B i) ∩ segment ℝ (R j) (B j) = ∅ := by
    intro i j hij
    ext q
    constructor
    · intro hq
      have hq_ge : ε ≤ q 0 :=
        segment_coord_ge (by linarith [hRx i]) (by linarith [hB0 i, hβ i]) hq.1
      have hq0_ne : q 0 ≠ 0 := by linarith [hε, hq_ge]
      have hqi := right_slope (i := i) hq.1
      have hqj := right_slope (i := j) hq.2
      have hm_eq : m i = m j := by
        have hmul : m i * q 0 = m j * q 0 := by linarith
        exact mul_right_cancel₀ hq0_ne hmul
      exact hij (hm_inj hm_eq)
    · intro hp
      cases hp
  have left_middle_left_standard :
      ∀ ⦃i j : κ⦄,
        i ≠ j →
          segment ℝ (A i) (L i) ∩ segment ℝ (L j) (M j) = ∅ := by
    intro i j hij
    ext q
    constructor
    · intro hq
      have hle : q 0 ≤ -ε :=
        segment_coord_le (by linarith [hA0 i, hα i]) (by linarith [hLx i]) hq.1
      have hge : -ε ≤ q 0 :=
        segment_coord_ge (by linarith [hLx j]) (by linarith [hM0 j, hε]) hq.2
      have hq0 : q 0 = -ε := le_antisymm hle hge
      have hqLi : q = L i :=
        eq_right_of_mem_segment_coord
          (by linarith [hA0 i, hLx i, hα i]) hq.1 (by simpa [hLx i] using hq0)
      have hqLj : q = L j :=
        eq_left_of_mem_segment_coord
          (by linarith [hLx j, hM0 j, hε]) hq.2 (by simpa [hLx j] using hq0)
      have hLL : L i = L j := by
        rw [← hqLi, hqLj]
      exact hij (hLinj hLL)
    · intro hp
      cases hp
  have left_middle_right_standard :
      ∀ i j : κ,
        segment ℝ (A i) (L i) ∩ segment ℝ (M j) (R j) = ∅ := by
    intro i j
    ext q
    constructor
    · intro hq
      have hle : q 0 ≤ -ε :=
        segment_coord_le (by linarith [hA0 i, hα i]) (by linarith [hLx i]) hq.1
      have hge : 0 ≤ q 0 :=
        segment_coord_ge (by linarith [hM0 j]) (by linarith [hRx j, hε]) hq.2
      linarith
    · intro hp
      cases hp
  have right_middle_left_standard :
      ∀ i j : κ,
        segment ℝ (R i) (B i) ∩ segment ℝ (L j) (M j) = ∅ := by
    intro i j
    ext q
    constructor
    · intro hq
      have hge : ε ≤ q 0 :=
        segment_coord_ge (by linarith [hRx i]) (by linarith [hB0 i, hβ i]) hq.1
      have hle : q 0 ≤ 0 :=
        segment_coord_le (by linarith [hLx j, hε]) (by linarith [hM0 j]) hq.2
      linarith
    · intro hp
      cases hp
  have right_middle_right_standard :
      ∀ ⦃i j : κ⦄,
        i ≠ j →
          segment ℝ (R i) (B i) ∩ segment ℝ (M j) (R j) = ∅ := by
    intro i j hij
    ext q
    constructor
    · intro hq
      have hge : ε ≤ q 0 :=
        segment_coord_ge (by linarith [hRx i]) (by linarith [hB0 i, hβ i]) hq.1
      have hle : q 0 ≤ ε :=
        segment_coord_le (by linarith [hM0 j, hε]) (by linarith [hRx j]) hq.2
      have hq0 : q 0 = ε := le_antisymm hle hge
      have hqRi : q = R i :=
        eq_left_of_mem_segment_coord
          (by linarith [hRx i, hB0 i, hβ i]) hq.1 (by simpa [hRx i] using hq0)
      have hqRj : q = R j :=
        eq_right_of_mem_segment_coord
          (by linarith [hM0 j, hRx j, hε]) hq.2 (by simpa [hRx j] using hq0)
      have hRR : R i = R j := by
        rw [← hqRi, hqRj]
      exact hij (hRinj hRR)
    · intro hp
      cases hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa [A] using transported_empty_of_standard_empty (left_left_standard hij)
  · intro i j
    simpa [A, B] using transported_empty_of_standard_empty (left_right_standard i j)
  · intro i j hij
    simpa [B] using transported_empty_of_standard_empty (right_right_standard hij)
  · intro i j hij
    simpa [A] using transported_empty_of_standard_empty (left_middle_left_standard hij)
  · intro i j
    simpa [A] using transported_empty_of_standard_empty (left_middle_right_standard i j)
  · intro i j
    simpa [B] using transported_empty_of_standard_empty (right_middle_left_standard i j)
  · intro i j hij
    simpa [B] using transported_empty_of_standard_empty (right_middle_right_standard hij)
