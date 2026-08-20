import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section


-- [TABLET NODE: EndpointRectangularWireCrossingsOpen]
lemma EndpointRectangularWireCrossingsOpen {ι : Type*}
    (ε : ℝ) (L M R : ι → EuclideanSpace ℝ (Fin 2))
    (Γ : ι → PolygonalArc)
    (hε : 0 < ε)
    (hLx : ∀ i, (L i) 0 = -ε)
    (hRx : ∀ i, (R i) 0 = ε)
    (hLinj : Function.Injective L)
    (hMinj : Function.Injective M)
    (hMx : ∀ i, (M i) 0 = 0)
    (hMorder : ∀ i j, (M i) 1 < (M j) 1 ↔ (L i) 1 < (L j) 1)
    (hΓvertices : ∀ i, (Γ i).vertices = [L i, M i, R i])
    (hΓtarget : ∀ i, (Γ i).target = R i) :
    ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      i ≠ j →
        p ∈ (Γ i).relativeInterior →
          p ∈ (Γ j).relativeInterior →
            p ∈ openSegment ℝ (M i) (R i) ∧
              p ∈ openSegment ℝ (M j) (R j) := by
-- BODY
  have hleft_x_zero :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (L i) (M i) → p 0 = 0 → p = M i := by
    intro i p hp hp0
    rcases hp with ⟨a, b, ha, hb, hab, hcomb⟩
    have hx : a * (-ε) + b * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hLx i, hMx i] using hx'
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
      simpa [hRx i, hMx i] using hx'
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
      simpa [hLx i, hMx i] using hx'
    nlinarith [ha, hε, hx]
  have hright_x_nonneg :
      ∀ ⦃i : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (M i) (R i) → 0 ≤ p 0 := by
    intro i p hp
    rcases hp with ⟨a, b, _ha, hb, _hab, hcomb⟩
    have hx : a * 0 + b * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb
      simpa [hRx i, hMx i] using hx'
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
      simpa [hLx i, hMx i] using hx'
    have hx_j : c * (-ε) + d * 0 = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hcomb_j
      simpa [hLx j, hMx j] using hx'
    have hac : a = c := by nlinarith [hε, hx_i, hx_j]
    have hbd : b = d := by nlinarith [hab, hcd, hac]
    have hy_i : a * (L i) 1 + b * (M i) 1 = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb_i
      simpa using hy'
    have hy_j : c * (L j) 1 + d * (M j) 1 = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hcomb_j
      simpa using hy'
    have hLy_ne : (L i) 1 ≠ (L j) 1 := by
      intro hy
      apply hij
      apply hLinj
      ext k
      fin_cases k
      · simpa using (hLx i).trans (hLx j).symm
      · exact hy
    rcases lt_or_gt_of_ne hLy_ne with hlt | hgt
    · have hMlt : (M i) 1 < (M j) 1 := (hMorder i j).2 hlt
      have hy_lt : a * (L i) 1 + b * (M i) 1 <
          a * (L j) 1 + b * (M j) 1 := by
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith [ha0, hab]
          simpa [ha0, hb1] using hMlt
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have h₁ : 0 < a * ((L j) 1 - (L i) 1) :=
            mul_pos ha_pos (sub_pos.mpr hlt)
          have h₂ : 0 ≤ b * ((M j) 1 - (M i) 1) :=
            mul_nonneg hb (sub_nonneg.mpr (le_of_lt hMlt))
          nlinarith
      have hy_j' : a * (L j) 1 + b * (M j) 1 = p 1 := by
        simpa [← hac, ← hbd] using hy_j
      rw [hy_i, hy_j'] at hy_lt
      exact (lt_irrefl (p 1)) hy_lt
    · have hMlt : (M j) 1 < (M i) 1 := (hMorder j i).2 hgt
      have hy_lt : c * (L j) 1 + d * (M j) 1 <
          c * (L i) 1 + d * (M i) 1 := by
        by_cases hc0 : c = 0
        · have hd1 : d = 1 := by linarith [hc0, hcd]
          simpa [hc0, hd1] using hMlt
        · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
          have h₁ : 0 < c * ((L i) 1 - (L j) 1) :=
            mul_pos hc_pos (sub_pos.mpr hgt)
          have h₂ : 0 ≤ d * ((M i) 1 - (M j) 1) :=
            mul_nonneg hd (sub_nonneg.mpr (le_of_lt hMlt))
          nlinarith
      have hy_i' : c * (L i) 1 + d * (M i) 1 = p 1 := by
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
    exact hij (hMinj (hpMi.symm.trans hpMj))
  have hright_left_disjoint :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → p ∈ segment ℝ (M i) (R i) →
          p ∈ segment ℝ (L j) (M j) → False := by
    intro i j p hij hpR hpL
    exact hleft_right_disjoint (Ne.symm hij) hpL hpR
  intro i j p hij hpi hpj
  rw [(Γ i).relativeInterior_eq, (Γ i).carrier_eq] at hpi
  rw [(Γ j).relativeInterior_eq, (Γ j).carrier_eq] at hpj
  rcases hpi with ⟨⟨mi, hmi, hp_i_seg⟩, hpne_i⟩
  rcases hpj with ⟨⟨mj, hmj, hp_j_seg⟩, hpne_j⟩
  have hmi_cases : mi = 0 ∨ mi = 1 := by
    have : mi + 1 < 3 := by simpa [hΓvertices i] using hmi
    omega
  have hmj_cases : mj = 0 ∨ mj = 1 := by
    have : mj + 1 < 3 := by simpa [hΓvertices j] using hmj
    omega
  rcases hmi_cases with rfl | rfl <;> rcases hmj_cases with rfl | rfl
  · exact False.elim (hleft_left_disjoint hij (by simpa [hΓvertices i] using hp_i_seg)
      (by simpa [hΓvertices j] using hp_j_seg))
  · exact False.elim (hleft_right_disjoint hij (by simpa [hΓvertices i] using hp_i_seg)
      (by simpa [hΓvertices j] using hp_j_seg))
  · exact False.elim (hright_left_disjoint hij (by simpa [hΓvertices i] using hp_i_seg)
      (by simpa [hΓvertices j] using hp_j_seg))
  · have hp_i_right : p ∈ segment ℝ (M i) (R i) := by
      simpa [hΓvertices i] using hp_i_seg
    have hp_j_right : p ∈ segment ℝ (M j) (R j) := by
      simpa [hΓvertices j] using hp_j_seg
    have hMi_ne_p : M i ≠ p := by
      intro hMip
      have hp0 : p 0 = 0 := by simpa [← hMip] using hMx i
      have hpMj : p = M j := hright_x_zero hp_j_right hp0
      exact hij (hMinj (hMip.trans hpMj))
    have hRi_ne_p : R i ≠ p := by
      intro hRip
      apply hpne_i
      right
      simpa [hΓtarget i, hRip]
    have hMj_ne_p : M j ≠ p := by
      intro hMjp
      have hp0 : p 0 = 0 := by simpa [← hMjp] using hMx j
      have hpMi : p = M i := hright_x_zero hp_i_right hp0
      exact hij (Eq.symm (hMinj (hMjp.trans hpMi)))
    have hRj_ne_p : R j ≠ p := by
      intro hRjp
      apply hpne_j
      right
      simpa [hΓtarget j, hRjp]
    exact
      ⟨mem_openSegment_of_ne_left_right hMi_ne_p hRi_ne_p hp_i_right,
        mem_openSegment_of_ne_left_right hMj_ne_p hRj_ne_p hp_j_right⟩
