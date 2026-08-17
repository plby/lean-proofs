import ErdosProblems.Erdos780.External.AllowedComplex
import ErdosProblems.Erdos780.External.PositiveAllowed
import ErdosProblems.Erdos780.External.SignedTargetOrbits
import ErdosProblems.Erdos780.External.CyclicExactness

namespace AllowedDescent

open TargetChains

noncomputable section

variable {p m alpha : ℕ} [NeZero p]

abbrev Vertex := ZMod p × Fin m
abbrev Total := TargetOrbits.TotalChain p m alpha
abbrev PA := AllowedComplex.PositiveAllowed p m alpha

noncomputable local instance targetOrder : LinearOrder (Vertex (p := p) (m := m)) :=
  LabelChainMap.targetLinearOrder

theorem single_empty_mem_allowed (r : ℤ) :
    Finsupp.single (∅ : Finset (Vertex (p := p) (m := m))) r ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.mem_allowedChains]
  intro s hs
  by_cases h : s = ∅
  · subst s
    exact AllowedFaces.isAllowed_empty p m alpha
  · exact ((Finsupp.mem_support_iff.mp hs) (by simp [h])).elim

noncomputable def positiveBoundary : PA (p := p) (m := m) (alpha := alpha) →ₗ[ℤ]
    PA (p := p) (m := m) (alpha := alpha) :=
  (PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))).domRestrict
      (AllowedComplex.PositiveAllowed p m alpha) |>.codRestrict
    (AllowedComplex.PositiveAllowed p m alpha) (by
      intro c
      change TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m))
          (PositiveTarget.boundary ℤ (Vertex (p := p) (m := m)) c.1) ∈
        AllowedFaces.allowedChains ℤ p m alpha
      change TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m))
          (TargetChains.projectPositive ℤ (Vertex (p := p) (m := m))
            (TargetChains.boundary ℤ (Vertex (p := p) (m := m))
              (TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m)) c.1))) ∈ _
      rw [TargetChains.positiveInclusion_projectPositive]
      apply Submodule.sub_mem
      · exact PositiveAllowed.boundary_mem_allowed c.2
      · exact single_empty_mem_allowed _)

theorem positiveBoundary_sq (c : PA (p := p) (m := m) (alpha := alpha)) :
    positiveBoundary (positiveBoundary c) = 0 := by
  apply Subtype.ext
  exact PositiveTarget.boundary_boundary ℤ (Vertex (p := p) (m := m)) c.1

noncomputable def totalBoundary : Total (p := p) (m := m) (alpha := alpha) →ₗ[ℤ]
    Total (p := p) (m := m) (alpha := alpha) :=
  (AllowedComplex.totalChainEquivPositiveAllowed (p := p) (m := m)
      (alpha := alpha)).symm.toLinearMap.comp
    ((positiveBoundary (p := p) (m := m) (alpha := alpha)).comp
      (AllowedComplex.totalChainEquivPositiveAllowed (p := p) (m := m)
        (alpha := alpha)).toLinearMap)

theorem equiv_coe_eq_totalInclusion
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    (AllowedComplex.totalChainEquivPositiveAllowed c).1 =
      SignedTargetOrbits.totalInclusion c := by
  apply Subtype.ext
  let P := AllowedComplex.positiveAllowedEquivSupported
    (p := p) (m := m) (alpha := alpha)
  let S := Finsupp.supportedEquivFinsupp
    (R := ℤ) (M := ℤ)
    {s : Finset (Vertex (p := p) (m := m)) |
      s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}
  let L := Finsupp.lcongr
    (AllowedComplex.totalFaceEquivNonemptyAllowed
      (p := p) (m := m) (alpha := alpha))
    (LinearEquiv.refl ℤ ℤ)
  have hc : P (AllowedComplex.totalChainEquivPositiveAllowed c) =
      S.symm (L c) := by
    change P (P.symm (S.symm (L c))) = S.symm (L c)
    exact P.apply_symm_apply _
  change
    ((P (AllowedComplex.totalChainEquivPositiveAllowed c)).1 :
        TargetChains.FullChain ℤ (Vertex (p := p) (m := m))) =
      (SignedTargetOrbits.totalInclusion c).1
  rw [hc]
  ext t
  change (S.symm (L c)).1 t =
    Finsupp.mapDomain SignedTargetOrbits.totalFaceVal c t
  by_cases h : t.Nonempty ∧ AllowedFaces.IsAllowed alpha t
  · let st : {s : Finset (Vertex (p := p) (m := m)) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} := ⟨t, h⟩
    let s : TargetOrbits.TotalFace p m alpha :=
      (AllowedComplex.totalFaceEquivNonemptyAllowed
        (p := p) (m := m) (alpha := alpha)).symm st
    have hs : SignedTargetOrbits.totalFaceVal s = t := by
      change s.2.1 = t
      exact congrArg Subtype.val
        ((AllowedComplex.totalFaceEquivNonemptyAllowed
          (p := p) (m := m) (alpha := alpha)).apply_symm_apply st)
    rw [← hs, Finsupp.mapDomain_apply
      SignedTargetOrbits.totalFaceVal_injective]
    have hsallowed :
        (SignedTargetOrbits.totalFaceVal s).Nonempty ∧
          AllowedFaces.IsAllowed alpha
            (SignedTargetOrbits.totalFaceVal s) :=
      ⟨TargetOrbits.allowedFace_nonempty s.2,
        (AllowedComplex.targetAllowed_iff s.2.1).1 s.2.2.2⟩
    let u : TargetOrbits.PositiveAllowedFinset p m alpha :=
      ⟨t, h.1, (AllowedComplex.targetAllowed_iff t).2 h.2⟩
    have hu : SignedTargetOrbits.totalFaceVal
        ((TargetOrbits.totalFaceEquivPositive p m alpha).symm u) = t := by
      exact congrArg Subtype.val
        ((TargetOrbits.totalFaceEquivPositive p m alpha).apply_symm_apply u)
    simp [S, L, s, st, hsallowed, u, hu, h,
      AllowedComplex.totalFaceEquivNonemptyAllowed,
      AllowedComplex.positivePredicateEquiv]
  · have ht : t ∉ Set.range
        (SignedTargetOrbits.totalFaceVal
          (p := p) (m := m) (alpha := alpha)) := by
      rintro ⟨s, rfl⟩
      apply h
      exact ⟨TargetOrbits.allowedFace_nonempty s.2,
        (AllowedComplex.targetAllowed_iff s.2.1).1 s.2.2.2⟩
    rw [Finsupp.mapDomain_of_notMem_range c t ht]
    simp [S, L, h]

theorem totalInclusion_boundary
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    SignedTargetOrbits.totalInclusion (totalBoundary c) =
      PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))
        (SignedTargetOrbits.totalInclusion c) := by
  rw [← equiv_coe_eq_totalInclusion (c := totalBoundary c),
    ← equiv_coe_eq_totalInclusion (c := c)]
  change (AllowedComplex.totalChainEquivPositiveAllowed
    ((AllowedComplex.totalChainEquivPositiveAllowed).symm
      (positiveBoundary (AllowedComplex.totalChainEquivPositiveAllowed c)))).1 =
        PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))
          (AllowedComplex.totalChainEquivPositiveAllowed c).1
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem totalBoundary_sq (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (totalBoundary c) = 0 := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [totalInclusion_boundary, totalInclusion_boundary,
    PositiveTarget.boundary_boundary]
  simp

theorem totalBoundary_targetAct (a : ZMod p)
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.totalTargetAct a c) =
      SignedTargetOrbits.totalTargetAct a (totalBoundary c) := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [totalInclusion_boundary,
    SignedTargetOrbits.totalInclusion_targetAct,
    SignedTargetOrbits.totalInclusion_targetAct,
    totalInclusion_boundary]
  exact (PositiveTarget.map_boundary
    (LabelChainMap.targetShift (m := m) a)
    (SignedTargetOrbits.totalInclusion c)).symm

theorem totalBoundary_actualTotalAct
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalAct c) =
      SignedTargetOrbits.actualTotalAct (totalBoundary c) := by
  rw [SignedTargetOrbits.actualTotalAct_eq_totalTargetAct]
  exact totalBoundary_targetAct 1 c

theorem totalBoundary_actualTotalTau
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalTau c) =
      SignedTargetOrbits.actualTotalTau (totalBoundary c) := by
  change totalBoundary (SignedTargetOrbits.actualTotalAct c - c) =
    SignedTargetOrbits.actualTotalAct (totalBoundary c) - totalBoundary c
  rw [map_sub, totalBoundary_actualTotalAct]

theorem totalBoundary_geometricTotalNorm
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.geometricTotalNorm c) =
      SignedTargetOrbits.geometricTotalNorm (totalBoundary c) := by
  simp only [SignedTargetOrbits.geometricTotalNorm,
    LinearMap.sum_apply, map_sum, totalBoundary_targetAct]

theorem totalBoundary_actualTotalNorm (hp : p.Prime)
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalNorm hp c) =
      SignedTargetOrbits.actualTotalNorm hp (totalBoundary c) := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm hp]
  exact totalBoundary_geometricTotalNorm c

noncomputable def datum (hp : p.Prime) :
    PeriodicDescent.Datum (Total (p := p) (m := m) (alpha := alpha)) where
  boundary := totalBoundary.toAddMonoidHom
  tau := SignedTargetOrbits.actualTotalTau
  normOp := SignedTargetOrbits.actualTotalNorm hp
  boundary_sq := totalBoundary_sq
  boundary_tau := totalBoundary_actualTotalTau
  boundary_norm := totalBoundary_actualTotalNorm hp
  ker_tau := SignedTargetOrbits.exists_actualTotalNorm_of_actualTotalTau_eq_zero hp
  ker_norm := SignedTargetOrbits.exists_actualTotalTau_of_actualTotalNorm_eq_zero hp

end

end AllowedDescent
