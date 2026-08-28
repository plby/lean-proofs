import Wikipedia.NoExoticSixSphere.JamesSphereQuotientTransitions
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientCompactFactorization
import Wikipedia.NoExoticSixSphere.CompactExhaustionHomology

/-!
# Finite-stage representation and zero detection in the actual James quotient

Compact exhaustion and the actual range homeomorphisms give homology
representatives in finite quotients. A class vanishing in the full quotient
vanishes after an original finite-stage transition. No direct-limit
preservation assertion is assumed.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.HomologyStages

theorem map_transition_homology (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (d : ℕ)
    (a : SingularHomology (FiniteStage.Space n k) d) :
    singularHomologyMap (FiniteStage.map n l) d
      (singularHomologyMap (FiniteStage.transition n hkl) d a) =
      singularHomologyMap (FiniteStage.map n k) d a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, FiniteStage.map_transition]

theorem range_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (FiniteStage.rangeHomeomorph n l : C(_, _)).comp (FiniteStage.transition n hkl) =
      (ContinuousMap.inclusion (FiniteStage.range_mono n hkl)).comp
        (FiniteStage.rangeHomeomorph n k : C(_, _)) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  exact ContinuousMap.congr_fun (FiniteStage.map_transition n hkl) a

theorem exists_homology_lift (n d : ℕ) (a : SingularHomology (Space n) d) :
    ∃ k, ∃ b : SingularHomology (FiniteStage.Space n k) d,
      singularHomologyMap (FiniteStage.map n k) d b = a := by
  obtain ⟨k, b, hb⟩ := CompactExhaustionHomology.exists_homology_lift
    (fun k ↦ Set.range (FiniteStage.map n k))
    (fun _ hK ↦ exists_stage_of_isCompact n hK) d a
  let E := homeomorphHomologyEquiv (FiniteStage.rangeHomeomorph n k) d
  refine ⟨k, E.symm b, ?_⟩
  have hc : (subtypeInclusion (Set.range (FiniteStage.map n k))).comp
      (FiniteStage.rangeHomeomorph n k : C(_, _)) = FiniteStage.map n k := rfl
  have he := congrArg (fun f ↦ singularHomologyMap f d) hc
  rw [singularHomologyMap_comp] at he
  apply (LinearMap.congr_fun he (E.symm b)).symm.trans
  change singularHomologyMap (subtypeInclusion (Set.range (FiniteStage.map n k))) d
    (E (E.symm b)) = a
  rw [E.apply_symm_apply]
  exact hb

theorem exists_later_zero (n k d : ℕ) (a : SingularHomology (FiniteStage.Space n k) d)
    (ha : singularHomologyMap (FiniteStage.map n k) d a = 0) :
    ∃ l, ∃ hkl : k ≤ l, singularHomologyMap (FiniteStage.transition n hkl) d a = 0 := by
  let E := homeomorphHomologyEquiv (FiniteStage.rangeHomeomorph n k) d
  have hinc : singularHomologyMap (subtypeInclusion (Set.range (FiniteStage.map n k))) d
      (E a) = singularHomologyMap (FiniteStage.map n k) d a := by
    change singularHomologyMap (subtypeInclusion (Set.range (FiniteStage.map n k))) d
      (singularHomologyMap (FiniteStage.rangeHomeomorph n k : C(_, _)) d a) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
    rfl
  obtain ⟨l, hkl, hl⟩ := CompactExhaustionHomology.exists_later_zero
    (fun k ↦ Set.range (FiniteStage.map n k))
    (fun _ hK ↦ exists_stage_of_isCompact n hK) (FiniteStage.range_mono n)
    k d (E a) (hinc.trans ha)
  refine ⟨l, hkl, ?_⟩
  apply (homeomorphHomologyEquiv (FiniteStage.rangeHomeomorph n l) d).injective
  rw [map_zero]
  have hc := congrArg (fun f ↦ singularHomologyMap f d) (range_transition n hkl)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hc
  exact (LinearMap.congr_fun hc a).trans hl

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.HomologyStages
