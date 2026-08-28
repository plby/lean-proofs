import Wikipedia.NoExoticSixSphere.JamesSphereWordHomologyMaps

/-!
# Projection and prepend give the full James word-space homology splitting

Actual classes lift to finite stages, and classes that become zero in the
full space become zero at later stages. These proved facts and the exact
stage naturality pass the finite-stage isomorphisms to the full James
space. No direct-limit homology theorem or James comparison is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.WordHomology

theorem projection_action_surjective (n d : ℕ) (hd : d ≠ 0) :
    Function.Surjective (projectionActionMap n d) := by
  rintro ⟨a, b⟩
  obtain ⟨k, a₀, ha⟩ := James.HomologyStages.exists_homology_lift (spherePole n) d a
  obtain ⟨l, b₀, hb⟩ := James.HomologyStages.exists_homology_lift (spherePole n) d b
  let m := max k l
  have hkm : k ≤ m := le_max_left _ _
  have hlm : l ≤ m + 1 := (le_max_right k l).trans (Nat.le_succ m)
  let a' := singularHomologyMap (transition n hkm) d a₀
  let b' := singularHomologyMap (transition n hlm) d b₀
  obtain ⟨c, hc⟩ := (StageHomology.projection_action_bijective n m d hd).surjective (a', b')
  have hc₁ : singularHomologyMap (StageHomology.projection n m) d c = a' := congrArg Prod.fst hc
  have hc₂ : singularHomologyMap (stageAction n m) d c = b' := congrArg Prod.snd hc
  refine ⟨singularHomologyMap (productInclusion n m) d c, ?_⟩
  apply Prod.ext
  · change singularHomologyMap (projection n) d
      (singularHomologyMap (productInclusion n m) d c) = a
    rw [projection_stage, hc₁]
    exact (inclusion_transition n hkm d a₀).trans ha
  · change singularHomologyMap (action n) d
      (singularHomologyMap (productInclusion n m) d c) = b
    rw [action_stage, hc₂]
    exact (inclusion_transition n hlm d b₀).trans hb

theorem projection_action_eq_zero (n d : ℕ) (hd : d ≠ 0)
    (a : SingularHomology (Parameter n) d) (ha : projectionActionMap n d a = 0) : a = 0 := by
  obtain ⟨k, z, rfl⟩ :=
    James.HomologyStages.exists_product_homology_lift (spherePole n) (Sphere n) d a
  have hp : singularHomologyMap (projection n) d
      (singularHomologyMap (productInclusion n k) d z) = 0 := congrArg Prod.fst ha
  have hq : singularHomologyMap (action n) d
      (singularHomologyMap (productInclusion n k) d z) = 0 := congrArg Prod.snd ha
  rw [projection_stage] at hp
  rw [action_stage] at hq
  obtain ⟨p, hkp, hp⟩ := James.HomologyStages.exists_later_zero (spherePole n) k d
    (singularHomologyMap (StageHomology.projection n k) d z) hp
  obtain ⟨q, hkq, hq⟩ := James.HomologyStages.exists_later_zero (spherePole n) (k + 1) d
    (singularHomologyMap (stageAction n k) d z) hq
  let m := max p q
  have hpm : p ≤ m := le_max_left _ _
  have hqm : q ≤ m + 1 := (le_max_right p q).trans (Nat.le_succ m)
  have hkm : k ≤ m := hkp.trans hpm
  let z' := singularHomologyMap (productTransition n hkm) d z
  have hp' : singularHomologyMap (StageHomology.projection n m) d z' = 0 := by
    rw [show z' = singularHomologyMap (productTransition n hkm) d z from rfl,
      projection_transition]
    exact transition_zero n hkp hpm d _ hp
  have hq' : singularHomologyMap (stageAction n m) d z' = 0 := by
    rw [show z' = singularHomologyMap (productTransition n hkm) d z from rfl,
      action_transition]
    exact transition_zero n hkq hqm d _ hq
  have hz : z' = 0 := by
    apply (StageHomology.projectionActionEquiv n m d hd).injective
    rw [StageHomology.projectionActionEquiv_apply, map_zero, hp', hq']
    rfl
  change singularHomologyMap (productInclusion n k) d z = 0
  rw [← productInclusion_transition n hkm d z]
  change singularHomologyMap (productInclusion n m) d z' = 0
  rw [hz, map_zero]

theorem projection_action_injective (n d : ℕ) (hd : d ≠ 0) :
    Function.Injective (projectionActionMap n d) :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (projection_action_eq_zero n d hd))

theorem projection_action_bijective (n d : ℕ) (hd : d ≠ 0) :
    Function.Bijective (projectionActionMap n d) :=
  ⟨projection_action_injective n d hd, projection_action_surjective n d hd⟩

def projectionActionEquiv (n d : ℕ) (hd : d ≠ 0) :
    SingularHomology (Parameter n) d ≃ₗ[ℤ]
      (SingularHomology (Words n) d × SingularHomology (Words n) d) :=
  LinearEquiv.ofBijective (projectionActionMap n d) (projection_action_bijective n d hd)

theorem projectionActionEquiv_apply (n d : ℕ) (hd : d ≠ 0)
    (a : SingularHomology (Parameter n) d) :
    projectionActionEquiv n d hd a =
      (singularHomologyMap (projection n) d a, singularHomologyMap (action n) d a) := rfl

end NoExoticSixSphere.JamesSphere.WordHomology
