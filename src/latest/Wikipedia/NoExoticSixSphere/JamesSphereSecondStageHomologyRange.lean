import Wikipedia.NoExoticSixSphere.JamesSphereStageCellHomology
import Wikipedia.NoExoticSixSphere.JamesHomologyStages
import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomeomorph
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# The original second James stage in full James homology

The actual later cell inclusions preserve low-degree homology. Compact
factorization represents full-space classes in a finite stage and
detects zero there. At the upper edge the second stage has vanishing
homology above its top cell, giving the missing injection.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.SecondStageHomologyRange

open James.HomologyStages

theorem fromSecond_bijective (n l : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Bijective (singularHomologyMap
      (transition (spherePole n) (show 2 ≤ l + 2 by omega)) d) := by
  induction l with
  | zero =>
    change Function.Bijective (singularHomologyMap (ContinuousMap.id _) d)
    rw [singularHomologyMap_id]
    exact Function.bijective_id
  | succ l ih =>
    have he : transition (spherePole n) (show 2 ≤ l + 1 + 2 by omega) =
        (StageAttachment.inclusion n (l + 2)).hom.comp
          (transition (spherePole n) (show 2 ≤ l + 2 by omega)) := rfl
    rw [he, singularHomologyMap_comp]
    have hs := StageAttachment.inclusion_homology_bijective_range n (l + 2) hn (by omega)
      d hd hdn
    change Function.Bijective (singularHomologyMap (StageAttachment.inclusion n (l + 2)).hom d ∘
      singularHomologyMap (transition (spherePole n) (show 2 ≤ l + 2 by omega)) d)
    exact hs.comp ih

theorem fromSecond_surjective (n l : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective (singularHomologyMap
      (transition (spherePole n) (show 2 ≤ l + 2 by omega)) d) := by
  induction l with
  | zero =>
    change Function.Surjective (singularHomologyMap (ContinuousMap.id _) d)
    rw [singularHomologyMap_id]
    exact Function.surjective_id
  | succ l ih =>
    have he : transition (spherePole n) (show 2 ≤ l + 1 + 2 by omega) =
        (StageAttachment.inclusion n (l + 2)).hom.comp
          (transition (spherePole n) (show 2 ≤ l + 2 by omega)) := rfl
    rw [he, singularHomologyMap_comp]
    have hs := StageAttachment.inclusion_homology_surjective_range n (l + 2) hn (by omega)
      d hd hdn
    change Function.Surjective (singularHomologyMap (StageAttachment.inclusion n (l + 2)).hom d ∘
      singularHomologyMap (transition (spherePole n) (show 2 ≤ l + 2 by omega)) d)
    exact hs.comp ih

theorem fullMap_injective (n : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Injective
      (singularHomologyMap (James.HomologyStages.inclusion (spherePole n) 2) d) := by
  have hz (a : SingularHomology (James.stage (spherePole n) 2) d)
      (ha : singularHomologyMap (James.HomologyStages.inclusion (spherePole n) 2) d a = 0) :
      a = 0 := by
    obtain ⟨l, hl, ha⟩ := exists_later_zero (spherePole n) 2 d a ha
    have hi : Function.Injective (singularHomologyMap (transition (spherePole n) hl) d) := by
      cases l with
      | zero => omega
      | succ l =>
        cases l with
        | zero => omega
        | succ l => exact (fromSecond_bijective n l hn d hd hdn).injective
    exact hi (ha.trans (map_zero _).symm)
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hab, sub_self]

theorem fullMap_surjective (n : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective
      (singularHomologyMap (James.HomologyStages.inclusion (spherePole n) 2) d) := by
  intro a
  obtain ⟨k, b, hb⟩ := exists_homology_lift (spherePole n) d a
  let l := max k 2
  have hkl : k ≤ l := le_max_left _ _
  have h2l : 2 ≤ l := le_max_right _ _
  let b' := singularHomologyMap (transition (spherePole n) hkl) d b
  have hb' : singularHomologyMap (James.HomologyStages.inclusion (spherePole n) l) d b' = a := by
    change (singularHomologyMap (James.HomologyStages.inclusion (spherePole n) l) d ∘ₗ
      singularHomologyMap (transition (spherePole n) hkl) d) b = a
    rw [← singularHomologyMap_comp, inclusion_transition]
    exact hb
  have hs : Function.Surjective (singularHomologyMap (transition (spherePole n) h2l) d) := by
    generalize he : l = m at h2l ⊢
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m => exact fromSecond_surjective n m hn d hd hdn
  obtain ⟨c, hc⟩ := hs b'
  refine ⟨c, ?_⟩
  rw [← inclusion_transition (spherePole n) h2l, singularHomologyMap_comp,
    LinearMap.comp_apply, hc]
  exact hb'

theorem secondStage_homology_above (n : ℕ) (hn : 2 ≤ n) (d : ℕ) (hd : 2 * n < d) :
    Subsingleton (SingularHomology (James.stage (spherePole n) 2) d) := by
  let : Subsingleton (SingularHomology (James.stage (spherePole n) 1) d) :=
    subsingleton_singularHomology_of_homeomorph_sphere
      (by omega) (by omega) (by omega) (FirstStage.homeomorph n).symm
  exact (StageAttachment.inclusion_homology_surjective n 1 hn d (by omega) (by omega)).subsingleton

theorem fullMap_bijective (n : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Bijective
      (singularHomologyMap (James.HomologyStages.inclusion (spherePole n) 2) d) := by
  refine ⟨?_, fullMap_surjective n hn d hd hdn⟩
  by_cases hstrict : d + 1 < 3 * n
  · exact fullMap_injective n hn d hd hstrict
  · let : Subsingleton (SingularHomology (James.stage (spherePole n) 2) d) :=
      secondStage_homology_above n hn d (by omega)
    exact fun _ _ _ ↦ Subsingleton.elim _ _

end NoExoticSixSphere.JamesSphere.SecondStageHomologyRange
