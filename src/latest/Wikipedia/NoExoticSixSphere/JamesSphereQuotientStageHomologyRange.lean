import Wikipedia.NoExoticSixSphere.JamesSphereQuotientCellHomology
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientHomologyStages

/-!
# The original second-stage inclusion controls the full quotient in low homology

Successive actual cell attachments give the finite-stage comparisons.
The original compact-exhaustion lift and zero-detection theorems pass
injectivity and surjectivity to the full quotient, with no substitute maps.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.StageHomologyRange

theorem fromSecond_bijective (n l : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Bijective (singularHomologyMap
      (FiniteStage.transition n (Nat.succ_le_succ (Nat.zero_le l))) d) := by
  induction l with
  | zero =>
    rw [FiniteStage.transition_refl, singularHomologyMap_id]
    exact Function.bijective_id
  | succ l ih =>
    rw [← FiniteStage.transition_trans n (Nat.succ_le_succ (Nat.zero_le l))
      (Nat.le_succ (l + 1)), singularHomologyMap_comp]
    exact (CellAttachment.transition_homology_bijective_range n l hn d hd hdn).comp ih

theorem fromSecond_surjective (n l : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective (singularHomologyMap
      (FiniteStage.transition n (Nat.succ_le_succ (Nat.zero_le l))) d) := by
  induction l with
  | zero =>
    rw [FiniteStage.transition_refl, singularHomologyMap_id]
    exact Function.surjective_id
  | succ l ih =>
    rw [← FiniteStage.transition_trans n (Nat.succ_le_succ (Nat.zero_le l))
      (Nat.le_succ (l + 1)), singularHomologyMap_comp]
    exact (CellAttachment.transition_homology_surjective_range n l hn d hd hdn).comp ih

theorem fullMap_injective (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Injective (singularHomologyMap (FiniteStage.map n 1) d) := by
  have hz (a : SingularHomology (FiniteStage.Space n 1) d)
      (ha : singularHomologyMap (FiniteStage.map n 1) d a = 0) : a = 0 := by
    obtain ⟨l, hl, ha⟩ := HomologyStages.exists_later_zero n 1 d a ha
    have hi : Function.Injective (singularHomologyMap (FiniteStage.transition n hl) d) := by
      cases l with
      | zero => omega
      | succ l => exact (fromSecond_bijective n l hn d hd hdn).injective
    exact hi (ha.trans (map_zero _).symm)
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hab, sub_self]

theorem fullMap_surjective (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective (singularHomologyMap (FiniteStage.map n 1) d) := by
  intro a
  obtain ⟨k, b, hb⟩ := HomologyStages.exists_homology_lift n d a
  let l := max k 1
  have hkl : k ≤ l := le_max_left _ _
  have h1l : 1 ≤ l := le_max_right _ _
  let b' := singularHomologyMap (FiniteStage.transition n hkl) d b
  have hb' : singularHomologyMap (FiniteStage.map n l) d b' = a :=
    (HomologyStages.map_transition_homology n hkl d b).trans hb
  have hs : Function.Surjective (singularHomologyMap (FiniteStage.transition n h1l) d) := by
    generalize hl : l = m at h1l ⊢
    cases m with
    | zero => omega
    | succ m => exact fromSecond_surjective n m hn d hd hdn
  obtain ⟨c, hc⟩ := hs b'
  refine ⟨c, ?_⟩
  calc
    singularHomologyMap (FiniteStage.map n 1) d c =
        singularHomologyMap (FiniteStage.map n l) d
          (singularHomologyMap (FiniteStage.transition n h1l) d c) :=
      (HomologyStages.map_transition_homology n h1l d c).symm
    _ = singularHomologyMap (FiniteStage.map n l) d b' := congrArg _ hc
    _ = a := hb'

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.StageHomologyRange
