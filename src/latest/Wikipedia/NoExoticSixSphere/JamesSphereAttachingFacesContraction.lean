import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCollapsedFaces

/-!
# A based contraction of the actual discarded boundary subspace

First move both clocks to zero, retaining all tails. Then contract the
tails inside that zero-clock face. Both stages stay in the discarded
subspace, are jointly continuous, and fix the original corner. Thus
the contraction required for the actual source quotient is supplied,
rather than assumed from the informal shape of its boundary faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem clockStage_mem (n : ℕ) (s : I) (p : collapsedFaces n) :
    ((fun i ↦ σ s * p.val.val.1 i), p.val.val.2) ∈ deletedAmbient n := by
  rcases p.property with hp | hp
  · left
    funext i
    change σ s * p.val.val.1 i = 0
    rw [hp, Pi.zero_apply, mul_zero]
  · exact Or.inr hp

def clockStage (n : ℕ) : C(I × collapsedFaces n, collapsedFaces n) :=
  ⟨fun u ↦ ⟨⟨((fun i ↦ σ u.1 * u.2.val.val.1 i), u.2.val.val.2),
      deleted_subset_full n (clockStage_mem n u.1 u.2)⟩, clockStage_mem n u.1 u.2⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hp : Continuous (fun u : I × collapsedFaces n ↦ u.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (continuous_pi (fun i ↦ (unitInterval.continuous_symm.comp continuous_fst).mul
      ((continuous_apply i).comp hp.fst))).prodMk hp.snd⟩

theorem clockStage_zero (n : ℕ) (p : collapsedFaces n) : clockStage n (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change σ (0 : I) * p.val.val.1 i = p.val.val.1 i
    rw [unitInterval.symm_zero, one_mul]
  · rfl

theorem clockStage_point (n : ℕ) (s : I) :
    clockStage n (s, collapsedPoint n) = collapsedPoint n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact mul_zero _
  · rfl

def clockEndpoint (n : ℕ) : C(collapsedFaces n, collapsedFaces n) :=
  (clockStage n).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

def clockHomotopy (n : ℕ) :
    (ContinuousMap.id (collapsedFaces n)).HomotopyRel (clockEndpoint n) {collapsedPoint n} where
  toContinuousMap := clockStage n
  map_zero_left := clockStage_zero n
  map_one_left _ := rfl
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact clockStage_point n s

def tailStage (n : ℕ) : C(I × collapsedFaces n, collapsedFaces n) :=
  ⟨fun u ↦ ⟨⟨(0, fun i j ↦ σ u.1 * u.2.val.val.2 i j),
      Or.inl ⟨0, Or.inl rfl⟩⟩, Or.inl rfl⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hp : Continuous (fun u : I × collapsedFaces n ↦ u.2.val.val.2) :=
      continuous_snd.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    exact continuous_const.prodMk (continuous_pi (fun i ↦ continuous_pi (fun j ↦
      (unitInterval.continuous_symm.comp continuous_fst).mul
        ((continuous_apply j).comp ((continuous_apply i).comp hp)))))⟩

theorem tailStage_zero (n : ℕ) (p : collapsedFaces n) :
    tailStage n (0, p) = clockEndpoint n p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change 0 = σ (1 : I) * p.val.val.1 i
    rw [unitInterval.symm_one, zero_mul]
  · funext i j
    change σ (0 : I) * p.val.val.2 i j = p.val.val.2 i j
    rw [unitInterval.symm_zero, one_mul]

theorem tailStage_one (n : ℕ) (p : collapsedFaces n) :
    tailStage n (1, p) = collapsedPoint n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i j
    change σ (1 : I) * p.val.val.2 i j = 0
    rw [unitInterval.symm_one, zero_mul]

theorem tailStage_point (n : ℕ) (s : I) :
    tailStage n (s, collapsedPoint n) = collapsedPoint n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i j
    exact mul_zero _

def tailHomotopy (n : ℕ) :
    (clockEndpoint n).HomotopyRel (ContinuousMap.const _ (collapsedPoint n))
      {collapsedPoint n} where
  toContinuousMap := tailStage n
  map_zero_left := tailStage_zero n
  map_one_left := tailStage_one n
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact (tailStage_point n s).trans (clockStage_point n 1).symm

def collapsedContraction (n : ℕ) :
    (ContinuousMap.id (collapsedFaces n)).HomotopyRel
      (ContinuousMap.const _ (collapsedPoint n)) {collapsedPoint n} :=
  (clockHomotopy n).trans (tailHomotopy n)

end NoExoticSixSphere.JamesSphere.AttachingSquare
