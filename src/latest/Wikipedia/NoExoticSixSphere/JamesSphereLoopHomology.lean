import Wikipedia.NoExoticSixSphere.JamesSphereCoverHomotopies

/-!
# Projection and the actual loop action give the James homology splitting

For positive degrees, the direct sum of the homology maps of projection
and generator concatenation is an isomorphism. The maps are identified
with the actual path-cover Mayer--Vietoris maps by the proved homotopies.
This is the loop-space side of the James argument, not the James-space
comparison equivalence or the corresponding word-space computation.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.LoopHomology

open CoverMaps

theorem cover_fst_raw (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).1 =
      singularHomologyMap (lowerEquiv n).toFun k
        (leftHomologyMap (Lower n) (Upper n) k
          (singularHomologyMap (Overlap.loopProductEquiv n).symm.toFun k a)).1 := rfl

theorem cover_snd_raw (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).2 =
      singularHomologyMap (upperEquiv n).toFun k
        (leftHomologyMap (Lower n) (Upper n) k
          (singularHomologyMap (Overlap.loopProductEquiv n).symm.toFun k a)).2 := rfl

theorem cover_fst_psi (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).1 =
      singularHomologyMap (lowerEquiv n).toFun k (singularHomologyMap (lowerPsi n) k a) := by
  let ψ : C(LoopParameter n, (Lower n ∩ Upper n : Set (EndingPath.Space (spherePole (n + 1))))) :=
    (Overlap.loopProductEquiv n).symm.toFun
  rw [cover_fst_raw]
  change singularHomologyMap (lowerEquiv n).toFun k
    (leftHomologyMap (Lower n) (Upper n) k (singularHomologyMap ψ k a)).1 = _
  rw [leftHomologyMap_apply]
  have hc := LinearMap.congr_fun (singularHomologyMap_comp ψ
    (ContinuousMap.inclusion (Set.inter_subset_left : Lower n ∩ Upper n ⊆ Lower n)) k) a
  exact congrArg (singularHomologyMap (lowerEquiv n).toFun k) hc.symm

theorem cover_snd_psi (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).2 =
      -singularHomologyMap (upperEquiv n).toFun k (singularHomologyMap (upperPsi n) k a) := by
  let ψ : C(LoopParameter n, (Lower n ∩ Upper n : Set (EndingPath.Space (spherePole (n + 1))))) :=
    (Overlap.loopProductEquiv n).symm.toFun
  rw [cover_snd_raw]
  change singularHomologyMap (upperEquiv n).toFun k
    (leftHomologyMap (Lower n) (Upper n) k (singularHomologyMap ψ k a)).2 = _
  rw [leftHomologyMap_apply, map_neg]
  have hc := LinearMap.congr_fun (singularHomologyMap_comp ψ
    (ContinuousMap.inclusion (Set.inter_subset_right : Lower n ∩ Upper n ⊆ Upper n)) k) a
  exact congrArg (fun b ↦ -singularHomologyMap (upperEquiv n).toFun k b) hc.symm

theorem cover_fst (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).1 =
      singularHomologyMap (loopProjection n) k a := by
  rw [cover_fst_psi, homotopy_homologyMap (lowerHomotopy n) k, singularHomologyMap_comp]
  exact (homotopyEquivHomologyEquiv (lowerEquiv n) k).apply_symm_apply
    (singularHomologyMap (loopProjection n) k a)

theorem cover_snd (n k : ℕ) (hk : k ≠ 0) (a : SingularHomology (LoopParameter n) k) :
    (Overlap.generatorCoverHomologyEquiv n k hk a).2 =
      -singularHomologyMap (generatorAction n) k a := by
  rw [cover_snd_psi, homotopy_homologyMap (upperHomotopy n) k, singularHomologyMap_comp]
  exact congrArg Neg.neg ((homotopyEquivHomologyEquiv (upperEquiv n) k).apply_symm_apply
    (singularHomologyMap (generatorAction n) k a))

def undoSecondSign (A : Type*) [AddCommGroup A] : (A × A) ≃ₗ[ℤ] (A × A) where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := Prod.ext rfl (neg_neg p.2)
  right_inv p := Prod.ext rfl (neg_neg p.2)
  map_add' p q := Prod.ext rfl (neg_add p.2 q.2)
  map_smul' r p := Prod.ext rfl (smul_neg r p.2).symm

def projectionActionEquiv (n k : ℕ) (hk : k ≠ 0) :
    SingularHomology (LoopParameter n) k ≃ₗ[ℤ]
      (SingularHomology (Loops n) k × SingularHomology (Loops n) k) :=
  (Overlap.generatorCoverHomologyEquiv n k hk).trans
    (undoSecondSign (SingularHomology (Loops n) k))

theorem projectionActionEquiv_apply (n k : ℕ) (hk : k ≠ 0)
    (a : SingularHomology (LoopParameter n) k) :
    projectionActionEquiv n k hk a =
      (singularHomologyMap (loopProjection n) k a,
        singularHomologyMap (generatorAction n) k a) := by
  apply Prod.ext
  · exact cover_fst n k hk a
  · change -(Overlap.generatorCoverHomologyEquiv n k hk a).2 = _
    rw [cover_snd, neg_neg]

theorem projection_action_bijective (n k : ℕ) (hk : k ≠ 0) :
    Function.Bijective (fun a : SingularHomology (LoopParameter n) k ↦
      (singularHomologyMap (loopProjection n) k a,
        singularHomologyMap (generatorAction n) k a)) := by
  have he : (fun a : SingularHomology (LoopParameter n) k ↦
      (singularHomologyMap (loopProjection n) k a, singularHomologyMap (generatorAction n) k a)) =
      projectionActionEquiv n k hk := by
    funext a
    exact (projectionActionEquiv_apply n k hk a).symm
  rw [he]
  exact (projectionActionEquiv n k hk).bijective

end NoExoticSixSphere.JamesSphere.LoopHomology
