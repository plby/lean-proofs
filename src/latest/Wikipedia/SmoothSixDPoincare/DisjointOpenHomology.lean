import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

/-!
# Actual homology decomposition for disjoint open subsets of one space

The literal map from the topological coproduct to the open union is a
homeomorphism. Transporting the native chain-level coproduct decomposition
therefore expresses every map out of this original union as the sum of its
actual restrictions to the original open subsets.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.DisjointOpenHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

variable {X : Type} [TopologicalSpace X] {ι : Type}
  (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hd : Pairwise (Disjoint on W))

def inclusion (i : ι) : C(W i, ↥(⋃ j, W j)) :=
  ⟨Set.inclusion (subset_iUnion W i), continuous_subtype_val.subtype_mk _⟩

def unionHomeomorph : (Σ i, W i) ≃ₜ ↥(⋃ i, W i) :=
  let e := Equiv.ofBijective (sigmaToiUnion W) (sigmaToiUnion_bijective W hd)
  e.toHomeomorphOfContinuousOpen (by
      apply continuous_sigma
      intro i
      exact (inclusion W i).continuous) (by
      apply isOpenMap_sigma.mpr
      intro i
      exact (hW i).isOpenMap_inclusion (subset_iUnion W i))

theorem unionHomeomorph_apply (i : ι) (x : W i) :
    unionHomeomorph W hW hd ⟨i, x⟩ = inclusion W i x := rfl

variable [Fintype ι]

def homologyEquiv (k : ℕ) :
    SingularHomology (↥(⋃ i, W i)) k ≃ₗ[ℤ] (∀ i, SingularHomology (W i) k) :=
  (homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).trans
    (sigmaHomologyEquiv (fun i => W i) k)

/-- The inverse decomposition is the sum of literal inclusion-induced maps. -/
theorem homologyEquiv_symm_apply (k : ℕ) (a : ∀ i, SingularHomology (W i) k) :
    (homologyEquiv W hW hd k).symm a =
      ∑ i, singularHomologyMap (inclusion W i) k (a i) := by
  change (homeomorphHomologyEquiv (unionHomeomorph W hW hd).symm k).symm
    ((sigmaHomologyEquiv (fun i => W i) k).symm a) = _
  rw [homeomorphHomologyEquiv_symm_apply, Homeomorph.symm_symm,
    sigmaHomologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem homology_decomposition (k : ℕ) (a : SingularHomology (↥(⋃ i, W i)) k) :
    a = ∑ i, singularHomologyMap (inclusion W i) k (homologyEquiv W hW hd k a i) := by
  have h := homologyEquiv_symm_apply W hW hd k (homologyEquiv W hW hd k a)
  rwa [LinearEquiv.symm_apply_apply] at h

variable {Y : Type} [TopologicalSpace Y]

/-- The map on the original union is the sum of its actual component restrictions. -/
theorem homology_map_out (f : C(↥(⋃ i, W i), Y)) (k : ℕ)
    (a : SingularHomology (↥(⋃ i, W i)) k) :
    singularHomologyMap f k a =
      ∑ i, singularHomologyMap (f.comp (inclusion W i)) k
        (homologyEquiv W hW hd k a i) := by
  calc
    singularHomologyMap f k a = singularHomologyMap f k
        (∑ i, singularHomologyMap (inclusion W i) k (homologyEquiv W hW hd k a i)) :=
      congrArg (singularHomologyMap f k) (homology_decomposition W hW hd k a)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [singularHomologyMap_comp, LinearMap.comp_apply]

end Wikipedia.SmoothSixDPoincare.DisjointOpenHomology
