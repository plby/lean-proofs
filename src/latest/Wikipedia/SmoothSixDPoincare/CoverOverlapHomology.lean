import Wikipedia.SmoothSixDPoincare.DisjointOpenHomology

/-!
# Native homology coordinates for separated components of a cover overlap

If the second cover member is a disjoint union of open neighborhoods, the
actual overlap decomposes into the intersections with those neighborhoods.
The equivalence and every inclusion below retain the original points.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CoverOverlapHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] {ι : Type}
  (U : Set X) (V : ι → Set X)

def componentInclusion (i : ι) : C(↥(U ∩ V i), ↥(U ∩ ⋃ j, V j)) :=
  ⟨fun x => ⟨x.val, ⟨x.property.1, mem_iUnion.mpr ⟨i, x.property.2⟩⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

def distributeHomeomorph : ↥(U ∩ ⋃ i, V i) ≃ₜ ↥(⋃ i, U ∩ V i) :=
  Homeomorph.setCongr (by ext x; simp)

variable (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V))

omit [TopologicalSpace X] in
include hd in
theorem disjoint_intersections : Pairwise (Disjoint on (fun i => U ∩ V i)) := by
  intro i j hij
  exact (hd hij).mono inter_subset_right inter_subset_right

variable [Fintype ι]

def homologyEquiv (k : ℕ) :
    SingularHomology (↥(U ∩ ⋃ i, V i)) k ≃ₗ[ℤ]
      (∀ i, SingularHomology (↥(U ∩ V i)) k) :=
  (homeomorphHomologyEquiv (distributeHomeomorph U V) k).trans
    (DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i)
      (fun i => hU.inter (hV i)) (disjoint_intersections U V hd) k)

theorem homologyEquiv_symm_apply (k : ℕ)
    (a : ∀ i, SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm a =
      ∑ i, singularHomologyMap (componentInclusion U V i) k (a i) := by
  change (homeomorphHomologyEquiv (distributeHomeomorph U V) k).symm
    ((DisjointOpenHomology.homologyEquiv (fun i => U ∩ V i)
      (fun i => hU.inter (hV i)) (disjoint_intersections U V hd) k).symm a) = _
  rw [homeomorphHomologyEquiv_symm_apply,
    DisjointOpenHomology.homologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem homology_decomposition (k : ℕ) (a : SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    a = ∑ i, singularHomologyMap (componentInclusion U V i) k
      (homologyEquiv U V hU hV hd k a i) := by
  have h := homologyEquiv_symm_apply U V hU hV hd k (homologyEquiv U V hU hV hd k a)
  rwa [LinearEquiv.symm_apply_apply] at h

variable {Y : Type} [TopologicalSpace Y]

theorem homology_map_out (f : C(↥(U ∩ ⋃ i, V i), Y)) (k : ℕ)
    (a : SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    singularHomologyMap f k a =
      ∑ i, singularHomologyMap (f.comp (componentInclusion U V i)) k
        (homologyEquiv U V hU hV hd k a i) := by
  calc
    singularHomologyMap f k a = singularHomologyMap f k
        (∑ i, singularHomologyMap (componentInclusion U V i) k
          (homologyEquiv U V hU hV hd k a i)) :=
      congrArg (singularHomologyMap f k) (homology_decomposition U V hU hV hd k a)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [singularHomologyMap_comp, LinearMap.comp_apply]

end Wikipedia.SmoothSixDPoincare.CoverOverlapHomology
