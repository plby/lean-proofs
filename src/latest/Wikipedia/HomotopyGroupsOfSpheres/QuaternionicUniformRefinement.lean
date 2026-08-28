import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRefinement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.UniformRefinement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformPrefixControl

/-!
# Arbitrarily fine, energy-preserving refinements of compact polygon families

The refinement is sampling of the same actual path. Compactness controls
the coarse generators, and a small reciprocal subdivision factor puts their
scaled versions in the logarithm target.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential NoExoticSixSphere.UniformTimePartition

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

theorem uniform_resample_properties (a b : symplecticSubgroup n) (l : ℕ)
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hsmall : ∀ i : Fin (m + 1), (1 / ((l : ℝ) + 1)) • generator a b v i ∈
      compatibleTarget n) :
    resample a b (time m) (time (refinedCount m l)) v ∈ admissible a b (refinedCount m l) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      path a b (time (refinedCount m l)) (resample a b (time m) (time (refinedCount m l)) v) t =
        path a b (time m) v t) ∧
    energy a b (time (refinedCount m l)) (resample a b (time m) (time (refinedCount m l)) v) =
      energy a b (time m) v := by
  let σ := time (refinedCount m l)
  have hz : σ 0 = time m 0 := (time_zero _).trans (time_zero _).symm
  have ho : σ (Fin.last (refinedCount m l + 1)) = time m (Fin.last (m + 1)) :=
    (time_last _).trans (time_last _).symm
  have hc (j : Fin (refinedCount m l + 1)) :
      time m (parentIndex m l j).castSucc ≤ σ j.castSucc ∧
        σ j.succ ≤ time m (parentIndex m l j).succ :=
    ⟨parentIndex_left m l j, parentIndex_right m l j⟩
  have hs (j : Fin (refinedCount m l + 1)) :
      ((σ j.succ - σ j.castSucc) /
        (time m (parentIndex m l j).succ - time m (parentIndex m l j).castSucc)) •
          generator a b v (parentIndex m l j) ∈ compatibleTarget n := by
    rw [refined_step_ratio]
    exact hsmall _
  refine ⟨resample_admissible a b (time m) σ (strictMono_time m) (strictMono_time _)
    hz ho v hv (parentIndex m l) hc hs, ?_,
    energy_resample a b (time m) σ (strictMono_time m) (strictMono_time _)
      hz ho v hv (parentIndex m l) hc hs⟩
  intro t ht
  apply path_resample a b (time m) σ (strictMono_time m) (strictMono_time _)
    hz ho v hv (parentIndex m l) hc hs
  simpa only [time_zero, time_last] using ht

noncomputable def uniformResampleFamily (a b : symplecticSubgroup n) (l : ℕ)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m) :
    C(X, Space n (refinedCount m l)) :=
  let R : C(admissible a b m, Space n (refinedCount m l)) :=
    ⟨fun v ↦ resample a b (time m) (time (refinedCount m l)) v.1,
      continuous_resample a b (time m) (time (refinedCount m l))⟩
  R.comp ⟨fun x ↦ ⟨p x, hp x⟩, p.continuous.subtype_mk hp⟩

theorem exists_family_generator_bound [CompactSpace X]
    (a b : symplecticSubgroup n) (p : C(X, Space n m))
    (hp : ∀ x, p x ∈ admissible a b m) :
    ∃ B : ℝ, ∀ x, ∀ i : Fin (m + 1), ‖generator a b (p x) i‖ ≤ B := by
  have hc (i : Fin (m + 1)) : Continuous (fun x ↦ ‖generator a b (p x) i‖) :=
    Continuous.norm (E := SkewSpace n)
      ((contMDiffOn_generator a b i).continuousOn.comp_continuous p.continuous hp)
  have hs : Continuous (fun x ↦ ∑ i : Fin (m + 1), ‖generator a b (p x) i‖) :=
    continuous_finsetSum _ (fun i _ ↦ hc i)
  obtain ⟨B, hB⟩ := (isCompact_range hs).bddAbove
  refine ⟨B, ?_⟩
  intro x i
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (E := SkewSpace n) (generator a b (p x) j))
    (Finset.mem_univ i)).trans (hB ⟨x, rfl⟩)

/-- Compact polygon families can be refined beyond any prescribed uniform
mesh threshold, preserving the realized path and its energy exactly. -/
theorem exists_uniform_family_refinement [CompactSpace X]
    (a b : symplecticSubgroup n) (p : C(X, Space n m))
    (hp : ∀ x, p x ∈ admissible a b m) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∃ q : C(X, Space n k), ∃ hq : ∀ x, q x ∈ admissible a b k,
      realizedFamily a b (time k) q hq = realizedFamily a b (time m) p hp ∧
      ∀ x, energy a b (time k) (q x) = energy a b (time m) (p x) := by
  obtain ⟨B, hB⟩ := exists_family_generator_bound a b p hp
  obtain ⟨L, hL⟩ := exists_uniform_prefix_target_bound n B
  let l := max N L
  have hscaled (x : X) (i : Fin (m + 1)) :
      (1 / ((l : ℝ) + 1)) • generator a b (p x) i ∈ compatibleTarget n := by
    have h := hL l (le_max_right _ _) (generator a b (p x) i) (hB x i)
      (0 : Fin (l + 1)) (unitTime l (0 : Fin (l + 1)).succ)
      ⟨((strictMono_unitTime l) (show (0 : Fin (l + 1)).castSucc <
        (0 : Fin (l + 1)).succ by simp)).le, le_rfl⟩
    change (time l (0 : Fin (l + 1)).succ - time l (0 : Fin (l + 1)).castSucc) •
      generator a b (p x) i ∈ compatibleTarget n at h
    rwa [time_step] at h
  let q := uniformResampleFamily a b l p hp
  have hprop (x : X) := uniform_resample_properties a b l (p x) (hp x) (hscaled x)
  have hq : ∀ x, q x ∈ admissible a b (refinedCount m l) := fun x ↦ (hprop x).1
  refine ⟨refinedCount m l, (le_max_left _ _).trans (le_refinedCount m l), q, hq, ?_,
    fun x ↦ (hprop x).2.2⟩
  apply ContinuousMap.ext
  intro z
  exact (hprop z.2).2.1 z.1 z.1.property

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
