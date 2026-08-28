import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonRefinement
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.UniformRefinement

/-!
# Arbitrarily fine exact refinements of symmetric determinant-one polygon families

The short-radius condition is preserved by all edge subdivisions. Consequently
every continuous family has arbitrarily fine uniform refinements preserving
its realized path and energy exactly, without compactness of the parameter space.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace NoExoticSixSphere.UniformTimePartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} {X : Type*} [TopologicalSpace X]

def uniformResampleFamily (a b : SpecialSpace ι) (l : ℕ)
    (p : C(X, VertexSpace.Space ι m)) (hp : ∀ x, p x ∈ admissible a b m) :
    C(X, VertexSpace.Space ι (refinedCount m l)) :=
  let R : C(admissible a b m, VertexSpace.Space ι (refinedCount m l)) :=
    ⟨fun v ↦ resample a b (time m) (strictMono_time m) (time (refinedCount m l)) v.1 v.2,
      continuous_resample a b (time m) (strictMono_time m) (time (refinedCount m l))⟩
  R.comp ⟨fun x ↦ ⟨p x, hp x⟩, p.continuous.subtype_mk hp⟩

theorem exists_uniform_family_refinement (a b : SpecialSpace ι)
    (p : C(X, VertexSpace.Space ι m)) (hp : ∀ x, p x ∈ admissible a b m)
    (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∃ q : C(X, VertexSpace.Space ι k),
      ∃ hq : ∀ x, q x ∈ admissible a b k,
        realizedFamily a b (time k) (strictMono_time k) q hq =
          realizedFamily a b (time m) (strictMono_time m) p hp ∧
        ∀ x, energy a b (time k) (q x) = energy a b (time m) (p x) := by
  let k := refinedCount m N
  let q := uniformResampleFamily a b N p hp
  have hz : time k 0 = time m 0 := (time_zero k).trans (time_zero m).symm
  have ho : time k (Fin.last (k + 1)) = time m (Fin.last (m + 1)) :=
    (time_last k).trans (time_last m).symm
  have hc (j : Fin (k + 1)) :
      time m (parentIndex m N j).castSucc ≤ time k j.castSucc ∧
        time k j.succ ≤ time m (parentIndex m N j).succ :=
    ⟨parentIndex_left m N j, parentIndex_right m N j⟩
  have hq : ∀ x, q x ∈ admissible a b k := fun x ↦
    resample_admissible a b (time m) (time k) (strictMono_time m) (strictMono_time k)
      hz ho (p x) (hp x) (parentIndex m N) hc
  refine ⟨k, le_refinedCount m N, q, hq, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro z
    have ht : (z.1 : ℝ) ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
      simpa only [time_zero, time_last] using z.1.property
    exact path_resample a b (time m) (time k) (strictMono_time m) (strictMono_time k)
      hz ho (p z.2) (hp z.2) (parentIndex m N) hc (hq z.2) ht
  · intro x
    exact energy_resample a b (time m) (time k) (strictMono_time m) (strictMono_time k)
      hz ho (p x) (hp x) (parentIndex m N) hc

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
