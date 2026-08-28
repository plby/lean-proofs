import Wikipedia.HopfProblem.OrbitPairSpherePolygonRefinement
import Wikipedia.HopfProblem.OrbitPairSpherePolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.UniformRefinement

/-!
# Arbitrarily fine sphere-polygon refinement with exact path and energy preservation

Every subdivision of a canonical nonantipodal segment is automatically short.
Thus the same uniform refinement works for all admissible polygons and all
continuous parameter families, without a compactness or generator-bound input.
A later energy cap can determine the mesh without changing the realized path.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace UniformTimePartition

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

theorem uniform_resample_properties (a b : Sphere n) (l : ℕ)
    (v : admissible (costDomain n) a b m) :
    resample a b (time m) (strictMono_time m) (time (refinedCount m l)) v ∈
        admissible (costDomain n) a b (refinedCount m l) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        ambientPath a b (time (refinedCount m l))
          (resample a b (time m) (strictMono_time m) (time (refinedCount m l)) v) t =
            (path a b (time m) (strictMono_time m) v t).val) ∧
      energy a b (time (refinedCount m l))
        (resample a b (time m) (strictMono_time m) (time (refinedCount m l)) v) =
          energy a b (time m) v.val := by
  let σ := time (refinedCount m l)
  have hz : σ 0 = time m 0 := (time_zero _).trans (time_zero _).symm
  have ho : σ (Fin.last (refinedCount m l + 1)) = time m (Fin.last (m + 1)) :=
    (time_last _).trans (time_last _).symm
  have hc (j : Fin (refinedCount m l + 1)) :
      time m (parentIndex m l j).castSucc ≤ σ j.castSucc ∧
        σ j.succ ≤ time m (parentIndex m l j).succ :=
    ⟨parentIndex_left m l j, parentIndex_right m l j⟩
  refine ⟨resample_admissible a b (time m) σ (strictMono_time m) (strictMono_time _)
    hz ho v (parentIndex m l) hc, ?_,
    energy_resample a b (time m) σ (strictMono_time m) (strictMono_time _)
      hz ho v (parentIndex m l) hc⟩
  intro t ht
  have htime : t ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
    simpa only [time_zero, time_last] using ht
  exact congrArg Subtype.val (path_resample a b (time m) σ (strictMono_time m)
    (strictMono_time _) hz ho v (parentIndex m l) hc htime)

def uniformResampleFamily (a b : Sphere n) (l : ℕ)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) :
    C(X, Space n (refinedCount m l)) :=
  let R : C(admissible (costDomain n) a b m, Space n (refinedCount m l)) :=
    ⟨resample a b (time m) (strictMono_time m) (time (refinedCount m l)),
      continuous_resample a b (time m) (strictMono_time m) (time (refinedCount m l))⟩
  R.comp ⟨fun x => ⟨p x, hp x⟩, p.continuous.subtype_mk hp⟩

theorem exists_uniform_family_refinement (a b : Sphere n) (p : C(X, Space n m))
    (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∃ q : C(X, Space n k),
      ∃ hq : ∀ x, q x ∈ admissible (costDomain n) a b k,
        realizedFamily a b (time k) (strictMono_time k) q hq =
          realizedFamily a b (time m) (strictMono_time m) p hp ∧
        ∀ x, energy a b (time k) (q x) = energy a b (time m) (p x) := by
  let q := uniformResampleFamily a b N p hp
  have hprop (x : X) := uniform_resample_properties a b N ⟨p x, hp x⟩
  have hq : ∀ x, q x ∈ admissible (costDomain n) a b (refinedCount m N) := fun x => (hprop x).1
  refine ⟨refinedCount m N, le_refinedCount m N, q, hq, ?_, fun x => (hprop x).2.2⟩
  apply ContinuousMap.ext
  intro z
  exact Subtype.ext ((hprop z.2).2.1 z.1 z.1.property)

theorem exists_uniform_family_refinement_with_mesh (a b : Sphere n) (p : C(X, Space n m))
    (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) (cap : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ 0 < k ∧
      (∀ i : Fin (k + 1), cap * (time k i.succ - time k i.castSucc) < Real.pi ^ 2) ∧
      ∃ q : C(X, Space n k), ∃ hq : ∀ x, q x ∈ admissible (costDomain n) a b k,
        realizedFamily a b (time k) (strictMono_time k) q hq =
          realizedFamily a b (time m) (strictMono_time m) p hp ∧
        ∀ x, energy a b (time k) (q x) = energy a b (time m) (p x) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (cap / Real.pi ^ 2) ((max N 1 : ℕ) : ℝ))
  have hNL : max N 1 ≤ L := by exact_mod_cast (le_max_right _ _).trans hL.le
  obtain ⟨k, hLk, q, hq, hpath, henergy⟩ := exists_uniform_family_refinement a b p hp L
  have hlarge : cap / Real.pi ^ 2 < (k : ℝ) :=
    ((le_max_left _ _).trans_lt hL).trans_le (by exact_mod_cast hLk)
  refine ⟨k, (le_max_left N 1).trans (hNL.trans hLk),
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans (hNL.trans hLk)),
    small_energy_step_of_large cap Real.pi_pos k hlarge, q, hq, hpath, henergy⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
