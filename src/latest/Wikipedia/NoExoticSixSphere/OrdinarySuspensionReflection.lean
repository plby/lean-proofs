import Wikipedia.NoExoticSixSphere.SuspensionPathHomotopyComparison
import Wikipedia.NoExoticSixSphere.SphereSuspensionHomotopyMap

/-!
# Ordinary sphere suspension reflects homotopy in the checked stability range

The minimum-path comparison is applied to the actual equatorial direction
maps. The two-pole correction and cosine latitude formula connect that
comparison to the original sphere suspension, not a substitute transition.
The resulting range suffices for sixth-stem maps with target dimension at
least eight. No computation of the stable group is asserted.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization SemicircleSuspension
open Wikipedia.HopfProblem.OrbitPair SpherePolygonEnergy

theorem homotopic_of_map_homotopic {m n : ℕ} (hd : m + 3 < 2 * (n + 1))
    {f g : C(Sphere m, Sphere n)} (H : (map f).Homotopic (map g)) : f.Homotopic g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hp := pathMap_homotopic_of_suspension H
  let D := equatorialDirection (k + 1)
  let fD : C(Sphere m, SphereSemicircle.Direction (south (k + 1))) := (D : C(_, _)).comp f
  let gD : C(Sphere m, SphereSemicircle.Direction (south (k + 1))) := (D : C(_, _)).comp g
  have hh := minimumPathMap_homotopicRel_iff (I := 𝓡 m)
    (south (k + 1)) (north (k + 1)) (north_eq_neg_south (k + 1))
    (by simpa only [finrank_euclideanSpace_fin] using hd) fD gD ∅
  have hD : fD.Homotopic gD := ContinuousMap.homotopicRel_empty.mp
    (hh.mpr (ContinuousMap.homotopicRel_empty.mpr hp))
  obtain ⟨K⟩ := hD
  have hf : (D.symm : C(_, _)).comp fD = f := by
    apply ContinuousMap.ext
    intro x
    exact D.symm_apply_apply (f x)
  have hg : (D.symm : C(_, _)).comp gD = g := by
    apply ContinuousMap.ext
    intro x
    exact D.symm_apply_apply (g x)
  exact ⟨((ContinuousMap.Homotopy.refl (D.symm : C(_, _))).comp K).cast hf hg⟩

theorem map_homotopic_iff {m n : ℕ} (hd : m + 3 < 2 * (n + 1))
    (f g : C(Sphere m, Sphere n)) : (map f).Homotopic (map g) ↔ f.Homotopic g :=
  ⟨homotopic_of_map_homotopic hd, map_homotopic⟩

theorem nullhomotopic_of_map_nullhomotopic {m n : ℕ} (hd : m + 3 < 2 * (n + 1))
    {f : C(Sphere m, Sphere n)} (H : (map f).Nullhomotopic) : f.Nullhomotopic := by
  obtain ⟨b, hb⟩ := H
  let c : Sphere n := spherePole n
  let g : C(Sphere m, Sphere n) := ContinuousMap.const _ c
  obtain ⟨a, ha⟩ := map_nullhomotopic (ContinuousMap.nullhomotopic_of_constant c)
  have hab : (ContinuousMap.const (Sphere (m + 1)) b).Homotopic
      (ContinuousMap.const _ a) := ContinuousMap.homotopic_const_iff.mpr
    (PathConnectedSpace.joined b a)
  exact ⟨c, homotopic_of_map_homotopic hd (hb.trans (hab.trans ha.symm))⟩

theorem map_nullhomotopic_iff {m n : ℕ} (hd : m + 3 < 2 * (n + 1))
    (f : C(Sphere m, Sphere n)) : (map f).Nullhomotopic ↔ f.Nullhomotopic :=
  ⟨nullhomotopic_of_map_nullhomotopic hd, map_nullhomotopic⟩

end NoExoticSixSphere.SphereMapSuspension
