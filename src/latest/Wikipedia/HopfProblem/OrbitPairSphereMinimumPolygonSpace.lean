import Wikipedia.HopfProblem.OrbitPairSphereSemicircleDirection
import Wikipedia.HopfProblem.OrbitPairSpherePolygonMinimum
import Wikipedia.HopfProblem.OrbitPairSphereEnergySublevels

/-!
# The actual minimum polygon locus and unit tangent directions

Sampling antipodal semicircles parametrizes the exact minimum-energy locus.
The energy comparison and the previously proved equality classification give
surjectivity. Any interior sample recovers the direction, giving injectivity.
All polygons and all continuity assertions use the original sphere topology.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereSemicircle

variable {n m : ℕ}

def minimumSet (a b : Sphere n) (τ : Fin (m + 2) → ℝ) : Set (Space n m) :=
  {v | v ∈ admissible (costDomain n) a b m ∧ energy a b τ v = Real.pi ^ 2}

def semicircleVertices (a : Sphere n) (τ : Fin (m + 2) → ℝ)
    (y : Direction a) : Space n m := fun j =>
  ⟨SphereGreatCircle.curve a.val y.val Real.pi (τ j.castSucc.succ), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      SphereGreatCircle.norm_curve (ClosedHemisphere.unit_norm a) y.2.1 y.2.2
        Real.pi (τ j.castSucc.succ)⟩

theorem continuous_semicircleVertices (a : Sphere n) (τ : Fin (m + 2) → ℝ) :
    Continuous (semicircleVertices a τ) := by
  apply continuous_pi
  intro j
  have hs : Continuous (fun y : Direction a =>
      Real.sin (Real.pi * τ j.castSucc.succ) • y.val) :=
    (continuous_subtype_val : Continuous (fun y : Direction a => y.val)).const_smul
      (Real.sin (Real.pi * τ j.castSucc.succ))
  have hc : Continuous (fun y : Direction a =>
      SphereGreatCircle.curve a.val y.val Real.pi (τ j.castSucc.succ)) :=
    continuous_const.add hs
  exact hc.subtype_mk _

theorem interior_time_mem (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (j : Fin m) :
    τ j.castSucc.succ ∈ Ioo (0 : ℝ) 1 := by
  have hlo : (0 : Fin (m + 2)) < j.castSucc.succ := by
    change 0 < j.val + 1
    omega
  have hhi : j.castSucc.succ < Fin.last (m + 1) := by
    change j.val + 1 < m + 1
    omega
  exact ⟨by simpa only [hzero] using hτ hlo, by simpa only [hone] using hτ hhi⟩

theorem vertices_semicircle (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (y : Direction a) (j : Fin (m + 2)) :
    (vertices a b (semicircleVertices a τ y) j).val =
      SphereGreatCircle.curve a.val y.val Real.pi (τ j) := by
  induction j using Fin.cases with
  | zero => rw [vertices_zero, hzero, SphereGreatCircle.curve_zero]
  | succ j =>
    induction j using Fin.lastCases with
    | last => rw [Fin.succ_last, vertices_last, hone, SphereGreatCircle.curve_pi_one, hanti]
    | cast j => rw [vertices_interior]; rfl

theorem energy_semicircle_le (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (y : Direction a) :
    energy a b τ (semicircleVertices a τ y) ≤ Real.pi ^ 2 := by
  have he := energy_le_of_matching_vertices a b τ hτ (semicircleVertices a τ y)
    (SphereGreatCircle.contDiff_curve a.val y.val Real.pi)
    (SphereGreatCircle.norm_curve (ClosedHemisphere.unit_norm a) y.2.1 y.2.2 Real.pi)
    (fun j => (vertices_semicircle a b τ hzero hone hanti y j).symm)
  simpa only [hzero, hone,
    SphereGreatCircle.energy_curve (ClosedHemisphere.unit_norm a) y.2.1 y.2.2] using he

variable (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)

include hτ hzero hone hanti hmesh

theorem semicircleVertices_mem_minimumSet (y : Direction a) :
    semicircleVertices a τ y ∈ minimumSet a b τ := by
  have he := energy_semicircle_le a b τ hτ hzero hone hanti y
  exact ⟨sublevel_subset_admissible a b τ hτ _ hmesh he,
    le_antisymm he
      (antipodal_energy_ge_of_mesh a b τ hτ hzero hone hanti _ hmesh _ he)⟩

def minimumParametrization : C(Direction a, minimumSet a b τ) where
  toFun y := ⟨semicircleVertices a τ y,
    semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hmesh y⟩
  continuous_toFun := (continuous_semicircleVertices a τ).subtype_mk _

theorem minimumParametrization_surjective :
    Function.Surjective (minimumParametrization a b τ hτ hzero hone hanti hmesh) := by
  intro v
  obtain ⟨y, hy, hay, hsample⟩ :=
    (energy_eq_min_iff_greatCircle a b τ hτ hzero hone hanti _ hmesh v.val v.2.2.le).mp v.2.2
  refine ⟨⟨y, hy, hay⟩, Subtype.ext ?_⟩
  funext j
  apply Subtype.ext
  change SphereGreatCircle.curve a.val y Real.pi (τ j.castSucc.succ) = (v.val j).val
  simpa only [vertices_interior] using (hsample j.castSucc.succ).symm

theorem minimumParametrization_injective (j : Fin m) :
    Function.Injective (minimumParametrization a b τ hτ hzero hone hanti hmesh) := by
  intro y z he
  have hp := congrArg (fun v : minimumSet a b τ => tangentComponent a (v.val j).val) he
  change tangentComponent a (SphereGreatCircle.curve a.val y.val Real.pi (τ j.castSucc.succ)) =
    tangentComponent a (SphereGreatCircle.curve a.val z.val Real.pi (τ j.castSucc.succ)) at hp
  rw [tangentComponent_curve, tangentComponent_curve] at hp
  exact Subtype.ext (smul_right_injective (M := Vector (n + 1))
    (ne_of_gt (sin_pi_mul_pos (interior_time_mem τ hτ hzero hone j))) hp)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
