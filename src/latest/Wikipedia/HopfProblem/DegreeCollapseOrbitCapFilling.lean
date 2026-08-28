import Wikipedia.HopfProblem.DegreeCollapseSeparatedMiddleSystem
import Wikipedia.SmoothSixDPoincare.ContinuousDiskExtension
import Wikipedia.SmoothSixDPoincare.SublevelDiskHomology

/-!
# A sphere reaching a contractible cap has a controlled disk filling

The continuous hitting time gives an actual flow homotopy into the cap.
Contract the endpoint inside that cap and cone the resulting homotopy.
The filling retains the exact sphere boundary and stays in the union of
the original sphere's complete orbits and the actual cap. This is the
image control needed when closing opposite middle cores.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nonempty (sphere (0 : V) 1)] [TopologicalSpace M]

def orbitSaturation (F : Flow ℝ M) (γ : C(sphere (0 : V) 1, M)) : Set M :=
  {x | ∃ z : sphere (0 : V) 1, ∃ t : ℝ, F t (γ z) = x}

theorem exists_orbit_cap_filling (F : Flow ℝ M) (γ : C(sphere (0 : V) 1, M))
    (τ : C(sphere (0 : V) 1, ℝ)) (C : Set M) [ContractibleSpace C]
    (hhit : ∀ z, F (τ z) (γ z) ∈ C) :
    ∃ K : C(closedBall (0 : V) 1, M),
      (∀ z : sphere (0 : V) 1, K ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z) ∧
      ∀ z, K z ∈ orbitSaturation F γ ∪ C := by
  let U := orbitSaturation F γ ∪ C
  let g : C(sphere (0 : V) 1, U) :=
    ⟨fun z => ⟨γ z, Or.inl ⟨z, 0, by simp⟩⟩, γ.continuous.subtype_mk _⟩
  let δ : C(sphere (0 : V) 1, C) :=
    ⟨fun z => ⟨F (τ z) (γ z), hhit z⟩,
      (F.continuous τ.continuous γ.continuous).subtype_mk _⟩
  let inclusion : C(C, U) :=
    ⟨fun x => ⟨x.val, Or.inr x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let H : g.Homotopy (inclusion.comp δ) := {
    toFun := fun p => ⟨F ((p.1 : ℝ) * τ p.2) (γ p.2), Or.inl ⟨p.2, _, rfl⟩⟩
    continuous_toFun := (F.continuous
      ((continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd))
      (γ.continuous.comp continuous_snd)).subtype_mk _
    map_zero_left := by
      intro z
      apply Subtype.ext
      change F ((0 : ℝ) * τ z) (γ z) = γ z
      simp
    map_one_left := by
      intro z
      apply Subtype.ext
      change F ((1 : ℝ) * τ z) (γ z) = F (τ z) (γ z)
      rw [one_mul] }
  obtain ⟨c, ⟨J⟩⟩ := ((id_nullhomotopic C).comp_left δ).comp_right inclusion
  let L := Wikipedia.SmoothSixDPoincare.DiskCone.extension g c (H.trans J)
  refine ⟨⟨fun z => (L z).val, continuous_subtype_val.comp L.continuous⟩, ?_, ?_⟩
  · intro z
    exact congrArg Subtype.val
      (Wikipedia.SmoothSixDPoincare.DiskCone.extension_boundary g c (H.trans J) z)
  · intro z
    exact (L z).property

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
