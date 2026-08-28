import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffineGenerators
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffineCoefficientsAnalytic
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffineEquivariance
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore

/-!
# The affine μ cocycle constructed from the actual triangle representation

The affine and holomorphic affine permutations form subgroups. The actual
two generator maps belong to these subgroups, hence so does every element
of the free product. Extracting their unique unit scale and translation
gives the affine cocycle; all cocycle identities follow from the already
constructed permutation representation. The cusp acts trivially on fibres.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

private theorem mem_subgroup_of_triangle_generators (K : Subgroup TriangleGroup)
    (h₁ : triangleGenerator₁ ∈ K) (h₂ : triangleGenerator₂ ∈ K) (g : TriangleGroup) : g ∈ K := by
  have hle : Subgroup.closure ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) ≤ K :=
    (Subgroup.closure_le _).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact h₁
      · exact h₂)
  rw [triangle_generators_generate] at hle
  exact hle (Subgroup.mem_top g)

variable {τ : ℍ → ℍ} (hτ : TauCovariant τ)

theorem representation_generatorOne_formula (z : ℍ) (u : ℂ) :
    representation hτ triangleGenerator₁ (z, u) =
      (triangleGeometricRepresentation triangleGenerator₁ z,
        (generatorOneScale τ z : ℂ) * u + generatorOneShift τ z) := by
  rw [representation_generator₁, triangleGeometricRepresentation_generator₁]
  rfl

theorem representation_generatorTwo_formula (z : ℍ) (u : ℂ) :
    representation hτ triangleGenerator₂ (z, u) =
      (triangleGeometricRepresentation triangleGenerator₂ z,
        (generatorTwoScale τ z : ℂ) * u + generatorTwoShift z) := by
  rw [representation_generator₂, triangleGeometricRepresentation_generator₂]
  rfl

/-- Every element of the actual free-product representation acts affinely
over its actual geometric base permutation, with a unit linear coefficient. -/
theorem representation_affine (g : TriangleGroup) :
    AffineFibres (representation hτ) triangleGeometricRepresentation g := by
  apply mem_subgroup_of_triangle_generators
    (affineSubgroup (representation hτ) triangleGeometricRepresentation)
  · exact ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ⟩
  · exact ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ⟩

theorem representation_fst (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    (representation hτ g (z, u)).1 = triangleGeometricRepresentation g z :=
  congrArg Prod.fst (action_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) g z u)

theorem representation_cusp_formula (z : ℍ) (u : ℂ) :
    representation hτ triangleCuspGenerator (z, u) =
      (triangleGeometricRepresentation triangleCuspGenerator z, u) :=
  Prod.ext (representation_fst hτ _ z u) (representation_cusp_snd hτ z u)

theorem representation_holomorphic_affine
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (g : TriangleGroup) :
    HolomorphicAffineFibres (representation hτ) triangleGeometricRepresentation 𝓘(ℂ) g := by
  apply mem_subgroup_of_triangle_generators
    (holomorphicAffineSubgroup (representation hτ) triangleGeometricRepresentation 𝓘(ℂ)
      triangleGeometricRepresentation_holomorphic)
  · exact ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ,
      generatorOneScale_holomorphic hτa, generatorOneShift_holomorphic hτa⟩
  · exact ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ,
      generatorTwoScale_holomorphic hτa, generatorTwoShift_holomorphic⟩

variable (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)

/-- The actual affine cocycle of the μ substitutions. Its nonvanishing,
identities, and holomorphicity have all been derived from the representation. -/
def cocycle : AffineCocycle where
  scale := scale (representation hτ) triangleGeometricRepresentation (representation_affine hτ)
  shift := shift (representation hτ) triangleGeometricRepresentation (representation_affine hτ)
  scale_one := scale_one (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ)
  shift_one := shift_one (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ)
  scale_mul := scale_mul (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ)
  shift_mul := shift_mul (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ)
  scale_holomorphic g := scale_holomorphic (representation hτ) triangleGeometricRepresentation
    𝓘(ℂ) (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)
  shift_holomorphic g := shift_holomorphic (representation hτ) triangleGeometricRepresentation
    𝓘(ℂ) (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)

/-- The packaged cocycle is exactly the fibre coordinate of the actual
permutation action, over the original Möbius action. -/
theorem cocycle_action_formula (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    representation hτ g (z, u) =
      (triangleGeometricRepresentation g z, (cocycle hτ hτa).fibreMap g z u) :=
  action_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) g z u

@[simp] theorem cocycle_scale_generator₁ (z : ℍ) :
    (cocycle hτ hτa).scale triangleGenerator₁ z = generatorOneScale τ z :=
  congrFun (scale_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_generatorOne_formula hτ)) z

@[simp] theorem cocycle_scale_generator₂ (z : ℍ) :
    (cocycle hτ hτa).scale triangleGenerator₂ z = generatorTwoScale τ z :=
  congrFun (scale_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_generatorTwo_formula hτ)) z

@[simp] theorem cocycle_shift_generator₁ (z : ℍ) :
    (cocycle hτ hτa).shift triangleGenerator₁ z = 1 / (τ z : ℂ) :=
  congrFun (shift_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_generatorOne_formula hτ)) z

@[simp] theorem cocycle_shift_generator₂ (z : ℍ) :
    (cocycle hτ hτa).shift triangleGenerator₂ z = 1 :=
  congrFun (shift_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_generatorTwo_formula hτ)) z

@[simp] theorem cocycle_scale_generator₁_val (z : ℍ) :
    ((cocycle hτ hτa).scale triangleGenerator₁ z : ℂ) = -1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₁, generatorOneScale_val]

@[simp] theorem cocycle_scale_generator₂_val (z : ℍ) :
    ((cocycle hτ hτa).scale triangleGenerator₂ z : ℂ) = 1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₂, generatorTwoScale_val]

theorem cocycle_fibreMap_generator₁ (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap triangleGenerator₁ z u = (1 - u) / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₁_val, cocycle_shift_generator₁]
  ring

theorem cocycle_fibreMap_generator₂ (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap triangleGenerator₂ z u = 1 + u / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₂_val, cocycle_shift_generator₂]
  ring

private theorem representation_cusp_affine_formula (z : ℍ) (u : ℂ) :
    representation hτ triangleCuspGenerator (z, u) =
      (triangleGeometricRepresentation triangleCuspGenerator z, ((1 : ℂˣ) : ℂ) * u + 0) := by
  simpa only [Units.val_one, one_mul, add_zero] using representation_cusp_formula hτ z u

@[simp] theorem cocycle_scale_cusp (z : ℍ) :
    (cocycle hτ hτa).scale triangleCuspGenerator z = 1 :=
  congrFun (scale_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_cusp_affine_formula hτ)) z

@[simp] theorem cocycle_shift_cusp (z : ℍ) :
    (cocycle hτ hτa).shift triangleCuspGenerator z = 0 :=
  congrFun (shift_eq_of_formula (representation hτ) triangleGeometricRepresentation
    (representation_affine hτ) (representation_cusp_affine_formula hτ)) z

@[simp] theorem cocycle_fibreMap_cusp (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap triangleCuspGenerator z u = u := by
  simp only [AffineCocycle.fibreMap, cocycle_scale_cusp, cocycle_shift_cusp,
    Units.val_one, one_mul, add_zero]

/-- Every integral cusp iterate fixes the entire affine fibre. -/
@[simp] theorem cocycle_fibreMap_cusp_zpow (n : ℤ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap (triangleCuspGenerator ^ n) z u = u :=
  ((cocycle hτ hτa).equivariant_zpow (fun _ => u) triangleCuspGenerator
    (fun w => (cocycle_fibreMap_cusp hτ hτa w u).symm) n z).symm

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
