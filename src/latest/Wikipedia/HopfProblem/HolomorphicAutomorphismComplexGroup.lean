import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# A complex Lie group from a proved multiplicative homeomorphism

Given an existing group and topology, a multiplicative homeomorphism from
the usual nonzero complex numbers gives an analytic singleton atlas. The
topology is never replaced: the atlas is obtained from an open embedding
into the punctured complex plane with the original topology on the group.
The same given equivalence is a genuine analytic diffeomorphism, and the
original multiplication and inversion are holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismComplexGroup

variable {G : Type*} [Group G] [TopologicalSpace G] (e : ℂˣ ≃ₜ* G)

/-- The single complex coordinate, read through the proved group homeomorphism. -/
def coordinate (g : G) : ℂ := (e.symm g : ℂˣ)

@[simp] theorem coordinate_equiv (u : ℂˣ) : coordinate e (e u) = (u : ℂ) := by
  simp only [coordinate, e.symm_apply_apply]

theorem coordinate_ne_zero (g : G) : coordinate e g ≠ 0 := (e.symm g).ne_zero

theorem coordinate_range : Set.range (coordinate e) = {z : ℂ | z ≠ 0} := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact coordinate_ne_zero e g
  · intro hz
    exact ⟨e (Units.mk0 z hz), by simp⟩

@[simp] theorem coordinate_mul (g h : G) :
    coordinate e (g * h) = coordinate e g * coordinate e h := by
  simp only [coordinate, map_mul, Units.val_mul]

@[simp] theorem coordinate_inv (g : G) :
    coordinate e g⁻¹ = (coordinate e g)⁻¹ := by
  simp only [coordinate, map_inv, Units.val_inv_eq_inv_val]

/-- This open embedding uses the given topology on `G`, not a transported
replacement topology. -/
theorem coordinate_isOpenEmbedding : IsOpenEmbedding (coordinate e) :=
  Units.isOpenEmbedding_val.comp e.symm.toHomeomorph.isOpenEmbedding

/-- A complex singleton atlas compatible with the unchanged topology on `G`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace ℂ G := (coordinate_isOpenEmbedding e).singletonChartedSpace

theorem chartAt_apply (g h : G) :
    letI := chartedSpace e
    chartAt ℂ g h = coordinate e h := rfl

theorem chartAt_source (g : G) :
    letI := chartedSpace e
    (chartAt ℂ g).source = Set.univ := rfl

theorem chartAt_target (g : G) :
    letI := chartedSpace e
    (chartAt ℂ g).target = {z : ℂ | z ≠ 0} := by
  let := chartedSpace e
  change ((coordinate_isOpenEmbedding e).toOpenPartialHomeomorph (coordinate e)).target = _
  rw [(coordinate_isOpenEmbedding e).toOpenPartialHomeomorph_target]
  exact coordinate_range e

/-- The original topological group is an analytic complex one-manifold
under the explicit singleton atlas. -/
theorem isManifold :
    letI := chartedSpace e
    IsManifold 𝓘(ℂ) ω G :=
  (coordinate_isOpenEmbedding e).isManifold_singleton

/-- The actual coordinate embedding is holomorphic. -/
theorem contMDiff_coordinate :
    letI := chartedSpace e
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinate e) :=
  contMDiff_isOpenEmbedding (coordinate_isOpenEmbedding e)

/-- The inverse of the given group homeomorphism is genuinely holomorphic. -/
theorem contMDiff_symm :
    letI := chartedSpace e
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (e.symm : G → ℂˣ) := by
  let := chartedSpace e
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact contMDiff_coordinate e

/-- The given group homeomorphism itself is genuinely holomorphic. -/
theorem contMDiff_equiv :
    letI := chartedSpace e
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (e : ℂˣ → G) := by
  let := chartedSpace e
  apply ContMDiff.of_comp_isOpenEmbedding (coordinate_isOpenEmbedding e)
  have heq : coordinate e ∘ e = (Units.val : ℂˣ → ℂ) := by
    funext u
    exact coordinate_equiv e u
  rw [heq]
  exact Units.contMDiff_val

/-- The same proved group homeomorphism, now as an actual analytic diffeomorphism. -/
def diffeomorph :
    letI := chartedSpace e
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂˣ G ω := by
  letI := chartedSpace e
  exact
    { toEquiv := e.toMulEquiv.toEquiv
      contMDiff_toFun := contMDiff_equiv e
      contMDiff_invFun := contMDiff_symm e }

@[simp] theorem diffeomorph_apply (u : ℂˣ) :
    letI := chartedSpace e
    diffeomorph e u = e u := rfl

@[simp] theorem diffeomorph_symm_apply (g : G) :
    letI := chartedSpace e
    (diffeomorph e).symm g = e.symm g := rfl

/-- The diffeomorphism has exactly the pre-existing homeomorphism as its
underlying topological equivalence. -/
theorem diffeomorph_toHomeomorph :
    letI := chartedSpace e
    (diffeomorph e).toHomeomorph = e.toHomeomorph := by
  let := chartedSpace e
  ext u
  rfl

theorem diffeomorph_mul (u v : ℂˣ) :
    letI := chartedSpace e
    diffeomorph e (u * v) = diffeomorph e u * diffeomorph e v := e.map_mul u v

/-- Multiplication is the original group multiplication, and is holomorphic
for the complex atlas constructed above. -/
theorem contMDiff_mul :
    letI := chartedSpace e
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ω (fun x : G × G => x.1 * x.2) := by
  let := chartedSpace e
  have hp : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ω
      (fun x : G × G => e.symm x.1 * e.symm x.2) :=
    ((contMDiff_symm e).comp contMDiff_fst).mul
      ((contMDiff_symm e).comp contMDiff_snd)
  simpa only [Function.comp_def, map_mul, e.apply_symm_apply] using
    (contMDiff_equiv e).comp hp

/-- Inversion is the original group inverse, and is holomorphic. -/
theorem contMDiff_inv :
    letI := chartedSpace e
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun g : G => g⁻¹) := by
  let := chartedSpace e
  simpa only [Function.comp_def, map_inv, e.apply_symm_apply] using
    (contMDiff_equiv e).comp (contMDiff_symm e).inv

/-- The genuine complex Lie-group structure on the existing topological
group, with no identification of `G` with a replacement underlying space. -/
theorem lieGroup :
    letI := chartedSpace e
    LieGroup 𝓘(ℂ) ω G := by
  let := chartedSpace e
  exact
    { toContMDiffMul := { toIsManifold := isManifold e, contMDiff_mul := contMDiff_mul e }
      contMDiff_inv := contMDiff_inv e }

end Wikipedia.HopfProblem.HolomorphicAutomorphismComplexGroup
