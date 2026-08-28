import Wikipedia.NoExoticSixSphere.GenericRegularSlabBoundaryHomotopy
import Wikipedia.NoExoticSixSphere.AnnulusBoundaryCollarDisk
import Wikipedia.NoExoticSixSphere.RegularCylinderBoundaryParityCriterion
import Wikipedia.NoExoticSixSphere.IntegralKernelEndpointQuadraticValue

/-!
# Equality of the original endpoint sphere parities across an actual cylinder

Construct the generic annulus and its raw boundary-operator homotopy from
the given original collared cylinder. The two actual collar derivatives,
ordered equation-frame coordinates, and the literal outer dilation give
the original endpoint parity criteria. Homotopy preserves extendability,
so the two original parities agree. Neither endpoint is assumed to have
zero parity or zero image in the slab homology.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

open GLOrthonormalization Stiefel DiskBoundary CylinderFiberSlab
open RegularSlabDiskCollar RegularSlabCylinderCollar

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t)

theorem sphereParity_eq_of_collaredCylinder (hd : m = n + 6) (a : Sphere m)
    (u₀ : C(Sphere 3, {x : Sphere m // d.leftMap x = z}))
    (u₁ : C(Sphere 3, {x : Sphere m // d.rightMap x = z}))
    (D : d.CollaredCylinderExtension 3
      ((constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)).comp u₀)
      ((constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)).comp u₁))
    (b : Sphere 3) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
    ∀ (hu₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ u₀) (hi₀ : Injective u₀)
      (hdu₀ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) u₀ q))
      (hu₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ u₁) (hi₁ : Injective u₁)
      (hdu₁ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) u₁ q)),
      (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd).sphereParity
        (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a)
          u₀ hu₀ hi₀ hdu₀ =
      (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd).sphereParity
        (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a)
          u₁ hu₁ hi₁ hdu₁ := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
  intro hu₀ hi₀ hdu₀ hu₁ hi₁ hdu₁
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e₀ := RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd
  let e₁ := RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd
  let a₀ := RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a
  let a₁ := RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
  let aN := RegularCylinderFiber.normalFrame d.map d.smooth_map z d.regular_map 6 hd a
  let f₀ :=
    (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)).comp u₀
  let f₁ :=
    (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)).comp u₁
  have hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀) := e₀.smooth.comp hu₀
  have hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁) := e₁.smooth.comp hu₁
  have hdf₀ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₀) q) := by
    intro q
    change Injective (mfderiv (𝓡 3) (𝓡 e₀.ambientDimension) (e₀.toFun ∘ u₀) q)
    rw [mfderiv_comp q (e₀.smooth.mdifferentiableAt (by simp)) (hu₀.mdifferentiableAt (by simp))]
    exact (e₀.injective_mfderiv (u₀ q)).comp (hdu₀ q)
  have hdf₁ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₁) q) := by
    intro q
    change Injective (mfderiv (𝓡 3) (𝓡 e₁.ambientDimension) (e₁.toFun ∘ u₁) q)
    rw [mfderiv_comp q (e₁.smooth.mdifferentiableAt (by simp)) (hu₁.mdifferentiableAt (by simp))]
    exact (e₁.injective_mfderiv (u₁ q)).comp (hdu₁ q)
  have hf₀inj : Injective f₀ := by
    intro q v he
    apply hi₀
    apply Subtype.ext
    exact congrArg (fun p : slab d.map z s t ↦ p.val.val.2) he
  have hf₁inj : Injective f₁ := by
    intro q v he
    apply hi₁
    apply Subtype.ext
    exact congrArg (fun p : slab d.map z s t ↦ p.val.val.2) he
  obtain ⟨g, hg, P, hg₀, hg₁, hderiv, _, hhom, _⟩ :=
    exists_original_boundary_operator_homotopy D b hd a hf₀ hf₁ hdf₀ hdf₁
      hf₀inj hf₁inj (fun _ ↦ rfl) (fun _ ↦ rfl)
  let G₀ : C(Sphere 3, Monomorphism.Space (m + 2) ((m + 2 - 7) + 4)) :=
    (e.puncturedRawFourAnnulusOperatorMap aN g hg P).comp P.innerBoundary
  let G₁ : C(Sphere 3, Monomorphism.Space (m + 2) ((m + 2 - 7) + 4)) :=
    (e.puncturedRawFourAnnulusOperatorMap aN g hg P).comp P.outerBoundary
  have hcrit₀ : e₀.sphereParity a₀ u₀ hu₀ hi₀ hdu₀ = 0 ↔ Extends G₀ := by
    apply RegularCylinderFiber.sphereParity_zero_iff_raw_boundaryOperator_extends
      d.map d.smooth_map z d.regular_map hd d.leftMap d.smooth_left d.regular_left
      d.leftTimes d.leftTimes.isOpen d.left_eq s d.left_mem a u₀ hu₀ hi₀ hdu₀
      (leftBoundaryDisk D b) (fun _ _ ↦ (contDiff_leftBoundaryDisk D b hf₀).contDiffAt)
      (leftBoundaryDisk_boundary D b) (ContinuousLinearEquiv.refl ℝ (Vector 4))
      (fun q ↦ e.fourDiskDerivative g q.val) G₀
    · intro q
      change e.rawNormalFourDiskOperator aN g q.val = _
      unfold EuclideanEmbedding.rawNormalFourDiskOperator
      rw [hg₀ q]
      rfl
    · intro q
      change fderiv ℝ (leftBoundaryDisk D b) q.val =
        (RegularCylinderFiber.collarTargetCoordinates m).toContinuousLinearMap.comp
          ((fderiv ℝ (e.toFun ∘ g) q.val).comp (ContinuousLinearMap.id ℝ (Vector 4)))
      rw [ContinuousLinearMap.comp_id, (hderiv q).1]
      exact fderiv_leftBoundaryDisk D b hf₀ q.val
    · exact leftBoundaryDisk_height_positive D b hf₀
  have hcrit₁ : e₁.sphereParity a₁ u₁ hu₁ hi₁ hdu₁ = 0 ↔ Extends G₁ := by
    apply RegularCylinderFiber.sphereParity_zero_iff_raw_boundaryOperator_extends
      d.map d.smooth_map z d.regular_map hd d.rightMap d.smooth_right d.regular_right
      d.rightTimes d.rightTimes.isOpen d.right_eq t d.right_mem a u₁ hu₁ hi₁ hdu₁
      (rightBoundaryDisk D b) (fun _ _ ↦ (contDiff_rightBoundaryDisk D b hf₁).contDiffAt)
      (rightBoundaryDisk_boundary D b) outerRadiusCoordinates
      (fun q ↦ e.fourDiskDerivative g ((2 : ℝ) • q.val)) G₁
    · intro q
      change e.rawNormalFourDiskOperator aN g ((2 : ℝ) • q.val) = _
      unfold EuclideanEmbedding.rawNormalFourDiskOperator
      rw [hg₁ q]
      rfl
    · intro q
      change fderiv ℝ (rightBoundaryDisk D b) q.val =
        (RegularCylinderFiber.collarTargetCoordinates m).toContinuousLinearMap.comp
          ((fderiv ℝ (e.toFun ∘ g) ((2 : ℝ) • q.val)).comp
            outerRadiusCoordinates.toContinuousLinearMap)
      rw [(hderiv q).2]
      exact fderiv_rightBoundaryDisk D b hf₁ q.val
    · exact rightBoundaryDisk_height_positive D b hf₁
  have hH : G₁.Homotopic G₀ := hhom
  exact zmodTwo_eq_of_zero_iff _ _
    (hcrit₀.trans ((extends_homotopic_iff hH).symm.trans hcrit₁.symm))

end NoExoticSixSphere.RegularCollaredCylinder
