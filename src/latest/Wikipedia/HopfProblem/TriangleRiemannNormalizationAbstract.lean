import Wikipedia.HopfProblem.RiemannSphereMobiusClosedDiscAnalytic

/-!
# Three-point normalization of a supplied closed-disc homeomorphism

An actual homeomorphism to the standard closed unit disc, together with
three distinct marked boundary points, gives an actual homeomorphism from
the source with its third marked point removed to a closed half-plane.
The construction is a restriction and composition of proved homeomorphisms;
it does not assert or assume a new Riemann mapping or boundary extension theorem.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TriangleRiemannNormalization

open RiemannSphere RiemannSphere.MobiusCircle

variable {K : Type*} [TopologicalSpace K]

/-- The ordinary complex coordinate of a given closed-disc homeomorphism. -/
def discCoordinate (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ℂ := e x

theorem discCoordinate_injective (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) :
    Function.Injective (discCoordinate e) := by
  intro x y he
  exact e.injective (Subtype.ext he)

theorem discCoordinate_ne (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1)
    {x y : K} (hxy : x ≠ y) : discCoordinate e x ≠ discCoordinate e y :=
  fun he => hxy (discCoordinate_injective e he)

theorem discCoordinate_norm_le (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) :
    ‖discCoordinate e x‖ ≤ 1 := by
  simpa only [discCoordinate, Metric.mem_closedBall, dist_zero_right] using (e x).property

theorem discCoordinate_continuous (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) :
    Continuous (discCoordinate e) := continuous_subtype_val.comp e.continuous

/-- The restricted disc-coordinate map. -/
def punctureMap (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K)
    (x : {x : K | x ≠ pinf}) : closedDiscWithoutPole (discCoordinate e pinf) :=
  ⟨discCoordinate e x, discCoordinate_norm_le e x, discCoordinate_ne e x.property⟩

theorem punctureMap_isEmbedding (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    IsEmbedding (punctureMap e pinf) := by
  have hs : IsEmbedding (Subtype.val : closedDiscWithoutPole (discCoordinate e pinf) → ℂ) :=
    IsEmbedding.subtypeVal
  have he : IsEmbedding (fun x : {x : K | x ≠ pinf} => e (x : K)) :=
    e.isEmbedding.comp IsEmbedding.subtypeVal
  have hv : IsEmbedding (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) :=
    IsEmbedding.subtypeVal
  have hcomp : IsEmbedding (fun x : {x : K | x ≠ pinf} => (e (x : K) : ℂ)) := hv.comp he
  exact hs.of_comp_iff.mp hcomp

theorem punctureMap_surjective (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Function.Surjective (punctureMap e pinf) := by
  intro z
  let y : Metric.closedBall (0 : ℂ) 1 := ⟨z, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1⟩
  have hx : e.symm y ≠ pinf := by
    intro he
    apply z.property.2
    have h := congrArg (discCoordinate e) he
    simpa only [discCoordinate, Homeomorph.apply_symm_apply] using h
  refine ⟨⟨e.symm y, hx⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) (e.apply_symm_apply y)

/-- Restrict the given homeomorphism and write its target as a literal
closed-disc subset of the complex plane with one point removed. -/
def punctureHomeomorph (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    {x : K | x ≠ pinf} ≃ₜ closedDiscWithoutPole (discCoordinate e pinf) :=
  (punctureMap_isEmbedding e pinf).toHomeomorphOfSurjective (punctureMap_surjective e pinf)

@[simp] theorem punctureHomeomorph_apply (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (pinf : K) (x : {x : K | x ≠ pinf}) :
    (punctureHomeomorph e pinf x : ℂ) = discCoordinate e x := rfl

@[simp] theorem punctureHomeomorph_symm_coordinate
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K)
    (z : closedDiscWithoutPole (discCoordinate e pinf)) :
    discCoordinate e ((punctureHomeomorph e pinf).symm z : K) = (z : ℂ) := by
  have h := congrArg (fun w : closedDiscWithoutPole (discCoordinate e pinf) => (w : ℂ))
    ((punctureHomeomorph e pinf).apply_symm_apply z)
  simpa only [punctureHomeomorph_apply] using h

variable (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K)
variable (h01 : p0 ≠ p1) (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf)
variable (h0 : ‖discCoordinate e p0‖ = 1) (h1 : ‖discCoordinate e p1‖ = 1)
variable (hinf : ‖discCoordinate e pinf‖ = 1)

/-- Remove the marked pole and normalize the first two marked points to
zero and one in the closed half-plane selected by the ordered triple. -/
def normalizationHomeomorph :
    {x : K | x ≠ pinf} ≃ₜ
      closedOrientedHalfPlane
        (orientation (discCoordinate e p0) (discCoordinate e p1) (discCoordinate e pinf)) :=
  (punctureHomeomorph e pinf).trans
    (closedDiscHalfPlaneHomeomorph (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf)

/-- The normalized finite coordinate is exactly the cross-ratio of the
given disc coordinate, with no replacement of the supplied map. -/
@[simp] theorem normalizationHomeomorph_apply (x : {x : K | x ≠ pinf}) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ) =
      crossRatio (discCoordinate e p0) (discCoordinate e p1) (discCoordinate e pinf)
        (discCoordinate e x) := by
  exact closedDiscHalfPlaneHomeomorph_apply (discCoordinate_ne e h01)
    (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

@[simp] theorem normalizationHomeomorph_first :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p0, h0inf⟩ : ℂ) = 0 := by
  rw [normalizationHomeomorph_apply]
  exact crossRatio_at_zero _ _ _

@[simp] theorem normalizationHomeomorph_second :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p1, h1inf⟩ : ℂ) = 1 := by
  rw [normalizationHomeomorph_apply]
  exact crossRatio_at_one (discCoordinate_ne e h01.symm) (discCoordinate_ne e h1inf)

/-- The finite normalized coordinate belongs to the strict half-plane
exactly when the supplied disc coordinate belongs to the open disc. -/
theorem normalizationHomeomorph_strict_iff (x : {x : K | x ≠ pinf}) :
    0 < orientation (discCoordinate e p0) (discCoordinate e p1) (discCoordinate e pinf) *
      (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ).im ↔
        ‖discCoordinate e x‖ < 1 := by
  exact closedDiscHalfPlaneHomeomorph_strict_iff (discCoordinate_ne e h01)
    (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

/-- The remaining marked boundary goes precisely to the real line. -/
theorem normalizationHomeomorph_boundary_iff (x : {x : K | x ≠ pinf}) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ).im = 0 ↔
      ‖discCoordinate e x‖ = 1 := by
  exact closedDiscHalfPlaneHomeomorph_im_eq_zero_iff (discCoordinate_ne e h01)
    (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

/-- The inverse is explicit in the original closed-disc coordinate. -/
@[simp] theorem normalizationHomeomorph_symm_coordinate
    (w : closedOrientedHalfPlane
      (orientation (discCoordinate e p0) (discCoordinate e p1) (discCoordinate e pinf))) :
    discCoordinate e
      ((normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf).symm w : K) =
        inverseCrossRatio (discCoordinate e p0) (discCoordinate e p1)
          (discCoordinate e pinf) w := by
  change discCoordinate e ((punctureHomeomorph e pinf).symm
    ((closedDiscHalfPlaneHomeomorph (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf).symm w) : K) = _
  rw [punctureHomeomorph_symm_coordinate, closedDiscHalfPlaneHomeomorph_symm_apply]

include h01 h0inf h1inf h0 h1 hinf in
theorem normalization_orientation_ne_zero :
    orientation (discCoordinate e p0) (discCoordinate e p1) (discCoordinate e pinf) ≠ 0 :=
  orientation_ne_zero h0 h1 hinf (discCoordinate_ne e h01.symm)
    (discCoordinate_ne e h1inf) (discCoordinate_ne e h0inf)

end Wikipedia.HopfProblem.TriangleRiemannNormalization
