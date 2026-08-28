import Wikipedia.NoExoticSixSphere.ResidualLinkHomotopy
import Wikipedia.NoExoticSixSphere.ResidualModelCoordinates

/-!
# Parity one for the actual local residual-coordinate operator link

The actual link is homotopic through injective operators to its constant
leading-block model. A fixed general linear source change identifies that
model exactly with the checked unit cusp frame. Thus the original operator
link has parity one, and cannot extend through injective operators over a ball.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization

theorem sphereParity_inclusion (r : ℕ)
    (f : C(Sphere 3, Stiefel.Space (3 + (r + 2)) (r + 2))) :
    sphereParity r ((inclusion (3 + (r + 2)) (r + 2)).comp f) =
      sphereThirdObstruction r f := by
  unfold sphereParity
  apply congrArg (sphereThirdObstruction r)
  apply ContinuousMap.ext
  intro q
  exact normalize_inclusion (f q)

end NoExoticSixSphere.Stiefel.Monomorphism

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne CorankOneEuclidean Stiefel
open Wikipedia.HopfProblem.DegreeCollapse

theorem constantModel_parity (a : Vector 2 ≃L[ℝ] Vector 2) {ε : ℝ} (hε : 0 < ε) :
    Monomorphism.sphereParity 1 (constantModel a hε) = 1 := by
  have he := Monomorphism.sphereParity_linearCoordinates 1
    (ContinuousLinearEquiv.refl ℝ (Vector 6)) (normalizingSource a ε hε.ne')
    (constantModel a hε)
  rw [constantModel_change a hε, Monomorphism.sphereParity_inclusion] at he
  exact he.symm.trans WhitneyCusp.simpleFrame_parity

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D : X → BlockMap (Vector 2) (Vector 4)}

theorem Data.center_parity (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (d.centerOperators hε hball) = 1 := by
  obtain ⟨a, ha⟩ := d.leading_center hε hball
  have he : d.centerOperators hε hball = constantModel a hε := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean
      (diagonal (leading (D (d.coord.symm 0))) (scaledParameter ε q)) =
      CorankOneEuclidean.toEuclidean (diagonal a.toContinuousLinearMap (scaledParameter ε q))
    rw [← ha]
  rw [he]
  exact constantModel_parity a hε

theorem Data.link_parity (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (d.linkOperators hD hε hball) = 1 :=
  (d.link_parity_eq_center hD hε hball).trans (d.center_parity hε hball)

theorem Data.no_link_extension (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ¬ ∃ G : C(DiskCylinder.Disk (E := Vector 4), Monomorphism.Space 6 3),
      ∀ q, G (DiskCylinder.boundaryToDisk q) = d.linkOperators hD hε hball q := by
  intro he
  have hz := (Monomorphism.sphereParity_zero_iff_extension 1
    (d.linkOperators hD hε hball)).mpr he
  rw [d.link_parity hD hε hball] at hz
  exact one_ne_zero hz

theorem exists_local_link_parity [FiniteDimensional ℝ X]
    (D : X → BlockMap (Vector 2) (Vector 4)) (hD : ContDiff ℝ ∞ D) (x : X)
    (hx : D x ∈ chart) (hz : residual (D x) = 0)
    (hb : Bijective (fderiv ℝ (fun y ↦ residual (D y)) x)) :
    ∃ d : Data D, x ∈ d.coord.source ∧ ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target,
        Monomorphism.sphereParity 1 (d.linkOperators hD.continuous hε hball) = 1 := by
  obtain ⟨d, hdx⟩ := exists_data D hD x hx hb
  obtain ⟨ε, hε, hball⟩ := d.exists_radius hdx hz
  exact ⟨d, hdx, ε, hε, hball, d.link_parity hD.continuous hε hball⟩

end NoExoticSixSphere.ResidualCoordinates
