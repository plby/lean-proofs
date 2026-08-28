import Wikipedia.NoExoticSixSphere.RoundDiskSuspensionQuotient
import Wikipedia.NoExoticSixSphere.CubicalSuspensionEvaluation
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Comparing a genuine round-disk quotient with cubical suspension

The two evaluation maps have exactly the same fibers after a specified
boundary homeomorphism. Their actual quotient maps construct a target
homeomorphism with a literal evaluation formula and the exact basepoint.
No orientation, degree, or homotopy-group identification is assumed.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.RoundDiskCubicalSuspension

open RoundDiskBoundarySegments

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y] [T2Space Y]
  (f : C(Disk (E := E), Y)) (z : Y)
  (hbase : ∀ x, f x = z ↔ x.val ∈ sphere (0 : E) 1)
  (hfiber : ∀ x y, f x = f y → f x = z ∨ x = y)
  (hsurj : Function.Surjective f)
  {n : ℕ} (e : Sphere n ≃ₜ Boundary (E := E))

def evaluation : C(unitInterval × Sphere n, Y) :=
  (RoundDiskSuspensionQuotient.evaluation f (e (spherePole n))).comp
    (Homeomorph.prodCongr (Homeomorph.refl unitInterval) e : C(_, _))

include hbase hfiber in
omit [T2Space Y] in
theorem evaluation_eq_iff (p q : unitInterval × Sphere n) :
    evaluation f e p = evaluation f e q ↔ p = q ∨
      (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = spherePole n) ∧
      (q.1 = 0 ∨ q.1 = 1 ∨ q.2 = spherePole n) := by
  have h := RoundDiskSuspensionQuotient.evaluation_eq_iff f z hbase hfiber
    (e (spherePole n)) (p.1, e p.2) (q.1, e q.2)
  change evaluation f e p = evaluation f e q ↔ _ at h
  simpa only [RoundDiskSuspensionQuotient.exceptional, mem_ofPred_eq,
    Prod.mk.injEq, e.injective.eq_iff, ← Prod.ext_iff] using h

include hbase hsurj in
omit [T2Space Y] in
theorem evaluation_surjective : Function.Surjective (evaluation f e) := by
  have hs := RoundDiskSuspensionQuotient.evaluation_surjective f z hbase hsurj
    (e (spherePole n))
  exact hs.comp (Homeomorph.prodCongr (Homeomorph.refl unitInterval) e).surjective

include hbase hsurj in
theorem evaluation_isQuotientMap : IsQuotientMap (evaluation f e) :=
  IsQuotientMap.of_surjective_continuous (evaluation_surjective f z hbase hsurj e)
    (evaluation f e).continuous

include hbase hfiber in
omit [T2Space Y] in
theorem same_fibers (p q : unitInterval × Sphere n) :
    CubicalSphereSuspension.evaluation n p = CubicalSphereSuspension.evaluation n q ↔
      evaluation f e p = evaluation f e q :=
  (CubicalSphereSuspension.evaluation_eq_iff n p q).trans
    (evaluation_eq_iff f z hbase hfiber e p q).symm

def homeomorph : Sphere (n + 1) ≃ₜ Y :=
  (CubicalSphereSuspension.evaluation_isQuotientMap n).homeomorph.symm.trans
    ((Homeomorph.Quotient.congrRight (same_fibers f z hbase hfiber e)).trans
      (evaluation_isQuotientMap f z hbase hsurj e).homeomorph)

theorem homeomorph_evaluation (p : unitInterval × Sphere n) :
    homeomorph f z hbase hfiber hsurj e (CubicalSphereSuspension.evaluation n p) =
      evaluation f e p := by
  change (evaluation_isQuotientMap f z hbase hsurj e).homeomorph
    ((Homeomorph.Quotient.congrRight (same_fibers f z hbase hfiber e))
      ((CubicalSphereSuspension.evaluation_isQuotientMap n).homeomorph.symm
        ((CubicalSphereSuspension.evaluation_isQuotientMap n).homeomorph
          (Quotient.mk _ p)))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem homeomorph_pole :
    homeomorph f z hbase hfiber hsurj e (spherePole (n + 1)) = z := by
  have h := homeomorph_evaluation f z hbase hfiber hsurj e (0, spherePole n)
  rw [CubicalSphereSuspension.evaluation_zero] at h
  refine h.trans ?_
  change f (point (e (spherePole n)) (0, e (spherePole n))) = z
  rw [point_zero]
  exact (hbase _).mpr (e (spherePole n)).property

end NoExoticSixSphere.RoundDiskCubicalSuspension
