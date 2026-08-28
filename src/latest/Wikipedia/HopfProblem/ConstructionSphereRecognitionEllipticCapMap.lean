import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSolidTorus
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticNative
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticGamma
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic

/-!
# The original elliptic cap mapped to its Seifert solid torus

The actual map `(s,x) ↦ (s,γ(x))` is equivariant for the original affine
action and the native weighted solid-torus action.  It descends to an open
quotient of the actual varying-period filling, preserves the original
base projection, and is invariant under the actual real delta flow.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticCapMap

open SpecialPeriods EllipticModel EllipticGamma EllipticNative
open Wikipedia.HopfProblem.Elliptic
open TrianglePeriodFamily.GammaZero (fibreGamma)

variable {j : Kind} (D : Equivariant.Data j)

theorem coverMap_capPermutation (v : Lattice) (p : D.TotalSpace) :
    coverMap D (D.permutation v p) =
      capPermutation j.order (circleShift j.order (v 0)) (coverMap D p) := by
  rw [coverMap_permutation, capPermutation_apply, coverMap_apply, circleShift_apply,
    rotate_neg_sector]

/-- Equality of the actual finite actions, before descending the gamma map. -/
theorem coverMap_capAction (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (p : D.TotalSpace) :
    letI := D.action v hv
    letI := capAction j.order (circleShift j.order (v 0)) (circleShift_pow_order j.order (v 0))
    coverMap D (g • p) = g • coverMap D p := by
  change coverMap D ((D.permutation v ^ g.toAdd.val) p) =
    (capPermutation j.order (circleShift j.order (v 0)) ^ g.toAdd.val) (coverMap D p)
  simp only [Equiv.Perm.coe_pow]
  exact Function.Semiconj.iterate_right (coverMap_capPermutation D v) g.toAdd.val p

/-- The actual covering map followed by the original weighted finite quotient. -/
def capCoinvariantMap (v : Lattice) (hv : AdmissibleTwist j v) :
    C(D.Space v hv, SolidQuotient j.order (v 0)) := by
  let := D.action v hv.1
  let := capAction j.order (circleShift j.order (v 0)) (circleShift_pow_order j.order (v 0))
  let f : D.TotalSpace → SolidQuotient j.order (v 0) :=
    solidProject j.order (v 0) ∘ coverMap D
  have hf : ∀ (g : CyclicGroup j) (p : D.TotalSpace), f (g • p) = f p := by
    intro g p
    change solidProject j.order (v 0) (coverMap D (g • p)) =
      solidProject j.order (v 0) (coverMap D p)
    rw [coverMap_capAction D v hv.1]
    exact FiniteQuotient.project_smul (CyclicGroup j) (Disc × EllipticModel.Circle) g _
  exact ⟨FiniteQuotient.descend f hf,
    FiniteQuotient.descend_continuous f hf
      ((solidProject_isOpenQuotientMap j.order (v 0)).continuous.comp (coverMap D).continuous)⟩

@[simp] theorem capCoinvariantMap_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (p : D.TotalSpace) :
    capCoinvariantMap D v hv (D.quotient v hv p) =
      solidProject j.order (v 0) (coverMap D p) := rfl

theorem capCoinvariantMap_surjective (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (capCoinvariantMap D v hv) := by
  intro q
  obtain ⟨p, hp⟩ := (solidProject_isOpenQuotientMap j.order (v 0)).surjective q
  obtain ⟨x, hx⟩ := coverMap_surjective D p
  refine ⟨D.quotient v hv x, ?_⟩
  rw [capCoinvariantMap_quotient, hx, hp]

theorem capCoinvariantMap_isOpenMap (v : Lattice) (hv : AdmissibleTwist j v) :
    IsOpenMap (capCoinvariantMap D v hv) := by
  apply IsOpenMap.of_comp (D.quotient_continuous v hv) (D.quotient_surjective v hv)
  change IsOpenMap (solidProject j.order (v 0) ∘ coverMap D)
  exact (solidProject_isOpenQuotientMap j.order (v 0)).isOpenMap.comp
    (coverMap_isOpenMap D)

/-- The Seifert map is a genuine open quotient of the whole original cap. -/
theorem capCoinvariantMap_isOpenQuotientMap (v : Lattice) (hv : AdmissibleTwist j v) :
    IsOpenQuotientMap (capCoinvariantMap D v hv) :=
  ⟨capCoinvariantMap_surjective D v hv, (capCoinvariantMap D v hv).continuous,
    capCoinvariantMap_isOpenMap D v hv⟩

/-- Its base coordinate is the original filling projection at every point. -/
theorem capCoinvariantMap_projection (v : Lattice) (hv : AdmissibleTwist j v)
    (q : D.Space v hv) :
    solidProjection j.order (v 0) (capCoinvariantMap D v hv q) = D.projection v hv q := by
  obtain ⟨p, rfl⟩ := D.quotient_surjective v hv q
  rfl

/-- The actual delta circle acts within each fibre of the Seifert map. -/
theorem capCoinvariantMap_flow_real (v : Lattice) (hv : AdmissibleTwist j v)
    (t : ℝ) (q : D.Space v hv) :
    capCoinvariantMap D v hv (Threefold.VerticalAction.Elliptic.flow D v hv (t : ℂ) q) =
      capCoinvariantMap D v hv q := by
  obtain ⟨p, rfl⟩ := D.quotient_surjective v hv q
  rw [Threefold.VerticalAction.Elliptic.flow_quotient, capCoinvariantMap_quotient,
    capCoinvariantMap_quotient, coverMap_periodFlow_real]

/-- Product coordinates for the actual cap's Seifert quotient when the twist is primitive. -/
def capSolidTorusMap (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) : C(D.Space v hv, Disc × EllipticModel.Circle) :=
  (solidTorusHomeomorph j.order (v 0) hell : C(_, _)).comp (capCoinvariantMap D v hv)

@[simp] theorem capSolidTorusMap_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) (s : Disc) (x : RealTorus₄) :
    capSolidTorusMap D v hv hell (D.quotient v hv (s, x)) =
      (rotate (v 0 • fibreGamma x) s, j.order • fibreGamma x) := by
  exact solidTorusHomeomorph_project j.order (v 0) hell s (fibreGamma x)

theorem capSolidTorusMap_isOpenQuotientMap (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) : IsOpenQuotientMap (capSolidTorusMap D v hv hell) := by
  let e := solidTorusHomeomorph j.order (v 0) hell
  have hq := capCoinvariantMap_isOpenQuotientMap D v hv
  exact ⟨e.surjective.comp hq.surjective, e.continuous.comp hq.continuous,
    e.isOpenMap.comp hq.isOpenMap⟩

/-- Exact base preservation in the product coordinates; the circle phase is retained. -/
theorem capSolidTorusMap_projection (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) (q : D.Space v hv) :
    solidBase j.order (v 0) (capSolidTorusMap D v hv hell q) = D.projection v hv q :=
  (solidProjection_eq_solidBase j.order (v 0) hell (capCoinvariantMap D v hv q)).symm.trans
    (capCoinvariantMap_projection D v hv q)

theorem capSolidTorusMap_flow_real (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) (t : ℝ) (q : D.Space v hv) :
    capSolidTorusMap D v hv hell (Threefold.VerticalAction.Elliptic.flow D v hv (t : ℂ) q) =
      capSolidTorusMap D v hv hell q :=
  congrArg (solidTorusHomeomorph j.order (v 0) hell) (capCoinvariantMap_flow_real D v hv t q)

/-- The product's disc radius is the original root radius, on the whole actual cap. -/
theorem capSolidTorusMap_norm (v : Lattice) (hv : AdmissibleTwist j v)
    (hell : v 0 = 1 ∨ v 0 = -1) (q : D.Space v hv) :
    ‖((capSolidTorusMap D v hv hell q).1 : ℂ)‖ ^ j.order = ‖(D.projection v hv q : ℂ)‖ := by
  obtain ⟨⟨s, x⟩, rfl⟩ := D.quotient_surjective v hv q
  rw [capSolidTorusMap_quotient, rotate_norm, D.projection_quotient]
  exact (norm_pow (s : ℂ) j.order).symm

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticCapMap
