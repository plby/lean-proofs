import Wikipedia.HopfProblem.EllipticDiscOrbits
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Disc coordinates on an actual cyclic rotation quotient

Suppose a homeomorphism to the unit disc intertwines a group generator
with one of the actual order-three or order-four elliptic rotations, and
every group element is a bounded power of that generator.  The corresponding
positive power coordinate induces a homeomorphism from the actual orbit
quotient to the disc.  Its projection formula is exact, including the center.

The topology is proved using the open complex power map and the actual
quotient topology.  No complex atlas or alternative quotient topology is
installed, and no separate continuity hypothesis on the action is needed.
-/

noncomputable section

open Function Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TriangleQuotientPower

open Elliptic

/-- The positive power map is open on the actual unit disc, including at
the origin. -/
theorem discPower_isOpenMap (m : ℕ) (hm : 0 < m) : IsOpenMap (discPower m hm) := by
  let : NeZero m := ⟨hm.ne'⟩
  have h : IsOpenMap (fun z : Disc => (z : ℂ) ^ m) :=
    (Complex.isOpenQuotientMap_pow m).isOpenMap.comp
      unitDisc.isOpen.isOpenMap_subtype_val
  exact h.subtype_mk _

/-- Surjectivity, continuity and openness for the same disc power map. -/
theorem discPower_isOpenQuotientMap (m : ℕ) (hm : 0 < m) :
    IsOpenQuotientMap (discPower m hm) :=
  ⟨discPower_surjective m hm, discPower_continuous m hm, discPower_isOpenMap m hm⟩

variable {H Y : Type*} [Group H] [TopologicalSpace Y] [MulAction H Y]
variable (j : Kind) (e : Y ≃ₜ Disc) (a : H)
variable (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
variable (heq : ∀ y : Y, e (a • y) = familyRotation j (e y))

include heq in
/-- Generator equivariance extends to every nonnegative power. -/
theorem map_pow_smul (n : ℕ) (y : Y) :
    e ((a ^ n) • y) = (familyRotation j)^[n] (e y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, heq, ih, Function.iterate_succ_apply']

include hgen heq in
/-- Fibres of the power coordinate are exactly the actual group orbits. -/
theorem powerCoordinate_eq_iff_mem_orbit (x y : Y) :
    discPower j.order j.order_pos (e x) = discPower j.order j.order_pos (e y) ↔
      x ∈ MulAction.orbit H y := by
  rw [discPower_eq_iff_familyRotation]
  constructor
  · rintro ⟨n, hn, hxy⟩
    refine ⟨a ^ n, ?_⟩
    apply e.injective
    exact (map_pow_smul j e a heq n y).trans hxy
  · rintro ⟨h, hh⟩
    obtain ⟨n, hn, rfl⟩ := hgen h
    exact ⟨n, hn, (map_pow_smul j e a heq n y).symm.trans (congrArg e hh)⟩

/-- The power coordinate descended to the genuine orbit quotient. -/
def orbitDiscMap : Quotient (MulAction.orbitRel H Y) → Disc :=
  Quotient.lift (fun y => discPower j.order j.order_pos (e y)) fun x y hxy =>
    (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mpr hxy

@[simp] theorem orbitDiscMap_mk (y : Y) :
    orbitDiscMap j e a hgen heq (Quotient.mk (MulAction.orbitRel H Y) y) =
      discPower j.order j.order_pos (e y) := rfl

theorem orbitDiscMap_continuous : Continuous (orbitDiscMap j e a hgen heq) :=
  ((discPower_continuous j.order j.order_pos).comp e.continuous).quotient_lift _

theorem orbitDiscMap_surjective : Surjective (orbitDiscMap j e a hgen heq) := by
  intro z
  obtain ⟨w, hw⟩ := discPower_surjective j.order j.order_pos z
  refine ⟨Quotient.mk (MulAction.orbitRel H Y) (e.symm w), ?_⟩
  simpa only [orbitDiscMap_mk, e.apply_symm_apply] using hw

theorem orbitDiscMap_injective : Injective (orbitDiscMap j e a hgen heq) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hxy
  apply Quotient.sound
  exact (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mp hxy

theorem orbitDiscMap_isOpenMap : IsOpenMap (orbitDiscMap j e a hgen heq) := by
  apply IsOpenMap.of_comp
    (show Continuous (Quotient.mk (MulAction.orbitRel H Y)) from continuous_quotient_mk')
    Quotient.mk_surjective
  exact (discPower_isOpenMap j.order j.order_pos).comp e.isOpenMap

/-- The actual finite-cyclic orbit quotient, with its existing quotient
topology, is homeomorphic to the disc by the positive power coordinate. -/
def orbitDiscHomeomorph : Quotient (MulAction.orbitRel H Y) ≃ₜ Disc :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (orbitDiscMap j e a hgen heq)
      ⟨orbitDiscMap_injective j e a hgen heq, orbitDiscMap_surjective j e a hgen heq⟩)
    (orbitDiscMap_continuous j e a hgen heq) (orbitDiscMap_isOpenMap j e a hgen heq)

@[simp] theorem orbitDiscHomeomorph_mk (y : Y) :
    orbitDiscHomeomorph j e a hgen heq (Quotient.mk (MulAction.orbitRel H Y) y) =
      discPower j.order j.order_pos (e y) := rfl

/-- The inverse identifies a power-coordinate value with the orbit of
any of its lifts. -/
@[simp] theorem orbitDiscHomeomorph_symm_power (y : Y) :
    (orbitDiscHomeomorph j e a hgen heq).symm (discPower j.order j.order_pos (e y)) =
      Quotient.mk (MulAction.orbitRel H Y) y :=
  (orbitDiscHomeomorph j e a hgen heq).symm_apply_apply
    (Quotient.mk (MulAction.orbitRel H Y) y)

end Wikipedia.HopfProblem.SpecialPeriods.TriangleQuotientPower
