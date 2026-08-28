import Wikipedia.HopfProblem.CuspCollapseStabilizersGroups
import Wikipedia.HopfProblem.ToricHexagon
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual phase characters on the six honeycomb edges

The quotient of the compact fibre torus by an edge stabilizer is the
ordinary unit complex circle.  The character is the integral determinant
character, and its section is given by the next primitive hexagon ray.
Both the kernel and the quotient topology are proved explicitly.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent

/-- The determinant character perpendicular to an integral direction. -/
def edgeCharacter (n : Fin 2 → ℤ) : CompactFibreTorus →* Circle where
  toFun u := u 0 ^ (-n 1) * u 1 ^ n 0
  map_one' := by simp
  map_mul' u v := by
    simp only [Pi.mul_apply, mul_zpow]
    ac_rfl

@[simp] theorem edgeCharacter_apply (n : Fin 2 → ℤ) (u : CompactFibreTorus) :
    edgeCharacter n u = u 0 ^ (-n 1) * u 1 ^ n 0 := rfl

theorem edgeCharacter_continuous (n : Fin 2 → ℤ) : Continuous (edgeCharacter n) :=
  ((continuous_apply 0).zpow (-n 1)).mul ((continuous_apply 1).zpow (n 0))

theorem edgeCharacter_edgeCompactPhase (n m : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (edgeCompactPhase m a) = a ^ (n 0 * m 1 - n 1 * m 0) := by
  change (a ^ m 0) ^ (-n 1) * (a ^ m 1) ^ n 0 = _
  rw [← zpow_mul, ← zpow_mul, ← zpow_add]
  congr 1
  ring

@[simp] theorem edgeCharacter_own_phase (n : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (edgeCompactPhase n a) = 1 := by
  rw [edgeCharacter_edgeCompactPhase]
  simp [mul_comm]

/-- The six determinant characters of the actual hexagon directions. -/
abbrev hexagonCharacter (k : Fin 6) : CompactFibreTorus →* Circle :=
  edgeCharacter (hexagonRay k)

/-- An explicit section, using the adjacent primitive lattice ray. -/
def hexagonCharacterSection (k : Fin 6) : Circle →* CompactFibreTorus :=
  edgeCompactPhase (hexagonRay (k + 1))

@[simp] theorem hexagonCharacterSection_apply (k : Fin 6) (a : Circle) (i : Fin 2) :
    hexagonCharacterSection k a i = a ^ hexagonRay (k + 1) i := rfl

theorem hexagonCharacterSection_continuous (k : Fin 6) :
    Continuous (hexagonCharacterSection k) := edgeCompactPhase_continuous _

@[simp] theorem hexagonCharacter_section (k : Fin 6) (a : Circle) :
    hexagonCharacter k (hexagonCharacterSection k a) = a := by
  rw [hexagonCharacterSection, edgeCharacter_edgeCompactPhase]
  have hd : hexagonRay k 0 * hexagonRay (k + 1) 1 -
      hexagonRay k 1 * hexagonRay (k + 1) 0 = 1 := by
    fin_cases k <;> decide
  rw [hd, zpow_one]

theorem hexagonCharacter_surjective (k : Fin 6) :
    Function.Surjective (hexagonCharacter k) :=
  fun a => ⟨hexagonCharacterSection k a, hexagonCharacter_section k a⟩

/-- Explicit unimodular decomposition of every phase into its parallel
edge phase and its character section. -/
theorem hexagonCharacter_decomposition (k : Fin 6) (u : CompactFibreTorus) :
    edgeCompactPhase (hexagonRay k) ((hexagonCharacter (k + 1) u)⁻¹) *
      hexagonCharacterSection k (hexagonCharacter k u) = u := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [hexagonCharacter, edgeCharacter, hexagonCharacterSection,
      edgeCompactPhase, hexagonRay]

/-- The kernel is exactly the original embedded edge-circle subgroup. -/
theorem ker_hexagonCharacter (k : Fin 6) :
    (hexagonCharacter k).ker = edgeCircle (hexagonRay k) := by
  ext u
  constructor
  · intro hu
    change hexagonCharacter k u = 1 at hu
    change ∃ a : Circle, edgeCompactPhase (hexagonRay k) a = u
    refine ⟨(hexagonCharacter (k + 1) u)⁻¹, ?_⟩
    simpa only [hu, map_one, mul_one] using hexagonCharacter_decomposition k u
  · rintro ⟨a, rfl⟩
    exact edgeCharacter_own_phase (hexagonRay k) a

theorem hexagonCharacter_eq_iff (k : Fin 6) (u v : CompactFibreTorus) :
    hexagonCharacter k u = hexagonCharacter k v ↔
      u⁻¹ * v ∈ edgeCircle (hexagonRay k) := by
  rw [← ker_hexagonCharacter, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

@[simp] theorem hexagonCharacter_opposite (k : Fin 6) (u : CompactFibreTorus) :
    hexagonCharacter (k + 3) u = (hexagonCharacter k u)⁻¹ := by
  simp only [hexagonCharacter, hexagonRay_opposite, edgeCharacter_apply,
    Pi.neg_apply, neg_neg, zpow_neg, mul_inv_rev, inv_inv]
  ac_rfl

/-- The phase quotient, using the actual stabilizer subgroup rather than
a replacement relation. -/
abbrev EdgePhaseQuotient (k : Fin 6) := CompactFibreTorus ⧸ edgeCircle (hexagonRay k)

/-- The character identifies the quotient group with the unit complex circle. -/
def edgePhaseQuotientEquiv (k : Fin 6) : EdgePhaseQuotient k ≃* Circle :=
  (QuotientGroup.quotientMulEquivOfEq (ker_hexagonCharacter k).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (hexagonCharacter k)
      (hexagonCharacterSection k) (hexagonCharacter_section k))

@[simp] theorem edgePhaseQuotientEquiv_mk (k : Fin 6) (u : CompactFibreTorus) :
    edgePhaseQuotientEquiv k (QuotientGroup.mk u) = hexagonCharacter k u := rfl

theorem edgePhaseQuotientEquiv_continuous (k : Fin 6) :
    Continuous (edgePhaseQuotientEquiv k) := by
  apply (QuotientGroup.isQuotientMap_mk (edgeCircle (hexagonRay k))).continuous_iff.mpr
  exact edgeCharacter_continuous (hexagonRay k)

/-- The quotient has its actual quotient topology and the usual circle topology. -/
def edgePhaseQuotientHomeomorph (k : Fin 6) : EdgePhaseQuotient k ≃ₜ Circle :=
  (edgePhaseQuotientEquiv k).toEquiv.toHomeomorphOfContinuousClosed
    (edgePhaseQuotientEquiv_continuous k) (edgePhaseQuotientEquiv_continuous k).isClosedMap

@[simp] theorem edgePhaseQuotientHomeomorph_mk (k : Fin 6) (u : CompactFibreTorus) :
    edgePhaseQuotientHomeomorph k (QuotientGroup.mk u) = hexagonCharacter k u := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
