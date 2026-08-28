import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorCoefficients
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Clutching the actual order-two divisor bundle

The cover consists of the complement of the central surface and all native
canonical charts restricted to the order-four elliptic patch.  The first
piece is a trivial line; on the elliptic pieces the transitions are the
original canonical inverse Jacobians.  The mixed transitions use the
actual nonzero section coefficients and their inverses.  No global
canonical bundle is substituted for this independently clutched bundle.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace

local instance transitionsManifold : IsManifold I ω Threefold.Space :=
  Threefold.space_isManifold

/-- One trivial piece off the surface and the actual canonical charts
restricted to the full order-four elliptic patch. -/
abbrev Index := Option (atlas Model Threefold.Space)

def baseSet : Index → Set Threefold.Space
  | none => outside
  | some i => (patch : Set Threefold.Space) ∩ i.val.source

theorem isOpen_baseSet (i : Index) : IsOpen (baseSet i) := by
  cases i with
  | none => exact outside.isOpen
  | some i => exact patch.isOpen.inter i.val.open_source

def indexAt (x : Threefold.Space) : Index := by
  classical
  exact if x ∈ outside then none else some (achart Model x)

theorem mem_baseSet_at (x : Threefold.Space) : x ∈ baseSet (indexAt x) := by
  classical
  unfold indexAt
  split_ifs with hx
  · exact hx
  · exact ⟨(mem_outside_or_patch x).resolve_left hx, mem_chart_source Model x⟩

/-- The coefficient as a unit wherever nonzero; values away from such
points are irrelevant to the mixed chart overlaps. -/
def coefficientUnit (i : atlas Model Threefold.Space) (x : Threefold.Space) : ℂˣ := by
  classical
  exact if h : patchCoefficient i x ≠ 0 then Units.mk0 (patchCoefficient i x) h else 1

theorem coefficientUnit_val (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : patchCoefficient i x ≠ 0) : (coefficientUnit i x : ℂ) = patchCoefficient i x := by
  simp only [coefficientUnit, dif_pos hx, Units.val_mk0]

/-- This unit identity comes from the actual canonical coefficient
equation, on the common locus where the section does not vanish. -/
theorem coefficientUnit_change (i j : atlas Model Threefold.Space) {x : Threefold.Space}
    (hw : x ∈ patch) (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) (hg : x ∈ outside) :
    NativeTransitions.transition Threefold.Space i j x * coefficientUnit i x =
      coefficientUnit j x := by
  apply Units.ext
  change (NativeTransitions.transition Threefold.Space i j x : ℂ) *
    (coefficientUnit i x : ℂ) = (coefficientUnit j x : ℂ)
  rw [coefficientUnit_val i (patchCoefficient_ne_zero i hw hi hg),
    coefficientUnit_val j (patchCoefficient_ne_zero j hw hj hg)]
  exact patchCoefficient_change i j hi hj

/-- Actual native canonical transitions inside the elliptic patch and
the actual section coefficient for its clutching to the trivial outside. -/
def transition : Index → Index → Threefold.Space → ℂˣ
  | none, none, _ => 1
  | none, some j, x => coefficientUnit j x
  | some i, none, x => (coefficientUnit i x)⁻¹
  | some i, some j, x => NativeTransitions.transition Threefold.Space i j x

theorem transition_none_some_val (j : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : x ∈ baseSet none ∩ baseSet (some j)) :
    (transition none (some j) x : ℂ) = patchCoefficient j x :=
  coefficientUnit_val j (patchCoefficient_ne_zero j hx.2.1 hx.2.2 hx.1)

theorem transition_some_none_val (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : x ∈ baseSet (some i) ∩ baseSet none) :
    (transition (some i) none x : ℂ) = (patchCoefficient i x)⁻¹ := by
  change ((coefficientUnit i x)⁻¹ : ℂˣ).val = _
  rw [Units.val_inv_eq_inv_val, coefficientUnit_val i
    (patchCoefficient_ne_zero i hx.1.1 hx.1.2 hx.2)]

theorem transition_self (i : Index) (x : Threefold.Space) (hx : x ∈ baseSet i) :
    transition i i x = 1 := by
  cases i with
  | none => rfl
  | some i => exact NativeTransitions.transition_self Threefold.Space i x hx.2

/-- The full cocycle identities include the overlaps with the trivial
outside piece and are proved from the genuine section coefficient ratios. -/
theorem transition_comp (i j k : Index) (x : Threefold.Space)
    (hx : x ∈ baseSet i ∩ baseSet j ∩ baseSet k) :
    transition j k x * transition i j x = transition i k x := by
  cases i with
  | none =>
    cases j with
    | none => cases k <;> simp only [transition, mul_one]
    | some j =>
      cases k with
      | none => exact inv_mul_cancel (coefficientUnit j x)
      | some k =>
        exact coefficientUnit_change j k hx.1.2.1 hx.1.2.2 hx.2.2 hx.1.1
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact one_mul _
      | some k =>
        have h := coefficientUnit_change i k hx.1.1.1 hx.1.1.2 hx.2.2 hx.1.2
        change coefficientUnit k x * (coefficientUnit i x)⁻¹ = _
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
        rfl
    | some j =>
      cases k with
      | none =>
        have h := coefficientUnit_change i j hx.1.1.1 hx.1.1.2 hx.1.2.2 hx.2
        change (coefficientUnit j x)⁻¹ * NativeTransitions.transition Threefold.Space i j x = _
        rw [← h, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        rfl
      | some k =>
        exact NativeTransitions.transition_comp Threefold.Space i j k x
          ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩

theorem transition_holomorphicOn (i j : Index) :
    ContMDiffOn I I₁ ω (fun x => (transition i j x : ℂ)) (baseSet i ∩ baseSet j) := by
  cases i with
  | none =>
    cases j with
    | none => exact contMDiffOn_const
    | some j =>
      exact ((patchCoefficient_holomorphicOn j).mono inter_subset_right).congr
        (fun _ hx => transition_none_some_val j hx)
  | some i =>
    cases j with
    | none =>
      have h := ((patchCoefficient_holomorphicOn i).mono inter_subset_left).inv₀
        (fun x hx => patchCoefficient_ne_zero i hx.1.1 hx.1.2 hx.2)
      exact h.congr (fun _ hx => transition_some_none_val i hx)
    | some j =>
      exact (NativeTransitions.transition_holomorphicOn Threefold.Space i j).mono
        (fun _ hx => ⟨hx.1.2, hx.2.2⟩)

/-- The independently clutched transition data of the effective divisor
bundle, using the existing holomorphic line-bundle core construction. -/
def transitions : HolomorphicCharacterBundle.TransitionData Threefold.Space Index where
  baseSet := baseSet
  isOpen_baseSet := isOpen_baseSet
  indexAt := indexAt
  mem_baseSet_at := mem_baseSet_at
  transition := transition
  transition_self := transition_self
  transition_comp := transition_comp
  continuousOn_transition i j := (transition_holomorphicOn i j).continuousOn

instance transitions_isHolomorphic : transitions.IsHolomorphic I where
  contMDiffOn_transition := transition_holomorphicOn

/-- The local defining equation is one off the central surface and the
actual native canonical-section coefficient on every elliptic chart. -/
def localEquation : Index → Threefold.Space → ℂ
  | none, _ => 1
  | some i, x => patchCoefficient i x

theorem localEquation_holomorphicOn (i : Index) :
    ContMDiffOn I I₁ ω (localEquation i) (baseSet i) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i => exact patchCoefficient_holomorphicOn i

theorem localEquation_ne_zero_on_outside (i : Index) {x : Threefold.Space}
    (hx : x ∈ baseSet i) (hg : x ∈ outside) : localEquation i x ≠ 0 := by
  cases i with
  | none => exact one_ne_zero
  | some i => exact patchCoefficient_ne_zero i hx.1 hx.2 hg

/-- The local equations obey the actual transition-ratio identity on
the entire overlaps, including zeros on elliptic-to-elliptic overlaps. -/
theorem localEquation_change (i j : Index) {x : Threefold.Space}
    (hx : x ∈ baseSet i ∩ baseSet j) :
    (transition i j x : ℂ) * localEquation i x = localEquation j x := by
  cases i with
  | none =>
    cases j with
    | none => exact one_mul _
    | some j =>
      change (transition none (some j) x : ℂ) * 1 = patchCoefficient j x
      rw [transition_none_some_val j hx, mul_one]
  | some i =>
    cases j with
    | none =>
      change (transition (some i) none x : ℂ) * patchCoefficient i x = 1
      rw [transition_some_none_val i hx]
      exact inv_mul_cancel₀ (patchCoefficient_ne_zero i hx.1.1 hx.1.2 hx.2)
    | some j => exact patchCoefficient_change i j hx.1.2 hx.2.2

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
