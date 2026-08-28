import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportIndependence
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportSubdivision

/-!
# Global radial scalar transport from the actual trivializing cover

The open cover supplies finite subordinate radial chains. Their actual
integral transport is independent of all chart and subdivision choices.
Choosing one of the constructed chains therefore defines an intrinsic
nonzero scalar in the original preferred fibre coordinates.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport

variable {ι : Type*} {A : TransitionData ComplexPlane₂ ι}

namespace ChartChain

/-- A finite monotone chart subdivision gives an actual subordinate chain. -/
def ofSubdivision {γ : ℝ → ComplexPlane₂} (n : ℕ) (t : Fin (n + 1) → ℝ)
    (c : Fin n → ι) (ht : Monotone t)
    (hc : ∀ k, MapsTo γ (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k))) :
    ChartChain A γ (t 0) (t (Fin.last n)) n := by
  induction n with
  | zero => exact .nil (t 0)
  | succ n ih =>
      have htail : Monotone (fun k : Fin (n + 1) => t k.succ) := by
        intro k l hkl
        apply ht
        exact Nat.succ_le_succ hkl
      exact .cons (c 0) (ht (Fin.zero_le _)) (hc 0)
        (ih (fun k => t k.succ) (fun k => c k.succ) htail (fun k => hc k.succ))

end ChartChain

variable (A)

/-- The actual cover, not a subdivision hypothesis, supplies a radial chain
from the origin to every point. -/
theorem exists_radial_chain (x : ComplexPlane₂) :
    ∃ n : ℕ, Nonempty (ChartChain A (radialCurve x) 0 1 n) := by
  obtain ⟨n, -, t, ht0, ht1, ht, c, hc⟩ := exists_radial_subdivision A x
  refine ⟨n, ?_⟩
  have C := ChartChain.ofSubdivision n t c ht hc
  rw [ht0, ht1] at C
  exact ⟨C⟩

/-- The length of one genuinely constructed subordinate radial chain. -/
def radialChainLength (x : ComplexPlane₂) : ℕ := (exists_radial_chain A x).choose

/-- A choice of actual chart chain, without any assumed transport properties. -/
def radialChain (x : ComplexPlane₂) :
    ChartChain A (radialCurve x) 0 1 (radialChainLength A x) :=
  Classical.choice (exists_radial_chain A x).choose_spec

/-- Transport of the scalar `1` in the preferred origin fibre coordinates to
the preferred coordinates at the endpoint. -/
def globalRadialScalar (x : ComplexPlane₂) : ℂ := (radialChain A x).scalar

theorem globalRadialScalar_ne_zero (x : ComplexPlane₂) :
    globalRadialScalar A x ≠ 0 := (radialChain A x).scalar_ne_zero

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable [A.IsHolomorphic Iℂ]

/-- Any actual subordinate radial chain computes the global scalar. This
eliminates the arbitrary choices in its definition. -/
theorem globalRadialScalar_eq_chain (x : ComplexPlane₂) {n : ℕ}
    (C : ChartChain A (radialCurve x) 0 1 n) :
    globalRadialScalar A x = C.scalar :=
  (radialChain A x).scalar_eq (radialCurve_contDiff x) C

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
