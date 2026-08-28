import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportStep

/-!
# Finite subordinate chart chains and their intrinsic scalar transport

Only monotone finite chains of actual subordinate segments are used. The
chain stores the charts and inclusion proofs, never a transport or frame.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- A monotone finite chain of genuinely subordinate curve segments. -/
inductive ChartChain (γ : ℝ → ComplexPlane₂) : ℝ → ℝ → ℕ → Type _ where
  | nil (a : ℝ) : ChartChain γ a a 0
  | cons {a d b : ℝ} {n : ℕ} (i : ι) (had : a ≤ d)
      (hchart : MapsTo γ (Icc a d) (A.baseSet i))
      (tail : ChartChain γ d b n) : ChartChain γ a b (n + 1)

namespace ChartChain

variable {A} {γ : ℝ → ComplexPlane₂} {a b : ℝ} {n : ℕ}

/-- Compose the actual local segment scalars; all coordinates are the
independently defined preferred fibre coordinates of the scalar core. -/
def scalar : {a b : ℝ} → {n : ℕ} → ChartChain A γ a b n → ℂ
  | _, _, _, .nil _ => 1
  | a, _, _, .cons (d := d) i _ _ tail => scalar tail * segmentScalar A γ i a d

@[simp] theorem scalar_nil (a : ℝ) : (ChartChain.nil (A := A) (γ := γ) a).scalar = 1 := rfl

@[simp] theorem scalar_cons {a d b : ℝ} {n : ℕ} (i : ι) (had : a ≤ d)
    (hi : MapsTo γ (Icc a d) (A.baseSet i)) (C : ChartChain A γ d b n) :
    (ChartChain.cons i had hi C).scalar = C.scalar * segmentScalar A γ i a d := rfl

theorem ordered (C : ChartChain A γ a b n) : a ≤ b := by
  induction C with
  | nil _ => exact le_rfl
  | cons _ had _ _ ih => exact had.trans ih

theorem scalar_ne_zero (C : ChartChain A γ a b n) : C.scalar ≠ 0 := by
  induction C with
  | nil _ => exact one_ne_zero
  | cons i _ _ _ ih => exact mul_ne_zero ih (segmentScalar_ne_zero A γ i _ _)

theorem scalar_eq_one_of_eq (C : ChartChain A γ a b n) (h : a = b) : C.scalar = 1 := by
  induction C with
  | nil _ => rfl
  | @cons a d b n i had hi C ih =>
      have hda : d = a := le_antisymm (by simpa only [← h] using C.ordered) had
      subst d
      subst b
      rw [scalar_cons, ih rfl,
        segmentScalar_self A γ i a (hi (left_mem_Icc.mpr le_rfl)), mul_one]

end ChartChain

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
