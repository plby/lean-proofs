import Mathlib.Topology.Homotopy.Basic

/-!
# Concatenating endpoint deformations with preserved properties

The ordinary two-stage homotopy concatenation joins the original
deformation to the new central endpoint interpolation. Pointwise
properties of every time slice, including equivariance and height
monotonicity, are retained by Mathlib's `HomotopyWith.trans`.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction.Concatenation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def slice (P : C(unitInterval × X, Y)) (s : unitInterval) : C(X, Y) :=
  ⟨fun x => P (s, x), P.continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem slice_apply (P : C(unitInterval × X, Y)) (s : unitInterval) (x : X) :
    slice P s x = P (s, x) := rfl

def asHomotopy (P : C(unitInterval × X, Y)) :
    (slice P 0).Homotopy (slice P 1) where
  toContinuousMap := P
  map_zero_left _ := rfl
  map_one_left _ := rfl

def connectingHomotopy (P K : C(unitInterval × X, Y))
    (hjoin : ∀ x, K (0, x) = P (1, x)) :
    (slice P 1).Homotopy (slice K 1) where
  toContinuousMap := K
  map_zero_left := hjoin
  map_one_left _ := rfl

/-- The genuine jointly continuous two-stage concatenation. -/
def map (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x)) :
    C(unitInterval × X, Y) :=
  ((asHomotopy P).trans (connectingHomotopy P K hjoin)).toContinuousMap

@[simp] theorem map_zero (P K : C(unitInterval × X, Y))
    (hjoin : ∀ x, K (0, x) = P (1, x)) (x : X) : map P K hjoin (0, x) = P (0, x) :=
  ContinuousMap.Homotopy.apply_zero _ x

@[simp] theorem map_one (P K : C(unitInterval × X, Y))
    (hjoin : ∀ x, K (0, x) = P (1, x)) (x : X) : map P K hjoin (1, x) = K (1, x) :=
  ContinuousMap.Homotopy.apply_one _ x

/-- Any property proved for every slice of both input homotopies remains
true for every slice of their actual concatenation. -/
theorem map_property (P K : C(unitInterval × X, Y))
    (hjoin : ∀ x, K (0, x) = P (1, x)) (R : C(X, Y) → Prop)
    (hP : ∀ s, R (slice P s)) (hK : ∀ s, R (slice K s)) (s : unitInterval) :
    R (slice (map P K hjoin) s) := by
  let F : (slice P 0).HomotopyWith (slice P 1) R :=
    { toHomotopy := asHomotopy P
      prop' := hP }
  let G : (slice P 1).HomotopyWith (slice K 1) R :=
    { toHomotopy := connectingHomotopy P K hjoin
      prop' := hK }
  exact (F.trans G).prop s

end Wikipedia.HopfProblem.CuspControlledRetraction.Concatenation
