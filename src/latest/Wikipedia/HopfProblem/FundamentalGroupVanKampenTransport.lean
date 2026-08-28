import Wikipedia.HopfProblem.SimplyConnectedCover

/-!
# Local path values for the topological van Kampen theorem

These elementary data record values of actual paths, before quotienting
by homotopy.  The subsequent interval and square subdivision arguments
construct a global value and prove its homotopy invariance.  Values are
multiplied in the order paths are traversed; the final fundamental-group
map reverses this convention by taking inverses.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
variable {G : Type*} [Group G]

/-- Restricting a path to an ordered interval preserves membership in a set. -/
theorem subpath_mem_of_mem_Icc {x y : X} (p : Path x y) {a b : I}
    (hab : a ≤ b) {s : Set X} (hp : ∀ t ∈ Icc a b, p t ∈ s) :
    ∀ t, p.subpath a b t ∈ s := by
  apply range_subset_iff.mp
  rw [p.range_subpath_of_le a b hab]
  exact image_subset_iff.mpr hp

/-- Group-valued local path data, with actual path-composition and
subdivision laws and agreement on the intersections of cover members. -/
structure LocalPathValue (U : ι → Set X) (G : Type*) [Group G] where
  value : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) → G
  refl : ∀ i (x : X) (hx : ∀ t, Path.refl x t ∈ U i),
    value i (Path.refl x) hx = 1
  trans : ∀ i {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (hpq : ∀ t, p.trans q t ∈ U i),
    value i (p.trans q) hpq = value i p hp * value i q hq
  subpath_mul : ∀ i {x y : X} (p : Path x y) (a b c : I)
    (_ : a ≤ b) (_ : b ≤ c)
    (hab : ∀ t, p.subpath a b t ∈ U i)
    (hbc : ∀ t, p.subpath b c t ∈ U i)
    (hac : ∀ t, p.subpath a c t ∈ U i),
    value i (p.subpath a c) hac =
      value i (p.subpath a b) hab * value i (p.subpath b c) hbc
  compatible : ∀ i j {x y : X} (p : Path x y)
    (hi : ∀ t, p t ∈ U i) (hj : ∀ t, p t ∈ U j),
    value i p hi = value j p hj

namespace LocalPathValue

variable {U : ι → Set X} (L : LocalPathValue U G)

theorem value_cast (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : ∀ t, p t ∈ U i)
    (hp' : ∀ t, p.cast hx hy t ∈ U i) :
    L.value i (p.cast hx hy) hp' = L.value i p hp := by
  cases hx
  cases hy
  rfl

/-- Invariance under a homotopy whose entire square lies in one cover member. -/
def HomotopyInvariant : Prop :=
  ∀ i {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (H : Path.Homotopy p q), (∀ s, H s ∈ U i) →
      L.value i p hp = L.value i q hq

end LocalPathValue

/-- A global multiplicative value of actual paths.  Homotopy invariance
is deliberately not a field: it is proved from local invariance by the
homotopy-square subdivision theorem. -/
structure PathValue (X : Type*) [TopologicalSpace X] (G : Type*) [Group G] where
  value : ∀ {x y : X}, Path x y → G
  refl : ∀ x, value (Path.refl x) = 1
  trans : ∀ {x y z : X} (p : Path x y) (q : Path y z),
    value (p.trans q) = value p * value q
  subpath_mul : ∀ {x y : X} (p : Path x y) (a b c : I), a ≤ b → b ≤ c →
    value (p.subpath a c) = value (p.subpath a b) * value (p.subpath b c)

namespace PathValue

variable (V : PathValue X G)

theorem value_cast {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) : V.value (p.cast hx hy) = V.value p := by
  cases hx
  cases hy
  rfl

@[simp] theorem value_subpath_zero_one {x y : X} (p : Path x y) :
    V.value (p.subpath 0 1) = V.value p := by
  rw [Path.subpath_zero_one, V.value_cast]

/-- Agreement with the original values on every complete local path. -/
def Extends {U : ι → Set X} (L : LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i),
    V.value p = L.value i p hp

/-- Invariance under every actual endpoint-preserving path homotopy. -/
def HomotopyInvariant : Prop :=
  ∀ {x y : X} (p q : Path x y), Path.Homotopic p q → V.value p = V.value q

end PathValue

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
