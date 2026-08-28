import Wikipedia.HopfProblem.FundamentalGroupVanKampenIntervalPrimitive
import Wikipedia.HopfProblem.FundamentalGroupVanKampenIntervalReparam
import Wikipedia.HopfProblem.FundamentalGroupVanKampenIntervalUniqueness

/-!
# Extending local path values along the interval

The normalized primitive of local path data gives the value of an actual
path at its terminal parameter.  Uniqueness of this primitive identifies
its affine pullback with the primitive of an ordered subpath.  This proves
both subdivision and concatenation for the resulting global path value,
without invoking homotopy invariance.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen
namespace LocalPathValue

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
variable {G : Type*} [Group G] {U : ι → Set X}
variable (L : LocalPathValue U G)

/-- Local values respect equality of the underlying paths. -/
theorem value_eq_of_path_eq (i : ι) {x y : X} {p q : Path x y} (h : p = q)
    (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i) :
    L.value i p hp = L.value i q hq := by
  cases h
  rfl

/-- An ordered affine pullback of a primitive, normalized at its new origin. -/
theorem isPrimitive_subpath {x y : X} (p : Path x y) {F : I → G}
    (hF : L.IsPrimitive p F) (a b : I) (hab : a ≤ b) :
    L.IsPrimitive (p.subpath a b)
      (fun t => (F a)⁻¹ * F (Icc.convexComb a b t)) := by
  intro s t hst i hi
  have heq := subpath_subpath p a b s t
  have hlocal : ∀ v,
      p.subpath (Icc.convexComb a b s) (Icc.convexComb a b t) v ∈ U i := by
    intro v
    rw [← heq]
    exact hi v
  have hv := L.value_eq_of_path_eq i heq hi hlocal
  have hstep := hF (Icc.convexComb a b s) (Icc.convexComb a b t)
    (convexComb_monotone hab hst) i hlocal
  change (F a)⁻¹ * F (Icc.convexComb a b t) =
    ((F a)⁻¹ * F (Icc.convexComb a b s)) *
      L.value i ((p.subpath a b).subpath s t) hi
  rw [hv, hstep, mul_assoc]
  rfl

variable (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)

/-- The uniquely normalized interval primitive of the local path data. -/
def transport {x y : X} (p : Path x y) : I → G :=
  (L.exists_primitive hopen hcover p).choose

@[simp] theorem transport_zero {x y : X} (p : Path x y) :
    L.transport hopen hcover p 0 = 1 :=
  (L.exists_primitive hopen hcover p).choose_spec.1

theorem transport_isPrimitive {x y : X} (p : Path x y) :
    L.IsPrimitive p (L.transport hopen hcover p) :=
  (L.exists_primitive hopen hcover p).choose_spec.2

/-- Restriction to an ordered subpath is the normalized affine pullback. -/
theorem transport_subpath {x y : X} (p : Path x y) (a b : I) (hab : a ≤ b) (t : I) :
    L.transport hopen hcover (p.subpath a b) t =
      (L.transport hopen hcover p a)⁻¹ *
        L.transport hopen hcover p (Icc.convexComb a b t) := by
  apply congrFun (L.primitive_unique hopen hcover (p.subpath a b)
    (L.transport_isPrimitive hopen hcover (p.subpath a b))
    (L.isPrimitive_subpath p (L.transport_isPrimitive hopen hcover p) a b hab) ?_) t
  simp only [transport_zero, Icc.convexComb_zero, inv_mul_cancel]

/-- The terminal value of the normalized primitive of an actual path. -/
def rawValue {x y : X} (p : Path x y) : G :=
  L.transport hopen hcover p 1

theorem rawValue_cast {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) :
    L.rawValue hopen hcover (p.cast hx hy) = L.rawValue hopen hcover p := by
  cases hx
  cases hy
  rfl

@[simp] theorem rawValue_subpath_zero_one {x y : X} (p : Path x y) :
    L.rawValue hopen hcover (p.subpath 0 1) = L.rawValue hopen hcover p := by
  rw [Path.subpath_zero_one, L.rawValue_cast]

/-- On an ordered subinterval the value is the quotient of endpoint transports. -/
theorem rawValue_subpath {x y : X} (p : Path x y) (a b : I) (hab : a ≤ b) :
    L.rawValue hopen hcover (p.subpath a b) =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p b := by
  simpa only [rawValue, Icc.convexComb_one] using
    L.transport_subpath hopen hcover p a b hab 1

/-- Complete paths in one cover member retain their original local value. -/
theorem rawValue_local (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
    L.rawValue hopen hcover p = L.value i p hp := by
  have hs : ∀ t, p.subpath 0 1 t ∈ U i := fun t => hp _
  have h := L.transport_isPrimitive hopen hcover p 0 1 (by exact zero_le_one) i hs
  rw [L.transport_zero, one_mul] at h
  change L.rawValue hopen hcover p = _ at h
  have hc : ∀ t, p.cast p.source p.target t ∈ U i := hp
  exact h.trans ((L.value_eq_of_path_eq i (Path.subpath_zero_one p) hs hc).trans
    (L.value_cast i p p.source p.target hp hc))

theorem rawValue_refl (x : X) : L.rawValue hopen hcover (Path.refl x) = 1 := by
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hp : ∀ t, Path.refl x t ∈ U i := fun _ => hi
  rw [L.rawValue_local hopen hcover i (Path.refl x) hp, L.refl]

/-- The endpoint-transport formula gives exact multiplication under subdivision. -/
theorem rawValue_subpath_mul {x y : X} (p : Path x y) (a b c : I)
    (hab : a ≤ b) (hbc : b ≤ c) :
    L.rawValue hopen hcover (p.subpath a c) =
      L.rawValue hopen hcover (p.subpath a b) *
        L.rawValue hopen hcover (p.subpath b c) := by
  rw [L.rawValue_subpath hopen hcover p a c (hab.trans hbc),
    L.rawValue_subpath hopen hcover p a b hab,
    L.rawValue_subpath hopen hcover p b c hbc, mul_assoc, mul_inv_cancel_left]

/-- The two exact half-subpaths of a concatenation give multiplicativity. -/
theorem rawValue_trans {x y z : X} (p : Path x y) (q : Path y z) :
    L.rawValue hopen hcover (p.trans q) =
      L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
  calc
    L.rawValue hopen hcover (p.trans q) =
        L.rawValue hopen hcover ((p.trans q).subpath 0 1) :=
      (L.rawValue_subpath_zero_one hopen hcover (p.trans q)).symm
    _ = L.rawValue hopen hcover ((p.trans q).subpath 0 intervalHalf) *
        L.rawValue hopen hcover ((p.trans q).subpath intervalHalf 1) :=
      L.rawValue_subpath_mul hopen hcover (p.trans q) 0 intervalHalf 1
        unitInterval.nonneg' unitInterval.le_one'
    _ = L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
      rw [trans_subpath_first_half, trans_subpath_second_half,
        L.rawValue_cast, L.rawValue_cast]

/-- The global multiplicative value of actual paths induced by an open cover. -/
def extension : PathValue X G where
  value := L.rawValue hopen hcover
  refl := L.rawValue_refl hopen hcover
  trans := L.rawValue_trans hopen hcover
  subpath_mul := L.rawValue_subpath_mul hopen hcover

theorem extension_extends : (L.extension hopen hcover).Extends L := by
  intro i x y p hp
  exact L.rawValue_local hopen hcover i p hp

include hopen hcover in
/-- Compatible local path values on an open cover extend to all actual paths. -/
theorem exists_extension : ∃ V : PathValue X G, V.Extends L :=
  ⟨L.extension hopen hcover, L.extension_extends hopen hcover⟩

include hopen hcover in
/-- The global extension is independent of all choices made in its construction. -/
theorem existsUnique_extension : ∃! V : PathValue X G, V.Extends L := by
  refine ⟨L.extension hopen hcover, L.extension_extends hopen hcover, ?_⟩
  intro V hV
  exact PathValue.eq_of_extends hopen hcover hV (L.extension_extends hopen hcover)

end LocalPathValue
end Wikipedia.HopfProblem.FundamentalGroupVanKampen
