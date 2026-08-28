import Wikipedia.HopfProblem.FundamentalGroupVanKampenIntervalPrimitive

/-!
# Uniqueness of the global extension of local path values

A global multiplicative path value produces its own primitive along each
path.  Primitive uniqueness therefore makes the extension unique.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen.PathValue

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
variable {G : Type*} [Group G] {U : ι → Set X}
variable {L : LocalPathValue U G} {V W : PathValue X G}

/-- Prefix values of a global extension form a primitive for the local data. -/
theorem isPrimitive_subpath (hV : V.Extends L) {x y : X} (p : Path x y) :
    L.IsPrimitive p (fun t ↦ V.value (p.subpath 0 t)) := by
  intro a b hab i hi
  change V.value (p.subpath 0 b) = V.value (p.subpath 0 a) * L.value i (p.subpath a b) hi
  rw [V.subpath_mul p 0 a b bot_le hab, hV i (p.subpath a b) hi]

/-- Two extensions agree on every actual path. -/
theorem value_eq_of_extends (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) (hV : V.Extends L) (hW : W.Extends L)
    {x y : X} (p : Path x y) : V.value p = W.value p := by
  have h := L.primitive_unique hopen hcover p
    (isPrimitive_subpath hV p) (isPrimitive_subpath hW p) (by
      simp only [Path.subpath_self, V.refl, W.refl])
  have h1 := congr_fun h 1
  simpa only [value_subpath_zero_one] using h1

/-- The open-cover extension is unique as a complete path-value structure. -/
theorem eq_of_extends (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) (hV : V.Extends L) (hW : W.Extends L) : V = W := by
  have hvalue : @V.value = @W.value := by
    funext x y p
    exact value_eq_of_extends hopen hcover hV hW p
  cases V
  cases W
  cases hvalue
  rfl

end Wikipedia.HopfProblem.FundamentalGroupVanKampen.PathValue
