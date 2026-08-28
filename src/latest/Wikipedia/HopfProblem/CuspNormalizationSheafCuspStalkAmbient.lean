import Wikipedia.HopfProblem.CuspNormalizationSheafReducedAmbient
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual ambient representatives of reduced-sheaf stalk elements

Every element of the genuine colimit stalk comes from a relative
section. Its defining local ambient extension then gives an actual
ambient holomorphic representative of that same stalk element.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M) (x : S)

/-- Every actual reduced-sheaf stalk element has a representative which
is the literal restriction of an actual ambient holomorphic section. -/
theorem exists_ambient_germ_eq (φ : (presheaf I S).stalk x) :
    ∃ (V : Opens M) (hxV : x.val ∈ V) (g : HolomorphicFunctionSheaf.Section I M V),
      (presheaf I S).germ (ambientOpen S V) x hxV (ambientRestriction I S V g) = φ := by
  obtain ⟨U, hxU, f, rfl⟩ := (presheaf I S).exists_germ_eq φ
  obtain ⟨V, hxV, g, hg⟩ := f.property ⟨x, hxU⟩
  refine ⟨V, hxV, g, ?_⟩
  apply (presheaf I S).germ_ext (U ⊓ ambientOpen S V) ⟨hxU, hxV⟩
    (homOfLE inf_le_right) (homOfLE inf_le_left)
  apply Section.ext I S
  intro y
  change g ⟨y.val.val, y.property.2⟩ = f ⟨y.val, y.property.1⟩
  exact (hg ⟨y.val, y.property.1⟩ y.property.2).symm

/-- To compare ring maps out of the actual reduced stalk, it suffices to
compare them on germs of actual ambient holomorphic sections. -/
theorem stalk_hom_ext_on_ambient {R : Type*} [NonAssocSemiring R]
    (F G : (presheaf I S).stalk x →+* R)
    (h : ∀ (V : Opens M) (hxV : x.val ∈ V) (g : HolomorphicFunctionSheaf.Section I M V),
      F ((presheaf I S).germ (ambientOpen S V) x hxV (ambientRestriction I S V g)) =
        G ((presheaf I S).germ (ambientOpen S V) x hxV (ambientRestriction I S V g))) :
    F = G := by
  apply RingHom.ext
  intro φ
  obtain ⟨V, hxV, g, rfl⟩ := exists_ambient_germ_eq I S x φ
  exact h V hxV g

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
