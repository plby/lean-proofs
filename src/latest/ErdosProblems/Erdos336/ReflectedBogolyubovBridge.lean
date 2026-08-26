import Mathlib
import ErdosProblems.Erdos336.EndpointCoreSmoothing

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Turning a fourfold difference pattern into four positive exact powers
-/

namespace Erdos336

/-- Membership in the fourfold difference set `2C-2C`, written with explicit
witnesses so no pointwise-set convention is hidden. -/
def InFourfoldDifference (C : Set ℤ) (x : ℤ) : Prop :=
  ∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C, ∃ d ∈ C, x = a + b - c - d

/-- If `C` and its reflection `u-C` are both exactly `h`-representable by
`D`, then translating `2C-2C` by `2u` puts it in the exact `4h`-power of `D`.
This is the algebraic bridge used after finite Bogolyubov. -/
theorem reflected_fourfoldDifference_rep
    {D C : Set ℤ} {u x : ℤ} {h : ℕ}
    (hC : ∀ a ∈ C, ZRepExactly D h a)
    (hreflect : ∀ a ∈ C, ZRepExactly D h (u - a))
    (hx : InFourfoldDifference C x) :
    ZRepExactly D (4 * h) (2 * u + x) := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hx
  have hab := (hC a ha).add (hC b hb)
  have hcd := (hreflect c hc).add (hreflect d hd)
  have hsum := hab.add hcd
  convert hsum using 1
  · omega
  · ring

end Erdos336
