import Mathlib.Topology.Maps.Proper.Basic

/-!
# An open condition holding uniformly over a compact space
-/

open Set

namespace NoExoticSixSphere

/-- Universal quantification over a compact factor preserves openness. -/
theorem isOpen_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {R : X → Y → Prop} (ho : IsOpen {p : X × Y | R p.1 p.2}) :
    IsOpen {x | ∀ y, R x y} := by
  have hclosed := isClosedMap_fst_of_compactSpace _ ho.isClosed_compl
  have heq : {x | ∀ y, R x y} = (Prod.fst '' {p : X × Y | ¬ R p.1 p.2})ᶜ := by
    ext x
    constructor
    · rintro h ⟨⟨x', y⟩, hn, he⟩
      change x' = x at he
      subst x'
      exact hn (h y)
    · intro h y
      by_contra hn
      exact h ⟨(x, y), hn, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

end NoExoticSixSphere
