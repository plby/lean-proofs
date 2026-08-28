import Wikipedia.NoExoticSixSphere.FamilyDoublePointSymmetry
import Wikipedia.NoExoticSixSphere.InvolutionQuotient

/-!
# The actual unordered family double-point closure

This is the quotient of the actual ordered closure by swapping its two
source points, with the quotient topology. Equality in this quotient is
exactly equality of ordered representatives up to swapping.
-/

open Set Function Topology

namespace NoExoticSixSphere.FamilyEmbedding

open InvolutionQuotient

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]

abbrev UnorderedClosedDoublePoints (f : P → E → F) :=
  Orbit (swapClosure f) (swapClosure_involutive f)

def unorderedProj (f : P → E → F) : closure (doublePoints f) → UnorderedClosedDoublePoints f :=
  proj (swapClosure f) (swapClosure_involutive f)

theorem unorderedProj_eq_iff (f : P → E → F) (r s : closure (doublePoints f)) :
    unorderedProj f r = unorderedProj f s ↔ r.val = s.val ∨ swapPair r.val = s.val := by
  rw [unorderedProj, proj_eq_iff]
  constructor
  · rintro (he | he)
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (congrArg Subtype.val he)
  · rintro (he | he)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)

theorem isOpenQuotientMap_unorderedProj (f : P → E → F) :
    IsOpenQuotientMap (unorderedProj f) :=
  isOpenQuotientMap_proj (swapClosure f) (swapClosure_involutive f) (swapClosure f).continuous

theorem swapClosure_fixed_iff (f : P → E → F) (r : closure (doublePoints f)) :
    swapClosure f r = r ↔ r.val.2.1 = r.val.2.2 := by
  constructor
  · intro he
    exact congrArg (fun q : closure (doublePoints f) ↦ q.val.2.2) he
  · intro he
    exact Subtype.ext (Prod.ext rfl (Prod.ext he.symm he))

end NoExoticSixSphere.FamilyEmbedding
