/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedRenewalKernel

/-!
# Literal codes for a recursively decorated renewal

This is the code-level counterpart of `decoratedRenewalKernel`.  A successor
code consists, chronologically, of an inward first-hit code, one decorated
child-return code, and a code for the remaining parent renewal.  The child
interval therefore occurs once.

The main theorem is an exact Tonelli identity: if the three component code
families have the stated kernel masses, then the total mass of the assembled
decorated codes is `decoratedRenewalKernel`.  This is the algebraic bridge
between erased-spine path codes and the recursive profile row.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularDecoratedRenewalCode

open AnnularDecoratedRenewalKernel

noncomputable section

/-- Chronological code for a parent renewal with the listed decorated child
returns. -/
def DecoratedRenewalCode
    {Middle Inner Exit Child : Type}
    (InwardCode : Middle → Inner → Type)
    (ChildCode : Child → Inner → Middle → Type)
    (EscapeCode : Middle → Exit → Type) :
    List Child → Middle → Exit → Type
  | [], u, w => EscapeCode u w
  | child :: children, u, w =>
      Σ z : Inner, Σ v : Middle,
        InwardCode u z × ChildCode child z v ×
          DecoratedRenewalCode InwardCode ChildCode EscapeCode children v w

noncomputable instance decoratedRenewalCodeCountable
    {Middle Inner Exit Child : Type}
    [Countable Middle] [Countable Inner]
    (InwardCode : Middle → Inner → Type)
    (ChildCode : Child → Inner → Middle → Type)
    (EscapeCode : Middle → Exit → Type)
    [∀ u z, Countable (InwardCode u z)]
    [∀ child z v, Countable (ChildCode child z v)]
    [∀ u w, Countable (EscapeCode u w)] :
    ∀ children u w,
      Countable (DecoratedRenewalCode InwardCode ChildCode EscapeCode
        children u w)
  | [], u, w => inferInstanceAs (Countable (EscapeCode u w))
  | child :: children, u, w => by
      letI (v : Middle) : Countable
          (DecoratedRenewalCode InwardCode ChildCode EscapeCode
            children v w) :=
        decoratedRenewalCodeCountable InwardCode ChildCode EscapeCode
          children v w
      change Countable (Σ z : Inner, Σ v : Middle,
        InwardCode u z × ChildCode child z v ×
          DecoratedRenewalCode InwardCode ChildCode EscapeCode children v w)
      exact inferInstance

/-- Product mass of the literal chronological code. -/
def decoratedRenewalCodeMass
    {Middle Inner Exit Child : Type}
    {InwardCode : Middle → Inner → Type}
    {ChildCode : Child → Inner → Middle → Type}
    {EscapeCode : Middle → Exit → Type}
    (inwardMass : ∀ u z, InwardCode u z → ℝ≥0∞)
    (childMass : ∀ child z v, ChildCode child z v → ℝ≥0∞)
    (escapeMass : ∀ u w, EscapeCode u w → ℝ≥0∞) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      DecoratedRenewalCode InwardCode ChildCode EscapeCode children u w →
        ℝ≥0∞
  | [], u, w, code => escapeMass u w code
  | child :: children, u, w, code =>
      inwardMass u code.1 code.2.2.1 *
        childMass child code.1 code.2.1 code.2.2.2.1 *
          decoratedRenewalCodeMass inwardMass childMass escapeMass
            children code.2.1 w code.2.2.2.2

/-- Exact mass disintegration of chronological decorated-renewal codes. -/
theorem tsum_decoratedRenewalCodeMass
    {Middle Inner Exit Child : Type}
    [Fintype Middle] [Fintype Inner]
    {InwardCode : Middle → Inner → Type}
    {ChildCode : Child → Inner → Middle → Type}
    {EscapeCode : Middle → Exit → Type}
    (inwardMass : ∀ u z, InwardCode u z → ℝ≥0∞)
    (childMass : ∀ child z v, ChildCode child z v → ℝ≥0∞)
    (escapeMass : ∀ u w, EscapeCode u w → ℝ≥0∞)
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (hinward : ∀ u z, ∑' code, inwardMass u z code = inward u z)
    (hchild : ∀ child z v,
      ∑' code, childMass child z v code = childKernel child z v)
    (hescape : ∀ u w, ∑' code, escapeMass u w code = escape u w) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      (∑' code, decoratedRenewalCodeMass inwardMass childMass escapeMass
          children u w code) =
        decoratedRenewalKernel inward childKernel escape children u w := by
  intro children
  induction children with
  | nil =>
      intro u w
      exact hescape u w
  | cons child children ih =>
      intro u w
      rw [decoratedRenewalKernel_cons_expanded]
      change (∑' code : Σ z : Inner, Σ v : Middle,
          InwardCode u z × ChildCode child z v ×
            DecoratedRenewalCode InwardCode ChildCode EscapeCode
              children v w,
        inwardMass u code.1 code.2.2.1 *
          childMass child code.1 code.2.1 code.2.2.2.1 *
            decoratedRenewalCodeMass inwardMass childMass escapeMass
              children code.2.1 w code.2.2.2.2) = _
      rw [ENNReal.tsum_sigma', tsum_fintype]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [ENNReal.tsum_sigma', tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      change (∑' b : InwardCode u z ×
          (ChildCode child z v ×
            DecoratedRenewalCode InwardCode ChildCode EscapeCode
              children v w),
        inwardMass u z b.1 * childMass child z v b.2.1 *
          decoratedRenewalCodeMass inwardMass childMass escapeMass
            children v w b.2.2) = _
      rw [ENNReal.tsum_prod']
      calc
        (∑' inwardCode : InwardCode u z,
            ∑' rest : ChildCode child z v ×
                DecoratedRenewalCode InwardCode ChildCode EscapeCode
                  children v w,
              inwardMass u z inwardCode *
                childMass child z v rest.1 *
                  decoratedRenewalCodeMass inwardMass childMass escapeMass
                    children v w rest.2) =
            (∑' inwardCode : InwardCode u z, inwardMass u z inwardCode) *
              (∑' rest : ChildCode child z v ×
                  DecoratedRenewalCode InwardCode ChildCode EscapeCode
                    children v w,
                childMass child z v rest.1 *
                  decoratedRenewalCodeMass inwardMass childMass escapeMass
                    children v w rest.2) := by
              calc
                (∑' inwardCode : InwardCode u z,
                    ∑' rest : ChildCode child z v ×
                        DecoratedRenewalCode InwardCode ChildCode EscapeCode
                          children v w,
                      inwardMass u z inwardCode *
                        childMass child z v rest.1 *
                          decoratedRenewalCodeMass inwardMass childMass
                            escapeMass children v w rest.2) =
                    ∑' inwardCode : InwardCode u z,
                      inwardMass u z inwardCode *
                        (∑' rest : ChildCode child z v ×
                            DecoratedRenewalCode InwardCode ChildCode
                              EscapeCode children v w,
                          childMass child z v rest.1 *
                            decoratedRenewalCodeMass inwardMass childMass
                              escapeMass children v w rest.2) := by
                        apply tsum_congr
                        intro inwardCode
                        calc
                          (∑' rest : ChildCode child z v ×
                              DecoratedRenewalCode InwardCode ChildCode
                                EscapeCode children v w,
                            inwardMass u z inwardCode *
                              childMass child z v rest.1 *
                                decoratedRenewalCodeMass inwardMass childMass
                                  escapeMass children v w rest.2) =
                              ∑' rest : ChildCode child z v ×
                                DecoratedRenewalCode InwardCode ChildCode
                                  EscapeCode children v w,
                                inwardMass u z inwardCode *
                                  (childMass child z v rest.1 *
                                    decoratedRenewalCodeMass inwardMass
                                      childMass escapeMass children v w
                                        rest.2) := by
                                  apply tsum_congr
                                  intro rest
                                  ac_rfl
                          _ = _ := ENNReal.tsum_mul_left
                _ = _ := ENNReal.tsum_mul_right
        _ = inward u z *
            (∑' rest : ChildCode child z v ×
                DecoratedRenewalCode InwardCode ChildCode EscapeCode
                  children v w,
              childMass child z v rest.1 *
                decoratedRenewalCodeMass inwardMass childMass escapeMass
                  children v w rest.2) := by rw [hinward]
        _ = inward u z *
            (∑' childCode : ChildCode child z v,
              ∑' tail : DecoratedRenewalCode InwardCode ChildCode
                  EscapeCode children v w,
                childMass child z v childCode *
                  decoratedRenewalCodeMass inwardMass childMass escapeMass
                    children v w tail) := by
              rw [ENNReal.tsum_prod']
        _ = inward u z *
            ((∑' childCode : ChildCode child z v,
                childMass child z v childCode) *
              (∑' tail : DecoratedRenewalCode InwardCode ChildCode
                  EscapeCode children v w,
                decoratedRenewalCodeMass inwardMass childMass escapeMass
                  children v w tail)) := by
              congr 1
              calc
                (∑' childCode : ChildCode child z v,
                    ∑' tail : DecoratedRenewalCode InwardCode ChildCode
                        EscapeCode children v w,
                      childMass child z v childCode *
                        decoratedRenewalCodeMass inwardMass childMass
                          escapeMass children v w tail) =
                    ∑' childCode : ChildCode child z v,
                      childMass child z v childCode *
                        (∑' tail : DecoratedRenewalCode InwardCode
                            ChildCode EscapeCode children v w,
                          decoratedRenewalCodeMass inwardMass childMass
                            escapeMass children v w tail) := by
                        apply tsum_congr
                        intro childCode
                        exact ENNReal.tsum_mul_left
                _ = _ := ENNReal.tsum_mul_right
        _ = inward u z *
            (childKernel child z v *
              decoratedRenewalKernel inward childKernel escape
                children v w) := by rw [hchild, ih]

end

end Erdos1165.AnnularDecoratedRenewalCode
