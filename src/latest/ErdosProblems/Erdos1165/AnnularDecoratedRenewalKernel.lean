/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularOffspringRenewal

/-!
# Renewal kernels with recursively decorated return intervals

A completed annular child interval must be refined *inside* the renewal
which contains it.  Multiplying a full parent-gap mass by a second copy of
the child mass would count that interval twice.  This file records the
correct algebraic operation.

An ordered list `children` represents the successive completed children of
one parent gap.  At each child the walk first uses `inward`, then the
child-specific return kernel, and only then continues with the remaining
children.  The zero-child case is the final `escape`.

The main results are:

* constant unrestricted child kernels recover the existing
  `markedOffspringKernelENNReal` exactly;
* the construction is monotone in every child kernel;
* childwise bounds by scalar multiples of one unrestricted return kernel
  compose into the product of those scalars, both pointwise and after
  summing a finite exit row.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularDecoratedRenewalKernel

open AnnularOffspringRenewal

noncomputable section

/-- The one-cycle kernel obtained by composing an inward first hit with a
return from the child boundary. -/
def composedCycleKernel
    {Middle Inner : Type*} [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (u v : Middle) : ℝ≥0∞ :=
  ∑ z, inward u z * returnKernel z v

theorem composedCycleKernel_mono
    {Middle Inner : Type*} [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (left right : Inner → Middle → ℝ≥0∞)
    (hle : ∀ z v, left z v ≤ right z v)
    (u v : Middle) :
    composedCycleKernel inward left u v ≤
      composedCycleKernel inward right u v := by
  unfold composedCycleKernel
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_right (hle z v) (inward u z)

theorem composedCycleKernel_scaled
    {Middle Inner : Type*} [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (cost : ℝ≥0∞) (u v : Middle) :
    composedCycleKernel inward
        (fun z v ↦ cost * returnKernel z v) u v =
      cost * composedCycleKernel inward returnKernel u v := by
  unfold composedCycleKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  change inward u z * (cost * returnKernel z v) =
    cost * (inward u z * returnKernel z v)
  ac_rfl

theorem composedCycleKernel_ne_top
    {Middle Inner : Type*} [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (hinward : ∀ u z, inward u z ≠ ⊤)
    (hreturn : ∀ z v, returnKernel z v ≠ ⊤)
    (u v : Middle) :
    composedCycleKernel inward returnKernel u v ≠ ⊤ := by
  unfold composedCycleKernel
  exact ENNReal.sum_ne_top.mpr fun z _ ↦
    ENNReal.mul_ne_top (hinward u z) (hreturn z v)

/-- A renewal gap whose successive inner-to-middle returns carry possibly
different decorations.  Crucially, the child return is inserted here,
before the remaining parent renewal, and is therefore used exactly once. -/
def decoratedRenewalKernel
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞) :
    List Child → Middle → Exit → ℝ≥0∞
  | [], u, w => escape u w
  | child :: children, u, w =>
      ∑ v, composedCycleKernel inward (childKernel child) u v *
        decoratedRenewalKernel inward childKernel escape children v w

@[simp] theorem decoratedRenewalKernel_nil
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (u : Middle) (w : Exit) :
    decoratedRenewalKernel inward childKernel escape [] u w = escape u w :=
  rfl

theorem decoratedRenewalKernel_cons
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (child : Child) (children : List Child) (u : Middle) (w : Exit) :
    decoratedRenewalKernel inward childKernel escape
        (child :: children) u w =
      ∑ v, composedCycleKernel inward (childKernel child) u v *
        decoratedRenewalKernel inward childKernel escape children v w :=
  rfl

/-- Fully expanded successor equation.  It displays the chronological order
`inward → decorated child return → remaining parent renewal`. -/
theorem decoratedRenewalKernel_cons_expanded
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (child : Child) (children : List Child) (u : Middle) (w : Exit) :
    decoratedRenewalKernel inward childKernel escape
        (child :: children) u w =
      ∑ z, inward u z *
        ∑ v, childKernel child z v *
          decoratedRenewalKernel inward childKernel escape children v w := by
  rw [decoratedRenewalKernel_cons]
  unfold composedCycleKernel
  calc
    ∑ v, (∑ z, inward u z * childKernel child z v) *
          decoratedRenewalKernel inward childKernel escape children v w =
        ∑ v, ∑ z, (inward u z * childKernel child z v) *
          decoratedRenewalKernel inward childKernel escape children v w := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_mul]
    _ = ∑ z, ∑ v, (inward u z * childKernel child z v) *
          decoratedRenewalKernel inward childKernel escape children v w :=
      Finset.sum_comm
    _ = ∑ z, inward u z *
        ∑ v, childKernel child z v *
          decoratedRenewalKernel inward childKernel escape children v w := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ac_rfl

/-- With one common unrestricted return law, the decorated renewal is
exactly the existing offspring kernel; only the number of children matters. -/
theorem decoratedRenewalKernel_const_eq_markedOffspringKernelENNReal
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      decoratedRenewalKernel inward (fun _ ↦ returnKernel) escape
          children u w =
        markedOffspringKernelENNReal
          (composedCycleKernel inward returnKernel) escape
          children.length u w := by
  intro children
  induction children with
  | nil =>
      intro u w
      rfl
  | cons child children ih =>
      intro u w
      rw [decoratedRenewalKernel_cons]
      simp only [List.length_cons]
      rw [markedOffspringKernelENNReal_succ]
      apply Finset.sum_congr rfl
      intro v _
      rw [ih]

/-- Pointwise monotonicity in every decorated child return kernel. -/
theorem decoratedRenewalKernel_mono
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (left right : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (hle : ∀ child z v, left child z v ≤ right child z v) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      decoratedRenewalKernel inward left escape children u w ≤
        decoratedRenewalKernel inward right escape children u w := by
  intro children
  induction children with
  | nil =>
      intro u w
      exact le_rfl
  | cons child children ih =>
      intro u w
      rw [decoratedRenewalKernel_cons, decoratedRenewalKernel_cons]
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul'
        (composedCycleKernel_mono inward (left child) (right child)
          (hle child) u v)
        (ih v w)

/-- Finiteness is inherited from the three literal stopped pieces. -/
theorem decoratedRenewalKernel_ne_top
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (hinward : ∀ u z, inward u z ≠ ⊤)
    (hchild : ∀ child z v, childKernel child z v ≠ ⊤)
    (hescape : ∀ u w, escape u w ≠ ⊤) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      decoratedRenewalKernel inward childKernel escape children u w ≠ ⊤ := by
  intro children
  induction children with
  | nil =>
      intro u w
      exact hescape u w
  | cons child children ih =>
      intro u w
      rw [decoratedRenewalKernel_cons]
      exact ENNReal.sum_ne_top.mpr fun v _ ↦
        ENNReal.mul_ne_top
          (composedCycleKernel_ne_top inward (childKernel child)
            hinward (hchild child) u v)
          (ih v w)

/-- Pull a child-dependent scalar from every decorated return.  This is the
exact algebraic identity behind recursive row-cost multiplication. -/
theorem decoratedRenewalKernel_scaled_eq
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (cost : Child → ℝ≥0∞) :
    ∀ (children : List Child) (u : Middle) (w : Exit),
      decoratedRenewalKernel inward
          (fun child z v ↦ cost child * returnKernel z v)
          escape children u w =
        (children.map cost).prod *
          markedOffspringKernelENNReal
            (composedCycleKernel inward returnKernel) escape
            children.length u w := by
  intro children
  induction children with
  | nil =>
      intro u w
      simp
  | cons child children ih =>
      intro u w
      rw [decoratedRenewalKernel_cons]
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [markedOffspringKernelENNReal_succ]
      rw [show composedCycleKernel inward
          (fun z v ↦ cost child * returnKernel z v) u =
          fun v ↦ cost child *
            composedCycleKernel inward returnKernel u v by
        funext v
        exact composedCycleKernel_scaled inward returnKernel
          (cost child) u v]
      simp_rw [ih]
      calc
        ∑ v, (cost child *
              composedCycleKernel inward returnKernel u v) *
            ((List.map cost children).prod *
              markedOffspringKernelENNReal
                (composedCycleKernel inward returnKernel) escape
                children.length v w) =
            ∑ v, (cost child * (List.map cost children).prod) *
              (composedCycleKernel inward returnKernel u v *
                markedOffspringKernelENNReal
                  (composedCycleKernel inward returnKernel) escape
                  children.length v w) := by
              apply Finset.sum_congr rfl
              intro v _
              ac_rfl
        _ = (cost child * (List.map cost children).prod) *
            ∑ v, composedCycleKernel inward returnKernel u v *
              markedOffspringKernelENNReal
                (composedCycleKernel inward returnKernel) escape
                children.length v w := by rw [Finset.mul_sum]

/-- Childwise domination by scalar multiples of one unrestricted return law
composes into the product of the child costs. -/
theorem decoratedRenewalKernel_le_costProduct_mul_markedOffspringKernelENNReal
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (cost : Child → ℝ≥0∞)
    (hle : ∀ child z v,
      childKernel child z v ≤ cost child * returnKernel z v)
    (children : List Child) (u : Middle) (w : Exit) :
    decoratedRenewalKernel inward childKernel escape children u w ≤
      (children.map cost).prod *
        markedOffspringKernelENNReal
          (composedCycleKernel inward returnKernel) escape
          children.length u w := by
  calc
    decoratedRenewalKernel inward childKernel escape children u w ≤
        decoratedRenewalKernel inward
          (fun child z v ↦ cost child * returnKernel z v)
          escape children u w :=
      decoratedRenewalKernel_mono inward childKernel
        (fun child z v ↦ cost child * returnKernel z v) escape hle
        children u w
    _ = _ := decoratedRenewalKernel_scaled_eq
      inward returnKernel escape cost children u w

/-- Weak endpoint-row form.  Once the unrestricted renewal row is bounded,
the same bound is inherited with precisely the product of child costs. -/
theorem sum_decoratedRenewalKernel_le_costProduct_mul
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner] [Fintype Exit]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (returnKernel : Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (cost : Child → ℝ≥0∞)
    (hle : ∀ child z v,
      childKernel child z v ≤ cost child * returnKernel z v)
    (children : List Child) (u : Middle) (rowUpper : ℝ≥0∞)
    (hrow : ∑ w : Exit,
      markedOffspringKernelENNReal
        (composedCycleKernel inward returnKernel) escape
        children.length u w ≤ rowUpper) :
    ∑ w : Exit,
        decoratedRenewalKernel inward childKernel escape children u w ≤
      (children.map cost).prod * rowUpper := by
  calc
    ∑ w : Exit,
        decoratedRenewalKernel inward childKernel escape children u w ≤
        ∑ w : Exit, (children.map cost).prod *
          markedOffspringKernelENNReal
            (composedCycleKernel inward returnKernel) escape
            children.length u w :=
      Finset.sum_le_sum fun w _ ↦
        decoratedRenewalKernel_le_costProduct_mul_markedOffspringKernelENNReal
          inward childKernel returnKernel escape cost hle children u w
    _ = (children.map cost).prod *
        ∑ w : Exit, markedOffspringKernelENNReal
          (composedCycleKernel inward returnKernel) escape
          children.length u w := by rw [Finset.mul_sum]
    _ ≤ (children.map cost).prod * rowUpper := by gcongr

end

end Erdos1165.AnnularDecoratedRenewalKernel
