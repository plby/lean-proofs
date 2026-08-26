import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Abstract frames

The elementary combinatorial engine behind the large lower-bound construction.
Coordinates are linearly ordered.  For every nonzero value in a coordinate we
choose a hyperplane that fixes that value and may additionally fix any earlier
coordinates to zero.  Together with the all-zero point, these hyperplanes form
a minimal cover.
-/

namespace Erdos1188

universe u

variable {n : ℕ} (S : Fin n → Type u)
variable [(i : Fin n) → Zero (S i)]
variable [(i : Fin n) → DecidableEq (S i)]

/-- An index for one of the non-axis hyperplanes of a frame. -/
structure FrameChoice where
  index : Fin n
  value : S index
  value_ne_zero : value ≠ 0

/-- `FrameChoice` is the dependent sum of a coordinate and a nonzero value. -/
def frameChoiceEquiv : FrameChoice S ≃ Σ i : Fin n, {a : S i // a ≠ 0} where
  toFun c := ⟨c.index, ⟨c.value, c.value_ne_zero⟩⟩
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [(i : Fin n) → Fintype (S i)] : Fintype (FrameChoice S) :=
  Fintype.ofEquiv (Σ i : Fin n, {a : S i // a ≠ 0}) (frameChoiceEquiv S).symm

/-- The point which is `c.value` in coordinate `c.index` and zero elsewhere. -/
def frameSpike (c : FrameChoice S) : (i : Fin n) → S i :=
  Pi.single c.index c.value

/-- `fixed c` lists the optional earlier coordinates fixed to zero in the
hyperplane indexed by `c`. -/
def FrameMember (fixed : FrameChoice S → Finset (Fin n))
    (c : FrameChoice S) (x : (i : Fin n) → S i) : Prop :=
  x c.index = c.value ∧ ∀ j ∈ fixed c, x j = 0

/-- The extra member of a frame is the all-zero point. -/
def OnFrameAxis (x : (i : Fin n) → S i) : Prop := ∀ i, x i = 0

/-- The arithmetic/frame condition: optional fixed coordinates are earlier than
that member's distinguished coordinate. -/
def FrameFixesEarlier (fixed : FrameChoice S → Finset (Fin n)) : Prop :=
  ∀ c j, j ∈ fixed c → j < c.index

/-- Every point is either the axis point or belongs to one of the frame
hyperplanes. -/
theorem frame_covers (fixed : FrameChoice S → Finset (Fin n))
    (hfixed : FrameFixesEarlier S fixed) (x : (i : Fin n) → S i) :
    OnFrameAxis S x ∨ ∃ c : FrameChoice S, FrameMember S fixed c x := by
  classical
  by_cases haxis : OnFrameAxis S x
  · exact Or.inl haxis
  · right
    let support : Finset (Fin n) := Finset.univ.filter fun i => x i ≠ 0
    have hs : support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply haxis
      intro i
      by_contra hi
      have himem : i ∈ support := by simp [support, hi]
      simpa [hempty] using himem
    let i : Fin n := support.min' hs
    have hi_mem : i ∈ support := Finset.min'_mem support hs
    have hi : x i ≠ 0 := (Finset.mem_filter.mp hi_mem).2
    let c : FrameChoice S := ⟨i, x i, hi⟩
    refine ⟨c, rfl, ?_⟩
    intro j hj
    have hji : j < i := hfixed c j hj
    by_contra hj0
    have hj_mem : j ∈ support := by simp [support, hj0]
    have hij : i ≤ j := Finset.min'_le support j hj_mem
    exact (not_le_of_gt hji) hij

/-- The spike belonging to a frame member lies in that member. -/
theorem frameSpike_mem (fixed : FrameChoice S → Finset (Fin n))
    (hfixed : FrameFixesEarlier S fixed) (c : FrameChoice S) :
    FrameMember S fixed c (frameSpike S c) := by
  constructor
  · simp [frameSpike]
  · intro j hj
    have hne : j ≠ c.index := ne_of_lt (hfixed c j hj)
    simp [frameSpike, hne]

/-- A spike is not the all-zero axis point. -/
theorem frameSpike_not_axis (c : FrameChoice S) :
    ¬ OnFrameAxis S (frameSpike S c) := by
  intro h
  have := h c.index
  simp [frameSpike, c.value_ne_zero] at this

/-- No frame hyperplane other than `c` contains the private point belonging to
`c`. -/
theorem frameSpike_private (fixed : FrameChoice S → Finset (Fin n))
    (c d : FrameChoice S)
    (hmem : FrameMember S fixed d (frameSpike S c)) : d = c := by
  classical
  have hindex : d.index = c.index := by
    by_contra hne
    have hz : frameSpike S c d.index = 0 := by simp [frameSpike, hne]
    exact d.value_ne_zero (by simpa [hz] using hmem.1.symm)
  cases c with
  | mk ci cv hc =>
      cases d with
      | mk di dv hd =>
          simp only at hindex
          subst di
          have hv : dv = cv := by
            simpa [frameSpike] using hmem.1.symm
          subst dv
          rfl

/-- Each non-axis member of a frame has an explicit private point. -/
theorem frame_has_private_point (fixed : FrameChoice S → Finset (Fin n))
    (hfixed : FrameFixesEarlier S fixed) (c : FrameChoice S) :
    FrameMember S fixed c (frameSpike S c) ∧
      ¬ OnFrameAxis S (frameSpike S c) ∧
      ∀ d : FrameChoice S, FrameMember S fixed d (frameSpike S c) → d = c := by
  exact ⟨frameSpike_mem S fixed hfixed c, frameSpike_not_axis S c,
    fun d hd => frameSpike_private S fixed c d hd⟩

/-- The all-zero point used as the axis member. -/
def frameAxisPoint : (i : Fin n) → S i := fun _ => 0

/-- The axis point belongs to the axis member. -/
theorem frameAxisPoint_on_axis : OnFrameAxis S (frameAxisPoint S) := by
  intro i
  rfl

/-- No non-axis frame hyperplane contains the axis point. -/
theorem frameAxisPoint_private (fixed : FrameChoice S → Finset (Fin n))
    (c : FrameChoice S) : ¬ FrameMember S fixed c (frameAxisPoint S) := by
  intro h
  exact c.value_ne_zero (by simpa [frameAxisPoint] using h.1.symm)

/-- Index all members of the full frame; `none` denotes the axis point. -/
def FullFrameMember (fixed : FrameChoice S → Finset (Fin n))
    (m : Option (FrameChoice S)) (x : (i : Fin n) → S i) : Prop :=
  match m with
  | none => OnFrameAxis S x
  | some c => FrameMember S fixed c x

/-- An explicit private witness for each member of the full frame. -/
def fullFrameWitness (m : Option (FrameChoice S)) : (i : Fin n) → S i :=
  match m with
  | none => frameAxisPoint S
  | some c => frameSpike S c

/-- The indexed full frame covers the product. -/
theorem fullFrame_covers (fixed : FrameChoice S → Finset (Fin n))
    (hfixed : FrameFixesEarlier S fixed) (x : (i : Fin n) → S i) :
    ∃ m : Option (FrameChoice S), FullFrameMember S fixed m x := by
  rcases frame_covers S fixed hfixed x with haxis | ⟨c, hc⟩
  · exact ⟨none, haxis⟩
  · exact ⟨some c, hc⟩

/-- Every member of the indexed full frame has a point contained in it and in
no other member.  This is the strongest direct form of deletion-minimality. -/
theorem fullFrame_private (fixed : FrameChoice S → Finset (Fin n))
    (hfixed : FrameFixesEarlier S fixed) (m : Option (FrameChoice S)) :
    FullFrameMember S fixed m (fullFrameWitness S m) ∧
      ∀ d : Option (FrameChoice S),
        FullFrameMember S fixed d (fullFrameWitness S m) → d = m := by
  cases m with
  | none =>
      constructor
      · exact frameAxisPoint_on_axis S
      · intro d hd
        cases d with
        | none => rfl
        | some c => exact False.elim (frameAxisPoint_private S fixed c hd)
  | some c =>
      constructor
      · exact frameSpike_mem S fixed hfixed c
      · intro d hd
        cases d with
        | none => exact False.elim (frameSpike_not_axis S c hd)
        | some e => simp [frameSpike_private S fixed c e hd]

end Erdos1188
