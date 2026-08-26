import ErdosProblems.Erdos1188.Frame

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sparse frames closed by a final coordinate

A usual earlier-coordinate frame leaves only its all-zero axis uncovered.  We
close that axis with one hyperplane for every value of an extra coordinate,
instead of using a single full-support axis member.  If the closing supports
collectively contain every base coordinate, the old frame spikes remain
private after choosing a suitable value in the closing coordinate.
-/

namespace Erdos1188

universe u v

variable {m : ℕ} (S : Fin m → Type u) (T : Type v)
variable [(i : Fin m) → Zero (S i)]
variable [(i : Fin m) → DecidableEq (S i)]
variable [DecidableEq T]

/-- Members are either ordinary members of the base frame or one member for
an arbitrary value of the closing coordinate. -/
abbrev SparseFrameChoice := Sum (FrameChoice S) T

/-- A point in the base product together with its closing-coordinate value. -/
abbrev SparseFramePoint := ((i : Fin m) → S i) × T

/-- Membership in a sparse closed frame.  A closing member fixes its closing
value and fixes a selected set of base coordinates to zero. -/
def SparseFrameMember
    (fixed : FrameChoice S → Finset (Fin m))
    (closingFixed : T → Finset (Fin m))
    (c : SparseFrameChoice S T) (x : SparseFramePoint S T) : Prop :=
  match c with
  | Sum.inl b => FrameMember S fixed b x.1
  | Sum.inr a => x.2 = a ∧ ∀ j ∈ closingFixed a, x.1 j = 0

/-- The base frame plus all closing members covers the enlarged product. -/
theorem sparseFrame_covers
    (fixed : FrameChoice S → Finset (Fin m))
    (closingFixed : T → Finset (Fin m))
    (hfixed : FrameFixesEarlier S fixed)
    (x : SparseFramePoint S T) :
    ∃ c : SparseFrameChoice S T, SparseFrameMember S T fixed closingFixed c x := by
  rcases frame_covers S fixed hfixed x.1 with haxis | ⟨c, hc⟩
  · refine ⟨Sum.inr x.2, rfl, ?_⟩
    intro j _
    exact haxis j
  · exact ⟨Sum.inl c, hc⟩

/-- A closing support system can protect every old frame spike if each base
coordinate occurs in at least one closing support. -/
def ClosingProtects
    (closingFixed : T → Finset (Fin m)) (escape : Fin m → T) : Prop :=
  ∀ i, i ∈ closingFixed (escape i)

/-- Private witness: closing members use the zero base point; base members use
their old spike and select a closing value whose support contains the spike
coordinate. -/
def sparseFrameWitness (escape : Fin m → T)
    (c : SparseFrameChoice S T) : SparseFramePoint S T :=
  match c with
  | Sum.inl b => (frameSpike S b, escape b.index)
  | Sum.inr a => (frameAxisPoint S, a)

/-- Every sparse-frame member has an explicit point contained in no other
member. -/
theorem sparseFrame_private
    (fixed : FrameChoice S → Finset (Fin m))
    (closingFixed : T → Finset (Fin m))
    (hfixed : FrameFixesEarlier S fixed)
    (escape : Fin m → T)
    (hprotect : ClosingProtects T closingFixed escape)
    (c : SparseFrameChoice S T) :
    SparseFrameMember S T fixed closingFixed c (sparseFrameWitness S T escape c) ∧
      ∀ d : SparseFrameChoice S T,
        SparseFrameMember S T fixed closingFixed d
          (sparseFrameWitness S T escape c) → d = c := by
  cases c with
  | inl b =>
      constructor
      · exact frameSpike_mem S fixed hfixed b
      · intro d hd
        cases d with
        | inl e =>
            exact congrArg Sum.inl (frameSpike_private S fixed b e hd)
        | inr a =>
            exfalso
            have ha : a = escape b.index := hd.1.symm
            subst a
            have hz := hd.2 b.index (hprotect b.index)
            have hnz : frameSpike S b b.index ≠ 0 := by
              simpa [frameSpike] using b.value_ne_zero
            exact hnz hz
  | inr a =>
      constructor
      · constructor
        · rfl
        · intro j _
          rfl
      · intro d hd
        cases d with
        | inl b =>
            exact False.elim (frameAxisPoint_private S fixed b hd)
        | inr b =>
            exact congrArg Sum.inr hd.1.symm

end Erdos1188
