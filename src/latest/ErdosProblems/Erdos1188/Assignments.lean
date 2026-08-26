import ErdosProblems.Erdos1188.ArithmeticFrame

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Injective assignments of frame supports
-/

namespace Erdos1188

variable {n : ℕ} (q : Fin n → ℕ)

abbrev NonzeroResidue (m : ℕ) := {a : ZMod m // a ≠ 0}

theorem card_nonzeroResidue (m : ℕ) [NeZero m] :
    Fintype.card (NonzeroResidue m) = m - 1 := by
  calc
    Fintype.card (NonzeroResidue m) = Fintype.card (ZMod m) - 1 :=
      Set.card_ne_eq (0 : ZMod m)
    _ = m - 1 := by rw [ZMod.card]

theorem card_earlierSubsets (i : Fin n) :
    Fintype.card (Finset (Fin i.val)) = 2 ^ i.val := by
  simp [Fintype.card_finset]

abbrev ProperEarlierSubsets (i : Fin n) :=
  {s : Finset (Fin i.val) // s ≠ Finset.univ}

theorem card_properEarlierSubsets (i : Fin n) :
    Fintype.card (ProperEarlierSubsets i) = 2 ^ i.val - 1 := by
  simpa [ProperEarlierSubsets, card_earlierSubsets] using
    (Set.card_ne_eq (α := Finset (Fin i.val)) (Finset.univ : Finset (Fin i.val)))

/-- Embed the first `i` finite indices as precisely the coordinates earlier
than `i : Fin n`. -/
def earlierEmbedding (i : Fin n) : Fin i.val ↪ Fin n where
  toFun j := ⟨j.val, lt_trans j.isLt i.isLt⟩
  inj' _ _ h := Fin.ext (Fin.mk.inj h)

/-- An assignment gives every nonzero value in coordinate `i` a distinct
subset of the `i` earlier coordinates. -/
abbrev FrameAssignment (q : Fin n → ℕ) :=
  (i : Fin n) → NonzeroResidue (q i) ↪ Finset (Fin i.val)

/-- If each coordinate has no more nonzero values than subsets of its earlier
coordinates, injective assignments exist. -/
theorem frameAssignment_nonempty
    [(i : Fin n) → NeZero (q i)]
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) : Nonempty (FrameAssignment q) := by
  classical
  have hi : ∀ i : Fin n,
      Nonempty (NonzeroResidue (q i) ↪ Finset (Fin i.val)) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    simpa [card_nonzeroResidue, card_earlierSubsets] using hcap i
  exact ⟨fun i => Classical.choice (hi i)⟩

/-- At a designated coordinate, one may choose the assignment to avoid the
full earlier set if there is one fewer unit of capacity. -/
theorem frameAssignment_exists_avoiding
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (htop : q top - 1 ≤ 2 ^ top.val - 1) :
    ∃ A : FrameAssignment q, ∀ a, A top a ≠ Finset.univ := by
  classical
  have hordinary : ∀ i : Fin n,
      Nonempty (NonzeroResidue (q i) ↪ Finset (Fin i.val)) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    simpa [card_nonzeroResidue, card_earlierSubsets] using hcap i
  have hproper : Nonempty (NonzeroResidue (q top) ↪ ProperEarlierSubsets top) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [card_nonzeroResidue, card_properEarlierSubsets] using htop
  let ep := Classical.choice hproper
  let eo := fun i => Classical.choice (hordinary i)
  let A : FrameAssignment q := fun i =>
    if h : i = top then
      h ▸ (ep.trans (Function.Embedding.subtype fun s : Finset (Fin top.val) =>
        s ≠ Finset.univ))
    else eo i
  refine ⟨A, ?_⟩
  intro a
  simp only [A, dif_pos rfl]
  exact (ep a).property

/-- Convert an assignment into the earlier-coordinate fixed sets of a frame. -/
def assignedFixed (A : FrameAssignment q)
    (c : FrameChoice (fun i => ZMod (q i))) : Finset (Fin n) :=
  (A c.index ⟨c.value, c.value_ne_zero⟩).map (earlierEmbedding c.index)

/-- Assigned fixed coordinates really are earlier. -/
theorem assignedFixed_fixesEarlier (A : FrameAssignment q) :
    FrameFixesEarlier (fun i => ZMod (q i)) (assignedFixed q A) := by
  intro c j hj
  rw [assignedFixed, Finset.mem_map] at hj
  obtain ⟨k, _, rfl⟩ := hj
  exact k.isLt

/-- At one distinguished coordinate, equality of assigned fixed sets forces
frame-choice equality. -/
theorem assignedFixed_local_injective (A : FrameAssignment q) :
    ∀ c d : FrameChoice (fun i => ZMod (q i)),
      c.index = d.index → assignedFixed q A c = assignedFixed q A d → c = d := by
  intro c d hindex hfixed
  cases c with
  | mk ci cv hcv =>
      cases d with
      | mk di dv hdv =>
          simp only at hindex
          subst di
          simp only [assignedFixed] at hfixed
          have hsets : A ci ⟨cv, hcv⟩ = A ci ⟨dv, hdv⟩ :=
            Finset.map_injective (earlierEmbedding ci) hfixed
          have hvals : (⟨cv, hcv⟩ : NonzeroResidue (q ci)) = ⟨dv, hdv⟩ :=
            (A ci).injective hsets
          have : cv = dv := congrArg Subtype.val hvals
          subst dv
          rfl

/-- Avoiding the full earlier set at a greatest coordinate ensures that no
non-axis frame support equals the full coordinate set. -/
theorem assignedFrameSupport_proper_of_avoiding
    (A : FrameAssignment q) (top : Fin n)
    (htop : ∀ i : Fin n, i ≤ top)
    (havoid : ∀ a, A top a ≠ Finset.univ) :
    ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ := by
  intro c hfull
  have htmem : top ∈ frameSupport q (assignedFixed q A) c := by
    rw [hfull]
    exact Finset.mem_univ top
  have htopindex : top = c.index := by
    rcases Finset.mem_insert.mp htmem with heq | hmem
    · exact heq
    · have hlt : top < c.index := assignedFixed_fixesEarlier q A c top hmem
      exact False.elim ((not_lt_of_ge (htop c.index)) hlt)
  cases c with
  | mk ci cv hcv =>
      simp only at htopindex
      subst ci
      apply havoid ⟨cv, hcv⟩
      apply Finset.eq_univ_of_forall
      intro k
      have hkmem : earlierEmbedding top k ∈
          frameSupport q (assignedFixed q A) ⟨top, cv, hcv⟩ := by
        rw [hfull]
        exact Finset.mem_univ _
      rcases Finset.mem_insert.mp hkmem with heq | hfixed
      · have : k.val = top.val := congrArg Fin.val heq
        exact False.elim ((ne_of_lt k.isLt) this)
      · rw [assignedFixed, Finset.mem_map] at hfixed
        obtain ⟨u, hu, huk⟩ := hfixed
        have : u = k := (earlierEmbedding top).injective huk
        simpa [this] using hu

/-- Every assignment has injective non-axis supports. -/
theorem assignedFrameSupport_injective (A : FrameAssignment q) :
    Function.Injective (frameSupport q (assignedFixed q A)) := by
  apply frameSupport_injective_of_local q (assignedFixed q A)
    (assignedFixed_fixesEarlier q A)
  exact assignedFixed_local_injective q A

/-- If no assigned support is the whole coordinate set, the full support map,
including the axis support, is injective. -/
theorem assignedFullFrameSupport_injective (A : FrameAssignment q)
    (hproper : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ) :
    Function.Injective (fullFrameSupport q (assignedFixed q A)) := by
  exact fullFrameSupport_injective_of q (assignedFixed q A)
    (assignedFrameSupport_injective q A) hproper

/-- Capacity theorem: pairwise-coprime factors support a minimal distinct
cover whenever every coordinate's nonzero values fit injectively among earlier
subsets and the greatest coordinate fits among the proper earlier subsets. -/
theorem exists_assigned_minimalDistinctCover
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (htopcap : q top - 1 ≤ 2 ^ top.val - 1) :
    ∃ A : FrameAssignment q,
      IsMinimalDistinctCoveringSystem
        (Finset.univ.image
          (arithmeticFrameClass q
            (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop
            (assignedFixed q A))) := by
  obtain ⟨A, havoid⟩ := frameAssignment_exists_avoiding q top hcap htopcap
  refine ⟨A, arithmeticFrame_isMinimalDistinct_of_support q hn hq hcop
    (assignedFixed q A) (assignedFixed_fixesEarlier q A) ?_⟩
  apply assignedFullFrameSupport_injective q A
  exact assignedFrameSupport_proper_of_avoiding q A top htop havoid

end Erdos1188
