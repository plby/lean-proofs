import Wikipedia.NoExoticSixSphere.JamesSphereAttachingPerimeter
import Wikipedia.NoExoticSixSphere.SimplePathConcatenation

/-!
# Exact fibers of the actual four-edge clock perimeter

The previously used, left-associated perimeter covers the entire clock
boundary and identifies only its two interval endpoints. These facts
are about the actual path parameter, including its unequal edge times,
and will identify the attaching-source quotient with a sphere.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem bottom_injective : Function.Injective bottom :=
  fun _ _ h ↦ congrArg (fun p : ClockBoundary ↦ p.val 0) h

theorem right_injective : Function.Injective right :=
  fun _ _ h ↦ congrArg (fun p : ClockBoundary ↦ p.val 1) h

theorem top_symm_injective : Function.Injective top.symm := by
  intro s t h
  have he : σ s = σ t := congrArg (fun p : ClockBoundary ↦ p.val 0) h
  simpa only [unitInterval.symm_symm] using congrArg unitInterval.symm he

theorem left_symm_injective : Function.Injective left.symm := by
  intro s t h
  have he : σ s = σ t := congrArg (fun p : ClockBoundary ↦ p.val 1) h
  simpa only [unitInterval.symm_symm] using congrArg unitInterval.symm he

theorem bottom_right_meet (s t : I) (h : bottom s = right t) : s = 1 ∧ t = 0 :=
  ⟨congrArg (fun p : ClockBoundary ↦ p.val 0) h,
    (congrArg (fun p : ClockBoundary ↦ p.val 1) h).symm⟩

theorem bottom_top_ne (s t : I) : bottom s ≠ top.symm t := by
  intro h
  have he : (0 : I) = 1 := congrArg (fun p : ClockBoundary ↦ p.val 1) h
  exact zero_ne_one he

theorem right_left_ne (s t : I) : right s ≠ left.symm t := by
  intro h
  have he : (1 : I) = 0 := congrArg (fun p : ClockBoundary ↦ p.val 0) h
  exact one_ne_zero he

theorem right_top_meet (s t : I) (h : right s = top.symm t) : s = 1 ∧ t = 0 := by
  refine ⟨congrArg (fun p : ClockBoundary ↦ p.val 1) h, ?_⟩
  have he : σ t = 1 := (congrArg (fun p : ClockBoundary ↦ p.val 0) h).symm
  simpa only [unitInterval.symm_symm, unitInterval.symm_one] using congrArg unitInterval.symm he

theorem bottom_left_meet (s t : I) (h : bottom s = left.symm t) : s = 0 ∧ t = 1 := by
  refine ⟨congrArg (fun p : ClockBoundary ↦ p.val 0) h, ?_⟩
  have he : σ t = 0 := (congrArg (fun p : ClockBoundary ↦ p.val 1) h).symm
  simpa only [unitInterval.symm_symm, unitInterval.symm_zero] using congrArg unitInterval.symm he

theorem top_left_meet (s t : I) (h : top.symm s = left.symm t) : s = 1 ∧ t = 0 := by
  have hs : σ s = 0 := congrArg (fun p : ClockBoundary ↦ p.val 0) h
  have ht : σ t = 1 := (congrArg (fun p : ClockBoundary ↦ p.val 1) h).symm
  constructor
  · simpa only [unitInterval.symm_symm, unitInterval.symm_zero] using congrArg unitInterval.symm hs
  · simpa only [unitInterval.symm_symm, unitInterval.symm_one] using congrArg unitInterval.symm ht

theorem firstTwo_top_meet (s t : I) (h : bottom.trans right s = top.symm t) :
    s = 1 ∧ t = 0 := by
  rw [Path.trans_apply] at h
  split_ifs at h with hs
  · exact False.elim (bottom_top_ne _ _ h)
  · obtain ⟨h₁, h₀⟩ := right_top_meet _ _ h
    refine ⟨Subtype.ext ?_, h₀⟩
    have he := congrArg Subtype.val h₁
    change 2 * (s : ℝ) - 1 = 1 at he
    change (s : ℝ) = 1
    linarith

theorem firstTwo_left_meet (s t : I) (h : bottom.trans right s = left.symm t) :
    s = 0 ∧ t = 1 := by
  rw [Path.trans_apply] at h
  split_ifs at h with hs
  · obtain ⟨h₀, h₁⟩ := bottom_left_meet _ _ h
    refine ⟨Subtype.ext ?_, h₁⟩
    have he := congrArg Subtype.val h₀
    change 2 * (s : ℝ) = 0 at he
    change (s : ℝ) = 0
    linarith
  · exact False.elim (right_left_ne _ _ h)

theorem firstThree_left_meet (s t : I)
    (h : ((bottom.trans right).trans top.symm) s = left.symm t) :
    (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rw [Path.trans_apply] at h
  split_ifs at h with hs
  · left
    obtain ⟨h₀, h₁⟩ := firstTwo_left_meet _ _ h
    refine ⟨Subtype.ext ?_, h₁⟩
    have he := congrArg Subtype.val h₀
    change 2 * (s : ℝ) = 0 at he
    change (s : ℝ) = 0
    linarith
  · right
    obtain ⟨h₁, h₀⟩ := top_left_meet _ _ h
    refine ⟨Subtype.ext ?_, h₀⟩
    have he := congrArg Subtype.val h₁
    change 2 * (s : ℝ) - 1 = 1 at he
    change (s : ℝ) = 1
    linarith

theorem perimeter_eq_iff (s t : I) :
    perimeter s = perimeter t ↔ s = t ∨ (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) :=
  SimplePath.closed_trans_eq_iff _ _
    (SimplePath.trans_injective _ _
      (SimplePath.trans_injective _ _ bottom_injective right_injective bottom_right_meet)
      top_symm_injective firstTwo_top_meet)
    left_symm_injective firstThree_left_meet s t

theorem perimeter_eq_corner_iff (s : I) : perimeter s = corner00 ↔ s = 0 ∨ s = 1 := by
  constructor
  · intro h
    rcases (perimeter_eq_iff s 0).mp (h.trans perimeter.source.symm) with h | ⟨h, _⟩
    · exact Or.inl h
    · exact h
  · rintro (rfl | rfl)
    · exact perimeter.source
    · exact perimeter.target

theorem perimeter_surjective : Function.Surjective perimeter := by
  intro p
  have hp : p ∈ Set.range bottom ∨ p ∈ Set.range right ∨
      p ∈ Set.range top.symm ∨ p ∈ Set.range left.symm := by
    rcases p.property with ⟨i, hi | hi⟩
    · fin_cases i
      · right; right; right
        refine ⟨σ (p.val 1), ?_⟩
        apply Subtype.ext
        funext j
        fin_cases j
        · exact hi.symm
        · exact unitInterval.symm_symm _
      · left
        refine ⟨p.val 0, ?_⟩
        apply Subtype.ext
        funext j
        fin_cases j
        · rfl
        · exact hi.symm
    · fin_cases i
      · right; left
        refine ⟨p.val 1, ?_⟩
        apply Subtype.ext
        funext j
        fin_cases j
        · exact hi.symm
        · rfl
      · right; right; left
        refine ⟨σ (p.val 0), ?_⟩
        apply Subtype.ext
        funext j
        fin_cases j
        · exact unitInterval.symm_symm _
        · exact hi.symm
  change p ∈ Set.range perimeter
  rw [perimeter, Path.trans_range, Path.trans_range, Path.trans_range]
  simpa only [Set.mem_union, or_assoc] using hp

end NoExoticSixSphere.JamesSphere.AttachingSquare
