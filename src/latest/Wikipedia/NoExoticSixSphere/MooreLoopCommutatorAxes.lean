import Wikipedia.NoExoticSixSphere.MooreLoopCancellation

/-!
# A based contraction of the actual loop commutator on its two axes

The Moore commutator is not literally constant on the axes. There it
equals the product of the two self-retracing loops. The simultaneous
explicit cancellation of these loops gives a continuous contraction on
the whole axes union and fixes its common identity point. This provides
the boundary homotopy needed for a subsequent smash-product descent.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

def commutatorMap : C(Loop y₀ × Loop y₀, Loop y₀) :=
  ⟨fun p ↦ p.1 * p.2 * reverse p.1 * reverse p.2,
    ((continuous_fst.mul continuous_snd).mul
      (continuous_reverse.comp continuous_fst)).mul (continuous_reverse.comp continuous_snd)⟩

theorem commutator_one_left (p : Loop y₀) : commutatorMap (1, p) = p * reverse p := by
  change (1 : Loop y₀) * p * reverse 1 * reverse p = p * reverse p
  rw [one_mul, reverse_one, mul_one]

theorem commutator_one_right (p : Loop y₀) : commutatorMap (p, 1) = p * reverse p := by
  change p * (1 : Loop y₀) * reverse p * reverse 1 = p * reverse p
  rw [mul_one, reverse_one, mul_one]

abbrev Axes (y₀ : Y) := {p : Loop y₀ × Loop y₀ // p.1 = 1 ∨ p.2 = 1}

def axesPoint : Axes y₀ := ⟨(1, 1), Or.inl rfl⟩

def axesMap : C(Axes y₀, Loop y₀) :=
  commutatorMap.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem axesMap_factor (p : Axes y₀) : axesMap p =
    (p.val.1 * reverse p.val.1) * (p.val.2 * reverse p.val.2) := by
  change p.val.1 * p.val.2 * reverse p.val.1 * reverse p.val.2 = _
  rcases p.property with h | h <;> simp only [h, reverse_one, one_mul, mul_one]

theorem axesMap_point : axesMap (axesPoint (y₀ := y₀)) = 1 := by
  change commutatorMap ((1 : Loop y₀), 1) = 1
  rw [commutator_one_left, reverse_one, mul_one]

def axesNullhomotopy : (axesMap (y₀ := y₀)).HomotopyRel
    (ContinuousMap.const _ 1) {axesPoint} where
  toFun u := retrace (u.1, u.2.val.1) * retrace (u.1, u.2.val.2)
  continuous_toFun := by
    have hl : Continuous (fun u : I × Axes y₀ ↦ retrace (u.1, u.2.val.1)) :=
      continuous_retrace.comp
      (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
    have hr : Continuous (fun u : I × Axes y₀ ↦ retrace (u.1, u.2.val.2)) :=
      continuous_retrace.comp
      (continuous_fst.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
    exact hl.mul hr
  map_zero_left p := by
    change retrace (0, p.val.1) * retrace (0, p.val.2) = axesMap p
    rw [retrace_zero, retrace_zero]
    exact (axesMap_factor p).symm
  map_one_left p := by
    change retrace (1, p.val.1) * retrace (1, p.val.2) = 1
    rw [retrace_one, retrace_one, mul_one]
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change retrace (s, (1 : Loop y₀)) * retrace (s, 1) = axesMap axesPoint
    rw [retrace_identity, mul_one, axesMap_point]

end NoExoticSixSphere.Moore.Loop
