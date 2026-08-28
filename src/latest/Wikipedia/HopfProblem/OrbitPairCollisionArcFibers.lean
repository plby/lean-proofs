import Wikipedia.HopfProblem.OrbitPairCollisionSpatialLabels

/-!
# Exact fibers along source arcs joining two collisions

Away from the spatial coordinates of collision sources, a fixed-time
slice has a singleton fiber. Along an arc avoiding those coordinates in
its interior, the only possible extra fiber points are the opposite
branches at its two collision endpoints. Disjoint source arcs therefore
project to embedded arcs meeting exactly at the corresponding endpoints.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open FamilyDoublePoints SynchronizedPairs

variable {M N : Type*} {F : ℝ × M → N}

theorem slice_fiber_eq_of_not_spatial_collision_source {t : ℝ} {x z : M}
    (hx : x ∉ Prod.snd '' collisionSources F) (hvalue : F (t, z) = F (t, x)) : z = x := by
  by_contra hne
  have hp : (t, (x, z)) ∈ doublePoints F := ⟨Ne.symm hne, hvalue.symm⟩
  exact hx ⟨(t, x), first_mem_collisionSources hp, rfl⟩

theorem collision_arc_slice_fiber_formula {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (hp₀ : (t, (x₀, y₀)) ∈ doublePoints F)
    (hp₁ : (t, (x₁, y₁)) ∈ doublePoints F)
    (hglobal₀ : HasGlobalProjectedCollisionFiber F (t, (x₀, y₀)))
    (hglobal₁ : HasGlobalProjectedCollisionFiber F (t, (x₁, y₁)))
    {f : ℝ → M} (hf0 : f 0 = x₀) (hf1 : f 1 = x₁)
    (havoid : ∀ s ∈ Ioo (0 : ℝ) 1, f s ∉ Prod.snd '' collisionSources F) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : M,
      F (t, z) = F (t, f s) ↔
        z = f s ∨ (s = 0 ∧ z = y₀) ∨ (s = 1 ∧ z = y₁) := by
  intro s hs z
  constructor
  · intro hvalue
    by_cases hs0 : s = 0
    · have hv : F (t, z) = F (first (t, (x₀, y₀))) := by
        simpa only [first, hs0, hf0] using hvalue
      rcases (hglobal₀ (t, z)).mp hv with hz | hz
      · left
        rw [hs0, hf0]
        exact congrArg (fun q : ℝ × M => q.2) hz
      · exact Or.inr (Or.inl ⟨hs0, congrArg (fun q : ℝ × M => q.2) hz⟩)
    by_cases hs1 : s = 1
    · have hv : F (t, z) = F (first (t, (x₁, y₁))) := by
        simpa only [first, hs1, hf1] using hvalue
      rcases (hglobal₁ (t, z)).mp hv with hz | hz
      · left
        rw [hs1, hf1]
        exact congrArg (fun q : ℝ × M => q.2) hz
      · exact Or.inr (Or.inr ⟨hs1, congrArg (fun q : ℝ × M => q.2) hz⟩)
    have hsi : s ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
    exact Or.inl (slice_fiber_eq_of_not_spatial_collision_source (havoid s hsi) hvalue)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simpa only [hf0] using hp₀.2.symm
    · simpa only [hf1] using hp₁.2.symm

theorem collision_arc_projection_injective {t : ℝ} {f g : ℝ → M} {y₀ y₁ : M}
    (hfi : Injective (fun s : unitInterval => f s))
    (hdisj : Disjoint (range (fun s : unitInterval => f s))
      (range (fun s : unitInterval => g s)))
    (hg0 : g 0 = y₀) (hg1 : g 1 = y₁)
    (hfiber : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : M,
      F (t, z) = F (t, f s) ↔
        z = f s ∨ (s = 0 ∧ z = y₀) ∨ (s = 1 ∧ z = y₁)) :
    Injective (fun s : unitInterval => F (t, f s)) := by
  intro s u heq
  rcases (hfiber s s.property (f u)).mp heq.symm with hsame | ⟨-, hzero⟩ | ⟨-, hone⟩
  · exact (hfi hsame).symm
  · exact False.elim (disjoint_left.mp hdisj ⟨u, rfl⟩ ⟨0, hg0.trans hzero.symm⟩)
  · exact False.elim (disjoint_left.mp hdisj ⟨u, rfl⟩ ⟨1, hg1.trans hone.symm⟩)

theorem collision_arc_crossing_parameters {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (hp₀ : (t, (x₀, y₀)) ∈ doublePoints F)
    (hp₁ : (t, (x₁, y₁)) ∈ doublePoints F)
    {f g : ℝ → M} (hf0 : f 0 = x₀) (hf1 : f 1 = x₁)
    (hg0 : g 0 = y₀) (hg1 : g 1 = y₁)
    (hgi : Injective (fun s : unitInterval => g s))
    (hdisj : Disjoint (range (fun s : unitInterval => f s))
      (range (fun s : unitInterval => g s)))
    (hfiber : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : M,
      F (t, z) = F (t, f s) ↔
        z = f s ∨ (s = 0 ∧ z = y₀) ∨ (s = 1 ∧ z = y₁)) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      F (t, f s) = F (t, g u) ↔ (s = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 1) := by
  intro s hs u hu
  constructor
  · intro heq
    rcases (hfiber s hs (g u)).mp heq.symm with hsame | ⟨hs0, hzero⟩ | ⟨hs1, hone⟩
    · exact False.elim (disjoint_left.mp hdisj ⟨⟨s, hs⟩, rfl⟩ ⟨⟨u, hu⟩, hsame⟩)
    · have hu0 : (⟨u, hu⟩ : unitInterval) = 0 := hgi (hzero.trans hg0.symm)
      exact Or.inl ⟨hs0, congrArg (fun q : unitInterval => q.val) hu0⟩
    · have hu1 : (⟨u, hu⟩ : unitInterval) = 1 := hgi (hone.trans hg1.symm)
      exact Or.inr ⟨hs1, congrArg (fun q : unitInterval => q.val) hu1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simpa only [hf0, hg0] using hp₀.2
    · simpa only [hf1, hg1] using hp₁.2

theorem collision_pair_source_endpoints_distinct {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (hp₀ : (t, (x₀, y₀)) ∈ doublePoints F)
    (hp₁ : (t, (x₁, y₁)) ∈ doublePoints F)
    (hvalue : F (t, x₀) ≠ F (t, x₁)) :
    x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧ Disjoint ({x₀, x₁} : Set M) {y₀, y₁} := by
  refine ⟨(fun heq => hvalue (congrArg (fun x => F (t, x)) heq)), ?_, ?_⟩
  · intro heq
    exact hvalue (hp₀.2.trans ((congrArg (fun x => F (t, x)) heq).trans hp₁.2.symm))
  · apply disjoint_left.mpr
    intro z hz hw
    simp only [mem_insert_iff, mem_singleton_iff] at hz hw
    rcases hz with hx₀ | hx₁
    · rcases hw with hy₀ | hy₁
      · exact hp₀.1 (hx₀.symm.trans hy₀)
      · exact hvalue ((congrArg (fun x => F (t, x)) (hx₀.symm.trans hy₁)).trans hp₁.2.symm)
    · rcases hw with hy₀ | hy₁
      · exact hvalue (hp₀.2.trans (congrArg (fun x => F (t, x)) (hy₀.symm.trans hx₁)))
      · exact hp₁.1 (hx₁.symm.trans hy₁)

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
