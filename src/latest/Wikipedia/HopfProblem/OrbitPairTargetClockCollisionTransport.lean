import Wikipedia.HopfProblem.OrbitPairFiniteProjectedCollisionFibers

/-!
# Exact collision transport for clocks depending on the projected target

When the new time is `t + beta(F(t,x))`, equal projected values receive
the same time shift. Thus two equal projected values have equal new times
exactly when their old times agree. Once the time-fibre maps are
equivalences, no projected-separation or spatial plateau hypothesis is
needed to transport the synchronized collision set exactly.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open FamilyDoublePoints SynchronizedPairs NativeFamily

variable {M N : Type*}

def sourceEquiv (e : M → ℝ ≃ ℝ) : (ℝ × M) ≃ (ℝ × M) where
  toFun q := (e q.2 q.1, q.2)
  invFun q := ((e q.2).symm q.1, q.2)
  left_inv q := Prod.ext ((e q.2).symm_apply_apply q.1) rfl
  right_inv q := Prod.ext ((e q.2).apply_symm_apply q.1) rfl

def pairEquiv (e : M → ℝ ≃ ℝ) : (ℝ × (M × M)) ≃ (ℝ × (M × M)) where
  toFun p := (e p.2.1 p.1, p.2)
  invFun p := ((e p.2.1).symm p.1, p.2)
  left_inv p := Prod.ext ((e p.2.1).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((e p.2.1).apply_symm_apply p.1) rfl

def family (F : ℝ × M → N) (e : M → ℝ ≃ ℝ) : ℝ × M → N :=
  F ∘ (sourceEquiv e).symm

theorem family_sourceEquiv (F : ℝ × M → N) (e : M → ℝ ≃ ℝ) (q : ℝ × M) :
    family F e (sourceEquiv e q) = F q := by
  change F ((sourceEquiv e).symm (sourceEquiv e q)) = F q
  rw [Equiv.symm_apply_apply]

variable {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}

theorem inverse_clock_identity
    (hclock : ∀ t x, e x t = t + β (F (t, x))) (q : ℝ × M) :
    (e q.2).symm q.1 + β (family F e q) = q.1 := by
  calc
    (e q.2).symm q.1 + β (family F e q) = e q.2 ((e q.2).symm q.1) :=
      (hclock ((e q.2).symm q.1) q.2).symm
    _ = q.1 := (e q.2).apply_symm_apply q.1

theorem old_times_eq_of_coincidence
    (hclock : ∀ t x, e x t = t + β (F (t, x))) {t : ℝ} {x y : M}
    (heq : family F e (t, x) = family F e (t, y)) :
    (e x).symm t = (e y).symm t := by
  have hx := inverse_clock_identity hclock (t, x)
  have hy := inverse_clock_identity hclock (t, y)
  change (e x).symm t + β (family F e (t, x)) = t at hx
  change (e y).symm t + β (family F e (t, y)) = t at hy
  rw [heq] at hx
  exact add_right_cancel (hx.trans hy.symm)

theorem mem_doublePoints_iff
    (hclock : ∀ t x, e x t = t + β (F (t, x))) (p : ℝ × (M × M)) :
    p ∈ doublePoints (family F e) ↔ (pairEquiv e).symm p ∈ doublePoints F := by
  rcases p with ⟨t, x, y⟩
  change (x ≠ y ∧ F ((e x).symm t, x) = F ((e y).symm t, y)) ↔
    (x ≠ y ∧ F ((e x).symm t, x) = F ((e x).symm t, y))
  constructor
  · rintro ⟨hne, heq⟩
    have ht := old_times_eq_of_coincidence hclock heq
    exact ⟨hne, by rwa [← ht] at heq⟩
  · rintro ⟨hne, heq⟩
    have hty : e y ((e x).symm t) = t := by
      rw [hclock, ← heq]
      exact inverse_clock_identity hclock (t, x)
    have hiy : (e y).symm t = (e x).symm t :=
      (e y).injective (((e y).apply_symm_apply t).trans hty.symm)
    exact ⟨hne, by rwa [hiy]⟩

theorem doublePoints_eq_image
    (hclock : ∀ t x, e x t = t + β (F (t, x))) :
    doublePoints (family F e) = pairEquiv e '' doublePoints F := by
  ext p
  rw [mem_doublePoints_iff hclock]
  constructor
  · intro hp
    exact ⟨(pairEquiv e).symm p, hp, (pairEquiv e).apply_symm_apply p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Equiv.symm_apply_apply] using hq

theorem finite_doublePoints
    (hclock : ∀ t x, e x t = t + β (F (t, x)))
    (hfinite : (doublePoints F).Finite) : (doublePoints (family F e)).Finite := by
  rw [doublePoints_eq_image hclock]
  exact hfinite.image (pairEquiv e)

def collisionEquiv (hclock : ∀ t x, e x t = t + β (F (t, x))) :
    doublePoints (family F e) ≃ doublePoints F :=
  (pairEquiv e).symm.subtypeEquiv (mem_doublePoints_iff hclock)

theorem sourceEquiv_first (p : ℝ × (M × M)) :
    sourceEquiv e (first p) = first (pairEquiv e p) := rfl

theorem sourceEquiv_second_of_collision
    (hclock : ∀ t x, e x t = t + β (F (t, x))) {p : ℝ × (M × M)}
    (hp : p ∈ doublePoints F) : sourceEquiv e (second p) = second (pairEquiv e p) := by
  apply Prod.ext
  · change e p.2.2 p.1 = e p.2.1 p.1
    rw [hclock, hclock, hp.2]
  · rfl

theorem triplePoints_eq_empty
    (hclock : ∀ t x, e x t = t + β (F (t, x))) (hno : triplePoints F = ∅) :
    triplePoints (family F e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨t, x, y, z⟩ h
  have hxy := old_times_eq_of_coincidence hclock h.2.2.2.1
  have hxz := old_times_eq_of_coincidence hclock h.2.2.2.2
  have htr : ((e x).symm t, (x, (y, z))) ∈ triplePoints F := by
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · have hh := h.2.2.2.1
      change F ((e x).symm t, x) = F ((e y).symm t, y) at hh
      rwa [← hxy] at hh
    · have hh := h.2.2.2.2
      change F ((e x).symm t, x) = F ((e z).symm t, z) at hh
      rwa [← hxz] at hh
  rw [hno] at htr
  exact htr

theorem collisionSources_eq_image
    (hclock : ∀ t x, e x t = t + β (F (t, x))) :
    collisionSources (family F e) = sourceEquiv e '' collisionSources F := by
  apply subset_antisymm
  · rintro q (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [doublePoints_eq_image hclock] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact ⟨first r, first_mem_collisionSources hr, sourceEquiv_first r⟩
    · rw [doublePoints_eq_image hclock] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact ⟨second r, second_mem_collisionSources hr,
        sourceEquiv_second_of_collision hclock hr⟩
  · rintro q ⟨z, hz, rfl⟩
    rcases hz with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · have hp' : pairEquiv e p ∈ doublePoints (family F e) := by
        rw [doublePoints_eq_image hclock]
        exact ⟨p, hp, rfl⟩
      rw [sourceEquiv_first]
      exact first_mem_collisionSources hp'
    · have hp' : pairEquiv e p ∈ doublePoints (family F e) := by
        rw [doublePoints_eq_image hclock]
        exact ⟨p, hp, rfl⟩
      rw [sourceEquiv_second_of_collision hclock hp]
      exact second_mem_collisionSources hp'

theorem family_fixed_of_clock_zero
    (hclock : ∀ t x, e x t = t + β (F (t, x))) {q : ℝ × M} (hq : β (F q) = 0) :
    family F e q = F q := by
  have heq : sourceEquiv e q = q := by
    apply Prod.ext
    · change e q.2 q.1 = q.1
      rw [hclock, hq, add_zero]
    · rfl
  have hh := family_sourceEquiv F e q
  rw [heq] at hh
  exact hh

theorem global_projected_collision_fibers
    (hclock : ∀ t x, e x t = t + β (F (t, x)))
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p) :
    ∀ p ∈ doublePoints (family F e), HasGlobalProjectedCollisionFiber (family F e) p := by
  intro p hp q
  let r := (pairEquiv e).symm p
  have hr : r ∈ doublePoints F := (mem_doublePoints_iff hclock p).mp hp
  have hfirst : sourceEquiv e (first r) = first p := by
    rw [sourceEquiv_first]
    exact congrArg first ((pairEquiv e).apply_symm_apply p)
  have hsecond : sourceEquiv e (second r) = second p := by
    rw [sourceEquiv_second_of_collision hclock hr]
    exact congrArg second ((pairEquiv e).apply_symm_apply p)
  constructor
  · intro heq
    have hold : F ((sourceEquiv e).symm q) = F (first r) := heq
    rcases (hglobal r hr ((sourceEquiv e).symm q)).mp hold with h | h
    · exact Or.inl (((sourceEquiv e).apply_symm_apply q).symm.trans
        ((congrArg (sourceEquiv e) h).trans hfirst))
    · exact Or.inr (((sourceEquiv e).apply_symm_apply q).symm.trans
        ((congrArg (sourceEquiv e) h).trans hsecond))
  · rintro (rfl | rfl)
    · rfl
    · exact hp.2.symm

end Wikipedia.HopfProblem.OrbitPair.TargetClock
