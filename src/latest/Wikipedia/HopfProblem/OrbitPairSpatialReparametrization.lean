import Wikipedia.HopfProblem.OrbitPairOrdinaryCollisionEvents

/-!
# Exact collision transport under time-dependent spatial reparametrization

Slice equivalences relabel source points without changing time or target
values. Ordered and unordered collisions and collision source points are
transported by explicit equivalences. Triple exclusion and the entire
collision-event set are retained.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

open FamilyDoublePoints

variable {M N : Type*}

def sourceEquiv (e : ℝ → M ≃ M) : (ℝ × M) ≃ (ℝ × M) := Equiv.prodCongrRight e

def pairEquiv (e : ℝ → M ≃ M) : (ℝ × (M × M)) ≃ (ℝ × (M × M)) :=
  Equiv.prodCongrRight (fun t => (e t).prodCongr (e t))

def changedFamily (F : ℝ × M → N) (e : ℝ → M ≃ M) : ℝ × M → N := F ∘ sourceEquiv e

theorem mem_doublePoints_iff (F : ℝ × M → N) (e : ℝ → M ≃ M) (p : ℝ × (M × M)) :
    p ∈ doublePoints (changedFamily F e) ↔ pairEquiv e p ∈ doublePoints F := by
  change (p.2.1 ≠ p.2.2 ∧ F (p.1, e p.1 p.2.1) = F (p.1, e p.1 p.2.2)) ↔
    (e p.1 p.2.1 ≠ e p.1 p.2.2 ∧ F (p.1, e p.1 p.2.1) = F (p.1, e p.1 p.2.2))
  constructor
  · intro h
    exact ⟨(e p.1).injective.ne h.1, h.2⟩
  · intro h
    exact ⟨fun heq => h.1 (congrArg (e p.1) heq), h.2⟩

theorem finite_doublePoints {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hF : (doublePoints F).Finite) : (doublePoints (changedFamily F e)).Finite := by
  have heq : doublePoints (changedFamily F e) = pairEquiv e ⁻¹' doublePoints F :=
    Set.ext (mem_doublePoints_iff F e)
  rw [heq]
  exact hF.preimage (pairEquiv e).injective.injOn

def sym2Equiv (e : M ≃ M) : Sym2 M ≃ Sym2 M where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by intro z; induction z using Sym2.ind; simp
  right_inv := by intro z; induction z using Sym2.ind; simp

def unorderedEquiv (e : ℝ → M ≃ M) : (ℝ × Sym2 M) ≃ (ℝ × Sym2 M) :=
  Equiv.prodCongrRight (fun t => sym2Equiv (e t))

theorem mem_unordered_iff (F : ℝ × M → N) (e : ℝ → M ≃ M) (p : ℝ × Sym2 M) :
    p ∈ unorderedDoublePoints (changedFamily F e) ↔
      unorderedEquiv e p ∈ unorderedDoublePoints F := by
  rcases p with ⟨t, z⟩
  induction z using Sym2.ind with
  | _ x y =>
    exact (FamilyDoublePoints.mem_unordered_iff (changedFamily F e) t x y).trans
      ((mem_doublePoints_iff F e (t, (x, y))).trans
        (FamilyDoublePoints.mem_unordered_iff F t (e t x) (e t y)).symm)

def collisionEquiv (F : ℝ × M → N) (e : ℝ → M ≃ M) :
    unorderedDoublePoints (changedFamily F e) ≃ unorderedDoublePoints F :=
  (unorderedEquiv e).subtypeEquiv (mem_unordered_iff F e)

theorem unordered_times_injective {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hsep : InjOn Prod.fst (unorderedDoublePoints F)) :
    InjOn Prod.fst (unorderedDoublePoints (changedFamily F e)) := by
  intro p hp q hq heq
  apply (unorderedEquiv e).injective
  exact hsep ((mem_unordered_iff F e p).mp hp) ((mem_unordered_iff F e q).mp hq) heq

theorem triplePoints_eq_empty {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hno : triplePoints F = ∅) : triplePoints (changedFamily F e) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨t, x, y, z⟩ h
  have htr : (t, (e t x, (e t y, e t z))) ∈ triplePoints F :=
    ⟨(e t).injective.ne h.1, (e t).injective.ne h.2.1,
      (e t).injective.ne h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  rw [hno] at htr
  exact htr

theorem collisionEvents_eq (F : ℝ × M → N) (e : ℝ → M ≃ M) :
    collisionEvents (changedFamily F e) = collisionEvents F := by
  apply subset_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨pairEquiv e p, (mem_doublePoints_iff F e p).mp hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(pairEquiv e).symm p, ?_, ?_⟩
    · apply (mem_doublePoints_iff F e _).mpr
      simpa only [Equiv.apply_symm_apply] using hp
    · rcases p with ⟨t, x, y⟩
      change (t, F (t, e t ((e t).symm x))) = (t, F (t, x))
      rw [Equiv.apply_symm_apply]

theorem mem_collisionSources_iff (F : ℝ × M → N) (e : ℝ → M ≃ M) (p : ℝ × M) :
    p ∈ collisionSources (changedFamily F e) ↔ sourceEquiv e p ∈ collisionSources F := by
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · subst p
      exact first_mem_collisionSources ((mem_doublePoints_iff F e q).mp hq)
    · subst p
      exact second_mem_collisionSources ((mem_doublePoints_iff F e q).mp hq)
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · refine Or.inl ⟨(pairEquiv e).symm q, ?_, ?_⟩
      · apply (mem_doublePoints_iff F e _).mpr
        simpa only [Equiv.apply_symm_apply] using hq
      · apply (sourceEquiv e).injective
        calc
          sourceEquiv e (SynchronizedPairs.first ((pairEquiv e).symm q)) =
              SynchronizedPairs.first (pairEquiv e ((pairEquiv e).symm q)) := rfl
          _ = sourceEquiv e p := by rw [Equiv.apply_symm_apply]; exact heq
    · refine Or.inr ⟨(pairEquiv e).symm q, ?_, ?_⟩
      · apply (mem_doublePoints_iff F e _).mpr
        simpa only [Equiv.apply_symm_apply] using hq
      · apply (sourceEquiv e).injective
        calc
          sourceEquiv e (SynchronizedPairs.second ((pairEquiv e).symm q)) =
              SynchronizedPairs.second (pairEquiv e ((pairEquiv e).symm q)) := rfl
          _ = sourceEquiv e p := by rw [Equiv.apply_symm_apply]; exact heq

theorem collisionSources_eq_image (F : ℝ × M → N) (e : ℝ → M ≃ M) :
    collisionSources (changedFamily F e) = (sourceEquiv e).symm '' collisionSources F := by
  ext p
  rw [mem_collisionSources_iff]
  constructor
  · intro hp
    exact ⟨sourceEquiv e p, hp, (sourceEquiv e).symm_apply_apply p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Equiv.apply_symm_apply] using hq

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization
