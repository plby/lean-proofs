import Wikipedia.HopfProblem.OrbitPairRetimingCollisionCriterion
import Wikipedia.HopfProblem.OrbitPairUnorderedCollisions

/-!
# Exact collision equivalences for a separated common-plateau time change

The collision transport changes time by the common scalar equivalence
exactly when both source points lie in the plateau. This rule respects
interchange of the two points and therefore also gives an equivalence of
unordered collisions, retaining their cardinality and finite pairing.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.TimeRetiming

variable {A M N : Type*}

def conditionalTimeEquiv (ρ : ℝ ≃ ℝ) (S : Set A) : (ℝ × A) ≃ (ℝ × A) := by
  classical
  exact
    { toFun := fun p => if p.2 ∈ S then (ρ p.1, p.2) else p
      invFun := fun p => if p.2 ∈ S then (ρ.symm p.1, p.2) else p
      left_inv := by intro p; by_cases hp : p.2 ∈ S <;> simp [hp]
      right_inv := by intro p; by_cases hp : p.2 ∈ S <;> simp [hp] }

theorem conditionalTimeEquiv_of_mem (ρ : ℝ ≃ ℝ) (S : Set A) {p : ℝ × A} (hp : p.2 ∈ S) :
    conditionalTimeEquiv ρ S p = (ρ p.1, p.2) := by
  classical
  simp only [conditionalTimeEquiv, Equiv.coe_fn_mk, if_pos hp]

theorem conditionalTimeEquiv_of_notMem (ρ : ℝ ≃ ℝ) (S : Set A) {p : ℝ × A} (hp : p.2 ∉ S) :
    conditionalTimeEquiv ρ S p = p := by
  classical
  simp only [conditionalTimeEquiv, Equiv.coe_fn_mk, if_neg hp]

theorem clock_doublePoints_iff_conditional_time
    {F : ℝ × M → N} {τ : ℝ × M → ℝ} (ρ : ℝ ≃ ℝ)
    {T : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F T U P)
    (hrange : ∀ t ∈ T, ∀ x, τ (t, x) ∈ T)
    (hfixed : ∀ t x, t ∉ T ∨ x ∉ U → τ (t, x) = t)
    (hplateau : ∀ t x, x ∈ P → τ (t, x) = ρ t) (p : ℝ × (M × M)) :
    p ∈ FamilyDoublePoints.doublePoints (clockFamily F τ) ↔
      conditionalTimeEquiv ρ (P ×ˢ P) p ∈ FamilyDoublePoints.doublePoints F := by
  classical
  by_cases hp : p.2 ∈ P ×ˢ P
  · rw [conditionalTimeEquiv_of_mem ρ (P ×ˢ P) hp]
    change (p.2.1 ≠ p.2.2 ∧ F (τ (p.1, p.2.1), p.2.1) =
        F (τ (p.1, p.2.2), p.2.2)) ↔
      (p.2.1 ≠ p.2.2 ∧ F (ρ p.1, p.2.1) = F (ρ p.1, p.2.2))
    rw [hplateau _ _ hp.1, hplateau _ _ hp.2]
  · rw [conditionalTimeEquiv_of_notMem ρ (P ×ˢ P) hp]
    rw [clock_doublePoints_iff hPU hsep hrange hfixed hplateau]
    constructor
    · rintro (h | h)
      · exact h.2
      · exact False.elim (hp ⟨h.1, h.2.1⟩)
    · intro hold
      left
      refine ⟨?_, hold⟩
      by_cases ht : p.1 ∈ T
      · right
        constructor
        · intro hx
          exact hp (collision_in_plateau (τ := Prod.fst) hPU hsep
            (fun _ ht _ => ht) ht hx hold.1 hold.2)
        · intro hy
          have hh := collision_in_plateau (τ := Prod.fst) hPU hsep
            (fun _ ht _ => ht) ht hy hold.1.symm hold.2.symm
          exact hp ⟨hh.2, hh.1⟩
      · exact Or.inl ht

def unorderedPlateau (P : Set M) : Set (Sym2 M) := {s | ∀ x ∈ s, x ∈ P}

theorem conditionalTimeEquiv_unorderedProjection (ρ : ℝ ≃ ℝ) (P : Set M)
    (p : ℝ × (M × M)) :
    FamilyDoublePoints.unorderedProjection (conditionalTimeEquiv ρ (P ×ˢ P) p) =
      conditionalTimeEquiv ρ (unorderedPlateau P) (FamilyDoublePoints.unorderedProjection p) := by
  classical
  have hiff : (FamilyDoublePoints.unorderedProjection p).2 ∈ unorderedPlateau P ↔
      p.2 ∈ P ×ˢ P := Sym2.forall_mem_pair
  by_cases hp : p.2 ∈ P ×ˢ P
  · rw [conditionalTimeEquiv_of_mem ρ (P ×ˢ P) hp,
      conditionalTimeEquiv_of_mem ρ (unorderedPlateau P) (hiff.mpr hp)]
    rfl
  · rw [conditionalTimeEquiv_of_notMem ρ (P ×ˢ P) hp,
      conditionalTimeEquiv_of_notMem ρ (unorderedPlateau P) (fun h => hp (hiff.mp h))]

theorem clock_unordered_iff_conditional_time
    {F : ℝ × M → N} {τ : ℝ × M → ℝ} (ρ : ℝ ≃ ℝ)
    {T : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F T U P)
    (hrange : ∀ t ∈ T, ∀ x, τ (t, x) ∈ T)
    (hfixed : ∀ t x, t ∉ T ∨ x ∉ U → τ (t, x) = t)
    (hplateau : ∀ t x, x ∈ P → τ (t, x) = ρ t) (p : ℝ × Sym2 M) :
    p ∈ FamilyDoublePoints.unorderedDoublePoints (clockFamily F τ) ↔
      conditionalTimeEquiv ρ (unorderedPlateau P) p ∈ FamilyDoublePoints.unorderedDoublePoints F := by
  rcases p with ⟨t, z⟩
  induction z using Sym2.ind with
  | _ x y =>
    let q : ℝ × (M × M) := (t, (x, y))
    let r := conditionalTimeEquiv ρ (P ×ˢ P) q
    have he := conditionalTimeEquiv_unorderedProjection ρ P q
    change FamilyDoublePoints.unorderedProjection q ∈
        FamilyDoublePoints.unorderedDoublePoints (clockFamily F τ) ↔
      conditionalTimeEquiv ρ (unorderedPlateau P) (FamilyDoublePoints.unorderedProjection q) ∈
        FamilyDoublePoints.unorderedDoublePoints F
    rw [← he]
    exact (FamilyDoublePoints.mem_unordered_iff (clockFamily F τ) t x y).trans
      ((clock_doublePoints_iff_conditional_time ρ hPU hsep hrange hfixed hplateau q).trans
        (FamilyDoublePoints.mem_unordered_iff F r.1 r.2.1 r.2.2).symm)

def clockUnorderedEquiv
    {F : ℝ × M → N} {τ : ℝ × M → ℝ} (ρ : ℝ ≃ ℝ)
    {T : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F T U P)
    (hrange : ∀ t ∈ T, ∀ x, τ (t, x) ∈ T)
    (hfixed : ∀ t x, t ∉ T ∨ x ∉ U → τ (t, x) = t)
    (hplateau : ∀ t x, x ∈ P → τ (t, x) = ρ t) :
    FamilyDoublePoints.unorderedDoublePoints (clockFamily F τ) ≃
      FamilyDoublePoints.unorderedDoublePoints F :=
  (conditionalTimeEquiv ρ (unorderedPlateau P)).subtypeEquiv
    (clock_unordered_iff_conditional_time ρ hPU hsep hrange hfixed hplateau)

end Wikipedia.HopfProblem.OrbitPair.TimeRetiming
