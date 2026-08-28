import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# A geometric collision-control criterion for nonuniform time changes

Separation is imposed on projected old-time images, allowing the two old
times to differ. This is stronger than ordinary synchronized injectivity
and addresses precisely the new coincidences that a time change can create.
Under this independent geometric condition, every moved collision lies in
the common time-profile plateau; all other collisions are unchanged.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.TimeRetiming

variable {M N : Type*}

def clockFamily (F : ℝ × M → N) (τ : ℝ × M → ℝ) (p : ℝ × M) : N := F (τ p, p.2)

def timePairMap (ρ : ℝ → ℝ) (p : ℝ × (M × M)) : ℝ × (M × M) := (ρ p.1, p.2)

def HasProjectedSeparation (F : ℝ × M → N) (J : Set ℝ) (U P : Set M) : Prop :=
  ∀ s ∈ J, ∀ t ∈ J, ∀ x ∈ U, ∀ y ∉ P, F (s, x) = F (t, y) → x = y

theorem collision_in_plateau {F : ℝ × M → N} {τ : ℝ × M → ℝ}
    {J : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F J U P)
    (hrange : ∀ t ∈ J, ∀ x, τ (t, x) ∈ J)
    {t : ℝ} (ht : t ∈ J) {x y : M} (hx : x ∈ U) (hne : x ≠ y)
    (heq : clockFamily F τ (t, x) = clockFamily F τ (t, y)) : x ∈ P ∧ y ∈ P := by
  have hyP : y ∈ P := by
    by_contra hy
    exact hne (hsep _ (hrange t ht x) _ (hrange t ht y) x hx y hy heq)
  have hxP : x ∈ P := by
    by_contra hxP
    exact hne (hsep _ (hrange t ht y) _ (hrange t ht x) y (hPU hyP) x hxP heq.symm).symm
  exact ⟨hxP, hyP⟩

theorem clock_eq_original {F : ℝ × M → N} {τ : ℝ × M → ℝ} {p : ℝ × M}
    (hτ : τ p = p.1) : clockFamily F τ p = F p := by
  rw [clockFamily, hτ]

theorem clock_doublePoints_iff {F : ℝ × M → N} {τ : ℝ × M → ℝ} {ρ : ℝ → ℝ}
    {J : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F J U P)
    (hrange : ∀ t ∈ J, ∀ x, τ (t, x) ∈ J)
    (hfixed : ∀ t x, t ∉ J ∨ x ∉ U → τ (t, x) = t)
    (hplateau : ∀ t x, x ∈ P → τ (t, x) = ρ t) (p : ℝ × (M × M)) :
    p ∈ FamilyDoublePoints.doublePoints (clockFamily F τ) ↔
      ((p.1 ∉ J ∨ (p.2.1 ∉ U ∧ p.2.2 ∉ U)) ∧ p ∈ FamilyDoublePoints.doublePoints F) ∨
      (p.2.1 ∈ P ∧ p.2.2 ∈ P ∧ timePairMap ρ p ∈ FamilyDoublePoints.doublePoints F) := by
  rcases p with ⟨t, x, y⟩
  constructor
  · rintro ⟨hne, heq⟩
    have hP (hx : x ∈ P) (hy : y ∈ P) :
        timePairMap ρ (t, (x, y)) ∈ FamilyDoublePoints.doublePoints F := by
      refine ⟨hne, ?_⟩
      change F (τ (t, x), x) = F (τ (t, y), y) at heq
      rw [hplateau t x hx, hplateau t y hy] at heq
      exact heq
    by_cases ht : t ∈ J
    · by_cases hx : x ∈ U
      · obtain ⟨hxP, hyP⟩ := collision_in_plateau hPU hsep hrange ht hx hne heq
        exact Or.inr ⟨hxP, hyP, hP hxP hyP⟩
      · by_cases hy : y ∈ U
        · obtain ⟨hyP, hxP⟩ := collision_in_plateau hPU hsep hrange ht hy hne.symm heq.symm
          exact Or.inr ⟨hxP, hyP, hP hxP hyP⟩
        · refine Or.inl ⟨Or.inr ⟨hx, hy⟩, hne, ?_⟩
          exact (clock_eq_original (hfixed t x (Or.inr hx))).symm.trans
            (heq.trans (clock_eq_original (hfixed t y (Or.inr hy))))
    · refine Or.inl ⟨Or.inl ht, hne, ?_⟩
      exact (clock_eq_original (hfixed t x (Or.inl ht))).symm.trans
        (heq.trans (clock_eq_original (hfixed t y (Or.inl ht))))
  · rintro (⟨hfix, hne, heq⟩ | ⟨hxP, hyP, hne, heq⟩)
    · have hx : τ (t, x) = t := hfixed t x (hfix.imp_right And.left)
      have hy : τ (t, y) = t := hfixed t y (hfix.imp_right And.right)
      exact ⟨hne, (clock_eq_original hx).trans (heq.trans (clock_eq_original hy).symm)⟩
    · refine ⟨hne, ?_⟩
      change F (τ (t, x), x) = F (τ (t, y), y)
      rw [hplateau t x hxP, hplateau t y hyP]
      exact heq

theorem timePairMap_injective {ρ : ℝ → ℝ} (hρ : Injective ρ) :
    Injective (timePairMap (M := M) ρ) := by
  intro p q heq
  have ht := congrArg (fun r : ℝ × (M × M) => r.1) heq
  have hs := congrArg (fun r : ℝ × (M × M) => r.2) heq
  exact Prod.ext (hρ ht) hs

theorem finite_clock_doublePoints {F : ℝ × M → N} {τ : ℝ × M → ℝ} {ρ : ℝ → ℝ}
    {J : Set ℝ} {U P : Set M} (hPU : P ⊆ U)
    (hsep : HasProjectedSeparation F J U P)
    (hrange : ∀ t ∈ J, ∀ x, τ (t, x) ∈ J)
    (hfixed : ∀ t x, t ∉ J ∨ x ∉ U → τ (t, x) = t)
    (hplateau : ∀ t x, x ∈ P → τ (t, x) = ρ t)
    (hρ : Injective ρ) (hfinite : (FamilyDoublePoints.doublePoints F).Finite) :
    (FamilyDoublePoints.doublePoints (clockFamily F τ)).Finite := by
  apply (hfinite.union (hfinite.preimage (timePairMap_injective hρ).injOn)).subset
  intro p hp
  rcases (clock_doublePoints_iff hPU hsep hrange hfixed hplateau p).mp hp with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2.2

end Wikipedia.HopfProblem.OrbitPair.TimeRetiming
