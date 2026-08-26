import ErdosProblems.Erdos192.Core

namespace Erdos192

/-- Positive standard-coordinate unit steps in real coordinate space. -/
def PositiveUnitWalk {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∀ n, ∃ i : Fin d, ∀ j, p (n + 1) j = p n j + if j = i then 1 else 0

/-- A nontrivial arithmetic progression, with its times in increasing order. -/
def HasWalkAP {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧ ∀ j, p a j + p c j = 2 * p b j

/-- The real Parikh walk with an arbitrary starting point. -/
def realWalk {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) (n : ℕ) (j : Fin d) : ℝ :=
  x j + parikhCount f n j

theorem parikhCount_succ {d : ℕ} (f : ℕ → Fin d) (n : ℕ) (j : Fin d) :
    parikhCount f (n + 1) j = parikhCount f n j + if j = f n then 1 else 0 := by
  by_cases h : j = f n
  · subst j
    simp [parikhCount, Finset.range_add_one, Finset.filter_insert]
  · simp [parikhCount, Finset.range_add_one, Finset.filter_insert, h, Ne.symm h]

theorem realWalk_positive {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    PositiveUnitWalk (realWalk x f) := by
  intro n
  refine ⟨f n, ?_⟩
  intro j
  simp only [realWalk, parikhCount_succ, Nat.cast_add]
  split_ifs <;> simp <;> ring

theorem positiveUnitWalk_representation {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : PositiveUnitWalk p) : ∃ f : ℕ → Fin d, p = realWalk (p 0) f := by
  classical
  choose f hf using hp
  refine ⟨f, funext fun n => funext fun j => ?_⟩
  induction n with
  | zero => simp [realWalk, parikhCount]
  | succ n ih =>
    rw [hf n j, ih]
    simp only [realWalk, parikhCount_succ, Nat.cast_add]
    split_ifs <;> simp <;> ring

theorem realWalk_hasAP_iff {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    HasWalkAP (realWalk x f) ↔ hasParikhAP f := by
  unfold HasWalkAP hasParikhAP
  constructor
  · rintro ⟨a, b, c, hab, hbc, h⟩
    refine ⟨a, b, c, hab, hbc, fun j => ?_⟩
    have hj := h j
    simp only [realWalk] at hj
    have : (parikhCount f a j : ℝ) + parikhCount f c j = 2 * parikhCount f b j := by
      linarith
    exact_mod_cast this
  · rintro ⟨a, b, c, hab, hbc, h⟩
    refine ⟨a, b, c, hab, hbc, fun j => ?_⟩
    have hj : (parikhCount f a j : ℝ) + parikhCount f c j = 2 * parikhCount f b j :=
      by exact_mod_cast h j
    simp only [realWalk]
    linarith

theorem geometric_classification_iff_words (d : ℕ) :
    (∀ p : ℕ → Fin d → ℝ, PositiveUnitWalk p → HasWalkAP p) ↔
      (∀ f : ℕ → Fin d, hasParikhAP f) := by
  constructor
  · intro h f
    exact (realWalk_hasAP_iff 0 f).mp (h _ (realWalk_positive 0 f))
  · intro h p hp
    obtain ⟨f, hf⟩ := positiveUnitWalk_representation p hp
    rw [hf]
    exact (realWalk_hasAP_iff _ f).mpr (h f)

theorem sum_parikhCount {d : ℕ} (f : ℕ → Fin d) (n : ℕ) :
    (∑ j : Fin d, parikhCount f n j) = n := by
  induction n with
  | zero => simp [parikhCount]
  | succ n ih => simp [parikhCount_succ, Finset.sum_add_distrib, ih]

theorem sum_realWalk {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) (n : ℕ) :
    (∑ j, realWalk x f n j) = (∑ j, x j) + n := by
  simp only [realWalk, Finset.sum_add_distrib]
  congr 1
  exact_mod_cast sum_parikhCount f n

theorem realWalk_injective {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    Function.Injective (realWalk x f) := by
  intro a b h
  have hs := congrArg (fun v : Fin d → ℝ => ∑ j, v j) h
  rw [sum_realWalk, sum_realWalk] at hs
  exact_mod_cast (add_left_cancel hs)

/-- The visited set contains three distinct points in arithmetic progression.
Only the first two need be required distinct: the equation forces the third. -/
def ContainsThreeTermAP {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∃ x y z : Fin d → ℝ, x ∈ Set.range p ∧ y ∈ Set.range p ∧ z ∈ Set.range p ∧
    x ≠ y ∧ ∀ j, x j + z j = 2 * y j

theorem realWalk_setAP_iff {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    ContainsThreeTermAP (realWalk x f) ↔ HasWalkAP (realWalk x f) := by
  constructor
  · rintro ⟨_, _, _, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, hne, h⟩
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => h j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_realWalk] at hs
    have hn : (a : ℝ) + c = 2 * b := by linarith
    have hn' : a + c = 2 * b := by exact_mod_cast hn
    have hab : a ≠ b := fun hab => hne (congrArg (realWalk x f) hab)
    by_cases ht : a < b
    · exact ⟨a, b, c, ht, by omega, h⟩
    · exact ⟨c, b, a, by omega, by omega, fun j => by rw [add_comm]; exact h j⟩
  · rintro ⟨a, b, c, hab, hbc, h⟩
    exact ⟨_, _, _, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩,
      fun heq => (Nat.ne_of_lt hab) (realWalk_injective x f heq), h⟩

theorem positiveUnitWalk_setAP_iff {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : PositiveUnitWalk p) : ContainsThreeTermAP p ↔ HasWalkAP p := by
  obtain ⟨f, hf⟩ := positiveUnitWalk_representation p hp
  rw [hf]
  exact realWalk_setAP_iff _ f

theorem no_zero_dimensional_walk (p : ℕ → Fin 0 → ℝ) : ¬PositiveUnitWalk p := by
  intro hp
  obtain ⟨i, _⟩ := hp 0
  exact Fin.elim0 i

end Erdos192
