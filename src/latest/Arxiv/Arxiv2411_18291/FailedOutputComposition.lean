import Arxiv.Arxiv2411_18291.FiniteObservedOutput

/-!
# Successive random outputs with dependent later stages

None records failure and stops the construction. A successful later output
is paired with all earlier outputs. The next distribution may depend on
that entire successful history; no independence assumption is made.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

def bindObservedOutput {A : Type*} {B : A → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a))) :
    PMF (Option (Σ a, B a)) :=
  p.bind fun oa => match oa with
    | none => PMF.pure none
    | some a => (q a).map (Option.map (Sigma.mk a))

theorem map_option_failure {A B : Type*} (f : A → B) (p : PMF (Option A)) :
    (p.map (Option.map f)) none = p none := by
  classical
  rw [PMF.map_apply, tsum_eq_single none]
  · simp
  · intro oa hoa
    cases oa with
    | none => exact (hoa rfl).elim
    | some a => simp

theorem bindObservedOutput_failure {A : Type*} [Finite A] {B : A → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a))) :
    bindObservedOutput p q none = p none + ∑' a, p (some a) * q a none := by
  classical
  let : Fintype A := Fintype.ofFinite A
  rw [bindObservedOutput, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  simp only [PMF.pure_apply_self, mul_one, map_option_failure, tsum_fintype]

theorem option_success_mass_le_one {A : Type*} [Finite A] (p : PMF (Option A)) :
    ∑' a, p (some a) ≤ 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have h := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at h
  rw [tsum_fintype, ← h]
  exact le_add_self

theorem bindObservedOutput_failure_le {A : Type*} [Finite A] {B : A → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a))) {ε₁ ε₂ : ℝ≥0∞}
    (hp : p none ≤ ε₁) (hq : ∀ a, q a none ≤ ε₂) :
    bindObservedOutput p q none ≤ ε₁ + ε₂ := by
  rw [bindObservedOutput_failure]
  apply add_le_add hp
  calc
    ∑' a, p (some a) * q a none ≤ ∑' a, p (some a) * ε₂ :=
      ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hq a) _
    _ = (∑' a, p (some a)) * ε₂ := ENNReal.tsum_mul_right
    _ ≤ 1 * ε₂ := mul_le_mul_left (option_success_mass_le_one p) ε₂
    _ = ε₂ := one_mul _

theorem bindObservedOutput_failure_real_le {A : Type*} [Finite A] {B : A → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a))) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hp : (p none).toReal ≤ ε₁) (hq : ∀ a, (q a none).toReal ≤ ε₂) :
    (bindObservedOutput p q none).toReal ≤ ε₁ + ε₂ := by
  apply ENNReal.toReal_le_of_le_ofReal (add_nonneg hε₁ hε₂)
  rw [ENNReal.ofReal_add hε₁ hε₂]
  exact bindObservedOutput_failure_le p q
    ((ENNReal.le_ofReal_iff_toReal_le (p.apply_ne_top none) hε₁).2 hp)
    (fun a => (ENNReal.le_ofReal_iff_toReal_le ((q a).apply_ne_top none) hε₂).2 (hq a))

def fourStageOutput {A : Type*} {B : A → Type*}
    {C : (a : A) → B a → Type*} {D : (a : A) → (b : B a) → C a b → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a)))
    (r : ∀ a b, PMF (Option (C a b))) (s : ∀ a b c, PMF (Option (D a b c))) :
    PMF (Option (Σ abc : (Σ ab : (Σ a, B a), C ab.1 ab.2),
      D abc.1.1 abc.1.2 abc.2)) :=
  bindObservedOutput
    (bindObservedOutput (bindObservedOutput p q) (fun ab => r ab.1 ab.2))
    (fun abc => s abc.1.1 abc.1.2 abc.2)

theorem fourStageOutput_failure_real_le {A : Type*} [Finite A] {B : A → Type*}
    [∀ a, Finite (B a)] {C : (a : A) → B a → Type*} [∀ a b, Finite (C a b)]
    {D : (a : A) → (b : B a) → C a b → Type*}
    (p : PMF (Option A)) (q : ∀ a, PMF (Option (B a)))
    (r : ∀ a b, PMF (Option (C a b))) (s : ∀ a b c, PMF (Option (D a b c)))
    {ε₁ ε₂ ε₃ ε₄ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hε₃ : 0 ≤ ε₃) (hε₄ : 0 ≤ ε₄)
    (hp : (p none).toReal ≤ ε₁) (hq : ∀ a, (q a none).toReal ≤ ε₂)
    (hr : ∀ a b, (r a b none).toReal ≤ ε₃)
    (hs : ∀ a b c, (s a b c none).toReal ≤ ε₄) :
    (fourStageOutput p q r s none).toReal ≤ ε₁ + ε₂ + ε₃ + ε₄ := by
  apply bindObservedOutput_failure_real_le _ _
    (add_nonneg (add_nonneg hε₁ hε₂) hε₃) hε₄ _ (fun abc => hs _ _ _)
  apply bindObservedOutput_failure_real_le _ _ (add_nonneg hε₁ hε₂) hε₃ _
    (fun ab => hr _ _)
  exact bindObservedOutput_failure_real_le p q hε₁ hε₂ hp hq

end Arxiv2411_18291.FiniteHistoryProcess
