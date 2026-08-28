import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Path
import Mathlib.Tactic.Linarith

/-!
# A topological monoid of genuine Moore loops

A loop carries a nonnegative real duration and a continuous real-parameter
curve, constant before time zero and after that duration. Concatenation
shifts the second curve by the first duration. Consequently its unit and
associativity laws are exact equalities, without quotienting by homotopy.
-/

noncomputable section

namespace NoExoticSixSphere.Moore

variable {Y : Type*} [TopologicalSpace Y]

def Loop (y₀ : Y) :=
  {p : ℝ × C(ℝ, Y) // 0 ≤ p.1 ∧ (∀ t, t ≤ 0 → p.2 t = y₀) ∧
    ∀ t, p.1 ≤ t → p.2 t = y₀}

namespace Loop

variable {y₀ : Y}

instance : TopologicalSpace (Loop y₀) := inferInstanceAs (TopologicalSpace
  {p : ℝ × C(ℝ, Y) // 0 ≤ p.1 ∧ (∀ t, t ≤ 0 → p.2 t = y₀) ∧
    ∀ t, p.1 ≤ t → p.2 t = y₀})

def duration (p : Loop y₀) : ℝ := p.val.1

def curve (p : Loop y₀) : C(ℝ, Y) := p.val.2

theorem duration_nonneg (p : Loop y₀) : 0 ≤ p.duration := p.property.1

theorem curve_of_nonpos (p : Loop y₀) (t : ℝ) (ht : t ≤ 0) : p.curve t = y₀ :=
  p.property.2.1 t ht

theorem curve_of_duration_le (p : Loop y₀) (t : ℝ) (ht : p.duration ≤ t) :
    p.curve t = y₀ := p.property.2.2 t ht

theorem curve_zero (p : Loop y₀) : p.curve 0 = y₀ := p.curve_of_nonpos 0 le_rfl

theorem curve_duration (p : Loop y₀) : p.curve p.duration = y₀ :=
  p.curve_of_duration_le _ le_rfl

@[ext]
theorem ext {p q : Loop y₀} (hd : p.duration = q.duration)
    (hc : ∀ t, p.curve t = q.curve t) : p = q := by
  apply Subtype.ext
  exact Prod.ext hd (ContinuousMap.ext hc)

def identity (y₀ : Y) : Loop y₀ :=
  ⟨(0, ContinuousMap.const ℝ y₀), le_rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

def concatenate (p q : Loop y₀) : Loop y₀ := by
  let f : C(ℝ, Y) := ⟨fun t ↦ if t ≤ p.duration then p.curve t
      else q.curve (t - p.duration),
    p.curve.continuous.if_le
      (q.curve.continuous.comp (continuous_id.sub continuous_const))
      continuous_id continuous_const (fun t ht ↦ by
        rw [ht, sub_self, p.curve_duration, q.curve_zero])⟩
  refine ⟨(p.duration + q.duration, f), add_nonneg p.duration_nonneg q.duration_nonneg,
    ?_, ?_⟩
  · intro t ht
    change (if t ≤ p.duration then p.curve t else q.curve (t - p.duration)) = y₀
    rw [if_pos (ht.trans p.duration_nonneg)]
    exact p.curve_of_nonpos t ht
  · intro t ht
    change (if t ≤ p.duration then p.curve t else q.curve (t - p.duration)) = y₀
    split_ifs
    · apply p.curve_of_duration_le
      linarith [q.duration_nonneg]
    · apply q.curve_of_duration_le
      linarith

theorem duration_concatenate (p q : Loop y₀) :
    (concatenate p q).duration = p.duration + q.duration := rfl

theorem curve_concatenate (p q : Loop y₀) (t : ℝ) :
    (concatenate p q).curve t =
      if t ≤ p.duration then p.curve t else q.curve (t - p.duration) := rfl

theorem identity_concatenate (p : Loop y₀) : concatenate (identity y₀) p = p := by
  apply ext
  · change 0 + p.duration = p.duration
    exact zero_add _
  · intro t
    rw [curve_concatenate]
    change (if t ≤ 0 then y₀ else p.curve (t - 0)) = p.curve t
    by_cases ht : t ≤ 0
    · rw [if_pos ht, p.curve_of_nonpos t ht]
    · rw [if_neg ht, sub_zero]

theorem concatenate_identity (p : Loop y₀) : concatenate p (identity y₀) = p := by
  apply ext
  · change p.duration + 0 = p.duration
    exact add_zero _
  · intro t
    rw [curve_concatenate]
    change (if t ≤ p.duration then p.curve t else y₀) = p.curve t
    by_cases ht : t ≤ p.duration
    · rw [if_pos ht]
    · rw [if_neg ht, p.curve_of_duration_le t (le_of_not_ge ht)]

theorem concatenate_assoc (p q r : Loop y₀) :
    concatenate (concatenate p q) r = concatenate p (concatenate q r) := by
  apply ext
  · change (p.duration + q.duration) + r.duration =
      p.duration + (q.duration + r.duration)
    exact add_assoc _ _ _
  · intro t
    simp only [curve_concatenate, duration_concatenate]
    by_cases hp : t ≤ p.duration
    · have hpq : t ≤ p.duration + q.duration := by linarith [q.duration_nonneg]
      simp [hpq, hp]
    · by_cases hpq : t ≤ p.duration + q.duration
      · have hq : t - p.duration ≤ q.duration := by linarith
        simp [hpq, hp, hq]
      · have hq : ¬ t - p.duration ≤ q.duration := by linarith
        simp [hpq, hp, hq, sub_sub]

instance : Monoid (Loop y₀) where
  one := identity y₀
  mul := concatenate
  one_mul := identity_concatenate
  mul_one := concatenate_identity
  mul_assoc := concatenate_assoc

theorem duration_one : (1 : Loop y₀).duration = 0 := rfl

theorem curve_one (t : ℝ) : (1 : Loop y₀).curve t = y₀ := rfl

theorem duration_mul (p q : Loop y₀) : (p * q).duration = p.duration + q.duration := rfl

theorem curve_mul (p q : Loop y₀) (t : ℝ) :
    (p * q).curve t = if t ≤ p.duration then p.curve t else q.curve (t - p.duration) := rfl

end Loop

end NoExoticSixSphere.Moore
