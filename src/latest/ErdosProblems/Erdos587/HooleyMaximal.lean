import Mathlib

/-!
# A finite weighted maximal inequality

Each binary choice has weights `1` and `w`, and multiplies the divisor
count by `1` and `2`, respectively. Dividing by `(1+2w)/(1+w)` preserves
its weighted mean. We prove the maximal inequality directly on the finite
choice tree, without a probabilistic or analytic hypothesis.
-/

open scoped BigOperators

namespace Erdos587

def DeltaChoice : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × DeltaChoice n

instance deltaChoiceFintype : (n : ℕ) → Fintype (DeltaChoice n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := deltaChoiceFintype n
    exact inferInstanceAs (Fintype (Bool × DeltaChoice n))

def deltaChoiceWeight : (w : List ℝ) → DeltaChoice w.length → ℝ
  | [], _ => 1
  | a :: w, s => (if s.1 then a else 1) * deltaChoiceWeight w s.2

def deltaChoiceMass (w : List ℝ) : ℝ := (w.map (fun a => 1 + a)).prod

noncomputable def deltaChoiceNormalizer (a : ℝ) : ℝ := (1 + 2 * a) / (1 + a)

/-- A crossing at any prefix, including the empty and the full prefix. -/
def deltaChoiceCrosses : (w : List ℝ) → ℝ → ℝ → DeltaChoice w.length → Prop
  | [], B, z, _ => B ≤ z
  | a :: w, B, z, s => B ≤ z ∨
      deltaChoiceCrosses w B
        ((if s.1 then 2 else 1) * z / deltaChoiceNormalizer a) s.2

noncomputable def deltaChoicePrefixValue :
    (w : List ℝ) → ℝ → DeltaChoice w.length → ℕ → ℝ
  | [], z, _, _ => z
  | _ :: _, z, _, 0 => z
  | a :: w, z, s, k + 1 => deltaChoicePrefixValue w
      ((if s.1 then 2 else 1) * z / deltaChoiceNormalizer a) s.2 k

lemma deltaChoiceCrosses_iff_exists_prefix (w : List ℝ) (B z : ℝ)
    (s : DeltaChoice w.length) :
    deltaChoiceCrosses w B z s ↔
      ∃ k ≤ w.length, B ≤ deltaChoicePrefixValue w z s k := by
  induction w generalizing z with
  | nil => simp [deltaChoiceCrosses, deltaChoicePrefixValue]
  | cons a w ih =>
    rw [deltaChoiceCrosses, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, Nat.zero_le _, h⟩
      · exact ⟨k + 1, Nat.succ_le_succ hk, h⟩
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero => exact Or.inl h
      | succ k => exact Or.inr ⟨k, Nat.le_of_succ_le_succ hk, h⟩

noncomputable def deltaCrossingMass (w : List ℝ) (B z : ℝ) : ℝ := by
  classical
  exact ∑ s : DeltaChoice w.length,
    if deltaChoiceCrosses w B z s then deltaChoiceWeight w s else 0

lemma deltaChoiceWeight_nonneg {w : List ℝ} (hw : ∀ a ∈ w, 0 ≤ a)
    (s : DeltaChoice w.length) : 0 ≤ deltaChoiceWeight w s := by
  induction w with
  | nil => exact zero_le_one
  | cons a w ih =>
    change 0 ≤ (if s.1 then a else 1) * deltaChoiceWeight w s.2
    apply mul_nonneg
    · split_ifs
      · exact hw a (by simp)
      · exact zero_le_one
    · exact ih (fun b hb => hw b (by simp [hb])) s.2

lemma deltaChoiceMass_nonneg {w : List ℝ} (hw : ∀ a ∈ w, 0 ≤ a) :
    0 ≤ deltaChoiceMass w := by
  unfold deltaChoiceMass
  apply List.prod_nonneg
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact add_nonneg zero_le_one (hw b hb)

lemma sum_deltaChoiceWeight (w : List ℝ) :
    (∑ s : DeltaChoice w.length, deltaChoiceWeight w s) = deltaChoiceMass w := by
  induction w with
  | nil =>
    change (∑ _s : Unit, (1 : ℝ)) = 1
    simp
  | cons a w ih =>
    change (∑ s : Bool × DeltaChoice w.length,
      (if s.1 then a else 1) * deltaChoiceWeight w s.2) = _
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.false_eq_true, if_true, if_false, one_mul]
    rw [← Finset.mul_sum, ih]
    simp only [deltaChoiceMass, List.map_cons, List.prod_cons]
    ring

lemma deltaCrossingMass_of_crossed {w : List ℝ} {B z : ℝ} (hz : B ≤ z) :
    deltaCrossingMass w B z = deltaChoiceMass w := by
  classical
  have hcross : ∀ s, deltaChoiceCrosses w B z s := by
    cases w with
    | nil => exact fun _ => hz
    | cons a w => exact fun _ => Or.inl hz
  simp only [deltaCrossingMass, hcross, if_true, sum_deltaChoiceWeight]

lemma deltaCrossingMass_nil (B z : ℝ) :
    deltaCrossingMass [] B z = if B ≤ z then 1 else 0 := by
  classical
  change (∑ _s : Unit, if B ≤ z then (1 : ℝ) else 0) = _
  simp

lemma deltaCrossingMass_cons {a B z : ℝ} (w : List ℝ) (hz : ¬ B ≤ z) :
    deltaCrossingMass (a :: w) B z =
      a * deltaCrossingMass w B (2 * z / deltaChoiceNormalizer a) +
        deltaCrossingMass w B (z / deltaChoiceNormalizer a) := by
  classical
  unfold deltaCrossingMass
  change (∑ s : Bool × DeltaChoice w.length,
    if deltaChoiceCrosses (a :: w) B z s then deltaChoiceWeight (a :: w) s else 0) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [deltaChoiceCrosses, deltaChoiceWeight, hz, false_or,
    Bool.false_eq_true, if_true, if_false, one_mul,
    Finset.mul_sum, mul_ite, mul_zero]

lemma deltaChoiceNormalizer_pos {a : ℝ} (ha : 0 ≤ a) :
    0 < deltaChoiceNormalizer a := by
  unfold deltaChoiceNormalizer
  positivity

lemma deltaChoiceNormalizer_balance {a z : ℝ} (ha : 0 ≤ a) :
    a * (2 * z / deltaChoiceNormalizer a) + z / deltaChoiceNormalizer a =
      z * (1 + a) := by
  have ha1 : (1 + a : ℝ) ≠ 0 := by positivity
  have ha2 : (1 + 2 * a : ℝ) ≠ 0 := by positivity
  unfold deltaChoiceNormalizer
  field_simp
  ring

/-- The total weight of paths crossing `B`, multiplied by `B`, is bounded
by the initial value times the total weight of all paths. -/
theorem deltaCrossingMass_maximal {w : List ℝ} (hw : ∀ a ∈ w, 0 ≤ a)
    (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    B * deltaCrossingMass w B z ≤ z * deltaChoiceMass w := by
  induction w generalizing z with
  | nil =>
    rw [deltaCrossingMass_nil]
    simp only [deltaChoiceMass, List.map_nil, List.prod_nil, mul_one]
    split_ifs with h
    · simpa using h
    · simpa using hz
  | cons a w ih =>
    have ha : 0 ≤ a := hw a (by simp)
    have hw' : ∀ b ∈ w, 0 ≤ b := fun b hb => hw b (by simp [hb])
    by_cases hcross : B ≤ z
    · rw [deltaCrossingMass_of_crossed hcross]
      exact mul_le_mul_of_nonneg_right hcross (deltaChoiceMass_nonneg hw)
    · rw [deltaCrossingMass_cons w hcross]
      have htrue := ih hw' (z := 2 * z / deltaChoiceNormalizer a)
        (div_nonneg (mul_nonneg (by norm_num) hz) (deltaChoiceNormalizer_pos ha).le)
      have hfalse := ih hw' (z := z / deltaChoiceNormalizer a)
        (div_nonneg hz (deltaChoiceNormalizer_pos ha).le)
      calc
        _ = a * (B * deltaCrossingMass w B (2 * z / deltaChoiceNormalizer a)) +
            B * deltaCrossingMass w B (z / deltaChoiceNormalizer a) := by ring
        _ ≤ a * ((2 * z / deltaChoiceNormalizer a) * deltaChoiceMass w) +
            (z / deltaChoiceNormalizer a) * deltaChoiceMass w :=
          add_le_add (mul_le_mul_of_nonneg_left htrue ha) hfalse
        _ = (a * (2 * z / deltaChoiceNormalizer a) + z / deltaChoiceNormalizer a) *
            deltaChoiceMass w := by ring
        _ = z * deltaChoiceMass (a :: w) := by
          rw [deltaChoiceNormalizer_balance ha]
          simp only [deltaChoiceMass, List.map_cons, List.prod_cons]
          ring

/-- A reciprocal-threshold bound for the explicitly defined prefix event. -/
theorem deltaChoice_prefix_maximal {w : List ℝ} (hw : ∀ a ∈ w, 0 ≤ a)
    {B : ℝ} (hB : 0 < B) :
    (∑ s : DeltaChoice w.length,
      if ∃ k ≤ w.length, B ≤ deltaChoicePrefixValue w 1 s k then
        deltaChoiceWeight w s else 0) ≤ deltaChoiceMass w / B := by
  classical
  simp_rw [← deltaChoiceCrosses_iff_exists_prefix]
  change deltaCrossingMass w B 1 ≤ deltaChoiceMass w / B
  rw [le_div_iff₀ hB]
  simpa only [mul_comm, one_mul, mul_one] using deltaCrossingMass_maximal hw B zero_le_one

end Erdos587
