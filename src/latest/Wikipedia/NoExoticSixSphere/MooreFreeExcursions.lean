import Wikipedia.NoExoticSixSphere.MooreLoopTopology
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Unique concatenation of genuine loop excursions

A positive-duration loop with no interior basepoint visit is an excursion.
Equality of concatenated excursions determines the first duration, then
the first loop, and then the remaining word. An injective alphabet of
excursions therefore induces an injective map from the actual free monoid.
-/

noncomputable section

namespace NoExoticSixSphere.Moore.Loop

variable {Y A : Type*} [TopologicalSpace Y] {y₀ : Y}

def IsExcursion (p : Loop y₀) : Prop :=
  0 < p.duration ∧ ∀ t, 0 < t → t < p.duration → p.curve t ≠ y₀

theorem mul_left_cancel_loops {p q r : Loop y₀} (h : p * q = p * r) : q = r := by
  apply ext
  · have hd := congrArg duration h
    rw [duration_mul, duration_mul] at hd
    exact add_left_cancel hd
  · intro t
    by_cases ht : t ≤ 0
    · rw [q.curve_of_nonpos t ht, r.curve_of_nonpos t ht]
    · have hs : ¬ p.duration + t ≤ p.duration := by linarith
      have hc := congrArg (fun v : Loop y₀ ↦ v.curve (p.duration + t)) h
      rw [curve_mul, if_neg hs, curve_mul, if_neg hs] at hc
      have he : p.duration + t - p.duration = t := by ring
      simpa only [he] using hc

theorem duration_le_of_excursion_mul_eq {p q r s : Loop y₀}
    (hp : IsExcursion p) (hq : IsExcursion q) (h : p * r = q * s) :
    q.duration ≤ p.duration := by
  by_contra hn
  have hlt : p.duration < q.duration := lt_of_not_ge hn
  have hc := congrArg (fun v : Loop y₀ ↦ v.curve p.duration) h
  rw [curve_mul, if_pos le_rfl, curve_duration, curve_mul, if_pos (le_of_lt hlt)] at hc
  exact hq.2 p.duration hp.1 hlt hc.symm

theorem first_eq_of_excursion_mul_eq {p q r s : Loop y₀}
    (hp : IsExcursion p) (hq : IsExcursion q) (h : p * r = q * s) : p = q := by
  have hd : p.duration = q.duration := le_antisymm
    (duration_le_of_excursion_mul_eq hq hp h.symm)
    (duration_le_of_excursion_mul_eq hp hq h)
  apply ext hd
  intro t
  by_cases ht : t ≤ p.duration
  · have hq : t ≤ q.duration := hd ▸ ht
    have hc := congrArg (fun v : Loop y₀ ↦ v.curve t) h
    rw [curve_mul, if_pos ht, curve_mul, if_pos hq] at hc
    exact hc
  · have hpt : p.duration ≤ t := le_of_not_ge ht
    have hqt : q.duration ≤ t := hd ▸ hpt
    rw [p.curve_of_duration_le t hpt, q.curve_of_duration_le t hqt]

theorem list_prod_injective_of_excursions (g : A → Loop y₀) (hg : Function.Injective g)
    (he : ∀ a, IsExcursion (g a)) : Function.Injective (fun l : List A ↦ (l.map g).prod) := by
  intro l
  induction l with
  | nil =>
    intro r h
    cases r with
    | nil => rfl
    | cons b r =>
      have hd := congrArg duration h
      simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
        duration_one, duration_mul] at hd
      have hp := (he b).1
      have hr := ((r.map g).prod).duration_nonneg
      linarith
  | cons a l ih =>
    intro r h
    cases r with
    | nil =>
      have hd := congrArg duration h
      simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
        duration_one, duration_mul] at hd
      have hp := (he a).1
      have hl := ((l.map g).prod).duration_nonneg
      linarith
    | cons b r =>
      simp only [List.map_cons, List.prod_cons] at h
      have hab : a = b := hg (first_eq_of_excursion_mul_eq (he a) (he b) h)
      subst b
      exact congrArg (List.cons a) (ih (mul_left_cancel_loops h))

theorem freeMonoid_lift_injective_of_excursions (g : A → Loop y₀)
    (hg : Function.Injective g) (he : ∀ a, IsExcursion (g a)) :
    Function.Injective (FreeMonoid.lift g) := by
  intro v w h
  apply FreeMonoid.toList.injective
  apply list_prod_injective_of_excursions g hg he
  simpa only [FreeMonoid.lift_apply] using h

end NoExoticSixSphere.Moore.Loop
