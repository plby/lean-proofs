import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.OfFn

/-!
# The actual reduced words underlying the James construction

Words consist of non-basepoint letters. The map from arbitrary words
deletes precisely the basepoint letters. Its universal property is the
pointed free-monoid property; no homotopy equivalence or exact sequence is
included in this algebraic construction.
-/

noncomputable section

namespace NoExoticSixSphere.James

universe u v

def Space (X : Type u) (x₀ : X) := FreeMonoid {x : X // x ≠ x₀}

instance {X : Type u} (x₀ : X) : Monoid (Space X x₀) :=
  inferInstanceAs (Monoid (FreeMonoid {x : X // x ≠ x₀}))

variable {X : Type u} (x₀ : X)

def letter (x : X) : Space X x₀ := by
  classical
  exact if h : x = x₀ then 1 else FreeMonoid.of ⟨x, h⟩

theorem letter_basepoint : letter x₀ x₀ = 1 := by simp [letter]

theorem letter_of_ne {x : X} (h : x ≠ x₀) :
    letter x₀ x = (FreeMonoid.of ⟨x, h⟩ : Space X x₀) := by
  exact dif_neg h

def word : List X → Space X x₀
  | [] => 1
  | x :: l => letter x₀ x * word l

theorem word_nil : word x₀ [] = 1 := rfl

theorem word_cons (x : X) (l : List X) :
    word x₀ (x :: l) = letter x₀ x * word x₀ l := rfl

theorem word_singleton (x : X) : word x₀ [x] = letter x₀ x := by
  rw [word_cons, word_nil, mul_one]

theorem word_append (l r : List X) : word x₀ (l ++ r) = word x₀ l * word x₀ r := by
  induction l with
  | nil => rw [List.nil_append, word_nil, one_mul]
  | cons x l ih => rw [List.cons_append, word_cons, word_cons, ih, mul_assoc]

theorem word_basepoint_cons (l : List X) : word x₀ (x₀ :: l) = word x₀ l := by
  rw [word_cons, letter_basepoint, one_mul]

theorem word_delete_basepoint (l r : List X) :
    word x₀ (l ++ x₀ :: r) = word x₀ (l ++ r) := by
  rw [word_append, word_basepoint_cons, word_append]

def letters (w : Space X x₀) : List X :=
  (FreeMonoid.toList w).map Subtype.val

theorem letters_one : letters x₀ 1 = [] := rfl

theorem letters_mul (v w : Space X x₀) :
    letters x₀ (v * w) = letters x₀ v ++ letters x₀ w := by
  change (FreeMonoid.toList v ++ FreeMonoid.toList w).map Subtype.val = _
  exact List.map_append

theorem letters_letter_mul {x : X} (h : x ≠ x₀) (w : Space X x₀) :
    letters x₀ (letter x₀ x * w) = x :: letters x₀ w := by
  rw [letter_of_ne x₀ h]
  rfl

theorem word_nonbasepoint_list (l : List {x : X // x ≠ x₀}) :
    word x₀ (l.map Subtype.val) = (FreeMonoid.ofList l : Space X x₀) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, word_cons, letter_of_ne x₀ x.property, ih]
    rfl

theorem word_letters (w : Space X x₀) : word x₀ (letters x₀ w) = w :=
  word_nonbasepoint_list x₀ (FreeMonoid.toList w)

theorem word_surjective : Function.Surjective (word x₀) :=
  fun w ↦ ⟨letters x₀ w, word_letters x₀ w⟩

variable {N : Type v} [Monoid N]

def lift (f : X → N) : Space X x₀ →* N :=
  FreeMonoid.lift (fun x : {x : X // x ≠ x₀} ↦ f x.val)

theorem lift_letter (f : X → N) (hf : f x₀ = 1) (x : X) :
    lift x₀ f (letter x₀ x) = f x := by
  by_cases hx : x = x₀
  · subst x
    rw [letter_basepoint, map_one, hf]
  · rw [letter_of_ne x₀ hx]
    exact FreeMonoid.lift_eval_of _ _

theorem lift_word (f : X → N) (hf : f x₀ = 1) (l : List X) :
    lift x₀ f (word x₀ l) = (l.map f).prod := by
  induction l with
  | nil => exact map_one _
  | cons x l ih => rw [word_cons, map_mul, lift_letter x₀ f hf, ih]; rfl

theorem hom_ext (f g : Space X x₀ →* N)
    (h : ∀ x, f (letter x₀ x) = g (letter x₀ x)) : f = g := by
  apply MonoidHom.ext
  intro w
  obtain ⟨l, rfl⟩ := word_surjective x₀ w
  induction l with
  | nil => rw [word_nil, map_one, map_one]
  | cons x l ih => rw [word_cons, map_mul, map_mul, h, ih]

end NoExoticSixSphere.James
