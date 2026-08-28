import Wikipedia.NoExoticSixSphere.JamesReducedWords

/-!
# The second James--Hopf word formula, with the basepoint relations checked

Pairs are ordered by increasing second position, then increasing first
position: right lexicographic order. Pairings which kill either basepoint
give a well-defined operation on actual reduced words.

This is the combinatorial second James--Hopf map. The loop-space comparison
and EHP exactness are not assertions of this file.
-/

noncomputable section

namespace NoExoticSixSphere.James

variable {X Y Z : Type*}

def pairsFrom (p : List X) : List X → List (X × X)
  | [] => []
  | x :: l => p.map (fun y ↦ (y, x)) ++ pairsFrom (p ++ [x]) l

def pairs (l : List X) : List (X × X) := pairsFrom [] l

theorem pairsFrom_map (f : X → Y) (p l : List X) :
    pairsFrom (p.map f) (l.map f) =
      (pairsFrom p l).map (fun z ↦ (f z.1, f z.2)) := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, pairsFrom]
    rw [show p.map f ++ [f x] = (p ++ [x]).map f by simp, ih]
    simp only [List.map_append, List.map_map, Function.comp_def]

theorem pairs_map (f : X → Y) (l : List X) :
    pairs (l.map f) = (pairs l).map (fun z ↦ (f z.1, f z.2)) :=
  pairsFrom_map f [] l

variable (x₀ : X) (z₀ : Z) (b : X → X → Z)

def pairWord (p : Space X x₀) (x : X) : Space Z z₀ :=
  lift x₀ (fun y ↦ letter z₀ (b y x)) p

variable (hleft : ∀ x, b x₀ x = z₀) (hright : ∀ x, b x x₀ = z₀)

include hleft in
theorem pairWord_word (p : List X) (x : X) :
    pairWord x₀ z₀ b (word x₀ p) x = word z₀ (p.map (fun y ↦ b y x)) := by
  have hb : (fun y ↦ letter z₀ (b y x)) x₀ = 1 := by
    change letter z₀ (b x₀ x) = 1
    rw [hleft, letter_basepoint]
  induction p with
  | nil => exact map_one _
  | cons y p ih =>
    change lift x₀ (fun y ↦ letter z₀ (b y x))
      (letter x₀ y * word x₀ p) = letter z₀ (b y x) * word z₀ (p.map (fun y ↦ b y x))
    rw [map_mul, lift_letter x₀ _ hb]
    exact congrArg (fun w ↦ letter z₀ (b y x) * w) ih

include hleft hright in
theorem pairWord_basepoint (p : Space X x₀) : pairWord x₀ z₀ b p x₀ = 1 := by
  obtain ⟨l, rfl⟩ := word_surjective x₀ p
  rw [pairWord_word x₀ z₀ b hleft]
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, word_cons, hright, letter_basepoint, one_mul, ih]

def hopfAux (p : Space X x₀) : List X → Space Z z₀
  | [] => 1
  | x :: l => pairWord x₀ z₀ b p x * hopfAux (p * letter x₀ x) l

include hleft hright in
theorem hopfAux_basepoint_cons (p : Space X x₀) (l : List X) :
    hopfAux x₀ z₀ b p (x₀ :: l) = hopfAux x₀ z₀ b p l := by
  rw [hopfAux, pairWord_basepoint x₀ z₀ b hleft hright, letter_basepoint, mul_one, one_mul]

include hleft hright in
theorem hopfAux_normalize (p : Space X x₀) (l : List X) :
    hopfAux x₀ z₀ b p (letters x₀ (word x₀ l)) = hopfAux x₀ z₀ b p l := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = x₀
    · subst x
      rw [word_basepoint_cons, hopfAux_basepoint_cons x₀ z₀ b hleft hright, ih]
    · rw [word_cons, letters_letter_mul x₀ hx, hopfAux, hopfAux, ih]

include hleft in
theorem hopfAux_word (p l : List X) :
    hopfAux x₀ z₀ b (word x₀ p) l =
      word z₀ ((pairsFrom p l).map (fun z ↦ b z.1 z.2)) := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    rw [hopfAux, pairWord_word x₀ z₀ b hleft]
    rw [show word x₀ p * letter x₀ x = word x₀ (p ++ [x]) by
      rw [word_append, word_singleton], ih]
    rw [pairsFrom, List.map_append, word_append, List.map_map]
    rfl

def secondHopf (w : Space X x₀) : Space Z z₀ := hopfAux x₀ z₀ b 1 (letters x₀ w)

theorem secondHopf_one : secondHopf x₀ z₀ b 1 = 1 := rfl

include hleft hright in
theorem secondHopf_word (l : List X) :
    secondHopf x₀ z₀ b (word x₀ l) = word z₀ ((pairs l).map (fun z ↦ b z.1 z.2)) := by
  rw [secondHopf, hopfAux_normalize x₀ z₀ b hleft hright]
  exact hopfAux_word x₀ z₀ b hleft [] l

include hleft hright in
theorem secondHopf_letter (x : X) : secondHopf x₀ z₀ b (letter x₀ x) = 1 := by
  rw [← word_singleton x₀ x, secondHopf_word x₀ z₀ b hleft hright]
  rfl

include hleft hright in
theorem secondHopf_two_letters (x y : X) :
    secondHopf x₀ z₀ b (letter x₀ x * letter x₀ y) = letter z₀ (b x y) := by
  have he : letter x₀ x * letter x₀ y = word x₀ [x, y] := by
    rw [word_cons, word_singleton]
  rw [he, secondHopf_word x₀ z₀ b hleft hright]
  exact word_singleton z₀ (b x y)

end NoExoticSixSphere.James
