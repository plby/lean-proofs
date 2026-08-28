import Wikipedia.NoExoticSixSphere.JamesWordTopology
import Wikipedia.NoExoticSixSphere.JamesWordStrata

/-!
# Continuous reversal and pointed maps on the original James words

Reversal is the actual reverse of the reduced word. A pointed letter
map acts letter by letter, retaining the original final topology.
Both operations preserve every finite stage. No new topology or
homotopy relation is assigned to the words.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesWordReversal

open NoExoticSixSphere

variable {X Y : Type*} (x₀ : X) (y₀ : Y)

def reverse (w : James.Space X x₀) : James.Space X x₀ :=
  MulOpposite.unop (James.lift x₀ (fun x ↦ MulOpposite.op (James.letter x₀ x)) w)

theorem reverse_one : reverse x₀ 1 = 1 := by
  change MulOpposite.unop (James.lift x₀
    (fun x ↦ MulOpposite.op (James.letter x₀ x)) 1) = 1
  rw [map_one]
  rfl

theorem reverse_mul (v w : James.Space X x₀) :
    reverse x₀ (v * w) = reverse x₀ w * reverse x₀ v := by
  change MulOpposite.unop (James.lift x₀
    (fun x ↦ MulOpposite.op (James.letter x₀ x)) (v * w)) = _
  rw [map_mul]
  rfl

theorem reverse_letter (x : X) : reverse x₀ (James.letter x₀ x) = James.letter x₀ x := by
  change MulOpposite.unop (James.lift x₀
    (fun x ↦ MulOpposite.op (James.letter x₀ x)) (James.letter x₀ x)) = _
  rw [James.lift_letter x₀ _ (by rw [James.letter_basepoint]; rfl)]
  rfl

theorem reverse_word (l : List X) : reverse x₀ (James.word x₀ l) = James.word x₀ l.reverse := by
  induction l with
  | nil => exact reverse_one x₀
  | cons x l ih =>
    rw [James.word_cons, reverse_mul, ih, reverse_letter,
      List.reverse_cons, James.word_append, James.word_singleton]

theorem reverse_reverse (w : James.Space X x₀) : reverse x₀ (reverse x₀ w) = w := by
  obtain ⟨l, rfl⟩ := James.word_surjective x₀ w
  rw [reverse_word, reverse_word, List.reverse_reverse]

theorem size_reverse_le (w : James.Space X x₀) :
    James.size x₀ (reverse x₀ w) ≤ James.size x₀ w := by
  have h := James.size_word_le x₀ (James.letters x₀ w).reverse
  rw [← reverse_word, James.word_letters, List.length_reverse, James.length_letters] at h
  exact h

theorem size_reverse (w : James.Space X x₀) :
    James.size x₀ (reverse x₀ w) = James.size x₀ w := by
  have h := size_reverse_le x₀ (reverse x₀ w)
  rw [reverse_reverse] at h
  exact le_antisymm (size_reverse_le x₀ w) h

def mapWords (f : X → Y) : James.Space X x₀ →* James.Space Y y₀ :=
  James.lift x₀ (fun x ↦ James.letter y₀ (f x))

theorem mapWords_letter (f : X → Y) (hf : f x₀ = y₀) (x : X) :
    mapWords x₀ y₀ f (James.letter x₀ x) = James.letter y₀ (f x) :=
  James.lift_letter x₀ _ (by rw [hf, James.letter_basepoint]) x

theorem mapWords_word (f : X → Y) (hf : f x₀ = y₀) (l : List X) :
    mapWords x₀ y₀ f (James.word x₀ l) = James.word y₀ (l.map f) := by
  induction l with
  | nil => exact map_one _
  | cons x l ih =>
    rw [James.word_cons, map_mul, mapWords_letter x₀ y₀ f hf, ih,
      List.map_cons, James.word_cons]

theorem size_mapWords_le (f : X → Y) (hf : f x₀ = y₀) (w : James.Space X x₀) :
    James.size y₀ (mapWords x₀ y₀ f w) ≤ James.size x₀ w := by
  have h := James.size_word_le y₀ ((James.letters x₀ w).map f)
  rw [← mapWords_word x₀ y₀ f hf, James.word_letters, List.length_map, James.length_letters] at h
  exact h

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_reverse : Continuous (reverse x₀) := by
  apply (James.continuous_iff_on_words x₀ _).mpr
  intro n
  have h := James.continuous_word_map x₀
    (List.ofFn (fun i : Fin n ↦ i)).reverse
    (fun v : Fin n → X ↦ fun i ↦ v i) (fun i ↦ continuous_apply i)
  apply h.congr
  intro v
  rw [reverse_word, List.map_reverse, ← List.ofFn_comp']

def reverseMap : C(James.Space X x₀, James.Space X x₀) :=
  ⟨reverse x₀, continuous_reverse x₀⟩

theorem continuous_mapWords (f : X → Y) (hf : f x₀ = y₀) (hc : Continuous f) :
    Continuous (mapWords x₀ y₀ f) := by
  apply (James.continuous_iff_on_words x₀ _).mpr
  intro n
  have h := (James.continuous_word_array y₀ n).comp
    (continuous_pi (fun i : Fin n ↦ hc.comp (continuous_apply i)))
  apply h.congr
  intro v
  rw [mapWords_word x₀ y₀ f hf, ← List.ofFn_comp']
  rfl

def mapWordsContinuous (f : C(X, Y)) (hf : f x₀ = y₀) :
    C(James.Space X x₀, James.Space Y y₀) :=
  ⟨mapWords x₀ y₀ f, continuous_mapWords x₀ y₀ f hf f.continuous⟩

def stageReverse (k : ℕ) : C(James.stage x₀ k, James.stage x₀ k) :=
  ⟨fun w ↦ ⟨reverse x₀ w.val, (size_reverse_le x₀ w.val).trans w.property⟩,
    ((continuous_reverse x₀).comp continuous_subtype_val).subtype_mk _⟩

def stageMap (f : C(X, Y)) (hf : f x₀ = y₀) (k : ℕ) :
    C(James.stage x₀ k, James.stage y₀ k) :=
  ⟨fun w ↦ ⟨mapWords x₀ y₀ f w.val, (size_mapWords_le x₀ y₀ f hf w.val).trans w.property⟩,
    ((continuous_mapWords x₀ y₀ f hf f.continuous).comp continuous_subtype_val).subtype_mk _⟩

end Wikipedia.HopfProblem.DegreeCollapse.JamesWordReversal
