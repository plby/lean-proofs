import Wikipedia.NoExoticSixSphere.JamesWordTopology
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Compactness.Compact

/-!
# Finite stages of the actual James construction

The stage indexed by `n` consists of reduced words of length at most `n`.
Padding with basepoints realizes it as the image of the `n`th Cartesian
power. The presentation has finite point fibers, a fact used to establish
separation and compact-domain factorization in the weak topology.
-/

noncomputable section

namespace NoExoticSixSphere.James

variable {X : Type*} (x₀ : X)

def size (w : Space X x₀) : ℕ := FreeMonoid.length w

theorem size_one : size x₀ 1 = 0 := rfl

theorem size_mul (v w : Space X x₀) : size x₀ (v * w) = size x₀ v + size x₀ w :=
  FreeMonoid.length_mul v w

theorem size_letter_le (x : X) : size x₀ (letter x₀ x) ≤ 1 := by
  by_cases h : x = x₀
  · subst x
    rw [letter_basepoint, size_one]
    exact Nat.zero_le _
  · rw [letter_of_ne x₀ h]
    exact Nat.le_refl 1

theorem size_word_le (l : List X) : size x₀ (word x₀ l) ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x l ih =>
    rw [word_cons, size_mul, List.length_cons]
    have h := size_letter_le x₀ x
    omega

theorem length_letters (w : Space X x₀) : (letters x₀ w).length = size x₀ w :=
  List.length_map Subtype.val

theorem letters_word [DecidableEq X] (l : List X) :
    letters x₀ (word x₀ l) = l.filter (fun x ↦ decide (x ≠ x₀)) := by
  classical
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x = x₀
    · subst x
      rw [word_basepoint_cons, ih]
      simp
    · rw [word_cons, letters_letter_mul x₀ h, ih]
      simp [h]

theorem mem_letters_word_iff (x : X) (l : List X) :
    x ∈ letters x₀ (word x₀ l) ↔ x ∈ l ∧ x ≠ x₀ := by
  classical
  rw [letters_word]
  simp only [List.mem_filter, decide_eq_true_eq]

theorem word_replicate_basepoint (n : ℕ) : word x₀ (List.replicate n x₀) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, word_basepoint_cons, ih]

def stage (n : ℕ) : Set (Space X x₀) := {w | size x₀ w ≤ n}

theorem stage_mono {n m : ℕ} (h : n ≤ m) : stage x₀ n ⊆ stage x₀ m :=
  fun _ hw ↦ hw.trans h

theorem mem_stage_size (w : Space X x₀) : w ∈ stage x₀ (size x₀ w) :=
  show size x₀ w ≤ size x₀ w from le_rfl

theorem exists_array_of_mem_stage {n : ℕ} {w : Space X x₀} (h : w ∈ stage x₀ n) :
    ∃ v : Fin n → X, word x₀ (List.ofFn v) = w := by
  let l := letters x₀ w ++ List.replicate (n - size x₀ w) x₀
  have hl : l.length = n := by
    dsimp [l]
    rw [List.length_append, length_letters, List.length_replicate]
    exact Nat.add_sub_of_le h
  have hw : word x₀ l = w := by
    rw [word_append, word_letters, word_replicate_basepoint, mul_one]
  refine ⟨fun i ↦ l.get (Fin.cast hl.symm i), ?_⟩
  rw [← List.ofFn_congr hl l.get, List.ofFn_get]
  exact hw

theorem range_word_array (n : ℕ) :
    Set.range (fun v : Fin n → X ↦ word x₀ (List.ofFn v)) = stage x₀ n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    change size x₀ (word x₀ (List.ofFn v)) ≤ n
    have h := size_word_le x₀ (List.ofFn v)
    simpa only [List.length_ofFn] using h
  · intro w hw
    exact exists_array_of_mem_stage x₀ hw

theorem finite_array_fiber (n : ℕ) (w : Space X x₀) :
    {v : Fin n → X | word x₀ (List.ofFn v) = w}.Finite := by
  classical
  let a : Set X := insert x₀ {x | x ∈ letters x₀ w}
  have ha : a.Finite := (List.finite_toSet (letters x₀ w)).insert x₀
  apply (Set.Finite.pi' (fun _ : Fin n ↦ ha)).subset
  intro v hv i
  change v i = x₀ ∨ v i ∈ letters x₀ w
  by_cases h : v i = x₀
  · exact Or.inl h
  · right
    rw [← hv]
    exact (mem_letters_word_iff x₀ (v i) (List.ofFn v)).mpr
      ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩

variable [TopologicalSpace X]

theorem isCompact_stage [CompactSpace X] (n : ℕ) : IsCompact (stage x₀ n) := by
  rw [← range_word_array]
  exact isCompact_range (continuous_word_array x₀ n)

end NoExoticSixSphere.James
