/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.External.Erdos88.Fourier

/-!
# Adaptive exposure trees

A full binary query tree chooses one of the remaining coordinates, reads its
Boolean value, and then continues in the branch selected by that value.  The
chronological answer word is a bijective, Hamming-weight-preserving change of
coordinates on the Boolean cube.  This is the finite symmetry behind adaptive
exposure of a uniform fixed-cardinality random set.
-/

open scoped BigOperators

noncomputable section

namespace Erdos900

/-- A query plan for `n` still-unread Boolean coordinates.  At a node the
coordinate `pivot` is read and removed; the remaining plan may depend on the
answer. -/
inductive AdaptiveTree : ℕ → Type
  | nil : AdaptiveTree 0
  | node {n : ℕ} (pivot : Fin (n + 1))
      (next : Bool → AdaptiveTree n) : AdaptiveTree (n + 1)

namespace AdaptiveTree

/-- Apply a branch-dependent equivalence to the second member of a pair. -/
def branchEquiv {α β : Type*} (e : Bool → α ≃ β) :
    Bool × α ≃ Bool × β where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

/-- The answer word produced by an adaptive tree, as an equivalence of
Boolean cubes.  The first output coordinate is the answer at the root. -/
def answerEquiv : {n : ℕ} → AdaptiveTree n →
    (Fin n → Bool) ≃ (Fin n → Bool)
  | 0, nil => Equiv.refl _
  | _ + 1, node pivot next =>
      (Fin.insertNthEquiv (fun _ : Fin (_ + 1) ↦ Bool) pivot).symm |>.trans
        (branchEquiv fun b ↦ answerEquiv (next b)) |>.trans
        (Fin.consEquiv (fun _ : Fin (_ + 1) ↦ Bool))

@[simp] theorem answerEquiv_nil :
    answerEquiv AdaptiveTree.nil = Equiv.refl (Fin 0 → Bool) := rfl

@[simp] theorem answerEquiv_node_zero {n : ℕ} (pivot : Fin (n + 1))
    (next : Bool → AdaptiveTree n) (x : Fin (n + 1) → Bool) :
    answerEquiv (.node pivot next) x 0 = x pivot := by
  simp [answerEquiv, branchEquiv]

@[simp] theorem answerEquiv_node_tail {n : ℕ} (pivot : Fin (n + 1))
    (next : Bool → AdaptiveTree n) (x : Fin (n + 1) → Bool) (i : Fin n) :
    answerEquiv (.node pivot next) x i.succ =
      answerEquiv (next (x pivot)) (Fin.removeNth pivot x) i := by
  simp [answerEquiv, branchEquiv]

/-- A sum over `Fin (n+1)` splits at an arbitrary coordinate. -/
theorem sum_indicator_removeNth {n : ℕ} (pivot : Fin (n + 1))
    (x : Fin (n + 1) → Bool) :
    (∑ i, if x i then 1 else 0) =
      (if x pivot then 1 else 0) +
        ∑ i, if Fin.removeNth pivot x i then 1 else 0 := by
  rw [Fin.sum_univ_succAbove]
  rfl

/-- The Boolean-slice Hamming weight is the corresponding indicator sum. -/
theorem boolWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
    Erdos88.Fourier.boolWeight x = ∑ i, if x i then 1 else 0 := by
  classical
  rw [Erdos88.Fourier.boolWeight, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Finset.mem_univ, if_true]

/-- Adaptive exposure merely reorders the input bits, even though the order
may depend on bits already read.  In particular it preserves Hamming weight. -/
theorem boolWeight_answerEquiv : {n : ℕ} → (T : AdaptiveTree n) →
    ∀ x, Erdos88.Fourier.boolWeight (answerEquiv T x) =
      Erdos88.Fourier.boolWeight x
  | 0, nil, x => by
      simp [boolWeight_eq_sum]
  | _ + 1, node pivot next, x => by
      rw [boolWeight_eq_sum, boolWeight_eq_sum]
      rw [Fin.sum_univ_succ]
      simp only [answerEquiv_node_zero, answerEquiv_node_tail]
      rw [← boolWeight_eq_sum
        (answerEquiv (next (x pivot)) (Fin.removeNth pivot x))]
      rw [boolWeight_answerEquiv (next (x pivot))]
      rw [boolWeight_eq_sum]
      exact (sum_indicator_removeNth pivot x).symm

/-- Restrict the adaptive cube equivalence to a fixed Hamming-weight slice. -/
def sliceEquiv (T : AdaptiveTree n) (m : ℕ) :
    Erdos88.Fourier.BoolSlice (Fin n) m ≃
      Erdos88.Fourier.BoolSlice (Fin n) m where
  toFun x := ⟨answerEquiv T x.1, by simpa [boolWeight_answerEquiv T x.1] using x.2⟩
  invFun x := ⟨(answerEquiv T).symm x.1, by
    have h := boolWeight_answerEquiv T ((answerEquiv T).symm x.1)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm.trans x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (answerEquiv T).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (answerEquiv T).apply_symm_apply x.1

@[simp] theorem sliceEquiv_val (T : AdaptiveTree n) (m : ℕ)
    (x : Erdos88.Fourier.BoolSlice (Fin n) m) :
    (sliceEquiv T m x).1 = answerEquiv T x.1 := rfl

end AdaptiveTree
end Erdos900
