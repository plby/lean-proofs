import ErdosProblems.Erdos73.ProjectiveDiagonalTree
import ErdosProblems.Erdos73.QuadrangleCorners

/-! Explicit corner labels and edge/opposite pairings of the projective quadrangulation. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

abbrev ProjectivePort (n : ℕ) := ProjectiveFace n × Fin 4

def projectiveFaceCorner {n : ℕ} (hn : 2 ≤ n) : ProjectiveFace n → Fin 4 → Fin n × Fin n
  | Sum.inl (r, c) =>
    if hr : r.val + 1 < n then
      ![(r, ⟨c.val, by have hh := c.isLt; omega⟩),
        (r, ⟨c.val + 1, by have hh := c.isLt; omega⟩),
        (⟨r.val + 1, hr⟩, ⟨c.val + 1, by have hh := c.isLt; omega⟩),
        (⟨r.val + 1, hr⟩, ⟨c.val, by have hh := c.isLt; omega⟩)]
    else
      ![(r, ⟨c.val, by have hh := c.isLt; omega⟩),
        (r, ⟨c.val + 1, by have hh := c.isLt; omega⟩),
        (⟨0, by omega⟩, ⟨n - 2 - c.val, by omega⟩),
        (⟨0, by omega⟩, ⟨n - 1 - c.val, by omega⟩)]
  | Sum.inr j =>
    ![projectiveRoot hn,
      projectiveBoundary hn ⟨2 * j.val + 1, by have hh := j.isLt; omega⟩,
      projectiveBoundary hn ⟨2 * j.val + 2, by have hh := j.isLt; omega⟩,
      projectiveBoundary hn ⟨2 * j.val + 3, by have hh := j.isLt; omega⟩]

def projectivePortLabel {n : ℕ} (hn : 2 ≤ n) (d : ProjectivePort n) : Fin n × Fin n :=
  projectiveFaceCorner hn d.1 d.2

def projectiveFaceParity {n : ℕ} : ProjectiveFace n → Bool
  | Sum.inl (r, c) => decide ((r.val + c.val) % 2 = 1)
  | Sum.inr _ => false

def projectiveFaceFlipped {n : ℕ} : ProjectiveFace n → Bool
  | Sum.inl (r, c) => decide (r.val = 0 ∧ c.val % 2 = 1)
  | Sum.inr _ => false

def projectivePortPair (n : ℕ) : Perm (ProjectivePort n) :=
  fiberPermutation (fun f => quadranglePair (projectiveFaceParity f))

theorem projectivePortPair_apply {n : ℕ} (d : ProjectivePort n) :
    projectivePortPair n d = (d.1, quadranglePair (projectiveFaceParity d.1) d.2) := rfl

def projectivePortOpposite (n : ℕ) : Perm (ProjectivePort n) :=
  fiberPermutation (fun _ => quadrangleOpposite)

theorem projectivePortOtherPair_apply {n : ℕ} (d : ProjectivePort n) :
    (projectivePortOpposite n * projectivePortPair n) d =
      (d.1, quadranglePair (!(projectiveFaceParity d.1)) d.2) :=
  Prod.ext rfl (quadrangleOpposite_pair (projectiveFaceParity d.1) d.2)

def projectivePortSelected {n : ℕ} (d : ProjectivePort n) : Bool :=
  quadrangleSelected (projectiveFaceFlipped d.1) d.2

theorem projectivePortPair_involutive (n : ℕ) : Function.Involutive (projectivePortPair n) :=
  fiberPermutation_involutive _ (fun f => quadranglePair_involutive (projectiveFaceParity f))

theorem projectivePortOpposite_involutive (n : ℕ) :
    Function.Involutive (projectivePortOpposite n) :=
  fiberPermutation_involutive _ (fun _ => quadrangleOpposite_involutive)

theorem projectivePortPair_free {n : ℕ} (d : ProjectivePort n) : projectivePortPair n d ≠ d := by
  intro he
  exact quadranglePair_free (projectiveFaceParity d.1) d.2 (congrArg Prod.snd he)

theorem projectivePortPair_commute (n : ℕ) :
    Function.Commute (projectivePortPair n) (projectivePortOpposite n) := by
  intro d
  exact Prod.ext rfl (quadranglePair_commute (projectiveFaceParity d.1) d.2)

theorem projectivePortSelected_opposite {n : ℕ} (d : ProjectivePort n) :
    projectivePortSelected (projectivePortOpposite n d) = projectivePortSelected d :=
  quadrangleSelected_opposite (projectiveFaceFlipped d.1) d.2

theorem projectivePortSelected_pair {n : ℕ} (d : ProjectivePort n) :
    projectivePortSelected (projectivePortPair n d) = !projectivePortSelected d :=
  quadrangleSelected_pair (projectiveFaceParity d.1) (projectiveFaceFlipped d.1) d.2

theorem projectiveBoundary_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (projectiveBoundary hn) := by
  intro i j he
  have hr := congrArg (fun v : Fin n × Fin n => v.1.val) he
  have hc := congrArg (fun v : Fin n × Fin n => v.2.val) he
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  dsimp only [projectiveBoundary] at hr hc
  split_ifs at hr hc <;> simp only [Fin.val_mk] at hr hc <;> omega

theorem projectiveFaceCorner_injective {n : ℕ} (hn : 2 ≤ n) (f : ProjectiveFace n) :
    Function.Injective (projectiveFaceCorner hn f) := by
  intro i j he
  rcases f with ⟨r, c⟩ | k
  · have hr := r.isLt
    have hc := c.isLt
    by_cases hh : r.val + 1 < n
    all_goals fin_cases i <;> fin_cases j <;>
      simp [projectiveFaceCorner, hh, Prod.mk.injEq, Fin.ext_iff] at he ⊢ <;> omega
  · have hk := k.isLt
    have hz : projectiveRoot hn = projectiveBoundary hn ⟨0, by omega⟩ := by
      dsimp only [projectiveBoundary, projectiveRoot]
      rw [dif_pos (by omega)]
    fin_cases i <;> fin_cases j <;>
      simp only [projectiveFaceCorner, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, hz] at he
    all_goals try rfl
    all_goals have hh := congrArg Fin.val (projectiveBoundary_injective hn he)
    all_goals apply Fin.ext
    all_goals dsimp only at hh ⊢
    all_goals omega

theorem projectivePortLabel_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (projectivePortLabel hn) := by
  rintro ⟨r, c⟩
  have hc := c.isLt
  by_cases hh : c.val + 1 < n
  · refine ⟨(Sum.inl (r, ⟨c.val, by omega⟩), 0), ?_⟩
    dsimp only [projectivePortLabel, projectiveFaceCorner]
    split <;> simp
  · refine ⟨(Sum.inl (r, ⟨c.val - 1, by omega⟩), 1), ?_⟩
    dsimp only [projectivePortLabel, projectiveFaceCorner]
    split <;> simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    all_goals apply Prod.ext
    all_goals first | rfl | (apply Fin.ext; dsimp only; omega)

end
end Erdos73
