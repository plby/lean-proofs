module

public import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.GroupWithZero.Hom

public section

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

lemma indicator_one_inter_apply (s t : Set α) (x : α) : 𝟭_[s ∩ t, M₀] x = 𝟭_[s] x * 𝟭_[t] x := by
  classical simp [indicator_apply, ← ite_and, and_comm]

lemma indicator_one_inter (s t : Set α) : 𝟭_[s ∩ t, M₀] = 𝟭_[s] * 𝟭_[t] :=
  funext <| indicator_one_inter_apply _ _

lemma map_indicator_one [FunLike F M₀ N₀] [MonoidWithZeroHomClass F M₀ N₀] (f : F) (s : Set α)
    (x : α) : f (𝟭_[s] x) = 𝟭_[s] x := by classical exact MonoidWithZeroHom.map_ite_one_zero ..

variable (M₀) in
@[simp] lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [indicator_apply, ← e.eq_symm_apply]

variable [Nontrivial M₀] {a : α}

@[simp high] lemma indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

lemma indicator_one_apply_ne_zero : 𝟭_[s, M₀] a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff

@[simp high] lemma indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]

lemma indicator_one_ne_zero : 𝟭_[s, M₀] ≠ 0 ↔ s.Nonempty := by simp [nonempty_iff_ne_empty]

variable (M₀) in
@[simp high] lemma support_indicator_one : 𝟭_[s, M₀].support = s := by
  ext; exact indicator_one_apply_ne_zero

end Set
