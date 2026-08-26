/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Basic definitions for Steve Fan's "Strongly complete sets and a conjecture of Erdős",
arXiv:2607.14071v3. No completeness criterion is assumed here.
-/
import Mathlib

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- A sum using each element of `A` at most once. -/
def IsSumOfDistinct (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ∑ x ∈ S, x = n

/-- The empty sum is included; this does not change eventual completeness. -/
def subsetSums (A : Set ℕ) : Set ℕ := {n | IsSumOfDistinct A n}

def IsComplete (A : Set ℕ) : Prop := ∀ᶠ n in atTop, IsSumOfDistinct A n

def IsStronglyComplete (A : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, IsComplete (A \ (D : Set ℕ))

/-- Distance to the nearest integer, expressed using the norm on `ℝ / ℤ`. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := ‖(x : UnitAddCircle)‖

lemma distToNearestInt_eq (x : ℝ) : distToNearestInt x = |x - round x| :=
  UnitAddCircle.norm_eq

lemma distToNearestInt_nonneg (x : ℝ) : 0 ≤ distToNearestInt x := norm_nonneg _

/-- Fan's divergence condition; nonnegative terms make nonsummability equivalent
to divergence of partial sums to infinity. -/
def PhaseDivergent (A : Set ℕ) : Prop :=
  ∀ θ : UnitAddCircle, θ ≠ 0 → ¬ Summable (fun a : A ↦ ‖(a : ℕ) • θ‖)

noncomputable def dyadicBlock (A : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter (· ∈ A)

@[simp] lemma mem_dyadicBlock {A : Set ℕ} {k n : ℕ} :
    n ∈ dyadicBlock A k ↔ 2 ^ k < n ∧ n ≤ 2 ^ (k + 1) ∧ n ∈ A := by
  classical
  simp [dyadicBlock, and_assoc]

lemma IsSumOfDistinct.mono {A B : Set ℕ} {n : ℕ}
    (h : IsSumOfDistinct A n) (hAB : A ⊆ B) : IsSumOfDistinct B n := by
  rcases h with ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hAB, rfl⟩

lemma IsComplete.mono {A B : Set ℕ} (hA : IsComplete A) (hAB : A ⊆ B) :
    IsComplete B := Filter.Eventually.mono hA fun _ hn ↦ hn.mono hAB

lemma IsStronglyComplete.isComplete {A : Set ℕ} (hA : IsStronglyComplete A) :
    IsComplete A := by
  simpa using hA ∅

lemma IsStronglyComplete.mono {A B : Set ℕ} (hA : IsStronglyComplete A)
    (hAB : A ⊆ B) : IsStronglyComplete B := by
  intro D
  exact (hA D).mono (sdiff_subset_sdiff_left hAB)

lemma IsSumOfDistinct.add {A B : Set ℕ} {m n : ℕ} (hAB : Disjoint A B)
    (hm : IsSumOfDistinct A m) (hn : IsSumOfDistinct B n) :
    IsSumOfDistinct (A ∪ B) (m + n) := by
  classical
  rcases hm with ⟨F, hF, rfl⟩
  rcases hn with ⟨G, hG, rfl⟩
  have hd : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hAB (hF hx) (hG hy)
  refine ⟨F ∪ G, ?_, Finset.sum_union hd⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Or.inl (hF hx)
  · exact Or.inr (hG hx)

lemma summable_sdiff_finset_iff (A : Set ℕ) (D : Finset ℕ) (f : ℕ → ℝ) :
    Summable (fun a : ↥(A \ (D : Set ℕ)) ↦ f a) ↔ Summable (fun a : A ↦ f a) := by
  let S : Set A := Subtype.val ⁻¹' (D : Set ℕ)
  have hS : S.Finite := (D.finite_toSet).preimage Subtype.val_injective.injOn
  let e : ↥(Sᶜ) ≃ ↥(A \ (D : Set ℕ)) :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have he := e.summable_iff (f := fun a : ↥(A \ (D : Set ℕ)) ↦ f a)
  have hs := hS.summable_compl_iff (f := fun a : A ↦ f a)
  exact he.symm.trans hs

lemma PhaseDivergent.sdiff_finset {A : Set ℕ} (hA : PhaseDivergent A) (D : Finset ℕ) :
    PhaseDivergent (A \ (D : Set ℕ)) := by
  intro θ hθ hsum
  exact hA θ hθ ((summable_sdiff_finset_iff A D (fun a ↦ ‖a • θ‖)).mp hsum)

lemma PhaseDivergent.mono {A B : Set ℕ} (hA : PhaseDivergent A) (hAB : A ⊆ B) :
    PhaseDivergent B := by
  intro θ hθ hsum
  have hi : Function.Injective (fun a : A ↦ (⟨a.1, hAB a.2⟩ : B)) := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : B ↦ (z : ℕ)) h)
  exact hA θ hθ (Summable.comp_injective (f := fun a : B ↦ ‖(a : ℕ) • θ‖)
    (i := fun a : A ↦ (⟨a.1, hAB a.2⟩ : B)) hsum hi)

/-- The exact phase interval occurring in the original Problem 254 suffices. -/
lemma phaseDivergent_of_unit_interval {A : Set ℕ}
    (hA : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun a : A ↦ distToNearestInt (θ * (a : ℝ)))) : PhaseDivergent A := by
  intro θ hθ hsum
  let x := AddCircle.equivIco (1 : ℝ) 0 θ
  have hx : (x : ℝ) ∈ Set.Ico 0 1 := by simpa using x.2
  have heq : ((x : ℝ) : UnitAddCircle) = θ := AddCircle.coe_equivIco
  have hxpos : 0 < (x : ℝ) := by
    by_contra h
    have hz : (x : ℝ) = 0 := by linarith [hx.1]
    apply hθ
    rw [← heq, hz, AddCircle.coe_zero]
  apply hA x hxpos hx.2
  simpa only [distToNearestInt, mul_comm (x : ℝ), ← nsmul_eq_mul,
    AddCircle.coe_nsmul, heq] using hsum

end Erdos254
