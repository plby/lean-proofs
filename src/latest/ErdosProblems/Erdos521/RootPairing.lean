/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting separated real roots under a local pairing, with two boundary losses.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

theorem card_le_card_add_two_of_pairing (F G : Finset ℝ) {a b ρ : ℝ} (hρ : 0 ≤ ρ)
    (hI : ∀ x ∈ F, x ∈ Set.Icc a b)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 2 * ρ < |x - y|)
    (hpair : ∀ x ∈ F, a + ρ ≤ x → x ≤ b - ρ → ∃ y ∈ G, |y - x| ≤ ρ) :
    F.card ≤ G.card + 2 := by
  classical
  let F₀ := F.filter (fun x ↦ a + ρ ≤ x ∧ x ≤ b - ρ)
  let F₁ := F.filter (fun x ↦ x < a + ρ)
  let F₂ := F.filter (fun x ↦ b - ρ < x)
  have hleft : F₁.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxF, hx₁⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyF, hy₁⟩ := Finset.mem_filter.mp hy
    by_contra hne
    have h := hsep x hxF y hyF hne
    have hdist : |x - y| ≤ ρ := abs_le.mpr
      ⟨by linarith [(hI x hxF).1], by linarith [(hI y hyF).1]⟩
    linarith
  have hright : F₂.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxF, hx₂⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyF, hy₂⟩ := Finset.mem_filter.mp hy
    by_contra hne
    have h := hsep x hxF y hyF hne
    have hdist : |x - y| ≤ ρ := abs_le.mpr
      ⟨by linarith [(hI y hyF).2], by linarith [(hI x hxF).2]⟩
    linarith
  have htransfer : ∀ x : F₀, ∃ y : G, |(y : ℝ) - (x : ℝ)| ≤ ρ := by
    intro x
    obtain ⟨hxF, hxlo, hxhi⟩ := Finset.mem_filter.mp x.2
    obtain ⟨y, hyG, hdist⟩ := hpair x hxF hxlo hxhi
    exact ⟨⟨y, hyG⟩, hdist⟩
  choose f hf using htransfer
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have h := hsep x (Finset.mem_filter.mp x.2).1 y (Finset.mem_filter.mp y.2).1 hne
    have heq : (f x : ℝ) = (f y : ℝ) := congrArg Subtype.val hxy
    have htriangle := abs_sub_le (x : ℝ) (f x : ℝ) (y : ℝ)
    have hx : |(x : ℝ) - (f x : ℝ)| ≤ ρ := by simpa only [abs_sub_comm] using hf x
    have hy : |(f x : ℝ) - (y : ℝ)| ≤ ρ := by rw [heq]; exact hf y
    linarith
  have hinner : F₀.card ≤ G.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have hcover : F ⊆ F₀ ∪ (F₁ ∪ F₂) := by
    intro x hx
    by_cases hlo : a + ρ ≤ x
    · by_cases hhi : x ≤ b - ρ
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hlo, hhi⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hhi⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hlo⟩))))
  have hcard : F.card ≤ F₀.card + (F₁.card + F₂.card) :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (add_le_add le_rfl (Finset.card_union_le _ _)))
  omega

end Erdos521
