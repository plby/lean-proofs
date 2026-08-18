/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.Basic
import ErdosProblems.Erdos984.HunterAnnulus

/-!
# Deterministic blue-set glue in Hunter's construction

These lemmas separate the two reasons a union of translated annuli contains
no blue three-term progression: a progression cannot use different
translates, and it cannot lie in one thin annulus.
-/

namespace Erdos984

section AddCommGroup

variable {G ι : Type*} [AddCommGroup G]

def StepThreeFree (S : Set G) (v : G) : Prop :=
  ∀ x : G, x ∈ S → x + v ∈ S → (x + v) + v ∈ S → False

def CrossThreeSeparated (A : ι → Set G) (v : G) : Prop :=
  ∀ (i₀ i₁ i₂ : ι) (x : G),
    x ∈ A i₀ → x + v ∈ A i₁ → (x + v) + v ∈ A i₂ →
      i₀ = i₁ ∧ i₁ = i₂

lemma stepThreeFree_iUnion (A : ι → Set G) (v : G)
    (hcross : CrossThreeSeparated A v)
    (hfiber : ∀ i, StepThreeFree (A i) v) :
    StepThreeFree (⋃ i, A i) v := by
  intro x hx₀ hx₁ hx₂
  simp only [Set.mem_iUnion] at hx₀ hx₁ hx₂
  obtain ⟨i₀, hi₀⟩ := hx₀
  obtain ⟨i₁, hi₁⟩ := hx₁
  obtain ⟨i₂, hi₂⟩ := hx₂
  obtain ⟨rfl, rfl⟩ := hcross i₀ i₁ i₂ x hi₀ hi₁ hi₂
  exact hfiber i₀ x hi₀ hi₁ hi₂

lemma stepThreeFree_biUnion {J : Set ι} (A : ι → Set G) (v : G)
    (hcross : CrossThreeSeparated A v)
    (hfiber : ∀ i ∈ J, StepThreeFree (A i) v) :
    StepThreeFree (⋃ i ∈ J, A i) v := by
  intro x hx₀ hx₁ hx₂
  simp only [Set.mem_iUnion] at hx₀ hx₁ hx₂
  obtain ⟨i₀, hi₀J, hi₀⟩ := hx₀
  obtain ⟨i₁, hi₁J, hi₁⟩ := hx₁
  obtain ⟨i₂, hi₂J, hi₂⟩ := hx₂
  obtain ⟨rfl, rfl⟩ := hcross i₀ i₁ i₂ x hi₀ hi₁ hi₂
  exact hfiber i₀ hi₀J x hi₀ hi₁ hi₂

end AddCommGroup

section Orbit

variable {G : Type*} [AddCommGroup G]

def additiveOrbit (θ : G) (n : ℕ) : G := n • θ

lemma additiveOrbit_add (θ : G) (m n : ℕ) :
    additiveOrbit θ (m + n) = additiveOrbit θ m + n • θ := by
  simp [additiveOrbit, add_nsmul]

def orbitColor (θ : G) (blue : Set G) [DecidablePred (· ∈ blue)] (n : ℕ) : Bool :=
  decide (additiveOrbit θ n ∉ blue)

@[simp] lemma orbitColor_eq_false {θ : G} {blue : Set G} [DecidablePred (· ∈ blue)]
    {n : ℕ} : orbitColor θ blue n = false ↔ additiveOrbit θ n ∈ blue := by
  simp [orbitColor]

/-- Pulling a stepwise three-free set back along a torus orbit gives the
blue half of an off-diagonal coloring. -/
lemma orbitColor_avoids_false_three (θ : G) (blue : Set G)
    [DecidablePred (· ∈ blue)] (N : ℕ)
    (hfree : ∀ d : ℕ, 0 < d → d < N → StepThreeFree blue (d • θ)) :
    AvoidsColorAP (orbitColor θ blue) false N 3 := by
  intro a d hd hend
  have hdN : d < N := by omega
  by_contra hnot
  simp only [not_exists, not_and, Decidable.not_not] at hnot
  have hc₀ : orbitColor θ blue a = false := by
    simpa only [zero_mul, Nat.add_zero] using hnot 0 (by norm_num)
  have hc₁ : orbitColor θ blue (a + d) = false := by
    simpa using hnot 1 (by norm_num)
  have hc₂ : orbitColor θ blue (a + 2 * d) = false := by
    simpa using hnot 2 (by norm_num)
  have hm₀ := (orbitColor_eq_false).1 hc₀
  have hm₁ := (orbitColor_eq_false).1 hc₁
  have hm₂ := (orbitColor_eq_false).1 hc₂
  apply hfree d hd hdN (additiveOrbit θ a) hm₀
  · simpa only [additiveOrbit_add] using hm₁
  · have heq : additiveOrbit θ (a + 2 * d) =
        (additiveOrbit θ a + d • θ) + d • θ := by
      simp only [additiveOrbit_add, mul_nsmul, two_nsmul, nsmul_add, add_assoc]
    rw [← heq]
    exact hm₂

end Orbit

end Erdos984
