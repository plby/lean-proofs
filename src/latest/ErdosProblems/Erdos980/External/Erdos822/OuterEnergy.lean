/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.CollisionFiber
import ErdosProblems.Erdos980.External.Erdos822.FiniteEnergy

/-!
# Energy of a labeled outer layer

The outer-product presentation is injective when every outer prime exceeds
its cofactor.  Reindexing through those labels turns the shifted-totient
energy into the sum of the fixed-cofactor collision fibers.
-/

namespace Erdos822

open scoped BigOperators Finset

/-- Labeled outer inputs before forgetting the cofactor/prime presentation. -/
def outerLabels (B : ℕ → Finset ℕ) (x : ℕ) :
    Finset (Sigma fun _ : ℕ => ℕ) :=
  (B x).sigma fun m => outerPrimes x m

/-- Forget a label by multiplying its cofactor and outer prime. -/
def outerLabelProduct (z : Sigma fun _ : ℕ => ℕ) : ℕ :=
  z.1 * z.2

theorem outerInputs_eq_image_outerLabelProduct (B : ℕ → Finset ℕ) (x : ℕ) :
    outerInputs B x = (outerLabels B x).image outerLabelProduct := by
  ext n
  simp [outerInputs, outerLabels, outerLabelProduct]
  grind

theorem outerLabelProduct_injOn
    (B : ℕ → Finset ℕ) (x : ℕ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p) :
    Set.InjOn outerLabelProduct (outerLabels B x) := by
  intro a ha b hb hab
  rcases a with ⟨m, p⟩
  rcases b with ⟨m', p'⟩
  have ha' : m ∈ B x ∧ p ∈ outerPrimes x m := by
    simpa [outerLabels] using ha
  have hb' : m' ∈ B x ∧ p' ∈ outerPrimes x m' := by
    simpa [outerLabels] using hb
  have hprod : m * p = m' * p' := by
    simpa [outerLabelProduct] using hab
  have huniq := eq_of_mul_eq_mul_of_large_primes
    (mem_outerPrimes_iff.mp ha'.2).2.2
    (mem_outerPrimes_iff.mp hb'.2).2.2
    (hpos m ha'.1) (hpos m' hb'.1)
    (hlarge m ha'.1 p ha'.2) (hlarge m' hb'.1 p' hb'.2) hprod
  rcases huniq with ⟨rfl, rfl⟩
  rfl

/-- The unlabeled outer-input energy equals the energy of the labeled
cofactor-prime family. -/
theorem collisionEnergy_outerInputs_eq_labels
    (B : ℕ → Finset ℕ) (x : ℕ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p) :
    collisionEnergy (outerInputs B x) shiftedTotient =
      collisionEnergy (outerLabels B x)
        (fun z => shiftedTotient (outerLabelProduct z)) := by
  rw [outerInputs_eq_image_outerLabelProduct]
  exact collisionEnergy_image_eq_of_injOn
    (outerLabels B x) outerLabelProduct shiftedTotient
    (outerLabelProduct_injOn B x hpos hlarge)

/-- Nested sigma set of fixed-cofactor collision fibers. -/
def outerCollisionSigma (B : ℕ → Finset ℕ) (x : ℕ) :
    Finset (Sigma fun _ : ℕ => Sigma fun _ : ℕ => ℕ × ℕ) :=
  (B x).sigma fun m => (B x).sigma fun m' => outerCollisionPairs x m m'

/-- The labeled collision-pair finset is in bijection with the nested sigma
of fixed-cofactor collision fibers. -/
theorem collisionPairs_outerLabels_card_eq_sum_outerCollisionPairs
    (B : ℕ → Finset ℕ) (x : ℕ) :
    (collisionPairs (outerLabels B x)
      (fun z => shiftedTotient (outerLabelProduct z))).card =
      ∑ m ∈ B x, ∑ m' ∈ B x, (outerCollisionPairs x m m').card := by
  classical
  let S := outerCollisionSigma B x
  have hcardS :
      S.card = ∑ m ∈ B x, ∑ m' ∈ B x,
        (outerCollisionPairs x m m').card := by
    simp [S, outerCollisionSigma, Finset.card_sigma]
  rw [← hcardS]
  symm
  apply Finset.card_bij
    (fun z _ =>
      ((⟨z.1, z.2.2.1⟩ : Sigma fun _ : ℕ => ℕ),
        (⟨z.2.1, z.2.2.2⟩ : Sigma fun _ : ℕ => ℕ)))
  · intro z hz
    rcases z with ⟨m, m', p, p'⟩
    change ⟨m, ⟨m', (p, p')⟩⟩ ∈ outerCollisionSigma B x at hz
    rw [outerCollisionSigma] at hz
    simp only [Finset.mem_sigma] at hz
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product]
    rw [mem_outerCollisionPairs_iff] at hz
    simp [outerLabels, outerLabelProduct, hz.1, hz.2.1, hz.2.2.1,
      hz.2.2.2.1, hz.2.2.2.2]
  · intro z hz w hw hzw
    rcases z with ⟨m, m', p, p'⟩
    rcases w with ⟨n, n', q, q'⟩
    cases hzw
    rfl
  · intro z hz
    rcases z with ⟨⟨m, p⟩, ⟨m', p'⟩⟩
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product] at hz
    have hp : m ∈ B x ∧ p ∈ outerPrimes x m := by
      simpa [outerLabels] using hz.1.1
    have hp' : m' ∈ B x ∧ p' ∈ outerPrimes x m' := by
      simpa [outerLabels] using hz.1.2
    refine ⟨⟨m, ⟨m', (p, p')⟩⟩, ?_, ?_⟩
    change ⟨m, ⟨m', (p, p')⟩⟩ ∈ outerCollisionSigma B x
    rw [outerCollisionSigma]
    simp only [Finset.mem_sigma]
    refine ⟨hp.1, hp'.1, ?_⟩
    rw [mem_outerCollisionPairs_iff]
    exact ⟨hp.2, hp'.2,
      by simpa [outerLabelProduct] using hz.2⟩
    rfl

/-- Exact sum formula for the collision energy of an injectively labeled
outer layer. -/
theorem collisionEnergy_outerInputs_eq_sum_outerCollisionPairs
    (B : ℕ → Finset ℕ) (x : ℕ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p) :
    collisionEnergy (outerInputs B x) shiftedTotient =
      ∑ m ∈ B x, ∑ m' ∈ B x, (outerCollisionPairs x m m').card := by
  rw [collisionEnergy_outerInputs_eq_labels B x hpos hlarge,
    ← collisionPairs_card_eq_collisionEnergy]
  exact collisionPairs_outerLabels_card_eq_sum_outerCollisionPairs B x

/-- Off-diagonal part of the cofactor-indexed outer collision energy. -/
def offDiagonalOuterCollisionEnergy (B : ℕ → Finset ℕ) (x : ℕ) : ℕ :=
  ∑ m ∈ B x, ∑ m' ∈ (B x).erase m,
    (outerCollisionPairs x m m').card

/-- The diagonal cofactor contribution is exactly the number of outer
inputs; all remaining energy is the explicit off-diagonal sum. -/
theorem collisionEnergy_outerInputs_eq_card_add_offDiagonal
    (B : ℕ → Finset ℕ) (x : ℕ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p) :
    collisionEnergy (outerInputs B x) shiftedTotient =
      (outerInputs B x).card + offDiagonalOuterCollisionEnergy B x := by
  rw [collisionEnergy_outerInputs_eq_sum_outerCollisionPairs B x hpos hlarge,
    offDiagonalOuterCollisionEnergy]
  have hsplit :
      ∑ m ∈ B x, ∑ m' ∈ B x, (outerCollisionPairs x m m').card =
        ∑ m ∈ B x,
          ((outerCollisionPairs x m m).card +
            ∑ m' ∈ (B x).erase m, (outerCollisionPairs x m m').card) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_erase_add _ _ hm]
    omega
  rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [outerInputs_card_eq_sum_outerPrimes_card B x hpos hlarge]
    apply Finset.sum_congr rfl
    intro m hm
    exact outerCollisionPairs_self_card_eq_outerPrimes_card
      (hpos m hm) (hlarge m hm)

end Erdos822
