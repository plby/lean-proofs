/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base

/-!
# Combining disjoint fibrewise residue distributions

Each prime has a unique cofactor owner. Pushforward under multiplication
by that owner gives one global prime-indexed probability distribution.
Its coverage dominates the coverage from any single cofactor fibre.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourcePrimeOwner (E : Finset ℕ) (Q : ℕ → Finset ℕ) (q : E.biUnion Q) : ℕ :=
  Classical.choose (Finset.mem_biUnion.mp q.property)

theorem sourcePrimeOwner_spec (E : Finset ℕ) (Q : ℕ → Finset ℕ) (q : E.biUnion Q) :
    sourcePrimeOwner E Q q ∈ E ∧ q.val ∈ Q (sourcePrimeOwner E Q q) :=
  Classical.choose_spec (Finset.mem_biUnion.mp q.property)

theorem sourcePrimeOwner_eq {E : Finset ℕ} {Q : ℕ → Finset ℕ}
    (hdisjoint : ∀ m ∈ E, ∀ n ∈ E, m ≠ n → Disjoint (Q m) (Q n))
    (q : E.biUnion Q) {m : ℕ} (hm : m ∈ E) (hqm : q.val ∈ Q m) :
    sourcePrimeOwner E Q q = m := by
  have hs := sourcePrimeOwner_spec E Q q
  by_contra hn
  exact Finset.disjoint_left.mp (hdisjoint _ hs.1 m hm hn) hs.2 hqm

def sourceCombinedResidueWeight (E : Finset ℕ) (Q : ℕ → Finset ℕ)
    (μ : ∀ _m q : ℕ, Fin q → ℝ) (q : E.biUnion Q) (b : Fin q.val) : ℝ :=
  pushResidueMass (sourcePrimeOwner E Q q) q.val (μ (sourcePrimeOwner E Q q) q.val) b

theorem sourceCombinedResidueWeight_nonneg {E : Finset ℕ} {Q : ℕ → Finset ℕ}
    {μ : ∀ _m q : ℕ, Fin q → ℝ}
    (hμ : ∀ m ∈ E, ∀ q ∈ Q m, ∀ b, 0 ≤ μ m q b)
    (q : E.biUnion Q) (b : Fin q.val) :
    0 ≤ sourceCombinedResidueWeight E Q μ q b := by
  have hs := sourcePrimeOwner_spec E Q q
  exact pushResidueMass_nonneg (hμ _ hs.1 _ hs.2) b

theorem sum_sourceCombinedResidueWeight {E : Finset ℕ} {Q : ℕ → Finset ℕ}
    {μ : ∀ _m q : ℕ, Fin q → ℝ}
    (hq : ∀ m ∈ E, ∀ q ∈ Q m, 0 < q)
    (hsum : ∀ m ∈ E, ∀ q ∈ Q m, ∑ b, μ m q b = 1) (q : E.biUnion Q) :
    ∑ b, sourceCombinedResidueWeight E Q μ q b = 1 := by
  have hs := sourcePrimeOwner_spec E Q q
  unfold sourceCombinedResidueWeight
  rw [sum_pushResidueMass (hq _ hs.1 _ hs.2)]
  exact hsum _ hs.1 _ hs.2

theorem normalized_sourceCombinedResidueWeight_eq {E : Finset ℕ} {Q : ℕ → Finset ℕ}
    {μ : ∀ _m q : ℕ, Fin q → ℝ}
    (hq : ∀ m ∈ E, ∀ q ∈ Q m, 0 < q)
    (hsum : ∀ m ∈ E, ∀ q ∈ Q m, ∑ b, μ m q b = 1)
    (q : E.biUnion Q) (b : Fin q.val) :
    normalizedRawMass (sourceCombinedResidueWeight E Q μ) q b =
      sourceCombinedResidueWeight E Q μ q b := by
  unfold normalizedRawMass normalizeFiniteWeight
  rw [sum_sourceCombinedResidueWeight hq hsum q, div_one]

theorem sum_residue_hit_eq {q : ℕ} (hq : 0 < q) (μ : Fin q → ℝ) (i : ℕ) :
    (∑ b : Fin q, if i % q = b.val then μ b else 0) = μ ⟨i % q, Nat.mod_lt i hq⟩ := by
  classical
  let b₀ : Fin q := ⟨i % q, Nat.mod_lt i hq⟩
  rw [Finset.sum_eq_single b₀]
  · simp only [b₀, if_true]
  · intro b _ hne
    have hn : i % q ≠ b.val := fun h ↦ hne (Fin.ext h.symm)
    exact if_neg hn
  · simp

theorem sum_le_sum_injective_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hinj : Function.Injective f) (g : κ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image f, g j := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij ↦ hinj hij
    _ ≤ ∑ j, g j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ ↦ hg j)

theorem sourceFamilyCoverage_ge_fibre {E : Finset ℕ} {Q : ℕ → Finset ℕ}
    {μ : ∀ _m q : ℕ, Fin q → ℝ}
    (hdisjoint : ∀ m ∈ E, ∀ n ∈ E, m ≠ n → Disjoint (Q m) (Q n))
    (hq : ∀ m ∈ E, ∀ q ∈ Q m, 0 < q)
    (hμ : ∀ m ∈ E, ∀ q ∈ Q m, ∀ b, 0 ≤ μ m q b)
    (hsum : ∀ m ∈ E, ∀ q ∈ Q m, ∑ b, μ m q b = 1)
    {m : ℕ} (hm : m ∈ E) (p : ℕ) :
    (∑ q : Q m, μ m q.val ⟨p % q.val, Nat.mod_lt p (hq m hm q.val q.property)⟩) ≤
      ∑ q : E.biUnion Q, ∑ b : Fin q.val, if (m * p) % q.val = b.val then
        normalizedRawMass (sourceCombinedResidueWeight E Q μ) q b else 0 := by
  classical
  let f : Q m → E.biUnion Q := fun q ↦ ⟨q.val, Finset.mem_biUnion.mpr ⟨m, hm, q.property⟩⟩
  let g : E.biUnion Q → ℝ := fun q ↦ ∑ b : Fin q.val, if (m * p) % q.val = b.val then
    normalizedRawMass (sourceCombinedResidueWeight E Q μ) q b else 0
  have hf : Function.Injective f := by
    intro q q' heq
    exact Subtype.ext (congrArg (fun x : E.biUnion Q ↦ x.val) heq)
  have hg : ∀ q, 0 ≤ g q := by
    intro q
    exact Finset.sum_nonneg fun b _ ↦ by
      split_ifs
      · exact normalizedRawMass_nonneg _ (sourceCombinedResidueWeight_nonneg hμ) q b
      · exact le_rfl
  have hpoint : ∀ q : Q m,
      μ m q.val ⟨p % q.val, Nat.mod_lt p (hq m hm q.val q.property)⟩ ≤ g (f q) := by
    intro q
    dsimp only [g]
    rw [sum_residue_hit_eq (hq m hm q.val q.property)]
    rw [normalized_sourceCombinedResidueWeight_eq hq hsum]
    unfold sourceCombinedResidueWeight
    rw [sourcePrimeOwner_eq hdisjoint (f q) hm q.property]
    exact residueMass_le_pushResidueMass_hit (hq m hm q.val q.property) (μ m q.val)
      (hμ m hm q.val q.property)
  exact (Finset.sum_le_sum fun q _ ↦ hpoint q).trans (sum_le_sum_injective_nonneg f hf g hg)

end

end Erdos4b
