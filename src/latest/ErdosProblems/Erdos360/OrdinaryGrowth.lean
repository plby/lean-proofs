import ErdosProblems.Erdos360.OrdinaryBridge

open scoped BigOperators Pointwise

namespace Erdos360

/-!
This file packages the ordinary-integer half of CFP Lemma 5.6.  The
modular phase machine supplies a uniform lower bound for the residues of
the seed subset-sum set modulo every pivot.  CFP Lemma 2.5 then turns each
such residue into a genuinely new ordinary subset sum as the pivots are
adjoined.  Diversity gives the aperiodicity conclusion needed by the
subsequent Lev sumset argument.
-/

/-- Direct modular-to-ordinary bridge, with the aperiodicity conclusion
used in CFP Lemma 5.6.  This form is independent of the particular modular
growth engine: every pivot contributes `q` new ordinary subset sums. -/
theorem ordinary_subsetSum_growth_and_aperiodic
    {A B : Finset ℕ} {q k : ℕ}
    (hAB : Disjoint A B)
    (hpos : ∀ t ∈ B, 0 < t)
    (hres : ∀ t ∈ B,
      q ≤ (occupiedResidues A.subsetSum t).card)
    (hk : 0 < k) (hdiverse : Diverse (A ∪ B) k) :
    A.subsetSum.card + B.card * q ≤ (A ∪ B).subsetSum.card ∧
      ¬ ContainedInNontrivialAP (A ∪ B).subsetSum := by
  constructor
  · have hgrowth := subsetSum_card_add_sum_le_union hAB (fun _ => q)
      hpos hres
    simpa [mul_comm] using hgrowth
  · exact subsetSum_not_containedInNontrivialAP_of_diverse hk hdiverse

/-- Target-sized form of `ordinary_subsetSum_growth_and_aperiodic`.  In the
CFP application `target = yz/(ℓ²v)`; the elementary parameter arithmetic is
isolated in `target ≤ |B|q`. -/
theorem large_ordinary_subsetSum_of_modular_residues
    {A B : Finset ℕ} {q k target : ℕ}
    (hAB : Disjoint A B)
    (hpos : ∀ t ∈ B, 0 < t)
    (hres : ∀ t ∈ B,
      q ≤ (occupiedResidues A.subsetSum t).card)
    (htarget : target ≤ B.card * q)
    (hk : 0 < k) (hdiverse : Diverse (A ∪ B) k) :
    target ≤ (A ∪ B).subsetSum.card ∧
      ¬ ContainedInNontrivialAP (A ∪ B).subsetSum := by
  obtain ⟨hgrowth, haper⟩ := ordinary_subsetSum_growth_and_aperiodic
    hAB hpos hres hk hdiverse
  exact ⟨htarget.trans (by omega), haper⟩

/-- Division-free quantitative form matching the scale in CFP Lemma 5.6.
If the pivot half has at least `z/(16ℓ)` elements and every pivot produces
at least `16y/(ℓv)` residues (both inequalities are written without
rounding-sensitive division), then the ordinary subset-sum set has size at
least `yz/(ℓ²v)`. -/
theorem cfp_large_ordinary_subsetSum_division_free
    {A B : Finset ℕ} {q k y z ℓ v : ℕ}
    (hAB : Disjoint A B)
    (hpos : ∀ t ∈ B, 0 < t)
    (hres : ∀ t ∈ B,
      q ≤ (occupiedResidues A.subsetSum t).card)
    (hz : z ≤ 16 * ℓ * B.card)
    (hy : 16 * y ≤ ℓ * v * q)
    (hk : 0 < k) (hdiverse : Diverse (A ∪ B) k) :
    y * z ≤ ℓ ^ 2 * v * (A ∪ B).subsetSum.card ∧
      ¬ ContainedInNontrivialAP (A ∪ B).subsetSum := by
  obtain ⟨hgrowth, haper⟩ := ordinary_subsetSum_growth_and_aperiodic
    hAB hpos hres hk hdiverse
  have hpivot : B.card * q ≤ (A ∪ B).subsetSum.card := by omega
  have hmul : (16 * y) * z ≤ (ℓ * v * q) * (16 * ℓ * B.card) :=
    Nat.mul_le_mul hy hz
  have hscale : y * z ≤ ℓ ^ 2 * v * (B.card * q) := by
    nlinarith
  exact ⟨hscale.trans (Nat.mul_le_mul_left (ℓ ^ 2 * v) hpivot), haper⟩

/-- CFP Lemma 5.6 in the parameterization produced by the deterministic
modular phase machine.  The interval hypothesis makes reduction modulo a
pivot injective on the seed.  The two alternatives of the modular theorem
both yield at least `q` occupied residues: either a quarter of the cyclic
group is filled (`64 q ≤ t`), or the quadratic-growth alternative applies
(`64 q ≤ k |A|`). -/
theorem ordinary_subsetSum_growth_of_modular_phases
    {lo hi phaseCount q diversity : ℕ} {A B : Finset ℕ}
    (hlo : 0 < lo) (hwidth : hi - lo ≤ lo)
    (hA : A ⊆ Finset.Ico lo hi) (hB : B ⊆ Finset.Ico lo hi)
    (hAB : Disjoint A B)
    (hphase : ∀ (t : ℕ) (ht : t ∈ B),
      @PhaseDiverse t ⟨by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega⟩ (by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega) (A.image fun a : ℕ => (a : ZMod t)))
    (hlog : ∀ t ∈ B, 4 * (Nat.log 2 t + 1) ^ 2 ≤ phaseCount)
    (hhalf : 2 * phaseCount ≤ A.card)
    (hqmod : ∀ t ∈ B, 64 * q ≤ t)
    (hqquad : 64 * q ≤ phaseCount * A.card)
    (hdiversity : 0 < diversity)
    (hdiverse : Diverse (A ∪ B) diversity) :
    A.subsetSum.card + B.card * q ≤ (A ∪ B).subsetSum.card ∧
      ¬ ContainedInNontrivialAP (A ∪ B).subsetSum := by
  constructor
  · exact subsetSum_card_add_pivot_growth hlo hwidth hA hB hAB hphase
      hlog hhalf hqmod hqquad
  · exact subsetSum_not_containedInNontrivialAP_of_diverse
      hdiversity hdiverse

/-- A convenient seed-free numerical corollary of the ordinary-growth
bridge. -/
theorem mul_le_subsetSum_card_of_modular_phases
    {lo hi phaseCount q : ℕ} {A B : Finset ℕ}
    (hlo : 0 < lo) (hwidth : hi - lo ≤ lo)
    (hA : A ⊆ Finset.Ico lo hi) (hB : B ⊆ Finset.Ico lo hi)
    (hAB : Disjoint A B)
    (hphase : ∀ (t : ℕ) (ht : t ∈ B),
      @PhaseDiverse t ⟨by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega⟩ (by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega) (A.image fun a : ℕ => (a : ZMod t)))
    (hlog : ∀ t ∈ B, 4 * (Nat.log 2 t + 1) ^ 2 ≤ phaseCount)
    (hhalf : 2 * phaseCount ≤ A.card)
    (hqmod : ∀ t ∈ B, 64 * q ≤ t)
    (hqquad : 64 * q ≤ phaseCount * A.card) :
    B.card * q ≤ (A ∪ B).subsetSum.card := by
  have h := subsetSum_card_add_pivot_growth hlo hwidth hA hB hAB hphase
    hlog hhalf hqmod hqquad
  omega

end Erdos360
