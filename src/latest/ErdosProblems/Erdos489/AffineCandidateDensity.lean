import ErdosProblems.Erdos489.AffineSieveDensity
import ErdosProblems.Erdos489.PeriodicIntervalDensity

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Integers in the residue class `1 mod Q` which avoid a finite list of
moduli. -/
def affineCandidates (l : List ℕ) (Q : ℕ) (n : ℕ) : Prop :=
  Nat.ModEq Q n 1 ∧ ∀ a ∈ l, ¬a ∣ n

noncomputable instance affineCandidates_decidable (l : List ℕ) (Q : ℕ) :
    DecidablePred (affineCandidates l Q) := Classical.decPred _

/-- The affine candidate predicate has period `Q * ∏l`. -/
theorem affineCandidates_periodic (l : List ℕ) (Q : ℕ) :
    Function.Periodic (affineCandidates l Q) (Q * l.prod) := by
  intro n
  apply propext
  constructor
  · rintro ⟨hmod, hav⟩
    constructor
    · simpa [Nat.ModEq, Nat.add_mod] using hmod
    · intro a ha hadiv
      apply hav a ha
      have haP : a ∣ Q * l.prod := dvd_mul_of_dvd_right (List.dvd_prod ha) Q
      exact (Nat.dvd_add_iff_left haP).1 hadiv
  · rintro ⟨hmod, hav⟩
    constructor
    · simpa [Nat.ModEq, Nat.add_mod] using hmod
    · intro a ha hadiv
      apply hav a ha
      have haP : a ∣ Q * l.prod := dvd_mul_of_dvd_right (List.dvd_prod ha) Q
      exact (Nat.dvd_add_iff_left haP).2 hadiv

/-- One affine parameter `k` gives one candidate integer `Qk+1` in the full
period. -/
theorem affineAvoidCount_le_candidate_period_count
    (l : List ℕ) (Q : ℕ) (hQ : 1 < Q) :
    affineAvoidCount l Q l.prod ≤
      ((Finset.range (Q * l.prod)).filter (affineCandidates l Q)).card := by
  let A : Finset ℕ :=
    (Finset.range l.prod).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1
  let C : Finset ℕ :=
    (Finset.range (Q * l.prod)).filter (affineCandidates l Q)
  let F : ℕ → ℕ := fun k => Q * k + 1
  have hmap : Set.MapsTo F (A : Set ℕ) (C : Set ℕ) := by
    intro k hk
    have hkA : k ∈ A := hk
    have hkr : k < l.prod := Finset.mem_range.mp (Finset.mem_filter.mp hkA).1
    have hkav := (Finset.mem_filter.mp hkA).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨?_, hkav⟩⟩
    · dsimp [F]
      have hQ0 : 0 < Q := by omega
      have hle : k + 1 ≤ l.prod := by omega
      have hmul := Nat.mul_le_mul_left Q hle
      nlinarith
    · dsimp [F]
      simp [Nat.ModEq]
  have hinj : Set.InjOn F (A : Set ℕ) := by
    intro x hx y hy hxy
    dsimp [F] at hxy
    have : Q * x = Q * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hcard := Finset.card_le_card_of_injOn F hmap hinj
  simpa [affineAvoidCount, A, C] using hcard

/-- Product-density lower bound for affine candidates in one full period. -/
theorem affineCandidates_period_count_lower
    (l : List ℕ) (Q : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (l.map fun a => a - 1).prod ≤
      ((Finset.range (Q * l.prod)).filter (affineCandidates l Q)).card := by
  exact (affine_heilbronn_rohrbach_count l Q hl hcop).trans
    (affineAvoidCount_le_candidate_period_count l Q hQ)

/-- Uniform product-density supply in every interval. -/
theorem affineCandidates_interval_count_lower
    (l : List ℕ) (Q L G : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (G / (Q * l.prod) - 2) * (l.map fun a => a - 1).prod ≤
      ((Finset.Icc L (L + G)).filter (affineCandidates l Q)).card := by
  have hperiod := periodic_interval_count_lower (affineCandidates l Q)
    (Q * l.prod) L G (Nat.mul_pos (by omega) (List.prod_pos
      (fun a ha => (hl a ha).trans' Nat.zero_lt_one)))
    (affineCandidates_periodic l Q)
  have hone := affineCandidates_period_count_lower l Q hQ hl hcop
  exact (Nat.mul_le_mul_left (G / (Q * l.prod) - 2) hone).trans hperiod

end Erdos489
