/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedCrt

/-!
# Local characterization of the extra pinned congruence

When the forced prime belongs to the finite prime cutoff, compatibility
is the unforced graph condition together with the literal affine
equations at the prescribed residue. This includes the empty local state.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def PinnedForcedLocalEquations {K : ℕ} (h : Fin K) (w m p₀ p a : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : Prop :=
  (∀ i, p ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true) →
    (p₀ : ZMod p) + pinnedIndexSlope h w p i * (a : ZMod p) = 0) ∧
  (∀ i, p ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true) →
    (m : ZMod p) * ((p₀ : ZMod p) + pinnedIndexSlope h w p i * (a : ZMod p)) = 1)

theorem pinnedForcedIntegerSolvable_iff_graph_and_local
    {K w m p₀ Y p a : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hrough : ∀ r ∈ P, w < r) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpP : p ∈ P)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ r ∈ P, r)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y) :
    PinnedForcedIntegerSolvable h w m p₀ p a d ↔
      (d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P ∧
        DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
          (truncatedPinnedFourierCompanion m Y) d) ∧
      PinnedForcedLocalEquations h w m p₀ p a d := by
  classical
  constructor
  · rintro ⟨q, hq, hqa⟩
    refine ⟨pinnedIntegerDivisorCondition_implies_cutoff_graph h P hP hrough hKw
      hm hp₀ hcop d hdiv hDsmall hEsmall hq, ?_⟩
    have heqs := ((pinnedDivisorPrimeEquations_iff_integer_divisibility h P hP d hdiv).mpr hq)
      ⟨p, hpP⟩
    have hcast := (ZMod.natCast_eq_natCast_iff q a p).mpr hqa
    simpa only [PinnedForcedLocalEquations, hcast] using heqs
  · rintro ⟨hg, hforced⟩
    have hsol := (doubledDivisorPrimeCompatible_iff_pinnedLocalSolvable h P hP hrough hKw
      hm hp₀ hcop d hg.1 hDsmall hEsmall).mp hg.2
    choose z hz0 hzD hzE using hsol
    let residue (r : P) : ℕ := if r.val = p then a else (z r).val
    have hpair : Set.Pairwise (Finset.univ : Finset P)
        (fun r s : P ↦ r.val.Coprime s.val) := by
      intro r hr s hs hne
      exact (Nat.coprime_primes (hP r r.property) (hP s s.property)).mpr
        (fun heq ↦ hne (Subtype.ext heq))
    let crt := Nat.chineseRemainderOfFinset residue (fun r : P ↦ r.val) Finset.univ
      (fun r hr ↦ (hP r r.property).ne_zero) hpair
    let q : ℕ := crt.val
    have hqa : q ≡ a [MOD p] := by
      simpa only [residue, if_pos rfl] using crt.property ⟨p, hpP⟩ (Finset.mem_univ _)
    have heqs : PinnedDivisorPrimeEquations h P w m p₀ q d := by
      intro r
      by_cases heq : r.val = p
      · have hr : r = ⟨p, hpP⟩ := Subtype.ext heq
        subst r
        have hcast := (ZMod.natCast_eq_natCast_iff q a p).mpr hqa
        simpa only [PinnedForcedLocalEquations, hcast] using hforced
      · have hqr : q ≡ (z r).val [MOD r.val] := by
          simpa only [residue, if_neg heq] using crt.property r (Finset.mem_univ _)
        let : NeZero r.val := ⟨(hP r r.property).ne_zero⟩
        have hcast : (q : ZMod r.val) = z r :=
          ((ZMod.natCast_eq_natCast_iff q (z r).val r.val).mpr hqr).trans
            (ZMod.natCast_zmod_val _)
        constructor
        · intro i hi
          rw [hcast]
          exact hzD r i hi
        · intro i hi
          rw [hcast]
          exact hzE r i hi
    exact ⟨q, (pinnedDivisorPrimeEquations_iff_integer_divisibility h P hP d hdiv).mp heqs, hqa⟩

end

end Erdos4b
