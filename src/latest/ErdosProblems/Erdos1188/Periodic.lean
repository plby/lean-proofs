import ErdosProblems.Erdos1188.Basic

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos1188

/-- Exact finite-period coverage test used by the independent checker. -/
def CoversResidues (N : ℕ) (S : Finset CongruenceClass) : Prop :=
  ∀ r : Fin N, ∃ c ∈ S, Satisfies (r.val : ℤ) c

/-- The canonical residue in `Fin N` of an integer, for positive `N`. -/
def intResidueFin (z : ℤ) (N : ℕ) (hN : N ≠ 0) : Fin N :=
  ⟨z.natMod (N : ℤ), Int.natMod_lt hN⟩

/-- Reducing an integer first modulo a common multiple `N` does not change
membership in a class whose modulus divides `N`. -/
theorem satisfies_intResidueFin_iff {N : ℕ} (hN : 0 < N) (z : ℤ)
    (c : CongruenceClass) (hdvd : c.1 ∣ N) :
    Satisfies ((intResidueFin z N (Nat.ne_of_gt hN)).val : ℤ) c ↔ Satisfies z c := by
  unfold Satisfies
  have hval : ((intResidueFin z N (Nat.ne_of_gt hN)).val : ℤ) = z % (N : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast (Nat.ne_of_gt hN)))
  rw [hval]
  have hdvdZ : (c.1 : ℤ) ∣ (N : ℤ) := by exact_mod_cast hdvd
  have heq : z % (N : ℤ) % (c.1 : ℤ) = z % (c.1 : ℤ) := by
    apply Int.ModEq.eq
    exact Int.ModEq.of_dvd hdvdZ (Int.mod_modEq z (N : ℤ))
  rw [heq]

/-- If every modulus divides a positive `N`, checking all residues modulo `N`
is exactly equivalent to checking every integer. -/
theorem covers_iff_coversResidues {N : ℕ} (hN : 0 < N)
    (S : Finset CongruenceClass) (hdiv : ∀ c ∈ S, c.1 ∣ N) :
    Covers S ↔ CoversResidues N S := by
  constructor
  · intro h r
    exact h (r.val : ℤ)
  · intro h z
    obtain ⟨c, hcS, hc⟩ := h (intResidueFin z N (Nat.ne_of_gt hN))
    exact ⟨c, hcS, (satisfies_intResidueFin_iff hN z c (hdiv c hcS)).mp hc⟩

end Erdos1188
