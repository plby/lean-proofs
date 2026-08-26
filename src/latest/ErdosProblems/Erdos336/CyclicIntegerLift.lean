import Mathlib
import ErdosProblems.Erdos336.FiniteBogolyubov
import ErdosProblems.Erdos336.ReflectedBogolyubovBridge

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting short cyclic fourfold differences back to the integers
-/

namespace Erdos336

open Finset

/-- Reduction modulo `N` of a finite integer set. -/
def integerResidues (N : ℕ) (C : Finset ℤ) : Finset (ZMod N) :=
  C.image fun z : ℤ => (z : ZMod N)

/-- Reduction modulo `N` preserves cardinality for a set contained in
`[0,N)`. -/
theorem card_integerResidues_eq {N : ℕ} (C : Finset ℤ)
    (hC : ∀ z ∈ C, 0 ≤ z ∧ z < (N : ℤ)) :
    (integerResidues N C).card = C.card := by
  classical
  rw [integerResidues, Finset.card_image_iff]
  intro a ha b hb hab
  apply CharP.intCast_injOn_Ico (ZMod N) N
  · exact ⟨hC a ha |>.1, hC a ha |>.2⟩
  · exact ⟨hC b hb |>.1, hC b hb |>.2⟩
  · exact hab

/-- If the modulus is larger than the entire possible fourfold-difference
range, a modular representation by residues of `C⊂[0,L]` is an actual integer
representation. -/
theorem lift_short_fourfoldDifference
    {N : ℕ} [NeZero N] {C : Finset ℤ} {L R x : ℤ}
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hC : ∀ z ∈ C, 0 ≤ z ∧ z ≤ L)
    (hsize : R + 2 * L < (N : ℤ))
    (hxbound : |x| ≤ R)
    (hx : ZModInFourfoldDifference (integerResidues N C) (x : ZMod N)) :
    InFourfoldDifference (C : Set ℤ) x := by
  classical
  obtain ⟨az, haz, bz, hbz, cz, hcz, dz, hdz, heq⟩ := hx
  obtain ⟨a, haC, rfl⟩ := Finset.mem_image.mp haz
  obtain ⟨b, hbC, rfl⟩ := Finset.mem_image.mp hbz
  obtain ⟨c, hcC, rfl⟩ := Finset.mem_image.mp hcz
  obtain ⟨d, hdC, rfl⟩ := Finset.mem_image.mp hdz
  have hdvd : (N : ℤ) ∣ (a + b - c - d) - x := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub x (a + b - c - d) N).mp
      (by simpa using heq)
  have hab := abs_le.mp hxbound
  have ha := hC a haC
  have hb := hC b hbC
  have hc := hC c hcC
  have hd := hC d hdC
  have hrange : |(a + b - c - d) - x| < (N : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : (a + b - c - d) - x = 0 := by
    by_contra hne
    have hlower := Int.le_abs_of_dvd hne hdvd
    omega
  exact ⟨a, by simpa using haC, b, by simpa using hbC,
    c, by simpa using hcC, d, by simpa using hdC, by omega⟩

/-- Uniform local integer Bogolyubov. A dense finite set in `[0,L]`, embedded
in a modulus larger than its fourfold-difference range, has a local Bohr patch
of dimension at most `16q³` inside its genuine integer set `2C-2C`. -/
theorem local_integer_bogolyubov
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    {C : Finset ℤ} {L R : ℤ}
    (hCne : C.Nonempty) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hC : ∀ z ∈ C, 0 ≤ z ∧ z ≤ L)
    (hsize : R + 2 * L < (N : ℤ))
    (hdense : N ≤ q * C.card) :
    let A := integerResidues N C
    let Γ := cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))
    Γ.card ≤ 16 * q ^ 3 ∧
      ∀ x : ℤ, |x| ≤ R →
        (∀ k ∈ Γ,
          ‖ZMod.stdAddChar ((x : ZMod N) * k) - 1‖ ≤ (1 / 2 : ℝ)) →
        InFourfoldDifference (C : Set ℤ) x := by
  classical
  dsimp only
  have hClt : ∀ z ∈ C, 0 ≤ z ∧ z < (N : ℤ) := by
    intro z hz
    have hz' := hC z hz
    constructor
    · exact hz'.1
    · omega
  have hcard := card_integerResidues_eq C hClt
  have hAne : (integerResidues N C).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : (integerResidues N C).card = 0 := by simp [hempty]
    rw [hcard, Finset.card_eq_zero] at this
    exact hCne.ne_empty this
  have hdenseA : N ≤ q * (integerResidues N C).card := by
    simpa [hcard] using hdense
  let Γ := cyclicLargeSpectrum (integerResidues N C)
    (((integerResidues N C).card : ℝ) / (4 * q))
  have hcardΓ : Γ.card ≤ 16 * q ^ 3 := by
    obtain ⟨_, hc⟩ := finite_cyclic_bogolyubov_uniform q hq
      (integerResidues N C) hAne hdenseA (0 : ZMod N) (by
        intro k hk
        simp)
    simpa [Γ] using hc
  refine ⟨by simpa [Γ] using hcardΓ, ?_⟩
  intro x hxbound hclose
  have hmod :
      ZModInFourfoldDifference (integerResidues N C) (x : ZMod N) := by
    obtain ⟨hm, _⟩ := finite_cyclic_bogolyubov_uniform q hq
      (integerResidues N C) hAne hdenseA (x : ZMod N) (by
        intro k hk
        exact hclose k (by simpa [Γ] using hk))
    exact hm
  exact lift_short_fourfoldDifference hL hR hC hsize hxbound hmod

end Erdos336
