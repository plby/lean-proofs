import Wikipedia.NoExoticSixSphere.FamilyDoublePointCompactness

/-!
# Actual singular parameters correspond bijectively to diagonal orbits

The generic local chart puts every singular parameter on the double-point
closure diagonal. Conversely diagonal accumulation forces a singular spatial
derivative. Swapping fixes these pairs, so passage to the genuine quotient
neither identifies distinct singular parameters nor duplicates them.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization OperatorRank

variable (f : ℝ → Vector 3 → Vector 6) (hf : ContDiff ℝ ∞ (uncurry f))
  (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))

include hf hreg

theorem singular_diagonal_mem_closure (p : ℝ × Vector 3)
    (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    (p.1, (p.2, p.2)) ∈ closure (doublePoints f) := by
  obtain ⟨hc, _⟩ := exists_unordered_closed_curve_chart f hf hreg p hp
  exact hc

def singularOrbit (p : {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)}) :
    diagonalOrbits f :=
  ⟨unorderedProj f ⟨(p.val.1, (p.val.2, p.val.2)),
    singular_diagonal_mem_closure f hf hreg p.val p.property⟩,
    (mem_diagonalOrbits_iff f _).mpr rfl⟩

theorem injective_singularOrbit : Injective (singularOrbit f hf hreg) := by
  intro p q he
  have heq := congrArg Subtype.val he
  rcases (unorderedProj_eq_iff f _ _).mp heq with heq | heq
  · exact Subtype.ext (congrArg (fun r : ℝ × (Vector 3 × Vector 3) ↦ (r.1, r.2.1)) heq)
  · exact Subtype.ext (congrArg (fun r : ℝ × (Vector 3 × Vector 3) ↦ (r.1, r.2.1)) heq)

theorem surjective_singularOrbit : Surjective (singularOrbit f hf hreg) := by
  rintro ⟨q, hq⟩
  obtain ⟨r, hrdiag, rfl⟩ := hq
  rcases r with ⟨⟨t, x, y⟩, hcl⟩
  change x = y at hrdiag
  subst y
  have hsing : ¬ Injective (fderiv ℝ (f t) x) := by
    intro hi
    exact diagonal_not_mem_closure_doublePoints f hf t x hi hcl
  exact ⟨⟨(t, x), hsing⟩, rfl⟩

def singularBoundaryEquiv :
    {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)} ≃ diagonalOrbits f :=
  Equiv.ofBijective (singularOrbit f hf hreg)
    ⟨injective_singularOrbit f hf hreg, surjective_singularOrbit f hf hreg⟩

theorem singularBoundary_card :
    Nat.card {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)} =
      Nat.card (diagonalOrbits f) := Nat.card_congr (singularBoundaryEquiv f hf hreg)

end NoExoticSixSphere.FamilyEmbedding
