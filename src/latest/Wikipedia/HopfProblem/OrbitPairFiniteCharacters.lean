import Wikipedia.HopfProblem.OrbitPairFreeTrivializations

/-!
# Finite equivariant coordinates over compact parts of the free quotient

Finitely many of the constructed smooth characters suffice over any
compact subset of the actual free quotient. Their Hermitian pairing
will provide a continuous local transport between nearby circle fibres.
-/

noncomputable section

open Set Topology
open scoped BigOperators ComplexConjugate

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace unitCircleMulAction

theorem compact_free_quotient_finite_characters (K : Set freeOrbitLocus) (hK : IsCompact K) :
    ∃ s : Finset SmoothOrbitCharacter, ∀ x : freeLocus, freeOrbitProjection x ∈ K →
      ∃ F ∈ s, F x.val ≠ 0 := by
  classical
  have hcover : K ⊆ ⋃ F : SmoothOrbitCharacter, (F.freeBase : Set freeOrbitLocus) := by
    intro y _
    obtain ⟨x, rfl⟩ := freeOrbitProjection_surjective y
    obtain ⟨F, hF⟩ := exists_smoothOrbitCharacter x
    exact mem_iUnion.mpr ⟨F, (F.mem_freePreimage_iff x).mpr hF⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun F : SmoothOrbitCharacter => (F.freeBase : Set freeOrbitLocus))
    (fun F => F.freeBase.isOpen) hcover
  refine ⟨s, fun x hx => ?_⟩
  obtain ⟨F, hFs, hxF⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨F, hFs, (F.mem_freePreimage_iff x).mp hxF⟩

def characterPairing (s : Finset SmoothOrbitCharacter) (x y : Threefold.Space) : ℂ :=
  ∑ F ∈ s, F x * conj (F y)

def characterEnergy (s : Finset SmoothOrbitCharacter) (x : Threefold.Space) : ℝ :=
  ∑ F ∈ s, Complex.normSq (F x)

theorem characterPairing_self (s : Finset SmoothOrbitCharacter) (x : Threefold.Space) :
    characterPairing s x x = (characterEnergy s x : ℂ) := by
  simp [characterPairing, characterEnergy, Complex.mul_conj]

theorem characterEnergy_nonneg (s : Finset SmoothOrbitCharacter) (x : Threefold.Space) :
    0 ≤ characterEnergy s x := Finset.sum_nonneg (fun F _ => Complex.normSq_nonneg (F x))

theorem characterEnergy_pos_iff (s : Finset SmoothOrbitCharacter) (x : Threefold.Space) :
    0 < characterEnergy s x ↔ ∃ F ∈ s, F x ≠ 0 := by
  rw [characterEnergy, Finset.sum_pos_iff_of_nonneg (fun F _ => Complex.normSq_nonneg (F x))]
  simp only [Complex.normSq_pos]

theorem characterPairing_continuous (s : Finset SmoothOrbitCharacter) :
    Continuous (fun p : Threefold.Space × Threefold.Space => characterPairing s p.1 p.2) := by
  apply continuous_finset_sum
  intro F _
  exact (F.smooth.continuous.comp continuous_fst).mul
    (Complex.continuous_conj.comp (F.smooth.continuous.comp continuous_snd))

theorem characterEnergy_continuous (s : Finset SmoothOrbitCharacter) :
    Continuous (characterEnergy s) := by
  apply continuous_finset_sum
  intro F _
  exact Complex.continuous_normSq.comp F.smooth.continuous

theorem characterPairing_equivariant (s : Finset SmoothOrbitCharacter)
    (u v : Circle) (x y : Threefold.Space) :
    characterPairing s (u • x) (v • y) = (u : ℂ) * conj (v : ℂ) * characterPairing s x y := by
  simp only [characterPairing, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [F.equivariant, F.equivariant, map_mul]
  ring

theorem characterEnergy_invariant (s : Finset SmoothOrbitCharacter) (u : Circle)
    (x : Threefold.Space) : characterEnergy s (u • x) = characterEnergy s x := by
  simp only [characterEnergy]
  apply Finset.sum_congr rfl
  intro F _
  rw [F.equivariant, Complex.normSq_mul, Circle.normSq_coe, one_mul]

def finiteCharacterDomain (s : Finset SmoothOrbitCharacter) : TopologicalSpace.Opens Threefold.Space :=
  ⟨{x | 0 < characterEnergy s x}, isOpen_lt continuous_const (characterEnergy_continuous s)⟩

theorem finiteCharacterDomain_subset_freeLocus (s : Finset SmoothOrbitCharacter) :
    (finiteCharacterDomain s : Set Threefold.Space) ⊆ freeLocus := by
  intro x hx
  obtain ⟨F, _, hF⟩ := (characterEnergy_pos_iff s x).mp hx
  exact F.nonzeroSet_subset_freeLocus hF

theorem finiteCharacterDomain_invariant (s : Finset SmoothOrbitCharacter)
    (u : Circle) (x : Threefold.Space) : u • x ∈ finiteCharacterDomain s ↔ x ∈ finiteCharacterDomain s := by
  change 0 < characterEnergy s (u • x) ↔ 0 < characterEnergy s x
  rw [characterEnergy_invariant]

end Wikipedia.HopfProblem.OrbitPair
