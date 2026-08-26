import ErdosProblems.Erdos394.RationalBoundaryAggregation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global label states and their selected pair-lattice reductions
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- Extend the first coordinate of a subtype-indexed global label pair by zero
off the prime set. -/
def globalLabelFirst (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (n : ℕ) : ℕ :=
  if hn : n ∈ P then (f ⟨n, hn⟩).1 else 0

/-- Extend the second coordinate similarly. -/
def globalLabelSecond (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (n : ℕ) : ℕ :=
  if hn : n ∈ P then (f ⟨n, hn⟩).2 else 0

@[simp] theorem globalLabelFirst_at (P : Finset ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) {p : ℕ} (hp : p ∈ P) :
    globalLabelFirst P f p = (f ⟨p, hp⟩).1 := by
  simp [globalLabelFirst, hp]

@[simp] theorem globalLabelSecond_at (P : Finset ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) {p : ℕ} (hp : p ∈ P) :
    globalLabelSecond P f p = (f ⟨p, hp⟩).2 := by
  simp [globalLabelSecond, hp]

/-- Membership in the global label box gives both coordinate bounds. -/
theorem globalLabel_bounds {P : Finset ℕ} {K : ℕ}
    {f : ∀ _p : ↥P, ℕ × ℕ} (hf : f ∈ globalLabelPairs P K) :
    (∀ p ∈ P, globalLabelFirst P f p < K) ∧
    (∀ p ∈ P, globalLabelSecond P f p < K) := by
  constructor <;> intro p hp
  · have hlocal := Fintype.mem_piFinset.mp hf ⟨p, hp⟩
    simp only [allLabelPairs, Finset.mem_product, Finset.mem_range] at hlocal
    simpa [globalLabelFirst, hp] using hlocal.1
  · have hlocal := Fintype.mem_piFinset.mp hf ⟨p, hp⟩
    simp only [allLabelPairs, Finset.mem_product, Finset.mem_range] at hlocal
    simpa [globalLabelSecond, hp] using hlocal.2

/-- Both-zero primes of a global label state. -/
def pairStateZeroPrimes (P : Finset ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) : Finset ℕ :=
  bothZeroLabelPrimes P (globalLabelFirst P f) (globalLabelSecond P f)

/-- The origin-ignored pair lattice attached to a global label state: only its
both-zero primes are forced. -/
def pairStateLattice (P : Finset ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) : Submodule ℤ (Fin 2 → ℤ) :=
  globalForcedPairLattice P (pairStateZeroPrimes P f)
    (globalLabelFirst P f) (globalLabelSecond P f)
    (Finset.filter_subset _ _)

/-- A pair-state lattice has exact index `q q₀₀`. -/
theorem pairStateLattice_index
    (P : Finset ℕ) (K : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    Nat.card ((Fin 2 → ℤ) ⧸ pairStateLattice P f) =
      primeProduct P * primeProduct (pairStateZeroPrimes P f) := by
  let a := globalLabelFirst P f
  let b := globalLabelSecond P f
  have hbnd := globalLabel_bounds hf
  exact globalForcedPairLattice_index P (pairStateZeroPrimes P f) a b
    (Finset.filter_subset _ _) (by rfl) hprime hbnd.1 hbnd.2 hKp

/-- A pair-state lattice has a two-element integer basis. -/
noncomputable def pairStateLatticeBasis
    (P : Finset ℕ) (K : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    Basis (Fin 2) ℤ (pairStateLattice P f) := by
  let a := globalLabelFirst P f
  let b := globalLabelSecond P f
  have hbnd := globalLabel_bounds hf
  exact globalForcedPairLatticeBasis P (pairStateZeroPrimes P f) a b
    (Finset.filter_subset _ _) (by rfl) hprime hbnd.1 hbnd.2 hKp

/-- Embed a natural ordered pair as a two-coordinate integer vector. -/
def natPairIntVectorEmbedding : (ℕ × ℕ) ↪ (Fin 2 → ℤ) where
  toFun := fun jl ↦ ![(jl.1 : ℤ), (jl.2 : ℤ)]
  inj' := by
    intro x y hxy
    apply Prod.ext
    · have h0 := congrFun hxy 0
      change (x.1 : ℤ) = (y.1 : ℤ) at h0
      exact_mod_cast h0
    · have h1 := congrFun hxy 1
      change (x.2 : ℤ) = (y.2 : ℤ) at h1
      exact_mod_cast h1

/-- All positive integer vectors in the square `[1,Y]²`. -/
def positiveSquareIntVectors (Y : ℕ) : Finset (Fin 2 → ℤ) :=
  ((Icc 1 Y) ×ˢ (Icc 1 Y)).map natPairIntVectorEmbedding

/-- Positive square points of an arbitrary integral lattice. -/
noncomputable def latticePositiveSquare
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (Y : ℕ) : Finset Λ := by
  classical
  exact Finset.subtype (fun x : Fin 2 → ℤ ↦ x ∈ Λ)
    (positiveSquareIntVectors Y)

/-- Canonical (noncomputable) lattice-membership indicator. -/
noncomputable def latticeMembershipIndicator
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (x : Fin 2 → ℤ) : ℕ := by
  classical
  exact if x ∈ Λ then 1 else 0

/-- The positive-square lattice cardinality is the double sum of its
membership indicators. -/
theorem latticePositiveSquare_card_eq_sum_indicator
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (Y : ℕ) :
    (latticePositiveSquare Λ Y).card =
      ∑ j ∈ Icc 1 Y, ∑ l ∈ Icc 1 Y,
        latticeMembershipIndicator Λ ![(j : ℤ), (l : ℤ)] := by
  classical
  unfold latticePositiveSquare
  rw [Finset.card_subtype]
  unfold positiveSquareIntVectors
  rw [Finset.filter_map, Finset.card_map, Finset.card_filter,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rfl

/-- Every point of `latticePositiveSquare` has coordinates in `[0,Y]`. -/
theorem latticePositiveSquare_point_bounds
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (Y : ℕ)
    (x : Λ) (hx : x ∈ latticePositiveSquare Λ Y) (i : Fin 2) :
    0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ) := by
  have hxbox : (x : Fin 2 → ℤ) ∈ positiveSquareIntVectors Y := by
    simpa [latticePositiveSquare] using hx
  unfold positiveSquareIntVectors at hxbox
  rw [Finset.mem_map] at hxbox
  obtain ⟨jl, hjl, heq⟩ := hxbox
  have hj := Finset.mem_Icc.mp (Finset.mem_product.mp hjl).1
  have hl := Finset.mem_Icc.mp (Finset.mem_product.mp hjl).2
  have hvec : (x : Fin 2 → ℤ) = ![(jl.1 : ℤ), (jl.2 : ℤ)] := heq.symm
  fin_cases i
  · rw [hvec]
    change (0 : ℤ) ≤ (jl.1 : ℤ) ∧ (jl.1 : ℤ) ≤ (Y : ℤ)
    constructor
    · positivity
    · exact_mod_cast hj.2
  · rw [hvec]
    change (0 : ℤ) ≤ (jl.2 : ℤ) ∧ (jl.2 : ℤ) ≤ (Y : ℤ)
    constructor
    · positivity
    · exact_mod_cast hl.2

/-- Tracked lattice count specialized to every global pair-label state. -/
theorem pairState_positive_square_count_tracked
    (P : Finset ℕ) (K Y : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    ∃ c : Basis (Fin 2) ℤ (pairStateLattice P f), ∃ L : ℕ,
      L = intSupHeight2 (c 0 : Fin 2 → ℤ) ∧ 0 < L ∧
      L ≤ intSupHeight2 (c 1 : Fin 2 → ℤ) ∧
      (((((c 0 : Fin 2 → ℤ) 1).natAbs ≤
          ((c 0 : Fin 2 → ℤ) 0).natAbs ∧
          2 * ((c 1 : Fin 2 → ℤ) 0).natAbs ≤ L) ∨
       (((c 0 : Fin 2 → ℤ) 0).natAbs ≤
          ((c 0 : Fin 2 → ℤ) 1).natAbs ∧
          2 * ((c 1 : Fin 2 → ℤ) 1).natAbs ≤ L)) ∧
      ((latticePositiveSquare (pairStateLattice P f) Y).card : ℝ) ≤
        (Y : ℝ) ^ 2 /
          ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) +
          40 * ((Y : ℝ) / (L : ℝ)) + 4) := by
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hq0 : 0 < primeProduct (pairStateZeroPrimes P f) := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦
      (hprime p (Finset.mem_filter.mp hp).1).pos
  exact integral_lattice_square_count_tracked
    (pairStateLattice P f)
    (pairStateLatticeBasis P K f hf hprime hKp)
    (latticePositiveSquare (pairStateLattice P f) Y)
    (by positivity)
    (pairStateLattice_index P K f hf hprime hKp)
    (latticePositiveSquare_point_bounds (pairStateLattice P f) Y)

/-- The pieces of the tracked reduction used by the global moment sum. -/
structure PairStateCountData (P : Finset ℕ) (Y : ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) where
  basis : Basis (Fin 2) ℤ (pairStateLattice P f)
  height : ℕ
  height_eq : height = intSupHeight2 (basis 0 : Fin 2 → ℤ)
  height_pos : 0 < height
  count_le :
    ((latticePositiveSquare (pairStateLattice P f) Y).card : ℝ) ≤
      (Y : ℝ) ^ 2 /
        ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) +
        40 * ((Y : ℝ) / (height : ℝ)) + 4

/-- Package the existential tracked count into the data used below. -/
theorem exists_pairStateCountData
    (P : Finset ℕ) (K Y : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    Nonempty (PairStateCountData P Y f) := by
  obtain ⟨c, L, hL, hLpos, hmin, hred, hcount⟩ :=
    pairState_positive_square_count_tracked P K Y f hf hprime hKp
  exact ⟨⟨c, L, hL, hLpos, hcount⟩⟩

/-- A fixed noncomputable choice of reduced data for one valid state. -/
noncomputable def chosenPairStateCountData
    (P : Finset ℕ) (K Y : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    PairStateCountData P Y f :=
  Classical.choice (exists_pairStateCountData P K Y f hf hprime hKp)

end Erdos394
