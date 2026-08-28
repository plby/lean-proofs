import Wikipedia.NoExoticSixSphere.OrthogonalExponentialSubdivision

/-!
# Finite exponential factors and genuine homotopies

Scaling finitely many continuous skew-adjoint factors supplies a homotopy
relative to any parameter set where they vanish. On a compact base, a homotopy
from the identity also supplies such a finite factorization by uniform local
logarithms. Existence of a factorization is not asserted for arbitrary maps.
-/

open unitInterval

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def productMap (N : ℕ) (K : ℕ → C(X, SkewOperators n)) :
    C(X, OrthogonalOperators n) where
  toFun x := ((List.range N).map (fun i ↦ exp (K i x))).prod
  continuous_toFun := continuous_list_prod (List.range N)
    (fun i _ ↦ contMDiff_exp.continuous.comp (K i).continuous)

/-- Scale all factors simultaneously; the product order is kept fixed. -/
noncomputable def productHomotopy (N : ℕ) (K : ℕ → C(X, SkewOperators n)) :
    (ContinuousMap.const X (1 : OrthogonalOperators n)).Homotopy (productMap N K) where
  toFun p := ((List.range N).map (fun i ↦ exp ((p.1 : ℝ) • K i p.2))).prod
  continuous_toFun := continuous_list_prod (List.range N) (fun i _ ↦
    contMDiff_exp.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).smul ((K i).continuous.comp continuous_snd)))
  map_zero_left x := by
    change ((List.range N).map (fun i ↦ exp ((0 : ℝ) • K i x))).prod = 1
    simp [exp_zero]
  map_one_left x := by
    change ((List.range N).map (fun i ↦ exp ((1 : ℝ) • K i x))).prod = _
    simp only [one_smul]
    rfl

noncomputable def productHomotopyRel (N : ℕ) (K : ℕ → C(X, SkewOperators n))
    (S : Set X) (hz : ∀ x ∈ S, ∀ i < N, K i x = 0) :
    (ContinuousMap.const X (1 : OrthogonalOperators n)).HomotopyRel (productMap N K) S where
  toHomotopy := productHomotopy N K
  prop' t x hx := by
    change ((List.range N).map (fun i ↦ exp ((t : ℝ) • K i x))).prod = 1
    apply List.prod_eq_one
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [hz x hx i (List.mem_range.mp hi), smul_zero, exp_zero]

/-- On compact bases, the finite factorization criterion is equivalent to an actual homotopy. -/
theorem homotopic_const_iff_exponentialFactorization [CompactSpace X]
    (a : C(X, OrthogonalOperators n)) :
    (ContinuousMap.const X (1 : OrthogonalOperators n)).Homotopic a ↔
      ∃ N : ℕ, ∃ K : ℕ → C(X, SkewOperators n), a = productMap N K := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨N, K, hend, _, _⟩ := exists_exponentialFactorization H.toContinuousMap
    refine ⟨N, K, ?_⟩
    apply ContinuousMap.ext
    intro x
    have h := hend x
    change H (1, x) = H (0, x) * _ at h
    rw [H.apply_one, H.apply_zero] at h
    change a x = (1 : OrthogonalOperators n) * productMap N K x at h
    simpa only [one_mul] using h
  · rintro ⟨N, K, rfl⟩
    exact ⟨productHomotopy N K⟩

/-- The factorization criterion also preserves the exact relative parameter set. -/
theorem homotopicRel_const_iff_exponentialFactorization [CompactSpace X]
    (a : C(X, OrthogonalOperators n)) (S : Set X) :
    Nonempty ((ContinuousMap.const X (1 : OrthogonalOperators n)).HomotopyRel a S) ↔
      ∃ N : ℕ, ∃ K : ℕ → C(X, SkewOperators n),
        a = productMap N K ∧ ∀ x ∈ S, ∀ i < N, K i x = 0 := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨N, K, hend, _, hstationary⟩ :=
      exists_exponentialFactorization H.toHomotopy.toContinuousMap
    refine ⟨N, K, ?_, ?_⟩
    · apply ContinuousMap.ext
      intro x
      have h := hend x
      change H (1, x) = H (0, x) * _ at h
      rw [H.apply_one, H.apply_zero] at h
      change a x = (1 : OrthogonalOperators n) * productMap N K x at h
      simpa only [one_mul] using h
    · intro x hx i _
      exact hstationary x (fun t ↦ (H.eq_fst t hx).trans (H.eq_fst 0 hx).symm) i
  · rintro ⟨N, K, rfl, hz⟩
    exact ⟨productHomotopyRel N K S hz⟩

end NoExoticSixSphere.OrthogonalExponential
