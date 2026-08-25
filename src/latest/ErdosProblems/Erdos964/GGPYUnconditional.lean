import ErdosProblems.Erdos964.ScalarSieveExcess
import ErdosProblems.Erdos964.GPYReduction

/-!
# Unconditional simultaneous large semiprimes in admissible triples

The scalar sieve with the checked polynomial produces a positive excess.
The fixed normalization and finite-pair argument then give the prescribed
factor statement needed for the divisor-ratio theorem.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter

theorem admissible_semiprime_triples : AdmissibleSemiprimeTriples := by
  classical
  intro A B hA hB hne hadm C
  let M := affineNormalizationModulus A B
  have hM : 0 < M := affineNormalizationModulus_pos A B hA hne
  obtain ⟨v, hv⟩ := exists_affine_avoiding_modulus A B M hM hadm
  let d : Fin 3 → ℕ := fun j => 2 * (A j * M) + (A j * v + B j)
  let K := 1 + ∑ j : Fin 3, d j
  have hK : 1 ≤ K := by dsimp only [K]; omega
  have hKsize (j : Fin 3) : 2 * (A j * M) + (A j * v + B j) ≤ K ^ 2 := by
    have hsingle : d j ≤ ∑ i : Fin 3, d i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    have hle : d j ≤ K := by dsimp only [K]; omega
    exact hle.trans (by nlinarith)
  let β : ℝ := 2 * sieveRadiusExponent
  let η : ℝ := β / 100
  let θβ : ℝ := 49999 / 50000
  let θp : ℝ := 49999 / 100000
  have hη : 0 < η := by norm_num [η, β, sieveRadiusExponent]
  have hηβ : η < β := by norm_num [η, β, sieveRadiusExponent]
  have hβθβ : 2 * β ≤ θβ := by norm_num [β, θβ, sieveRadiusExponent]
  have hθβ1 : θβ < 1 := by norm_num [θβ]
  have hβθp : β < θp := by norm_num [β, θp, sieveRadiusExponent]
  have hθphalf : θp < 1 / 2 := by norm_num [θp]
  have hmargin : (19 / 15 : ℝ) < 3 * (β / 2) * scalarPrimeIntegral η β := by
    have h := (show (19 / 15 : ℝ) < 19 / 15 + 1 / 10000 by norm_num).trans
      scalarPrimeIntegral_positive_margin
    calc
      _ < 3 * sieveRadiusExponent * scalarPrimeIntegral η β := by
        simpa only [η, β] using h
      _ = _ := by dsimp only [β]; ring
  have hpairs := eventually_two_scalar_semiprime_values A B hA hB hne hadm v K hv hK hKsize
    η β θβ θp hη hηβ hβθβ hθβ1 hβθp hθphalf hmargin
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hpairs
  obtain ⟨T₁, hT₁, hlarge⟩ := exists_scalarSmallPrimeSupport_ge (C + 1) η hη
  apply exists_infinite_pair_of_unbounded (fun i n => A i * n + B i ∈ E2 C)
  intro H
  let t := max T₀ (max T₁ (H + 2))
  have ht₀ : T₀ ≤ t := le_max_left _ _
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htH : H + 2 ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨n, hn, i, j, hij, hi, hj⟩ := hT₀ t ht₀
  let x := M * n + v
  have hHn : H < n := by have := (Finset.mem_Ico.mp hn).1; nlinarith
  have hnx : n ≤ x := (Nat.le_mul_of_pos_left n hM).trans (Nat.le_add_right _ _)
  have hset (m c : ℕ) : (scalarAffineSemiprimeSet m c K η t : Set ℕ) ⊆ E2 C := by
    intro u hu
    have hmem : u ∈ semiprimesAtScale (scalarSmallPrimeSupport η K t) (K * t)
        (m * (2 * t ^ 2) + c - 1) := by
      exact (Finset.mem_sdiff.mp hu).1
    apply semiprimesAtScale_subset_E2 (scalarSmallPrimeSupport η K t) C (K * t) _ _ _ hmem
    · intro p hp
      exact ⟨(scalarSmallPrimeSupport_spec η K t p hp).1,
        (Nat.lt_succ_self C).trans_le (hlarge t ht₁ K hK p hp)⟩
    · intro p hp
      exact scalarSmallPrimeSupport_le_scale η K t p hK hp
  refine ⟨x, hHn.trans_le hnx, i, j, hij, ?_, ?_⟩
  · have hid : A i * x + B i = A i * M * n + (A i * v + B i) := by dsimp only [x]; ring
    rw [hid]
    exact hset _ _ hi
  · have hid : A j * x + B j = A j * M * n + (A j * v + B j) := by dsimp only [x]; ring
    rw [hid]
    exact hset _ _ hj

theorem goldston_graham_pintz_yildirim : GoldstonGrahamPintzYildirimStatement :=
  gpy_of_admissible_semiprime_triples admissible_semiprime_triples

end Erdos964
