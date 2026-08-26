import ErdosProblems.Erdos941.IntegralHitting
import ErdosProblems.Erdos941.ParitySphereCount

/-! # The integral targets for the two forms at 7 -/

namespace Erdos941

open PairLocal

theorem sevenModularTarget_int {v : Triple}
    (h : SevenModularTarget (mapCoeffs (Int.castRingHom (ZMod 49)) v)) :
    (7 : ℤ) ∣ v.1 - 3 * v.2.1 ∧ (7 : ℤ) ∣ v.2.2 - 5 * v.2.1 ∧
      (49 : ℤ) ∣ lambda v.1 v.2.1 v.2.2 := by
  obtain ⟨⟨hA, hC⟩, hL⟩ := h
  change primeSquareReduce 7 (v.1 : ZMod 49) =
    3 * primeSquareReduce 7 (v.2.1 : ZMod 49) at hA
  change primeSquareReduce 7 (v.2.2 : ZMod 49) =
    5 * primeSquareReduce 7 (v.2.1 : ZMod 49) at hC
  simp only [map_intCast] at hA hC
  change -(v.1 : ZMod 49) + (v.2.1 : ZMod 49) - (v.2.2 : ZMod 49) = 0 at hL
  refine ⟨?_, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
    push_cast
    exact sub_eq_zero.mpr hA
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
    push_cast
    exact sub_eq_zero.mpr hC
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 49).mp
    simpa only [lambda, Int.cast_sub, Int.cast_add, Int.cast_neg] using hL

theorem exists_large_seven_parity_target :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ) (b : Bool), N ≤ n → n % 8 = (if b then 6 else 3) →
      n % 3 = 2 → 7 ∣ n → ∃ v : Triple, tripleNorm v = n ∧ SphereParity b v ∧
        (7 : ℤ) ∣ v.1 - 3 * v.2.1 ∧ (7 : ℤ) ∣ v.2.2 - 5 * v.2.1 ∧
        (49 : ℤ) ∣ lambda v.1 v.2.1 v.2.2 ∧
        (3 : ℤ) ∣ v.1 + v.2.1 ∧ (3 : ℤ) ∣ v.2.2 := by
  obtain ⟨K, hK, havoid⟩ := exists_seven_modular_avoidance
  obtain ⟨N, hN, hhit⟩ := exists_large_dense_trajectory_hit 7 33 SevenModularTarget (by decide)
    K hK havoid 6 (by norm_num)
  refine ⟨N, hN, ?_⟩
  intro n b hn h8 h3 h7
  let A := {v // v ∈ paritySpherePoints n b}
  let o : A → OrientedTriple := fun v =>
    orientSpherePoint h3 ⟨v.1, (Finset.mem_filter.mp v.2).1⟩
  have hval (v : A) : (o v).1.2 = v.1 := orientSpherePoint_val _ _
  have h8' : n % 8 = 3 ∨ n % 8 = 6 := by
    cases b
    · exact Or.inl h8
    · exact Or.inr h8
  obtain ⟨L, v, i, _, hbad⟩ := hhit n hn (by omega) (by omega) h3 A o
    (by
      intro v w h
      apply Subtype.ext
      simpa only [hval] using h)
    (fun v => by rw [hval]; exact mem_spherePoints.mp (Finset.mem_filter.mp v.2).1)
    (by
      have h := sphereCount_le_six_parity_count b h8
      change (sphereCount n : ℝ) ≤ 6 * Fintype.card {v // v ∈ paritySpherePoints n b}
      rw [Fintype.card_coe]
      exact_mod_cast h)
  let s := centeredState L (o v) i
  have hnorm : tripleNorm s.1.2 = n := by
    rw [centeredState_norm, hval]
    exact mem_spherePoints.mp (Finset.mem_filter.mp v.2).1
  have hparity : SphereParity b s.1.2 := by
    have h : SphereParity b (o v).1.2 := by rw [hval]; exact (Finset.mem_filter.mp v.2).2
    exact h.centeredState L i
  obtain ⟨hT, hAB, hC⟩ := integral_badTurn_target SevenModularTarget s hnorm h7 hbad
  obtain ⟨hA7, hC7, hL⟩ := sevenModularTarget_int hT
  exact ⟨s.1.2, hnorm, hparity, hA7, hC7, hL, hAB, hC⟩

theorem exists_large_seven_sphere_target :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 8 = 3 → n % 3 = 2 → 7 ∣ n →
      ∃ v : Triple, tripleNorm v = n ∧ SevenTarget v.1 v.2.1 v.2.2 := by
  obtain ⟨N, hN, hhit⟩ := exists_large_seven_parity_target
  refine ⟨N, hN, ?_⟩
  intro n hn h8 h3 h7
  obtain ⟨v, hv, hp, hA7, hC7, hL, hAB, hC⟩ := hhit n false hn h8 h3 h7
  have hAo : v.1 % 2 = 1 := hp.1
  have hBo : v.2.1 % 2 = 1 := hp.2.1
  exact ⟨v, hv, hA7, hC7, hL, hAB, hC, hp.2.2, by omega⟩

theorem exists_large_fourteen_sphere_target :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 8 = 6 → n % 3 = 2 → 7 ∣ n →
      ∃ v : Triple, tripleNorm v = n ∧ FourteenTarget v.1 v.2.1 v.2.2 := by
  obtain ⟨N, hN, hhit⟩ := exists_large_seven_parity_target
  refine ⟨N, hN, ?_⟩
  intro n hn h8 h3 h7
  obtain ⟨v, hv, hp, hA7, hC7, hL, hAB, hC⟩ := hhit n true hn h8 h3 h7
  exact ⟨v, hv, hA7, hC7, hL, hAB, hC, hp.1, hp.2.1, hp.2.2⟩

end Erdos941
