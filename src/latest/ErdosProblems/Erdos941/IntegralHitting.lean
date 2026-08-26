import ErdosProblems.Erdos941.DenseTrajectoryHitting

/-! # Translating modular target hits back to integral sphere points -/

namespace Erdos941

open PairLocal

noncomputable def orientSpherePoint {n : ℕ} (hn : n % 3 = 2) (v : {v // v ∈ spherePoints n}) :
    OrientedTriple := by
  have hnorm : tripleNorm v.1 % 3 = 2 := by
    rw [mem_spherePoints.mp v.2]
    exact_mod_cast hn
  let a := Classical.choose (exists_other_admissible hnorm (false, false))
  exact ⟨(a, v.1), hnorm, (Classical.choose_spec (exists_other_admissible hnorm (false, false))).1⟩

theorem orientSpherePoint_val {n : ℕ} (hn : n % 3 = 2) (v : {v // v ∈ spherePoints n}) :
    (orientSpherePoint hn v).1.2 = v.1 := by unfold orientSpherePoint; rfl

theorem integral_modular_norm {p n : ℕ} (s : OrientedTriple) (hn : tripleNorm s.1.2 = n) :
    normThree (mapCoeffs (primeSquareReduce p) (orientedModState p s).2) = (n : ZMod p) := by
  change normThree (mapCoeffs (primeSquareReduce p)
    (mapCoeffs (Int.castRingHom (ZMod (p ^ 2))) s.1.2)) = _
  rw [mapCoeffs_intCast_comp, normThree_mapCoeffs]
  change (tripleNorm s.1.2 : ZMod p) = _
  rw [hn]
  simp

theorem integral_badTurn_target {p n : ℕ} (target : ModularTriple p → Prop)
    (s : OrientedTriple) (hn : tripleNorm s.1.2 = n) (hp : p ∣ n)
    (hbad : modularBadTurn p target (orientedModState p s) (orientedChoice s)) :
    target (mapCoeffs (Int.castRingHom (ZMod (p ^ 2))) s.1.2) ∧
      (3 : ℤ) ∣ s.1.2.1 + s.1.2.2.1 ∧ (3 : ℤ) ∣ s.1.2.2.2 := by
  have hnorm : normThree (mapCoeffs (primeSquareReduce p) (orientedModState p s).2) = 0 := by
    rw [integral_modular_norm s hn]
    exact (ZMod.natCast_eq_zero_iff n p).mpr hp
  obtain ⟨hT, ha, hb⟩ := hbad.resolve_left (not_not.mpr hnorm)
  have ha' : s.1.1 = (true, false) := ha
  have hb' : nextAxis s = (true, true) := (orientedChoice_axis s).symm.trans hb
  have h1 := s.2.2
  have h2 := nextAxis_admissible s
  rw [ha'] at h1
  rw [hb'] at h2
  simp only [Admissible, axisDot, sign, ↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul] at h1 h2
  exact ⟨hT, by omega, by omega⟩

theorem exists_large_sphere_integral_target (p : ℕ) [NeZero (p ^ 2)]
    (t : ZMod (p ^ 2)) (target : ModularTriple p → Prop) (ht : 3 * t = 1)
    (K : ℕ) (hK : 0 < K)
    (havoid : ∀ (j : ℕ) (s : (Axis × ModularTriple p) × Bool),
      modularAvoidance p t target (K * j) s ≤ (3 ^ K - 1) ^ j) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ¬4 ∣ n → n % 8 ≠ 7 → n % 3 = 2 → p ∣ n →
      ∃ v : Triple, tripleNorm v = n ∧
        target (mapCoeffs (Int.castRingHom (ZMod (p ^ 2))) v) ∧
        (3 : ℤ) ∣ v.1 + v.2.1 ∧ (3 : ℤ) ∣ v.2.2 := by
  obtain ⟨N, hN, hhit⟩ := exists_large_dense_trajectory_hit p t target ht K hK havoid 1 (by norm_num)
  refine ⟨N, hN, ?_⟩
  intro n hn h4 h8 h3 hp
  obtain ⟨L, v, i, _, hbad⟩ := hhit n hn h4 h8 h3 {v // v ∈ spherePoints n}
    (orientSpherePoint h3)
    (by
      intro v w h
      apply Subtype.ext
      simpa only [orientSpherePoint_val] using h)
    (fun v => by rw [orientSpherePoint_val]; exact mem_spherePoints.mp v.2)
    (by simp only [one_mul, Fintype.card_coe]; rfl)
  let s := centeredState L (orientSpherePoint h3 v) i
  have hnorm : tripleNorm s.1.2 = n := by
    rw [centeredState_norm, orientSpherePoint_val]
    exact mem_spherePoints.mp v.2
  exact ⟨s.1.2, hnorm, integral_badTurn_target target s hnorm hp hbad⟩

theorem exists_large_five_sphere_target :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ¬4 ∣ n → n % 8 ≠ 7 → n % 3 = 2 → 5 ∣ n →
      ∃ v : Triple, tripleNorm v = n ∧ (25 : ℤ) ∣ v.2.2 := by
  obtain ⟨K, hK, havoid⟩ := exists_five_modular_avoidance
  obtain ⟨N, hN, hhit⟩ := exists_large_sphere_integral_target 5 17 (fun v => v.2.2 = 0)
    (by decide) K hK havoid
  refine ⟨N, hN, ?_⟩
  intro n hn h4 h8 h3 h5
  obtain ⟨v, hv, ht, _⟩ := hhit n hn h4 h8 h3 h5
  exact ⟨v, hv, (ZMod.intCast_zmod_eq_zero_iff_dvd v.2.2 25).mp ht⟩

theorem exists_large_thirteen_sphere_target :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ¬4 ∣ n → n % 8 ≠ 7 → n % 3 = 2 → 13 ∣ n →
      ∃ v : Triple, tripleNorm v = n ∧ (169 : ℤ) ∣ v.2.2 := by
  obtain ⟨K, hK, havoid⟩ := exists_thirteen_modular_avoidance
  obtain ⟨N, hN, hhit⟩ := exists_large_sphere_integral_target 13 113 (fun v => v.2.2 = 0)
    (by decide) K hK havoid
  refine ⟨N, hN, ?_⟩
  intro n hn h4 h8 h3 h13
  obtain ⟨v, hv, ht, _⟩ := hhit n hn h4 h8 h3 h13
  exact ⟨v, hv, (ZMod.intCast_zmod_eq_zero_iff_dvd v.2.2 169).mp ht⟩

end Erdos941
