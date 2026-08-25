import Util.IncidenceGeometry.Basic
import Mathlib.Data.Set.Card

open Classical
noncomputable section

lemma TwoCirclesIntersectionsAtMostTwo
    (c x : EuclideanSpace ℝ (Fin 2)) (hcx : c ≠ x) (r ρ : ℝ) :
    {p : EuclideanSpace ℝ (Fin 2) | dist p c = r ∧ dist p x = ρ}.Finite ∧
      ({p : EuclideanSpace ℝ (Fin 2) | dist p c = r ∧ dist p x = ρ}.ncard) ≤ 2 := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p : EuclideanSpace ℝ (Fin 2) | dist p c = r ∧ dist p x = ρ}
  change S.Finite ∧ S.ncard ≤ 2
  have circle_sq :
      ∀ {a p : EuclideanSpace ℝ (Fin 2)} {R : ℝ}, dist p a = R →
        (p 0 - a 0) ^ 2 + (p 1 - a 1) ^ 2 = R ^ 2 := by
    intro a p R hp
    have hsq : dist p a ^ 2 = R ^ 2 := by rw [hp]
    rw [dist_eq_norm] at hsq
    change ‖p - a‖ ^ 2 = R ^ 2 at hsq
    have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (p - a)
    rw [hnorm] at hsq
    norm_num at hsq
    simpa [EuclideanSpace, Fin.sum_univ_two, sub_eq_add_neg, sq] using hsq
  have quadratic_roots :
      ∀ (A B C : ℝ), A ≠ 0 →
        ({t : ℝ | A * t ^ 2 + B * t + C = 0}.Finite ∧
          ({t : ℝ | A * t ^ 2 + B * t + C = 0}.ncard) ≤ 2) := by
    intro A B C hA
    let Y : Set ℝ := {y | y ^ 2 = B ^ 2 - 4 * A * C}
    have hY : Y.Finite ∧ Y.ncard ≤ 2 := by
      by_cases hnon : Y.Nonempty
      · rcases hnon with ⟨y0, hy0⟩
        have hsub : Y ⊆ ({y0, -y0} : Set ℝ) := by
          intro y hy
          have hy' : y ^ 2 = y0 ^ 2 := by
            rw [hy, hy0]
          rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hy') with h | h
          · simp [h]
          · simp [h]
        have hpairfin : ({y0, -y0} : Set ℝ).Finite := by simp
        have hfin : Y.Finite := hpairfin.subset hsub
        refine ⟨hfin, ?_⟩
        calc
          Y.ncard ≤ ({y0, -y0} : Set ℝ).ncard := Set.ncard_le_ncard hsub hpairfin
          _ ≤ 2 := by
            calc
              ({y0, -y0} : Set ℝ).ncard ≤ ({-y0} : Set ℝ).ncard + 1 :=
                Set.ncard_insert_le y0 ({-y0} : Set ℝ)
              _ = 2 := by simp
      · have hYempty : Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hnon
        simp [hYempty]
    let f : ℝ → ℝ := fun t => 2 * A * t + B
    have hf_inj : Function.Injective f := by
      intro x y hxy
      dsimp [f] at hxy
      have hcoef : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hA
      have hmul : (2 * A) * (x - y) = 0 := by nlinarith
      have hsub : x - y = 0 := (mul_eq_zero.mp hmul).resolve_left hcoef
      exact sub_eq_zero.mp hsub
    have hinj : Set.InjOn f ({t : ℝ | A * t ^ 2 + B * t + C = 0}) := hf_inj.injOn
    have hsub : f '' {t : ℝ | A * t ^ 2 + B * t + C = 0} ⊆ Y := by
      intro y hy
      rcases hy with ⟨t, ht, rfl⟩
      dsimp [Y, f]
      have hmul : A ^ 2 * t ^ 2 + A * B * t + A * C = 0 := by
        calc
          A ^ 2 * t ^ 2 + A * B * t + A * C = A * (A * t ^ 2 + B * t + C) := by ring
          _ = 0 := by rw [ht, mul_zero]
      ring_nf at ht ⊢
      ring_nf at hmul
      nlinarith [hmul]
    have hfin_image : (f '' {t : ℝ | A * t ^ 2 + B * t + C = 0}).Finite :=
      hY.1.subset hsub
    have hfin : ({t : ℝ | A * t ^ 2 + B * t + C = 0} : Set ℝ).Finite :=
      Set.Finite.of_finite_image hfin_image hinj
    refine ⟨hfin, ?_⟩
    rw [← Set.InjOn.ncard_image hinj]
    exact (Set.ncard_le_ncard hsub hY.1).trans hY.2
  by_cases h0 : c 0 ≠ x 0
  · let d0 : ℝ := x 0 - c 0
    let d1 : ℝ := x 1 - c 1
    let K : ℝ := (x 0 ^ 2 - c 0 ^ 2 + x 1 ^ 2 - c 1 ^ 2 + r ^ 2 - ρ ^ 2) / 2
    let A : ℝ := d1 ^ 2 + d0 ^ 2
    let Bcoef : ℝ := -2 * d1 * (K - c 0 * d0) - 2 * d0 ^ 2 * c 1
    let Ccoef : ℝ := (K - c 0 * d0) ^ 2 + d0 ^ 2 * c 1 ^ 2 - d0 ^ 2 * r ^ 2
    let T : Set ℝ := {t : ℝ | A * t ^ 2 + Bcoef * t + Ccoef = 0}
    have hd0 : d0 ≠ 0 := by
      dsimp [d0]
      exact sub_ne_zero.mpr h0.symm
    have hA : A ≠ 0 := by
      have hd0pos : 0 < d0 ^ 2 := sq_pos_of_ne_zero hd0
      have hd1nonneg : 0 ≤ d1 ^ 2 := sq_nonneg d1
      have hpos : 0 < A := by
        dsimp [A]
        exact add_pos_of_nonneg_of_pos hd1nonneg hd0pos
      exact ne_of_gt hpos
    have hT : T.Finite ∧ T.ncard ≤ 2 := by
      simpa [T] using quadratic_roots A Bcoef Ccoef hA
    have lin_of_mem : ∀ p ∈ S, d0 * p 0 + d1 * p 1 = K := by
      intro p hp
      have hpc := circle_sq hp.1
      have hpx := circle_sq hp.2
      dsimp [d0, d1, K]
      nlinarith [hpc, hpx]
    have hproj_sub : (fun p : EuclideanSpace ℝ (Fin 2) => p 1) '' S ⊆ T := by
      intro t ht
      rcases ht with ⟨p, hp, rfl⟩
      have hpc := circle_sq hp.1
      have hlin := lin_of_mem p hp
      have hlin' : K - d1 * p 1 = d0 * p 0 := by nlinarith [hlin]
      have hterm : K - d1 * p 1 - c 0 * d0 = d0 * (p 0 - c 0) := by nlinarith [hlin']
      have hscaled :
          (K - d1 * p 1 - c 0 * d0) ^ 2 + d0 ^ 2 * (p 1 - c 1) ^ 2 -
              d0 ^ 2 * r ^ 2 = 0 := by
        calc
          (K - d1 * p 1 - c 0 * d0) ^ 2 + d0 ^ 2 * (p 1 - c 1) ^ 2 -
              d0 ^ 2 * r ^ 2
              = (d0 * (p 0 - c 0)) ^ 2 + d0 ^ 2 * (p 1 - c 1) ^ 2 -
                  d0 ^ 2 * r ^ 2 := by rw [hterm]
          _ = d0 ^ 2 * ((p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 - r ^ 2) := by ring
          _ = 0 := by rw [hpc]; ring
      change A * (p 1) ^ 2 + Bcoef * (p 1) + Ccoef = 0
      calc
        A * (p 1) ^ 2 + Bcoef * (p 1) + Ccoef
            = (K - d1 * p 1 - c 0 * d0) ^ 2 + d0 ^ 2 * (p 1 - c 1) ^ 2 -
                d0 ^ 2 * r ^ 2 := by
              dsimp [A, Bcoef, Ccoef]
              ring
        _ = 0 := hscaled
    have hinj : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 1) S := by
      intro p hp q hq hpq
      have hplin := lin_of_mem p hp
      have hqlin := lin_of_mem q hq
      have hpq1 : p 1 = q 1 := hpq
      ext i
      fin_cases i
      · have hmul : d0 * (p 0 - q 0) = 0 := by
          calc
            d0 * (p 0 - q 0)
                = (d0 * p 0 + d1 * p 1) - (d0 * q 0 + d1 * q 1) := by
                  rw [hpq1]
                  ring
            _ = K - K := by rw [hplin, hqlin]
            _ = 0 := by ring
        have hsub : p 0 - q 0 = 0 := (mul_eq_zero.mp hmul).resolve_left hd0
        exact sub_eq_zero.mp hsub
      · exact hpq1
    have hfin_image : ((fun p : EuclideanSpace ℝ (Fin 2) => p 1) '' S).Finite :=
      hT.1.subset hproj_sub
    have hSfin : S.Finite := Set.Finite.of_finite_image hfin_image hinj
    refine ⟨hSfin, ?_⟩
    rw [← Set.InjOn.ncard_image hinj]
    exact (Set.ncard_le_ncard hproj_sub hT.1).trans hT.2
  · have h0eq : c 0 = x 0 := not_not.mp h0
    have h1 : c 1 ≠ x 1 := by
      intro h1eq
      apply hcx
      ext i
      fin_cases i
      · exact h0eq
      · exact h1eq
    let d0 : ℝ := x 1 - c 1
    let d1 : ℝ := x 0 - c 0
    let K : ℝ := (x 0 ^ 2 - c 0 ^ 2 + x 1 ^ 2 - c 1 ^ 2 + r ^ 2 - ρ ^ 2) / 2
    let A : ℝ := d1 ^ 2 + d0 ^ 2
    let Bcoef : ℝ := -2 * d1 * (K - c 1 * d0) - 2 * d0 ^ 2 * c 0
    let Ccoef : ℝ := (K - c 1 * d0) ^ 2 + d0 ^ 2 * c 0 ^ 2 - d0 ^ 2 * r ^ 2
    let T : Set ℝ := {t : ℝ | A * t ^ 2 + Bcoef * t + Ccoef = 0}
    have hd0 : d0 ≠ 0 := by
      dsimp [d0]
      exact sub_ne_zero.mpr h1.symm
    have hA : A ≠ 0 := by
      have hd0pos : 0 < d0 ^ 2 := sq_pos_of_ne_zero hd0
      have hd1nonneg : 0 ≤ d1 ^ 2 := sq_nonneg d1
      have hpos : 0 < A := by
        dsimp [A]
        exact add_pos_of_nonneg_of_pos hd1nonneg hd0pos
      exact ne_of_gt hpos
    have hT : T.Finite ∧ T.ncard ≤ 2 := by
      simpa [T] using quadratic_roots A Bcoef Ccoef hA
    have lin_of_mem : ∀ p ∈ S, d1 * p 0 + d0 * p 1 = K := by
      intro p hp
      have hpc := circle_sq hp.1
      have hpx := circle_sq hp.2
      dsimp [d0, d1, K]
      nlinarith [hpc, hpx]
    have hproj_sub : (fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' S ⊆ T := by
      intro t ht
      rcases ht with ⟨p, hp, rfl⟩
      have hpc := circle_sq hp.1
      have hlin := lin_of_mem p hp
      have hlin' : K - d1 * p 0 = d0 * p 1 := by nlinarith [hlin]
      have hterm : K - d1 * p 0 - c 1 * d0 = d0 * (p 1 - c 1) := by nlinarith [hlin']
      have hscaled :
          (K - d1 * p 0 - c 1 * d0) ^ 2 + d0 ^ 2 * (p 0 - c 0) ^ 2 -
              d0 ^ 2 * r ^ 2 = 0 := by
        calc
          (K - d1 * p 0 - c 1 * d0) ^ 2 + d0 ^ 2 * (p 0 - c 0) ^ 2 -
              d0 ^ 2 * r ^ 2
              = (d0 * (p 1 - c 1)) ^ 2 + d0 ^ 2 * (p 0 - c 0) ^ 2 -
                  d0 ^ 2 * r ^ 2 := by rw [hterm]
          _ = d0 ^ 2 * ((p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 - r ^ 2) := by ring
          _ = 0 := by rw [hpc]; ring
      change A * (p 0) ^ 2 + Bcoef * (p 0) + Ccoef = 0
      calc
        A * (p 0) ^ 2 + Bcoef * (p 0) + Ccoef
            = (K - d1 * p 0 - c 1 * d0) ^ 2 + d0 ^ 2 * (p 0 - c 0) ^ 2 -
                d0 ^ 2 * r ^ 2 := by
              dsimp [A, Bcoef, Ccoef]
              ring
        _ = 0 := hscaled
    have hinj : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 2) => p 0) S := by
      intro p hp q hq hpq
      have hplin := lin_of_mem p hp
      have hqlin := lin_of_mem q hq
      have hpq0 : p 0 = q 0 := hpq
      ext i
      fin_cases i
      · exact hpq0
      · have hmul : d0 * (p 1 - q 1) = 0 := by
          calc
            d0 * (p 1 - q 1)
                = (d1 * p 0 + d0 * p 1) - (d1 * q 0 + d0 * q 1) := by
                  rw [hpq0]
                  ring
            _ = K - K := by rw [hplin, hqlin]
            _ = 0 := by ring
        have hsub : p 1 - q 1 = 0 := (mul_eq_zero.mp hmul).resolve_left hd0
        exact sub_eq_zero.mp hsub
    have hfin_image : ((fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' S).Finite :=
      hT.1.subset hproj_sub
    have hSfin : S.Finite := Set.Finite.of_finite_image hfin_image hinj
    refine ⟨hSfin, ?_⟩
    rw [← Set.InjOn.ncard_image hinj]
    exact (Set.ncard_le_ncard hproj_sub hT.1).trans hT.2
