import ErdosProblems.Erdos587.HooleyAdaptedMass
import ErdosProblems.Erdos587.HooleyInnerRadius
import ErdosProblems.Erdos587.HooleyBoxMass

/-! # Full individual widths and cardinality of the adapted inner GAP -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

theorem delta_full_width_adapted_inner_box (X : ConvexProgression) (hX : 0 < X.rank)
    (D : MahlerBoxData X) (U : Finset (Fin X.rank → ℤ)) (hU : 0 < U.card)
    (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤)
    {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)),
      δ • x ∈ X.body)
    (hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) X.body)
    (hproper : X.SProper 1) (hbase : ∃ c : Fin X.rank → ℤ, X.eval c = X.base)
    (hlarge : 16 * (D.scale : ℝ) ≤ δ * U.card) :
    let F := 9 * X.rank * ⌈32 * (D.scale : ℝ) / δ⌉₊
    0 < F ∧ ∃ Q : GeneralizedAP, Q.rank = X.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ X.carrier ∧ (∀ i, U.card ≤ F * Q.length i) ∧
      U.card ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      Q = deltaBasisBox X D.basis (fun i => ⌊D.bound i / D.scale⌋₊) := by
  classical
  let K := ⌈32 * (D.scale : ℝ) / δ⌉₊
  let F := 9 * X.rank * K
  let R : Fin X.rank → ℕ := fun i => ⌊D.bound i / D.scale⌋₊
  let B : Fin X.rank → ℕ := fun i => ⌈8 * D.bound i / δ⌉₊
  let Q := deltaBasisBox X D.basis R
  let A := U.image (latticeCoordinates D.basis)
  have hK : 0 < K := by
    have hh : (0 : ℝ) < 32 * D.scale / δ := by
      have hs : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
      positivity
    have hKR : (0 : ℝ) < K := hh.trans_le (Nat.le_ceil (32 * (D.scale : ℝ) / δ))
    exact_mod_cast hKR
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨hQproper, hQhom, hQsub⟩ := delta_adapted_inner_box X D hproper hbase
  have hBbounds (i : Fin X.rank) : U.card ≤ B i ∧ B i ≤ K * R i :=
    delta_inner_radius_budgets D.scale_pos hU hδ
      (delta_adapted_width_of_robust_spanning X D U k hk hspan hδ hsub hround i) hlarge
  have hAcard : A.card = U.card :=
    Finset.card_image_of_injOn (latticeCoordinates D.basis).injective.injOn
  have hApos : 0 < A.card := by rwa [hAcard]
  have hmass (i : Fin X.rank) : (∑ v ∈ A, (v i).natAbs) ≤ B i := by
    have heq : (∑ v ∈ A, ((v i).natAbs : ℝ)) =
        ∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ) := by
      dsimp only [A]
      rw [Finset.sum_image (fun u _ v _ h => (latticeCoordinates D.basis).injective h)]
      simp only [Nat.cast_natAbs]
    have hh : (∑ v ∈ A, ((v i).natAbs : ℝ)) ≤ (B i : ℝ) := by
      calc
        _ = ∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ) := heq
        _ ≤ 4 * D.bound i / δ := delta_adapted_coordinate_mass X D U hδ hsub hround i
        _ ≤ 8 * D.bound i / δ :=
          div_le_div_of_nonneg_right (by have := D.bound_nonneg i; linarith) hδ.le
        _ ≤ (B i : ℝ) := Nat.le_ceil _
    exact_mod_cast hh
  have hcard := CFP.delta_box_product_lower_of_coordinate_mass hX A hApos B
    (fun i => by rw [hAcard]; exact (hBbounds i).1) hmass
  have hprod : (∏ i, B i) ≤ K ^ X.rank * ∏ i, R i := by
    calc
      _ ≤ ∏ i, K * R i := Finset.prod_le_prod' (fun i _ => (hBbounds i).2)
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  have hRcard : (∏ i, R i) ≤ Q.carrier.card := by
    rw [Q.card_carrier_of_proper hQproper]
    change (∏ i, R i) ≤ ∏ i, (2 * R i + 1)
    exact Finset.prod_le_prod' (fun _ _ => by omega)
  have hKF : K ≤ F := by
    have hh := Nat.mul_le_mul_right K (show 1 ≤ 9 * X.rank by omega)
    simpa only [one_mul] using hh
  refine ⟨hF, Q, rfl, hQproper, hQhom, hQsub, ?_, ?_, rfl⟩
  · intro i
    calc
      U.card ≤ B i := (hBbounds i).1
      _ ≤ K * R i := (hBbounds i).2
      _ ≤ F * Q.length i := Nat.mul_le_mul hKF (by change R i ≤ 2 * R i; omega)
  · calc
      U.card ^ (Q.rank + 1) = U.card ^ (X.rank + 1) := rfl
      _ ≤ 2 * (9 * X.rank) ^ X.rank * ∏ i, B i := by simpa only [hAcard] using hcard
      _ ≤ 2 * (9 * X.rank) ^ X.rank * (K ^ X.rank * Q.carrier.card) :=
        Nat.mul_le_mul_left _ (hprod.trans (Nat.mul_le_mul_left _ hRcard))
      _ = 2 * F ^ Q.rank * Q.carrier.card := by
        change 2 * (9 * X.rank) ^ X.rank * (K ^ X.rank * Q.carrier.card) =
          2 * (9 * X.rank * K) ^ X.rank * Q.carrier.card
        simp only [mul_pow]
        ring

end Erdos587.GeneralizedAP
