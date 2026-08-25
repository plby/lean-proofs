import ErdosProblems.Erdos237.S2DyadicGeometry
import ErdosProblems.Erdos237.S2BoxLowerLimit

/-! A convergent dyadic lower bound for the actual squared S2 fibers. -/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def s2DyadicHeight {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    (L : ℕ) (i : K) (a : Fin L) : ℝ :=
  if s2IsInner q m i then dyadicHeight L a else dyadicHeight L a ^ 2

noncomputable def s2DyadicCoefficient {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L : ℕ} (x : K → Fin L) : ℝ := ∏ i, s2DyadicHeight q m L i (x i)

theorem prod_s2Inner_value {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    (a b : K → ℝ) :
    (∏ i : K, if s2IsInner q m i then a i else b i) =
      a (q.symm none) * a (q.symm (some m)) *
        ∏ h ∈ univ.erase m, b (q.symm (some h)) := by
  rw [← q.symm.prod_comp (fun i => if s2IsInner q m i then a i else b i),
    univ_option, prod_insertNone]
  simp only [s2IsInner, Equiv.apply_symm_apply, true_or, ↓reduceIte,
    Option.some_ne_none, false_or, Option.some.injEq]
  rw [← mul_prod_erase _ _ (mem_univ m)]
  simp only [↓reduceIte]
  rw [← mul_assoc]
  congr 1
  apply prod_congr rfl
  intro h hh
  exact if_neg (mem_erase.mp hh).1

theorem prod_configRight {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L : ℕ} (x : K → Fin L) (f : Fin L → ℝ) :
    (∏ h : H, f (s2ConfigRight q m x h)) =
      f (x (q.symm none)) * ∏ h ∈ univ.erase m, f (s2ConfigLeft q x h) := by
  rw [← mul_prod_erase _ _ (mem_univ m)]
  simp only [s2ConfigRight, ↓reduceIte]
  congr 1
  apply prod_congr rfl
  intro h hh
  rw [if_neg (mem_erase.mp hh).1]

theorem s2DyadicCoefficient_eq {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L : ℕ} (x : K → Fin L) :
    s2DyadicCoefficient q m x = (∏ h : H, dyadicHeight L (s2ConfigLeft q x h)) *
      (∏ h : H, dyadicHeight L (s2ConfigRight q m x h)) := by
  simp only [s2DyadicCoefficient, s2DyadicHeight]
  rw [prod_s2Inner_value q m, prod_configRight q m]
  rw [← mul_prod_erase univ (fun h => dyadicHeight L (s2ConfigLeft q x h)) (mem_univ m)]
  simp only [s2ConfigLeft, prod_pow]
  ring

theorem s2DyadicCoefficient_le_y_product {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (e : H ≃ Fin k) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    (alpha : ℝ) (N : ℕ) {x : K → Fin L} (hx : x ∈ s2DyadicBoxes q m L k)
    {z : K → ℕ} (hz : z ∈ maynardDivisorTupleSupport K (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N))
    (hbox : z ∈ engelsmaFractionalTupleShell K alpha
      (fun i => dyadicLength L k (x i) / 2) (fun i => dyadicUpper L k (x i) / 2) N) :
    s2DyadicCoefficient q m x ≤
      dyadicY (L := L) e alpha N (s2LiftLeft q z) *
        dyadicY (L := L) e alpha N (s2LiftRight q m z) := by
  obtain ⟨hlgood, hrgood⟩ := s2DyadicBoxes_project_good q m e hL hk hx
  obtain ⟨hlbox, hrbox⟩ := s2DyadicShell_projects q m e alpha N hbox
  obtain ⟨_, hls, hrs⟩ := s2Lift_supported q m (isMaynardDivisorTuple_of_mem_support hz)
  have hls' := mem_maynardDivisorTupleSupport_iff.mpr ⟨hls.mem_maynardDivisorTupleBox, hls⟩
  have hrs' := mem_maynardDivisorTupleSupport_iff.mpr ⟨hrs.mem_maynardDivisorTupleBox, hrs⟩
  have hl := coefficient_le_dyadicRawWeight e alpha N hlgood hlbox
  have hr := coefficient_le_dyadicRawWeight e alpha N hrgood hrbox
  change (∏ i, (fun h => dyadicHeight L (s2ConfigLeft q x h)) (e.symm i)) ≤ _ at hl
  change (∏ i, (fun h => dyadicHeight L (s2ConfigRight q m x h)) (e.symm i)) ≤ _ at hr
  rw [e.symm.prod_comp (fun h => dyadicHeight L (s2ConfigLeft q x h))] at hl
  rw [e.symm.prod_comp (fun h => dyadicHeight L (s2ConfigRight q m x h))] at hr
  rw [s2DyadicCoefficient_eq]
  simp only [dyadicY, restrictToMaynardSupport, if_pos hls', if_pos hrs']
  exact mul_le_mul hl hr (by unfold dyadicHeight; positivity)
    (dyadicRawWeight_nonneg e alpha N _)

theorem s2Dyadic_volume_term_eq {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L k : ℕ} (x : K → Fin L) :
    s2DyadicCoefficient q m x *
        (∏ i, (dyadicUpper L k (x i) / 2 - dyadicLength L k (x i) / 2)) =
      (1 / 2 : ℝ) ^ Fintype.card K * ∏ i, s2MixedMass q m L k i (x i) := by
  simp_rw [← sub_div, dyadicUpper_sub_length]
  rw [s2DyadicCoefficient, ← prod_mul_distrib]
  have hterm (i : K) : s2DyadicHeight q m L i (x i) * (dyadicLength L k (x i) / 2) =
      (1 / 2 : ℝ) * s2MixedMass q m L k i (x i) := by
    unfold s2DyadicHeight s2MixedMass dyadicLinearMass dyadicSquareMass
    split_ifs <;> ring
  simp_rw [hterm]
  rw [prod_mul_distrib]
  simp

theorem s2Dyadic_volume_lower_bound {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (hL : 0 < L) (hk : 0 < k) (hcard : Fintype.card H ≤ k) :
    ((∑ a, dyadicLinearMass L k a) ^ 2 *
        (∑ a, dyadicSquareMass L k a) ^ (univ.erase m).card / 2) *
        (1 / 2 : ℝ) ^ ((univ.erase m).card + 2) ≤
      ∑ x ∈ s2DyadicBoxes q m L k, s2DyadicCoefficient q m x *
        ∏ i, (dyadicUpper L k (x i) / 2 - dyadicLength L k (x i) / 2) := by
  simp_rw [s2Dyadic_volume_term_eq]
  rw [← mul_sum, card_extraCoordinate q m]
  unfold s2DyadicBoxes
  rw [sum_filter]
  have h := mul_le_mul_of_nonneg_right (dyadic_mixed_mass_lower_bound q m hL hk hcard)
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ ((univ.erase m).card + 2))
  simpa only [mul_comm] using h

theorem exists_dyadic_s2Fiber_lower_sequence {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (e : H ≃ Fin k) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ J : ℝ, ∃ b : ℕ → ℝ,
      ((∑ a, dyadicLinearMass L k a) ^ 2 *
          (∑ a, dyadicSquareMass L k a) ^ (univ.erase m).card / 2) *
          (1 / 2 : ℝ) ^ ((univ.erase m).card + 2) ≤ J ∧
      Tendsto b atTop (nhds J) ∧
      ∀ᶠ N : ℕ in atTop, b N ≤ s2FiberSquareDiagonal H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N) (dyadicY (L := L) e alpha N) m /
          sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2) := by
  have hkpos : 0 < k := (pow_pos (by decide) L).trans_le hk
  have hcard : Fintype.card H = k := (Fintype.card_congr e).trans (Fintype.card_fin k)
  have hint (a : Fin L) : dyadicLength L k a / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      dyadicUpper L k a / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      dyadicLength L k a / 2 ≤ dyadicUpper L k a / 2 := by
    have hl := dyadicLength_nonneg L k a
    have hu := dyadicUpper_le_half hL hk a
    have he := dyadicUpper_eq_two_mul_length L k a
    exact ⟨⟨by positivity, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
  obtain ⟨b, hb, hble⟩ := exists_s2Fiber_lower_sequence_of_boxes q m halpha
    (dyadicY (L := L) e alpha) (dyadicY_nonneg e alpha)
    (s2DyadicBoxes q m L k) (s2DyadicCoefficient q m)
    (fun x i => dyadicLength L k (x i) / 2) (fun x i => dyadicUpper L k (x i) / 2)
    (fun x _ i => (hint (x i)).1) (fun x _ i => (hint (x i)).2.1)
    (fun x _ i => (hint (x i)).2.2)
    (fun _ hx => s2DyadicBoxes_sum_upper_lt_one q m hL hk hx)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      intro x _ y _ hxy
      exact s2DyadicShells_disjoint halpha hN hxy)
    (by
      filter_upwards [] with N x hx z hz hbox
      exact s2DyadicCoefficient_le_y_product q m e hL hk alpha N hx hz hbox)
  exact ⟨_, b, s2Dyadic_volume_lower_bound q m hL hkpos hcard.le, hb, hble⟩

end Erdos237
