import ErdosProblems.Erdos4.ProductPrimeMeanSquare

/-!
# The anchored average and its exact Fourier error

The anchored affine forms use the ratio `p / q`. Their Fourier expansion
therefore has the source character and the conjugate target character.
After the proved conductor truncation, the error is exactly the finite
source error controlled by the double prime mean-square estimate.
-/

open scoped BigOperators

namespace Erdos4.AnchoredFourierAverage

open ProductFourierInversion FiniteCharacterSupport ProductCharacterEncoding

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

theorem value_mul (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u v : ∀ p, (ZMod (ell p))ˣ) :
    value ell chi (u * v) = value ell chi u * value ell chi v := by
  simp only [value, Pi.mul_apply, Units.val_mul, map_mul, Finset.prod_mul_distrib]

theorem value_one (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    value ell chi 1 = 1 := by simp [value]

theorem value_norm (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u : ∀ p, (ZMod (ell p))ˣ) : ‖value ell chi u‖ = 1 := by
  unfold value
  rw [norm_prod]
  exact Finset.prod_eq_one (fun p _hp => (chi p).unit_norm_eq_one (u p))

theorem value_inv (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u : ∀ p, (ZMod (ell p))ˣ) : value ell chi u⁻¹ = star (value ell chi u) := by
  have hh : value ell chi u⁻¹ * value ell chi u = 1 := by
    rw [← value_mul, inv_mul_cancel, value_one]
  have hi : (value ell chi u)⁻¹ = value ell chi u⁻¹ := inv_eq_of_mul_eq_one_left hh
  rw [← hi]
  simpa only [starRingEnd_apply] using Complex.inv_eq_conj (value_norm ell chi u)

theorem value_div (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u v : ∀ p, (ZMod (ell p))ˣ) :
    value ell chi (u / v) = value ell chi u * star (value ell chi v) := by
  rw [div_eq_mul_inv, value_mul, value_inv]

noncomputable def unitPoint (n : ℕ) (hn : n.Coprime (modulus ell)) : ∀ p, (ZMod (ell p))ˣ :=
  fun p => ZMod.unitsMap (local_dvd_modulus ell p) (ZMod.unitOfCoprime n hn)

theorem value_unitPoint (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (n : ℕ) (hn : n.Coprime (modulus ell)) :
    value ell chi (unitPoint ell n hn) = ProductPrimeMeanSquare.value ell chi n := by
  unfold value ProductPrimeMeanSquare.value
  apply Finset.prod_congr rfl
  intro p _hp
  change chi p ((ZMod.unitsMap (local_dvd_modulus ell p) (ZMod.unitOfCoprime n hn)) : ZMod (ell p)) = _
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (local_dvd_modulus ell p)]

theorem value_ratio (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (p q : ℕ) (hp : p.Coprime (modulus ell)) (hq : q.Coprime (modulus ell)) :
    value ell chi (unitPoint ell p hp / unitPoint ell q hq) =
      ProductPrimeMeanSquare.value ell chi p * star (ProductPrimeMeanSquare.value ell chi q) := by
  rw [value_div, value_unitPoint, value_unitPoint]

variable {k : ℕ}

noncomputable def square (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) : ℂ :=
  TensorMoments.amplitude (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
    (fun p a t => (LocalOrthogonality.extendedBasis (ell p : ℝ) a
      (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) t) : ℂ)) u ^ 2

noncomputable def realSquare (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) : ℝ :=
  (∑ a, DivisorCoefficients.coefficient m R ell a *
    ∏ p, LocalOrthogonality.extendedBasis (ell p : ℝ) (a p)
      (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) (u p))) ^ 2

theorem realSquare_nonneg (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) : 0 ≤ realSquare ell m R h j u := sq_nonneg _

theorem square_eq_realSquare (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) :
    square ell m R h j u = (realSquare ell m R h j u : ℂ) := by
  simp only [square, realSquare, TensorMoments.amplitude, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]

theorem truncated_inversion (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (hh : ∀ p, Function.Injective (h p)) (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) :
    square ell m R h j u = UnitFourier.coefficient ell m R h j (fun _ => 1) +
      ∑ chi : smallCharacters ell R, UnitFourier.coefficient ell m R h j chi.val * value ell chi.val u := by
  classical
  let f : (∀ p, DirichletCharacter ℂ (ell p)) → ℂ :=
    fun chi => UnitFourier.coefficient ell m R h j chi * value ell chi u
  let oneChar : ∀ p, DirichletCharacter ℂ (ell p) := fun _ => 1
  have hs : smallCharacters ell R ⊆ Finset.univ.erase oneChar := by
    intro chi hchi
    exact Finset.mem_erase.mpr ⟨((mem_smallCharacters ell R chi).mp hchi).1, Finset.mem_univ _⟩
  have hsub : (∑ chi ∈ smallCharacters ell R, f chi) = ∑ chi ∈ Finset.univ.erase oneChar, f chi := by
    apply Finset.sum_subset hs
    intro chi hchi hnot
    have hne : chi ≠ fun _ => 1 := (Finset.mem_erase.mp hchi).1
    simp only [f, coefficient_zero_outside ell m R h hh j chi hne hnot, zero_mul]
  have hone : f oneChar = UnitFourier.coefficient ell m R h j (fun _ => 1) := by
    simp [f, oneChar, value]
  calc
    square ell m R h j u = ∑ chi, f chi := (actual_coefficient_inversion ell m R h j u).symm
    _ = (∑ chi ∈ Finset.univ.erase oneChar, f chi) + f oneChar :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ oneChar)).symm
    _ = UnitFourier.coefficient ell m R h j (fun _ => 1) + ∑ chi ∈ smallCharacters ell R, f chi := by
      rw [← hsub, hone]
      ring
    _ = _ := by rw [Finset.sum_coe_sort (smallCharacters ell R) f]

/-- Exact arithmetic-ratio average, before any inequality or exceptional
set estimate is applied. -/
theorem source_average_eq (m : ℝ) (R : ℕ) (h : ∀ p, Fin k → ZMod (ell p))
    (hh : ∀ p, Function.Injective (h p)) (j : Fin k) (sources : Finset ℕ)
    (hs : ∀ p ∈ sources, p.Coprime (modulus ell))
    (q : ℕ) (hq : q.Coprime (modulus ell)) :
    (∑ p : sources, square ell m R h j
      (unitPoint ell p (hs p p.property) / unitPoint ell q hq)) =
      (sources.card : ℂ) * UnitFourier.coefficient ell m R h j (fun _ => 1) +
        ProductPrimeMeanSquare.sourceError ell R
          (fun chi => UnitFourier.coefficient ell m R h j chi.val) sources q := by
  simp_rw [truncated_inversion ell m R h hh j, value_ratio]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_comm]
  unfold ProductPrimeMeanSquare.sourceError
  apply Finset.sum_congr rfl
  intro chi _hchi
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- The prime mean-square estimate now applies directly to the
discrepancy of the nonnegative anchored weights from their principal
source average. -/
theorem source_average_mean_square {t R : ℕ} {m : ℝ} (hm : 1 ≤ m)
    (ht : 2 ≤ t) (hR : 2 ≤ R)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10) (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus ell)) :
    (∑ q : targets, ‖(∑ p : sources, (realSquare ell m R h j
      (unitPoint ell p (hscop p p.property) / unitPoint ell q (htcop q q.property)) : ℂ)) -
        (sources.card : ℂ) * UnitFourier.coefficient ell m R h j (fun _ => 1)‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) *
        ((RestrictedProductNorm.energy (DivisorCoefficients.coefficient (k := k) m R ell) /
          UnitFourier.unitDensity ell) * δ) ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * sources.card) := by
  simp_rw [← square_eq_realSquare, source_average_eq ell m R h hh j sources hscop,
    add_sub_cancel_left]
  exact ProductPrimeMeanSquare.actual_source_error_mean_square ell hm ht hR hH hinj hRQ hell
    h hh j hδ0 hδ1 hlocal X Y hX hY sources targets hsources htargets hscop htcop

end Erdos4.AnchoredFourierAverage
