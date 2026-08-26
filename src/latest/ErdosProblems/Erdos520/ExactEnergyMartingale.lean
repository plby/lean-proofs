import ErdosProblems.Erdos520.NormalizedEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# An exactly normalized Parseval energy martingale

The deterministic normalizer used here is the finite Euler product

`Z(y) = ∏_{p ≤ y} (1 + 1 / p)`.

Unlike normalization by `log y`, this makes the conditional evolution of the
inverse-square smooth energy exact.  No Mertens asymptotic is involved in the
martingale identity itself.
-/

/-! ## Exact finite Walsh Parseval -/

theorem WalshCoeff.fintypeAverage_eval_sq_eq_energy_one :
    ∀ {n : ℕ} (c : WalshCoeff n),
      fintypeAverage (fun omega => c.eval omega ^ 2) = c.energy 1
  | 0, .const c => by
      simp [fintypeAverage, WalshCoeff.eval, WalshCoeff.energy]
  | n + 1, .step c0 c1 => by
      rw [fintypeAverage_fin_succ]
      simp_rw [WalshCoeff.eval_cons_false, WalshCoeff.eval_cons_true]
      have hpoint (omega : Fin n → Bool) :
          ((c0.eval omega - c1.eval omega) ^ 2 +
              (c0.eval omega + c1.eval omega) ^ 2) / 2 =
            c0.eval omega ^ 2 + c1.eval omega ^ 2 := by ring
      simp_rw [hpoint]
      unfold fintypeAverage
      rw [Finset.sum_add_distrib, add_div]
      change fintypeAverage (fun omega => c0.eval omega ^ 2) +
          fintypeAverage (fun omega => c1.eval omega ^ 2) = _
      rw [fintypeAverage_eval_sq_eq_energy_one c0,
        fintypeAverage_eval_sq_eq_energy_one c1]
      simp [WalshCoeff.energy]

theorem mask_parseval {n : ℕ} (c : (Fin n → Bool) → ℝ) :
    fintypeAverage (fun omega => maskEval c omega ^ 2) = maskEnergy 1 c := by
  have heval : (WalshCoeff.ofMask c).eval = maskEval c := by
    funext omega
    exact WalshCoeff.eval_ofMask c omega
  rw [← heval, ← WalshCoeff.energy_ofMask 1 c]
  exact WalshCoeff.fintypeAverage_eval_sq_eq_energy_one _

theorem finsetWalsh_parseval_fin {n : ℕ} (c : Finset (Fin n) → ℝ) :
    fintypeAverage (fun omega => finsetWalshEval c omega ^ 2) =
      ∑ A, c A ^ 2 := by
  let e := maskSupportEquiv (Fin n)
  let c' : (Fin n → Bool) → ℝ := fun A => c (e A)
  have heval : maskEval c' = finsetWalshEval c := by
    funext omega
    unfold maskEval finsetWalshEval c'
    simp_rw [maskChar_eq_prod_support]
    exact e.sum_comp (fun A => c A * ∏ i ∈ A, cubeSign (omega i))
  have henergy : maskEnergy 1 c' = ∑ A, c A ^ 2 := by
    unfold maskEnergy c'
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.cast_one, one_pow, one_mul]
    exact e.sum_comp (fun A => c A ^ 2)
  rw [← heval, ← henergy]
  exact mask_parseval c'

theorem finsetWalsh_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) :
    fintypeAverage (fun omega => finsetWalshEval c omega ^ 2) =
      ∑ A, c A ^ 2 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let pointE : (ι → Bool) ≃ (Fin (Fintype.card ι) → Bool) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => Bool) e
  let subsetE : Finset ι ≃ Finset (Fin (Fintype.card ι)) := e.finsetCongr
  let c' : Finset (Fin (Fintype.card ι)) → ℝ := fun A => c (subsetE.symm A)
  have heval (omega : ι → Bool) :
      finsetWalshEval c' (pointE omega) = finsetWalshEval c omega := by
    unfold finsetWalshEval
    symm
    apply Fintype.sum_equiv subsetE
    intro A
    change c A * ∏ i ∈ A, cubeSign (omega i) =
      c (subsetE.symm (subsetE A)) *
        ∏ i ∈ subsetE A, cubeSign (pointE omega i)
    rw [subsetE.symm_apply_apply]
    rw [show subsetE A = Finset.map e.toEmbedding A by rfl, Finset.prod_map]
    apply congrArg (c A * ·)
    apply Finset.prod_congr rfl
    intro i _hi
    have hp : pointE omega (e i) = omega i := by
      change (Equiv.piCongrLeft
        (fun _ : Fin (Fintype.card ι) => Bool) e) omega (e i) = omega i
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    change cubeSign (omega i) = cubeSign (pointE omega (e i))
    rw [hp]
  have hsq : (∑ A, c' A ^ 2) = ∑ A, c A ^ 2 := by
    symm
    apply Fintype.sum_equiv subsetE
    intro A
    simp [c']
  calc
    fintypeAverage (fun omega => finsetWalshEval c omega ^ 2) =
        fintypeAverage
          ((fun omega => finsetWalshEval c' omega ^ 2) ∘ pointE) := by
      congr 1
      funext omega
      exact congrArg (· ^ 2) (heval omega).symm
    _ = fintypeAverage (fun omega => finsetWalshEval c' omega ^ 2) :=
      fintypeAverage_comp_equiv pointE _
    _ = ∑ A, c' A ^ 2 := finsetWalsh_parseval_fin c'
    _ = ∑ A, c A ^ 2 := hsq

theorem powersetWalsh_parseval {α : Type*} [DecidableEq α]
    (P : Finset α) (c : Finset α → ℝ) :
    fintypeAverage (fun eta => powersetWalshEval P c eta ^ 2) =
      ∑ A ∈ P.powerset, c A ^ 2 := by
  let c' : Finset P → ℝ := fun A =>
    c (A.map (Function.Embedding.subtype _))
  have heval : finsetWalshEval c' = powersetWalshEval P c := by
    funext eta
    unfold finsetWalshEval powersetWalshEval c'
    calc
      (∑ A : Finset P,
          c (A.map (Function.Embedding.subtype _)) *
            ∏ i ∈ A, cubeSign (eta i)) =
          ∑ A : Finset P,
            c (A.map (Function.Embedding.subtype _)) *
              finsetFiberCharacter P eta
                (A.map (Function.Embedding.subtype _)) := by
        apply Finset.sum_congr rfl
        intro A _hA
        rw [finsetFiberCharacter_map_subtype]
      _ = ∑ A ∈ P.powerset,
          c A * finsetFiberCharacter P eta A :=
        sum_finset_subtype_eq_sum_powerset P
          (fun A => c A * finsetFiberCharacter P eta A)
  rw [← heval, finsetWalsh_parseval]
  exact sum_finset_subtype_eq_sum_powerset P (fun A => c A ^ 2)

/-! ## Euler normalizers -/

/-- Exact deterministic second-moment normalizer through prime cutoff `y`. -/
noncomputable def primeEnergyNormalizer (y : ℕ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, (1 + (p : ℝ)⁻¹)

/-- The corresponding normalizer for a fresh block `(a,b]`. -/
noncomputable def freshPrimeEnergyNormalizer (a b : ℕ) : ℝ :=
  ∏ p ∈ freshPrimes a b, (1 + (p : ℝ)⁻¹)

theorem primeEnergyNormalizer_pos (y : ℕ) :
    0 < primeEnergyNormalizer y := by
  unfold primeEnergyNormalizer
  exact Finset.prod_pos fun p hp => by positivity

theorem freshPrimeEnergyNormalizer_pos (a b : ℕ) :
    0 < freshPrimeEnergyNormalizer a b := by
  unfold freshPrimeEnergyNormalizer
  exact Finset.prod_pos fun p hp => by positivity

theorem primeEnergyNormalizer_factor {a b : ℕ} (hab : a ≤ b) :
    primeEnergyNormalizer b =
      primeEnergyNormalizer a * freshPrimeEnergyNormalizer a b := by
  unfold primeEnergyNormalizer freshPrimeEnergyNormalizer
  rw [primesBelow_succ_eq_union_freshPrimes hab]
  exact Finset.prod_union (primesBelow_succ_disjoint_freshPrimes a b)

theorem sum_powerset_freshProduct_inv (a b : ℕ) :
    (∑ S ∈ (freshPrimes a b).powerset,
        ((freshProduct S : ℝ)⁻¹)) = freshPrimeEnergyNormalizer a b := by
  classical
  unfold freshPrimeEnergyNormalizer
  calc
    (∑ S ∈ (freshPrimes a b).powerset,
        ((freshProduct S : ℝ)⁻¹)) =
        ∑ S ∈ (freshPrimes a b).powerset,
          ∏ p ∈ S, ((p : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro S hS
      unfold freshProduct
      rw [Nat.cast_prod, Finset.prod_inv_distrib]
    _ = ∏ p ∈ freshPrimes a b, (1 + (p : ℝ)⁻¹) := by
      rw [Finset.prod_one_add]

/-! ## Exact fresh-fiber second moments -/

theorem freshFiberExpansion_parseval_integral
    (old : Omega) (z a b : ℕ) :
    (∫ eta, freshFiberExpansion old z a b eta ^ 2
        ∂freshCubeLaw a b) =
      ∑ S ∈ (freshPrimes a b).powerset,
        freshCoefficient old z a S ^ 2 := by
  unfold freshCubeLaw
  rw [integral_coin_eq_fintypeAverage]
  exact powersetWalsh_parseval (freshPrimes a b)
    (freshCoefficient old z a)

theorem finiteCoinAverage_ΨReal_sq
    (old : Omega) (z : ℝ) {a b : ℕ} (hab : a ≤ b) :
    fintypeAverage (fun eta : freshPrimes a b → Bool =>
        |ΨReal (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2) =
      ∑ S ∈ (freshPrimes a b).powerset,
        |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 := by
  have hpoint (eta : freshPrimes a b → Bool) :
      ΨReal (Function.updateFinset old (freshPrimes a b) eta) z b =
        freshFiberExpansion old ⌊z⌋₊ a b eta := by
    change Ψ (Function.updateFinset old (freshPrimes a b) eta) ⌊z⌋₊ b = _
    rw [← spliceFresh_eq_updateFinset old eta]
    change frozenSmoothTerminal old ⌊z⌋₊ eta = _
    exact frozenSmoothTerminal_eq_freshFiberExpansion old ⌊z⌋₊ hab eta
  simp_rw [hpoint, sq_abs]
  unfold freshFiberExpansion
  rw [powersetWalsh_parseval]
  apply Finset.sum_congr rfl
  intro S hS
  change freshCoefficient old ⌊z⌋₊ a S ^ 2 =
    realFreshCoefficient old z a S ^ 2
  rw [realFreshCoefficient_eq_freshCoefficient_floor]

/-! ## Exactly normalized energy -/

/-- Parseval energy divided by its exact finite Euler-product mean. -/
noncomputable def exactNormalizedEnergy (omega : Omega) (y : ℕ) : ℝ :=
  smoothEnergy omega y / primeEnergyNormalizer y

theorem exactNormalizedEnergy_nonneg (omega : Omega) (y : ℕ) :
    0 ≤ exactNormalizedEnergy omega y :=
  div_nonneg (smoothEnergy_nonneg omega y) (primeEnergyNormalizer_pos y).le

theorem stronglyMeasurable_exactNormalizedEnergy (y : ℕ) :
    StronglyMeasurable[Filtration.piFinset ((y + 1).primesBelow)]
      (fun omega : Omega => exactNormalizedEnergy omega y) := by
  exact (stronglyMeasurable_smoothEnergy y).div stronglyMeasurable_const

theorem integrable_exactNormalizedEnergy (y : ℕ) :
    Integrable (fun omega : Omega => exactNormalizedEnergy omega y) μ := by
  exact (integrable_smoothEnergy y).div_const _

theorem finiteCoinFiberIntegral_smoothEnergy
    (old : Omega) {a b : ℕ} (hab : a ≤ b) :
    finiteCoinFiberIntegral (freshPrimes a b)
        (fun omega : Omega => smoothEnergy omega b) old =
      freshPrimeEnergyNormalizer a b * smoothEnergy old a := by
  classical
  unfold finiteCoinFiberIntegral
  rw [integral_coin_eq_fintypeAverage]
  unfold fintypeAverage smoothEnergy
  have hfreshInt (eta : freshPrimes a b → Bool) :
      IntegrableOn
        (fun z : ℝ =>
          |ΨReal (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2 /
            z ^ 2)
        (Ioi (0 : ℝ)) :=
    integrableOn_ΨReal_sq_div_sq
      (Function.updateFinset old (freshPrimes a b) eta) b
  have hcoeffInt (S : Finset ℕ)
      (hS : S ∈ (freshPrimes a b).powerset) :
      IntegrableOn
        (fun z : ℝ =>
          |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 / z ^ 2)
        (Ioi (0 : ℝ)) :=
    integrableOn_realFreshCoefficient_sq_div_sq_of_mem old hS
  calc
    (∑ eta : freshPrimes a b → Bool,
          ∫ z in Ioi (0 : ℝ),
            |ΨReal
                (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2 /
              z ^ 2) /
          (Fintype.card (freshPrimes a b → Bool) : ℝ) =
        (∫ z in Ioi (0 : ℝ),
          ∑ eta : freshPrimes a b → Bool,
            |ΨReal
                (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2 /
              z ^ 2) /
          (Fintype.card (freshPrimes a b → Bool) : ℝ) := by
      rw [integral_finset_sum Finset.univ]
      intro eta heta
      exact hfreshInt eta
    _ = ∫ z in Ioi (0 : ℝ),
          (∑ eta : freshPrimes a b → Bool,
            |ΨReal
                (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2 /
              z ^ 2) /
            (Fintype.card (freshPrimes a b → Bool) : ℝ) := by
      rw [integral_div]
    _ = ∫ z in Ioi (0 : ℝ),
          (∑ S ∈ (freshPrimes a b).powerset,
            |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2) / z ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      have hparseval := finiteCoinAverage_ΨReal_sq old z hab
      unfold fintypeAverage at hparseval
      calc
        (∑ eta : freshPrimes a b → Bool,
              |ΨReal
                  (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2 /
                z ^ 2) /
            (Fintype.card (freshPrimes a b → Bool) : ℝ) =
            ((∑ eta : freshPrimes a b → Bool,
                |ΨReal
                    (Function.updateFinset old (freshPrimes a b) eta) z b| ^ 2) /
              (Fintype.card (freshPrimes a b → Bool) : ℝ)) / z ^ 2 := by
          rw [← Finset.sum_div]
          ring
        _ = (∑ S ∈ (freshPrimes a b).powerset,
              |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2) / z ^ 2 := by
          rw [hparseval]
    _ = ∑ S ∈ (freshPrimes a b).powerset,
          ∫ z in Ioi (0 : ℝ),
            |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 / z ^ 2 := by
      rw [← integral_finset_sum (freshPrimes a b).powerset]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        dsimp only
        rw [Finset.sum_div]
      · intro S hS
        exact hcoeffInt S hS
    _ = ∑ S ∈ (freshPrimes a b).powerset,
          ((freshProduct S : ℝ)⁻¹) * smoothEnergy old a := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSsub : S ⊆ freshPrimes a b := Finset.mem_powerset.mp hS
      have hprime : ∀ p ∈ S, p.Prime := fun p hp =>
        (mem_freshPrimes.mp (hSsub hp)).1
      have hd : 0 < freshProduct S := freshProduct_pos_of_primes hprime
      simpa only [smoothEnergy] using!
        integral_ΨReal_div_mul_inv_sq_Ioi old a hd
    _ = freshPrimeEnergyNormalizer a b * smoothEnergy old a := by
      rw [← Finset.sum_mul, sum_powerset_freshProduct_inv]

theorem finiteCoinFiberIntegral_exactNormalizedEnergy
    (old : Omega) {a b : ℕ} (hab : a ≤ b) :
    finiteCoinFiberIntegral (freshPrimes a b)
        (fun omega : Omega => exactNormalizedEnergy omega b) old =
      exactNormalizedEnergy old a := by
  unfold finiteCoinFiberIntegral exactNormalizedEnergy
  rw [integral_div]
  change
    finiteCoinFiberIntegral (freshPrimes a b)
          (fun omega : Omega => smoothEnergy omega b) old /
        primeEnergyNormalizer b =
      smoothEnergy old a / primeEnergyNormalizer a
  rw [finiteCoinFiberIntegral_smoothEnergy old hab,
    primeEnergyNormalizer_factor hab]
  have hZa : primeEnergyNormalizer a ≠ 0 :=
    (primeEnergyNormalizer_pos a).ne'
  have hZfresh : freshPrimeEnergyNormalizer a b ≠ 0 :=
    (freshPrimeEnergyNormalizer_pos a b).ne'
  field_simp

theorem stronglyMeasurable_exactNormalizedEnergy_union
    {a b : ℕ} (hab : a ≤ b) :
    StronglyMeasurable[Filtration.piFinset
      ((a + 1).primesBelow ∪ freshPrimes a b)]
        (fun omega : Omega => exactNormalizedEnergy omega b) := by
  rw [← primesBelow_succ_eq_union_freshPrimes hab]
  exact stronglyMeasurable_exactNormalizedEnergy b

/-- Exact conditional martingale identity between arbitrary prime cutoffs. -/
theorem condExp_exactNormalizedEnergy
    {a b : ℕ} (hab : a ≤ b) :
    μ[(fun omega : Omega => exactNormalizedEnergy omega b) |
        Filtration.piFinset ((a + 1).primesBelow)] =ᵐ[μ]
      fun omega => exactNormalizedEnergy omega a := by
  have hfiber := freshPrimeFiberIntegral_ae_eq_condExp
    (stronglyMeasurable_exactNormalizedEnergy_union hab)
  exact hfiber.symm.trans <| ae_of_all μ fun old =>
    finiteCoinFiberIntegral_exactNormalizedEnergy old hab

/-- Filtration which reveals all prime signs at most the current cutoff. -/
noncomputable def primeEnergyFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace Omega) where
  seq y := Filtration.piFinset ((y + 1).primesBelow)
  mono' a b hab := by
    apply Filtration.piFinset.mono
    intro p hp
    have hpinfo := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr
      ⟨hpinfo.1.trans_le (Nat.add_le_add_right hab 1), hpinfo.2⟩
  le' y := Filtration.piFinset.le _

@[simp] theorem primeEnergyFiltration_apply (y : ℕ) :
    primeEnergyFiltration y =
      Filtration.piFinset ((y + 1).primesBelow) := rfl

theorem stronglyAdapted_exactNormalizedEnergy :
    StronglyAdapted primeEnergyFiltration
      (fun y omega => exactNormalizedEnergy omega y) := by
  intro y
  exact stronglyMeasurable_exactNormalizedEnergy y

/-- The exactly normalized inverse-square smooth energy is a genuine
martingale, not merely an asymptotic supermartingale. -/
theorem martingale_exactNormalizedEnergy :
    Martingale (fun y omega => exactNormalizedEnergy omega y)
      primeEnergyFiltration μ := by
  apply martingale_nat stronglyAdapted_exactNormalizedEnergy
    integrable_exactNormalizedEnergy
  intro y
  exact (condExp_exactNormalizedEnergy (Nat.le_succ y)).symm

end Problem520
end Erdos
