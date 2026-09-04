import ErdosProblems.Erdos520.Bonami
import ErdosProblems.Erdos520.FreshExpansion
import Mathlib.Probability.UniformOn

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-- The finite subset encoded by a Boolean mask. -/
def maskSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => A i = true

/-- Boolean masks on a finite type are equivalent to its finite subsets. -/
def maskSupportEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun := maskSupport
  invFun A i := decide (i ∈ A)
  left_inv A := by
    funext i
    simp only [maskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases A i <;> simp
  right_inv A := by
    ext i
    simp [maskSupport]

/-- `maskDegree` counts the coordinates selected by the mask. -/
lemma maskDegree_eq_sum_indicator :
    ∀ {n : ℕ} (A : Fin n → Bool),
      maskDegree A = ∑ i, if A i then 1 else 0
  | 0, A => by simp [maskDegree]
  | n + 1, A => by
      rw [maskDegree, Fin.sum_univ_succ]
      rw [maskDegree_eq_sum_indicator (Fin.tail A)]
      rfl

/-- `maskChar` is the usual product of the selected coordinate signs. -/
lemma maskChar_eq_prod_indicator :
    ∀ {n : ℕ} (A omega : Fin n → Bool),
      maskChar A omega =
        ∏ i, if A i then cubeSign (omega i) else 1
  | 0, A, omega => by simp [maskChar]
  | n + 1, A, omega => by
      rw [maskChar, Fin.prod_univ_succ]
      rw [maskChar_eq_prod_indicator (Fin.tail A) (Fin.tail omega)]
      rfl

lemma maskDegree_eq_card_support {n : ℕ} (A : Fin n → Bool) :
    maskDegree A = (maskSupport A).card := by
  rw [maskDegree_eq_sum_indicator, maskSupport, Finset.card_filter]

lemma maskChar_eq_prod_support {n : ℕ} (A omega : Fin n → Bool) :
    maskChar A omega = ∏ i ∈ maskSupport A, cubeSign (omega i) := by
  rw [maskChar_eq_prod_indicator]
  simp [maskSupport, Finset.prod_filter]

/-- A Walsh polynomial indexed by all finite subsets of a finite type. -/
noncomputable def finsetWalshEval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (omega : ι → Bool) : ℝ :=
  ∑ A, c A * ∏ i ∈ A, cubeSign (omega i)

/-- The coefficient energy occurring in the coefficient-weighted Bonami bound. -/
noncomputable def finsetWalshEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (c : Finset ι → ℝ) : ℝ :=
  ∑ A, ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2

/-- Coefficient-weighted Bonami for subsets of `Fin n`. -/
theorem finset_bonami_fin (r : ℕ) (hr : 1 ≤ r) {n : ℕ}
    (c : Finset (Fin n) → ℝ) :
    evenNormSq r (finsetWalshEval c) ≤ finsetWalshEnergy r c := by
  let e := maskSupportEquiv (Fin n)
  let c' : (Fin n → Bool) → ℝ := fun A => c (e A)
  have heval : maskEval c' = finsetWalshEval c := by
    funext omega
    unfold maskEval finsetWalshEval c'
    simp_rw [maskChar_eq_prod_support]
    exact e.sum_comp (fun A => c A * ∏ i ∈ A, cubeSign (omega i))
  have henergy : maskEnergy r c' = finsetWalshEnergy r c := by
    unfold maskEnergy finsetWalshEnergy c'
    simp_rw [maskDegree_eq_card_support]
    exact e.sum_comp
      (fun A => ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2)
  rw [← heval, ← henergy]
  exact mask_bonami r hr c'

lemma fintypeAverage_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (g : κ → ℝ) :
    fintypeAverage (g ∘ e) = fintypeAverage g := by
  unfold fintypeAverage
  change (∑ i, g (e i)) / (Fintype.card ι : ℝ) =
    (∑ i, g i) / (Fintype.card κ : ℝ)
  rw [e.sum_comp]
  rw [Fintype.card_congr e]

lemma evenNormSq_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℕ) (e : ι ≃ κ) (g : κ → ℝ) :
    evenNormSq r (g ∘ e) = evenNormSq r g := by
  unfold evenNormSq
  congr 1
  exact fintypeAverage_comp_equiv e (fun x => |g x| ^ (2 * r))

/-- Coefficient-weighted Bonami for subsets of an arbitrary finite type. -/
theorem finset_bonami {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (hr : 1 ≤ r) (c : Finset ι → ℝ) :
    evenNormSq r (finsetWalshEval c) ≤ finsetWalshEnergy r c := by
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
      change (Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => Bool) e)
          omega (e i) = omega i
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    change cubeSign (omega i) = cubeSign (pointE omega (e i))
    rw [hp]
  have henergy : finsetWalshEnergy r c' = finsetWalshEnergy r c := by
    unfold finsetWalshEnergy
    symm
    apply Fintype.sum_equiv subsetE
    intro A
    change ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2 =
      ((2 * r - 1 : ℕ) : ℝ) ^ (subsetE A).card *
        c (subsetE.symm (subsetE A)) ^ 2
    rw [subsetE.symm_apply_apply]
    rw [show subsetE A = Finset.map e.toEmbedding A by rfl, Finset.card_map]
  have hnorm :
      evenNormSq r (finsetWalshEval c) =
        evenNormSq r (finsetWalshEval c') := by
    calc
      evenNormSq r (finsetWalshEval c) =
          evenNormSq r (finsetWalshEval c' ∘ pointE) := by
            congr 1
            funext omega
            exact (heval omega).symm
      _ = evenNormSq r (finsetWalshEval c') :=
        evenNormSq_comp_equiv r pointE (finsetWalshEval c')
  rw [hnorm, ← henergy]
  exact finset_bonami_fin r hr c'

/-- Reindex all subsets of a finset subtype as the ambient powerset. -/
lemma sum_finset_subtype_eq_sum_powerset {α M : Type*} [AddCommMonoid M]
    (P : Finset α) (F : Finset α → M) :
    (∑ A : Finset P, F (A.map (Function.Embedding.subtype _))) =
      ∑ A ∈ P.powerset, F A := by
  classical
  let e := Equiv.finsetSubtypeComm (fun x : α => x ∈ P)
  let : Fintype {A : Finset α // ∀ x ∈ A, x ∈ P} :=
    Fintype.ofEquiv (Finset P) e
  calc
    (∑ A : Finset P, F (A.map (Function.Embedding.subtype _))) =
        ∑ A : {A : Finset α // ∀ x ∈ A, x ∈ P}, F A := by
          exact e.sum_comp (fun A => F A)
    _ = ∑ A ∈ P.powerset, F A := by
      symm
      exact Finset.sum_subtype P.powerset (fun A => by
        simp only [Finset.mem_powerset, Finset.subset_iff]) F

/-- Character of an ambient subset, evaluated on signs indexed by `P`.
Outside `P` it is defined to be trivial; only subsets in `P.powerset` are
used below. -/
def finsetFiberCharacter {α : Type*} [DecidableEq α] (P : Finset α)
    (eta : P → Bool) (A : Finset α) : ℝ :=
  ∏ i ∈ A, if hi : i ∈ P then cubeSign (eta ⟨i, hi⟩) else 1

lemma finsetFiberCharacter_map_subtype {α : Type*} [DecidableEq α]
    (P : Finset α) (eta : P → Bool) (A : Finset P) :
    finsetFiberCharacter P eta (A.map (Function.Embedding.subtype _)) =
      ∏ i ∈ A, cubeSign (eta i) := by
  unfold finsetFiberCharacter
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [i.property]

/-- A Walsh polynomial on the finite cube indexed by `P`, written in the
ambient `P.powerset` notation used by the number-theoretic model. -/
noncomputable def powersetWalshEval {α : Type*} [DecidableEq α]
    (P : Finset α) (c : Finset α → ℝ) (eta : P → Bool) : ℝ :=
  ∑ A ∈ P.powerset, c A * finsetFiberCharacter P eta A

/-- The coefficient-weighted energy of an ambient-powerset Walsh
polynomial. -/
noncomputable def powersetWalshEnergy {α : Type*} [DecidableEq α]
    (r : ℕ) (P : Finset α) (c : Finset α → ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2

/-- Coefficient-weighted Bonami in ambient powerset notation. -/
theorem powerset_bonami {α : Type*} [DecidableEq α]
    (r : ℕ) (hr : 1 ≤ r) (P : Finset α) (c : Finset α → ℝ) :
    evenNormSq r (powersetWalshEval P c) ≤
      powersetWalshEnergy r P c := by
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
  have henergy : finsetWalshEnergy r c' = powersetWalshEnergy r P c := by
    unfold finsetWalshEnergy powersetWalshEnergy c'
    calc
      (∑ A : Finset P,
          ((2 * r - 1 : ℕ) : ℝ) ^ A.card *
            c (A.map (Function.Embedding.subtype _)) ^ 2) =
          ∑ A : Finset P,
            ((2 * r - 1 : ℕ) : ℝ) ^
                (A.map (Function.Embedding.subtype _)).card *
              c (A.map (Function.Embedding.subtype _)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro A _hA
          rw [Finset.card_map]
      _ = ∑ A ∈ P.powerset,
          ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2 :=
        sum_finset_subtype_eq_sum_powerset P
          (fun A => ((2 * r - 1 : ℕ) : ℝ) ^ A.card * c A ^ 2)
  rw [← heval, ← henergy]
  exact finset_bonami r hr c'

/-- Equation (18) with the old coordinates frozen and only the fresh signs
left as variables. -/
noncomputable def freshFiberExpansion
    (old : Omega) (z a b : ℕ) (eta : freshPrimes a b → Bool) : ℝ :=
  powersetWalshEval (freshPrimes a b) (freshCoefficient old z a) eta

/-- Equation (19) on the conditional fresh-coordinate fiber. -/
theorem freshFiberExpansion_bonami (r : ℕ) (hr : 1 ≤ r)
    (old : Omega) (z a b : ℕ) :
    evenNormSq r (freshFiberExpansion old z a b) ≤
      ∑ A ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ A.card *
          freshCoefficient old z a A ^ 2 := by
  simpa only [freshFiberExpansion, powersetWalshEnergy] using!
    powerset_bonami r hr (freshPrimes a b) (freshCoefficient old z a)

/-- Integration against a finite product of fair coins is normalized finite
averaging. -/
theorem integral_coin_eq_fintypeAverage {α : Type*} [DecidableEq α]
    {P : Finset α} (g : (P → Bool) → ℝ) :
    ∫ eta, g eta ∂Measure.pi (fun _ : P => coin) = fintypeAverage g := by
  rw [MeasureTheory.integral_fintype]
  · have hmass (eta : P → Bool) :
        (Measure.pi (fun _ : P => coin)).real {eta} =
          1 / (Fintype.card (P → Bool) : ℝ) := by
      rw [Measure.real, Measure.pi_singleton]
      have hcoin (i : P) : coin {eta i} = (1 / 2 : ℝ≥0∞) := by
        cases eta i <;> simp [coin]
      simp_rw [hcoin]
      rw [Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow]
      simp only [Fintype.card_fun, Fintype.card_bool]
      norm_num
      rw [one_div_pow]
      simp [one_div]
    unfold fintypeAverage
    simp_rw [hmass, smul_eq_mul]
    simp_rw [show ∀ eta : P → Bool,
      1 / (Fintype.card (P → Bool) : ℝ) * g eta =
        g eta / (Fintype.card (P → Bool) : ℝ) by intro eta; ring]
    rw [Finset.sum_div]
  · exact Integrable.of_finite

/-- Integral form of equation (19) on the finite fresh-coordinate product
space. -/
theorem freshFiberExpansion_bonami_integral (r : ℕ) (hr : 1 ≤ r)
    (old : Omega) (z a b : ℕ) :
    (∫ eta, |freshFiberExpansion old z a b eta| ^ (2 * r)
        ∂Measure.pi (fun _ : freshPrimes a b => coin)) ^
          (1 / (r : ℝ)) ≤
      ∑ A ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ A.card *
          freshCoefficient old z a A ^ 2 := by
  rw [integral_coin_eq_fintypeAverage]
  exact freshFiberExpansion_bonami r hr old z a b

/-- The fresh Walsh polynomial on the original infinite sample space, with
its old-coordinate coefficients frozen at `old`. -/
noncomputable def frozenFreshWalshExpansion
    (old : Omega) (z a b : ℕ) (omega : Omega) : ℝ :=
  ∑ A ∈ (freshPrimes a b).powerset,
    freshCharacter omega A * freshCoefficient old z a A

@[simp] lemma cubeSign_apply_eq_ε (omega : Omega) (p : ℕ) :
    cubeSign (omega p) = ε omega p := by
  rfl

lemma finsetFiberCharacter_restrict {P S : Finset ℕ} (hS : S ⊆ P)
    (omega : Omega) :
    finsetFiberCharacter P (P.restrict omega) S =
      freshCharacter omega S := by
  unfold finsetFiberCharacter freshCharacter
  apply Finset.prod_congr rfl
  intro p hp
  rw [dif_pos (hS hp)]
  rfl

/-- Restricting a global sign configuration to the fresh block evaluates the
same frozen Walsh polynomial. -/
theorem freshFiberExpansion_restrict (old omega : Omega) (z a b : ℕ) :
    freshFiberExpansion old z a b ((freshPrimes a b).restrict omega) =
      frozenFreshWalshExpansion old z a b omega := by
  unfold freshFiberExpansion powersetWalshEval frozenFreshWalshExpansion
  apply Finset.sum_congr rfl
  intro A hA
  rw [finsetFiberCharacter_restrict (Finset.mem_powerset.mp hA)]
  ring

@[simp] theorem frozenFreshWalshExpansion_self (omega : Omega)
    (z a b : ℕ) :
    frozenFreshWalshExpansion omega z a b omega =
      freshWalshExpansion omega z a b := by
  rfl

/-- Global-`μ` form of equation (19), with the old coefficients frozen.  It
is the finite conditional-fiber estimate pulled back along restriction to
the fresh coordinates. -/
theorem frozenFreshWalshExpansion_bonami_integral
    (r : ℕ) (hr : 1 ≤ r) (old : Omega) (z a b : ℕ) :
    (∫ omega, |frozenFreshWalshExpansion old z a b omega| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤
      ∑ A ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ A.card *
          freshCoefficient old z a A ^ 2 := by
  let P := freshPrimes a b
  let g : (P → Bool) → ℝ := fun eta =>
    |freshFiberExpansion old z a b eta| ^ (2 * r)
  have hg : AEStronglyMeasurable g (Measure.pi (fun _ : P => coin)) :=
    (measurable_of_finite g).aestronglyMeasurable
  have hrestrict :
      (∫ omega, g (P.restrict omega) ∂μ) =
        ∫ eta, g eta ∂Measure.pi (fun _ : P => coin) := by
    simpa only [μ] using!
      (integral_restrict_infinitePi (μ := fun _ : ℕ => coin) hg)
  have heq :
      (∫ omega, |frozenFreshWalshExpansion old z a b omega| ^ (2 * r) ∂μ) =
        ∫ omega, g (P.restrict omega) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ fun omega => by
      unfold g P
      change |frozenFreshWalshExpansion old z a b omega| ^ (2 * r) =
        |freshFiberExpansion old z a b
          ((freshPrimes a b).restrict omega)| ^ (2 * r)
      rw [freshFiberExpansion_restrict]
  rw [heq, hrestrict]
  exact freshFiberExpansion_bonami_integral r hr old z a b

end Problem520
end Erdos
