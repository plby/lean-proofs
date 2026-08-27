import ErdosProblems.Erdos4.FGKMTTranslatedCenterLaw
import ErdosProblems.Erdos4.FGKMTFullTranslatedTuples

/-! Exact target incidences of the normalized translated center laws. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding AnchoredFourierAverage

namespace FiniteLaw

theorem prob_congr_iff {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (E F : Ω → Prop) (h : ∀ o, E o ↔ F o) : μ.prob E = μ.prob F := by
  unfold prob
  apply Finset.sum_congr rfl
  intro o _
  simp only [h o]

theorem prob_range_injective {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FiniteLaw Ω) (f : I → Ω) (hf : Function.Injective f) :
    μ.prob (fun o => ∃ i, f i = o) = ∑ i, μ.weight (f i) := by
  rw [prob_eq_mean]
  simp only [mean, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter (fun o => ∃ i, f i = o)) = Finset.univ.image f := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [hs, Finset.sum_image]
  intro i _ j _ hij
  exact hf hij

end FiniteLaw

variable {k : ℕ}

def translatedAnchorCenter (h : Fin k → ℕ) {p Y q : ℕ} (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y) (i : Fin k) : TranslatedCenter Y :=
  ⟨q + Y - h i * p, (translated_anchor_mem h hq0 hqY hshift i).1⟩

theorem translatedAnchorCenter_injective (h : Fin k → ℕ) (hinj : Function.Injective h)
    {p Y q : ℕ} (hp : 0 < p) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y) :
    Function.Injective (translatedAnchorCenter h hq0 hqY hshift) := by
  intro i j hij
  have hv := congrArg Subtype.val hij
  change q + Y - h i * p = q + Y - h j * p at hv
  have hi := hshift i
  have hj := hshift j
  have hm : h i * p = h j * p := by omega
  exact hinj (mul_right_cancel₀ hp.ne' hm)

theorem mem_translatedEdge_iff_anchor (h : Fin k → ℕ) {p Y q : ℕ}
    (hq0 : 1 ≤ q) (hqY : q ≤ Y) (hshift : ∀ i, h i * p ≤ Y)
    (n : TranslatedCenter Y) :
    q ∈ translatedEdge h p Y n.val ↔
      ∃ i, translatedAnchorCenter h hq0 hqY hshift i = n := by
  constructor
  · intro hq
    obtain ⟨_, _, i, hi⟩ := (mem_translatedEdge h p Y n.val q).mp hq
    refine ⟨i, Subtype.ext ?_⟩
    change q + Y - h i * p = n.val
    omega
  · rintro ⟨i, rfl⟩
    exact (translated_anchor_mem h hq0 hqY hshift i).2

theorem translatedCenter_incidence_eq (h : Fin k → ℕ) (hinj : Function.Injective h)
    {p Y q : ℕ} (hp : 0 < p) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y) (μ : FiniteLaw (TranslatedCenter Y)) :
    μ.prob (fun n => q ∈ translatedEdge h p Y n.val) =
      ∑ i : Fin k, μ.weight (translatedAnchorCenter h hq0 hqY hshift i) := by
  rw [μ.prob_congr_iff _ _ (mem_translatedEdge_iff_anchor h hq0 hqY hshift)]
  exact μ.prob_range_injective _ (translatedAnchorCenter_injective h hinj hp hq0 hqY hshift)

theorem translatedCenter_incidence_le (h : Fin k → ℕ) (hinj : Function.Injective h)
    {p Y q : ℕ} (hp : 0 < p) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y) (μ : FiniteLaw (TranslatedCenter Y))
    {ω : ℝ} (hω : ∀ n, μ.weight n ≤ ω) :
    μ.prob (fun n => q ∈ translatedEdge h p Y n.val) ≤ (k : ℝ) * ω := by
  rw [translatedCenter_incidence_eq h hinj hp hq0 hqY hshift]
  calc
    _ ≤ ∑ _i : Fin k, ω := Finset.sum_le_sum (fun i _ => hω _)
    _ = _ := by simp

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

noncomputable def rationalBaseIncidence (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) : ℝ :=
  (rationalCenterLaw ell₀ ell₁ b R h hY p).prob
    (fun n => q ∈ translatedEdge h p Y n.val)

theorem rationalBaseIncidence_nonneg (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) :
    0 ≤ rationalBaseIncidence ell₀ ell₁ b R h hY p q :=
  (rationalCenterLaw ell₀ ell₁ b R h hY p).prob_nonneg _

theorem rationalBaseIncidence_eq_full (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) (hq0 : 1 ≤ q) (hqY : q ≤ Y) :
    rationalBaseIncidence ell₀ ell₁ b R h hY p q =
      (rationalCenterLaw ell₀ ell₁ b R h hY p).prob
        (fun n => q + Y ∈ translatedSites h p n.val) :=
  (rationalCenterLaw ell₀ ell₁ b R h hY p).prob_congr_iff _ _
    (fun n => mem_translatedEdge_iff_sites h p Y n.val hq0 hqY)

theorem rationalBaseIncidence_eq_unitWeight (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hinj : Function.Injective h)
    (hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) (hp0 : 0 < p) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y)
    (hp : p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) :
    rationalBaseIncidence ell₀ ell₁ b R h hY p q =
      aggregateUnitWeight ell₀ ell₁ b R
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))
        (unitPoint (Sum.elim ell₀ ell₁) p hp / unitPoint (Sum.elim ell₀ ell₁) q hq) /
          maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
  unfold rationalBaseIncidence
  rw [translatedCenter_incidence_eq h hinj hp0 hq0 hqY hshift]
  simp_rw [rationalCenterLaw_weight ell₀ ell₁ b R h hY p hZ]
  change (∑ i : Fin k,
    maskedTranslatedWeight ell₀ ell₁ b R h Y p (q + Y - h i * p) /
      maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) = _
  rw [← Finset.sum_div]
  apply congrArg (fun s : ℝ => s / maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
  unfold aggregateUnitWeight
  apply Finset.sum_congr rfl
  intro i _
  exact maskedTranslatedWeight_anchor ell₀ ell₁ b R h hlarge Y p q hshift hp hq i

end Erdos4.FGKMT
