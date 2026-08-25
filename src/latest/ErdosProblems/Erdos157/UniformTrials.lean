import ErdosProblems.Erdos157.Masks

/-! Uniform independent trials from a surjective finite additive homomorphism. -/

namespace Erdos157.Elementary.UniformTrials

variable {A G : Type*} [AddCommGroup A] [AddCommGroup G] [Fintype A] [Fintype G]
    [DecidableEq G]

def missed {n : ℕ} (f : A →+ (Fin n → G)) (s : Finset G) : Finset A :=
  Finset.univ.filter (fun a => ∀ j, f a j ∉ s)

theorem missed_card {n : ℕ} (f : A →+ (Fin n → G)) (hf : Function.Surjective f) (s : Finset G) :
    (missed f s).card * Fintype.card G ^ n = Fintype.card A * (Fintype.card G - s.card) ^ n := by
  have h := Masks.card_hom_preimage_mul f hf (Fintype.piFinset (fun _ : Fin n => sᶜ))
  simpa only [Fintype.mem_piFinset, Finset.mem_compl, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_piFinset_const, Finset.card_compl, missed] using h

theorem missed_density {n : ℕ} (f : A →+ (Fin n → G)) (hf : Function.Surjective f) (s : Finset G) :
    ((missed f s).card : ℝ) / Fintype.card A = (1 - (s.card : ℝ) / Fintype.card G) ^ n := by
  have h := missed_card f hf s
  have hsub : s.card ≤ Fintype.card G := Finset.card_le_univ s
  have hr : ((missed f s).card : ℝ) * (Fintype.card G : ℝ) ^ n =
      (Fintype.card A : ℝ) * ((Fintype.card G : ℝ) - s.card) ^ n := by exact_mod_cast h
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hratio : 1 - (s.card : ℝ) / Fintype.card G =
      ((Fintype.card G : ℝ) - s.card) / Fintype.card G := by rw [sub_div, div_self hG.ne']
  rw [hratio, div_pow]
  apply (div_eq_div_iff hA.ne' (pow_ne_zero _ hG.ne')).mpr
  simpa only [mul_comm] using hr

theorem missed_density_le_exp {n : ℕ} (f : A →+ (Fin n → G)) (hf : Function.Surjective f) (s : Finset G) :
    ((missed f s).card : ℝ) / Fintype.card A ≤
      Real.exp (-(n : ℝ) * ((s.card : ℝ) / Fintype.card G)) := by
  rw [missed_density f hf s]
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hsub : (s.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ s
  have hnonneg : 0 ≤ 1 - (s.card : ℝ) / Fintype.card G := by
    have h := (div_le_one hG).mpr hsub
    linarith
  calc
    _ ≤ (Real.exp (-((s.card : ℝ) / Fintype.card G))) ^ n :=
      pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg _) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

section VaryingCoordinates

variable {I : Type*} {A' G' : I → Type*} [∀ i, AddCommGroup (A' i)] [∀ i, AddCommGroup (G' i)]

def piTrials {n : ℕ} (f : ∀ i, A' i →+ (Fin n → G' i)) :
    (∀ i, A' i) →+ (Fin n → ∀ i, G' i) where
  toFun a j i := f i (a i) j
  map_zero' := by ext j i; exact congrFun (map_zero (f i)) j
  map_add' a b := by ext j i; exact congrFun (map_add (f i) (a i) (b i)) j

theorem piTrials_surjective {n : ℕ} (f : ∀ i, A' i →+ (Fin n → G' i))
    (hf : ∀ i, Function.Surjective (f i)) : Function.Surjective (piTrials f) := by
  intro y
  choose a ha using (fun i => hf i (fun j => y j i))
  refine ⟨a, ?_⟩
  funext j i
  exact congrFun (ha i) j

variable {T : I → Type*} [∀ i, DecidableEq (T i)]

def varyingMaskSums {n : ℕ} (t : ∀ i, Fin n → T i × T i × T i) :
    (∀ i, T i → G' i) →+ (Fin n → ∀ i, G' i) := piTrials (fun i => Masks.maskSums (t i))

theorem varyingMaskSums_surjective {n : ℕ} (t : ∀ i, Fin n → T i × T i × T i)
    (hcard : ∀ i j, 2 ≤ (Parabola.support (t i j)).card)
    (hdisjoint : ∀ i, Pairwise (fun j k => Disjoint (Parabola.support (t i j)) (Parabola.support (t i k)))) :
    Function.Surjective (varyingMaskSums (G' := G') t) :=
  piTrials_surjective _ (fun i => Masks.maskSums_surjective (t i) (hcard i) (hdisjoint i))

end VaryingCoordinates
end Erdos157.Elementary.UniformTrials
