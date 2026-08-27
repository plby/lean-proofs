import ErdosProblems.Erdos4.LocalCharacterMatrix

/-! Exact small-prime mask counts; the shifts need not be distinct modulo the prime. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {p k : ℕ} [Fact p.Prime]

def SmallPrimeGood (h : Fin k → ZMod p) (x : ZMod p) : Prop := ∀ i, x + h i ≠ 0

def SmallAnchorGood (h : Fin k → ZMod p) (j : Fin k) (u : (ZMod p)ˣ) : Prop :=
  ∀ i, 1 + (h i - h j) * (u : ZMod p) ≠ 0

def smallAnchorCenter (h : Fin k → ZMod p) (j : Fin k) (u : (ZMod p)ˣ) : ZMod p :=
  (↑(u⁻¹) : ZMod p) - h j

theorem smallAnchorCenter_mul (h : Fin k → ZMod p) (j i : Fin k) (u : (ZMod p)ˣ) :
    (smallAnchorCenter h j u + h i) * (u : ZMod p) = 1 + (h i - h j) * (u : ZMod p) := by
  have hu : (↑(u⁻¹) : ZMod p) * (u : ZMod p) = 1 := u.inv_val
  unfold smallAnchorCenter
  calc
    _ = (↑(u⁻¹) : ZMod p) * (u : ZMod p) + (h i - h j) * (u : ZMod p) := by ring
    _ = _ := by rw [hu]

theorem smallAnchorGood_iff (h : Fin k → ZMod p) (j : Fin k) (u : (ZMod p)ˣ) :
    SmallAnchorGood h j u ↔ SmallPrimeGood h (smallAnchorCenter h j u) := by
  constructor
  · intro hu i hz
    have hh := smallAnchorCenter_mul h j i u
    rw [hz, zero_mul] at hh
    exact hu i hh.symm
  · intro hu i hz
    have hh : (smallAnchorCenter h j u + h i) * (u : ZMod p) = 0 := by
      rw [smallAnchorCenter_mul, hz]
    exact hu i ((mul_eq_zero.mp hh).resolve_right u.ne_zero)

theorem smallAnchorCenter_injective (h : Fin k → ZMod p) (j : Fin k) :
    Function.Injective (smallAnchorCenter h j) := by
  intro u v huv
  apply inv_injective
  apply Units.ext
  change (↑(u⁻¹) : ZMod p) - h j = (↑(v⁻¹) : ZMod p) - h j at huv
  exact sub_left_inj.mp huv

theorem smallAnchorCenter_surjective_good (h : Fin k → ZMod p) (j : Fin k)
    (x : ZMod p) (hx : SmallPrimeGood h x) :
    ∃ u : (ZMod p)ˣ, SmallAnchorGood h j u ∧ smallAnchorCenter h j u = x := by
  let u : (ZMod p)ˣ := (Units.mk0 (x + h j) (hx j))⁻¹
  have heq : smallAnchorCenter h j u = x := by simp [smallAnchorCenter, u]
  refine ⟨u, (smallAnchorGood_iff h j u).mpr ?_, heq⟩
  rwa [heq]

noncomputable def smallPrimeGoodStates (h : Fin k → ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (SmallPrimeGood h)

noncomputable def smallAnchorGoodStates (h : Fin k → ZMod p) (j : Fin k) : Finset ((ZMod p)ˣ) :=
  Finset.univ.filter (SmallAnchorGood h j)

theorem smallAnchorGoodStates_card (h : Fin k → ZMod p) (j : Fin k) :
    (smallAnchorGoodStates h j).card = (smallPrimeGoodStates h).card := by
  apply Finset.card_bij (fun u _ => smallAnchorCenter h j u)
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (smallAnchorGood_iff h j u).mp (Finset.mem_filter.mp hu).2⟩
  · intro u hu v hv huv
    exact smallAnchorCenter_injective h j huv
  · intro x hx
    obtain ⟨u, hu, heq⟩ := smallAnchorCenter_surjective_good h j x (Finset.mem_filter.mp hx).2
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, heq⟩

noncomputable def smallPresieveDensity (h : Fin k → ZMod p) : ℝ :=
  (smallPrimeGoodStates h).card / (p : ℝ)

noncomputable def smallAnchoredDensity (h : Fin k → ZMod p) (j : Fin k) : ℝ :=
  (smallAnchorGoodStates h j).card / (Fintype.card ((ZMod p)ˣ) : ℝ)

theorem smallPresieveDensity_nonneg (h : Fin k → ZMod p) : 0 ≤ smallPresieveDensity h := by
  unfold smallPresieveDensity
  positivity

theorem smallPresieveDensity_pos (h : Fin k → ZMod p) (ha : ∃ x, SmallPrimeGood h x) :
    0 < smallPresieveDensity h := by
  obtain ⟨x, hx⟩ := ha
  have hcard : 0 < (smallPrimeGoodStates h).card :=
    Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact div_pos (by exact_mod_cast hcard) hp

theorem smallAnchoredDensity_eq (h : Fin k → ZMod p) (j : Fin k) :
    smallAnchoredDensity h j = smallPresieveDensity h / (((p : ℝ) - 1) / p) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  unfold smallAnchoredDensity smallPresieveDensity
  rw [smallAnchorGoodStates_card, ZMod.card_units_eq_totient, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp

end Erdos4.FGKMT
