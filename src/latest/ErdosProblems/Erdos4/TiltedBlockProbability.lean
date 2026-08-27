import ErdosProblems.Erdos4.TiltedBlocks
import ErdosProblems.Erdos4.TiltedConditioning

/-! Positivity and exact local factors for the actual all-fiber blocks. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

theorem atom_le_inv {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    atom s u ≤ 1 / (s : ℝ) := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  unfold atom
  apply (div_le_div_iff₀ (denominator_pos hs hu0) (show (0 : ℝ) < s by linarith)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (s : ℝ) - 1 by linarith) (sub_nonneg.mpr hu1)]

theorem beta_lt_one {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    beta s u < 1 := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have ha := atom_le_inv hs hu0 hu1
  unfold beta
  calc
    _ ≤ ((s : ℝ) - 1) * (1 / (s : ℝ)) := mul_le_mul_of_nonneg_left ha (by linarith)
    _ < 1 := by
      rw [mul_one_div, div_lt_one (show (0 : ℝ) < s by linarith)]
      linarith

theorem localLaw_prob_avoid_pos (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (E : Finset (ZMod s)) (hE : E.card < s) :
    0 < (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ E) := by
  rw [localLaw_prob_avoid]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hER : (E.card : ℝ) < s := by exact_mod_cast hE
  split_ifs with hz
  · apply mul_pos (beta_pos hs hu0)
    apply sub_pos.mpr
    exact (div_lt_one (show (0 : ℝ) < s - 1 by linarith)).mpr (by linarith)
  · have ha := atom_le_inv hs hu0.le hu1
    have hle := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg E.card)
    have hlt : (E.card : ℝ) * (1 / (s : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one (show (0 : ℝ) < s by linarith)]
      exact hER
    linarith

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem sieveLaw_survival_pos (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ)
    (hsize : ∀ l, T.card < ell l) :
    0 < (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) := by
  rw [sieveLaw_survival_product]
  apply Finset.prod_pos
  intro l _
  exact localLaw_prob_avoid_pos (ell l) (Fact.out : (ell l).Prime).two_le _
    (rpow_tilt_pos (Fact.out : (ell l).Prime).two_le τ)
    (rpow_tilt_le_one (Fact.out : (ell l).Prime).two_le hτ) _
    (Finset.card_image_le.trans_lt (hsize l))

omit [Fintype P] [DecidableEq P] in
theorem zero_mem_residues_iff (T : Finset ℕ) (l : P) :
    (0 : ZMod (ell l)) ∈ residues ell T l ↔ ell l ∣ ∏ n ∈ T, n := by
  simp only [residues, Finset.mem_image, ZMod.natCast_eq_zero_iff]
  exact ((Nat.prime_iff.mp (Fact.out : (ell l).Prime)).dvd_finsetProd_iff _).symm

/-- Equation (4.7), now derived for each block in the product sieve. -/
theorem sieveLaw_block_factor (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ)
    (hinj : ∀ l, Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) T) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) =
      ∏ l, if ell l ∣ ∏ n ∈ T, n
        then beta (ell l) ((ell l : ℝ) ^ (-τ)) *
          (1 - ((T.card : ℝ) - 1) / ((ell l : ℝ) - 1))
        else 1 - (T.card : ℝ) * atom (ell l) ((ell l : ℝ) ^ (-τ)) := by
  rw [sieveLaw_survival_product]
  apply Finset.prod_congr rfl
  intro l _
  rw [residueLaw, localLaw_prob_avoid]
  have hcard : (residues ell T l).card = T.card := Finset.card_image_of_injOn (hinj l)
  simp only [hcard, zero_mem_residues_iff]

/-- The exact prime-set law (6.14), before any small-set approximation. -/
theorem sieveLaw_nonzero_set (τ : ℝ) (hτ : 0 ≤ τ) (T : Finset ℕ)
    (hnonzero : ∀ n ∈ T, ∀ l, ¬ell l ∣ n) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) =
      ∏ l : P, (1 - ((residues ell T l).card : ℝ) * atom (ell l) ((ell l : ℝ) ^ (-τ))) := by
  rw [sieveLaw_survival_product]
  apply Finset.prod_congr rfl
  intro l _
  rw [residueLaw, localLaw_prob_avoid]
  have hz : (0 : ZMod (ell l)) ∉ residues ell T l := by
    simp only [residues, Finset.mem_image, ZMod.natCast_eq_zero_iff]
    exact fun ⟨n, hn, hd⟩ => hnonzero n hn l hd
  simp only [if_neg hz]

end Erdos4.Tilted
