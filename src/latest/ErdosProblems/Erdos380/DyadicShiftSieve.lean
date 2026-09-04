import ErdosProblems.Erdos380.UniformSieve
import ErdosProblems.Erdos380.LongSmoothIntervals

/-! # Uniform deletion of consecutive shifts modulo a dyadic prime band -/

open scoped BigOperators Function

namespace Erdos380

noncomputable def unitShiftResidues {q : ℕ} (c : (ZMod q)ˣ) (H : ℕ) : Finset (ZMod q) := by
  classical
  exact (forwardShiftResidues q H).image fun r => (↑c⁻¹ : ZMod q) * r

lemma unitShiftResidues_card {q H : ℕ} (c : (ZMod q)ˣ) (hH : H ≤ q) :
    (unitShiftResidues c H).card = H := by
  classical
  calc
    (unitShiftResidues c H).card = (forwardShiftResidues q H).card := by
      unfold unitShiftResidues
      apply Finset.card_image_of_injOn
      intro r _ s _ h
      have h' := congrArg (fun a : ZMod q => (c : ZMod q) * a) h
      simpa only [← mul_assoc, Units.mul_inv, one_mul] using h'
    _ = H := forwardShiftResidues_card hH

lemma mem_unitShiftResidues_iff {q H n : ℕ} (c : (ZMod q)ˣ) :
    (n : ZMod q) ∈ unitShiftResidues c H ↔
      ∃ j ∈ Finset.range H, (c : ZMod q) * n + j = 0 := by
  classical
  constructor
  · intro hn
    obtain ⟨r, hr, hrn⟩ := Finset.mem_image.mp hn
    obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hr
    refine ⟨j, hj, ?_⟩
    rw [← hrn, ← hjr, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]
  · rintro ⟨j, hj, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨-(j : ZMod q), Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    have heq : -(j : ZMod q) = (c : ZMod q) * n := (eq_neg_of_add_eq_zero_left hz).symm
    rw [heq, ← mul_assoc, Units.inv_mul, one_mul]

theorem dyadicResidueSurvivors_card_le_uniform {P k H : ℕ}
    (hP : 2 ≤ P) (hk : 0 < k) (hH : 0 < H) (hHP : H ≤ P)
    (hcount : ((P : ℝ) / Real.log P) / 10 ≤ ((dyadicPrimes P).card : ℝ))
    (hkP : 20 * (k : ℝ) * Real.log P ≤ P)
    (m₀ N : ℕ) (hpower : (2 * P) ^ (2 * k) ≤ N)
    (vanish : ∀ q : dyadicPrimes P, Finset (ZMod q.1))
    (hvanish : ∀ q, (vanish q).card = H) :
    letI : ∀ q : dyadicPrimes P, NeZero q.1 :=
      fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
    ((residueClassSurvivors vanish m₀ N).card : ℝ) ≤
      ((N : ℝ) + N) / (((H : ℝ) / (40 * k * Real.log P)) ^ k) := by
  classical
  let : ∀ q : dyadicPrimes P, NeZero q.1 :=
    fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hcard : 2 * k ≤ Fintype.card (dyadicPrimes P) := by
    have h : (2 * k : ℝ) ≤ ((P : ℝ) / Real.log P) / 10 := by
      rw [div_div]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have h' := h.trans hcount
    simpa only [Fintype.card_coe] using (show 2 * k ≤ (dyadicPrimes P).card by exact_mod_cast h')
  have hcoprime : Pairwise (Nat.Coprime on fun q : dyadicPrimes P => q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (Finset.mem_filter.mp q.2).2 (Finset.mem_filter.mp r.2).2).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  have hsieve := residueClassSurvivors_card_le_uniform (fun q : dyadicPrimes P => q.1)
    hcoprime vanish hk hH (by omega : 0 < 2 * P) hcard
    (fun q => (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).2) hvanish
    (fun q => hHP.trans_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1)
    m₀ N hpower
  have hdenom : (H : ℝ) / (40 * k * Real.log P) ≤
      (Fintype.card (dyadicPrimes P) : ℝ) * H / (2 * k * (2 * P : ℕ)) := by
    calc
      (H : ℝ) / (40 * k * Real.log P) =
          (((P : ℝ) / Real.log P) / 10) * H / (2 * k * (2 * P : ℕ)) := by
        push_cast
        field_simp
        ring
      _ ≤ _ := by simp only [Fintype.card_coe]; gcongr
  exact hsieve.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hdenom k))

theorem exists_uniform_dyadicShiftSieve_bound : ∃ P₀ : ℕ, ∀ P ≥ P₀,
    ∀ k H : ℕ, 0 < k → 0 < H → H ≤ P → 20 * (k : ℝ) * Real.log P ≤ P →
    ∀ m₀ N : ℕ, (2 * P) ^ (2 * k) ≤ N →
    ∀ c : ∀ q : dyadicPrimes P, (ZMod q.1)ˣ,
    letI : ∀ q : dyadicPrimes P, NeZero q.1 :=
      fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
    ((residueClassSurvivors (fun q => unitShiftResidues (c q) H) m₀ N).card : ℝ) ≤
      ((N : ℝ) + N) / (((H : ℝ) / (40 * k * Real.log P)) ^ k) := by
  obtain ⟨P₁, hP₁⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 2 P₁, ?_⟩
  intro P hP k H hk hH hHP hkP m₀ N hpower c
  exact dyadicResidueSurvivors_card_le_uniform ((le_max_left _ _).trans hP) hk hH hHP
    (hP₁ P ((le_max_right _ _).trans hP)).1 hkP m₀ N hpower _
    (fun q => unitShiftResidues_card (c q) (hHP.trans
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1.le))

end Erdos380
