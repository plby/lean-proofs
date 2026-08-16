import Wikipedia.SzemeredisTheorem.Statement
import Wikipedia.SzemeredisTheorem.Main
import Wikipedia.SzemeredisTheorem.ArithmeticProgression.CountExtraction
import Wikipedia.SzemeredisTheorem.ArithmeticProgression.ShortInterval

/-!
# From the finite cyclic theorem to the upper-density theorem

The finite theorem supplies many progressions in a dense subset of a cyclic
group.  We place a dense natural-number prefix in a cyclic group four times
as large.  At sufficiently large scales the quantitative lower bound beats
the diagonal progressions; a nonconstant cyclic progression can then be
unwrapped without modular wraparound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The inclusive prefix density appearing in the Lean Eval definition. -/
noncomputable def prefixDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)

/-- The elements of `A` in the inclusive prefix through `n`. -/
noncomputable def naturalPrefix (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (n + 1)).filter (fun k => k ∈ A)

theorem prefixDensity_eq_card (A : Set ℕ) (n : ℕ) :
    prefixDensity A n = (naturalPrefix A n).card / (n + 1 : ℕ) := by
  classical
  simp [prefixDensity, naturalPrefix, Set.indicator]

theorem prefixDensity_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ prefixDensity A n := by
  rw [prefixDensity_eq_card]
  positivity

theorem frequently_lt_prefixDensity_of_lt_upperDensity
    {A : Set ℕ} {r : ℝ} (h : r < SzemeredisTheorem.upperDensity A) :
    ∃ᶠ n in Filter.atTop, r < prefixDensity A n := by
  apply Filter.frequently_lt_of_lt_limsup
      (Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0)
        (prefixDensity_nonneg A))
  change r < Filter.limsup (prefixDensity A) Filter.atTop at h
  exact h

/-- The copy of a natural prefix inside `ZMod N`, selected by standard
representatives. -/
noncomputable def cyclicPrefix (A : Set ℕ) (n N : ℕ) [NeZero N] : Finset (ZMod N) :=
  by
    classical
    exact Finset.univ.filter fun x => x.val < n + 1 ∧ x.val ∈ A

theorem cyclicPrefix_card {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    (cyclicPrefix A n N).card = (naturalPrefix A n).card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod N))
  · intro x hx
    simp only [naturalPrefix, cyclicPrefix, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [ZMod.val_natCast_of_lt]
      · exact (Finset.mem_range.mp hx.1)
      · exact (Finset.mem_range.mp hx.1).trans_le hN
    · rw [ZMod.val_natCast_of_lt]
      · exact hx.2
      · exact (Finset.mem_range.mp hx.1).trans_le hN
  · intro x hx y hy hxy
    simp only [naturalPrefix, Finset.mem_filter] at hx hy
    have hxN : x < N := (Finset.mem_range.mp hx.1).trans_le hN
    have hyN : y < N := (Finset.mem_range.mp hy.1).trans_le hN
    have hval := congrArg (ZMod.val : ZMod N → ℕ) hxy
    simpa [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] using hval
  · intro z hz
    simp only [cyclicPrefix, Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · simp only [naturalPrefix, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hz.2.1, hz.2.2⟩
    · exact ZMod.natCast_zmod_val z

theorem mean_cyclicPrefix {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    mean (finsetIndicator (cyclicPrefix A n N)) =
      prefixDensity A n * ((n + 1 : ℕ) / N : ℝ) := by
  rw [mean_finsetIndicator, cyclicPrefix_card hN, prefixDensity_eq_card]
  simp only [ZMod.card]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Unwrap a nonconstant cyclic progression contained in a short natural
interval.  If its integer common difference is negative, reverse the order
of its terms. -/
theorem exists_naturalAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj

/-- The quantitative cyclic theorem implies the Lean Eval upper-density
form of Szemerédi's theorem. -/
theorem containsArbitraryAPs_of_upperDensity_pos (A : Set ℕ)
    (hupper : 0 < SzemeredisTheorem.upperDensity A) :
    SzemeredisTheorem.ContainsArbitraryAPs A := by
  intro k
  let K : ℕ := max 2 k
  have hKtwo : 2 ≤ K := by
    exact le_max_left 2 k
  have hkK : k ≤ K := by
    exact le_max_right 2 k
  let δ : ℝ := SzemeredisTheorem.upperDensity A / 8
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨c, hc, huniform⟩ := szemeredi K hKtwo hδ
  obtain ⟨m : ℕ, hm : 1 / c < m⟩ := exists_nat_gt (1 / c)
  have hfrequent :
      ∃ᶠ n in Filter.atTop,
        SzemeredisTheorem.upperDensity A / 2 < prefixDensity A n :=
    frequently_lt_prefixDensity_of_lt_upperDensity (by linarith)
  have heventual : ∀ᶠ n : ℕ in Filter.atTop, m ≤ n :=
    Filter.eventually_ge_atTop m
  obtain ⟨n, hprefix, hmn⟩ :=
    (hfrequent.and_eventually heventual).exists
  let N : ℕ := 4 * (n + 1)
  letI : NeZero N := ⟨by dsimp [N]; omega⟩
  have hnN : n + 1 ≤ N := by
    dsimp [N]
    omega
  let S : Finset (ZMod N) := cyclicPrefix A n N
  have hmean : δ ≤ mean (finsetIndicator S) := by
    rw [show S = cyclicPrefix A n N from rfl,
      mean_cyclicPrefix (A := A) hnN]
    have hratio : (((n + 1 : ℕ) : ℝ) / (N : ℕ)) = 1 / 4 := by
      dsimp [N]
      push_cast
      field_simp
    rw [hratio]
    dsimp [δ]
    linarith
  have hcyclic :
      c ≤ cyclicAPCount K N (finsetIndicator S) :=
    huniform N S hmean
  have hf0 : ∀ x : ZMod N, 0 ≤ finsetIndicator S x := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod N, finsetIndicator S x ≤ 1 := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hmean_one : mean (finsetIndicator S) ≤ 1 :=
    mean_le_of_le_const hf1
  have hmn_real : 1 / c < (n : ℝ) := by
    exact hm.trans_le (by exact_mod_cast hmn)
  have hone_n : 1 < (n : ℝ) * c := by
    exact (div_lt_iff₀ hc).mp hmn_real
  have hn_le_N : (n : ℝ) ≤ N := by
    exact_mod_cast (show n ≤ N by omega)
  have hone_N : 1 < (N : ℝ) * c :=
    hone_n.trans_le (mul_le_mul_of_nonneg_right hn_le_N hc.le)
  have hoffdiag :
      0 < cyclicAPOffDiagMass K N (finsetIndicator S) := by
    apply cyclicAPOffDiagMass_pos_of_count (by omega) hf0 hf1
    calc
      1 ^ (K - 1) * mean (finsetIndicator S) =
          mean (finsetIndicator S) := by simp
      _ ≤ 1 := hmean_one
      _ < (N : ℝ) * c := hone_N
      _ ≤ (N : ℝ) * cyclicAPCount K N (finsetIndicator S) :=
        mul_le_mul_of_nonneg_left hcyclic (by positivity)
  obtain ⟨a, d, hd, hpositive⟩ :=
    exists_cyclicAP_of_offDiagMass_pos hf0 hoffdiag
  have htermS :
      ∀ j : ℕ, j < K → a + (j : ZMod N) * d ∈ S := by
    intro j hj
    let jf : Fin K := ⟨j, hj⟩
    have hp := hpositive jf
    have hmem : cyclicAPTerm a d jf ∈ S := by
      by_contra hnot
      rw [finsetIndicator_of_not_mem hnot] at hp
      linarith
    simpa [cyclicAPTerm, jf] using hmem
  have htermData :
      ∀ j : ℕ, j < K →
        cyclicAPVal a d j < n + 1 ∧ cyclicAPVal a d j ∈ A := by
    intro j hj
    have hmem := htermS j hj
    simpa [S, cyclicPrefix, cyclicAPVal] using hmem
  have hinterval :
      ∀ j : ℕ, j < K →
        (0 : ℤ) ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ (n : ℤ) := by
    intro j hj
    have hmem := htermData j hj
    constructor
    · positivity
    · exact_mod_cast (Nat.lt_succ_iff.mp hmem.1)
  have hA :
      ∀ j : ℕ, j < K → cyclicAPVal a d j ∈ A := by
    intro j hj
    exact (htermData j hj).2
  have hwidth : 2 * ((n : ℤ) - 0) < (N : ℤ) := by
    dsimp [N]
    push_cast
    omega
  obtain ⟨x, step, hstep, hprogression⟩ :=
    exists_naturalAP_of_cyclicAPVal_shortInterval
      a d hd hKtwo 0 n hinterval hwidth hA
  exact ⟨x, step, hstep, fun j hj => hprogression j (hj.trans_le hkK)⟩

end Wikipedia.SzemeredisTheorem
