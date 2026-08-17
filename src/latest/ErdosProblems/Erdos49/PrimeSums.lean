import ErdosProblems.Erdos49.ExceptionalBasic

/-!
# Prime-counting and reciprocal-prime estimates

The cluster estimates need two standard consequences of the prime number
theorem and Mertens' theorem.  They are recorded here in a form over natural
endpoints.
-/

open Filter Set
open scoped BigOperators Topology

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def primeReciprocalUpTo (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

lemma mertens_sum_eq_primeReciprocalUpTo (x : ℕ) :
    (∑ p ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p) =
      primeReciprocalUpTo x := by
  apply Finset.sum_congr
  · ext p
    simp only [Nat.floor_natCast, Finset.mem_filter, Finset.mem_Ioc,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp0, hpx⟩, hp⟩
      exact ⟨hpx, hp⟩
    · rintro ⟨hpx, hp⟩
      exact ⟨⟨hp.pos, hpx⟩, hp⟩
  · intro p hp
    rfl

lemma primeReciprocalUpTo_eq (x : ℕ) :
    primeReciprocalUpTo x =
      Real.log (Real.log (x : ℝ)) + Mertens.M + Mertens.E₂p x := by
  rw [← mertens_sum_eq_primeReciprocalUpTo]
  exact Mertens.sum_prime_div_eq x

def mertensReciprocalError : ℝ := Real.log 4 + 6 + Mertens.E₁

lemma mertensReciprocalError_nonneg : 0 ≤ mertensReciprocalError := by
  unfold mertensReciprocalError
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith [Mertens.E₁.nonneg]

lemma primeReciprocalUpTo_error {x : ℕ} (hx : 2 ≤ x) :
    |primeReciprocalUpTo x -
      (Real.log (Real.log (x : ℝ)) + Mertens.M)| ≤
        mertensReciprocalError / Real.log x := by
  rw [primeReciprocalUpTo_eq]
  rw [show Real.log (Real.log (x : ℝ)) + Mertens.M + Mertens.E₂p x -
      (Real.log (Real.log (x : ℝ)) + Mertens.M) = Mertens.E₂p x by ring]
  simpa [mertensReciprocalError] using Mertens.E₂p.abs_le (by
    exact_mod_cast hx : (2 : ℝ) ≤ (x : ℝ))

def primeReciprocalInterval (u v : ℕ) : ℝ :=
  ∑ p ∈ Analytic.primeInterval u v, (1 : ℝ) / p

lemma primeReciprocalInterval_eq_sub {u v : ℕ} (huv : u ≤ v) :
    primeReciprocalInterval u v =
      primeReciprocalUpTo v - primeReciprocalUpTo (u - 1) := by
  unfold primeReciprocalInterval primeReciprocalUpTo Analytic.primeInterval
  have hsub : Nat.primesLE (u - 1) ⊆ Nat.primesLE v :=
    Nat.primesLE_mono ((Nat.sub_le u 1).trans huv)
  have hset : (Finset.Icc u v).filter Nat.Prime =
      Nat.primesLE v \ Nat.primesLE (u - 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpu, hpv⟩, hp⟩
      refine ⟨⟨hpv, hp⟩, ?_⟩
      intro h
      have hp_le := h.1
      have hpPos := hp.pos
      omega
    · rintro ⟨⟨hpv, hp⟩, hnot⟩
      have hpu : u ≤ p := by
        by_contra h
        apply hnot
        exact ⟨by omega, hp⟩
      exact ⟨⟨hpu, hpv⟩, hp⟩
  rw [hset, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

lemma primeReciprocalInterval_upper {u v : ℕ}
    (hu : 3 ≤ u) (huv : u ≤ v) :
    primeReciprocalInterval u v ≤
      Real.log (Real.log (v : ℝ)) -
        Real.log (Real.log ((u - 1 : ℕ) : ℝ)) +
      2 * mertensReciprocalError / Real.log (u - 1 : ℕ) := by
  have hu1 : 2 ≤ u - 1 := by omega
  have hv2 : 2 ≤ v := by omega
  have hEu := Mertens.E₂p.abs_le (by
    exact_mod_cast hu1 : (2 : ℝ) ≤ ((u - 1 : ℕ) : ℝ))
  have hEv := Mertens.E₂p.abs_le (by
    exact_mod_cast hv2 : (2 : ℝ) ≤ (v : ℝ))
  have hlogmono : Real.log (u - 1 : ℕ) ≤ Real.log (v : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast ((Nat.sub_le u 1).trans huv)
  have hlogu : 0 < Real.log (u - 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast hu1)
  have hlogv : 0 < Real.log (v : ℝ) :=
    Real.log_pos (by exact_mod_cast hv2)
  have herrv : mertensReciprocalError / Real.log v ≤
      mertensReciprocalError / Real.log (u - 1 : ℕ) := by
    exact div_le_div_of_nonneg_left mertensReciprocalError_nonneg hlogu hlogmono
  rw [primeReciprocalInterval_eq_sub huv, primeReciprocalUpTo_eq,
    primeReciprocalUpTo_eq]
  have hEu' := abs_le.mp hEu
  have hEv' := abs_le.mp hEv
  have hEdiff : Mertens.E₂p (v : ℝ) - Mertens.E₂p (u - 1 : ℕ) ≤
      2 * mertensReciprocalError / Real.log (u - 1 : ℕ) := by
    have hupperV : Mertens.E₂p (v : ℝ) ≤
        mertensReciprocalError / Real.log v := by
      unfold mertensReciprocalError
      exact hEv'.2
    have hlowerU : -mertensReciprocalError / Real.log (u - 1 : ℕ) ≤
        Mertens.E₂p (u - 1 : ℕ) := by
      unfold mertensReciprocalError
      simpa only [neg_div] using hEu'.1
    calc
      Mertens.E₂p (v : ℝ) - Mertens.E₂p (u - 1 : ℕ) ≤
          mertensReciprocalError / Real.log v +
            mertensReciprocalError / Real.log (u - 1 : ℕ) := by
        calc
          Mertens.E₂p (v : ℝ) - Mertens.E₂p (u - 1 : ℕ) ≤
              mertensReciprocalError / Real.log v -
                (-mertensReciprocalError / Real.log (u - 1 : ℕ)) :=
            sub_le_sub hupperV hlowerU
          _ = mertensReciprocalError / Real.log v +
                mertensReciprocalError / Real.log (u - 1 : ℕ) := by ring
      _ ≤ mertensReciprocalError / Real.log (u - 1 : ℕ) +
            mertensReciprocalError / Real.log (u - 1 : ℕ) := by
        simpa [add_comm] using
          add_le_add_right herrv (mertensReciprocalError / Real.log (u - 1 : ℕ))
      _ = 2 * mertensReciprocalError / Real.log (u - 1 : ℕ) := by ring
  calc
    Real.log (Real.log (v : ℝ)) + Mertens.M + Mertens.E₂p v -
        (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + Mertens.M +
          Mertens.E₂p (u - 1 : ℕ)) =
      Real.log (Real.log (v : ℝ)) -
        Real.log (Real.log ((u - 1 : ℕ) : ℝ)) +
        (Mertens.E₂p v - Mertens.E₂p (u - 1 : ℕ)) := by ring
    _ ≤ Real.log (Real.log (v : ℝ)) -
        Real.log (Real.log ((u - 1 : ℕ) : ℝ)) +
        2 * mertensReciprocalError / Real.log (u - 1 : ℕ) := by
      gcongr

/-- Chebyshev's upper bound, specialized to natural arguments with a generous
absolute constant. -/
theorem eventually_primeCounting_nat_upper :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ 4 * n / Real.log n := by
  have hreal := Chebyshev.eventually_primeCounting_le
    (by norm_num : (0 : ℝ) < 1)
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually hreal, eventually_ge_atTop 2] with n hn hn2
  have hcoeff : Real.log 4 + 1 ≤ 4 := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hlog ⊢
    linarith
  have hscale : 0 ≤ (n : ℝ) / Real.log n := by
    exact div_nonneg (by positivity) (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n by omega)))
  have hn' : (Nat.primeCounting n : ℝ) ≤
      (Real.log 4 + 1) * n / Real.log n := by simpa using hn
  calc
    (Nat.primeCounting n : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := hn'
    _ = (Real.log 4 + 1) * ((n : ℝ) / Real.log n) := by ring
    _ ≤ 4 * ((n : ℝ) / Real.log n) :=
      mul_le_mul_of_nonneg_right hcoeff hscale
    _ = 4 * n / Real.log n := by ring

theorem exists_primeCounting_nat_upper :
    ∃ X : ℕ, 2 ≤ X ∧ ∀ n : ℕ, X ≤ n →
      (Nat.primeCounting n : ℝ) ≤ 4 * n / Real.log n := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 eventually_primeCounting_nat_upper
  refine ⟨max 2 X₀, le_max_left _ _, ?_⟩
  intro n hn
  exact hX₀ n ((le_max_right 2 X₀).trans hn)

#print axioms primeReciprocalInterval_upper
#print axioms eventually_primeCounting_nat_upper

end

end Erdos49
