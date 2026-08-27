import ErdosProblems.Erdos587.HooleyDelta

/-!
# Counting centered rational approximants by Delta fibers

An approximant is encoded by its nonzero-index product and its integer
error. Inside a fixed encoded fiber, its denominator determines the
other two coordinates. A ratio-two denominator range therefore costs
one Hooley Delta value, without subdividing the index range.
-/

open scoped BigOperators

namespace Erdos587

@[ext] structure DeltaApproximant where
  index : ℕ
  denominator : ℕ
  numerator : ℤ
  deriving DecidableEq

def deltaApproximantError (a : ℤ) (q : ℕ) (x : DeltaApproximant) : ℤ :=
  a * x.index * x.denominator - q * x.numerator

lemma deltaApproximant_eq_of_encoding {a : ℤ} {q : ℕ} (hq : 0 < q)
    {x y : DeltaApproximant} (hb : 0 < x.denominator)
    (hden : x.denominator = y.denominator)
    (hprod : x.index * x.denominator = y.index * y.denominator)
    (herr : deltaApproximantError a q x = deltaApproximantError a q y) : x = y := by
  have hm : x.index = y.index := by
    apply Nat.eq_of_mul_eq_mul_right hb
    simpa only [← hden] using hprod
  have hnum : x.numerator = y.numerator := by
    dsimp only [deltaApproximantError] at herr
    rw [hm, hden] at herr
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    exact mul_left_cancel₀ hqZ (by linarith : (q : ℤ) * x.numerator = q * y.numerator)
  exact DeltaApproximant.ext hm hden hnum

open Classical in
theorem delta_approximant_card_le_residue_delta_sum {a : ℤ} {q X : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 < B) (S : Finset DeltaApproximant) (E : Finset ℤ)
    (hindex : ∀ x ∈ S, 0 < x.index)
    (hlow : ∀ x ∈ S, B < x.denominator)
    (hupp : ∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B)
    (hproduct : ∀ x ∈ S, x.index * x.denominator ≤ X)
    (herror : ∀ x ∈ S, deltaApproximantError a q x ∈ E) :
    S.card ≤ ∑ t ∈ E, ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
      hooleyDelta n := by
  let T : Finset (Σ _t : ℤ, ℕ) := E.sigma
    (fun t => (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t))
  let e : DeltaApproximant → (Σ _t : ℤ, ℕ) := fun x =>
    ⟨deltaApproximantError a q x, x.index * x.denominator⟩
  have hb (x : DeltaApproximant) (hx : x ∈ S) : 0 < x.denominator := by
    have h := (hB.trans (hlow x hx))
    exact_mod_cast h
  have hmaps : (S : Set DeltaApproximant).MapsTo e (T : Set (Σ _t : ℤ, ℕ)) := by
    intro x hx
    apply Finset.mem_sigma.mpr
    refine ⟨herror x hx, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (hindex x hx) (hb x hx), hproduct x hx⟩, ?_⟩⟩
    refine ⟨x.numerator, ?_⟩
    dsimp only [e, deltaApproximantError]
    push_cast
    ring
  have hfiber (z : Σ _t : ℤ, ℕ) (hz : z ∈ T) :
      (S.filter (fun x => e x = z)).card ≤ hooleyDelta z.2 := by
    have hn : z.2 ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1).1
      omega
    apply card_le_hooleyDelta_of_divisor_encoding (S.filter (fun x => e x = z))
      DeltaApproximant.denominator hn hB
    · intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hprod : x.index * x.denominator = z.2 := congrArg (fun w : Σ _t : ℤ, ℕ => w.2) he
      refine ⟨x.index, ?_⟩
      rw [← hprod]
      ring
    · intro x hx
      exact hlow x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact hupp x (Finset.mem_filter.mp hx).1
    · intro x hx y hy hden
      have hxS := (Finset.mem_filter.mp hx).1
      have hxy : e x = e y := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact deltaApproximant_eq_of_encoding hq (hb x hxS) hden
        (congrArg (fun w : Σ _t : ℤ, ℕ => w.2) hxy)
        (congrArg (fun w : Σ _t : ℤ, ℕ => w.1) hxy)
  calc
    _ = ∑ z ∈ T, (S.filter (fun x => e x = z)).card := Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ z ∈ T, hooleyDelta z.2 := Finset.sum_le_sum hfiber
    _ = _ := Finset.sum_sigma _ _ _

end Erdos587
