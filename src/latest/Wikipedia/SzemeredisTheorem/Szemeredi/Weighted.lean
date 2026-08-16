import Wikipedia.SzemeredisTheorem.ArithmeticProgression.Count
import Wikipedia.SzemeredisTheorem.Finite.Mean

/-!
# From dense sets to bounded dense weights

The hypergraph-removal layer will first produce a quantitative progression
count for dense finite sets.  This file proves the standard thresholding
step that upgrades such a theorem to functions `g : ZMod N → [0,1]`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A quantitative dense-set arithmetic-progression counting statement at
one fixed modulus. -/
def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

/-- A quantitative arithmetic-progression counting statement for bounded
nonnegative weights at one fixed modulus. -/
def HasWeightedAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ g : ZMod N → ℝ,
    (∀ x, 0 ≤ g x) →
    (∀ x, g x ≤ 1) →
    δ ≤ mean g →
      c ≤ cyclicAPCount k N g

/-- Uniform dense-set AP counting with one lower bound for every nontrivial
cyclic modulus. -/
def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

/-- Uniform bounded-weight AP counting with one lower bound for every
nontrivial cyclic modulus. -/
def HasUniformWeightedAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasWeightedAPCount k N δ c

/-- Thresholding at `δ/2` turns a dense bounded weight into a dense set.
The progression count loses the expected factor `(δ/2)^k`. -/
theorem weightedAPCount_of_denseAPCount
    {k N : ℕ} [NeZero N] {δ c : ℝ}
    (hδ0 : 0 ≤ δ)
    (hdense : HasDenseAPCount k N (δ / 2) c)
    {g : ZMod N → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1)
    (hmean : δ ≤ mean g) :
    (δ / 2) ^ k * c ≤ cyclicAPCount k N g := by
  let A : Finset (ZMod N) :=
    Finset.univ.filter fun x => δ / 2 ≤ g x
  have hpoint :
      ∀ x : ZMod N,
        g x ≤ δ / 2 + finsetIndicator A x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx]
      linarith [hg1 x]
    · rw [finsetIndicator_of_not_mem hx, add_zero]
      have hnot : ¬δ / 2 ≤ g x := by
        simpa [A] using hx
      exact le_of_lt (lt_of_not_ge hnot)
  have hmean_upper :=
    mean_mono (f := g)
      (g := fun x => δ / 2 + finsetIndicator A x) hpoint
  rw [mean_add, mean_const] at hmean_upper
  have hAmean : δ / 2 ≤ mean (finsetIndicator A) := by
    linarith
  have hsetCount := hdense A hAmean
  have hscaled_nonneg :
      ∀ x : ZMod N,
        0 ≤ δ / 2 * finsetIndicator A x := by
    intro x
    exact mul_nonneg (div_nonneg hδ0 (by norm_num))
      (by
        unfold finsetIndicator
        split <;> norm_num)
  have hscaled_le :
      ∀ x : ZMod N,
        δ / 2 * finsetIndicator A x ≤ g x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx, mul_one]
      simpa [A] using (Finset.mem_filter.mp hx).2
    · rw [finsetIndicator_of_not_mem hx, mul_zero]
      exact hg0 x
  have hcountMono :
      cyclicAPCount k N
          (fun x => δ / 2 * finsetIndicator A x) ≤
        cyclicAPCount k N g :=
    cyclicAPCount_mono (k := k) (N := N)
      hscaled_nonneg hscaled_le
  rw [cyclicAPCount_smul] at hcountMono
  calc
    (δ / 2) ^ k * c ≤
        (δ / 2) ^ k *
          cyclicAPCount k N (finsetIndicator A) :=
      mul_le_mul_of_nonneg_left hsetCount
        (pow_nonneg (div_nonneg hδ0 (by norm_num)) _)
    _ ≤ cyclicAPCount k N g := hcountMono

end Wikipedia.SzemeredisTheorem
