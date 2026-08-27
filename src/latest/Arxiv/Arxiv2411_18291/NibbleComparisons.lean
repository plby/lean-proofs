import Arxiv.Arxiv2411_18291.ComparisonIncrementBounds
import Arxiv.Arxiv2411_18291.RemovalDensity

/-!
# Concrete reciprocal comparison functions for clique removal

The small parameter a will be n to the power -epsilon/3. Thus the initial
degree error is a cubed, the edge critical width is a squared times D, and
the face critical width is a times the vertex count.
-/

noncomputable section

namespace Arxiv2411_18291

def nibbleDegreeMain (k : ℕ) (D p : ℝ) : ℝ := D * p ^ (k - 1)

def nibbleCliqueMain (k : ℕ) (g D p : ℝ) : ℝ := D * g * p ^ k / k

def nibbleEdgeScale (a D p : ℝ) : ℝ := a ^ 2 * D / p

def nibbleDegreeError (k : ℕ) (a D p : ℝ) : ℝ := 16 * k * nibbleEdgeScale a D p

def nibbleCliqueError (k : ℕ) (a g D p : ℝ) : ℝ :=
  16 * (k : ℝ) ^ 2 * a ^ 3 * D * g / p ^ 2

def nibbleDegreeUpper (k : ℕ) (a D p : ℝ) : ℝ :=
  nibbleDegreeMain k D p + nibbleDegreeError k a D p

def nibbleDegreeLower (k : ℕ) (a D p : ℝ) : ℝ :=
  nibbleDegreeMain k D p - nibbleDegreeError k a D p

def nibbleCliqueUpper (k : ℕ) (a g D p : ℝ) : ℝ :=
  nibbleCliqueMain k g D p + nibbleCliqueError k a g D p

def nibbleCliqueLower (k : ℕ) (a g D p : ℝ) : ℝ :=
  nibbleCliqueMain k g D p - nibbleCliqueError k a g D p

theorem nibbleDegreeMain_pos {k : ℕ} {D p : ℝ} (hD : 0 < D) (hp : 0 < p) :
    0 < nibbleDegreeMain k D p := mul_pos hD (pow_pos hp _)

theorem nibbleCliqueMain_pos {k : ℕ} (hk : 0 < k) {g D p : ℝ}
    (hg : 0 < g) (hD : 0 < D) (hp : 0 < p) : 0 < nibbleCliqueMain k g D p := by
  unfold nibbleCliqueMain
  positivity

theorem nibbleEdgeScale_nonneg {a D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ nibbleEdgeScale a D p := div_nonneg (mul_nonneg (sq_nonneg _) hD) hp

theorem nibble_main_relation {k : ℕ} (hk : 0 < k) (g D p : ℝ) :
    nibbleCliqueMain k g D p = nibbleDegreeMain k D p * p * g / k := by
  unfold nibbleCliqueMain nibbleDegreeMain
  have hexp : k - 1 + 1 = k := by omega
  have hpow : p ^ k = p ^ (k - 1) * p := by simpa only [hexp] using pow_succ p (k - 1)
  rw [hpow]
  ring

theorem nibbleEdgeScale_degree_ratio {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (hD : D ≠ 0) (hp : p ≠ 0) :
    nibbleEdgeScale a D p / nibbleDegreeMain k D p = a ^ 2 / p ^ k := by
  unfold nibbleEdgeScale nibbleDegreeMain
  have hexp : k - 1 + 1 = k := by omega
  have hpow : p ^ k = p ^ (k - 1) * p := by simpa only [hexp] using pow_succ p (k - 1)
  rw [hpow]
  field_simp

theorem nibbleDegreeMain_clique_ratio {k : ℕ} (hk : 0 < k) {g D p : ℝ}
    (hg : g ≠ 0) (hD : D ≠ 0) (hp : p ≠ 0) :
    nibbleDegreeMain k D p / nibbleCliqueMain k g D p = (k : ℝ) / (p * g) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [nibble_main_relation hk]
  have hm' : nibbleDegreeMain k D p ≠ 0 := mul_ne_zero hD (pow_ne_zero _ hp)
  field_simp

theorem nibbleEdgeScale_clique_ratio {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (hg : g ≠ 0) (hD : D ≠ 0) (hp : p ≠ 0) :
    nibbleEdgeScale a D p * nibbleDegreeMain k D p / nibbleCliqueMain k g D p =
      (k : ℝ) * a ^ 2 * D / (p ^ 2 * g) := by
  rw [mul_div_assoc, nibbleDegreeMain_clique_ratio hk hg hD hp]
  unfold nibbleEdgeScale
  ring

end Arxiv2411_18291
