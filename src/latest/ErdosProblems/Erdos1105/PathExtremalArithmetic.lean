import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

/-- The edge count of the standard connected path-extremal graph
`H(n,K,a)`: a clique on `K-a` vertices and `n-K+a` vertices joined to
the same `a` vertices of that clique. -/
def pathExtremalEdges (n K a : ℕ) : ℕ :=
  (K - a).choose 2 + a * (n - K + a)

lemma pathExtremalEdges_affine {n m K a : ℕ} (hKn : K ≤ n) (hnm : n ≤ m) :
    pathExtremalEdges n K a + a * (m - n) = pathExtremalEdges m K a := by
  have hsub : m - K + a = (n - K + a) + (m - n) := by omega
  simp only [pathExtremalEdges, hsub]
  ring

lemma pathExtremalEdges_clique_succ {n K a : ℕ} (ha : 2 * a ≤ K) (hn : K + 1 ≤ n) :
    pathExtremalEdges n (K + 1) a = pathExtremalEdges n K a + (K - 2 * a) := by
  have hsub : K + 1 - a = K - a + 1 := by omega
  have hc := Nat.choose_succ_succ (K - a) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right] at hc
  have hrest : n - K + a = (n - (K + 1) + a) + 1 := by omega
  have hK : K - a = a + (K - 2 * a) := by omega
  simp only [pathExtremalEdges, hsub, hc, hrest]
  nlinarith

lemma pathExtremalEdges_mono_clique {n K L a : ℕ}
    (ha : 2 * a ≤ K) (hKL : K ≤ L) (hn : L ≤ n) :
    pathExtremalEdges n K a ≤ pathExtremalEdges n L a := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hKL ih =>
    have h := ih (by omega)
    rw [pathExtremalEdges_clique_succ (by omega) hn]
    omega

lemma pathExtremalEdges_twice (n K a : ℕ) (ha : a ≤ K) (hn : K ≤ n) :
    2 * (pathExtremalEdges n K a : ℚ) =
      3 * (a : ℚ) ^ 2 + (2 * n - 4 * K + 1) * a + (K : ℚ) ^ 2 - K := by
  simp only [pathExtremalEdges, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
    Nat.cast_sub ha, Nat.cast_sub hn]
  ring

/-- Convexity of the extremal edge count in its third parameter. -/
lemma pathExtremalEdges_le_max (n K l a u : ℕ)
    (hla : l ≤ a) (hau : a ≤ u) (huK : u ≤ K) (hKn : K ≤ n) :
    pathExtremalEdges n K a ≤
      max (pathExtremalEdges n K l) (pathExtremalEdges n K u) := by
  by_contra! h
  have hleft : (pathExtremalEdges n K l : ℚ) < pathExtremalEdges n K a := by
    exact_mod_cast lt_of_le_of_lt (le_max_left _ _) h
  have hright : (pathExtremalEdges n K u : ℚ) < pathExtremalEdges n K a := by
    exact_mod_cast lt_of_le_of_lt (le_max_right _ _) h
  have hl := pathExtremalEdges_twice n K l (hla.trans (hau.trans huK)) hKn
  have ha := pathExtremalEdges_twice n K a (hau.trans huK) hKn
  have hu := pathExtremalEdges_twice n K u huK hKn
  have hla' : (l : ℚ) ≤ a := by exact_mod_cast hla
  have hau' : (a : ℚ) ≤ u := by exact_mod_cast hau
  have hslope : 0 < 3 * ((a : ℚ) + l) + (2 * n - 4 * K + 1) := by
    by_contra! hs
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hla') hs
    nlinarith
  have hslope' : 0 ≤ 3 * ((u : ℚ) + a) + (2 * n - 4 * K + 1) := by linarith
  have hm := mul_nonneg (sub_nonneg.mpr hau') hslope'
  nlinarith

lemma pathExtremalEdges_at_path_order_le_clique {k a : ℕ} (hk : 4 ≤ k)
    (ha : 2 * a ≤ k - 2) : pathExtremalEdges k (k - 1) a ≤ (k - 1).choose 2 := by
  have h := pathExtremalEdges_twice k (k - 1) a (by omega) (by omega)
  have hc := Nat.cast_choose_two ℚ (k - 1)
  have hk' : (4 : ℚ) ≤ k := by exact_mod_cast hk
  have ha' : (2 : ℚ) * a + 2 ≤ k := by
    exact_mod_cast (show 2 * a + 2 ≤ k by omega)
  have hpred : ((k - 1 : ℕ) : ℚ) = k - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hpred] at h hc
  have hm := mul_nonneg (show (0 : ℚ) ≤ a by positivity)
    (show (0 : ℚ) ≤ 2 * k - 5 - 3 * a by linarith)
  have hb : (pathExtremalEdges k (k - 1) a : ℚ) ≤ (k - 1).choose 2 := by nlinarith
  exact_mod_cast hb

lemma cone_nonempty_count (n k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) :
    r.choose 2 + (k + 1 - r) * (n + 1 - r) =
      n + pathExtremalEdges n (k - 1) (k - r) := by
  have hr' : r - 1 + 1 = r := by omega
  have hc := Nat.choose_succ_succ (r - 1) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hr', Nat.choose_one_right] at hc
  have h₁ : k - 1 - (k - r) = r - 1 := by omega
  have h₂ : n - (k - 1) + (k - r) = n + 1 - r := by omega
  have h₃ : k + 1 - r = k - r + 1 := by omega
  have h₄ : r - 1 + (n + 1 - r) = n := by omega
  simp only [pathExtremalEdges, h₁, h₂, h₃]
  nlinarith

lemma cone_empty_count_le (n k d : ℕ) (hkd₁ : 2 * d + 2 ≤ k)
    (hkd₂ : k ≤ 2 * d + 3) (hkn : k ≤ n) :
    (d + 1).choose 2 + (d + 1) * (n + 1 - (d + 1)) ≤
      n + pathExtremalEdges n (k - 1) d := by
  have hc₁ : (d + 1).choose 2 = d.choose 2 + d := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ d 1
  have hc₂ : (d + 2).choose 2 = d.choose 2 + 2 * d + 1 := by
    have h := Nat.choose_succ_succ (d + 1) 1
    simp only [Nat.choose_one_right] at h
    change (d + 2).choose 2 = d + 1 + (d + 1).choose 2 at h
    omega
  have hn₁ : n + 1 - (d + 1) = n - d := by omega
  have hcases : k = 2 * d + 2 ∨ k = 2 * d + 3 := by omega
  rcases hcases with rfl | rfl
  · have hK : 2 * d + 2 - 1 = 2 * d + 1 := by omega
    have hsub : 2 * d + 1 - d = d + 1 := by omega
    have hrest : n - (2 * d + 1) + d + 1 = n - d := by omega
    have hnd : n - d + d = n := by omega
    simp only [pathExtremalEdges, hK, hsub, hc₁, hn₁]
    nlinarith
  · have hK : 2 * d + 3 - 1 = 2 * d + 2 := by omega
    have hsub : 2 * d + 2 - d = d + 2 := by omega
    have hrest : n - (2 * d + 2) + d + 2 = n - d := by omega
    have hnd : n - d + d = n := by omega
    simp only [pathExtremalEdges, hK, hsub, hc₁, hc₂, hn₁]
    nlinarith

end Erdos1105

#print axioms Erdos1105.pathExtremalEdges_le_max
