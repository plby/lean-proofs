import ErdosProblems.Erdos19.SizeWindowColoring

/-! # A uniform saving for edge-size windows below the projective scale -/

namespace Erdos19

theorem size_window_degree_margin (n q r R : ℕ) (hq : 0 < q)
    (hn : 4 * q ≤ n) (hr : 32 * q ≤ r) (hR : R ≤ r + r / (16 * q)) :
    R * n ≤ (n + n / (2 * q)) * (r - 1) := by
  let m := n / (2 * q)
  have hq2 : 0 < 2 * q := by omega
  have hm : 2 ≤ m := (Nat.le_div_iff_mul_le hq2).mpr (by omega)
  have hfloor := Nat.lt_mul_div_succ n hq2
  have hn' : n ≤ 4 * q * m := by
    change n < 2 * q * (m + 1) at hfloor
    nlinarith only [hfloor, Nat.mul_le_mul_left (2 * q) (show m + 1 ≤ 2 * m by omega)]
  have hdiv := Nat.mul_div_le r (16 * q)
  have hrmargin : 4 * q * (r / (16 * q) + 1) ≤ r - 1 := by
    have hrsub : r - 1 + 1 = r := by omega
    nlinarith only [hdiv, hr, hrsub, hq]
  have h₁ := Nat.mul_le_mul_right (r / (16 * q) + 1) hn'
  have h₂ := Nat.mul_le_mul_left m hrmargin
  have h₃ := Nat.mul_le_mul_right n hR
  have hrsub : r - 1 + 1 = r := by omega
  change R * n ≤ (n + m) * (r - 1)
  nlinarith only [h₁, h₂, h₃, congrArg (fun x ↦ x * n) hrsub]

theorem size_window_common_gap (h n r R D : ℕ) (hh : 2 ≤ h) (hn : n ≤ D)
    (hr : h + 1 ≤ r) (hR : h * R ^ 2 ≤ (h - 2) * n) :
    (R - 1) ^ 2 + (n - 1) / (r - 1) + D / h ≤ D := by
  have hhpos : 0 < h := by omega
  have hdiv : h * ((n - 1) / (r - 1)) ≤ n :=
    ((Nat.mul_le_mul_right _ (show h ≤ r - 1 by omega)).trans (Nat.mul_div_le (n - 1) (r - 1))).trans
      (Nat.sub_le n 1)
  have hR' : h * (R - 1) ^ 2 ≤ h * R ^ 2 :=
    Nat.mul_le_mul_left h (Nat.pow_le_pow_left (Nat.sub_le R 1) 2)
  have hscale := Nat.mul_le_mul_left (h - 1) hn
  have hfloor := Nat.mul_div_le D h
  have hhsub : h - 2 + 2 = h := by omega
  have hhsub' : h - 1 + 1 = h := by omega
  apply Nat.le_of_mul_le_mul_left (c := h) _ hhpos
  nlinarith only [hdiv, hR', hR, hscale, hfloor,
    congrArg (fun x ↦ x * n) hhsub, congrArg (fun x ↦ x * n) hhsub',
    congrArg (fun x ↦ x * D) hhsub']

theorem size_window_palette_saving (n q : ℕ) (hq : 0 < q) :
    (n + n / (2 * q)) - (n + n / (2 * q)) / q ≤ n - n / (2 * q) := by
  have hmul := Nat.mul_div_le n (2 * q)
  have hsmall : n / (2 * q) ≤ n := Nat.div_le_self _ _
  have hdiv : 2 * (n / (2 * q)) ≤ (n + n / (2 * q)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      2 * (n / (2 * q)) * q = 2 * q * (n / (2 * q)) := by ring
      _ ≤ n := hmul
      _ ≤ n + n / (2 * q) := Nat.le_add_right _ _
  omega

namespace SetHypergraph

theorem eventually_edgeColorable_of_subprojective_window (h : ℕ) (hh : 2 ≤ h) :
    ∃ q : ℕ, 0 < q ∧ ∃ N : ℕ, 4 * q ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → ∀ r R : ℕ,
      32 * q ≤ r → h + 1 ≤ r →
      (∀ e : H, r ≤ e.1.ncard) → (∀ e : H, e.1.ncard ≤ R) →
      R ≤ r + r / (16 * q) → h * R ^ 2 ≤ (h - 2) * n →
      H.EdgeColorable (n - n / (2 * q)) := by
  obtain ⟨q, hq, N₀, _, hcolor⟩ := eventually_edgeColorable_of_size_window h (by omega)
  refine ⟨q, hq, max N₀ (4 * q), le_max_right _ _, ?_⟩
  intro n hn H hlinear r R hrq hrh hmin hmax hwidth hR
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnq : 4 * q ≤ n := (le_max_right _ _).trans hn
  have hc := hcolor (n + n / (2 * q)) (hn₀.trans (Nat.le_add_right _ _))
    (Fin n) H hlinear r R (by omega) hmin hmax
    (by simpa only [Fintype.card_fin] using size_window_degree_margin n q r R hq hnq hrq hwidth)
    (by simpa only [Fintype.card_fin] using (size_window_common_gap h n r R
      (n + n / (2 * q)) hh (Nat.le_add_right _ _) hrh hR))
  exact hc.mono (size_window_palette_saving n q hq)

#print axioms eventually_edgeColorable_of_subprojective_window

end SetHypergraph
end Erdos19
