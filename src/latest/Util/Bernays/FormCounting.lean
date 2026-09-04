import Util.Bernays.FullClassAsymptotic
import Util.Bernays.CanonicalFormClass

/-!
# Exact transport from ideal-class norm counts to the original form count
-/

open Filter Topology
open scoped Classical

namespace BinQuadForm

theorem B_nat_eq_positiveValues_add_one (f : BinQuadForm) (N : ℕ) :
    f.B (N : ℝ) = (Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N).card + 1 := by
  rw [f.B_eq_card_filter (Nat.cast_nonneg N), Nat.floor_natCast]
  have hset : (Finset.range (N + 1)).filter (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ)) =
      insert 0 (Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_lt_succ, Nat.cast_zero,
        true_and, Finset.mem_insert, true_or]
      exact iff_true_intro ⟨0, 0, f.eval_zero_zero⟩
    · simp only [Finset.mem_filter, Finset.mem_range, Bernays.positiveValues,
        Finset.mem_insert, hn, false_or, Finset.mem_filter, Finset.mem_Icc, Nat.lt_succ_iff]
      have hpos : 1 ≤ n := by omega
      simp only [hpos, true_and]
  rw [hset, Finset.card_insert_of_notMem]
  simp [Bernays.positiveValues]

theorem positiveValues_eq_canonicalClassValues {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive)
    (N : ℕ) :
    let hD := f.canonical_order_discr.trans_lt hf.2
    letI := Bernays.quadraticOrderIsDomain hD
    Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N =
      Bernays.classValues hD (f.canonicalClass hf hp)⁻¹ N := by
  let hD := f.canonical_order_discr.trans_lt hf.2
  let := Bernays.quadraticOrderIsDomain hD
  ext n
  simp only [Bernays.classValues, Bernays.positiveValues, Finset.mem_filter]
  apply and_congr_right
  intro hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [represented_pos_iff_canonicalClass_norm hf hp hnpos]
  apply exists_congr
  intro J
  rw [eq_inv_iff_mul_eq_one]
  exact and_comm

theorem B_nat_limit {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    Tendsto (fun N : ℕ => (f.B (N : ℝ) : ℝ) / Bernays.scale N)
      atTop (𝓝 (Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2))) := by
  let hD := f.canonical_order_discr.trans_lt hf.2
  let := Bernays.quadraticOrderIsDomain hD
  have hclass := Bernays.classValues_card_limit hD (f.canonicalClass hf hp)⁻¹
  have hone : Tendsto (fun N : ℕ => 1 / Bernays.scale N) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Bernays.scale_tendsto_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := hclass.add hone
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [B_nat_eq_positiveValues_add_one, positiveValues_eq_canonicalClassValues hf hp,
    Nat.cast_add, Nat.cast_one, add_div]

end BinQuadForm
