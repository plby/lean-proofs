import ErdosProblems.Erdos633b.CaseFiveAngles
import ErdosProblems.Erdos633b.DoubledOrdering

/-! Attach the last enlarged reference tile with exact coverage, disjointness, and count. -/

namespace Erdos633b.CaseFiveCoordinates

open Sixty

noncomputable def attached_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (attached d hd a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hm)).support ((m * (a + 2 * b)) ^ 2) := by
  apply quadratic_patch_permuted _ _ (Equiv.swap 0 2) (m * (a + 2 * b))
    (mul_pos hm (by omega))
  intro i
  rw [attached_sides d hd he a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hm) (by exact_mod_cast hrel),
    reference_sides d hd he a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hc) (by exact_mod_cast hrel)]
  push_cast
  congr 1
  fin_cases i <;> rfl

noncomputable def attach_doubled_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (patch : Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (DoubledCoordinates.outer d hd a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hm)).support
      (m ^ 2 * (a + 2 * b) * (2 * a + b))) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (outer d hd a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hm)).support
      (3 * m ^ 2 * (a + 2 * b) * (a + b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let S := DoubledCoordinates.outer d hd a b c m har hbr hcr hmr
  let U := outer d hd a b c m har hbr hcr hmr
  let R := groupTwoReference d hd a b har hbr
  let t := extensionRatio a b
  have ht : 0 < t := extensionRatio_pos a b har hbr
  have first : Patch R (U.edgeFirst (1 / (1 + t)) (Triangle.extension_weight_pos t ht)).support
      (m ^ 2 * (a + 2 * b) * (2 * a + b)) := by
    have hfirst : U.edgeFirst (1 / (1 + t)) (Triangle.extension_weight_pos t ht) = S :=
      S.edgeExtension_first t ht
    rw [hfirst]
    exact patch
  have second : Patch R
      (U.edgeSecond (1 / (1 + t)) (Triangle.extension_weight_lt_one t ht)).support
      ((m * (a + 2 * b)) ^ 2) := attached_patch d hd he a b c m ha hb hc hm hrel
  have result := first.glueTwo second (U.edgeParts_disjoint_interiors (1 / (1 + t))
    (Triangle.extension_weight_pos t ht) (Triangle.extension_weight_lt_one t ht))
  rw [U.edgeParts_cover (1 / (1 + t)) (Triangle.extension_weight_pos t ht)
    (Triangle.extension_weight_lt_one t ht)] at result
  have hn : m ^ 2 * (a + 2 * b) * (2 * a + b) + (m * (a + 2 * b)) ^ 2 =
      3 * m ^ 2 * (a + 2 * b) * (a + b) := by ring
  rwa [hn] at result

theorem integer_tiling_exists (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ m : ℕ, ∃ hm : 0 < m,
      Nonempty (Tiling (outer d hd a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hm)) (3 * m ^ 2 * (a + 2 * b) * (a + b))) := by
  obtain ⟨m, hm, ⟨patch⟩⟩ := DoubledCoordinates.doubled_patch_exists d hd he a b c ha hb hc hrel
  exact ⟨m, hm, ⟨(attach_doubled_patch d hd he a b c m ha hb hc hm hrel patch).toTiling⟩⟩

end Erdos633b.CaseFiveCoordinates
