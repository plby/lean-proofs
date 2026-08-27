import ErdosProblems.Erdos587.GAPDilationCover
import ErdosProblems.Erdos587.NVDevelopment

/-! # Polynomial translate covers of dilated coefficient boxes -/

open scoped Pointwise

namespace Erdos587.CFP

theorem delta_coordBox_dilate_cover {d : ℕ} (L : Fin d → ℕ) (c : ℕ) (hc : 0 < c) :
    ∃ F : Finset (Fin d → ℤ), F.card ≤ c ^ d ∧
      nvCoordBox (fun i => c * L i) ⊆ F + nvCoordBox L := by
  classical
  let offset : (Fin d → Fin c) → Fin d → ℤ := fun u i => (u i : ℤ) * (L i + 1)
  let F := Finset.univ.image offset
  refine ⟨F, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro x hx
    have hx' := mem_nvCoordBox_iff.mp hx
    have hxNat (i : Fin d) : (x i).toNat ≤ c * L i := by
      exact Int.toNat_le.mpr (hx' i).2
    let u : Fin d → Fin c := fun i => ⟨(x i).toNat / (L i + 1), by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
      have := hxNat i
      nlinarith⟩
    let r : Fin d → ℤ := fun i => ((x i).toNat % (L i + 1) : ℕ)
    have hr : r ∈ nvCoordBox L := by
      apply mem_nvCoordBox_iff.mpr
      intro i
      constructor
      · positivity
      · change (((x i).toNat % (L i + 1) : ℕ) : ℤ) ≤ (L i : ℤ)
        exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt (x i).toNat (Nat.succ_pos (L i)))
    refine Finset.mem_add.mpr ⟨offset u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩,
      r, hr, ?_⟩
    funext i
    have hh : (u i : ℕ) * (L i + 1) + (x i).toNat % (L i + 1) = (x i).toNat := by
      dsimp only [u]
      simpa only [Nat.mul_comm] using Nat.div_add_mod (x i).toNat (L i + 1)
    have hcast : (u i : ℤ) * ((L i : ℤ) + 1) + ((x i).toNat % (L i + 1) : ℕ) = x i := by
      have hh' : (u i : ℤ) * ((L i : ℤ) + 1) + ((x i).toNat % (L i + 1) : ℕ) =
          ((x i).toNat : ℤ) := by exact_mod_cast hh
      exact hh'.trans (Int.toNat_of_nonneg (hx' i).1)
    exact hcast

end Erdos587.CFP
