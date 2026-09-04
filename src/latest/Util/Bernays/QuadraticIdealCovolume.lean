import Util.Bernays.QuadraticComplexLattice

/-!
# Covolume and index of arbitrary quadratic-order ideals
-/

namespace Bernays

theorem quadraticIdealLattice_covolume {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    ZLattice.covolume (quadraticIdealLattice d b I) =
      (I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤) := by
  let := quadraticIdealLattice_discrete hD I
  let := quadraticIdealLattice_full hD I hI
  let := quadraticIdealLattice_discrete hD ⊤
  let := quadraticIdealLattice_full hD ⊤ top_ne_bot
  have hle : quadraticIdealLattice d b I ≤ quadraticIdealLattice d b ⊤ :=
    Submodule.map_mono le_top
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (quadraticIdealLattice d b I) (quadraticIdealLattice d b ⊤) hle
  have hindex : (quadraticIdealLattice d b I).toAddSubgroup.relIndex
      (quadraticIdealLattice d b ⊤).toAddSubgroup = I.cardQuot := by
    change (I.toAddSubgroup.map (quadraticComplexMap d b).toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup (QuadraticAlgebra ℤ d b)).map (quadraticComplexMap d b).toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ (quadraticComplexMap_injective hD),
      AddSubgroup.relIndex_top_right]
    rfl
  rw [hindex] at h
  exact (div_eq_iff (ZLattice.covolume_pos (quadraticIdealLattice d b ⊤)).ne').mp h

end Bernays
