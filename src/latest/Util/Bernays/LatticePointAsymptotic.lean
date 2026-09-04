import Util.Bernays.LatticeCellBounds
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Uniform boundary error for lattice translates in the complex plane
-/

open MeasureTheory Metric Set Module
open scoped Classical

namespace Bernays

def latticeCosetBall (L : Submodule ℤ ℂ) (a : ℂ) (R : ℝ) : Set L :=
  {l | ‖a + (l : ℂ)‖ ≤ R}

theorem finite_latticeCosetBall (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (a : ℂ) (R : ℝ) : (latticeCosetBall L a R).Finite := by
  have hclosed : IsClosed (L : Set ℂ) :=
    AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hfinite : (closedBall (-a) R ∩ (L : Set ℂ)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall hclosed
  have hpre := hfinite.preimage (f := ((↑) : L → ℂ)) Subtype.val_injective.injOn
  convert hpre using 1
  ext l
  simp only [latticeCosetBall, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
    mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm]
  exact (and_iff_left l.2).symm

theorem latticeCosetBall_error (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℂ, ∀ R : ℝ, 0 ≤ R →
      |(Nat.card (latticeCosetBall L a R) : ℝ) - Real.pi / ZLattice.covolume L * R ^ 2| ≤
        K * (R + 1) := by
  let b := Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  obtain ⟨B₀, hB₀⟩ := (isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)))
  let B := max B₀ 0
  have hB : ∀ z ∈ F, ‖z‖ ≤ B := fun z hz => (hB₀ z hz).trans (le_max_left _ _)
  have hBpos : 0 ≤ B := le_max_right _ _
  have hF := ZLattice.isAddFundamentalDomain b volume
  have hcovol : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hc : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  let K := Real.pi * (2 * B + B ^ 2 + 1) / ZLattice.covolume L
  have hK : 0 < K := div_pos (mul_pos Real.pi_pos (by nlinarith [sq_nonneg B])) hc
  refine ⟨K, hK, ?_⟩
  intro a R hR
  let S := (finite_latticeCosetBall L a R).toFinset
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hS (l : L) : l ∈ S ↔ ‖a + (l : ℂ)‖ ≤ R := Set.Finite.mem_toFinset _
  have herr := complex_fundamental_cell_error L.toAddSubgroup hF hBpos hB hR a S hS
  have hcard : (S.card : ℝ) = Nat.card (latticeCosetBall L a R) := by
    exact_mod_cast (Set.ncard_eq_toFinset_card (latticeCosetBall L a R)
      (finite_latticeCosetBall L a R)).symm
  rw [hcard, ← hcovol] at herr
  have hdiv := div_le_div_of_nonneg_right herr hc.le
  have heq : |(Nat.card (latticeCosetBall L a R) : ℝ) * ZLattice.covolume L - Real.pi * R ^ 2| /
      ZLattice.covolume L =
      |(Nat.card (latticeCosetBall L a R) : ℝ) - Real.pi / ZLattice.covolume L * R ^ 2| := by
    rw [← abs_of_pos hc]
    rw [← abs_div, abs_of_pos hc]
    congr 1
    field_simp
  rw [heq] at hdiv
  apply hdiv.trans
  dsimp only [K]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hc.le
  rw [mul_assoc Real.pi (2 * B + B ^ 2 + 1) (R + 1)]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) hR]

end Bernays
