import ErdosProblems.Erdos1148.ChartContainment
import ErdosProblems.Erdos1148.QuadraticRootCounts

/-!
# The second chart has the same root bound

When the leading coefficient is a unit, every root in the flipped chart is
a unit. Inverting the root embeds this set into the first chart's roots.
-/

namespace Erdos1148.DukeArithmetic

lemma discr_flipCoeffs {R : Type*} [CommRing R] (t : R × R × R) :
    discr (flipCoeffs t) = discr t := by dsimp [discr, flipCoeffs]; ring

lemma flipCoeffs_smul {R : Type*} [CommRing R] (a : R) (t : R × R × R) :
    flipCoeffs (a • t) = a • flipCoeffs t := by ext <;> simp [flipCoeffs]

lemma isUnit_of_flipped_root {R : Type*} [CommRing R]
    (t : R × R × R) (ha : IsUnit t.1) (x : R) (hx : neighborRemainder x (flipCoeffs t) = 0) :
    IsUnit x := by
  have heq : x * (t.2.1 - t.2.2 * x) = t.1 := by
    dsimp [neighborRemainder, flipCoeffs] at hx
    linear_combination hx
  exact (IsUnit.mul_iff.mp (heq.symm ▸ ha)).1

lemma reciprocal_flipped_root {R : Type*} [CommRing R]
    (t : R × R × R) (x y : R) (hxy : x * y = 1)
    (hx : neighborRemainder x (flipCoeffs t) = 0) : neighborRemainder y t = 0 := by
  dsimp [neighborRemainder, flipCoeffs] at hx ⊢
  linear_combination (t.2.1 * y - t.2.2 * (x * y + 1)) * hxy - y ^ 2 * hx

lemma zmod_inv_inv_of_unit {n : ℕ} (x : ZMod n) (hx : IsUnit x) : x⁻¹⁻¹ = x := by
  obtain ⟨u, rfl⟩ := hx
  rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_inv]

theorem quadraticRootResidues_flip_card_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) (ha : IsUnit t.1) :
    (quadraticRootResidues p n (flipCoeffs t)).card ≤ (quadraticRootResidues p n t).card := by
  classical
  let ρ := PadicInt.toZModPow n (p := p)
  have ha' : IsUnit (mapCoeffs ρ t).1 := ha.map ρ
  have hroot (x : ZMod (p ^ n)) (hx : x ∈ quadraticRootResidues p n (flipCoeffs t)) :
      neighborRemainder x (flipCoeffs (mapCoeffs ρ t)) = 0 := by
    rw [flipCoeffs_mapCoeffs]
    exact (Finset.mem_filter.mp hx).2
  have hunit (x : ZMod (p ^ n)) (hx : x ∈ quadraticRootResidues p n (flipCoeffs t)) :
      IsUnit x := isUnit_of_flipped_root (mapCoeffs ρ t) ha' x (hroot x hx)
  apply Finset.card_le_card_of_injOn (fun x : ZMod (p ^ n) => x⁻¹)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact reciprocal_flipped_root (mapCoeffs ρ t) x x⁻¹
      (ZMod.mul_inv_of_unit x (hunit x hx)) (hroot x hx)
  · intro x hx y hy hxy
    have h := congrArg (fun z : ZMod (p ^ n) => z⁻¹) hxy
    simpa only [zmod_inv_inv_of_unit x (hunit x hx), zmod_inv_inv_of_unit y (hunit y hy)] using h

theorem quadraticRootResidues_flip_card_le_of_scaled_unit (p : ℕ) [Fact p.Prime] (n r : ℕ)
    (t : PadicInt p × PadicInt p × PadicInt p) (ha : IsUnit t.1) (hD : discr t ≠ 0) :
    (quadraticRootResidues p n (flipCoeffs ((p : PadicInt p) ^ r • t))).card ≤
      8 * p ^ ((discr ((p : PadicInt p) ^ r • t)).valuation / 2) := by
  rw [flipCoeffs_smul]
  have hD' : discr (flipCoeffs t) ≠ 0 := by rwa [discr_flipCoeffs]
  have hbound (m : ℕ) : (quadraticRootResidues p m (flipCoeffs t)).card ≤
      8 * p ^ ((discr (flipCoeffs t)).valuation / 2) := by
    rw [discr_flipCoeffs]
    exact (quadraticRootResidues_flip_card_le p m t ha).trans
      (quadraticRootResidues_card_le_of_unit p m t ha hD)
  have h := quadraticRootResidues_card_le_of_scaled p n r (flipCoeffs t) hD' 8 (by decide) hbound
  simpa only [discr_smul, discr_flipCoeffs] using h

end Erdos1148.DukeArithmetic
