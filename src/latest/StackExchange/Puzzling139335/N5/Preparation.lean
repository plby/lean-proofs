import StackExchange.Puzzling139335.N5.Prepared
import StackExchange.Puzzling139335.N5.FourthSide
import StackExchange.Puzzling139335.N5.StrictFrame
import StackExchange.Puzzling139335.N5.RightArm
import StackExchange.Puzzling139335.N5.TopContacts
import StackExchange.Puzzling139335.N5Facet.Trigonometry

/-!
# Constructing the final actual five-incidence configuration

All support parameters and complete contact intervals are derived here
from the dissection.  The singleton piece is excluded from the center,
so the corner-free piece is its actual owner.
-/

open Set

namespace Puzzling139335.N5

/-- Every normalized protected-center dissection yields actual data for
the final support calculation, after at most a common diagonal reflection
and relabeling. -/
theorem Normalized.exists_prepared {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ∃ d' : SquareDissection, Nonempty (Prepared d') := by
  obtain ⟨d', b, hn, _hsource, hcenter, _hrightsingle, hb, hb₁, hRight₀, hRight₂,
    _hsegment⟩ := h.exists_fourth_right_geometry hc
  have hc' : d'.HasProtectedCenter := hcenter.mpr hc
  obtain ⟨eR, heR⟩ := d'.congruent 0 2
  obtain ⟨θ, hθ, hk, hkh, hhc, hc₁, hz, hd, hf⟩ :=
    hn.exists_strict_corner_angle hc' eR heR
  have hunit : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  obtain ⟨hcos, hsin⟩ := N5Facet.acute_trig_pos hθ.1 hθ.2
  have hsc := N5Facet.sin_lt_cos hθ.1 hθ.2
  have hCy := hkh.trans hhc
  have hE₀ : Schoenflies.Plane.mk 1 b ∈ d'.piece 0 :=
    (hRight₀ b).mpr ⟨hb.le, le_rfl⟩
  have hE₂ : Schoenflies.Plane.mk 1 b ∈ d'.piece 2 :=
    (hRight₂ b).mpr ⟨le_rfl, hb₁.le⟩
  have hratio := hn.right_contact_lt_frame_ratio eR heR hunit hcos hsin hf hE₀
  have hratiohalf : Real.sin θ / (1 + Real.cos θ) < 1 / 2 := by
    apply (div_lt_iff₀ (by linarith only [hcos] : 0 < 1 + Real.cos θ)).mpr
    linarith only [hsc, hc₁]
  have hbhalf : b < 1 / 2 := hratio.trans hratiohalf
  have hform := right_arm_swapped_form_of_contact d' eR heR hf hunit hcos hsin hc₁ hb
    hCy hE₀ hE₂
  have hnotR := hn.center_not_mem_singleton_of_right_contact eR heR hf hunit hcos hsin
    hsc hc₁ hhc hCy hb hbhalf hE₀ hE₂
  have hcenterD : squareCenter ∈ interior (d'.piece 3) := by
    obtain ⟨i, hi⟩ := hc'
    rcases hn.center_owner_cases hi with rfl | rfl
    · exact (hnotR (interior_subset hi)).elim
    · exact hi
  obtain ⟨m, hbm, hm, hTop₂, hTop₃⟩ := hn.exists_top_contact_partition_of_swapped_form
    eR heR hunit hcos hsin hc₁ hb hb₁ hCy hform hRight₀
  obtain ⟨eD, heD⟩ := d'.congruent 0 3
  refine ⟨d', ⟨{
    normalized := hn
    eR := eR
    eD := eD
    image_R := heR
    image_D := heD
    C := eR.symm (corner 2)
    C_eq := rfl
    θ := θ
    angle := hθ
    C_height_pos := hk
    C_height_lt_first := hkh
    C_first_lt_cos := hhc
    cos_lt_one := hc₁
    transverse_pos := hz
    support_lt_one := hd
    b := b
    m := m
    b_pos := hb
    b_lt_half := hbhalf
    b_lt_ratio := hratio
    b_lt_m := hbm
    m_lt_one := hm
    R_form := hform
    right_source := hRight₀
    right_singleton := hRight₂
    top_singleton := hTop₂
    top_fourth := hTop₃
    center_fourth := hcenterD
  }⟩⟩

end Puzzling139335.N5
