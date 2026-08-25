import ErdosProblems.Erdos1058.Erdos1058PeriodicData0
import ErdosProblems.Erdos1058.Erdos1058PeriodicData1
import ErdosProblems.Erdos1058.Erdos1058PeriodicData2
import ErdosProblems.Erdos1058.Erdos1058PeriodicData3

namespace Erdos1058.PeriodicSieveCertificate

/-- The two mixed cubic characters are obstructed for every relevant even gap. -/
theorem gap_obstructions {d : ℕ}
    (hpos : 0 < d) (hle : d ≤ 210) (heven : d % 2 = 0) :
    Obstruction d 0 ∧ Obstruction d 1 := by
  interval_cases d <;> norm_num at hpos heven
  · exact ⟨periodic_2_0, periodic_2_1⟩
  · exact ⟨periodic_4_0, periodic_4_1⟩
  · exact ⟨periodic_6_0, periodic_6_1⟩
  · exact ⟨periodic_8_0, periodic_8_1⟩
  · exact ⟨periodic_10_0, periodic_10_1⟩
  · exact ⟨periodic_12_0, periodic_12_1⟩
  · exact ⟨periodic_14_0, periodic_14_1⟩
  · exact ⟨periodic_16_0, periodic_16_1⟩
  · exact ⟨periodic_18_0, periodic_18_1⟩
  · exact ⟨periodic_20_0, periodic_20_1⟩
  · exact ⟨periodic_22_0, periodic_22_1⟩
  · exact ⟨periodic_24_0, periodic_24_1⟩
  · exact ⟨periodic_26_0, periodic_26_1⟩
  · exact ⟨periodic_28_0, periodic_28_1⟩
  · exact ⟨periodic_30_0, periodic_30_1⟩
  · exact ⟨periodic_32_0, periodic_32_1⟩
  · exact ⟨periodic_34_0, periodic_34_1⟩
  · exact ⟨periodic_36_0, periodic_36_1⟩
  · exact ⟨periodic_38_0, periodic_38_1⟩
  · exact ⟨periodic_40_0, periodic_40_1⟩
  · exact ⟨periodic_42_0, periodic_42_1⟩
  · exact ⟨periodic_44_0, periodic_44_1⟩
  · exact ⟨periodic_46_0, periodic_46_1⟩
  · exact ⟨periodic_48_0, periodic_48_1⟩
  · exact ⟨periodic_50_0, periodic_50_1⟩
  · exact ⟨periodic_52_0, periodic_52_1⟩
  · exact ⟨periodic_54_0, periodic_54_1⟩
  · exact ⟨periodic_56_0, periodic_56_1⟩
  · exact ⟨periodic_58_0, periodic_58_1⟩
  · exact ⟨periodic_60_0, periodic_60_1⟩
  · exact ⟨periodic_62_0, periodic_62_1⟩
  · exact ⟨periodic_64_0, periodic_64_1⟩
  · exact ⟨periodic_66_0, periodic_66_1⟩
  · exact ⟨periodic_68_0, periodic_68_1⟩
  · exact ⟨periodic_70_0, periodic_70_1⟩
  · exact ⟨periodic_72_0, periodic_72_1⟩
  · exact ⟨periodic_74_0, periodic_74_1⟩
  · exact ⟨periodic_76_0, periodic_76_1⟩
  · exact ⟨periodic_78_0, periodic_78_1⟩
  · exact ⟨periodic_80_0, periodic_80_1⟩
  · exact ⟨periodic_82_0, periodic_82_1⟩
  · exact ⟨periodic_84_0, periodic_84_1⟩
  · exact ⟨periodic_86_0, periodic_86_1⟩
  · exact ⟨periodic_88_0, periodic_88_1⟩
  · exact ⟨periodic_90_0, periodic_90_1⟩
  · exact ⟨periodic_92_0, periodic_92_1⟩
  · exact ⟨periodic_94_0, periodic_94_1⟩
  · exact ⟨periodic_96_0, periodic_96_1⟩
  · exact ⟨periodic_98_0, periodic_98_1⟩
  · exact ⟨periodic_100_0, periodic_100_1⟩
  · exact ⟨periodic_102_0, periodic_102_1⟩
  · exact ⟨periodic_104_0, periodic_104_1⟩
  · exact ⟨periodic_106_0, periodic_106_1⟩
  · exact ⟨periodic_108_0, periodic_108_1⟩
  · exact ⟨periodic_110_0, periodic_110_1⟩
  · exact ⟨periodic_112_0, periodic_112_1⟩
  · exact ⟨periodic_114_0, periodic_114_1⟩
  · exact ⟨periodic_116_0, periodic_116_1⟩
  · exact ⟨periodic_118_0, periodic_118_1⟩
  · exact ⟨periodic_120_0, periodic_120_1⟩
  · exact ⟨periodic_122_0, periodic_122_1⟩
  · exact ⟨periodic_124_0, periodic_124_1⟩
  · exact ⟨periodic_126_0, periodic_126_1⟩
  · exact ⟨periodic_128_0, periodic_128_1⟩
  · exact ⟨periodic_130_0, periodic_130_1⟩
  · exact ⟨periodic_132_0, periodic_132_1⟩
  · exact ⟨periodic_134_0, periodic_134_1⟩
  · exact ⟨periodic_136_0, periodic_136_1⟩
  · exact ⟨periodic_138_0, periodic_138_1⟩
  · exact ⟨periodic_140_0, periodic_140_1⟩
  · exact ⟨periodic_142_0, periodic_142_1⟩
  · exact ⟨periodic_144_0, periodic_144_1⟩
  · exact ⟨periodic_146_0, periodic_146_1⟩
  · exact ⟨periodic_148_0, periodic_148_1⟩
  · exact ⟨periodic_150_0, periodic_150_1⟩
  · exact ⟨periodic_152_0, periodic_152_1⟩
  · exact ⟨periodic_154_0, periodic_154_1⟩
  · exact ⟨periodic_156_0, periodic_156_1⟩
  · exact ⟨periodic_158_0, periodic_158_1⟩
  · exact ⟨periodic_160_0, periodic_160_1⟩
  · exact ⟨periodic_162_0, periodic_162_1⟩
  · exact ⟨periodic_164_0, periodic_164_1⟩
  · exact ⟨periodic_166_0, periodic_166_1⟩
  · exact ⟨periodic_168_0, periodic_168_1⟩
  · exact ⟨periodic_170_0, periodic_170_1⟩
  · exact ⟨periodic_172_0, periodic_172_1⟩
  · exact ⟨periodic_174_0, periodic_174_1⟩
  · exact ⟨periodic_176_0, periodic_176_1⟩
  · exact ⟨periodic_178_0, periodic_178_1⟩
  · exact ⟨periodic_180_0, periodic_180_1⟩
  · exact ⟨periodic_182_0, periodic_182_1⟩
  · exact ⟨periodic_184_0, periodic_184_1⟩
  · exact ⟨periodic_186_0, periodic_186_1⟩
  · exact ⟨periodic_188_0, periodic_188_1⟩
  · exact ⟨periodic_190_0, periodic_190_1⟩
  · exact ⟨periodic_192_0, periodic_192_1⟩
  · exact ⟨periodic_194_0, periodic_194_1⟩
  · exact ⟨periodic_196_0, periodic_196_1⟩
  · exact ⟨periodic_198_0, periodic_198_1⟩
  · exact ⟨periodic_200_0, periodic_200_1⟩
  · exact ⟨periodic_202_0, periodic_202_1⟩
  · exact ⟨periodic_204_0, periodic_204_1⟩
  · exact ⟨periodic_206_0, periodic_206_1⟩
  · exact ⟨periodic_208_0, periodic_208_1⟩
  · exact ⟨periodic_210_0, periodic_210_1⟩

end Erdos1058.PeriodicSieveCertificate
