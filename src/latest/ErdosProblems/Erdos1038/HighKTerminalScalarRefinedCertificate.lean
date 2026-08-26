import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk000
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk001
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk002
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk003
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk004
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk005
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk006
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk007
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk008
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk009
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk010
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk011
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk012
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk013
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk014
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk015
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk016
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk017
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk018
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedChunk019

/-! Complete proof-producing terminal scalar list certificate. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKTerminalFormula.CertificateData

open Erdos1038.OneCutTailCertificate

theorem refined_certified : AllRefinedCertified refinedData := by
  have h020 : AllRefinedCertified ([] : List RefinedData) := by
    simp [AllRefinedCertified]
  have h019 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk019.certified h020
  have h018 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk018.certified h019
  have h017 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk017.certified h018
  have h016 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk016.certified h017
  have h015 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk015.certified h016
  have h014 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk014.certified h015
  have h013 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk013.certified h014
  have h012 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk012.certified h013
  have h011 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk011.certified h012
  have h010 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk010.certified h011
  have h009 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk009.certified h010
  have h008 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk008.certified h009
  have h007 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk007.certified h008
  have h006 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk006.certified h007
  have h005 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk005.certified h006
  have h004 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk004.certified h005
  have h003 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk003.certified h004
  have h002 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk002.certified h003
  have h001 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk001.certified h002
  have h000 := AllRefinedCertified.append
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk000.certified h001
  simpa [
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk000.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk001.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk002.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk003.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk004.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk005.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk006.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk007.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk008.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk009.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk010.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk011.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk012.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk013.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk014.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk015.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk016.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk017.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk018.items,
    Erdos1038.HighKTerminalFormula.CertificateData.RefinedChunk019.items,
    refinedData] using! h000

end Erdos1038.HighKTerminalFormula.CertificateData
