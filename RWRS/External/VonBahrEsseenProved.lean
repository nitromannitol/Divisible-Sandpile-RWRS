import RWRS.External.VonBahrEsseen
import LatticeProb.Prob.VonBahrEsseenSum

-- FROZEN-STATEMENT-BEGIN
/-- The von Bahr--Esseen tail inequality for independent centred summands.
Cited in `rwrs.tex:1096-1098`; proved by the shared library. -/
theorem RWRS.External.vonBahrEsseen : RWRS.External.VonBahrEsseen
-- FROZEN-STATEMENT-END
:= by
  exact LatticeProb.vonBahrEsseen
