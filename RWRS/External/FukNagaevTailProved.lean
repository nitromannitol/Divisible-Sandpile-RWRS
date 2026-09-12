import RWRS.External.FukNagaevTail
import LatticeProb.Prob.FukNagaev

-- FROZEN-STATEMENT-BEGIN
/-- The Fuk--Nagaev tail inequality for independent centred summands.
Cited in `rwrs.tex:1096-1098`; proved by the shared library. -/
theorem RWRS.External.fukNagaevTail : RWRS.External.FukNagaevTail
-- FROZEN-STATEMENT-END
:= by
  exact LatticeProb.fukNagaev_tail
