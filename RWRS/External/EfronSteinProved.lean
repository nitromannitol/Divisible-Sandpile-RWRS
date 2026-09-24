import RWRS.External.EfronStein
import RWRS.Support.EfronStein

-- FROZEN-STATEMENT-BEGIN
/-- The Efron--Stein inequality for a countable i.i.d. field.
Cited in `rwrs.tex:694-699`; proved by the shared library. -/
theorem RWRS.External.efronStein (V : Type*) [Countable V] :
    RWRS.External.EfronStein V
-- FROZEN-STATEMENT-END
:= by
  exact RWRS.Support.efronStein V
