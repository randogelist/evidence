import ZetaBetaHankel.Zeta357DigitAdmissionParts.SourceDeterminantTransfer
import ZetaBetaHankel.Zeta357DigitAdmissionParts.RowDeterminantCore

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

namespace ZetaBetaHankel.Zeta357Canonical
open scoped BigOperators

structure RowRecurrence where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def recurrenceRow (s : RowRecurrence) (previous current : List ℤ) : List ℤ :=
  (List.range (current.length + 1)).map fun j =>
    (s.a * (if j = 0 then 0 else current.getD (j - 1) 0) +
      s.b * current.getD j 0 + s.c * previous.getD j 0) / s.d


end ZetaBetaHankel.Zeta357Canonical
