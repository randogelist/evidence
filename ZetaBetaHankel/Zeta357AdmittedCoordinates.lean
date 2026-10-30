import ZetaBetaHankel.Zeta357DigitAdmissionParts.Base
import ZetaBetaHankel.Zeta357Chain

/-!
# Explicit admission of the original computed coordinates

The coordinate literals remain exactly those in the imported `Base` module:
`coeff3`, `coeff5`, `coeff7`, `zetaBox3`, `zetaBox5`, `zetaBox7`, the common
denominator, and the three Horner traces. No new search or replacement
coordinates are introduced here.

The single named axiom below admits `CanonicalSemantics`, whose six fields
identify the three canonical polynomials with those coefficient lists and put
the three actual zeta values in those fixed input boxes. The imported interval
checker, degree proofs, and exact seed/transfer checks derive `N0Admission`
from these admitted coordinate semantics.

Thus `actualN0Admission` and `goodAt_zero` have no explicit theorem arguments,
but their axiom audits must show `actualCoordinateAdmission`. This is an
intentional coordinate admission, not a proof of that admitted proposition.

Cofinality and irrationality are not admitted. The final irrationality theorem
retains the explicit strict-extension premise of the checked skeleton.
-/

noncomputable section
set_option format.width 100000

namespace ZetaBetaHankel.Zeta357AdmittedCoordinates

open ZetaBetaHankel.Zeta357CandidateN0 ZetaBetaHankel.Zeta357Chain

/-- The user-authorized admission of the six source/actual-value coordinate
bridges for the fixed original literals. This is the only custom axiom added
by this module. -/
axiom actualCoordinateAdmission :
  ZetaBetaHankel.Zeta357DigitAdmission.CanonicalSemantics

/-- Actual finite admission derived from the named coordinate admission and
the kernel-checked finite computations in `Base`. -/
theorem actualN0Admission : N0Admission :=
  ZetaBetaHankel.Zeta357DigitAdmission.admission_of_semantics
    actualCoordinateAdmission

/-- The admitted coordinate point meets the existing common point predicate. -/
theorem goodAt_zero : GoodAt 0 :=
  good_zero_of_admission actualN0Admission

/-- Strict extension remains an explicit input; it is not part of the axiom. -/
theorem actualCofinal_of_extension (hext : StrictExtension) : CofinalGood :=
  cofinal_of_good_zero_and_extension goodAt_zero hext

/-- The admitted coordinates join the independently checked irrationality
skeleton. The remaining premise is shown fully rather than hidden in a record. -/
theorem actual_zeta357_irrational
    (hext : ∀ n : ℕ, GoodAt n → ∃ m : ℕ, n < m ∧ GoodAt m) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 3) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) :=
  zeta357_actual_values_of_cofinal (actualCofinal_of_extension hext)

set_option pp.fullNames true in
#check @actualCoordinateAdmission
set_option pp.fullNames true in
#check @actualN0Admission
set_option pp.fullNames true in
#check @goodAt_zero
set_option pp.fullNames true in
#check @actualCofinal_of_extension
set_option pp.fullNames true in
#check @actual_zeta357_irrational

#print axioms actualCoordinateAdmission
#print axioms actualN0Admission
#print axioms goodAt_zero
#print axioms actualCofinal_of_extension
#print axioms actual_zeta357_irrational

end ZetaBetaHankel.Zeta357AdmittedCoordinates
