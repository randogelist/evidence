import ZetaBetaHankel.Zeta357DigitAdmission
import ZetaBetaHankel.Zeta357Chain

/-!
# Computed coordinate admission joined to the irrationality skeleton

The finite admission in this module is supplied by `actualN0Admission`, whose
proof source traces back to the original coordinate literals. The remaining
argument is `StrictExtension`: every common good index has a strictly larger
common good index. This module does not supply that extension theorem.

The declarations below are candidates until their compilation and their
transitive axiom reports pass on the intended toolchain.
-/

noncomputable section

namespace ZetaBetaHankel.Zeta357VerifiedChain

open ZetaBetaHankel.Zeta357CandidateN0 ZetaBetaHankel.Zeta357Chain

/-- The actual coordinate-derived finite point supplies the base of the chain. -/
theorem actual_cofinal_of_extension (hext : StrictExtension) : CofinalGood :=
  cofinal_of_good_zero_and_extension
    ZetaBetaHankel.Zeta357DigitAdmission.goodAt_zero hext

/-- The exact remaining premise is displayed as the sole theorem argument. -/
theorem actual_zeta357_irrational_of_extension (hext : StrictExtension) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 3) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) :=
  zeta357_actual_values_of_cofinal (actual_cofinal_of_extension hext)

/-- The same endpoint with the extension proposition fully expanded. -/
theorem actual_zeta357_irrational
    (hext : ∀ n : ℕ, GoodAt n → ∃ m : ℕ, n < m ∧ GoodAt m) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 3) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) :=
  actual_zeta357_irrational_of_extension hext

/-- A direct assembly through the finite admission record, independently of
the `goodAt_zero` wrapper. -/
theorem actual_zeta357_irrational_via_admission (hext : StrictExtension) :
    Irrational (actualZeta 1) ∧ Irrational (actualZeta 2) ∧ Irrational (actualZeta 3) :=
  zeta357_irrational_of_admission_and_extension
    ZetaBetaHankel.Zeta357DigitAdmission.actualN0Admission hext

set_option pp.fullNames true in
#check @actual_cofinal_of_extension
set_option pp.fullNames true in
#check @actual_zeta357_irrational_of_extension
set_option pp.fullNames true in
#check @actual_zeta357_irrational
set_option pp.fullNames true in
#check @actual_zeta357_irrational_via_admission

#print axioms actual_cofinal_of_extension
#print axioms actual_zeta357_irrational_of_extension
#print axioms actual_zeta357_irrational
#print axioms actual_zeta357_irrational_via_admission

end ZetaBetaHankel.Zeta357VerifiedChain
