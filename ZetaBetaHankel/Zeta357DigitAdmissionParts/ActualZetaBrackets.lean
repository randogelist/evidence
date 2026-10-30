import ZetaBetaHankel.Zeta357DigitAdmissionParts.AnalyticBridge
import ZetaBetaHankel.Zeta357DigitAdmissionParts.EtaCoordinates

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

namespace ZetaBetaHankel.Zeta357Analytic

open ZetaBetaHankel.Zeta357EtaArithmetic
open ZetaBetaHankel.Zeta357DigitAdmission
open ZetaBetaHankel.Zeta357CandidateN0

theorem actual_zeta3_enclosed : Contains denominator zetaBox3 (actualZeta 1) := by
  apply zeta3_box_of_approximation
  have h := finiteEta_source_bounds_succ 2 8320 (by decide)
  norm_num only [etaFactor3, etaTail, actualZeta, Nat.cast_sub, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  exact h

theorem actual_zeta5_enclosed : Contains denominator zetaBox5 (actualZeta 2) := by
  apply zeta5_box_of_approximation
  have h := finiteEta_source_bounds_succ 4 8320 (by decide)
  norm_num only [etaFactor5, etaTail, actualZeta, Nat.cast_sub, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  exact h

theorem actual_zeta7_enclosed : Contains denominator zetaBox7 (actualZeta 3) := by
  apply zeta7_box_of_approximation
  have h := finiteEta_source_bounds_succ 6 8320 (by decide)
  norm_num only [etaFactor7, etaTail, actualZeta, Nat.cast_sub, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  exact h

end ZetaBetaHankel.Zeta357Analytic
