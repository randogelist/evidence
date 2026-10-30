import ZetaBetaHankel.Zeta357CandidateN0

/-!
# The exact standalone zeta(3), zeta(5), zeta(7) irrationality junction

This module proves the complete implication from the existing `CofinalGood`
predicate to irrationality of the three actual zeta values. It also proves
that a finite admitted point together with a strict extension theorem supplies
that cofinal predicate. No extension theorem is assumed as an axiom or asserted
without its explicit argument.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open Polynomial

namespace ZetaBetaHankel.Zeta357Chain

open ZetaBetaHankel.USPD ZetaBetaHankel.Zeta357CandidateN0

/-- A cofinal sequence of nonzero, quadratically small integer-polynomial
evaluations suffices; no assertion about every sufficiently large index is needed. -/
theorem irrational_of_cofinal_quadratic_decay
    (P : ℕ → ℤ[X]) (x : ℝ) (S : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hdegree : ∀ n, (P n).natDegree ≤ S n)
    (hindex : ∀ n, n < S n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, L ≤ n ∧
      0 < |evalIntPoly (P n) x| ∧
      |evalIntPoly (P n) x| ≤ Real.exp (-ε * (S n : ℝ) ^ 2)) :
    Irrational x := by
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hb : 0 < q.den := q.pos
  have hbR : (0 : ℝ) < q.den := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ q.den := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log (q.den : ℝ) := Real.log_nonneg hb1
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.log q.den / ε)
  obtain ⟨n, hn, hnonzero, hupper⟩ := hcofinal L
  have hLS : L < S n := lt_of_le_of_lt hn (hindex n)
  have hLSR : (L : ℝ) < (S n : ℝ) := by exact_mod_cast hLS
  have hchoice0 : Real.log q.den < (S n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (hL.trans hLSR)
  have hchoice : Real.log q.den < ε * (S n : ℝ) := by
    simpa [mul_comm] using hchoice0
  have hSposNat : 0 < S n := lt_of_le_of_lt (Nat.zero_le n) (hindex n)
  have hSpos : (0 : ℝ) < S n := by exact_mod_cast hSposNat
  have hdeg : ((P n).natDegree : ℝ) ≤ (S n : ℝ) := by
    exact_mod_cast hdegree n
  have hstrict : ((P n).natDegree : ℝ) * Real.log q.den < ε * (S n : ℝ) ^ 2 := by
    calc
      ((P n).natDegree : ℝ) * Real.log q.den
          ≤ (S n : ℝ) * Real.log q.den := mul_le_mul_of_nonneg_right hdeg hlog
      _ < (S n : ℝ) * (ε * (S n : ℝ)) := mul_lt_mul_of_pos_left hchoice hSpos
      _ = ε * (S n : ℝ) ^ 2 := by ring
  have hnegative : ((P n).natDegree : ℝ) * Real.log q.den - ε * (S n : ℝ) ^ 2 < 0 :=
    sub_neg.mpr hstrict
  have hrat : (q.num : ℝ) / (q.den : ℝ) = x := (Rat.cast_def q).symm.trans hq
  apply integer_polynomial_squeeze (P n) q.num q.den hb
  · rw [hrat]
    exact abs_pos.mp hnonzero
  · rw [hrat]
    calc
      (q.den : ℝ) ^ (P n).natDegree * |evalIntPoly (P n) x|
          ≤ (q.den : ℝ) ^ (P n).natDegree * Real.exp (-ε * (S n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hupper (le_of_lt (pow_pos hbR _))
      _ = Real.exp (((P n).natDegree : ℝ) * Real.log q.den - ε * (S n : ℝ) ^ 2) := by
          rw [show (q.den : ℝ) ^ (P n).natDegree =
              Real.exp (((P n).natDegree : ℝ) * Real.log q.den) by
            rw [← Real.log_pow, Real.exp_log (pow_pos hbR _)]]
          rw [← Real.exp_add]
          congr 1
          ring
      _ < 1 := Real.exp_lt_one_iff.mpr hnegative

/-- The common cutoff dominates the index regardless of any admission. -/
theorem index_lt_scale (n : ℕ) : n < scale n := by
  unfold scale
  apply lt_of_lt_of_le (b := 40 * (n + 1))
  · omega
  · exact le_max_left _ _

/-- Each of the three degrees is bounded by the common cutoff. -/
theorem degree_le_scale (k n : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    (primitivePolynomial k n).natDegree ≤ scale n := by
  have houter := le_max_right (40 * (n + 1))
    (max ((primitivePolynomial 1 n).natDegree + 1)
      (max ((primitivePolynomial 2 n).natDegree + 1)
        ((primitivePolynomial 3 n).natDegree + 1)))
  have h1 := le_max_left ((primitivePolynomial 1 n).natDegree + 1)
    (max ((primitivePolynomial 2 n).natDegree + 1)
      ((primitivePolynomial 3 n).natDegree + 1))
  have h23 := le_max_right ((primitivePolynomial 1 n).natDegree + 1)
    (max ((primitivePolynomial 2 n).natDegree + 1)
      ((primitivePolynomial 3 n).natDegree + 1))
  have h2 := le_max_left ((primitivePolynomial 2 n).natDegree + 1)
    ((primitivePolynomial 3 n).natDegree + 1)
  have h3 := le_max_right ((primitivePolynomial 2 n).natDegree + 1)
    ((primitivePolynomial 3 n).natDegree + 1)
  rcases hk with rfl | rfl | rfl <;> unfold scale <;> omega

/-- An explicit sublinear logarithm bound, sufficient for both transfer costs. -/
theorem log_add_two_le_div_hundred (s : ℝ) (hs : 100000 ≤ s) :
    Real.log (s + 2) ≤ s / 100 := by
  have hs0 : 0 ≤ s := by linarith
  have hp : 0 < s + 2 := by linarith
  have hroot0 : 0 ≤ Real.sqrt (s + 2) := Real.sqrt_nonneg _
  have hprod : 0 ≤ s * (s - 100000) := mul_nonneg hs0 (by linarith)
  have hroot : Real.sqrt (s + 2) ≤ s / 200 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hlog := Real.log_le_self hroot0
  rw [Real.log_sqrt hp.le] at hlog
  linarith

/-- The two transfer costs still leave a uniform positive quadratic margin. -/
theorem good_large_quadratic (n : ℕ) (hn : 100000 ≤ n) (h : GoodAt n) :
    (0 < |value 1 n| ∧ |value 1 n| ≤ Real.exp (-(1 / 2 : ℝ) * (scale n : ℝ) ^ 2)) ∧
    (0 < |value 2 n| ∧ |value 2 n| ≤ Real.exp (-(1 / 2 : ℝ) * (scale n : ℝ) ^ 2)) ∧
    (0 < |value 3 n| ∧ |value 3 n| ≤ Real.exp (-(1 / 2 : ℝ) * (scale n : ℝ) ^ 2)) := by
  obtain ⟨h3, h5, h7⟩ := h
  change 0 < |value 1 n| ∧ |value 1 n| ≤
    Real.exp (-(89 / 100 : ℝ) * (scale n : ℝ) ^ 2) at h3
  simp only [Transfer35At, alpha35, C35, zero_mul, zero_add] at h5
  simp only [Transfer57At, alpha57, C57, zero_mul, zero_add] at h7
  have hsNat : 100000 ≤ scale n := le_trans hn (index_lt_scale n).le
  have hs : (100000 : ℝ) ≤ (scale n : ℝ) := by exact_mod_cast hsNat
  have hs0 : (0 : ℝ) ≤ (scale n : ℝ) := Nat.cast_nonneg _
  have hlog := log_add_two_le_div_hundred (scale n : ℝ) hs
  have hcost := mul_le_mul_of_nonneg_left hlog hs0
  have hupper5 : |value 2 n| ≤ Real.exp
      (-(89 / 100 : ℝ) * (scale n : ℝ) ^ 2 +
        10 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) := by
    calc
      |value 2 n| ≤ Real.exp (10 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
          |value 1 n| := h5.2
      _ ≤ Real.exp (10 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
          Real.exp (-(89 / 100 : ℝ) * (scale n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3.2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hupper7 : |value 3 n| ≤ Real.exp
      (-(89 / 100 : ℝ) * (scale n : ℝ) ^ 2 +
        21 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) := by
    calc
      |value 3 n| ≤ Real.exp (11 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
          |value 2 n| := h7.2
      _ ≤ Real.exp (11 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
          Real.exp (-(89 / 100 : ℝ) * (scale n : ℝ) ^ 2 +
            10 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hupper5 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨⟨h3.1, h3.2.trans ?_⟩, ⟨h5.1, hupper5.trans ?_⟩,
    ⟨h7.1, hupper7.trans ?_⟩⟩
  all_goals apply Real.exp_le_exp.mpr
  all_goals nlinarith [sq_nonneg (scale n : ℝ)]

/-- The established integer-polynomial contradiction applied to the exact
standalone family, with the common cofinal premise displayed explicitly. -/
theorem zeta357_irrational_of_cofinal (h : CofinalGood) :
    Irrational (actualZeta 1) ∧ Irrational (actualZeta 2) ∧ Irrational (actualZeta 3) := by
  have hk : ∀ k : ℕ, k = 1 ∨ k = 2 ∨ k = 3 → Irrational (actualZeta k) := by
    intro k hk
    apply irrational_of_cofinal_quadratic_decay (primitivePolynomial k) (actualZeta k)
      scale (1 / 2) (by norm_num) (fun n => degree_le_scale k n hk) index_lt_scale
    intro L
    obtain ⟨n, hn, hgood⟩ := h (max L 100000)
    have hLn : L ≤ n := le_trans (le_max_left _ _) hn
    have hbig : 100000 ≤ n := le_trans (le_max_right _ _) hn
    have hdecay := good_large_quadratic n hbig hgood
    refine ⟨n, hLn, ?_⟩
    rcases hk with rfl | rfl | rfl
    · exact hdecay.1
    · exact hdecay.2.1
    · exact hdecay.2.2
  exact ⟨hk 1 (Or.inl rfl), hk 2 (Or.inr (Or.inl rfl)),
    hk 3 (Or.inr (Or.inr rfl))⟩

/-- The exact extension obligation needed after the admitted finite point. -/
def StrictExtension : Prop :=
  ∀ n : ℕ, GoodAt n → ∃ m : ℕ, n < m ∧ GoodAt m

/-- Finite admission and a strict extension theorem produce common cofinality. -/
theorem cofinal_of_good_zero_and_extension (hzero : GoodAt 0) (hext : StrictExtension) :
    CofinalGood := by
  intro L
  induction L with
  | zero => exact ⟨0, le_refl _, hzero⟩
  | succ L ih =>
    obtain ⟨n, hn, hgood⟩ := ih
    obtain ⟨m, hnm, hm⟩ := hext n hgood
    exact ⟨m, by omega, hm⟩

/-- Cofinality supplies the strict extension obligation at every admitted point. -/
theorem strictExtension_of_cofinal (h : CofinalGood) : StrictExtension := by
  intro n _
  obtain ⟨m, hm, hgood⟩ := h (n + 1)
  exact ⟨m, by omega, hgood⟩

/-- The coordinate admission plugs directly into the existing irrationality
skeleton once a strict extension theorem is supplied. -/
theorem zeta357_irrational_of_admission_and_extension
    (hzero : N0Admission) (hext : StrictExtension) :
    Irrational (actualZeta 1) ∧ Irrational (actualZeta 2) ∧ Irrational (actualZeta 3) :=
  zeta357_irrational_of_cofinal
    (cofinal_of_good_zero_and_extension (good_zero_of_admission hzero) hext)

/-- A completed extension record is already the full sufficient certificate. -/
theorem zeta357_irrational_of_candidate_extension (h : CandidateExtension) :
    Irrational (actualZeta 1) ∧ Irrational (actualZeta 2) ∧ Irrational (actualZeta 3) :=
  zeta357_irrational_of_cofinal h.cofinal_good

/-- The same conclusion with the numerical zeta arguments made visible. -/
theorem zeta357_actual_values_of_cofinal (h : CofinalGood) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 3) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) := by
  simpa [actualZeta] using zeta357_irrational_of_cofinal h

#print axioms irrational_of_cofinal_quadratic_decay
#print axioms log_add_two_le_div_hundred
#print axioms good_large_quadratic
#print axioms zeta357_irrational_of_cofinal
#print axioms cofinal_of_good_zero_and_extension
#print axioms strictExtension_of_cofinal
#print axioms zeta357_irrational_of_admission_and_extension
#print axioms zeta357_irrational_of_candidate_extension
#print axioms zeta357_actual_values_of_cofinal

end ZetaBetaHankel.Zeta357Chain
