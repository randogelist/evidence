import ZetaBetaHankel.USPDCore

/-!
# Qualitative adjusted blueprint closed from the singular USPD input

This is the exact one-input qualitative closure requested for the canonical
adjacent odd-zeta determinant family.  It includes all admissible adjacent
coupled rays, every pure odd zeta value from weight five onward, the corrected
zeta(3)/zeta(5) cone, and the n -> n+2 -> n+4 consequence.

The numerical exponents 538, 62 and 61 and the independent beta-chain source
theorems are deliberately not folded into this qualitative proposition.
-/

noncomputable section
namespace ZetaBetaHankel.USPD

/-- Pure odd-zeta value indexed so `k = 1` is zeta(5). -/
noncomputable def higherOddValue (k : ℕ) : ℝ :=
  ZetaBetaHankel.Repaired.riemannZetaReal ((2 * k + 3 : ℕ) : ℝ)

/-- The original coupled zeta(3)/zeta(5) value. -/
noncomputable def coupled35Value (a b : ℤ) : ℝ :=
  (b : ℝ) * ZetaBetaHankel.Repaired.riemannZetaReal 5 +
    (a : ℝ) * ZetaBetaHankel.Repaired.riemannZetaReal 3

/-- Every admissible adjacent coupled ray is irrational. -/
theorem adjacent_coupled_irrational (h : USPD)
    (k : ℕ) (hk : 1 ≤ k) (a b : ℤ)
    (hcone : ZetaBetaHankel.Repaired.InPositiveCone k a b) :
    Irrational (ZetaBetaHankel.Repaired.xiCoupled k a b) := by
  let ray : Ray := ⟨k, hk, a, b, hcone⟩
  exact universal_irrational h ray

/-- Every pure odd zeta value of weight at least five is irrational. -/
theorem all_higher_odd_irrational (h : USPD)
    (k : ℕ) (hk : 1 ≤ k) : Irrational (higherOddValue k) := by
  have hraw := universal_irrational h (pureHigherRay k hk)
  simpa [actualValue, pureHigherRay, higherOddValue,
    ZetaBetaHankel.Repaired.xiCoupled] using hraw

/-- Weight five is the first pure specialization. -/
theorem zeta_five_irrational (h : USPD) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) := by
  have hraw := all_higher_odd_irrational h 1 (by omega)
  simpa [higherOddValue] using hraw

/-- Corrected positive-cone irrationality for b*zeta(5)+a*zeta(3). -/
theorem coupled35_irrational (h : USPD) (a b : ℤ)
    (hb : 0 < b)
    (ha : (a : ℝ) < (Real.pi ^ 2 / 3) * (b : ℝ)) :
    Irrational (coupled35Value a b) := by
  have hraw := universal_irrational h (coupled35Ray a b hb ha)
  simpa [actualValue, coupled35Ray, coupled35Value,
    ZetaBetaHankel.Repaired.xiCoupled] using hraw

/-- The requested n -> n+2 -> n+4 implication is a consequence of the same
    universal input, not a second conditional premise. -/
theorem odd_two_step (h : USPD) (k : ℕ) (hk : 1 ≤ k) :
    (Irrational (higherOddValue k) ∧
      Irrational (higherOddValue (k + 1))) →
      Irrational (higherOddValue (k + 2)) := by
  intro _
  exact all_higher_odd_irrational h (k + 2) (by omega)

/-- The exact qualitative adjusted endpoint controlled by the singular input. -/
structure AdjustedBlueprint : Prop where
  universal_ray_irrationality : ∀ ray : Ray, Irrational (actualValue ray)
  adjacent_coupled_irrationality :
    ∀ (k : ℕ), 1 ≤ k → ∀ (a b : ℤ),
      ZetaBetaHankel.Repaired.InPositiveCone k a b →
      Irrational (ZetaBetaHankel.Repaired.xiCoupled k a b)
  all_higher_odd_irrationality :
    ∀ (k : ℕ), 1 ≤ k → Irrational (higherOddValue k)
  weight_five_irrationality :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5)
  corrected_coupled_35_irrationality :
    ∀ (a b : ℤ), 0 < b →
      (a : ℝ) < (Real.pi ^ 2 / 3) * (b : ℝ) →
      Irrational (coupled35Value a b)
  two_step_odd_transition :
    ∀ (k : ℕ), 1 ≤ k →
      (Irrational (higherOddValue k) ∧
        Irrational (higherOddValue (k + 1))) →
        Irrational (higherOddValue (k + 2))

/-- A-Tier target: USPD is the only conditional input. -/
theorem adjusted_blueprint_of_uspd (h : USPD) : AdjustedBlueprint := by
  refine
    { universal_ray_irrationality := universal_irrational h
      adjacent_coupled_irrationality := ?_
      all_higher_odd_irrationality := ?_
      weight_five_irrationality := zeta_five_irrational h
      corrected_coupled_35_irrationality := ?_
      two_step_odd_transition := ?_ }
  · intro k hk a b hcone
    exact adjacent_coupled_irrational h k hk a b hcone
  · intro k hk
    exact all_higher_odd_irrational h k hk
  · intro a b hb ha
    exact coupled35_irrational h a b hb ha
  · intro k hk
    exact odd_two_step h k hk

end ZetaBetaHankel.USPD
