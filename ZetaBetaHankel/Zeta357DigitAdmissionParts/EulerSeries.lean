import ZetaBetaHankel.Zeta357DigitAdmissionParts.Base

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Generic Euler transform and a certified geometric remainder.
   Prepared without local Lean execution.
   API references checked against official Mathlib documentation:
   Analysis.SpecificLimits.Normed; InfiniteSum.NatInt/Real/Constructions.
-/

namespace ZetaBetaHankel.Zeta357Euler

open scoped BigOperators

def eulerKernel (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 / 2 : ℝ) ^ (n + 1)

def eulerDifference (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) * a k

theorem eulerKernel_nonneg (n k : ℕ) : 0 ≤ eulerKernel n k := by
  unfold eulerKernel
  positivity

theorem eulerKernel_hasSum (k : ℕ) :
    HasSum (fun n => eulerKernel n k) 1 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hp : (1 / 2 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hbase :=
    (hasSum_choose_mul_geometric_of_norm_lt_one k hr).mul_right
      ((1 / 2 : ℝ) ^ (k + 1))
  have hv :
      (1 / (1 - (1 / 2 : ℝ)) ^ (k + 1)) * (1 / 2 : ℝ) ^ (k + 1) = 1 := by
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact div_mul_cancel₀ 1 hp
  have hscaled :
      HasSum (fun n : ℕ =>
        ((n + k).choose k : ℝ) * (1 / 2 : ℝ) ^ n *
          (1 / 2 : ℝ) ^ (k + 1)) 1 := by
    simpa only [hv] using hbase
  have hshift : HasSum (fun n => eulerKernel (n + k) k) 1 := by
    apply hscaled.congr_fun
    intro n
    unfold eulerKernel
    rw [show n + k + 1 = n + (k + 1) by omega, pow_add]
    ring
  have hprefix : ∑ n ∈ Finset.range k, eulerKernel n k = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [eulerKernel, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
  have hfull :=
    (hasSum_nat_add_iff (f := fun n => eulerKernel n k) k).mp hshift
  simpa only [hprefix, add_zero] using hfull

theorem eulerKernel_mul_tsum (k : ℕ) (c : ℝ) :
    (∑' n, eulerKernel n k * c) = c := by
  simpa only [one_mul] using ((eulerKernel_hasSum k).mul_right c).tsum_eq

/-- Euler's transform for every absolutely summable real sequence.
No positivity or complete monotonicity assumption is required for the identity.
-/
theorem euler_transform {a : ℕ → ℝ} (ha : Summable a) :
    (∑' n, (1 / 2 : ℝ) ^ (n + 1) * eulerDifference a n) =
      ∑' k, (-1 : ℝ) ^ k * a k := by
  let F : ℕ → ℕ → ℝ :=
    fun k n => eulerKernel n k * ((-1 : ℝ) ^ k * a k)
  have habs : Summable (fun p : ℕ × ℕ => eulerKernel p.2 p.1 * |a p.1|) := by
    apply (summable_prod_of_nonneg (fun p =>
      mul_nonneg (eulerKernel_nonneg p.2 p.1) (abs_nonneg _))).2
    constructor
    · intro k
      exact ((eulerKernel_hasSum k).mul_right |a k|).summable
    · simpa only [eulerKernel_mul_tsum] using ha.abs
  have hF : Summable (Function.uncurry F) := by
    apply Summable.of_abs
    convert habs using 1
    ext p
    dsimp [F, Function.uncurry]
    rw [abs_mul, abs_of_nonneg (eulerKernel_nonneg p.2 p.1), abs_mul, abs_pow]
    norm_num
  have hrow (n : ℕ) :
      (∑' k, F k n) = (1 / 2 : ℝ) ^ (n + 1) * eulerDifference a n := by
    calc
      (∑' k, F k n) = ∑ k ∈ Finset.range (n + 1), F k n := by
        apply tsum_eq_sum
        intro k hk
        have hnk : n < k := by
          have : ¬ k < n + 1 := by simpa only [Finset.mem_range] using hk
          omega
        simp [F, eulerKernel, Nat.choose_eq_zero_of_lt hnk]
      _ = (1 / 2 : ℝ) ^ (n + 1) * eulerDifference a n := by
        unfold eulerDifference
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [F, eulerKernel]
        ring
  calc
    (∑' n, (1 / 2 : ℝ) ^ (n + 1) * eulerDifference a n) =
        ∑' n, ∑' k, F k n := tsum_congr fun n => (hrow n).symm
    _ = ∑' k, ∑' n, F k n := hF.tsum_comm
    _ = ∑' k, (-1 : ℝ) ^ k * a k := by
      apply tsum_congr
      intro k
      exact eulerKernel_mul_tsum k ((-1 : ℝ) ^ k * a k)

theorem half_geometric_hasSum :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
  convert hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1) using 1
  norm_num

theorem half_geometric_tail_hasSum (J : ℕ) :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + J + 1)) ((1 / 2 : ℝ) ^ J) := by
  convert half_geometric_hasSum.mul_right ((1 / 2 : ℝ) ^ (J + 1)) using 1
  · ext n
    rw [← pow_add]
    congr 1
    omega
  · rw [pow_succ]
    ring

/-- Positivity of the Euler coefficients supplies the one-sided remainder
used in the C certificate: the tail after J terms lies in [0,2^(-J)]. -/
theorem euler_remainder_bound (d : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n ∧ d n ≤ 1) (J : ℕ) :
    (∑ n ∈ Finset.range J, d n * (1 / 2 : ℝ) ^ (n + 1)) ≤
        (∑' n, d n * (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∑' n, d n * (1 / 2 : ℝ) ^ (n + 1)) ≤
        (∑ n ∈ Finset.range J, d n * (1 / 2 : ℝ) ^ (n + 1)) +
          (1 / 2 : ℝ) ^ J := by
  let f : ℕ → ℝ := fun n => d n * (1 / 2 : ℝ) ^ (n + 1)
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using half_geometric_hasSum.summable.mul_right (1 / 2 : ℝ)
  have hf : Summable f := by
    apply hg.of_norm_bounded
    intro n
    dsimp [f]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hd n).1 (pow_nonneg (by norm_num) _))]
    exact (mul_le_mul_of_nonneg_right (hd n).2
      (pow_nonneg (by norm_num) _)).trans_eq (one_mul _)
  have htail0 : 0 ≤ ∑' n, f (n + J) := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg (hd (n + J)).1 (pow_nonneg (by norm_num) _)
  have htail : (∑' n, f (n + J)) ≤ (1 / 2 : ℝ) ^ J := by
    have hcomp : ∀ n : ℕ, f (n + J) ≤ (1 / 2 : ℝ) ^ (n + J + 1) := by
      intro n
      exact (mul_le_mul_of_nonneg_right (hd (n + J)).2
        (pow_nonneg (by norm_num) _)).trans_eq (one_mul _)
    have hle := Summable.tsum_le_tsum hcomp
      ((summable_nat_add_iff J).2 hf) (half_geometric_tail_hasSum J).summable
    simpa only [(half_geometric_tail_hasSum J).tsum_eq] using hle
  have hsplit := Summable.sum_add_tsum_nat_add J hf
  constructor
  · change (∑ n ∈ Finset.range J, f n) ≤ ∑' n, f n
    linarith
  · change (∑' n, f n) ≤ (∑ n ∈ Finset.range J, f n) + (1 / 2 : ℝ) ^ J
    linarith

end ZetaBetaHankel.Zeta357Euler
