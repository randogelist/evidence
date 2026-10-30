import ZetaBetaHankel.Zeta357DigitAdmissionParts.EtaArithmetic
import ZetaBetaHankel.Zeta357DigitAdmissionParts.EulerSeries

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/-
Analytic Euler-coefficient bridge. Requires Mathlib, Repaired.ExactModel,
and EtaArithmetic's homogeneous/finiteEta_eq_sum definitions.
No local Lean execution. No axioms or omitted theorem bodies.
-/
namespace ZetaBetaHankel.Zeta357Analytic

open scoped BigOperators
open ZetaBetaHankel.Zeta357EtaArithmetic

/-- The n-th Euler difference of the shifted reciprocal power sequence. -/
def delta (s n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (n.choose k : ℝ) / ((k : ℝ) + 1) ^ s

private theorem choose_column_sum (m k : ℕ) :
    (∑ j ∈ Finset.range m, j.choose k) = m.choose (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
      exact Nat.add_comm _ _

private theorem delta_extend (s j n : ℕ) (hjn : j ≤ n) :
    delta s j = ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * (j.choose k : ℝ) / ((k : ℝ) + 1) ^ s := by
  unfold delta
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hjn))
  intro k hk hnot
  have hjk : j < k := by
    have : ¬ k < j + 1 := by simpa only [Finset.mem_range] using hnot
    omega
  simp [Nat.choose_eq_zero_of_lt hjk]

private theorem weighted_choose_term (s n k : ℕ) :
    ((n : ℝ) + 1) *
        ((-1 : ℝ) ^ k * (n.choose k : ℝ) / ((k : ℝ) + 1) ^ (s + 1)) =
      (-1 : ℝ) ^ k * ((n + 1).choose (k + 1) : ℝ) /
        ((k : ℝ) + 1) ^ s := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hc : ((n : ℝ) + 1) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  calc
    _ = (-1 : ℝ) ^ k *
        ((((n : ℝ) + 1) * (n.choose k : ℝ)) / ((k : ℝ) + 1) ^ (s + 1)) := by ring
    _ = (-1 : ℝ) ^ k *
        ((((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1)) /
          ((k : ℝ) + 1) ^ (s + 1)) := by rw [hc]
    _ = _ := by rw [pow_succ]; field_simp [hk]; ring

theorem delta_succ (s n : ℕ) :
    delta (s + 1) n = (∑ j ∈ Finset.range (n + 1), delta s j) /
      ((n : ℝ) + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  calc
    delta (s + 1) n * ((n : ℝ) + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * ((n + 1).choose (k + 1) : ℝ) /
          ((k : ℝ) + 1) ^ s := by
      rw [mul_comm, delta, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact weighted_choose_term s n k
    _ = ∑ k ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (j.choose k : ℝ) / ((k : ℝ) + 1) ^ s := by
      apply Finset.sum_congr rfl
      intro k hk
      have hc : ((n + 1).choose (k + 1) : ℝ) =
          ∑ j ∈ Finset.range (n + 1), (j.choose k : ℝ) := by
        exact_mod_cast (choose_column_sum (n + 1) k).symm
      rw [hc, Finset.mul_sum, Finset.sum_div]
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (j.choose k : ℝ) / ((k : ℝ) + 1) ^ s :=
      Finset.sum_comm
    _ = ∑ j ∈ Finset.range (n + 1), delta s j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (delta_extend s j n (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm

theorem delta_zero (n : ℕ) : delta 0 n = if n = 0 then 1 else 0 := by
  simp only [delta, pow_zero, div_one]
  exact_mod_cast (Int.alternating_sum_range_choose (n := n))

theorem delta_one (n : ℕ) : delta 1 n = 1 / ((n : ℝ) + 1) := by
  rw [show 1 = 0 + 1 from rfl, delta_succ]
  simp [delta_zero]

theorem delta_nonneg_le_one (s n : ℕ) : 0 ≤ delta s n ∧ delta s n ≤ 1 := by
  induction s generalizing n with
  | zero => simp only [delta_zero]; split <;> norm_num
  | succ s ih =>
      simp only [delta_succ]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsum0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), delta s j :=
        Finset.sum_nonneg (fun j _ => (ih j).1)
      have hsum1 : (∑ j ∈ Finset.range (n + 1), delta s j) ≤ (n : ℝ) + 1 := by
        calc
          _ ≤ ∑ _j ∈ Finset.range (n + 1), (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => (ih j).2)
          _ = _ := by simp
      exact ⟨div_nonneg hsum0 hn.le, (div_le_iff₀ hn).2 (by simpa using hsum1)⟩

theorem delta_eq_homogeneous (r n : ℕ) :
    delta (r + 1) n = homogeneous r (n + 1) / ((n : ℝ) + 1) := by
  induction r generalizing n with
  | zero => simpa [homogeneous] using delta_one n
  | succ r ih =>
      rw [delta_succ]
      simp only [ih, homogeneous, Nat.cast_add, Nat.cast_one]

theorem finiteEta_eq_delta_sum (s J : ℕ) (hs : 0 < s) :
    finiteEta s J = ∑ j ∈ Finset.range J,
      delta s j / (2 : ℝ) ^ (j + 1) := by
  rw [finiteEta_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : delta s j = homogeneous (s - 1) (j + 1) / ((j : ℝ) + 1) := by
    simpa only [Nat.sub_add_cancel hs] using delta_eq_homogeneous (s - 1) j
  rw [he]
  push_cast
  rw [div_mul_eq_div_div]

/-- The source definition at a positive natural argument is the usual p-series. -/
theorem sourceZeta_eq_tsum_nat_pow (s : ℕ) (hs : 0 < s) :
    ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) =
      ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ := by
  unfold ZetaBetaHankel.Repaired.riemannZetaReal
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Nat.ne_of_gt hs]
  · rw [if_neg hn, Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]

def pterm (s n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ s

theorem pterm_summable (s : ℕ) (hs : 1 < s) : Summable (pterm s) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_pow_inv.mpr hs
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).2 h
  simpa only [pterm, one_div, Nat.cast_add, Nat.cast_one] using hshift

theorem sourceZeta_eq_tsum_pterm (s : ℕ) (hs : 1 < s) :
    ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) = ∑' n, pterm s n := by
  rw [sourceZeta_eq_tsum_nat_pow s (by omega)]
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_pow_inv.mpr hs
  have hs0 : s ≠ 0 := by omega
  simpa only [Nat.cast_zero, zero_pow hs0, inv_zero, zero_add,
    Nat.cast_add, Nat.cast_one, pterm, one_div] using h.tsum_eq_zero_add

theorem signed_pterm_summable (s : ℕ) (hs : 1 < s) :
    Summable (fun n => (-1 : ℝ) ^ n * pterm s n) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    using (pterm_summable s hs).norm

theorem pterm_odd (s n : ℕ) :
    pterm s (2 * n + 1) = (1 / (2 : ℝ) ^ s) * pterm s n := by
  unfold pterm
  push_cast
  rw [show (2 : ℝ) * n + 1 + 1 = 2 * ((n : ℝ) + 1) by ring, mul_pow]
  simp only [one_div, mul_inv_rev]
  ring

theorem eta_eq_factor_sourceZeta (s : ℕ) (hs : 1 < s) :
    (∑' n, (-1 : ℝ) ^ n * pterm s n) =
      (1 - 2 / (2 : ℝ) ^ s) *
        ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) := by
  have hp := pterm_summable s hs
  have he : Summable (fun n => pterm s (2 * n)) :=
    hp.comp_injective (by intro a b h; omega)
  have ho : Summable (fun n => pterm s (2 * n + 1)) :=
    hp.comp_injective (by intro a b h; omega)
  have hsg := signed_pterm_summable s hs
  have hse : Summable (fun n => (-1 : ℝ) ^ (2 * n) * pterm s (2 * n)) :=
    hsg.comp_injective (by intro a b h; omega)
  have hso : Summable (fun n => (-1 : ℝ) ^ (2 * n + 1) * pterm s (2 * n + 1)) :=
    hsg.comp_injective (by intro a b h; omega)
  have htotal := tsum_even_add_odd (f := pterm s) he ho
  have hsigned := tsum_even_add_odd (f := fun n => (-1 : ℝ) ^ n * pterm s n) hse hso
  have hodd : (∑' n, pterm s (2 * n + 1)) =
      (1 / (2 : ℝ) ^ s) * (∑' n, pterm s n) := by
    simp_rw [pterm_odd]
    rw [tsum_mul_left]
  have heven : (∑' n, (-1 : ℝ) ^ (2 * n) * pterm s (2 * n)) =
      ∑' n, pterm s (2 * n) := by
    apply tsum_congr
    intro n
    simp [pow_mul]
  have hoddsg : (∑' n, (-1 : ℝ) ^ (2 * n + 1) * pterm s (2 * n + 1)) =
      -(∑' n, pterm s (2 * n + 1)) := by
    calc
      _ = ∑' n, -(pterm s (2 * n + 1)) := by
        apply tsum_congr
        intro n
        simp [pow_add, pow_mul]
      _ = _ := by rw [tsum_neg]
  rw [heven, hoddsg] at hsigned
  rw [hodd] at htotal hsigned
  rw [sourceZeta_eq_tsum_pterm s hs]
  nlinarith

theorem eulerDifference_pterm (s n : ℕ) :
    ZetaBetaHankel.Zeta357Euler.eulerDifference (pterm s) n = delta s n := by
  unfold ZetaBetaHankel.Zeta357Euler.eulerDifference delta
  apply Finset.sum_congr rfl
  intro k hk
  unfold pterm
  ring

theorem delta_euler_tsum (s : ℕ) (hs : 1 < s) :
    (∑' n, delta s n * (1 / 2 : ℝ) ^ (n + 1)) =
      (1 - 2 / (2 : ℝ) ^ s) *
        ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) := by
  calc
    _ = ∑' n, (1 / 2 : ℝ) ^ (n + 1) *
        ZetaBetaHankel.Zeta357Euler.eulerDifference (pterm s) n := by
      apply tsum_congr
      intro n
      rw [eulerDifference_pterm]
      ring
    _ = ∑' n, (-1 : ℝ) ^ n * pterm s n :=
      ZetaBetaHankel.Zeta357Euler.euler_transform (pterm_summable s hs)
    _ = _ := eta_eq_factor_sourceZeta s hs

/-- Exact one-sided finite enclosure for the genuine source zeta series. -/
theorem finiteEta_source_bounds (s J : ℕ) (hs : 1 < s) :
    finiteEta s J ≤ (1 - 2 / (2 : ℝ) ^ s) *
        ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) ∧
      (1 - 2 / (2 : ℝ) ^ s) *
        ZetaBetaHankel.Repaired.riemannZetaReal (s : ℝ) ≤
        finiteEta s J + 1 / (((2 ^ J : ℕ) : ℝ)) := by
  have h := ZetaBetaHankel.Zeta357Euler.euler_remainder_bound
    (delta s) (delta_nonneg_le_one s) J
  have hp : (∑ n ∈ Finset.range J, delta s n * (1 / 2 : ℝ) ^ (n + 1)) =
      finiteEta s J := by
    rw [finiteEta_eq_delta_sum s J (by omega)]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [one_div, inv_pow, div_eq_mul_inv]
  rw [hp, delta_euler_tsum s hs] at h
  simpa only [one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat] using h

/-- This form is convenient for the integer checker at any positive integer weight. -/
theorem finiteEta_source_bounds_succ (r J : ℕ) (hr : 0 < r) :
    finiteEta (r + 1) J ≤ (((2 ^ r - 1 : ℕ) : ℝ) / ((2 ^ r : ℕ) : ℝ)) *
        ZetaBetaHankel.Repaired.riemannZetaReal ((r + 1 : ℕ) : ℝ) ∧
      (((2 ^ r - 1 : ℕ) : ℝ) / ((2 ^ r : ℕ) : ℝ)) *
        ZetaBetaHankel.Repaired.riemannZetaReal ((r + 1 : ℕ) : ℝ) ≤
        finiteEta (r + 1) J + 1 / (((2 ^ J : ℕ) : ℝ)) := by
  have h := finiteEta_source_bounds (r + 1) J (by omega)
  have hp : 1 ≤ (2 : ℕ) ^ r := by
    have := pow_pos (by decide : 0 < (2 : ℕ)) r
    omega
  have hne : (2 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (1 : ℝ) - 2 / (2 : ℝ) ^ (r + 1) =
      (((2 ^ r - 1 : ℕ) : ℝ) / ((2 ^ r : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hp]
    push_cast
    rw [pow_succ]
    field_simp [hne]
    ring
  simpa only [he] using h

end ZetaBetaHankel.Zeta357Analytic
