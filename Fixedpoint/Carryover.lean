import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

open Set Metric Real Classical

theorem exp_converges_zero (q A : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q ∧ q < 1) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, A * q^n < ε := by
  intro ε hε
  use Nat.floor (logb q (ε / A)) + 1
  intro n hn
  -- rw [dist_0_eq_abs, abs_of_nonneg]
  -- swap
  -- . apply mul_nonneg
  --   . exact hA
  --   apply pow_nonneg
  --   . exact hq.1
  by_cases z: 0 = A
  . rwa [←z, zero_mul]
  refine (lt_div_iff₀' ?h.hc).mp ?h.a

  have pos : 0 < A := by
    simp only [gt_iff_lt, one_div, ge_iff_le] at *
    apply lt_of_le_of_ne hA
    simpa only [ne_eq]

  apply pos

  by_cases h : 0 = q
  . rw [←h, zero_pow]
    apply div_pos
    apply hε 
    apply lt_of_le_of_ne
    assumption
    simp; assumption
    linarith

  refine (pow_lt_iff_lt_log ?h.a.hx ?h.a.hy).mpr ?h.a.a
  . rcases hq with ⟨h1, h2⟩
    apply lt_of_le_of_ne
    assumption
    simp; assumption
  . apply div_pos
    apply hε 
    apply lt_of_le_of_ne
    exact hA
    simp
    exact z
  rw [←div_lt_iff_of_neg, log_div_log, ←gt_iff_lt]
  simp only [gt_iff_lt, one_div, ge_iff_le] at *
  apply Nat.lt_of_floor_lt
  linarith
  apply log_neg
  apply lt_of_le_of_ne
  exact hq.1
  apply h
  exact hq.2

-- theorem exp_converges_zero' (q : ℝ) (hq : 0 ≤ q ∧ q < 1) :
--   ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (q^n) 0 < ε := by
--   intro ε hε 
--   have := exp_converges_zero q 1 ?_ hq ε hε 
--   rcases this with ⟨N, hN⟩
--   use N
--   intro n hn
--   specialize hN n hn
--   simp at *
--   assumption
--   norm_num
