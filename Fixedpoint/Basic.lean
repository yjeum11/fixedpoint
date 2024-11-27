import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Algebra.Order.CauSeq.Basic

import Fixedpoint.Carryover

/-
Banach fixed-point theorem

References:

https://en.wikipedia.org/wiki/Banach_fixed-point_theorem
https://wiki.math.ntnu.no/_media/tma4145/2020h/banach.pdf

-/

namespace project

open Classical Filter Finset Real

noncomputable section

variable {X : Type} [NX : Nonempty X] [MetricSpace X] [CompleteSpace X]

def IsContraction (f : X → X) : Prop :=
  ∃ q > 0, q < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ q * dist x y

def IsFixedPoint (f : X → X) (p : X) : Prop :=
  f p = p

def T (f : X → X) : ℕ → X
  | 0 => choice NX
  | n+1 => f (T f n)

theorem exists_fixed_point_of_isContraction (f : X → X) (hf : IsContraction f)
  : ∃ p, IsFixedPoint f p := by

  rcases hf with ⟨q, hf⟩
  have Tdist : ∀ n, dist (T f (n+1)) (T f n) ≤ q^n * dist (T f 1) (T f 0) := by
    intro n
    induction' n with n ih
    . simp
    rw [T] at *
    rcases hf with ⟨qgt0, qle1, hq⟩
    have := hq (f (T f n)) (T f n)
    apply le_trans
    apply this
    rw [pow_succ]
    nth_rw 3 [mul_comm]
    rw [mul_assoc, mul_le_mul_left]
    apply ih
    apply qgt0

  have Tdist' : ∀ n p, 1 ≤ p → dist (T f (n+p)) (T f n) ≤ dist (T f 1) (T f 0) * (1-q)⁻¹ * q^n  := by
    intro n p hp
    calc dist (T f (n+p)) (T f n) ≤
            ∑ k ∈ range p, dist (T f (n+k+1)) (T f (n+k)) := by
              induction' p, hp using Nat.le_induction with p hp ih
              . rw [sum_range_one]; simp
              rw [sum_range_succ, ←add_assoc]
              apply le_trans (dist_triangle (T f (n+p+1)) (T f (n+p)) (T f n))
              rw [add_comm]
              apply add_le_add_right
              exact ih
        _ ≤ ∑ k ∈ range p, q^(n+k) * dist (T f 1) (T f 0) := by
              apply sum_le_sum
              intro i hi
              apply Tdist
        _ = (∑ k ∈ range p, q^k) * dist (T f 1) (T f 0) * q^n := by
              simp_rw [pow_add, mul_assoc]
              rw [←mul_sum, ←sum_mul]
              ring
        _ ≤ (∑' (k : ℕ), q^k) * dist (T f 1) (T f 0) * q^n := by
              apply mul_le_mul
              apply mul_le_mul
              . apply sum_le_tsum
                intro i hi
                . apply pow_nonneg
                  apply le_of_lt hf.1
                apply summable_geometric_of_lt_one
                apply le_of_lt hf.1
                apply hf.2.1
              . simp
              . apply dist_nonneg
              . apply tsum_nonneg
                intro i
                apply pow_nonneg
                apply le_of_lt hf.1
              . simp
              . apply pow_nonneg; apply le_of_lt hf.1
              . apply mul_nonneg 
                . apply tsum_nonneg
                  intro i
                  apply pow_nonneg
                  apply le_of_lt hf.1
                . apply dist_nonneg
                
        _ = (1-q)⁻¹ * dist (T f 1) (T f 0) * q^n := by
              rw [tsum_geometric_of_lt_one]
              apply le_of_lt hf.1
              apply hf.2.1
    simp [mul_comm]
  
  have Tconv_aux (m n : ℕ) (hmn : m > n) : dist (T f m) (T f n) ≤ dist (T f 1) (T f 0) * (1-q)⁻¹ * q^n := by
    let p := m - n
    have p_ge_1 : 1 ≤ p := by 
      dsimp [p]
      omega
    have : m = n + p := by omega
    rw [this]
    apply Tdist'
    apply p_ge_1

  have Tconv : CauchySeq (T f) := by
    rw [Metric.cauchySeq_iff']

    intro ε hε
    let A := (dist (T f 1) (T f 0)) * (1-q)⁻¹
    let N := Nat.floor (logb q (ε / A)) + 1
    use N
    intro n hn

    by_cases h: n = N
    . rwa [h, dist_self]
    apply lt_of_le_of_lt
    apply Tconv_aux
    . omega
    
    by_cases h: (dist (T f 1) (T f 0)) * (1-q)⁻¹ = 0
    . rwa [h, zero_mul]
    have hA : 0 < (dist (T f 1) (T f 0)) * (1-q)⁻¹ := by
      simp at h
      rcases h with ⟨h1, h2⟩
      apply mul_pos
      apply lt_of_le_of_ne
      . apply dist_nonneg
      . rw [←dist_ne_zero]
        simpa
      . simp
        exact hf.2.1

    refine (lt_div_iff₀' ?h.hc).mp ?h.a
    . apply hA
    by_cases hq : 0 = q
    . rw [←hq]
      simp only [NNReal.coe_zero, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow,
        tsub_zero, inv_one, NNReal.coe_one, mul_one]
      apply div_pos
      apply hε 
      apply lt_of_le_of_ne
      apply dist_nonneg
      rw [←dist_ne_zero]
      simp at h
      rcases h with ⟨h1, h2⟩
      simpa

    refine (pow_lt_iff_lt_log ?h.a.hx ?h.a.hy).mpr ?h.a.a
    . apply hf.1
    . apply div_pos
      apply hε
      apply hA
    
    rw [←div_lt_iff_of_neg, log_div_log, ←gt_iff_lt]
    simp at *
    apply Nat.lt_of_floor_lt

    dsimp [N, A] at hn
    dsimp [N, A]
    linarith
    apply log_neg
    apply hf.1
    apply hf.2.1

  apply cauchySeq_tendsto_of_complete at Tconv
  rcases Tconv with ⟨L, hL⟩
  rw [Metric.tendsto_atTop] at hL

  use L

  rw [IsFixedPoint, ←dist_eq_zero]

  have dist_small : ∀ ε > 0, dist L (f L) < ε := by
    intro ε hε 
    have ep : ε / 2 > 0 := by linarith

    rcases hL (ε/2) ep with ⟨N, hN⟩

    have : ∀ n ≥ N, dist L (f L) < ε := by 
      intro n hn
      calc dist L (f L) ≤ dist L (T f (n+1)) + dist (T f (n+1)) (f L) := by exact dist_triangle L (T f (n+1)) (f L)
        _ = dist L (T f (n+1)) + dist (f (T f n)) (f L) := by 
          simp
          dsimp [T]
        _ ≤ dist L (T f (n+1)) + q * dist (T f n) L := by 
          apply add_le_add_left
          apply hf.2.2
        _ < ε/2 + q * ε/2 := by
          apply add_lt_add
          . have : n + 1 ≥ N := by linarith
            rw [dist_comm]
            apply hN (n+1) this
          . rw [mul_div_assoc, mul_lt_mul_left hf.1]
            apply hN n hn

      have hqε : q * (ε / 2) < ε / 2 := by
        apply mul_lt_of_lt_one_left
        . apply ep
        . exact hf.2.1

      have : ε = ε / 2 + ε / 2 := by linarith
      nth_rw 3 [this]
      apply add_lt_add_left
      rw [mul_div_assoc]
      apply hqε
    
    apply this N ?_
    linarith

  have : 0 = dist L (f L) := by
    by_contra h
    have : 0 < dist L (f L) := by
      apply lt_of_le_of_ne
      . apply dist_nonneg
      apply h
    have : 0 < dist L (f L) / 2  := by
      apply div_pos
      exact this
      norm_num
    specialize dist_small (dist L (f L)/2) this
    linarith

  rw [dist_comm]
  apply Eq.symm
  assumption

def TheFixedPoint (f : X → X) (hf : IsContraction f) : X :=
  choose (exists_fixed_point_of_isContraction f hf)

-- set_option pp.proofs true
theorem unique_fixed_point_of_isContraction (f : X → X) (hf : IsContraction f)
  (p : X) (hp : IsFixedPoint f p)
  : p = TheFixedPoint f hf := by
  
  rw [←dist_eq_zero]

  dsimp [IsContraction] at hf
  -- rcases hf with ⟨q, hq⟩
  let q : ℝ := choose hf
  let hq := choose_spec hf

  dsimp [IsFixedPoint] at *
  have fix : f (TheFixedPoint f hf) = TheFixedPoint f hf := by
    have h := Classical.choose_spec (exists_fixed_point_of_isContraction f hf)
    dsimp [TheFixedPoint]
    apply h

  have : dist p (TheFixedPoint f hf) ≤ q * dist p (TheFixedPoint f hf) := by 
    calc dist p (TheFixedPoint f hf) = 
      dist (f p) (f (TheFixedPoint f hf)) := by rw [hp, fix]
    _ ≤ q * dist p (TheFixedPoint f hf) := by apply hq.2.2

  by_cases h : dist p (TheFixedPoint f hf) = 0
  . exact h
  . by_contra
    suffices dist p (TheFixedPoint f hf) > q * dist p (TheFixedPoint f hf) by
      linarith
    rw [mul_comm]
    have : dist p (TheFixedPoint f hf) > 0 := by 
      apply lt_of_le_of_ne
      apply dist_nonneg
      exact fun a ↦ h (id (Eq.symm a))
    apply mul_lt_of_lt_one_right
    apply this
    apply hq.2.1

end
end project
